module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClU4Pair
public import CFSG.LocalAnalysis.ComponentInitial.FourGroupOddUnitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBInner
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveUnitaryLocalComponentSplit

public noncomputable section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup Module Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.FourGroupOddUnitary
open CFSG.GH74.GLS.IVK

section Basis

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]
  {h : UnitaryFieldData p f E} {B : V →ₛₗ[h.bar] V →ₗ[E] E}

@[expose] def invGL (s : V →ₗ[E] V) (hs : s * s = 1) : LinearMap.GeneralLinearGroup E V := ⟨s, s, hs, hs⟩

theorem isometry_of_basis {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι E V)
    (s : V →ₗ[E] V) (hs : ∀ i j, B (s (b i)) (s (b j)) = B (b i) (b j)) :
    ∀ x y, B (s x) (s y) = B x y := by
  have hext : (B.comp s).compl₂ s = B := by
    refine LinearMap.ext_basis b b fun i j => ?_
    rw [LinearMap.compl₂_apply, LinearMap.comp_apply]
    exact hs i j
  intro x y
  exact LinearMap.congr_fun₂ hext x y

structure AdaptedONB (B : V →ₛₗ[h.bar] V →ₗ[E] E) (A W : Submodule E V) where
  ea : Basis (Fin (finrank E A)) E A
  ew : Basis (Fin (finrank E W)) E W
  ea_orth : ∀ i j, B (ea i) (ea j) = if i = j then 1 else 0
  ew_orth : ∀ i j, B (ew i) (ew j) = if i = j then 1 else 0

theorem exists_adaptedONB [FiniteDimensional E V] (hB : B.IsSymm) {A W : Submodule E V}
    (hsepA : (B.domRestrict₁₂ A A).SeparatingLeft) (hsepW : (B.domRestrict₁₂ W W).SeparatingLeft) :
    Nonempty (AdaptedONB B A W) := by
  obtain ⟨ea, hea⟩ := h.exists_orthonormal_basis (M := A) (B := B.domRestrict₁₂ A A)
    ⟨fun x y => hB.eq x y⟩ hsepA
  obtain ⟨ew, hew⟩ := h.exists_orthonormal_basis (M := W) (B := B.domRestrict₁₂ W W)
    ⟨fun x y => hB.eq x y⟩ hsepW
  refine ⟨⟨ea, ew, fun i j => ?_, fun i j => ?_⟩⟩
  · have := hea i j
    rwa [LinearMap.domRestrict₁₂_apply] at this
  · have := hew i j
    rwa [LinearMap.domRestrict₁₂_apply] at this

namespace AdaptedONB

variable {A W : Submodule E V} (Q : AdaptedONB B A W) (hc : IsCompl A W)

@[expose] noncomputable def b : Basis (Fin (finrank E A) ⊕ Fin (finrank E W)) E V :=
  sumBasis hc Q.ea Q.ew

theorem b_inl (i) : Q.b hc (Sum.inl i) = (Q.ea i : V) := sumBasis_inl hc Q.ea Q.ew i

theorem b_inr (j) : Q.b hc (Sum.inr j) = (Q.ew j : V) := sumBasis_inr hc Q.ea Q.ew j

theorem gram (hB : B.IsSymm) (horth : ∀ a ∈ A, ∀ w ∈ W, B a w = 0) :
    ∀ α β, B (Q.b hc α) (Q.b hc β) = if α = β then 1 else 0 := by
  rintro (i | i) (j | j)
  · rw [b_inl, b_inl, Q.ea_orth]; simp
  · rw [b_inl, b_inr, horth _ (Q.ea i).2 _ (Q.ew j).2]; simp
  · rw [b_inr, b_inl, ← hB.eq, horth _ (Q.ea j).2 _ (Q.ew i).2, map_zero]; simp
  · rw [b_inr, b_inr, Q.ew_orth]; simp

end AdaptedONB

theorem exists_scalar_of_mk_eq {y T : sesqUnitaryGroup B}
    (hyT : (QuotientGroup.mk y : sesqProjUnitary h B) = QuotientGroup.mk T) :
    ∃ c : E, h.norm c = 1 ∧ ∀ v, unitaryOp T v = c • unitaryOp y v := by
  have h1 : y⁻¹ * T ∈ sesqNormOneScalars h B := QuotientGroup.eq.mp hyT
  obtain ⟨c, hc, hcx⟩ := h1
  refine ⟨c, hc, fun v => ?_⟩
  have h2 : unitaryOp y⁻¹ (unitaryOp T v) = c • v := by
    have := LinearMap.congr_fun (show unitaryOp (y⁻¹ * T) = c • 1 from hcx) v
    rw [unitaryOp_mul] at this
    simpa using this
  have h3 := congrArg (unitaryOp y) h2
  rw [unitaryOp_apply_inv, map_smul] at h3
  exact h3

theorem mk_eq_of_smul {y T : sesqUnitaryGroup B} {c : E} (hc : h.norm c = 1)
    (hTc : ∀ v, unitaryOp T v = c • unitaryOp y v) :
    (QuotientGroup.mk y : sesqProjUnitary h B) = QuotientGroup.mk T := by
  refine QuotientGroup.eq.2 ⟨c, hc, ?_⟩
  refine LinearMap.ext fun v => ?_
  show unitaryOp (y⁻¹ * T) v = (c • (1 : Module.End E V)) v
  rw [unitaryOp_mul, Module.End.mul_apply, hTc, map_smul, unitaryOp_inv_apply]
  simp

section Sign

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι E V)

@[expose] noncomputable def signOp (S : Finset ι) : V →ₗ[E] V :=
  b.constr E (fun i => (if i ∈ S then (-1 : E) else 1) • b i)

omit [Fintype ι] in
theorem signOp_apply (S : Finset ι) (i : ι) :
    signOp b S (b i) = (if i ∈ S then (-1 : E) else 1) • b i := by
  simp only [signOp, Basis.constr_basis]

omit [Fintype ι] in
theorem signOp_mul_self (S : Finset ι) : signOp b S * signOp b S = 1 := by
  refine b.ext fun i => ?_
  rw [Module.End.mul_apply, signOp_apply, map_smul, signOp_apply, smul_smul, Module.End.one_apply]
  split_ifs <;> simp

theorem signOp_isometry (hG : ∀ i j, B (b i) (b j) = if i = j then 1 else 0) (S : Finset ι) :
    ∀ x y, B (signOp b S x) (signOp b S y) = B x y := by
  refine isometry_of_basis b _ fun i j => ?_
  simp only [signOp_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, hG]
  by_cases hij : i = j
  · subst hij
    split_ifs <;> simp
  · simp [hij]

@[expose] noncomputable def signU (hG : ∀ i j, B (b i) (b j) = if i = j then 1 else 0) (S : Finset ι) :
    sesqUnitaryGroup B :=
  ⟨invGL (signOp b S) (signOp_mul_self b S), fun x y => signOp_isometry b hG S x y⟩

theorem unitaryOp_signU (hG : ∀ i j, B (b i) (b j) = if i = j then 1 else 0) (S : Finset ι) :
    unitaryOp (signU b hG S) = signOp b S := rfl

theorem det_signOp (S : Finset ι) : LinearMap.det (signOp b S) = (-1) ^ S.card := by
  have h1 : LinearMap.toMatrix b b (signOp b S) = FourGroupOddBilinear.signDiag S := by
    rw [toMatrix_eq_diagonal b (μ := fun i => if i ∈ S then (-1 : E) else 1)
      (fun i => signOp_apply b S i)]
    rfl
  rw [← LinearMap.det_toMatrix b, h1, FourGroupOddBilinear.det_signDiag]

end Sign

section Perm

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι E V)

@[expose] noncomputable def permOp (σ : ι → ι) : V →ₗ[E] V := b.constr E (fun i => b (σ i))

omit [Fintype ι] [DecidableEq ι] in
theorem permOp_apply (σ : ι → ι) (i : ι) : permOp b σ (b i) = b (σ i) := by
  simp only [permOp, Basis.constr_basis]

omit [Fintype ι] [DecidableEq ι] in
theorem permOp_mul_self {σ : ι → ι} (hσ : ∀ i, σ (σ i) = i) : permOp b σ * permOp b σ = 1 := by
  refine b.ext fun i => ?_
  rw [Module.End.mul_apply, permOp_apply, permOp_apply, hσ, Module.End.one_apply]

theorem permOp_isometry (hG : ∀ i j, B (b i) (b j) = if i = j then 1 else 0) {σ : ι → ι}
    (hσ : ∀ i, σ (σ i) = i) : ∀ x y, B (permOp b σ x) (permOp b σ y) = B x y := by
  refine isometry_of_basis b _ fun i j => ?_
  rw [permOp_apply, permOp_apply, hG, hG]
  have : σ i = σ j ↔ i = j := ⟨fun h => by rw [← hσ i, h, hσ], fun h => by rw [h]⟩
  simp only [this]

@[expose] noncomputable def permU (hG : ∀ i j, B (b i) (b j) = if i = j then 1 else 0) {σ : ι → ι}
    (hσ : ∀ i, σ (σ i) = i) : sesqUnitaryGroup B :=
  ⟨invGL (permOp b σ) (permOp_mul_self b hσ), fun x y => permOp_isometry b hG hσ x y⟩

theorem det_eq_one_or_neg_one_of_mul_self {s : V →ₗ[E] V} (hs : s * s = 1) [Module.Finite E V] :
    LinearMap.det s = 1 ∨ LinearMap.det s = -1 := by
  have h1 : LinearMap.det s * LinearMap.det s = 1 := by rw [← map_mul, hs, map_one]
  exact mul_self_eq_one_iff.1 h1

end Perm

section SignMk

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι E V)
  (hG : ∀ i j, B (b i) (b j) = if i = j then 1 else 0)

theorem signU_mul_self (S : Finset ι) : signU b hG S * signU b hG S = 1 :=
  Subtype.ext (Units.ext (signOp_mul_self b S))

theorem mk_signU_mul_self (S : Finset ι) :
    (QuotientGroup.mk (signU b hG S) : sesqProjUnitary h B) * QuotientGroup.mk (signU b hG S) = 1 := by
  rw [← QuotientGroup.mk_mul, signU_mul_self, QuotientGroup.mk_one]

theorem signU_not_mem_Z (h2 : (2 : E) ≠ 0) {S : Finset ι} {i j : ι} (hi : i ∈ S) (hj : j ∉ S) :
    signU b hG S ∉ sesqNormOneScalars h B := by
  rintro ⟨c, -, hc⟩
  have hc' : unitaryOp (signU b hG S) = c • 1 := hc
  have h1 := LinearMap.congr_fun hc' (b i)
  have h2' := LinearMap.congr_fun hc' (b j)
  rw [unitaryOp_signU, signOp_apply] at h1 h2'
  simp only [hi, hj, ite_true, ite_false, LinearMap.smul_apply, Module.End.one_apply] at h1 h2'
  have hbi : b i ≠ 0 := b.ne_zero i
  have hbj : b j ≠ 0 := b.ne_zero j
  have h3 : (c + 1) • b i = 0 := by rw [add_smul, one_smul, ← h1]; simp
  have h4 : (c - 1) • b j = 0 := by rw [sub_smul, one_smul, ← h2']; simp
  have hc1 : c = -1 := by
    have := (smul_eq_zero.mp h3).resolve_right hbi
    linear_combination this
  have hc2 : c = 1 := by
    have := (smul_eq_zero.mp h4).resolve_right hbj
    linear_combination this
  apply h2
  linear_combination hc1 - hc2

theorem mk_signU_ne_one (h2 : (2 : E) ≠ 0) {S : Finset ι} {i j : ι} (hi : i ∈ S) (hj : j ∉ S) :
    (QuotientGroup.mk (signU b hG S) : sesqProjUnitary h B) ≠ 1 := fun h1 =>
  signU_not_mem_Z b hG h2 hi hj ((QuotientGroup.eq_one_iff _).1 h1)

theorem mk_signU_mem_projSpecial {S : Finset ι} (hS : Even S.card) :
    (QuotientGroup.mk (signU b hG S) : sesqProjUnitary h B) ∈
      CFSG.ComponentClassification.CatalogueBUnitaryB.projSpecial h B := by
  refine Subgroup.mem_map_of_mem (QuotientGroup.mk' (sesqNormOneScalars h B)) ?_
  rw [CFSG.ComponentClassification.CatalogueBUnitaryB.mem_unitarySpecial]
  show LinearMap.det (signOp b S) = 1
  rw [det_signOp, hS.neg_one_pow]

theorem mk_signU_ne_mk (h2 : (2 : E) ≠ 0) {S : Finset ι} {i j : ι} (hi : i ∈ S) (hj : j ∉ S)
    {T : sesqUnitaryGroup B} {μ : E} (hμ : μ ≠ 0) (hTi : unitaryOp T (b i) = μ • b i)
    (hTj : unitaryOp T (b j) = μ • b j) :
    (QuotientGroup.mk (signU b hG S) : sesqProjUnitary h B) ≠ QuotientGroup.mk T := by
  intro heq
  obtain ⟨c, -, hTc⟩ := exists_scalar_of_mk_eq heq
  have h1 := hTc (b i)
  have h2' := hTc (b j)
  rw [hTi, unitaryOp_signU, signOp_apply] at h1
  rw [hTj, unitaryOp_signU, signOp_apply] at h2'
  simp only [hi, hj, ite_true, ite_false, neg_smul, one_smul] at h1 h2'
  have hbi : b i ≠ 0 := b.ne_zero i
  have hbj : b j ≠ 0 := b.ne_zero j
  have h3 : (μ + c) • b i = 0 := by rw [add_smul, h1]; simp
  have h4 : (μ - c) • b j = 0 := by rw [sub_smul, h2']; simp
  have hc1 := (smul_eq_zero.mp h3).resolve_right hbi
  have hc2 := (smul_eq_zero.mp h4).resolve_right hbj
  apply hμ
  have : (2 : E) * μ = 0 := by linear_combination hc1 + hc2
  exact (mul_eq_zero.mp this).resolve_left h2

theorem signU_comm (S S' : Finset ι) :
    signU b hG S * signU b hG S' = signU b hG S' * signU b hG S := by
  refine Subtype.ext (Units.ext (b.ext fun i => ?_))
  show signOp b S (signOp b S' (b i)) = signOp b S' (signOp b S (b i))
  simp only [signOp_apply, map_smul, smul_smul, mul_comm]

theorem mk_signU_ne_mk_signU (h2 : (2 : E) ≠ 0) {S S' : Finset ι} {i j : ι} (hi : i ∈ S)
    (hi' : i ∉ S') (hj : j ∉ S) (hj' : j ∉ S') :
    (QuotientGroup.mk (signU b hG S) : sesqProjUnitary h B) ≠ QuotientGroup.mk (signU b hG S') := by
  intro heq
  obtain ⟨c, -, hTc⟩ := exists_scalar_of_mk_eq heq
  have h1 := hTc (b i)
  have h2' := hTc (b j)
  rw [unitaryOp_signU, unitaryOp_signU, signOp_apply, signOp_apply] at h1 h2'
  simp only [hi, hi', hj, hj', ite_true, ite_false, one_smul, smul_neg, neg_smul] at h1 h2'
  have hbi : b i ≠ 0 := b.ne_zero i
  have hbj : b j ≠ 0 := b.ne_zero j
  have h3 : (1 + c) • b i = 0 := by
    rw [add_smul, one_smul]
    nth_rewrite 1 [h1]
    exact neg_add_cancel _
  have h4 : (c - 1) • b j = 0 := by rw [sub_smul, one_smul, ← h2']; simp
  have hc1 := (smul_eq_zero.mp h3).resolve_right hbi
  have hc2 := (smul_eq_zero.mp h4).resolve_right hbj
  apply h2
  linear_combination hc1 - hc2

end SignMk

section Adapted

variable {A W : Submodule E V} (Q : AdaptedONB B A W) (hc : IsCompl A W)

theorem AdaptedONB.coord_A {a : V} (ha : a ∈ A) :
    ∃ c : Fin (finrank E A) → E, a = ∑ i, c i • Q.b hc (Sum.inl i) := by
  refine ⟨fun i => Q.ea.repr ⟨a, ha⟩ i, ?_⟩
  have h1 := congrArg Subtype.val (Q.ea.sum_repr ⟨a, ha⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
  exact h1.symm.trans (Finset.sum_congr rfl fun i _ => by rw [AdaptedONB.b_inl])

theorem AdaptedONB.coord_W {w : V} (hw : w ∈ W) :
    ∃ c : Fin (finrank E W) → E, w = ∑ j, c j • Q.b hc (Sum.inr j) := by
  refine ⟨fun j => Q.ew.repr ⟨w, hw⟩ j, ?_⟩
  have h1 := congrArg Subtype.val (Q.ew.sum_repr ⟨w, hw⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
  exact h1.symm.trans (Finset.sum_congr rfl fun j _ => by rw [AdaptedONB.b_inr])

theorem AdaptedONB.signOp_fix_W {S : Finset (Fin (finrank E A) ⊕ Fin (finrank E W))}
    (hS : ∀ j, Sum.inr j ∉ S) {w : V} (hw : w ∈ W) : signOp (Q.b hc) S w = w := by
  obtain ⟨c, rfl⟩ := Q.coord_W hc hw
  simp only [map_sum, map_smul, signOp_apply, hS, ite_false, one_smul]

theorem AdaptedONB.signOp_fix_A {S : Finset (Fin (finrank E A) ⊕ Fin (finrank E W))}
    (hS : ∀ i, Sum.inl i ∉ S) {a : V} (ha : a ∈ A) : signOp (Q.b hc) S a = a := by
  obtain ⟨c, rfl⟩ := Q.coord_A hc ha
  simp only [map_sum, map_smul, signOp_apply, hS, ite_false, one_smul]

theorem AdaptedONB.signOp_mem_A (S : Finset (Fin (finrank E A) ⊕ Fin (finrank E W))) {a : V}
    (ha : a ∈ A) : signOp (Q.b hc) S a ∈ A := by
  obtain ⟨c, rfl⟩ := Q.coord_A hc ha
  rw [map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul, signOp_apply, AdaptedONB.b_inl]
  exact A.smul_mem _ (A.smul_mem _ (Q.ea i).2)

theorem AdaptedONB.signOp_mem_W (S : Finset (Fin (finrank E A) ⊕ Fin (finrank E W))) {w : V}
    (hw : w ∈ W) : signOp (Q.b hc) S w ∈ W := by
  obtain ⟨c, rfl⟩ := Q.coord_W hc hw
  rw [map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [map_smul, signOp_apply, AdaptedONB.b_inr]
  exact W.smul_mem _ (W.smul_mem _ (Q.ew j).2)

theorem AdaptedONB.det_restrict_signOp (S₀ : Finset (Fin (finrank E A)))
    (hA : ∀ a ∈ A, signOp (Q.b hc) (S₀.map Function.Embedding.inl) a ∈ A) :
    LinearMap.det ((signOp (Q.b hc) (S₀.map Function.Embedding.inl)).restrict hA) =
      (-1) ^ S₀.card := by
  have h1 : LinearMap.toMatrix Q.ea Q.ea ((signOp (Q.b hc) (S₀.map Function.Embedding.inl)).restrict hA)
      = FourGroupOddBilinear.signDiag S₀ := by
    rw [toMatrix_eq_diagonal Q.ea (μ := fun i => if i ∈ S₀ then (-1 : E) else 1)]
    · rfl
    · intro i
      apply Subtype.ext
      show signOp (Q.b hc) (S₀.map Function.Embedding.inl) (Q.ea i : V) =
        (if i ∈ S₀ then (-1 : E) else 1) • (Q.ea i : V)
      rw [← AdaptedONB.b_inl Q hc i, signOp_apply]
      simp
  rw [← LinearMap.det_toMatrix Q.ea, h1, FourGroupOddBilinear.det_signDiag]

theorem AdaptedONB.signU_A_mem (hG : ∀ α β, B (Q.b hc α) (Q.b hc β) = if α = β then 1 else 0)
    (S₀ : Finset (Fin (finrank E A))) (hS : Even S₀.card) :
    signU (Q.b hc) hG (S₀.map Function.Embedding.inl) ∈ summandUnitarySet B A W := by
  refine ⟨fun w hw => Q.signOp_fix_W hc (fun j => by simp) hw,
    fun a ha => Q.signOp_mem_A hc _ ha, ?_⟩
  show LinearMap.det ((signOp (Q.b hc) (S₀.map Function.Embedding.inl)).restrict _) = 1
  rw [Q.det_restrict_signOp hc, hS.neg_one_pow]

theorem AdaptedONB.signU_W_commute (hG : ∀ α β, B (Q.b hc α) (Q.b hc β) = if α = β then 1 else 0)
    {g : sesqUnitaryGroup B} (hg : g ∈ summandUnitarySet B A W)
    (S₁ : Finset (Fin (finrank E W))) :
    g * signU (Q.b hc) hG (S₁.map Function.Embedding.inr) =
      signU (Q.b hc) hG (S₁.map Function.Embedding.inr) * g := by
  obtain ⟨hgW, hgA, -⟩ := hg
  refine Subtype.ext (Units.ext (LinearMap.ext fun v => ?_))
  obtain ⟨a, w, ha, hw, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint v
  have hfa : signOp (Q.b hc) (S₁.map Function.Embedding.inr) a = a :=
    Q.signOp_fix_A hc (fun i => by simp) ha
  have hsw := Q.signOp_mem_W hc (S₁.map Function.Embedding.inr) hw
  have hga := hgA a ha
  have hfga : signOp (Q.b hc) (S₁.map Function.Embedding.inr) (unitaryOp g a) = unitaryOp g a :=
    Q.signOp_fix_A hc (fun i => by simp) hga
  show unitaryOp g (signOp (Q.b hc) (S₁.map Function.Embedding.inr) (a + w)) =
    signOp (Q.b hc) (S₁.map Function.Embedding.inr) (unitaryOp g (a + w))
  rw [map_add, map_add, map_add, hfa, map_add, hgW _ hw, hfga, hgW _ hsw]

theorem summand_commute (hc : IsCompl A W) {g₁ g₂ : sesqUnitaryGroup B}
    (h₁W : ∀ w ∈ W, unitaryOp g₁ w = w) (h₁A : ∀ a ∈ A, unitaryOp g₁ a ∈ A)
    (h₂A : ∀ a ∈ A, unitaryOp g₂ a = a) (h₂W : ∀ w ∈ W, unitaryOp g₂ w ∈ W) :
    g₁ * g₂ = g₂ * g₁ := by
  refine Subtype.ext (Units.ext (LinearMap.ext fun v => ?_))
  obtain ⟨a, w, ha, hw, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint v
  show unitaryOp g₁ (unitaryOp g₂ (a + w)) = unitaryOp g₂ (unitaryOp g₁ (a + w))
  rw [map_add, map_add, map_add, map_add, h₂A _ ha, h₁W _ hw, h₂A _ (h₁A _ ha), h₁W _ (h₂W _ hw)]

theorem swap_inv (hc : IsCompl A W) {s : sesqUnitaryGroup B}
    (hsA : ∀ a ∈ A, unitaryOp s a ∈ W) (hsW : ∀ w ∈ W, unitaryOp s w ∈ A) :
    (∀ a ∈ A, unitaryOp s⁻¹ a ∈ W) ∧ (∀ w ∈ W, unitaryOp s⁻¹ w ∈ A) := by
  have key : ∀ {P R : Submodule E V}, IsCompl P R → (∀ a ∈ P, unitaryOp s a ∈ R) →
      (∀ w ∈ R, unitaryOp s w ∈ P) → ∀ a ∈ P, unitaryOp s⁻¹ a ∈ R := by
    intro P R hPR hsP hsR a ha
    obtain ⟨a', w', ha', hw', hdec⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hPR.codisjoint
      (unitaryOp s⁻¹ a)
    have h1 : a = unitaryOp s a' + unitaryOp s w' := by
      rw [← map_add, hdec, unitaryOp_apply_inv]
    have h2 : unitaryOp s a' = a - unitaryOp s w' := by rw [h1]; abel
    have h3 : unitaryOp s a' ∈ P := h2 ▸ P.sub_mem ha (hsR _ hw')
    have h4 : unitaryOp s a' = 0 := by
      exact (Submodule.disjoint_def.mp hPR.disjoint.symm) _ (hsP _ ha') h3 
    have h5 : a' = 0 := unitaryOp_injective s (by rw [h4, map_zero])
    rw [← hdec, h5, zero_add]
    exact hw'
  exact ⟨key hc hsA hsW, key hc.symm hsW hsA⟩

@[expose] noncomputable def swapIdx (hAW : finrank E A = finrank E W) :
    Fin (finrank E A) ⊕ Fin (finrank E W) → Fin (finrank E A) ⊕ Fin (finrank E W) :=
  Sum.elim (fun i => Sum.inr (finCongr hAW i)) (fun j => Sum.inl ((finCongr hAW).symm j))

theorem swapIdx_invol (hAW : finrank E A = finrank E W) (α : Fin (finrank E A) ⊕ Fin (finrank E W)) :
    swapIdx hAW (swapIdx hAW α) = α := by
  rcases α with i | j <;> simp [swapIdx]

theorem AdaptedONB.permOp_mem_W (hAW : finrank E A = finrank E W) {a : V} (ha : a ∈ A) :
    permOp (Q.b hc) (swapIdx hAW) a ∈ W := by
  obtain ⟨c, rfl⟩ := Q.coord_A hc ha
  rw [map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul, permOp_apply]
  simp only [swapIdx, Sum.elim_inl, AdaptedONB.b_inr]
  exact W.smul_mem _ (Q.ew _).2

theorem AdaptedONB.permOp_mem_A (hAW : finrank E A = finrank E W) {w : V} (hw : w ∈ W) :
    permOp (Q.b hc) (swapIdx hAW) w ∈ A := by
  obtain ⟨c, rfl⟩ := Q.coord_W hc hw
  rw [map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [map_smul, permOp_apply]
  simp only [swapIdx, Sum.elim_inr, AdaptedONB.b_inl]
  exact A.smul_mem _ (Q.ea _).2

theorem AdaptedONB.permOp_anticomm (hAW : finrank E A = finrank E W) {T : V →ₗ[E] V} {μ : E}
    (hTA : ∀ a ∈ A, T a = μ • a) (hTW : ∀ w ∈ W, T w = -(μ • w)) :
    T * permOp (Q.b hc) (swapIdx hAW) = -(permOp (Q.b hc) (swapIdx hAW) * T) := by
  refine (Q.b hc).ext fun α => ?_
  rcases α with i | j
  · have h1 : T (Q.b hc (Sum.inl i)) = μ • Q.b hc (Sum.inl i) := by
      rw [AdaptedONB.b_inl]; exact hTA _ (Q.ea i).2
    have h2 : T (Q.b hc (Sum.inr (finCongr hAW i))) = -(μ • Q.b hc (Sum.inr (finCongr hAW i))) := by
      rw [AdaptedONB.b_inr]; exact hTW _ (Q.ew _).2
    simp only [Module.End.mul_apply, LinearMap.neg_apply, permOp_apply, swapIdx, Sum.elim_inl, h1, h2,
      map_smul]
  · have h1 : T (Q.b hc (Sum.inr j)) = -(μ • Q.b hc (Sum.inr j)) := by
      rw [AdaptedONB.b_inr]; exact hTW _ (Q.ew j).2
    have h2 : T (Q.b hc (Sum.inl ((finCongr hAW).symm j))) =
        μ • Q.b hc (Sum.inl ((finCongr hAW).symm j)) := by
      rw [AdaptedONB.b_inl]; exact hTA _ (Q.ea _).2
    simp only [Module.End.mul_apply, LinearMap.neg_apply, permOp_apply, swapIdx, Sum.elim_inr, h1, h2,
      map_smul, map_neg, neg_neg]

theorem AdaptedONB.comm_signOp {T : V →ₗ[E] V} {μ : E} (hTA : ∀ a ∈ A, T a = μ • a)
    (hTW : ∀ w ∈ W, T w = -(μ • w)) (S : Finset (Fin (finrank E A) ⊕ Fin (finrank E W))) :
    T * signOp (Q.b hc) S = signOp (Q.b hc) S * T := by
  refine (Q.b hc).ext fun α => ?_
  rcases α with i | j
  · have h1 : T (Q.b hc (Sum.inl i)) = μ • Q.b hc (Sum.inl i) := by
      rw [AdaptedONB.b_inl]; exact hTA _ (Q.ea i).2
    simp only [Module.End.mul_apply, signOp_apply, map_smul, h1]
    rw [smul_comm]
  · have h1 : T (Q.b hc (Sum.inr j)) = -(μ • Q.b hc (Sum.inr j)) := by
      rw [AdaptedONB.b_inr]; exact hTW _ (Q.ew j).2
    simp only [Module.End.mul_apply, signOp_apply, map_smul, h1, map_neg, smul_neg]
    rw [smul_comm]

theorem AdaptedONB.exists_swap [FiniteDimensional E V]
    (hG : ∀ α β, B (Q.b hc α) (Q.b hc β) = if α = β then 1 else 0)
    (hAW : finrank E A = finrank E W) (hA0 : 0 < finrank E A) {T : sesqUnitaryGroup B} {μ : E}
    (hTA : ∀ a ∈ A, unitaryOp T a = μ • a) (hTW : ∀ w ∈ W, unitaryOp T w = -(μ • w)) :
    ∃ s : sesqUnitaryGroup B, (∀ a ∈ A, unitaryOp s a ∈ W) ∧ (∀ w ∈ W, unitaryOp s w ∈ A) ∧
      LinearMap.det (unitaryOp s) = 1 ∧ unitaryOp T * unitaryOp s = -(unitaryOp s * unitaryOp T) := by
  set s₀ := permU (Q.b hc) hG (swapIdx_invol hAW) with hs₀
  have hs₀op : unitaryOp s₀ = permOp (Q.b hc) (swapIdx hAW) := rfl
  have hs₀A : ∀ a ∈ A, unitaryOp s₀ a ∈ W := fun a ha => by
    rw [hs₀op]; exact Q.permOp_mem_W hc hAW ha
  have hs₀W : ∀ w ∈ W, unitaryOp s₀ w ∈ A := fun w hw => by
    rw [hs₀op]; exact Q.permOp_mem_A hc hAW hw
  have hs₀T : unitaryOp T * unitaryOp s₀ = -(unitaryOp s₀ * unitaryOp T) := by
    rw [hs₀op]; exact Q.permOp_anticomm hc hAW hTA hTW
  have hdet : LinearMap.det (unitaryOp s₀) = 1 ∨ LinearMap.det (unitaryOp s₀) = -1 := by
    refine det_eq_one_or_neg_one_of_mul_self ?_
    rw [hs₀op]; exact permOp_mul_self _ (swapIdx_invol hAW)
  rcases hdet with hd | hd
  · exact ⟨s₀, hs₀A, hs₀W, hd, hs₀T⟩
  · set x := signU (Q.b hc) hG {Sum.inl (⟨0, hA0⟩ : Fin (finrank E A))} with hx
    have hxop : unitaryOp x = signOp (Q.b hc) {Sum.inl (⟨0, hA0⟩ : Fin (finrank E A))} := rfl
    refine ⟨s₀ * x, fun a ha => ?_, fun w hw => ?_, ?_, ?_⟩
    · show unitaryOp s₀ (unitaryOp x a) ∈ W
      rw [hxop]
      exact hs₀A _ (Q.signOp_mem_A hc _ ha)
    · show unitaryOp s₀ (unitaryOp x w) ∈ A
      rw [hxop, Q.signOp_fix_W hc (fun j => by simp) hw]
      exact hs₀W _ hw
    · show LinearMap.det (unitaryOp s₀ * unitaryOp x) = 1
      rw [map_mul, hd, hxop, det_signOp]
      simp
    · show unitaryOp T * (unitaryOp s₀ * unitaryOp x) = -((unitaryOp s₀ * unitaryOp x) * unitaryOp T)
      have hcomm : unitaryOp T * unitaryOp x = unitaryOp x * unitaryOp T := by
        rw [hxop]; exact Q.comm_signOp hc hTA hTW _
      rw [← mul_assoc, hs₀T, neg_mul, mul_assoc, hcomm, ← mul_assoc]

end Adapted

end Basis

end CFSG.GH74.GLS.IVK.Proofs2
