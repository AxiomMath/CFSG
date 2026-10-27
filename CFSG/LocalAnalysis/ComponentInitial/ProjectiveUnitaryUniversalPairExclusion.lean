module

public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveUnitaryLocalComponent
public import CFSG.LocalAnalysis.ComponentInitial.OddProjectivePairExclusion
public import CFSG.LocalAnalysis.ComponentInitial.FourGroupOddUnitary

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Module Subgroup CFSG.ComponentClassification
open CFSG.LocalAnalysis.ComponentInitial.OddProjectivePair
open CFSG.LocalAnalysis.ComponentInitial.FourGroupOddUnitary (matrixGL coe_matrixGL
  matrixGL_mem_special)

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]
  {h : UnitaryFieldData p f E} {B : V →ₛₗ[h.bar] V →ₗ[E] E}

namespace UnitaryPair

theorem end_eq_one_or_neg_one {A : Type*} [AddCommGroup A] [Module E A] [FiniteDimensional E A]
    (htwo : (2 : E) ≠ 0) (hA : finrank E A = 2) {x : Module.End E A} (hx : x * x = 1)
    (hdet : LinearMap.det x = 1) : x = 1 ∨ x = -1 := by
  let b : Basis (Fin 2) E A := Module.finBasisOfFinrankEq E A hA
  have hM : LinearMap.toMatrix b b x * LinearMap.toMatrix b b x = 1 := by
    rw [← LinearMap.toMatrix_mul, hx, LinearMap.toMatrix_one]
  have hdetM : (LinearMap.toMatrix b b x).det = 1 := by rw [LinearMap.det_toMatrix, hdet]
  rcases fin_two_eq_one_or_eq_neg_one htwo hM hdetM with h1 | h1
  · left
    apply (LinearMap.toMatrix b b).injective
    rw [h1, LinearMap.toMatrix_one]
  · right
    apply (LinearMap.toMatrix b b).injective
    rw [h1, map_neg, LinearMap.toMatrix_one]

theorem eq_of_isCompl {A W : Submodule E V} (hAW : IsCompl A W) {x y : sesqUnitaryGroup B}
    (hA : ∀ a ∈ A, unitaryOp x a = unitaryOp y a)
    (hW : ∀ w ∈ W, unitaryOp x w = unitaryOp y w) : x = y := by
  refine Subtype.ext (Units.ext (LinearMap.ext fun v => ?_))
  obtain ⟨a, ha, w, hw, rfl⟩ :=
    Submodule.mem_sup.1 (hAW.sup_eq_top ▸ Submodule.mem_top : v ∈ A ⊔ W)
  change unitaryOp x (a + w) = unitaryOp y (a + w)
  rw [map_add, map_add, hA a ha, hW w hw]

theorem eq_of_mem_summandUnitarySet_of_finrank_eq_two [FiniteDimensional E V]
    (htwo : (2 : E) ≠ 0) {A W : Submodule E V} (hAW : IsCompl A W) (hA2 : finrank E A = 2)
    {x y : sesqUnitaryGroup B} (hx : x ∈ summandUnitarySet B A W)
    (hy : y ∈ summandUnitarySet B A W) (hx2 : x * x = 1) (hy2 : y * y = 1) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) : x = y := by
  have hneg : ∀ z : sesqUnitaryGroup B, z ∈ summandUnitarySet B A W → z * z = 1 → z ≠ 1 →
      ∀ a ∈ A, unitaryOp z a = -a := by
    intro z hz hz2 hz1
    obtain ⟨hzW, hzA, hdet⟩ := hz
    have hzz : unitaryOp z * unitaryOp z = 1 := congrArg unitaryOp hz2
    have hrr : (unitaryOp z).restrict hzA * (unitaryOp z).restrict hzA = 1 :=
      LinearMap.ext fun a => Subtype.ext (by
        change unitaryOp z (unitaryOp z a) = a
        rw [← Module.End.mul_apply, hzz, Module.End.one_apply])
    rcases end_eq_one_or_neg_one htwo hA2 hrr hdet with h1 | h1
    · exfalso
      refine hz1 (eq_of_isCompl hAW (fun a ha => ?_) fun w hw => ?_)
      · have h2 := congrArg (fun φ : Module.End E A => (φ ⟨a, ha⟩ : V)) h1
        simp only [LinearMap.restrict_apply, Module.End.one_apply] at h2
        exact h2
      · rw [hzW w hw]
        rfl
    · intro a ha
      have h2 := congrArg (fun φ : Module.End E A => (φ ⟨a, ha⟩ : V)) h1
      simpa using h2
  exact eq_of_isCompl hAW (fun a ha => by rw [hneg x hx hx2 hx1 a ha, hneg y hy hy2 hy1 a ha])
    fun w hw => by rw [hx.1 w hw, hy.1 w hw]

theorem exists_summand_diagonal (hB : B.IsSymm) {A W : Submodule E V} (hc : IsCompl A W)
    (horth : ∀ a ∈ A, ∀ w ∈ W, B a w = 0) {r : ℕ} (b : Basis (Fin r) E A)
    (hb : ∀ i j, B.domRestrict₁₂ A A (b i) (b j) = if i = j then 1 else 0)
    (d : Fin r → E) (hd : ∀ i, d i * d i = 1) (hprod : ∏ i, d i = 1) :
    ∃ S : sesqUnitaryGroup B, S ∈ summandUnitarySet B A W ∧ S * S = 1 ∧
      (∀ i, unitaryOp S (b i) = d i • (b i : V)) ∧ ∀ w ∈ W, unitaryOp S w = w := by
  classical
  set X : Matrix (Fin r) (Fin r) E := Matrix.diagonal d with hX
  have hdet : X.det = 1 := by rw [hX, Matrix.det_diagonal, hprod]
  have hd' : ∀ i, d i = 1 ∨ d i = -1 := fun i => mul_self_eq_one_iff.1 (hd i)
  have hXσ : ∀ i j, h.bar (X i j) = X i j := by
    intro i j
    rw [hX, Matrix.diagonal_apply]
    split_ifs
    · rcases hd' i with h1 | h1 <;> rw [h1] <;> simp
    · exact map_zero _
  have hXX : X * X = 1 := by
    rw [hX, Matrix.diagonal_mul_diagonal,
      show (fun i => d i * d i) = fun _ => (1 : E) from funext hd, Matrix.diagonal_one]
  have hXG : X.transpose * 1 * X = 1 := by
    rw [hX, Matrix.diagonal_transpose, Matrix.mul_one, ← hX, hXX]
  have hG : ∀ i j, B.domRestrict₁₂ A A (b i) (b j) = (1 : Matrix (Fin r) (Fin r) E) i j :=
    fun i j => by rw [hb, Matrix.one_apply]
  set gA := matrixGL b X (by rw [hdet]; exact one_ne_zero) with hgAdef
  have hgA : gA ∈ sesqSpecialUnitaryGroup (B.domRestrict₁₂ A A) :=
    matrixGL_mem_special b 1 hG hdet hXσ hXG
  obtain ⟨hmem, hS⟩ := glConj_symm_summandGL_mem hB hc horth hgA
  set Ψ := Submodule.prodEquivOfIsCompl A W hc with hΨ
  set S : sesqUnitaryGroup B := ⟨_, hmem⟩ with hSdef
  have happ : ∀ v, unitaryOp S v =
      Ψ ((summandGL E A W gA : A × W →ₗ[E] A × W) (Ψ.symm v)) := fun v => by
    change ((glConj Ψ.symm (summandGL E A W gA) : LinearMap.GeneralLinearGroup E V) :
      Module.End E V) v = _
    rw [glConj_apply, LinearEquiv.symm_symm]
  have hW : ∀ w ∈ W, unitaryOp S w = w := fun w hw => by
    rw [happ, show Ψ.symm w = (0, ⟨w, hw⟩) from
      Submodule.prodEquivOfIsCompl_symm_apply_right A W hc ⟨w, hw⟩, summandGL_apply, map_zero,
      Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, zero_add]
  have hA : ∀ a (ha : a ∈ A), unitaryOp S a =
      (((gA : LinearMap.GeneralLinearGroup E A) : Module.End E A) ⟨a, ha⟩ : V) := fun a ha => by
    rw [happ, show Ψ.symm a = (⟨a, ha⟩, 0) from
      Submodule.prodEquivOfIsCompl_symm_apply_left A W hc ⟨a, ha⟩, summandGL_apply,
      Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, add_zero]
  have hgAb : ∀ i, ((gA : LinearMap.GeneralLinearGroup E A) : Module.End E A) (b i) =
      d i • b i := fun i => by
    rw [hgAdef, coe_matrixGL, Matrix.toLin_self]
    simp [hX, Matrix.diagonal_apply]
  have hgAA : ∀ x : A, ((gA : LinearMap.GeneralLinearGroup E A) : Module.End E A)
      (((gA : LinearMap.GeneralLinearGroup E A) : Module.End E A) x) = x := fun x => by
    rw [hgAdef, coe_matrixGL, ← LinearMap.comp_apply, ← Matrix.toLin_mul, hXX, Matrix.toLin_one,
      LinearMap.id_apply]
  refine ⟨S, hS, ?_, fun i => ?_, hW⟩
  · refine eq_of_isCompl hc (fun a ha => ?_) fun w hw => ?_
    · change unitaryOp S (unitaryOp S a) = a
      rw [hA a ha, hA _ (Submodule.coe_mem _), Subtype.coe_eta, hgAA]
    · change unitaryOp S (unitaryOp S w) = w
      rw [hW w hw, hW w hw]
  · rw [hA _ (b i).2, Subtype.coe_eta, hgAb, Submodule.coe_smul]

end UnitaryPair

open UnitaryPair

theorem odd_projective_unitary_commuting_universal_pair_exclusion (h : UnitaryFieldData p f E)
    (hp : p ≠ 2) [FiniteDimensional E V] (hn : 2 ≤ finrank E V) {B : V →ₛₗ[h.bar] V →ₗ[E] E}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) :
    ¬ ∃ B₁ B₂ : Subgroup (sesqProjUnitary h B),
      CFSG.Assembly.IsQuasisimple B₁ ∧ CFSG.Assembly.IsQuasisimple B₂ ∧ ⁅B₁, B₂⁆ = ⊥ ∧
      (∃ V₁ : Subgroup (sesqProjUnitary h B), V₁ ≤ B₁ ∧ CFSG.IsElementaryAbelian 2 V₁ ∧
        Nat.card V₁ = 4) ∧
      (∃ V₂ : Subgroup (sesqProjUnitary h B), V₂ ≤ B₂ ∧ CFSG.IsElementaryAbelian 2 V₂ ∧
        Nat.card V₂ = 4) ∧
      (∀ t ∈ B₂, orderOf t = 2 → CFSG.Assembly.IsComponentOf B₁
        (centralizer ({t} : Set (sesqProjUnitary h B)))) ∧
      (∀ s ∈ B₁, orderOf s = 2 → CFSG.Assembly.IsComponentOf B₂
        (centralizer ({s} : Set (sesqProjUnitary h B)))) := by
  rintro ⟨B₁, B₂, hq₁, hq₂, hcomm, ⟨V₁, hV₁, hV₁e, hV₁c⟩, ⟨V₂, hV₂, hV₂e, hV₂c⟩, h₁, h₂⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htwo := two_ne_zero_of_odd h hp
  set π := QuotientGroup.mk' (sesqNormOneScalars h B) with hπ
  have hB₁p := commutator_eq_self_of_isQuasisimple hq₁
  have hB₂p := commutator_eq_self_of_isQuasisimple hq₂
  have hB₁ne := ne_bot_of_card_eq_four hV₁ hV₁c
  have hB₂ne := ne_bot_of_card_eq_four hV₂ hV₂c
  have hB₁B₂ : B₁ ≤ centralizer (B₂ : Set (sesqProjUnitary h B)) :=
    commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hB₂B₁ : B₂ ≤ centralizer (B₁ : Set (sesqProjUnitary h B)) :=
    commutator_eq_bot_iff_le_centralizer.1 (by rw [commutator_comm]; exact hcomm)
  set B₁hat := ⁅B₁.comap π, B₁.comap π⁆ with hB₁hat
  have hmk₁ : ∀ g ∈ B₁hat, π g ∈ B₁ := fun g hg => commutator_le_self (B₁.comap π) hg
  obtain ⟨t, htV, -, -, ht1, -, -⟩ := exists_ne_one_ne_one_ne hV₂c
  have ht2 : t ^ 2 = 1 := by
    have := hV₂e
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V₂) t htV
  have htB₂ : t ∈ B₂ := hV₂ htV
  obtain ⟨T, hT⟩ := QuotientGroup.mk'_surjective (sesqNormOneScalars h B) t
  have hC₁ := h₁ t htB₂ (orderOf_eq_prime ht2 ht1)
  have hBcomp₁ := (isComponentOf_iff_isComponent_subgroupOf hC₁.1).1 hC₁
  have hmap₁ : ((B₁.subgroupOf (centralizer {t})).map (centralizer {t}).subtype :
      Subgroup (sesqProjUnitary h B)) = B₁ := map_subgroupOf_eq_of_le hC₁.1
  obtain ⟨l, -, -, -, hP, hM, hcompl, horth, hndP, hndM, A, W, hAW, hdimA, hBhat, ⟨e, he⟩, -⟩ :=
    odd_projective_unitary_local_component_supported_on_eigenspace h hp hn hB hBl
      (orderOf_eq_prime ht2 ht1) hT hBcomp₁ (Q := B₂) (by rw [hmap₁]; exact hB₂B₁) hB₂ne hB₂p
  rw [hmap₁] at hBhat
  have hAWc : IsCompl A W := by
    rcases hAW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hcompl
    · exact hcompl.symm
  have hW0 : W ≠ ⊥ := by
    rcases hAW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hM
    · exact hP
  have hAWo : ∀ a ∈ A, ∀ w ∈ W, B a w = 0 := by
    rcases hAW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact horth
    · intro a ha w hw
      rw [← hB.eq, horth w hw a ha, map_zero]
  have hAnd : (B.domRestrict₁₂ A A).Nondegenerate := by
    rcases hAW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hndP
    · exact hndM
  have hmemB : ∀ g : sesqUnitaryGroup B, g ∈ summandUnitarySet B A W → g ∈ B₁hat := fun g hg => by
    rw [← SetLike.mem_coe, hBhat]
    exact hg
  have hmemB' : ∀ g : sesqUnitaryGroup B, g ∈ B₁hat → g ∈ summandUnitarySet B A W := fun g hg => by
    rw [← hBhat]
    exact hg
  have hr2 : finrank E A ≠ 2 := by
    intro hr
    obtain ⟨v, hv, v', hv', hv1, hv'1, hvv'⟩ := exists_ne_one_ne_one_ne hV₁c
    have hsq : ∀ w ∈ V₁, w * w = 1 := fun w hw => by
      have := hV₁e
      rw [← sq]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V₁) w hw
    have hlift : ∀ w ∈ V₁, ∃ x : sesqUnitaryGroup B, x ∈ B₁hat ∧ π x = w ∧ x * x = 1 := by
      intro w hw
      set y : B₁.subgroupOf (centralizer {t}) :=
        ⟨⟨w, hC₁.1 (hV₁ hw)⟩, by rw [mem_subgroupOf]; exact hV₁ hw⟩
      refine ⟨(e.symm y : sesqUnitaryGroup B), ?_, ?_, ?_⟩
      · have hK : ⁅((B₁.subgroupOf (centralizer {t})).map (centralizer {t}).subtype).comap π,
            ((B₁.subgroupOf (centralizer {t})).map (centralizer {t}).subtype).comap π⁆ =
            B₁hat := by rw [hmap₁]
        exact (Subgroup.ext_iff.1 hK _).1 (e.symm y).2
      · rw [← he, MulEquiv.apply_symm_apply]
      · have hy : y * y = 1 := Subtype.ext (Subtype.ext (hsq w hw))
        rw [← Subgroup.coe_mul, ← map_mul, hy, map_one, Subgroup.coe_one]
    obtain ⟨x, hxB, hxv, hx2⟩ := hlift v hv
    obtain ⟨x', hx'B, hx'v, hx'2⟩ := hlift v' hv'
    have hx1 : x ≠ 1 := fun h1 => hv1 (by rw [← hxv, h1, map_one])
    have hx'1 : x' ≠ 1 := fun h1 => hv'1 (by rw [← hx'v, h1, map_one])
    apply hvv'
    rw [← hxv, ← hx'v, eq_of_mem_summandUnitarySet_of_finrank_eq_two htwo hAWc hr
      (hmemB' x hxB) (hmemB' x' hx'B) hx2 hx'2 hx1 hx'1]
  have hr3 : 3 ≤ finrank E A := by omega
  have hAs : (B.domRestrict₁₂ A A).IsSymm := ⟨fun x y => hB.eq x y⟩
  obtain ⟨b, hb⟩ := h.exists_orthonormal_basis (M := A) (B := B.domRestrict₁₂ A A) hAs hAnd.1
  set i₀ : Fin (finrank E A) := ⟨0, by omega⟩
  set i₁ : Fin (finrank E A) := ⟨1, by omega⟩
  set i₂ : Fin (finrank E A) := ⟨2, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have h02 : i₀ ≠ i₂ := by simp [i₀, i₂, Fin.ext_iff]
  have h21 : i₂ ≠ i₁ := by simp [i₂, i₁, Fin.ext_iff]
  obtain ⟨S, hSS, hS2, hSb, hSW⟩ := exists_summand_diagonal hB hAWc hAWo b hb (signs i₀ i₁)
    (signs_mul_self i₀ i₁) (prod_signs i₀ i₁)
  obtain ⟨g, hgS, -, hgb, -⟩ := exists_summand_diagonal hB hAWc hAWo b hb (signs i₀ i₂)
    (signs_mul_self i₀ i₂) (prod_signs i₀ i₂)
  have hSmem : S ∈ B₁hat := hmemB S hSS
  have hgmem : g ∈ B₁hat := hmemB g hgS
  have hneg : ∀ v : V, -v = v → v = 0 := by
    intro v hv
    have h2v : (2 : E) • v = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← hv]
      exact neg_add_cancel v
    exact (smul_eq_zero.1 h2v).resolve_left htwo
  have hb0 : ∀ i, (b i : V) ≠ 0 := fun i h0 => b.ne_zero i (Subtype.ext h0)
  have hS0 : unitaryOp S (b i₀) = -(b i₀ : V) := by rw [hSb, signs_left h01, neg_one_smul]
  have hS2b : unitaryOp S (b i₂) = (b i₂ : V) := by rw [hSb, signs_of_ne h02.symm h21, one_smul]
  have hg2 : unitaryOp g (b i₂) = -(b i₂ : V) := by rw [hgb, signs_right h02, neg_one_smul]
  set s := π S with hsdef
  have hsB₁ : s ∈ B₁ := hmk₁ S hSmem
  have hs2 : s ^ 2 = 1 := by rw [hsdef, ← map_pow, sq, hS2, map_one]
  have hs1 : s ≠ 1 := by
    intro h1
    obtain ⟨c, -, hc⟩ := mem_sesqNormOneScalars.1 ((QuotientGroup.eq_one_iff S).1 h1)
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    have hcw := LinearMap.congr_fun hc w
    change unitaryOp S w = _ at hcw
    rw [hSW w hw, LinearMap.smul_apply, Module.End.one_apply] at hcw
    have hc1 : c = 1 := by
      have h3 : (c - 1) • w = 0 := by rw [sub_smul, ← hcw, one_smul, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right hw0)
    have hcb := LinearMap.congr_fun hc (b i₀ : V)
    change unitaryOp S (b i₀) = _ at hcb
    rw [hS0, LinearMap.smul_apply, Module.End.one_apply, hc1, one_smul] at hcb
    exact hb0 i₀ (hneg _ hcb)
  have hC₂ := h₂ s hsB₁ (orderOf_eq_prime hs2 hs1)
  have hBcomp₂ := (isComponentOf_iff_isComponent_subgroupOf hC₂.1).1 hC₂
  have hmap₂ : ((B₂.subgroupOf (centralizer {s})).map (centralizer {s}).subtype :
      Subgroup (sesqProjUnitary h B)) = B₂ := map_subgroupOf_eq_of_le hC₂.1
  obtain ⟨l', hl'0, hSS', -, -, -, -, -, -, -, A', W', hA'W', hdimA', -, -, hfix'⟩ :=
    odd_projective_unitary_local_component_supported_on_eigenspace h hp hn hB hBl
      (orderOf_eq_prime hs2 hs1) hsdef.symm hBcomp₂ (Q := B₁) (by rw [hmap₂]; exact hB₁B₂)
      hB₁ne hB₁p
  have hA'ne : A' ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at hdimA'
    omega
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA'ne
  have hSa : unitaryOp S a = a := hfix' S hSmem a ha
  have hb2A' : (b i₂ : V) ∈ A' := by
    rcases hA'W' with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · have h1 := LinearMap.mem_ker.1 ha
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hSa, sub_eq_zero]
        at h1
      have hl1 : l' = 1 := by
        have h3 : (1 - l') • a = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
        exact (sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right ha0)).symm
      refine LinearMap.mem_ker.2 ?_
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hS2b, hl1, one_smul,
        sub_self]
    · have h1 := LinearMap.mem_ker.1 ha
      rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, hSa] at h1
      have hl1 : l' = -1 := by
        have h3 : (1 + l') • a = 0 := by rw [add_smul, one_smul, h1]
        rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
        exact (smul_eq_zero.1 h3).resolve_right ha0
      refine LinearMap.mem_ker.2 ?_
      rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, hS2b, hl1,
        neg_one_smul, add_neg_cancel]
  apply hb0 i₂
  apply hneg
  rw [← hg2, hfix' g hgmem _ hb2A']

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
