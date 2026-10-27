module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsUniBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsLinLift
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.LinUnitUnitaryBlocks
import CFSG.RankThree.PartOne.KC.UnitaryNonsplitCount
import CFSG.GroupTheory.Fitting.LayerProjection
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutUnitaryField

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks
  (toLinSU toLinSU_injective mem_range_toLinSU)
open scoped Matrix

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem ringEquiv_eq_one_of_fix_bar (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : Odd p)
    (τ : K ≃+* K) (hτ : τ ^ p = 1) (hfix : ∀ k : K, h.bar k = k → τ k = k) : τ = 1 := by
  have hσ : Function.Involutive h.bar := h.bar_bar
  rcases CFSG.ComponentClassification.AschbacherToolkit.Bender.UnitaryField.eq_id_or_eq_conj_of_fix
    (RingEquiv.ofBijective h.bar hσ.bijective) hσ τ.toRingHom hfix with h1 | h1
  · ext k
    exact h1 k
  · have e1 : ∀ k, τ k = h.bar k := h1
    have h2 : τ ^ 2 = 1 := by
      ext k
      change τ (τ k) = k
      rw [e1, e1, h.bar_bar]
    have h3 := pow_gcd_eq_one.mpr ⟨h2, hτ⟩
    rwa [(Nat.coprime_two_left.mpr hp).gcd_eq_one, pow_one] at h3

theorem ringHom_eq_id_of_fix_pow (hK : UnitaryFieldData ℓ f K) {E : Type*} [Field E]
    [Algebra K E] {d : ℕ} (hd : Odd d) (hE : UnitaryFieldData ℓ (f * d) E) (θ : E →+* E)
    (hθK : ∀ k : K, θ (algebraMap K E k) = algebraMap K E k)
    (hθ : ∀ e : E, e ^ (ℓ ^ f) ^ d = e → θ e = e) : θ = RingHom.id E := by
  have hσ : Function.Involutive hE.bar := hE.bar_bar
  rcases CFSG.ComponentClassification.AschbacherToolkit.Bender.UnitaryField.eq_id_or_eq_conj_of_fix
    (RingEquiv.ofBijective hE.bar hσ.bijective) hσ θ (fun t ht => hθ t (by
      have h1 : hE.bar t = t := ht
      rwa [UnitaryFieldData.bar_apply, pow_mul] at h1)) with h1 | h1
  · ext e
    exact h1 e
  · exfalso
    obtain ⟨ω, hω⟩ := hK.exists_bar_ne
    obtain ⟨m, rfl⟩ := hd
    have h2 : θ (algebraMap K E ω) = hE.bar (algebraMap K E ω) := h1 _
    rw [hθK, UnitaryFieldData.bar_apply, ← map_pow] at h2
    apply hω
    apply (algebraMap K E).injective
    rw [h2, UnitaryFieldData.bar_apply]
    congr 1
    rw [mul_add, mul_one, pow_add, pow_mul ω, pow_card_two_mul hK m ω]

section Support

variable {hK : UnitaryFieldData ℓ f K} {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {B : V →ₛₗ[hK.bar] V →ₗ[K] K}

theorem primaryComponent_le_of_specialBlock_eq (hℓ : ℓ ≠ 2)
    {x y : LinearMap.GeneralLinearGroup K V} (Hx : UnitaryPrimaryData hK.bar B x)
    (Hy : UnitaryPrimaryData hK.bar B y) {a : primaryFactors (x : Module.End K V)}
    {b : primaryFactors (y : Module.End K V)} (ha : dualPoly hK.bar (a : K[X]) = a)
    (hb : dualPoly hK.bar (b : K[X]) = b) (hgood : IsGoodBlock hK x a)
    (heq : specialBlock B x (a : K[X]) = specialBlock B y (b : K[X])) :
    primaryComponent (x : Module.End K V) (a : K[X]) ≤
      primaryComponent (y : Module.End K V) (b : K[X]) := by
  intro w hw
  have hcl : w ∈ AddSubgroup.closure {u | ∃ g ∈ specialBlock B x (a : K[X]), ∃ v,
      (g : Module.End K V) v - v = u} :=
    primaryComponent_le_closure_specialBlock Hx ha hℓ hgood hw
  clear hw
  induction hcl using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨g, hg, v, rfl⟩ := hu
    exact sub_mem_primaryComponent_of_mem_specialBlock Hy hb (heq ▸ hg) v
  | zero => exact zero_mem _
  | add u₁ u₂ _ _ h₁ h₂ => exact add_mem h₁ h₂
  | neg u _ hu => exact neg_mem hu

end Support

variable {n : ℕ}

theorem commutator_comap_specialBlock_eq (h : UnitaryFieldData ℓ f K)
    {x : LinearMap.GeneralLinearGroup K (Fin n → K)} (H : UnitaryPrimaryData h.bar (idForm h n) x)
    {a : primaryFactors (x : Module.End K (Fin n → K))} (hgood : IsGoodBlock h x a) :
    ⁅(specialBlock (idForm h n) x (a : K[X])).comap (toLinSU h n),
      (specialBlock (idForm h n) x (a : K[X])).comap (toLinSU h n)⁆ =
      (specialBlock (idForm h n) x (a : K[X])).comap (toLinSU h n) := by
  have hq2 : 2 ≤ ℓ ^ f := by
    have := Nat.one_lt_pow (by have := h.one_le; omega : f ≠ 0) h.prime.one_lt
    omega
  have hSBle : specialBlock (idForm h n) x (a : K[X]) ≤ (toLinSU h n).range := fun g hg =>
    mem_range_toLinSU (specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq2 a hgood hg)
  have hperfSB : ⁅specialBlock (idForm h n) x (a : K[X]), specialBlock (idForm h n) x (a : K[X])⁆ =
      specialBlock (idForm h n) x (a : K[X]) := by
    haveI := ((specialBlockFacts_of_good H hq2 a hgood).quasisimple hgood.1).1
    exact CFSG.GroupTheory.commutator_eq_self_of_isPerfect_subgroup
  apply Subgroup.map_injective (toLinSU_injective (h := h) (n := n))
  rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self hSBle, hperfSB]

theorem plSemiVec_mulVec_of_mul_eq (B : GL (Fin n) K) (τ : K ≃+* K)
    {M N : Matrix (Fin n) (Fin n) K} (hMN : (B : Matrix (Fin n) (Fin n) K) * M.map τ = N * B)
    (v : Fin n → K) : plSemiVec B τ (M *ᵥ v) = N *ᵥ plSemiVec B τ v := by
  have hτ : (fun i => τ ((M *ᵥ v) i)) = M.map τ *ᵥ fun i => τ (v i) := by
    ext i
    exact RingHom.map_mulVec τ.toRingHom M v i
  rw [plSemiVec_apply, plSemiVec_apply, hτ, Matrix.mulVec_mulVec, hMN, ← Matrix.mulVec_mulVec]

theorem conj_glAut_eq_of_fix (h : UnitaryFieldData ℓ f K)
    {F : Subgroup (gramSU h (idGram K n))} (hF : ⁅F, F⁆ = F)
    (B : primeFormUnitary h (idGram K n)) (τ : K ≃+* K)
    (hfix : ∀ g ∈ F, (primeFormConjHom h (idGram K n) B *
      primeFormFieldHom h (isPrimeFormGram_idGram (n := n)) τ) (g : primeFormP h (idGram K n)) =
        g)
    {g : gramSU h (idGram K n)} (hg : g ∈ F) :
    (B : GL (Fin n) K) * glAut τ (g : GL (Fin n) K) * (B : GL (Fin n) K)⁻¹ = g := by
  have hker : (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)).ker ≤
      Subgroup.center _ := by
    rw [QuotientGroup.ker_mk']
    exact normOneScalars_le_center h _ n
  have hψ := map_eq_self_of_perfect (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))
    hker hF ((primeFormConjSU h (idGram K n) B).toMonoidHom.comp
      (primeFormFieldSU h (isPrimeFormGram_idGram (n := n)) τ).toMonoidHom) (fun g' hg' => by
        rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom,
          QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, ← primeFormConjAut_mk,
          ← primeFormFieldAut_mk]
        exact hfix g' hg') hg
  exact congrArg Subtype.val hψ

theorem exists_smul_of_fix_specialBlock_uni (h : UnitaryFieldData ℓ f K) (hℓ : ℓ ≠ 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (A : primeFormUnitary h (idGram K n)) {c : Kˣ}
    (hA : (A : GL (Fin n) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    {x : LinearMap.GeneralLinearGroup K (Fin n → K)}
    (hx : x = Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
    {a : primaryFactors (x : Module.End K (Fin n → K))} (hself : dualPoly h.bar (a : K[X]) = a)
    (hgood : IsGoodBlock h x a) (B : primeFormUnitary h (idGram K n)) (τ : K ≃+* K)
    (hτ : τ ^ p = 1) (μ : K)
    (hμ : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map τ =
      (μ • ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hfix : ∀ g ∈ (specialBlock (idForm h n) x (a : K[X])).comap (toLinSU h n),
      (primeFormConjHom h (idGram K n) B *
        primeFormFieldHom h (isPrimeFormGram_idGram (n := n)) τ)
          (g : primeFormP h (idGram K n)) = g) :
    τ = 1 ∧ ∃ e : AdjoinRoot (a : K[X]),
      ∀ w : primaryComponent (x : Module.End K (Fin n → K)) (a : K[X]),
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) =
          ((e • w : primaryComponent (x : Module.End K (Fin n → K)) (a : K[X])) : Fin n → K) := by
  classical
  haveI := h.finite
  have H : UnitaryPrimaryData h.bar (idForm h n) x :=
    hx ▸ CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks.primaryData_toLin'
      h A.2 hp hpℓ hA
  have hq2 : 2 ≤ ℓ ^ f := by
    have := Nat.one_lt_pow (by have := h.one_le; omega : f ≠ 0) h.prime.one_lt
    omega
  haveI : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
  set W := primaryComponent (x : Module.End K (Fin n → K)) (a : K[X]) with hWdef
  set SB := specialBlock (idForm h n) x (a : K[X]) with hSBdef
  have hSBle : SB ≤ (toLinSU h n).range := fun g hg =>
    mem_range_toLinSU (specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq2 a hgood hg)
  have hperfF : ⁅SB.comap (toLinSU h n), SB.comap (toLinSU h n)⁆ = SB.comap (toLinSU h n) :=
    commutator_comap_specialBlock_eq h H hgood
  have hxv : ∀ v : Fin n → K, (x : Module.End K (Fin n → K)) v =
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v := by
    intro v
    rw [hx]
    rfl
  have hs : ∀ y ∈ SB, ∀ v, plSemiVec (B : GL (Fin n) K) τ ((y : Module.End K (Fin n → K)) v) =
      (y : Module.End K (Fin n → K)) (plSemiVec (B : GL (Fin n) K) τ v) := by
    intro y hy v
    obtain ⟨g, rfl⟩ := hSBle hy
    have hgF : g ∈ SB.comap (toLinSU h n) := hy
    have hg' : (B : GL (Fin n) K) * glAut τ (g : GL (Fin n) K) = (g : GL (Fin n) K) * B :=
      mul_inv_eq_iff_eq_mul.mp (conj_glAut_eq_of_fix h hperfF B τ hfix hgF)
    have hMN := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) hg'
    simp only [Units.val_mul, coe_glAut] at hMN
    change plSemiVec (B : GL (Fin n) K) τ (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ plSemiVec (B : GL (Fin n) K) τ v
    exact plSemiVec_mulVec_of_mul_eq _ τ hMN v
  have hsW : ∀ w ∈ W, plSemiVec (B : GL (Fin n) K) τ w ∈ W := by
    intro w hw
    have hcl : w ∈ AddSubgroup.closure {u | ∃ g ∈ SB, ∃ v,
        (g : Module.End K (Fin n → K)) v - v = u} :=
      primaryComponent_le_closure_specialBlock H hself hℓ hgood hw
    clear hw
    induction hcl using AddSubgroup.closure_induction with
    | mem u hu =>
      obtain ⟨g, hg, v, rfl⟩ := hu
      rw [map_sub, hs g hg]
      exact sub_mem_primaryComponent_of_mem_specialBlock H hself hg _
    | zero =>
      rw [map_zero]
      exact zero_mem _
    | add u₁ u₂ _ _ h₁ h₂ =>
      rw [map_add]
      exact add_mem h₁ h₂
    | neg u _ hu =>
      rw [map_neg]
      exact neg_mem hu
  have hsx : ∀ v, plSemiVec (B : GL (Fin n) K) τ ((x : Module.End K (Fin n → K)) v) =
      μ • (x : Module.End K (Fin n → K)) (plSemiVec (B : GL (Fin n) K) τ v) := by
    intro v
    rw [hxv, hxv, plSemiVec_mulVec_of_mul_eq _ τ hμ, Matrix.smul_mulVec]
  have hroot : ∀ w : W,
      (⟨plSemiVec (B : GL (Fin n) K) τ ((AdjoinRoot.root (a : K[X]) • w : W) : Fin n → K),
        hsW _ (AdjoinRoot.root (a : K[X]) • w).2⟩ : W) =
        (algebraMap K (AdjoinRoot (a : K[X])) μ * AdjoinRoot.root (a : K[X])) •
          ⟨plSemiVec (B : GL (Fin n) K) τ w, hsW w w.2⟩ := by
    intro w
    apply Subtype.ext
    rw [Subtype.coe_mk, coe_root_smul_primaryComponent, hsx, mul_smul,
      coe_algebraMap_smul_primaryComponent, coe_root_smul_primaryComponent]
  have hsemi : ∀ (g : K[X]) (w : W),
      plSemiVec (B : GL (Fin n) K) τ ((AdjoinRoot.mk (a : K[X]) g • w : W) : Fin n → K) =
        ((g.eval₂ ((algebraMap K (AdjoinRoot (a : K[X]))).comp τ.toRingHom)
          (algebraMap K (AdjoinRoot (a : K[X])) μ * AdjoinRoot.root (a : K[X])) •
          (⟨plSemiVec (B : GL (Fin n) K) τ w, hsW w w.2⟩ : W) : W) : Fin n → K) := by
    intro g
    induction g using Polynomial.induction_on with
    | C k =>
      intro w
      rw [coe_mk_smul_primaryComponent, aeval_C, Module.algebraMap_end_apply, plSemiVec_smul,
        eval₂_C, RingHom.comp_apply, coe_algebraMap_smul_primaryComponent]
      rfl
    | add g₁ g₂ h₁ h₂ =>
      intro w
      rw [map_add, add_smul, Submodule.coe_add, map_add, h₁, h₂, eval₂_add, add_smul,
        Submodule.coe_add]
    | monomial m k ih =>
      intro w
      have e1 : AdjoinRoot.mk (a : K[X]) (C k * X ^ (m + 1)) =
          AdjoinRoot.mk (a : K[X]) (C k * X ^ m) * AdjoinRoot.root (a : K[X]) := by
        rw [pow_succ, ← mul_assoc (C k), map_mul, AdjoinRoot.mk_X]
      have e2 : (C k * X ^ (m + 1)).eval₂
          ((algebraMap K (AdjoinRoot (a : K[X]))).comp τ.toRingHom)
          (algebraMap K (AdjoinRoot (a : K[X])) μ * AdjoinRoot.root (a : K[X])) =
          (C k * X ^ m).eval₂ ((algebraMap K (AdjoinRoot (a : K[X]))).comp τ.toRingHom)
            (algebraMap K (AdjoinRoot (a : K[X])) μ * AdjoinRoot.root (a : K[X])) *
          (algebraMap K (AdjoinRoot (a : K[X])) μ * AdjoinRoot.root (a : K[X])) := by
        rw [pow_succ, ← mul_assoc (C k), eval₂_mul_X]
      rw [e1, mul_smul, ih, hroot w, smul_smul, e2]
  obtain ⟨w₀, hw₀⟩ : ∃ w : W, w ≠ 0 := by
    have h2 : 2 ≤ Module.finrank (AdjoinRoot (a : K[X])) W := hgood.1
    have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := AdjoinRoot (a : K[X])) (by omega)
    exact exists_ne 0
  have hs0 : (⟨plSemiVec (B : GL (Fin n) K) τ w₀, hsW w₀ w₀.2⟩ : W) ≠ 0 := by
    intro h0
    apply hw₀
    apply Subtype.ext
    apply plSemiVec_injective (B : GL (Fin n) K) τ
    rw [Submodule.coe_zero, map_zero]
    exact congrArg Subtype.val h0
  have hwd : (a : K[X]).eval₂ ((algebraMap K (AdjoinRoot (a : K[X]))).comp τ.toRingHom)
      (algebraMap K (AdjoinRoot (a : K[X])) μ * AdjoinRoot.root (a : K[X])) = 0 := by
    have h1 := hsemi (a : K[X]) w₀
    rw [AdjoinRoot.mk_self, zero_smul, Submodule.coe_zero, map_zero] at h1
    have h2 : (a : K[X]).eval₂ ((algebraMap K (AdjoinRoot (a : K[X]))).comp τ.toRingHom)
        (algebraMap K (AdjoinRoot (a : K[X])) μ * AdjoinRoot.root (a : K[X])) •
          (⟨plSemiVec (B : GL (Fin n) K) τ w₀, hsW w₀ w₀.2⟩ : W) = 0 := Subtype.ext h1.symm
    exact (smul_eq_zero.mp h2).resolve_right hs0
  set θ := AdjoinRoot.lift ((algebraMap K (AdjoinRoot (a : K[X]))).comp τ.toRingHom)
    (algebraMap K (AdjoinRoot (a : K[X])) μ * AdjoinRoot.root (a : K[X])) hwd with hθdef
  have hθ : ∀ (e : AdjoinRoot (a : K[X])) (w : W),
      plSemiVec (B : GL (Fin n) K) τ ((e • w : W) : Fin n → K) =
        ((θ e • (⟨plSemiVec (B : GL (Fin n) K) τ w, hsW w w.2⟩ : W) : W) : Fin n → K) := by
    intro e w
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective e
    rw [hθdef, AdjoinRoot.lift_mk]
    exact hsemi g w
  obtain ⟨hfixE, hscal⟩ := specialBlock_selfDual_commutant H hself hℓ hgood
    (plSemiVec (B : GL (Fin n) K) τ) (plSemiVec_injective _ τ) hs hsW θ hθ
  have h0 := coeff_zero_ne_zero_of_mem_primaryFactors H.squarefree a.2
  have hd : Odd (a : K[X]).natDegree := odd_natDegree_of_selfDual h h0 hself
  have hθK : ∀ k : K, θ (algebraMap K (AdjoinRoot (a : K[X])) k) =
      algebraMap K (AdjoinRoot (a : K[X])) (τ k) := by
    intro k
    rw [hθdef]
    exact AdjoinRoot.lift_of hwd
  have hτ1 : τ = 1 := by
    refine ringEquiv_eq_one_of_fix_bar h (hp.odd_of_ne_two hp2) τ hτ fun k hk => ?_
    apply (algebraMap K (AdjoinRoot (a : K[X]))).injective
    rw [← hθK]
    apply hfixE
    rw [← map_pow]
    congr 1
    have hk' : k ^ ℓ ^ f = k := hk
    generalize (a : K[X]).natDegree = d
    induction d with
    | zero => rw [pow_zero, pow_one]
    | succ d ih => rw [pow_succ, pow_mul, ih, hk']
  obtain ⟨hE, -⟩ :=
    exists_selfDualFactor hself (CFSG.RankThree.PartOne.selfDualPrimaryBlock H a hself)
  have hθid : θ = RingHom.id _ :=
    ringHom_eq_id_of_fix_pow h hd hE θ (fun k => by rw [hθK, hτ1]; rfl) hfixE
  obtain ⟨e, he⟩ := hscal hθid
  refine ⟨hτ1, e, fun w => ?_⟩
  have h1 := he w
  rw [plSemiVec_apply] at h1
  rw [← h1, hτ1]
  rfl

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
