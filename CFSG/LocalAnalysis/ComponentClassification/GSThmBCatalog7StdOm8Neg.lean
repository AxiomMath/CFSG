module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8

open Module
open CFSG.GroupTheory.WeirSylow (IsPlusType isPlusType_congr not_isPlusType_quadMinus)
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

theorem not_isPlusType_coordinateQuadMinus {K : Type} [Field K] [Finite K] (n : ℕ)
    (hn : 1 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ¬ IsPlusType (coordinateQuadMinus n K hn b c) := by
  rw [← isPlusType_congr (coordinateMinusIsometry n K hn b c)]
  exact not_isPlusType_quadMinus hn hirr

section Unitary

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
theorem polar_eq_zero_of_singular (Q : QuadraticForm K V) {S : Submodule K V}
    (hS : ∀ x ∈ S, Q x = 0) {x y : V} (hx : x ∈ S) (hy : y ∈ S) : Q.polarBilin x y = 0 := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hS _ (S.add_mem hx hy),
    hS x hx, hS y hy]
  simp

theorem sq_sub_ne_zero {d : K} (hns : ¬ IsSquare d) {α β : K} (h : α ≠ 0 ∨ β ≠ 0) :
    α ^ 2 - β ^ 2 * d ≠ 0 := by
  intro h0
  by_cases hβ : β = 0
  · subst hβ
    have hα : α = 0 := by simpa using h0
    rcases h with h | h
    · exact h hα
    · exact h rfl
  · apply hns
    refine ⟨α / β, ?_⟩
    field_simp
    linear_combination -h0

theorem unitary_step [Finite K] (hodd : Odd (Nat.card K)) (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (A : V →ₗ[K] V) {d : K} (hns : ¬ IsSquare d)
    (hA2 : ∀ x, A (A x) = d • x) (hadj : ∀ x y, Q.polarBilin (A x) y = -Q.polarBilin x (A y))
    (S : Submodule K V) (hSA : ∀ x ∈ S, A x ∈ S) (hS : ∀ x ∈ S, Q x = 0)
    (h3 : 2 * finrank K S + 3 ≤ finrank K V) :
    ∃ S' : Submodule K V, (∀ x ∈ S', A x ∈ S') ∧ (∀ x ∈ S', Q x = 0) ∧
      finrank K S' = finrank K S + 2 := by
  have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  set B := Q.polarBilin with hBdef
  have hsymm : ∀ x y, B x y = B y x := fun x y => QuadraticMap.polar_comm Q x y
  set P := LinearMap.BilinForm.orthogonal B S with hPdef
  have hP : finrank K P = finrank K V - finrank K S := LinearMap.BilinForm.finrank_orthogonal hQ S
  have hSP : S ≤ P := fun x hx n hn => polar_eq_zero_of_singular Q hS hn hx
  have hPperp : LinearMap.BilinForm.orthogonal B P = S := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · intro s hs p hp
      rw [hsymm]
      exact hp s hs
    · rw [LinearMap.BilinForm.finrank_orthogonal hQ P, hP]
      have := Submodule.finrank_le S
      omega
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (S.comap P.subtype)
  have hSPc : finrank K (S.comap P.subtype) = finrank K S :=
    (LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hSP))
  have hCdim : finrank K C = finrank K V - 2 * finrank K S := by
    have := Submodule.finrank_add_eq_of_isCompl hC
    have hSle := Submodule.finrank_le S
    omega
  set QC := (Q.comp P.subtype).comp C.subtype with hQCdef
  have hQCB : ∀ u w : C, QC.polarBilin u w = B ((u : P) : V) ((w : P) : V) := by
    intro u w
    simp only [hQCdef, hBdef, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      QuadraticMap.comp_apply, Submodule.coe_subtype, Submodule.coe_add]
  have hsep : ∀ u : C, (∀ w : C, B ((u : P) : V) ((w : P) : V) = 0) → u = 0 := by
    intro u hu
    have huP : ((u : P) : V) ∈ LinearMap.BilinForm.orthogonal B P := by
      intro p hp
      obtain ⟨a, ha, w, hw, haw⟩ : ∃ a ∈ S.comap P.subtype, ∃ w ∈ C, a + w = ⟨p, hp⟩ :=
        Submodule.mem_sup.mp (hC.sup_eq_top ▸ Submodule.mem_top)
      have hpu : p = (a : V) + ((w : P) : V) := by
        have := congrArg Subtype.val haw
        simp only [Submodule.coe_add] at this
        exact this.symm
      rw [hpu, map_add, LinearMap.add_apply, hsymm ((w : P) : V), hu ⟨w, hw⟩, add_zero,
        hsymm]
      exact hsymm _ _ ▸ (u : P).property a ha
    rw [hPperp] at huP
    have hu0 : (u : P) ∈ S.comap P.subtype ⊓ C := ⟨huP, u.property⟩
    rw [hC.inf_eq_bot, Submodule.mem_bot] at hu0
    exact Subtype.ext hu0
  have hQC : QC.polarBilin.Nondegenerate := by
    refine ⟨fun u hu => hsep u fun w => ?_, fun u hu => hsep u fun w => ?_⟩
    · rw [← hQCB]
      exact hu w
    · rw [hsymm, ← hQCB]
      exact hu w
  obtain ⟨c, hc0, hcQ⟩ := CatalogueBOddQuadratic.exists_isotropic_of_three_le hodd QC hQC (by
    rw [hCdim]
    omega)
  set y : V := ((c : P) : V) with hydef
  have hyP : y ∈ P := (c : P).property
  have hyS : y ∉ S := by
    intro hy
    have hc1 : (c : P) ∈ S.comap P.subtype ⊓ C := ⟨hy, c.property⟩
    rw [hC.inf_eq_bot, Submodule.mem_bot] at hc1
    exact hc0 (Subtype.ext hc1)
  have hy0 : y ≠ 0 := fun h => hyS (h ▸ S.zero_mem)
  have hQy : Q y = 0 := hcQ
  have hBy : B y (A y) = 0 := by
    have h := hadj y y
    rw [hsymm (A y) y] at h
    have : (2 : K) * B y (A y) = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left h2
  have hQ2 : ∀ x, B x x = 2 * Q x := fun x => by
    rw [hBdef, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul, two_mul]
  have hQAy : Q (A y) = 0 := by
    have h := hadj (A y) y
    rw [hA2, map_smul, LinearMap.smul_apply, hQ2 (A y), hQ2 y, hQy] at h
    simp only [mul_zero, smul_zero] at h
    have h' : (2 : K) * Q (A y) = 0 := by linear_combination h
    exact (mul_eq_zero.mp h').resolve_left h2
  have hSy : ∀ s ∈ S, B s y = 0 := fun s hs => hyP s hs
  have hSAy : ∀ s ∈ S, B s (A y) = 0 := by
    intro s hs
    have h := hadj s y
    rw [hSy (A s) (hSA s hs)] at h
    linear_combination h
  have hkey : ∀ α β : K, α • y + β • A y ∈ S → α = 0 ∧ β = 0 := by
    intro α β hx
    by_contra hne
    have hne' : α ≠ 0 ∨ β ≠ 0 := by tauto
    have h1 : α • (α • y + β • A y) - β • A (α • y + β • A y) ∈ S :=
      S.sub_mem (S.smul_mem α hx) (S.smul_mem β (hSA _ hx))
    have h2' : α • (α • y + β • A y) - β • A (α • y + β • A y) = (α ^ 2 - β ^ 2 * d) • y := by
      rw [map_add, map_smul, map_smul, hA2, smul_add, smul_add, smul_smul, smul_smul, smul_smul,
        smul_smul, sub_smul]
      module
    rw [h2'] at h1
    exact hyS ((Submodule.smul_mem_iff S (sq_sub_ne_zero hns hne')).mp h1)
  set T := Submodule.span K {y, A y} with hTdef
  have hmemT : ∀ x ∈ T, ∃ α β : K, α • y + β • A y = x := by
    intro x hx
    obtain ⟨α, β, h⟩ := Submodule.mem_span_pair.mp hx
    exact ⟨α, β, h⟩
  refine ⟨S ⊔ T, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨α, β, rfl⟩ := hmemT t ht
    rw [map_add, map_add, map_smul, map_smul, hA2, smul_smul]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (hSA s hs)) (Submodule.mem_sup_right ?_)
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · intro x hx
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨α, β, rfl⟩ := hmemT t ht
    have hpol1 : QuadraticMap.polar Q (α • y) (β • A y) = 0 := by
      rw [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right]
      change α * (β * B y (A y)) = 0
      rw [hBy, mul_zero, mul_zero]
    have hpol2 : QuadraticMap.polar Q s (α • y + β • A y) = 0 := by
      rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
        QuadraticMap.polar_smul_right]
      change α * B s y + β * B s (A y) = 0
      rw [hSy s hs, hSAy s hs, mul_zero, mul_zero, add_zero]
    have e1 : Q (α • y + β • A y) = 0 := by
      rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, hQy, hQAy,
        hpol1]
      ring
    rw [QuadraticMap.map_add Q, hS s hs, e1, hpol2]
    ring
  · have hinf : S ⊓ T = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxS, hxT⟩ := Submodule.mem_inf.mp hx
      obtain ⟨α, β, rfl⟩ := hmemT x hxT
      obtain ⟨rfl, rfl⟩ := hkey α β hxS
      simp
    have hind : LinearIndependent K ![y, A y] := by
      rw [LinearIndependent.pair_iff]
      intro α β h
      exact hkey α β (h ▸ S.zero_mem)
    have hTdim : finrank K T = 2 := by
      rw [hTdef, show ({y, A y} : Set V) = Set.range ![y, A y] by
        rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
          Set.singleton_union]]
      rw [finrank_span_eq_card hind]
      simp
    have := Submodule.finrank_sup_add_finrank_inf_eq S T
    rw [hinf, finrank_bot, hTdim] at this
    omega

theorem isPlusType_of_unitary [Finite K] (hodd : Odd (Nat.card K)) (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : finrank K V = 8) (A : V →ₗ[K] V) {d : K}
    (hns : ¬ IsSquare d) (hA2 : ∀ x, A (A x) = d • x)
    (hadj : ∀ x y, Q.polarBilin (A x) y = -Q.polarBilin x (A y)) : IsPlusType Q := by
  obtain ⟨S₁, hS₁A, hS₁, hS₁d⟩ := unitary_step hodd Q hQ A hns hA2 hadj ⊥
    (fun x hx => by rw [(Submodule.mem_bot K).mp hx, map_zero]; exact Submodule.zero_mem _)
    (fun x hx => by rw [(Submodule.mem_bot K).mp hx, QuadraticMap.map_zero]) (by simp [hdim])
  rw [finrank_bot] at hS₁d
  obtain ⟨S₂, -, hS₂, hS₂d⟩ := unitary_step hodd Q hQ A hns hA2 hadj S₁ hS₁A hS₁
    (by rw [hS₁d, hdim]; norm_num)
  exact ⟨S₂, by rw [hS₂d, hS₁d, hdim], hS₂⟩

end Unitary

section Multiplier

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem multiplier_eq_of_not_isPlusType (ℓ f : ℕ) (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) (hf : 1 ≤ f)
    (hcard : Nat.card K = ℓ ^ f) (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : finrank K V = 8) (hnp : ¬ IsPlusType Q) (A : V ≃ₗ[K] V) (d μ : Kˣ)
    (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V)) : (μ : K) = d := by
  have hKodd : Odd (Nat.card K) := by rw [hcard]; exact (hℓ.odd_of_ne_two hodd).pow
  obtain ⟨hsign, hadj, hsplit, -⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure ℓ f hℓ hodd hf
      hcard (by omega) Q hQ A d μ hsquare hsim hnonscalar
  rcases hsign with h1 | hm
  · exact (div_eq_one_iff_eq (Units.ne_zero d)).mp h1
  · exfalso
    apply hnp
    by_cases hsq : IsSquare (d : K)
    · obtain ⟨b0, hb0⟩ := hsq
      have hb00 : b0 ≠ 0 := by
        rintro rfl
        apply d.ne_zero
        rw [hb0, mul_zero]
      obtain ⟨-, -, -, -, hneg⟩ := hsplit (Units.mk0 b0 hb00) (by
        rw [Units.val_mk0, sq]
        exact hb0)
      obtain ⟨hP, -, -, -, hPd, -⟩ := hneg hm
      exact ⟨positiveSquareKernel A (Units.mk0 b0 hb00 : K), by rw [hPd, hdim], hP⟩
    · refine isPlusType_of_unitary hKodd Q hQ hdim A.toLinearMap hsq hsquare fun x y => ?_
      have h := hadj x y
      rw [hm] at h
      change Q.polarBilin (A x) y = -Q.polarBilin x (A y)
      rw [h]
      ring

end Multiplier

end CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8
