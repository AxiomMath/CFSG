module

public import CFSG.ClassicalInvolution.Q3.Q3PSL9Bar
public import CFSG.ClassicalInvolution.Q3.LieSystem
public import CFSG.ClassicalInvolution.Q3.Q3PSL9Conj
public import CFSG.ClassicalInvolution.Q3.Q3PSL9Layer
public import CFSG.LieType.HighestRoot.CentChevalleySLThree

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4 CFSG.ClassicalInvolution.Q3.Q3PSL9
open scoped MatrixGroups commutatorElement

section Model

variable {F : Type} [Field F] [Finite F]

theorem eq_diag_of_comm_transvections {E : Type} [Field E] {N : Matrix (Fin 2) (Fin 2) E}
    (h1 : N * !![1, 1; 0, 1] = !![1, 1; 0, 1] * N)
    (h2 : N * !![1, 0; 1, 1] = !![1, 0; 1, 1] * N) : N = !![N 0 0, 0; 0, N 0 0] := by
  have a1 := congrFun (congrFun h1 0) 0
  have a2 := congrFun (congrFun h1 0) 1
  have b1 := congrFun (congrFun h2 0) 0
  have b2 := congrFun (congrFun h2 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at a1 a2 b1 b2
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · exact b1
  · exact a1
  · linear_combination -a2

theorem eq_one_or_zneg_of_comm_Qns (hns : ¬ ∃ i : F, i * i = -1) {g : SL(4, F)} (hg2 : g * g = 1)
    (hgu : g * u0 F = u0 F * g) (hgQ : ∀ p ∈ Qns F, g * p = p * g) : g = 1 ∨ g = zneg F := by
  have : Fact (¬ IsSquare (-1 : F)) := ⟨fun ⟨r, hr⟩ => hns ⟨r, hr.symm⟩⟩
  obtain ⟨N, hN⟩ := exists_Phi_of_comm (g : Matrix (Fin 4) (Fin 4) F) (by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hgu])
  have hcomm : ∀ M : SL(2, QE F), N * (M : Matrix (Fin 2) (Fin 2) (QE F)) = M * N := by
    intro M
    apply Phi_injective
    have h := congrArg (fun x : SL(4, F) => (x : Matrix (Fin 4) (Fin 4) F))
      (hgQ (PhiSL M) ⟨M, rfl⟩)
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_PhiSL] at h
    rw [map_mul, map_mul, hN]
    exact h
  have hdet1 : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (QE F)).det = 1 := by
    simp [Matrix.det_fin_two_of]
  have hdet2 : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) (QE F)).det = 1 := by
    simp [Matrix.det_fin_two_of]
  have hN' := eq_diag_of_comm_transvections (hcomm ⟨!![1, 1; 0, 1], hdet1⟩)
    (hcomm ⟨!![1, 0; 1, 1], hdet2⟩)
  set a : QE F := N 0 0 with ha
  have hNN : N * N = 1 := by
    apply Phi_injective
    rw [map_mul, hN, map_one, ← Matrix.SpecialLinearGroup.coe_mul, hg2]
    rfl
  have haa : a * a = 1 := by
    have := congrFun (congrFun hNN 0) 0
    rw [hN'] at this
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  rcases mul_self_eq_one_iff.mp haa with h | h
  · left
    apply Subtype.ext
    rw [← hN, hN', h]
    rw [Matrix.one_fin_two.symm, map_one]
    rfl
  · right
    apply Subtype.ext
    rw [← hN, hN', h, coe_zneg]
    have : (!![-1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) (QE F)) = -1 := by
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp
    rw [this, map_neg, map_one]

theorem comm_mem_Qns {g h : SL(4, F)} (hg : g * u0 F = u0 F * g) (hh : h * u0 F = u0 F * h) :
    g * h * g⁻¹ * h⁻¹ ∈ Qns F := by
  have hg' : g⁻¹ * u0 F = u0 F * g⁻¹ := (Commute.inv_left (show Commute g (u0 F) from hg)).eq
  have hh' : h⁻¹ * u0 F = u0 F * h⁻¹ := (Commute.inv_left (show Commute h (u0 F) from hh)).eq
  have key : ∀ k : SL(4, F), k * u0 F = u0 F * k →
      ∃ N : Matrix (Fin 2) (Fin 2) (QE F), Phi N = (k : Matrix (Fin 4) (Fin 4) F) :=
    fun k hk => exists_Phi_of_comm (k : Matrix (Fin 4) (Fin 4) F) (by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hk])
  obtain ⟨Ng, hNg⟩ := key g hg
  obtain ⟨Nh, hNh⟩ := key h hh
  obtain ⟨Ng', hNg'⟩ := key g⁻¹ hg'
  obtain ⟨Nh', hNh'⟩ := key h⁻¹ hh'
  have hgg : Ng * Ng' = 1 := by
    apply Phi_injective
    rw [map_mul, hNg, hNg', ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, map_one]
    rfl
  have hhh : Nh * Nh' = 1 := by
    apply Phi_injective
    rw [map_mul, hNh, hNh', ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, map_one]
    rfl
  have hdet : (Ng * Nh * Ng' * Nh').det = 1 := by
    have e1 : Ng.det * Ng'.det = 1 := by rw [← Matrix.det_mul, hgg, Matrix.det_one]
    have e2 : Nh.det * Nh'.det = 1 := by rw [← Matrix.det_mul, hhh, Matrix.det_one]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
    calc Ng.det * Nh.det * Ng'.det * Nh'.det = (Ng.det * Ng'.det) * (Nh.det * Nh'.det) := by ring
      _ = 1 := by rw [e1, e2, one_mul]
  refine ⟨⟨Ng * Nh * Ng' * Nh', hdet⟩, Subtype.ext ?_⟩
  show Phi (Ng * Nh * Ng' * Nh') = ((g * h * g⁻¹ * h⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)
  simp only [Matrix.SpecialLinearGroup.coe_mul, ← hNg, ← hNh, ← hNg', ← hNh', map_mul]

theorem exists_layer0_sl4_strong (hns : ¬ ∃ i : F, i * i = -1) (u : SL(4, F))
    (hu : u * u = zneg F) :
    ∃ L0 : Subgroup SL(4, F), L0 ≤ Subgroup.centralizer ({u} : Set SL(4, F)) ∧
      (∀ x ∈ Subgroup.centralizer ({u} : Set SL(4, F)), ∀ y ∈ L0, x * y * x⁻¹ ∈ L0) ∧
      u * u ∈ L0 ∧ Nonempty (L0 ≃* SL(2, QE F)) ∧
      (∀ g : SL(4, F), g * g = 1 → g * u = u * g → (∀ y ∈ L0, g * y = y * g) →
        g = 1 ∨ g = zneg F) ∧
      (∀ P : Subgroup SL(4, F), P ≤ Subgroup.centralizer ({u} : Set SL(4, F)) → ⁅P, P⁆ = P →
        P ≤ L0) := by
  obtain ⟨Q, hQ⟩ := exists_conj_u0_sl4 hns u hu
  have hu' : u = Q * u0 F * Q⁻¹ := hQ.symm
  have hc : Function.Injective (MulAut.conj Q).toMonoidHom := (MulAut.conj Q).injective
  have hmem : ∀ y, y ∈ (Qns F).map (MulAut.conj Q).toMonoidHom ↔ Q⁻¹ * y * Q ∈ Qns F := by
    intro y
    constructor
    · rintro ⟨r, hr, rfl⟩
      have e : Q⁻¹ * (MulAut.conj Q).toMonoidHom r * Q = r := by
        show Q⁻¹ * (Q * r * Q⁻¹) * Q = r
        group
      rw [e]
      exact hr
    · intro hy
      exact ⟨Q⁻¹ * y * Q, hy, by simp [MulAut.conj_apply]; group⟩
  have hcomm : ∀ x : SL(4, F), x * u = u * x → (Q⁻¹ * x * Q) * u0 F = u0 F * (Q⁻¹ * x * Q) := by
    intro x hx
    have e1 : u0 F = Q⁻¹ * u * Q := by rw [hu']; group
    rw [e1]
    calc Q⁻¹ * x * Q * (Q⁻¹ * u * Q) = Q⁻¹ * (x * u) * Q := by group
      _ = Q⁻¹ * (u * x) * Q := by rw [hx]
      _ = (Q⁻¹ * u * Q) * (Q⁻¹ * x * Q) := by group
  have hzc : ∀ x : SL(4, F), x * zneg F * x⁻¹ = zneg F := fun x => by
    rw [Subgroup.mem_center_iff.mp zneg_mem_center x]
    group
  refine ⟨(Qns F).map (MulAut.conj Q).toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [hmem] at hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Qns_comm hy
    have e1 : u * y = Q * (u0 F * (Q⁻¹ * y * Q)) * Q⁻¹ := by rw [hu']; group
    have e2 : y * u = Q * ((Q⁻¹ * y * Q) * u0 F) * Q⁻¹ := by rw [hu']; group
    rw [e1, e2, h1]
  · intro x hx y hy
    rw [hmem] at hy ⊢
    have := Qns_norm_of_comm (hcomm x (Subgroup.mem_centralizer_singleton_iff.mp hx)) hy
    have e : Q⁻¹ * (x * y * x⁻¹) * Q = (Q⁻¹ * x * Q) * (Q⁻¹ * y * Q) * (Q⁻¹ * x * Q)⁻¹ := by
      group
    rw [e]
    exact this
  · rw [hmem]
    have e : Q⁻¹ * (u * u) * Q = u0 F * u0 F := by rw [hu']; group
    rw [e, u0_mul_self]
    exact zneg_mem_Qns
  · exact ⟨(Subgroup.equivMapOfInjective (Qns F) (MulAut.conj Q).toMonoidHom hc).symm.trans
      (MonoidHom.ofInjective PhiSL_injective).symm⟩
  · intro g hg2 hgu hgL
    have h1 : (Q⁻¹ * g * Q) * (Q⁻¹ * g * Q) = 1 := by
      calc (Q⁻¹ * g * Q) * (Q⁻¹ * g * Q) = Q⁻¹ * (g * g) * Q := by group
        _ = 1 := by rw [hg2]; group
    have h3 : ∀ p ∈ Qns F, (Q⁻¹ * g * Q) * p = p * (Q⁻¹ * g * Q) := by
      intro p hp
      have hpL : Q * p * Q⁻¹ ∈ (Qns F).map (MulAut.conj Q).toMonoidHom :=
        ⟨p, hp, by simp [MulAut.conj_apply]⟩
      have h4 := hgL _ hpL
      calc (Q⁻¹ * g * Q) * p = Q⁻¹ * (g * (Q * p * Q⁻¹)) * Q := by group
        _ = Q⁻¹ * ((Q * p * Q⁻¹) * g) * Q := by rw [h4]
        _ = p * (Q⁻¹ * g * Q) := by group
    rcases eq_one_or_zneg_of_comm_Qns hns h1 (hcomm g hgu) h3 with h | h
    · left
      calc g = Q * (Q⁻¹ * g * Q) * Q⁻¹ := by group
        _ = 1 := by rw [h]; group
    · right
      calc g = Q * (Q⁻¹ * g * Q) * Q⁻¹ := by group
        _ = zneg F := by rw [h, hzc Q]
  · intro P hP hperf
    calc P = ⁅P, P⁆ := hperf.symm
      _ ≤ (Qns F).map (MulAut.conj Q).toMonoidHom := by
        rw [Subgroup.commutator_le]
        intro x hx y hy
        rw [hmem]
        have hxu := Subgroup.mem_centralizer_singleton_iff.mp (hP hx)
        have hyu := Subgroup.mem_centralizer_singleton_iff.mp (hP hy)
        have key := comm_mem_Qns (hcomm x hxu) (hcomm y hyu)
        have e : Q⁻¹ * ⁅x, y⁆ * Q =
            (Q⁻¹ * x * Q) * (Q⁻¹ * y * Q) * (Q⁻¹ * x * Q)⁻¹ * (Q⁻¹ * y * Q)⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact key

theorem exists_layer_bar9_strong {Xb : Type*} [Group Xb] (hF : Nat.card F = 3)
    (ψ : SL(4, F) →* Xb) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center SL(4, F))
    {f : SL(4, F)} (hf : f ∈ Subgroup.center SL(4, F)) (hfz : ψ f ≠ 1) {ub : Xb}
    (hub : ub * ub = ψ f) :
    ∃ Lb : Subgroup Xb, Lb ≤ Subgroup.centralizer ({ub} : Set Xb) ∧
      (∀ x ∈ Subgroup.centralizer ({ub} : Set Xb), ∀ y ∈ Lb, x * y * x⁻¹ ∈ Lb) ∧ ub * ub ∈ Lb ∧
      Nonempty (Lb ≃* SL(2, GaloisField 3 2)) ∧
      (∀ P : Subgroup Xb, P ≤ Subgroup.centralizer ({ub} : Set Xb) → ⁅P, P⁆ = P → P ≤ Lb) ∧
      (∀ x : Xb, x * x = 1 → x * ub = ub * x → (∀ y ∈ Lb, x * y = y * x) →
        x = 1 ∨ x = ub * ub) ∧
      (∀ x ∈ Subgroup.center Xb, x = 1 ∨ x = ub * ub) := by
  have hf1 : f ≠ 1 := fun h => hfz (by rw [h, map_one])
  have hfm : f = zneg F := eq_zneg_of_mem_center hF hf hf1
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    by_contra hx1
    have hxm : x = zneg F := eq_zneg_of_mem_center hF (hker (MonoidHom.mem_ker.mpr hx)) hx1
    exact hfz (by rw [hfm, ← hxm]; exact hx)
  obtain ⟨w, rfl⟩ := hψ ub
  have hw : w * w = zneg F := by
    rw [← hfm]
    exact hinj (by rw [map_mul, hub])
  obtain ⟨L0, hL0c, hL0n, hwL, ⟨e0⟩, hF2, hF3⟩ :=
    exists_layer0_sl4_strong (not_exists_sq_neg_one_of_card_three hF) w hw
  obtain ⟨σ⟩ := nonempty_ringEquiv_qe_galoisField_nine hF
  have hψc : ∀ x : SL(4, F), ψ x ∈ Subgroup.centralizer ({ψ w} : Set Xb) → x ∈
      Subgroup.centralizer ({w} : Set SL(4, F)) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    apply hinj
    rw [map_mul, map_mul]
    exact hx
  refine ⟨L0.map ψ, ?_, ?_, ?_,
    ⟨((Subgroup.equivMapOfInjective L0 ψ hinj).symm.trans e0).trans
      (CFSG.LieType.HighestRoot.slMapEquiv σ)⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨l, hl, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (hL0c hl)]
  · rintro xb hxb _ ⟨l, hl, rfl⟩
    obtain ⟨x, rfl⟩ := hψ xb
    exact ⟨x * l * x⁻¹, hL0n x (hψc x hxb) l hl, by simp⟩
  · exact ⟨w * w, hwL, by rw [map_mul]⟩
  · intro P hP hperf
    set P' : Subgroup SL(4, F) := P.comap ψ with hP'
    have hmapP : P'.map ψ = P := Subgroup.map_comap_eq_self_of_surjective hψ P
    have hperf' : ⁅P', P'⁆ = P' := by
      apply Subgroup.map_injective hinj
      rw [Subgroup.map_commutator, hmapP, hperf]
    have h1 := hF3 P' (fun x hx => hψc x (hP hx)) hperf'
    rw [← hmapP]
    exact Subgroup.map_mono h1
  · intro x hx2 hxu hxL
    obtain ⟨g, rfl⟩ := hψ x
    have hg2 : g * g = 1 := hinj (by rw [map_mul, hx2, map_one])
    have hgu : g * w = w * g := hinj (by rw [map_mul, map_mul]; exact hxu)
    have hgL : ∀ y ∈ L0, g * y = y * g := fun y hy =>
      hinj (by rw [map_mul, map_mul]; exact hxL _ ⟨y, hy, rfl⟩)
    rcases hF2 g hg2 hgu hgL with h | h
    · left
      rw [h, map_one]
    · right
      rw [h, ← map_mul, hw]
  · intro x hx
    obtain ⟨g, rfl⟩ := hψ x
    have hgc : g ∈ Subgroup.center SL(4, F) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact hinj (by rw [map_mul, map_mul]; exact Subgroup.mem_center_iff.mp hx (ψ y))
    by_cases hg1 : g = 1
    · left
      rw [hg1, map_one]
    · right
      rw [eq_zneg_of_mem_center hF hgc hg1, ← map_mul, hw]

end Model


theorem exists_layer_bar_comp9_strong {Xb : Type} [Group Xb] {c : CompData}
    (hc : c = CompData.model CFSG.Assembly.LowTwoRank.StatedLieTag.PSL 4) (ψ : c.G →* Xb)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center c.G) {f : c.G}
    (hf : f ∈ Subgroup.center c.G) (hfz : ψ f ≠ 1) {ub : Xb} (hub : ub * ub = ψ f) :
    ∃ Lb : Subgroup Xb, Lb ≤ Subgroup.centralizer ({ub} : Set Xb) ∧
      (∀ x ∈ Subgroup.centralizer ({ub} : Set Xb), ∀ y ∈ Lb, x * y * x⁻¹ ∈ Lb) ∧
      ub * ub ∈ Lb ∧ Nonempty (Lb ≃* SL(2, GaloisField 3 2)) ∧
      (∀ P : Subgroup Xb, P ≤ Subgroup.centralizer ({ub} : Set Xb) → ⁅P, P⁆ = P → P ≤ Lb) ∧
      (∀ x : Xb, x * x = 1 → x * ub = ub * x → (∀ y ∈ Lb, x * y = y * x) →
        x = 1 ∨ x = ub * ub) ∧
      (∀ x ∈ Subgroup.center Xb, x = 1 ∨ x = ub * ub) := by
  subst hc
  have : Finite (GaloisField 3 1) := inferInstance
  have hF : Nat.card (GaloisField 3 1) = 3 := by simpa using GaloisField.card 3 1 (by norm_num)
  exact exists_layer_bar9_strong (F := GaloisField 3 1) hF ψ hψ hker hf hfz hub

end CFSG.ClassicalInvolution.Q3.Q3AM
