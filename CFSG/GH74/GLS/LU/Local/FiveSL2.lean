module

public import CFSG.GH74.GLS.IVK.L2.BorelMatrices

public section

open Subgroup CFSG.PSL2Table CFSG.GH74.GLS.IVK.L2Borel
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section Matrices

variable {F : Type} [Field F]

private theorem inv_mul_mul_mem_unipSL {x : SL(2, F)} (hx : x ∈ borelSL F) {u : SL(2, F)}
    (hu : u ∈ unipSL F) : x⁻¹ * u * x ∈ unipSL F := by
  rw [mem_borelSL_iff] at hx
  rw [mem_unipSL_iff] at hu ⊢
  have hdet := det_entries x
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [mul_apply_SL, Matrix.adjugate_fin_two, hx, hu.1, hu.2.1, hu.2.2] <;>
    linear_combination hdet + ((x : Matrix (Fin 2) (Fin 2) F) 0 1) * hx

private theorem mul_mul_inv_mem_unipSL {x : SL(2, F)} (hx : x ∈ borelSL F) {u : SL(2, F)}
    (hu : u ∈ unipSL F) : x * u * x⁻¹ ∈ unipSL F := by
  simpa using inv_mul_mul_mem_unipSL (inv_mem hx) hu

private theorem conj_unip_one_apply_one_zero (x : SL(2, F)) :
    ((x * unip 1 * x⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 =
      -((x : Matrix (Fin 2) (Fin 2) F) 1 0) ^ 2 := by
  simp [mul_apply_SL, Matrix.adjugate_fin_two]
  ring

private theorem sup_eq_top_of_conj_unipSL {P Q : Subgroup SL(2, F)} {a b : SL(2, F)}
    (hP : ∀ y, y ∈ P ↔ a⁻¹ * y * a ∈ unipSL F) (hQ : ∀ y, y ∈ Q ↔ b⁻¹ * y * b ∈ unipSL F)
    (hPQ : P ≠ Q) : P ⊔ Q = ⊤ := by
  set x : SL(2, F) := a⁻¹ * b with hx
  have hx10 : (x : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
    intro h0
    apply hPQ
    ext y
    rw [hP, hQ]
    have hxB : x ∈ borelSL F := h0
    have hconj : b⁻¹ * y * b = x⁻¹ * (a⁻¹ * y * a) * x := by simp [hx, mul_assoc]
    rw [hconj]
    constructor
    · intro hy
      exact inv_mul_mul_mem_unipSL hxB hy
    · intro hy
      have := mul_mul_inv_mem_unipSL hxB hy
      simpa [mul_assoc] using this
  set H : Subgroup SL(2, F) := (P ⊔ Q).comap (MulAut.conj a).toMonoidHom
  have hHtop : H = ⊤ := by
    refine eq_top_of_unip_mem (A := x * unip 1 * x⁻¹) ?_ ?_ ?_
    · intro t
      show a * unip t * a⁻¹ ∈ P ⊔ Q
      apply Subgroup.mem_sup_left
      rw [hP]
      have : a⁻¹ * (a * unip t * a⁻¹) * a = unip t := by group
      rw [this]
      exact unip_mem_unipSL t
    · show a * (x * unip 1 * x⁻¹) * a⁻¹ ∈ P ⊔ Q
      apply Subgroup.mem_sup_right
      rw [hQ]
      have : b⁻¹ * (a * (x * unip 1 * x⁻¹) * a⁻¹) * b = unip 1 := by
        simp only [hx]
        group
      rw [this]
      exact unip_mem_unipSL 1
    · rw [conj_unip_one_apply_one_zero]
      simpa using hx10
  refine eq_top_iff.2 fun g _ => ?_
  have h1 : a⁻¹ * g * a ∈ H := by rw [hHtop]; exact Subgroup.mem_top _
  have h2 : a * (a⁻¹ * g * a) * a⁻¹ ∈ P ⊔ Q := h1
  have e : a * (a⁻¹ * g * a) * a⁻¹ = g := by group
  rwa [e] at h2

private theorem card_unipSL : Nat.card ↥(unipSL F) = Nat.card F := by
  refine Nat.card_congr (Equiv.symm (Equiv.ofBijective
    (fun t : F => (⟨unip t, unip_mem_unipSL t⟩ : ↥(unipSL F))) ⟨?_, ?_⟩))
  · intro s t h
    have := congrArg (fun x : ↥(unipSL F) => ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simpa using this
  · rintro ⟨A, hA⟩
    refine ⟨(A : Matrix (Fin 2) (Fin 2) F) 0 1, Subtype.ext ?_⟩
    rw [mem_unipSL_iff] at hA
    apply SL_ext <;> simp [hA.1, hA.2.1, hA.2.2]

end Matrices

section ZMod5

local instance factPrimeFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private theorem card_sl2_zmod_five : Nat.card SL(2, ZMod 5) = 120 := by
  rw [CFSG.GorensteinWalter.sl2_card_formula, Nat.card_zmod]
  norm_num

private theorem factorization_card_sl2_zmod_five :
    (Nat.card SL(2, ZMod 5)).factorization 5 = 1 := by
  rw [card_sl2_zmod_five]
  simp [Nat.factorization]

private theorem neg_one_ne_one_zmod_five : (-1 : SL(2, ZMod 5)) ≠ 1 := by
  intro h
  have := congrArg (fun A : SL(2, ZMod 5) => (A : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0) h
  revert this
  simp
  decide

private theorem card_center_sl2_zmod_five : Nat.card ↥(center SL(2, ZMod 5)) = 2 := by
  have h : ((center SL(2, ZMod 5) : Subgroup SL(2, ZMod 5)) : Set SL(2, ZMod 5)) = {1, -1} := by
    ext A
    simp [mem_center_SL_iff]
  have h2 : Nat.card ↥(center SL(2, ZMod 5)) =
      Set.ncard ((center SL(2, ZMod 5) : Subgroup SL(2, ZMod 5)) : Set SL(2, ZMod 5)) :=
    Nat.card_coe_set_eq _
  rw [h2, h, Set.ncard_pair neg_one_ne_one_zmod_five.symm]

private theorem unip_mem_commutator_zmod_five (t : ZMod 5) :
    unip t ∈ ⁅(⊤ : Subgroup SL(2, ZMod 5)), (⊤ : Subgroup SL(2, ZMod 5))⁆ := by
  let a : (ZMod 5)ˣ := ⟨2, 3, by decide, by decide⟩
  have h : ⁅diag a, unip (2 * t)⁆ = unip t := by
    rw [commutatorElement_def, diag_conj_unip, unip_neg, ← unip_add]
    congr 1
    show (2 : ZMod 5) ^ 2 * (2 * t) + -(2 * t) = t
    revert t
    decide
  rw [← h]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top (diag a))
    (Subgroup.mem_top (unip (2 * t)))

private theorem perfect_sl2_zmod_five :
    ⁅(⊤ : Subgroup SL(2, ZMod 5)), (⊤ : Subgroup SL(2, ZMod 5))⁆ = ⊤ := by
  set C : Subgroup SL(2, ZMod 5) :=
    ⁅(⊤ : Subgroup SL(2, ZMod 5)), (⊤ : Subgroup SL(2, ZMod 5))⁆
  have hup : ∀ t : ZMod 5, unip t ∈ C := unip_mem_commutator_zmod_five
  have hlow : lowT (1 : ZMod 5) ∈ C := by
    have h := Subgroup.Normal.conj_mem (inferInstance : C.Normal) _ (hup (-1))
      (wc (1 : ZMod 5) one_ne_zero)
    rw [wc_conj_unip] at h
    have e : lowT (1 : ZMod 5) = lowT (-((1 : ZMod 5) ^ 2 * -1)) := by congr 1
    rw [e]
    exact h
  exact eq_top_of_unip_mem hup hlow (by simp)

private theorem normal_cases_sl2_zmod_five (N : Subgroup SL(2, ZMod 5)) [N.Normal] :
    N = ⊥ ∨ N = center SL(2, ZMod 5) ∨ N = ⊤ := by
  have hsimple : IsSimpleGroup PSL(2, ZMod 5) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; norm_num)
  have hker : (mk : SL(2, ZMod 5) →* PSL(2, ZMod 5)).ker = center SL(2, ZMod 5) :=
    QuotientGroup.ker_mk' _
  have : (N.map (mk : SL(2, ZMod 5) →* PSL(2, ZMod 5))).Normal :=
    Subgroup.Normal.map inferInstance _ mk_surjective
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map (mk : SL(2, ZMod 5) →* PSL(2, ZMod 5))) with
    h | h
  · have hle : N ≤ center SL(2, ZMod 5) := by
      rw [← hker]
      exact (Subgroup.map_eq_bot_iff N).mp h
    by_cases hneg : (-1 : SL(2, ZMod 5)) ∈ N
    · right; left
      refine le_antisymm hle fun z hz => ?_
      rcases (mem_center_SL_iff z).mp hz with rfl | rfl
      · exact N.one_mem
      · exact hneg
    · left
      refine eq_bot_iff.2 fun z hz => ?_
      rcases (mem_center_SL_iff z).mp (hle hz) with rfl | rfl
      · exact Subgroup.one_mem _
      · exact absurd hz hneg
  · right; right
    have hsup : N ⊔ center SL(2, ZMod 5) = ⊤ := by
      have := Subgroup.comap_map_eq (mk : SL(2, ZMod 5) →* PSL(2, ZMod 5)) N
      rwa [h, Subgroup.comap_top, hker, eq_comm] at this
    have hcomm := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup
      (inferInstance : IsMulCommutative (center SL(2, ZMod 5)))
    rw [_root_.commutator_def, perfect_sl2_zmod_five] at hcomm
    exact top_le_iff.mp hcomm

private theorem exists_conj_unipSL {P : Subgroup SL(2, ZMod 5)} (hP : Nat.card ↥P = 5) :
    ∃ a : SL(2, ZMod 5), ∀ y, y ∈ P ↔ a⁻¹ * y * a ∈ unipSL (ZMod 5) := by
  have hcardU : Nat.card ↥(unipSL (ZMod 5)) =
      5 ^ (Nat.card SL(2, ZMod 5)).factorization 5 := by
    rw [card_unipSL, Nat.card_zmod, factorization_card_sl2_zmod_five]
    norm_num
  have hcardP : Nat.card ↥P = 5 ^ (Nat.card SL(2, ZMod 5)).factorization 5 := by
    rw [hP, factorization_card_sl2_zmod_five]
    norm_num
  let SU : Sylow 5 SL(2, ZMod 5) := Sylow.ofCard (unipSL (ZMod 5)) hcardU
  let SP : Sylow 5 SL(2, ZMod 5) := Sylow.ofCard P hcardP
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq SL(2, ZMod 5) SU SP
  refine ⟨a, fun y => ?_⟩
  have h1 : (SP : Subgroup SL(2, ZMod 5)) = P := Sylow.coe_ofCard P hcardP
  have h2 : (SU : Subgroup SL(2, ZMod 5)) = unipSL (ZMod 5) := Sylow.coe_ofCard _ hcardU
  rw [← h1, ← ha, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, h2]
  simp [MulAut.smul_def]

private theorem sup_eq_top_of_card_five {P Q : Subgroup SL(2, ZMod 5)} (hP : Nat.card ↥P = 5)
    (hQ : Nat.card ↥Q = 5) (hPQ : P ≠ Q) : P ⊔ Q = ⊤ := by
  obtain ⟨a, ha⟩ := exists_conj_unipSL hP
  obtain ⟨b, hb⟩ := exists_conj_unipSL hQ
  exact sup_eq_top_of_conj_unipSL ha hb hPQ

end ZMod5

theorem sl2_five_card {K : Type} [Group K] (e : SL(2, ZMod 5) ≃* K) : Nat.card K = 120 := by
  rw [← Nat.card_congr e.toEquiv]
  exact card_sl2_zmod_five

theorem sl2_five_center_card {K : Type} [Group K] (e : SL(2, ZMod 5) ≃* K) :
    Nat.card ↥(Subgroup.center K) = 2 := by
  rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]
  exact card_center_sl2_zmod_five

theorem sl2_five_perfect {K : Type} [Group K] (e : SL(2, ZMod 5) ≃* K) :
    ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ := by
  have h := congrArg (Subgroup.map (e : SL(2, ZMod 5) →* K)) perfect_sl2_zmod_five
  rwa [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective] at h

theorem sl2_five_normal_cases {K : Type} [Group K] (e : SL(2, ZMod 5) ≃* K) (N : Subgroup K)
    [N.Normal] : N = ⊥ ∨ N = Subgroup.center K ∨ N = ⊤ := by
  have hmap : (N.comap (e : SL(2, ZMod 5) →* K)).map (e : SL(2, ZMod 5) →* K) = N :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective N
  rcases normal_cases_sl2_zmod_five (N.comap (e : SL(2, ZMod 5) →* K)) with h | h | h
  · left
    rw [← hmap, h, Subgroup.map_bot]
  · right; left
    rw [← hmap, h, Subgroup.map_center_eq e]
  · right; right
    rw [← hmap, h, Subgroup.map_top_of_surjective _ e.surjective]

theorem sl2_five_sylow_gen {K : Type} [Group K] (e : SL(2, ZMod 5) ≃* K) {P Q : Subgroup K}
    (hP : Nat.card ↥P = 5) (hQ : Nat.card ↥Q = 5) (hPQ : P ≠ Q) : P ⊔ Q = ⊤ := by
  have hcard : ∀ R : Subgroup K, Nat.card ↥R = 5 →
      Nat.card ↥(R.comap (e : SL(2, ZMod 5) →* K)) = 5 := fun R hR => by
    rw [Subgroup.comap_equiv_eq_map_symm, Subgroup.card_map_of_injective e.symm.injective, hR]
  have hne : P.comap (e : SL(2, ZMod 5) →* K) ≠ Q.comap (e : SL(2, ZMod 5) →* K) :=
    fun h => hPQ (Subgroup.comap_injective e.surjective h)
  have h := sup_eq_top_of_card_five (hcard P hP) (hcard Q hQ) hne
  rw [Subgroup.comap_sup_eq (e : SL(2, ZMod 5) →* K) P Q e.surjective] at h
  exact Subgroup.comap_injective e.surjective (by rw [h, Subgroup.comap_top])

end CFSG.GH74.GLS.LU.Local.Five
