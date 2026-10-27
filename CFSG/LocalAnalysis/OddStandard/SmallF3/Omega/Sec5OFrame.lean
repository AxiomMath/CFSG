module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Center
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BAab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OFacts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec5o_mem_normalizer_of_type {L : Subgroup G} {s : G} {n : ℕ} {ε : ℤˣ} {k : ℕ} {α : ℤˣ}
    (h : InducesTypeSome L s n ε k α) : s ∈ normalizer (L : Set G) := by
  obtain ⟨V, _, _, _, Q, hQ, e, x, -, -, hind, -⟩ := h
  exact hind.1

theorem sec5o_t_mem_centerIn [Finite G] (h52b : Asc82Lemma52b) {t : G} {L : Subgroup G}
    (hs : Sec5Setting G t L) : t ∈ centerIn L := by
  have h1 : twoCoreIn L = zpowers t := (h52b G t L hs).2
  have h2 := sec5_twoCoreIn_le_centerIn hs.component.isQuasisimple
  exact h2 (h1 ▸ Subgroup.mem_zpowers t)

theorem sec5o_t_mem_centralizer [Finite G] (h52b : Asc82Lemma52b) {t : G} {L : Subgroup G}
    (hs : Sec5Setting G t L) : t ∈ centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact ((sec5_mem_centerIn_iff.mp (sec5o_t_mem_centerIn h52b hs)).2 y hy).symm

private theorem sec5o_eq_of_sq_eq_one_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {a b : C} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  classical
  haveI : Fintype C := Fintype.ofFinite C
  by_contra hab
  have hle := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) (by norm_num)
  have hsub : ({1, a, b} : Finset C) ⊆ Finset.univ.filter (fun c : C => c ^ 2 = 1) := by
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hc with rfl | rfl | rfl
    · exact one_pow 2
    · exact ha
    · exact hb
  have hcard : ({1, a, b} : Finset C).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm ha1, Ne.symm hb1⟩), Finset.card_pair hab]
  have := Finset.card_le_card hsub
  change _ ≤ (Finset.univ.filter (fun c : C => c ^ 2 = 1)).card at this
  have h2 : (Finset.univ.filter (fun c : C => c ^ 2 = 1)).card ≤ 2 := by
    convert hle using 2
  omega

theorem sec5o_eq_one_or_t_of_mem_A_cent [Finite G] (h52a : Asc82Lemma52a)
    (h52b : Asc82Lemma52b) {t : G} {L S : Subgroup G} {z r : G} {B A : Subgroup G}
    (hR : Sec5RCtx G t L S z r B A) {x : G} (hxA : x ∈ A) (hxC : x ∈ centralizer (L : Set G)) :
    x = 1 ∨ x = t := by
  classical
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  right
  by_contra hxt
  have hs : Sec5Setting G t L := hR.toSec5Ctx.toSec5Setting
  have htC : t ∈ centralizer (L : Set G) := sec5o_t_mem_centralizer h52b hs
  obtain ⟨hAcomm, hAsq⟩ := sec5b_A_elemAb hR
  have htA : t ∈ A := (sec5b_card_t_mem hR).2
  have ht1 : t ≠ 1 := by
    intro h
    have h2 := hR.involution
    rw [h, orderOf_one] at h2
    norm_num at h2
  let H : Subgroup G := centralizer (L : Set G)
  have hApg : IsPGroup 2 ↥(A.subgroupOf H) := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa only [pow_one, pow_two, Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one]
      using hAsq (g : G) g.2
  obtain ⟨Q, hQ⟩ := hApg.exists_le_sylow
  haveI : IsCyclic ↥(Q : Subgroup ↥H) := h52a G t L hs Q
  let x' : ↥H := ⟨x, hxC⟩
  let t' : ↥H := ⟨t, htC⟩
  have hx'Q : x' ∈ (Q : Subgroup ↥H) := hQ (show x' ∈ A.subgroupOf H from hxA)
  have ht'Q : t' ∈ (Q : Subgroup ↥H) := hQ (show t' ∈ A.subgroupOf H from htA)
  let xQ : ↥(Q : Subgroup ↥H) := ⟨x', hx'Q⟩
  let tQ : ↥(Q : Subgroup ↥H) := ⟨t', ht'Q⟩
  have hxQ2 : xQ ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    show (x : G) ^ 2 = 1
    rw [pow_two]
    exact hAsq x hxA
  have htQ2 : tQ ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    show (t : G) ^ 2 = 1
    rw [pow_two]
    exact hAsq t htA
  have hxQ1 : xQ ≠ 1 := by
    intro h
    refine hx1 ?_
    have := congrArg (fun y : ↥(Q : Subgroup ↥H) => (((y : ↥H) : G))) h
    simpa [xQ, x'] using this
  have htQ1 : tQ ≠ 1 := by
    intro h
    refine ht1 ?_
    have := congrArg (fun y : ↥(Q : Subgroup ↥H) => (((y : ↥H) : G))) h
    simpa [tQ, t'] using this
  have hxt' : x' ≠ t' := by
    intro h
    refine hxt ?_
    have := congrArg (fun y : ↥H => (y : G)) h
    simpa [x', t'] using this
  have hxQtQ : xQ ≠ tQ := by
    intro h
    refine hxt' ?_
    have := congrArg (fun y : ↥(Q : Subgroup ↥H) => (y : ↥H)) h
    simpa [xQ, tQ] using this
  exact hxQtQ (sec5o_eq_of_sq_eq_one_of_isCyclic hxQ2 htQ2 hxQ1 htQ1)

private theorem sec5o_weight_single_add {i j : Fin 6} (hij : i ≠ j) :
    vecWeight (Pi.single i (1 : ZMod 2) + Pi.single j 1) = 2 := by
  revert i j
  decide +kernel

private theorem sec5o_single_add_not_mem_centralizer [Finite G] (h52a : Asc82Lemma52a)
    (h52b : Asc82Lemma52b) {t : G} {L S : Subgroup G} {z r : G} {B A : Subgroup G}
    {φ : (Fin 6 → ZMod 2) → G} (hR : Sec5RCtx G t L S z r B A) (hm : Sec5Model58 t L z r A φ)
    {i j : Fin 6} (hij : i ≠ j) :
    φ (Pi.single i 1 + Pi.single j 1) ∉ centralizer (L : Set G) := by
  intro hmem
  have hw := sec5o_weight_single_add hij
  rcases sec5o_eq_one_or_t_of_mem_A_cent h52a h52b hR (hm.perm.mem _) hmem with h1 | ht
  · have hv := hm.perm.injective (h1.trans hm.perm.map_zero.symm)
    have hw0 : vecWeight (Pi.single i 1 + Pi.single j 1) = 0 := by
      rw [hv, sec5b6_vecWeight_zero]
    rw [hw] at hw0
    norm_num at hw0
  · have hone : φ (1 : Fin 6 → ZMod 2) = t := by simpa only [Pi.one_def] using hm.map_one
    have hv := hm.perm.injective (ht.trans hone.symm)
    have hw6 : vecWeight (Pi.single i 1 + Pi.single j 1) = 6 := by
      rw [hv, sec5b6_vecWeight_one]
    rw [hw] at hw6
    norm_num at hw6

theorem sec5o_frame_even [Finite G] (hF : Asc82FactFrame6) (h52a : Asc82Lemma52a)
    (h52b : Asc82Lemma52b) {t : G} {L S : Subgroup G} {z r : G} {B A : Subgroup G}
    {φ : (Fin 6 → ZMod 2) → G} (hR : Sec5RCtx G t L S z r B A) (hm : Sec5Model58 t L z r A φ)
    {x : G} (hx : x ∈ L ⊔ centralizer (L : Set G)) {σ : Equiv.Perm (Fin 6)}
    (hσ : ∀ i : Fin 6, x⁻¹ * φ (Pi.single i 1) * x * (φ (Pi.single (σ i) 1))⁻¹ ∈
      centralizer (L : Set G)) : Equiv.Perm.sign σ = 1 := by
  have hs : Sec5Setting G t L := hR.toSec5Ctx.toSec5Setting
  refine hF G L (fun i => φ (Pi.single i 1)) hs.isOm6Z2 ?_ ?_ ?_ x hx σ hσ
  · intro i
    obtain ⟨α, hα⟩ := hm.type_one (Pi.single i 1) (Or.inl (sec5b6_vecWeight_single i))
    exact ⟨sec5o_mem_normalizer_of_type hα, α, hα⟩
  · intro i j
    rw [← hm.perm.map_add (Pi.single i 1) (Pi.single j 1), add_comm,
      hm.perm.map_add (Pi.single j 1) (Pi.single i 1)]
  · intro i j hij
    constructor
    · have hL : φ (Pi.single i 1 + Pi.single j 1) ∈ L :=
        (hm.mem_L _).mpr ((sec5b6_isEvenVec_iff _).mpr (by
          rw [sec5o_weight_single_add hij]; norm_num))
      rw [← hm.perm.map_add (Pi.single i 1) (Pi.single j 1)]
      exact Subgroup.mem_sup_left hL
    · intro hmem
      have hj2 : φ (Pi.single j 1) * φ (Pi.single j 1) = 1 :=
        (sec5b_A_elemAb hR).2 _ (hm.perm.mem _)
      have hinv : (φ (Pi.single j 1))⁻¹ = φ (Pi.single j 1) :=
        (eq_inv_of_mul_eq_one_right hj2).symm
      have hprod : φ (Pi.single i 1) * (φ (Pi.single j 1))⁻¹ =
          φ (Pi.single i 1 + Pi.single j 1) := by
        rw [hinv, ← hm.perm.map_add (Pi.single i 1) (Pi.single j 1)]
      rw [hprod] at hmem
      exact sec5o_single_add_not_mem_centralizer h52a h52b hR hm hij hmem

end CFSG.OddStandard.SmallF3.Omega
