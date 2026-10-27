module

public import CFSG.ClassicalInvolution.Phan.Phan3B3Order
public import CFSG.ClassicalInvolution.Phan.Phan3Sp4Pres
public import CFSG.ClassicalInvolution.Phan.Phan3D4CT

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.CosetTable CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair)
open scoped MatrixGroups

@[expose] def commWordN {n : ℕ} (g h : Fin n) : List (Fin n × Bool) :=
  [(g, true), (h, true), (g, false), (h, false)]

theorem eq_comm_of_wordVal_commWordN {Y : Type*} [Group Y] {n : ℕ} (x : Fin n → Y) {g h : Fin n}
    (hw : wordVal x (commWordN g h) = 1) : x g * x h = x h * x g := by
  simp only [commWordN, wordVal, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    letterVal, Bool.cond_true, Bool.cond_false, mul_one] at hw
  have h1 : x g * x h * ((x g)⁻¹ * (x h)⁻¹) = 1 := by rw [mul_assoc]; exact hw
  rw [← mul_inv_rev] at h1
  exact mul_inv_eq_one.1 h1

theorem commWordN_mem_b3CtCommRels :
    ∀ p ∈ ([(0, 4), (0, 5), (1, 4), (1, 5)] : List (Fin 6 × Fin 6)),
      commWordN p.1 p.2 ∈ b3CtCommRels := by
  decide +kernel

@[expose] def b3SlEmb : Fin 4 → Fin 6 := ![0, 1, 2, 3]

@[expose] def b3SpEmb : Fin 4 → Fin 6 := ![2, 3, 4, 5]

theorem b3Sl3EdgeRels_eq :
    b3Sl3EdgeRels = sl3Rels.map (List.map fun l => (b3SlEmb l.1, l.2)) := by
  decide +kernel

theorem b3Sp4EdgeRels_eq :
    b3Sp4EdgeRels = sp4Rels.map (List.map fun l => (b3SpEmb l.1, l.2)) := by
  decide +kernel

theorem exists_b3_gen : ∀ j : Fin 6, (∃ g, b3SlEmb g = j) ∨ ∃ g, b3SpEmb g = j := by
  decide +kernel

theorem exists_b3_node : ∀ j : Fin 6, ∃ k : Fin 3,
    j = ⟨2 * k.val, by omega⟩ ∨ j = ⟨2 * k.val + 1, by omega⟩ := by
  decide +kernel

variable (hc : B3Checks)

section Simple

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
  (π : PhanB3Group →* G) (hπ : Function.Surjective π)

@[expose] noncomputable def b3CtG (π : PhanB3Group →* G) (k : Fin 6) : G := π (b3CtEltP k)

@[expose] def b3CtNode (π : PhanB3Group →* G) (k : Fin 3) : Subgroup G :=
  Subgroup.closure {b3CtG π ⟨2 * k.val, by omega⟩, b3CtG π ⟨2 * k.val + 1, by omega⟩}

include hc hnab hπ

theorem wordVal_b3CtG_eq_one {v : List (Fin 6 × Bool)}
    (h : v ∈ b3Sl3EdgeRels ++ b3Sp4EdgeRels ++ b3CtCommRels) : wordVal (b3CtG π) v = 1 := by
  obtain ⟨N, hN, h1, -⟩ := exists_ker_le_ker hc hnab π hπ
  have h3 := hN (h1 v h)
  rw [MonoidHom.mem_ker] at h3
  have h4 : wordVal (b3CtG π) v = π (wordVal b3CtEltP v) := wordVal_map π b3CtEltP v
  rw [h4, h3]

theorem wordVal_b3CtG_eq_gen (i : Fin 8) :
    wordVal (b3CtG π) (decodeWord 6 b3PhanInCtCodes[i.val]!) = π (PresentedGroup.of i) := by
  obtain ⟨N, hN, -, h2⟩ := exists_ker_le_ker hc hnab π hπ
  have h3 := hN (h2 i)
  rw [MonoidHom.mem_ker, map_mul, map_inv] at h3
  have h4 : wordVal (b3CtG π) (decodeWord 6 b3PhanInCtCodes[i.val]!) =
      π (wordVal b3CtEltP (decodeWord 6 b3PhanInCtCodes[i.val]!)) := wordVal_map π b3CtEltP _
  rw [h4]
  exact inv_mul_eq_one.1 h3

theorem exists_b3CtG_ne_one : ∃ j : Fin 6, b3CtG π j ≠ 1 := by
  by_contra hcon
  have hcon' : ∀ j, b3CtG π j = 1 := fun j => not_not.1 fun h => hcon ⟨j, h⟩
  have h1 : ∀ i : Fin 8, π (PresentedGroup.of i) = 1 := fun i => by
    rw [← wordVal_b3CtG_eq_gen hc hnab π hπ i]
    exact wordVal_eq_one_of_forall _ hcon' _
  have h2 : π = 1 := PresentedGroup.ext fun i => by rw [h1 i]; rfl
  obtain ⟨x, y, hxy⟩ := hnab
  obtain ⟨px, rfl⟩ := hπ x
  obtain ⟨py, rfl⟩ := hπ y
  rw [h2] at hxy
  exact hxy (by simp)

theorem exists_b3EdgeHoms {K : Type} [Field K] (hK : Nat.card K = 3) :
    ∃ (θA : SL(3, K) →* G) (θB : StatedSp 2 (ZMod 3) →* G),
      (∀ g, θA (sl3Gen K g) = b3CtG π (b3SlEmb g)) ∧
      (∀ g, θB (sp4Gen g) = b3CtG π (b3SpEmb g)) ∧
      θA.ker ≤ Subgroup.center SL(3, K) ∧
      θB.ker ≤ Subgroup.center (StatedSp 2 (ZMod 3)) := by
  obtain ⟨θA, hA⟩ := sl3_lift_of_card hK hc.sl3 (fun g => b3CtG π (b3SlEmb g)) (by
    intro r hr
    have h1 := wordVal_map_reindex (MonoidHom.id G) (b3CtG π) (fun g => b3CtG π (b3SlEmb g))
      b3SlEmb (fun g => rfl) r
    rw [MonoidHom.id_apply] at h1
    rw [← h1]
    refine wordVal_b3CtG_eq_one hc hnab π hπ
      (List.mem_append_left _ (List.mem_append_left _ ?_))
    rw [b3Sl3EdgeRels_eq]
    exact List.mem_map.2 ⟨r, hr, rfl⟩)
  obtain ⟨θB, hB⟩ := sp4_lift_of_card hc.sp4 (fun g => b3CtG π (b3SpEmb g)) (by
    intro r hr
    have h1 := wordVal_map_reindex (MonoidHom.id G) (b3CtG π) (fun g => b3CtG π (b3SpEmb g))
      b3SpEmb (fun g => rfl) r
    rw [MonoidHom.id_apply] at h1
    rw [← h1]
    refine wordVal_b3CtG_eq_one hc hnab π hπ
      (List.mem_append_left _ (List.mem_append_right _ ?_))
    rw [b3Sp4EdgeRels_eq]
    exact List.mem_map.2 ⟨r, hr, rfl⟩)
  have hA2 : θA (sl3Gen K 2) = b3CtG π 2 := hA 2
  have hB0 : θB (sp4Gen 0) = b3CtG π 2 := hB 0
  have hne : b3CtG π 2 ≠ 1 := by
    intro h2
    have hθA : θA = 1 := sl3_hom_eq_one_of_gen hK θA 2 (by rw [hA2, h2])
    have hθB : θB = 1 := sp4_hom_eq_one_of_gen θB 0 (by rw [hB0, h2])
    obtain ⟨j, hj⟩ := exists_b3CtG_ne_one hc hnab π hπ
    apply hj
    obtain ⟨g, rfl⟩ | ⟨g, rfl⟩ := exists_b3_gen j
    · rw [← hA g, hθA]
      rfl
    · rw [← hB g, hθB]
      rfl
  have hAne : ∀ g, θA (sl3Gen K g) ≠ 1 := fun g h => hne (by
    have := sl3_hom_eq_one_of_gen hK θA g h
    rw [← hA2, this]
    rfl)
  have hBne : ∀ g, θB (sp4Gen g) ≠ 1 := fun g h => hne (by
    have := sp4_hom_eq_one_of_gen θB g h
    rw [← hB0, this]
    rfl)
  exact ⟨θA, θB, hA, hB, sl3_ker_le_center θA 0 (hAne 0), sp4_ker_le_center θB 0 (hBne 0)⟩

theorem b3CtNode_commutes : ∀ a ∈ b3CtNode π 0, ∀ b ∈ b3CtNode π 2, a * b = b * a := by
  have hgen : ∀ p ∈ ([(0, 4), (0, 5), (1, 4), (1, 5)] : List (Fin 6 × Fin 6)),
      b3CtG π p.1 * b3CtG π p.2 = b3CtG π p.2 * b3CtG π p.1 := fun p hp =>
    eq_comm_of_wordVal_commWordN _ (wordVal_b3CtG_eq_one hc hnab π hπ
      (List.mem_append_right _ (commWordN_mem_b3CtCommRels p hp)))
  refine commutes_closure ?_
  intro s hs t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · exact hgen (0, 4) (by simp)
  · exact hgen (0, 5) (by simp)
  · exact hgen (1, 4) (by simp)
  · exact hgen (1, 5) (by simp)

theorem iSup_b3CtNode : ⨆ k, b3CtNode π k = ⊤ := by
  have h2 : (⊤ : Subgroup PhanB3Group).map π ≤ Subgroup.closure (Set.range (b3CtG π)) := by
    rw [← PresentedGroup.closure_range_of, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, ← wordVal_b3CtG_eq_gen hc hnab π hπ i]
    exact wordVal_mem_closure_range _ _
  have h3 : Subgroup.closure (Set.range (b3CtG π)) ≤ ⨆ k, b3CtNode π k := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := exists_b3_node j
    refine Subgroup.mem_iSup_of_mem k (Subgroup.subset_closure ?_)
    rcases hk with rfl | rfl
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ rfl
  rw [eq_top_iff]
  intro g _
  obtain ⟨p, rfl⟩ := hπ g
  exact h3 (h2 ⟨p, Subgroup.mem_top _, rfl⟩)

theorem exists_b3CtChain {K : Type} [Field K] (hK : Nat.card K = 3) :
    ∃ U : Fin 3 → Subgroup G, (∀ a ∈ U 0, ∀ b ∈ U 2, a * b = b * a) ∧
      (∃ W, WeakCT.LinearBlockStandardPair K W (U 0) (U 1)) ∧
      (∃ W, SymplecticBlockPair K W (U 1) (U 2)) ∧ ⨆ k, U k = ⊤ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨θA, θB, hA, hB, hkerA, hkerB⟩ := exists_b3EdgeHoms hc hnab π hπ hK
  refine ⟨b3CtNode π, b3CtNode_commutes hc hnab π hπ, ?_, ?_, iSup_b3CtNode hc hnab π hπ⟩
  · refine ⟨_, linearBlockStandardPair_of_hom hK θA hkerA ?_ ?_⟩
    · rw [hA 0, hA 1]
      rfl
    · rw [hA 2, hA 3]
      rfl
  · refine symplecticBlockPair_of_hom hK θB hkerB ?_ ?_
    · rw [hB 0, hB 1]
      rfl
    · rw [hB 2, hB 3]
      rfl

end Simple

end CFSG.ClassicalInvolution.Phan.Q3G
