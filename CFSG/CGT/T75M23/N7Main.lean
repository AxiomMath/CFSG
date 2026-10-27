module

public import CFSG.CGT.T75M23.N7Branch
public import CFSG.CGT.T75M23.N7Sem6
public import CFSG.CGT.T75M23.N7Split

public section

namespace CFSG.CGT.T75M23

open CFSG.CGT.T75JM CFSG.CosetTable

variable {G : Type*} [Group G] {T : Subgroup G}

@[expose] def tGen7 (i : Fin 4) : PG 6 rels7 := PresentedGroup.of (⟨2 + i.val, by omega⟩ : Fin 6)

theorem exists_mulEquiv_normalizer7
    (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hsq : ∀ a ∈ T, a ^ 2 = 1) (h16 : Nat.card T = 16)
    (hC : Subgroup.centralizer (T : Set G) = T) (φ : NQ T ≃* alternatingGroup (Fin 7))
    (hmod : ModClass7) (hnodup : A7Nodup)
    (hcard : Finite (PG 6 rels7) ∧ Nat.card (PG 6 rels7) ≤ 40320) :
    ∃ Ψ : PG 6 rels7 ≃* Subgroup.normalizer (T : Set G),
      Subgroup.map Ψ.toMonoidHom (Subgroup.closure (Set.range tGen7)) =
        T.subgroupOf (Subgroup.normalizer (T : Set G)) := by
  classical
  obtain ⟨c⟩ := exists_coords hcomm hsq h16
  obtain ⟨D, hD1, hD2⟩ := exists_complement_normalizer7 hcomm hsq h16 hC φ
  obtain ⟨g, h, hrel, hcl, hequiv⟩ := branch_data7 c hC φ D hD1 hD2 hmod hnodup
  obtain ⟨Q, Qi, hQ⟩ := hequiv
  set c' := c.change Q Qi hQ.1 hQ.2.1 (fun v hv => hQ.left_inv hv) (fun v hv => hQ.right_inv hv)
    with hc'
  have hgX : colsOf c' g = modelX7 := by
    apply cols_ext
    intro i
    have h2i : 2 ^ i.val < 16 := by fin_cases i <;> decide
    rw [colsOf_change c Q Qi hQ.1 hQ.2.1 (fun v hv => hQ.left_inv hv)
      (fun v hv => hQ.right_inv hv) g _ h2i, hQ.intertwine_x,
      hQ.left_inv (applyC_lt modelX7_lt _)]
  have hhY : colsOf c' h = modelY7 := by
    apply cols_ext
    intro i
    have h2i : 2 ^ i.val < 16 := by fin_cases i <;> decide
    rw [colsOf_change c Q Qi hQ.1 hQ.2.1 (fun v hv => hQ.left_inv hv)
      (fun v hv => hQ.right_inv hv) h _ h2i, hQ.intertwine_y,
      hQ.left_inv (applyC_lt modelY7_lt _)]
  have hsem := sem7_of_data c' g h hgX hhY hrel.x2 hrel.y5 hrel.r3 hrel.r4 hrel.r5
  set Tn := T.subgroupOf (Subgroup.normalizer (T : Set G)) with hTn
  set f : Fin 6 → Subgroup.normalizer (T : Set G) :=
    ![g, h, tN c' 0, tN c' 1, tN c' 2, tN c' 3] with hf
  let Φ : PG 6 rels7 →* Subgroup.normalizer (T : Set G) :=
    PresentedGroup.toGroup (f := f) fun r hr => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
      exact lift_rels7_eq_one hsem w hw
  have hmem : ∀ j : Fin 6, f j ∈ Φ.range := fun j => ⟨PresentedGroup.of j,
    PresentedGroup.toGroup.of _⟩
  set S := Subgroup.map Φ (Subgroup.closure (Set.range tGen7)) with hS
  have hSt : ∀ j : Fin 4, f ⟨2 + j.val, by omega⟩ ∈ S := fun j =>
    ⟨tGen7 j, Subgroup.subset_closure ⟨j, rfl⟩, PresentedGroup.toGroup.of _⟩
  have hpart : ∀ (b : Bool) (n : ℕ), (n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8) →
      inN (tOf c' (if b then n else 0)) ∈ S := by
    intro b n hn
    cases b
    · simp only [Bool.false_eq_true, ite_false, tOf_zero c']
      exact S.one_mem
    · simp only [ite_true]
      rcases hn with rfl | rfl | rfl | rfl
      · exact hSt 0
      · exact hSt 1
      · exact hSt 2
      · exact hSt 3
  have hT : ∀ t : T, inN t ∈ S := by
    intro t
    rw [decomp c' t]
    simp only [← inN_mul]
    refine S.mul_mem (S.mul_mem (hpart _ _ (by simp)) (hpart _ _ (by simp)))
      (S.mul_mem (hpart _ _ (by simp)) (hpart _ _ (by simp)))
  have hSR : S ≤ Φ.range := Subgroup.map_le_range _ _
  have hDR : D ≤ Φ.range := by
    rw [← hcl, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hmem 0
    · exact hmem 1
  have hsurj : Function.Surjective Φ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff]
    intro x _
    have hx : x ∈ Tn ⊔ D := by rw [hD2]; exact Subgroup.mem_top x
    obtain ⟨t, ht, d, hd, hmul⟩ := Subgroup.mem_sup_of_normal_left.1 hx
    rw [← hmul]
    have ht' : t = inN (⟨((t : Subgroup.normalizer (T : Set G)) : G), ht⟩ : T) := Subtype.ext rfl
    rw [ht']
    exact Φ.range.mul_mem (hSR (hT _)) (hDR hd)
  have hcardN : Nat.card (Subgroup.normalizer (T : Set G)) = 40320 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Tn]
    have hq : Nat.card (NQ T) = 2520 := (Nat.card_congr φ.toEquiv).trans card_alt7
    have ht : Nat.card Tn = 16 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv).trans h16
    rw [hq, ht]
  have hfinN : Finite (Subgroup.normalizer (T : Set G)) :=
    Nat.finite_of_card_ne_zero (by rw [hcardN]; norm_num)
  obtain ⟨hfin, hle⟩ := hcard
  have hbij : Function.Bijective Φ := hsurj.bijective_of_nat_card_le (by rw [hcardN]; exact hle)
  refine ⟨MulEquiv.ofBijective Φ hbij, ?_⟩
  show S = Tn
  refine le_antisymm ?_ ?_
  · rw [hS, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    have h0 : Φ (tGen7 i) = f ⟨2 + i.val, by omega⟩ := PresentedGroup.toGroup.of _
    have h1 : f ⟨2 + i.val, by omega⟩ = tN c' i.val := by fin_cases i <;> rfl
    show Φ (tGen7 i) ∈ Tn
    rw [h0, h1]
    exact (tOf c' (2 ^ i.val)).2
  · intro x hx
    have : x = inN (⟨(x : G), hx⟩ : T) := Subtype.ext rfl
    rw [this]
    exact hT _

end CFSG.CGT.T75M23
