module

public import CFSG.LargeExtraspecial.S12TriGNative

public section

namespace CFSG.LargeExtraspecial.S12Tri

open Equiv Subgroup

theorem card_mulAut_le_of_closure {G : Type*} [Group G] {a b : G}
    (hgen : closure ({a, b} : Set G) = ⊤) (S : Set (G × G)) [Finite S]
    (hS : ∀ σ : MulAut G, (σ a, σ b) ∈ S) : Nat.card (MulAut G) ≤ Nat.card S := by
  refine Nat.card_le_card_of_injective (fun σ => ⟨(σ a, σ b), hS σ⟩) fun σ τ h => ?_
  have h1 : σ a = τ a := congrArg (fun p : S => (p : G × G).1) h
  have h2 : σ b = τ b := congrArg (fun p : S => (p : G × G).2) h
  have hst : σ.toMonoidHom = τ.toMonoidHom := MonoidHom.eq_of_eqOn_dense hgen (by
    rintro x (rfl | rfl)
    · exact h1
    · exact h2)
  exact MulEquiv.ext fun x => DFunLike.congr_fun hst x

theorem a6_parts
    : (bfs 16).length = 360 ∧ a6Pair a6a a6b = true ∧ a6Count ≤ 1440 := by
  have h := a6Check_eq
  simp only [a6Check, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem a5_parts
    : (bfs5 12).length = 60 ∧ a5Pair a5a a5b = true ∧ a5Count ≤ 120 := by
  have h := a5Check_eq
  simp only [a5Check, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem a6Pair_iff {x y : Perm (Fin 6)} : a6Pair x y = true ↔ x ^ 2 = 1 ∧ x ≠ 1 ∧ y ^ 4 = 1 ∧
    y ^ 2 ≠ 1 ∧ (x * y) ^ 5 = 1 ∧ x * y ≠ 1 ∧ Perm.sign x = 1 ∧ Perm.sign y = 1 := by
  simp only [a6Pair, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem a5Pair_iff {x y : Perm (Fin 5)} : a5Pair x y = true ↔ x ^ 2 = 1 ∧ x ≠ 1 ∧ y ^ 3 = 1 ∧
    y ≠ 1 ∧ (x * y) ^ 5 = 1 ∧ x * y ≠ 1 ∧ Perm.sign x = 1 ∧ Perm.sign y = 1 := by
  simp only [a5Pair, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem mem_closure_of_mem_bfs : ∀ n, ∀ x ∈ bfs n, x ∈ closure ({a6a, a6b} : Set (Perm (Fin 6)))
  | 0, x, hx => by
    simp only [bfs, List.mem_singleton] at hx
    rw [hx]
    exact one_mem _
  | n + 1, x, hx => by
    simp only [bfs, bfsStep, List.mem_dedup, List.mem_append, List.mem_map] at hx
    rcases hx with (hx | ⟨y, hy, rfl⟩) | ⟨y, hy, rfl⟩
    · exact mem_closure_of_mem_bfs n x hx
    · exact mul_mem (subset_closure (by simp)) (mem_closure_of_mem_bfs n y hy)
    · exact mul_mem (subset_closure (by simp)) (mem_closure_of_mem_bfs n y hy)

theorem mem_closure_of_mem_bfs5 :
    ∀ n, ∀ x ∈ bfs5 n, x ∈ closure ({a5a, a5b} : Set (Perm (Fin 5)))
  | 0, x, hx => by
    simp only [bfs5, List.mem_singleton] at hx
    rw [hx]
    exact one_mem _
  | n + 1, x, hx => by
    simp only [bfs5, bfs5Step, List.mem_dedup, List.mem_append, List.mem_map] at hx
    rcases hx with (hx | ⟨y, hy, rfl⟩) | ⟨y, hy, rfl⟩
    · exact mem_closure_of_mem_bfs5 n x hx
    · exact mul_mem (subset_closure (by simp)) (mem_closure_of_mem_bfs5 n y hy)
    · exact mul_mem (subset_closure (by simp)) (mem_closure_of_mem_bfs5 n y hy)

theorem le_card_closure_of_list {P : Type*} [Group P] [DecidableEq P] [Finite P] {S : Set P}
    {L : List P} (hnd : L.Nodup) (hL : ∀ x ∈ L, x ∈ closure S) :
    L.length ≤ Nat.card (closure S) := by
  have hsub : (L.toFinset : Set P) ⊆ closure S := fun x hx => hL x (List.mem_toFinset.1 hx)
  calc L.length = (L.toFinset : Set P).ncard := by
        rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
    _ ≤ (closure S : Set P).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = Nat.card (closure S) := (Nat.card_coe_set_eq _).symm

theorem closure_a6
    : closure ({a6a, a6b} : Set (Perm (Fin 6))) = alternatingGroup (Fin 6) := by
  obtain ⟨hlen, hpair, -⟩ := a6_parts
  obtain ⟨-, -, -, -, -, -, hsa, hsb⟩ := a6Pair_iff.1 hpair
  have hle : closure ({a6a, a6b} : Set (Perm (Fin 6))) ≤ alternatingGroup (Fin 6) := by
    rw [closure_le]
    rintro x (rfl | rfl)
    · exact Perm.mem_alternatingGroup.2 hsa
    · exact Perm.mem_alternatingGroup.2 hsb
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hnd : (bfs 16).Nodup := List.nodup_dedup _
  calc Nat.card (alternatingGroup (Fin 6)) = 360 := by
        rw [nat_card_alternatingGroup, Nat.card_fin]; rfl
    _ = (bfs 16).length := hlen.symm
    _ ≤ _ := le_card_closure_of_list hnd (mem_closure_of_mem_bfs 16)

theorem closure_a5
    : closure ({a5a, a5b} : Set (Perm (Fin 5))) = alternatingGroup (Fin 5) := by
  obtain ⟨hlen, hpair, -⟩ := a5_parts
  obtain ⟨-, -, -, -, -, -, hsa, hsb⟩ := a5Pair_iff.1 hpair
  have hle : closure ({a5a, a5b} : Set (Perm (Fin 5))) ≤ alternatingGroup (Fin 5) := by
    rw [closure_le]
    rintro x (rfl | rfl)
    · exact Perm.mem_alternatingGroup.2 hsa
    · exact Perm.mem_alternatingGroup.2 hsb
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hnd : (bfs5 12).Nodup := List.nodup_dedup _
  calc Nat.card (alternatingGroup (Fin 5)) = 60 := by
        rw [nat_card_alternatingGroup, Nat.card_fin]; rfl
    _ = (bfs5 12).length := hlen.symm
    _ ≤ _ := le_card_closure_of_list hnd (mem_closure_of_mem_bfs5 12)

theorem closure_subtype_eq_top {P : Type*} [Group P] {H : Subgroup P} {a b : H}
    (h : closure ({(a : P), (b : P)} : Set P) = H) : closure ({a, b} : Set H) = ⊤ := by
  apply Subgroup.map_injective H.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype, Set.image_pair]
  exact h

theorem coe_mulAut_pow_eq_one_iff {P : Type*} [Group P] {H : Subgroup P} (σ : MulAut H) (g : H)
    (n : ℕ) : ((σ g : H) : P) ^ n = 1 ↔ (g : P) ^ n = 1 := by
  rw [← Subgroup.coe_pow, ← Subgroup.coe_pow, ← map_pow, OneMemClass.coe_eq_one,
    OneMemClass.coe_eq_one, MulEquiv.map_eq_one_iff]

end CFSG.LargeExtraspecial.S12Tri
