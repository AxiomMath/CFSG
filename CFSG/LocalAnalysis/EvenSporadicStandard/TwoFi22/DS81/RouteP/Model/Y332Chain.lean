module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Y332
public import CFSG.Perm.ChainLower

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open Equiv CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.LevelChain
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
open CFSG.Sporadic.LevelChain.Native (levelTrees levelLv)

theorem wordG_mem_of_forall {G : Type*} [Group G] (K : Subgroup G) (gens : ℤ → G) :
    ∀ w : List ℤ, (∀ l ∈ w, gens l ∈ K) → wordG gens w ∈ K
  | [], _ => K.one_mem
  | l :: w, h => by
    have ih := wordG_mem_of_forall K gens w fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    have e : wordG gens (l :: w) = gens l * wordG gens w := by simp [wordG]
    rw [e]
    exact K.mul_mem (h l List.mem_cons_self) ih

theorem letterPerm_mem_lvlGroup {G : Type*} [Group G] (π : ℕ → G) {starts : Array ℕ} {i m : ℕ}
    (hm : starts[i + 1]! ≤ m) {l : ℤ} (h1 : starts[i]! + 1 ≤ l.natAbs)
    (h2 : l.natAbs ≤ starts[i + 1]!) : letterPerm π m l ∈ lvlGroup starts π i := by
  unfold letterPerm
  by_cases hpos : 0 < l
  · have hc : 0 < l ∧ (l - 1).toNat < m := ⟨hpos, by omega⟩
    rw [if_pos hc]
    exact gs_mem_lvlGroup π (by omega) (by omega)
  · have hneg : l < 0 := by omega
    have hc : l < 0 ∧ (-l - 1).toNat < m := ⟨hneg, by omega⟩
    rw [if_neg (fun h => hpos h.1), if_pos hc]
    exact Subgroup.inv_mem _ (gs_mem_lvlGroup π (by omega) (by omega))

theorem y332Starts_le : ∀ i < 8, y332Starts[i + 1]! ≤ 71 := by decide

theorem y332Perm_mem_nest :
    ∀ i, 1 ≤ i → i < y332Base.size → ∀ j, y332Starts[i]! ≤ j → j < y332Starts[i + 1]! →
      y332Perm j ∈ lvlGroup y332Starts y332Perm (i - 1) := by
  intro i hi1 hi j hj1 hj2
  have hi8 : i < 8 := hi
  obtain ⟨hw, heq⟩ := y332NestOK_parts y332Facts.nest hi1 hi8 hj1 hj2
  have hj71 : j < 71 := by have := y332Starts_le i hi8; omega
  have hrep : ∀ l < (y332Gens y332Tabs).size, Rep 920808 (y332Gens y332Tabs)[l]! (y332Perm l) :=
    fun l hl => rep_y332Perm (by rwa [y332Gens_size] at hl)
  have hinv : ∀ l < (y332Gens y332Tabs).size,
      invOK 920808 (y332Gens y332Tabs)[l]! (invT 920808 (y332Gens y332Tabs)[l]!) = true :=
    fun l hl => invOK_y332Gens (by rwa [y332Gens_size] at hl)
  have hword := rep_wordT_letters (G := Perm Ω) (n := 920808) (by norm_num) hrep hinv
    (y332Word (y332Lines ())[j + 39]!)
  have hword' := rep_of_eqTab hword heq
  have hperm := rep_unique (rep_y332Perm hj71) hword'
  rw [hperm, y332Gens_size]
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  apply wordG_mem_of_forall
  intro l hl
  obtain ⟨hl1, hl2⟩ := hw l hl
  rw [Nat.add_sub_cancel] at hl1
  exact letterPerm_mem_lvlGroup y332Perm (y332Starts_le i' (by omega)) hl1 hl2

theorem y332Base_size : y332Base.size = 8 := rfl

theorem prod_y332Sizes : ∏ l ∈ Finset.Ico 0 y332Base.size, y332Sizes[l]! = 129123503308800 := by
  decide

theorem card_lvlGroup_y332_ge :
    129123503308800 ≤ Nat.card (lvlGroup y332Starts y332Perm 0) := by
  obtain ⟨hsz, hinv, htsz, htree, hfix, hsizes⟩ := y332TreesOK_parts y332Facts.trees
  have hlsz : (y332Letters (y332Gens y332Tabs)).size = 142 := y332Letters_size _
  have h := CFSG.Perm.card_lvlGroup_ge (G := Perm Ω) (n := 920808)
    (letters := y332Letters (y332Gens y332Tabs)) (gs := y332Perm) (starts := y332Starts)
    (base := y332Base)
    (trees := levelTrees degree (y332Letters (y332Gens y332Tabs)) y332Starts y332Base)
    (fun j hj => by
      rw [hlsz] at hj
      rw [y332Letters_even _ (by omega)]
      exact rep_y332Perm (by omega))
    (fun j hj => by
      rw [hlsz] at hj
      exact hinv j (by omega))
    (by rw [hsz]; rfl) rfl (by decide) (fun i hi => htree i (y332Base_size ▸ hi))
    (fun i hi1 hi => hfix i hi1 (y332Base_size ▸ hi)) y332Perm_mem_nest 0 (Nat.zero_le _)
  have hprod : ∏ l ∈ Finset.Ico 0 y332Base.size,
      (levelTrees degree (y332Letters (y332Gens y332Tabs)) y332Starts y332Base)[l]!.pts.size =
        129123503308800 := by
    rw [Finset.prod_congr rfl (g := fun l => y332Sizes[l]!)
      (fun l hl => hsizes l (by simpa [y332Base_size] using hl))]
    exact prod_y332Sizes
  rwa [hprod] at h

theorem card_closure_nine_ge :
    129123503308800 ≤ Nat.card (Subgroup.closure (y332Perm '' Set.Iio 9)) := by
  refine card_lvlGroup_y332_ge.trans (Subgroup.card_le_of_le ?_)
  refine lvlGroup_le y332Perm _ fun j hj1 hj2 => Subgroup.subset_closure ⟨j, ?_, rfl⟩
  have h9 : y332Starts[0 + 1]! = 9 := by decide
  rw [h9] at hj2
  exact hj2

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
