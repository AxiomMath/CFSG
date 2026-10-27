module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy2Gen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGenRank

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem fzc_sy3_pair_eq_of_odd_zpow {x y w : G} (hx4 : x ^ 4 = 1) {i j : ℤ}
    (hi : Odd i) (hw : w = x ^ i * y ^ j) : closure {x, y} = closure {w, y} := by
  have hx4z : x ^ (4 : ℤ) = 1 := by rw [zpow_ofNat, hx4]
  have hxi : x ^ i ∈ closure {w, y} := by
    have heq : x ^ i = w * (y ^ j)⁻¹ := by rw [hw]; group
    rw [heq]
    exact mul_mem (subset_closure (by simp)) (inv_mem (zpow_mem (subset_closure (by simp)) _))
  have hxmem : x ∈ closure {w, y} := by
    obtain ⟨m, hm⟩ : ∃ m : ℤ, i * i = 1 + 4 * m := by
      obtain ⟨n, rfl⟩ := hi
      exact ⟨n * n + n, by ring⟩
    have hxii : (x ^ i) ^ i = x := by
      rw [← zpow_mul, hm, zpow_add, zpow_one, zpow_mul, hx4z, one_zpow, mul_one]
    rw [← hxii]
    exact zpow_mem hxi i
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hxmem
    · exact subset_closure (by simp)
  · rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · rw [hw]
      exact mul_mem (zpow_mem (subset_closure (by simp)) i)
        (zpow_mem (subset_closure (by simp)) j)
    · exact subset_closure (by simp)

private theorem fzc_sy3_pair_closure_of_card_le_two {s : Finset G} (hs : s.card ≤ 2) :
    ∃ b₁ b₂ : G, closure (s : Set G) = closure {b₁, b₂} := by
  classical
  have hcases : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 := by omega
  rcases hcases with h | h | h
  · refine ⟨1, 1, ?_⟩
    rw [Finset.card_eq_zero.mp h]
    simp [Subgroup.closure_singleton_one]
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    exact ⟨a, a, by simp⟩
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h
    exact ⟨a, b, by simp⟩

theorem fzc_sy3_exchange2 {A : Subgroup G} (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hA4 : ∀ a ∈ A, a ^ 4 = 1) {b₁ b₂ : G} (hgen : closure {b₁, b₂} = A) {w : G}
    (hw : w ∈ A) (hwsq : ∀ a ∈ A, a ^ 2 ≠ w) : ∃ u : G, closure {w, u} = A := by
  have hb1 : b₁ ∈ A := by rw [← hgen]; exact subset_closure (by simp)
  have hb2 : b₂ ∈ A := by rw [← hgen]; exact subset_closure (by simp)
  have h12 : b₁ * b₂ = b₂ * b₁ := hAc b₁ hb1 b₂ hb2
  have hset : ({b₁, b₂, b₂} : Set G) = {b₁, b₂} := by
    ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  obtain ⟨i, j, k, hwik⟩ := CFSG.RankThree.PartTwo.Sec11.exists_zpow_triple_of_mem_closure
    h12 h12 (hAc b₂ hb2 b₂ hb2) (z := w) (by rw [hset, hgen]; exact hw)
  have hw_eq : w = b₁ ^ i * b₂ ^ (j + k) := by rw [hwik, mul_assoc, ← zpow_add]
  have hnotboth : ¬ (Even i ∧ Even (j + k)) := by
    rintro ⟨hi, hm⟩
    obtain ⟨i', hi'⟩ := (even_iff_exists_two_mul).mp hi
    obtain ⟨m', hm'⟩ := (even_iff_exists_two_mul).mp hm
    have hcomm : Commute (b₁ ^ i') (b₂ ^ m') :=
      (show Commute b₁ b₂ from h12).zpow_zpow i' m'
    have e1 : (b₁ ^ i') ^ (2 : ℤ) = b₁ ^ i := by
      rw [← zpow_mul, show i' * 2 = i by omega]
    have e2 : (b₂ ^ m') ^ (2 : ℤ) = b₂ ^ (j + k) := by
      rw [← zpow_mul, show m' * 2 = j + k by omega]
    have hsquare : (b₁ ^ i' * b₂ ^ m') ^ 2 = w := by
      rw [show (b₁ ^ i' * b₂ ^ m') ^ 2
            = (b₁ ^ i' * b₂ ^ m') ^ (2 : ℤ) from (zpow_ofNat _ 2).symm,
        hcomm.mul_zpow 2, e1, e2, ← hw_eq]
    exact hwsq _ (mul_mem (zpow_mem hb1 i') (zpow_mem hb2 m')) hsquare
  have hodd : Odd i ∨ Odd (j + k) := by
    by_contra h
    rw [not_or] at h
    exact hnotboth ⟨Int.not_odd_iff_even.mp h.1, Int.not_odd_iff_even.mp h.2⟩
  rcases hodd with hi | hm
  · have h1 : closure {b₁, b₂} = closure {w, b₂} :=
      fzc_sy3_pair_eq_of_odd_zpow (hA4 b₁ hb1) hi hw_eq
    exact ⟨b₂, by rw [← h1, hgen]⟩
  · have hw_eq' : w = b₂ ^ (j + k) * b₁ ^ i := by
      rw [hw_eq, ((show Commute b₁ b₂ from h12).zpow_zpow i (j + k)).eq]
    have h1 : closure {b₂, b₁} = closure {w, b₁} :=
      fzc_sy3_pair_eq_of_odd_zpow (hA4 b₂ hb2) hm hw_eq'
    refine ⟨b₁, ?_⟩
    rw [← h1]
    rw [show ({b₂, b₁} : Set G) = {b₁, b₂} from by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto, hgen]

theorem fzc_sy3_cyc {N E X : Subgroup G} (hNc : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (hN4 : ∀ a ∈ N, a ^ 4 = 1) (hNr : S4A.RankLE N 3) (hsq : ∀ a ∈ N, a ^ 2 ∈ E)
    {x : G} (hx : x ∈ X) {n : ℕ} (hxn : x ^ n ∈ N) (hxnE : x ^ n ∉ E)
    (hcov : ∀ g ∈ X, ∃ k : ℕ, g * (x ^ k)⁻¹ ∈ N) :
    ∃ s : Finset G, s.card ≤ 3 ∧ closure (s : Set G) = X := by
  classical
  let N₀ : Subgroup G := X ⊓ N
  have hN₀le : N₀ ≤ N := inf_le_right
  have hN₀c : ∀ a ∈ N₀, ∀ b ∈ N₀, a * b = b * a :=
    fun a ha b hb => hNc a (hN₀le ha) b (hN₀le hb)
  have hN₀4 : ∀ a ∈ N₀, a ^ 4 = 1 := fun a ha => hN4 a (hN₀le ha)
  obtain ⟨s₀, hs₀card, hs₀c⟩ := hNr N₀ inf_le_right
  obtain ⟨b₁, b₂, b₃, hbgen⟩ := fzc_sy2_three_gen hs₀card
  have hwN₀ : x ^ n ∈ N₀ := ⟨pow_mem hx n, hxn⟩
  have hwsq : ∀ a ∈ N₀, a ^ 2 ≠ x ^ n := by
    intro a ha h
    exact hxnE (h ▸ hsq a (hN₀le ha))
  obtain ⟨u, v, huv⟩ := fzc_sy2_exchange hN₀c hN₀4 (b₁ := b₁) (b₂ := b₂) (b₃ := b₃)
    (by rw [← hbgen, hs₀c]) (c := x ^ n) hwN₀ hwsq
  have hu : u ∈ N₀ := by rw [← huv]; exact subset_closure (by simp)
  have hv : v ∈ N₀ := by rw [← huv]; exact subset_closure (by simp)
  refine ⟨{x, u, v}, Finset.card_le_three, ?_⟩
  rw [show (↑({x, u, v} : Finset G) : Set G) = ({x, u, v} : Set G) from by simp]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact hx
    · exact (inf_le_left : N₀ ≤ X) hu
    · exact (inf_le_left : N₀ ≤ X) hv
  · intro g hg
    obtain ⟨k, hk⟩ := hcov g hg
    have hkN₀ : g * (x ^ k)⁻¹ ∈ N₀ :=
      ⟨mul_mem hg (Subgroup.inv_mem (H := X) (pow_mem hx k)), hk⟩
    have hsub : closure ({x ^ n, u, v} : Set G) ≤ closure ({x, u, v} : Set G) := by
      rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact pow_mem (subset_closure (by simp)) n
      · exact subset_closure (by simp)
      · exact subset_closure (by simp)
    have hg1 : g * (x ^ k)⁻¹ ∈ closure ({x, u, v} : Set G) :=
      hsub (huv.symm ▸ hkN₀)
    have hg2 : x ^ k ∈ closure ({x, u, v} : Set G) :=
      pow_mem (subset_closure (by simp)) k
    have he : g = (g * (x ^ k)⁻¹) * x ^ k := by group
    rw [he]
    exact mul_mem hg1 hg2

theorem fzc_sy3_klein {N E X : Subgroup G} (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE4 : ∀ a ∈ E, a ^ 4 = 1) (hEr : S4A.RankLE E 2) (hEN : E ≤ N)
    (hNE : ∀ a ∈ N, ∀ b ∈ N, a ∉ E → b ∉ E → a * b⁻¹ ∈ E)
    {x y : G} (hx : x ∈ X) (hy : y ∈ X) (hx2 : x ^ 2 ∈ N) (hx2E : x ^ 2 ∉ E)
    (hy2 : y ^ 2 ∈ N) (hy2E : y ^ 2 ∉ E)
    (hcov : ∀ g ∈ X, g ∈ N ∨ g * x⁻¹ ∈ N ∨ g * y⁻¹ ∈ N ∨ g * (x * y)⁻¹ ∈ N)
    (hw : ∀ e ∈ X ⊓ E, e ^ 2 ≠ x ^ 2 * (y ^ 2)⁻¹) :
    ∃ u : G, closure {x, y, u} = X := by
  classical
  let X₁ : Subgroup G := X ⊓ E
  have hX₁leE : X₁ ≤ E := inf_le_right
  have hX₁c : ∀ a ∈ X₁, ∀ b ∈ X₁, a * b = b * a :=
    fun a ha b hb => hEc a (hX₁leE ha) b (hX₁leE hb)
  have hX₁4 : ∀ a ∈ X₁, a ^ 4 = 1 := fun a ha => hE4 a (hX₁leE ha)
  obtain ⟨s₁, hs₁card, hs₁c⟩ := hEr X₁ inf_le_right
  obtain ⟨b₁, b₂, hbgen⟩ := fzc_sy3_pair_closure_of_card_le_two hs₁card
  have hw₀ : x ^ 2 * (y ^ 2)⁻¹ ∈ X₁ :=
    ⟨mul_mem (pow_mem hx 2) (Subgroup.inv_mem (H := X) (pow_mem hy 2)),
      hNE (x ^ 2) hx2 (y ^ 2) hy2 hx2E hy2E⟩
  have hw₀sq : ∀ a ∈ X₁, a ^ 2 ≠ x ^ 2 * (y ^ 2)⁻¹ := fun a ha => hw a ha
  obtain ⟨u, hu⟩ := fzc_sy3_exchange2 hX₁c hX₁4 (by rw [← hbgen, hs₁c]) hw₀ hw₀sq
  have huX₁ : u ∈ X₁ := hu ▸ subset_closure (by simp)
  have huX : u ∈ X := (inf_le_left : X₁ ≤ X) huX₁
  refine ⟨u, ?_⟩
  let H : Subgroup G := closure ({x, y, u} : Set G)
  have hxH : x ∈ H := subset_closure (by simp)
  have hyH : y ∈ H := subset_closure (by simp)
  have huH : u ∈ H := subset_closure (by simp)
  have hw₀H : x ^ 2 * (y ^ 2)⁻¹ ∈ H :=
    mul_mem (pow_mem hxH 2) (Subgroup.inv_mem (H := H) (pow_mem hyH 2))
  have hX₁H : X₁ ≤ H := by
    rw [← hu]
    exact (Subgroup.closure_le H).mpr (by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hw₀H
      · exact huH)
  have hNX : ∀ n ∈ X ⊓ N, n ∈ H := by
    intro n hn
    by_cases hnE : n ∈ E
    · exact hX₁H ⟨hn.1, hnE⟩
    · have hnE' : n * (x ^ 2)⁻¹ ∈ E := hNE n hn.2 (x ^ 2) hx2 hnE hx2E
      have hnX : n * (x ^ 2)⁻¹ ∈ X := mul_mem hn.1 (Subgroup.inv_mem (H := X) (pow_mem hx 2))
      have h1 : n * (x ^ 2)⁻¹ ∈ H := hX₁H ⟨hnX, hnE'⟩
      have h2 : x ^ 2 ∈ H := pow_mem hxH 2
      have he : n = (n * (x ^ 2)⁻¹) * x ^ 2 := by group
      rw [he]
      exact mul_mem h1 h2
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact huX
  · intro g hg
    rcases hcov g hg with hgN | hgx | hgy | hgxy
    · exact hNX g ⟨hg, hgN⟩
    · have h1 : g * x⁻¹ ∈ H := hNX _ ⟨mul_mem hg (Subgroup.inv_mem (H := X) hx), hgx⟩
      have he : g = (g * x⁻¹) * x := by group
      rw [he]
      exact mul_mem h1 hxH
    · have h1 : g * y⁻¹ ∈ H := hNX _ ⟨mul_mem hg (Subgroup.inv_mem (H := X) hy), hgy⟩
      have he : g = (g * y⁻¹) * y := by group
      rw [he]
      exact mul_mem h1 hyH
    · have h1 : g * (x * y)⁻¹ ∈ H :=
        hNX _ ⟨mul_mem hg (Subgroup.inv_mem (H := X) (mul_mem hx hy)), hgxy⟩
      have he : g = (g * (x * y)⁻¹) * (x * y) := by group
      rw [he]
      exact mul_mem h1 (mul_mem hxH hyH)

end CFSG.OddStandard.SmallF3.FritzII
