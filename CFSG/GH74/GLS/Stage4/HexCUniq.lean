module

public import CFSG.GH74.GLS.Stage4.HexCSub

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G}

theorem rgd2_unique_15 (R : RGD2 6 H r₁ r₂ U root) {x y : G} (hx : x ∈ root 1) (hy : y ∈ root 5)
    (h : x * y ∈ Vsub root 2 4) : x = 1 ∧ y = 1 := by
  have hc : x * y ∈ chainProd root (intList 2 4) := by
    have : x * y ∈ ((Vsub root 2 4 : Subgroup G) : Set G) := h
    rwa [Vsub_carrier R (by norm_num) (by norm_num)] at this
  obtain ⟨f₂, hf₂, he₂⟩ := exists_fun_of_mem_chainProd root _ (nodup_intList _ _) _ hc
  have hl : intList 1 ((6 : ℕ) : ℤ) = [1, 2, 3, 4, 5, 6] := by decide
  have key := R.unique (fun k => if k = 1 then x else if k = 5 then y else 1)
    (fun k => if 2 ≤ k ∧ k ≤ 4 then f₂ k else 1)
    (fun k hk => by
      rw [hl] at hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hx, hy, (root _).one_mem])
    (fun k hk => by
      split_ifs with hk'
      · exact hf₂ k (mem_intList_iff.2 hk')
      · exact (root k).one_mem)
    (by
      rw [prod_pad (n := 6) (by norm_num) (by norm_num) (by norm_num) f₂, ← he₂, hl]
      simp)
  have h1 := key 1 (by rw [hl]; simp)
  have h5 := key 5 (by rw [hl]; simp)
  simp at h1 h5
  exact ⟨h1, h5⟩

end CFSG.GH74.GLS.Stage4.Hex
