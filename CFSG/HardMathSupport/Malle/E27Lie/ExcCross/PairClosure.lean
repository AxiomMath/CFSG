module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.HardMathSupport.Malle.E27Lie.ExcCross

theorem nine_dvd_card_closure_pair {G : Type*} [Group G] [Finite G] (x y : G) (hx : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hy : y ^ 3 = 1) (hc : x * y = y * x) (hn : y ∉ Subgroup.zpowers x) :
    9 ∣ Nat.card (Subgroup.closure ({x, y} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := Subgroup.closure ({x, y} : Set G) with hH
  have hcomm : ∀ g ∈ H, ∀ h ∈ H, g * h = h * g := by
    have hcentre : ∀ g ∈ ({x, y} : Set G), g ∈ Subgroup.centralizer ({x, y} : Set G) := by
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rcases hg with rfl | rfl <;> rcases hh with rfl | rfl <;>
        first | rfl | exact hc | exact hc.symm
    intro g hg h hh
    have h1 : H ≤ Subgroup.centralizer ({x, y} : Set G) := (Subgroup.closure_le _).2 hcentre
    have h2 := h1 hg
    rw [← Subgroup.centralizer_closure] at h2
    exact (Subgroup.mem_centralizer_iff.1 h2 h hh).symm
  have hcube : ∀ g ∈ H, g ^ 3 = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg => rcases hg with rfl | rfl <;> assumption
    | one => simp
    | mul g h hg hh ihg ihh =>
      rw [Commute.mul_pow (hcomm g hg h hh), ihg, ihh, one_mul]
    | inv g hg ihg => rw [inv_pow, ihg, inv_one]
  have hp : IsPGroup 3 H := fun g => ⟨1, Subtype.ext (by simpa using hcube g g.2)⟩
  obtain ⟨n, hn'⟩ := (IsPGroup.iff_card (p := 3)).1 hp
  have hxH : x ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
  have hyH : y ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hord : orderOf x = 3 := orderOf_eq_prime hx hx1
  have hle : Subgroup.zpowers x ≤ H := (Subgroup.zpowers_le).2 hxH
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hlt' : n ≤ 1 := by omega
    have hcard : Nat.card H ≤ 3 := by
      rw [hn']
      calc 3 ^ n ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hlt'
        _ = 3 := by norm_num
    have heq : Subgroup.zpowers x = H :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hord]; exact hcard)
    exact hn (heq ▸ hyH)
  rw [hn']
  exact (pow_dvd_pow 3 hn2 : 3 ^ 2 ∣ 3 ^ n)

end CFSG.HardMathSupport.Malle.E27Lie.ExcCross

end
