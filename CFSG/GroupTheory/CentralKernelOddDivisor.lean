module

public import CFSG.RankThree.PartTwo.Sec13.KF135FamOddPair

public section

namespace CFSG.GroupTheory

theorem dvd_card_map_of_ker_le_center {X Y : Type*} [Group X] [Group Y] {R : Subgroup X}
    [Finite R] {ψ : X →* Y} (hψ : ψ.ker ≤ Subgroup.center X)
    (hR : ∀ c ∈ R, (∀ y ∈ R, c * y = y * c) → c * c = 1) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (h : r ∣ Nat.card R) : r ∣ Nat.card (R.map ψ) := by
  let f : R →* Y := ψ.domRestrict R
  have hsq : ∀ x ∈ f.ker, x ^ 2 = 1 := by
    intro x hx
    have hxX : (x : X) ∈ ψ.ker := hx
    have hcent : ∀ y ∈ R, (x : X) * y = y * (x : X) := fun y _ =>
      (Subgroup.mem_center_iff.1 (hψ hxX) y).symm
    apply Subtype.ext
    rw [Subgroup.coe_pow, pow_two, hR x x.2 hcent, Subgroup.coe_one]
  have hres := CFSG.RankThree.PartTwo.Sec13.KF135Proof.FamOdd.dvd_card_range_of_ker
    f hr hr2 h hsq
  rwa [MonoidHom.domRestrict_range] at hres

end CFSG.GroupTheory
