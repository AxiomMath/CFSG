module

public import CFSG.CGT.PushingUpLit.CGT6.EmbAltOT

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv

variable {V : Type} [CommGroup V] {m : ℕ}

theorem cb_commV_zpowers_conj (x g : MulAut V) :
    commV (Subgroup.zpowers (g * x * g⁻¹)) = (commV (Subgroup.zpowers x)).map g.toMonoidHom :=
  CFSG.Quasithin.commV_zpowers_conj_eq x g

theorem cb_mem_zpowers_sq {x : MulAut V} (hx : x ^ 2 = 1) {z : MulAut V}
    (hz : z ∈ Subgroup.zpowers x) : z = 1 ∨ z = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
  have h2 : (orderOf x : ℤ) ∣ 2 := by exact_mod_cast hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
  · left
    have : x = 1 := orderOf_eq_one_iff.mp h1
    rw [this, one_zpow]
  · have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rw [← zpow_mod_orderOf, h1]
    rcases hk with hk | hk
    · left; rw [show ((2 : ℕ) : ℤ) = 2 from rfl, hk, zpow_zero]
    · right; rw [show ((2 : ℕ) : ℤ) = 2 from rfl, hk, zpow_one]

theorem cb_commV_zpowers_le_fixV_self (hV : ∀ v : V, v ^ 2 = 1) {x : MulAut V}
    (hx : x ^ 2 = 1) : commV (Subgroup.zpowers x) ≤ fixV (Subgroup.zpowers x) :=
  CFSG.CGT.PushingUpLit.CGT6.commV_zpowers_le_fixV_self hV hx

theorem cb_commV_zpowers_le_fixV (hV : ∀ v : V, v ^ 2 = 1) (hm : 7 ≤ m) (hodd : Odd m)
    {Y : Subgroup (MulAut V)} (θ : Y ≃* alternatingGroup (Fin m))
    (hnat : IsNatSectionWith (altAct m) θ (commV Y) ⊥) {t : MulAut V} (ht : t ^ 2 = 1)
    (hc : ∀ y ∈ Y, t * y = y * t) : commV (Subgroup.zpowers t) ≤ fixV Y :=
  CFSG.CGT.PushingUpLit.CGT6.commV_zpowers_le_fixV hV hm hodd θ hnat ht hc

theorem cb_commV_invariant_of_normalizing {Y : Subgroup (MulAut V)} {c : MulAut V}
    (hnorm : ∀ y ∈ Y, c * y * c⁻¹ ∈ Y) {w : V} (hw : w ∈ commV Y) : c w ∈ commV Y :=
  CFSG.Quasithin.commV_apply_mem_of_normalizes hnorm hw

end CFSG.CGT.PushingUpLit.CGT6
