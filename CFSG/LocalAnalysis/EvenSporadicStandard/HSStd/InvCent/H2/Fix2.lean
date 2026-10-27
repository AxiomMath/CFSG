module

public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Basic

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG.EvenSporadicStandard.SolomonRed

variable {G : Type*} [Group G]

theorem exists_commute_of_normal_two_group [Finite G] {t : G} (ht : t * t = 1) {Z : Subgroup G}
    (hZn : Z.Normal) (hZ2 : IsPGroup 2 ↥Z) (hZ1 : Z ≠ ⊥) :
    ∃ z ∈ Z, z ≠ 1 ∧ z * t = t * z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases ht1 : t = 1
  · obtain ⟨z, hz⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := Z)).1 hZ1
    exact ⟨z, z.2, fun h => hz (Subtype.ext h), by rw [ht1]; simp⟩
  · by_cases htZ : t ∈ Z
    · exact ⟨t, htZ, ht1, rfl⟩
    · by_contra hcon
      have hfp : ∀ w ∈ Z, t * w = w * t → w = 1 := by
        intro w hw hwt
        by_contra hw1
        exact hcon ⟨w, hw, hw1, hwt.symm⟩
      have hσ : ∀ x, (MulAut.conj t) ((MulAut.conj t) x) = x := by
        intro x
        simpa [MulAut.conj_apply] using conj_conj_of_mul_self_eq_one ht x
      have hZσ : ∀ w ∈ Z, (MulAut.conj t) w ∈ Z := fun w hw => by
        simpa [MulAut.conj_apply] using hZn.conj_mem w hw t
      have hfpσ : ∀ w ∈ Z, (MulAut.conj t) w = w → w = 1 := fun w hw hw' =>
        hfp w hw (conj_eq_self_iff.1 (by simpa [MulAut.conj_apply] using hw'))
      have hinv := fixedPointFree_inverts (MulAut.conj t) hσ hZσ hfpσ
      have h2 : 2 ∣ Nat.card Z := by
        obtain ⟨n, hn⟩ := hZ2.exists_card_eq
        rcases n with _ | n
        · exfalso
          have : Nat.card Z = 1 := by simpa using hn
          exact hZ1 (Subgroup.card_eq_one.mp this)
        · rw [hn, pow_succ]
          exact dvd_mul_left _ _
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
      have hx2 : (x : G) * (x : G) = 1 := by
        have : x * x = 1 := by
          have := pow_orderOf_eq_one x
          rw [hx, pow_two] at this
          exact this
        exact congrArg Subtype.val this
      have hx1 : (x : G) ≠ 1 := by
        intro h1
        have : x = 1 := Subtype.ext h1
        rw [this, orderOf_one] at hx
        omega
      have hxi : (MulAut.conj t) (x : G) = (x : G)⁻¹ := hinv x x.2
      have hxinv : (x : G)⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
      rw [hxinv] at hxi
      exact hx1 (hfp x x.2 (conj_eq_self_iff.1 (by simpa [MulAut.conj_apply] using hxi)))

theorem inf_centralizer_ne_bot [Finite G] {W : Subgroup G} (hW2 : IsPGroup 2 ↥W) (hW1 : W ≠ ⊥) :
    W ⊓ centralizer (W : Set G) ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial ↥W := (Subgroup.nontrivial_iff_ne_bot W).2 hW1
  haveI : Nontrivial (Subgroup.center ↥W) := hW2.center_nontrivial
  obtain ⟨c, hc1⟩ := exists_ne (1 : Subgroup.center ↥W)
  have hx1 : ((c : ↥W) : G) ≠ 1 := by
    intro h1
    exact hc1 (Subtype.ext (Subtype.ext h1))
  refine (Subgroup.ne_bot_iff_exists_ne_one (H := W ⊓ centralizer (W : Set G))).2
    ⟨⟨((c : ↥W) : G), (c : ↥W).2, ?_⟩, ?_⟩
  · change ((c : ↥W) : G) ∈ centralizer (W : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 c.2 (⟨w, hw⟩ : ↥W))
  · intro h1
    exact hx1 (congrArg Subtype.val h1)

theorem exists_fixed_of_simple_nonab [Finite G] {L : Subgroup G} (hL : IsSimpleGroup ↥L)
    (hnab : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a) {z : G} (hz : z * z = 1)
    (hzL : ∀ x ∈ L, z * x * z⁻¹ ∈ L) : ∃ x ∈ L, x ≠ 1 ∧ x * z = z * x := by
  by_contra hcon
  have hfix : ∀ w ∈ L, z * w = w * z → w = 1 := by
    intro w hw hzw
    by_contra hw1
    exact hcon ⟨w, hw, hw1, hzw.symm⟩
  have hcomm := fixedPointFree_commute_of_mul_self_eq_one hz hzL hfix
  obtain ⟨a, ha, b, hb, hab⟩ := hnab
  exact hab (hcomm a ha b hb)

end CFSG.EvenSporadicStandard.HSStd.InvCent
