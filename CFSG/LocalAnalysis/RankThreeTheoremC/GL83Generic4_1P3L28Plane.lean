module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Pt
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3P34Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l28plane_inf_center {P : Sylow 3 G} {M : Subgroup G} {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} {U : Subgroup G}
    (hR : L28Prop34 3 P J x) (hV : L28InV 3 P x U) :
    U ⊓ L28Z (P : Subgroup G) = zpowers x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hxP, ⟨-, hx1, hx3, -, -⟩, -, -⟩ := hgen
  obtain ⟨hPC, hZc, -, -, -⟩ := hR
  obtain ⟨hUQ, hUel, hUc, hxU, hUZ⟩ := hV
  have hxZ : x ∈ L28Z (P : Subgroup G) :=
    ⟨⟨x, hxP⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext
      (mem_centralizer_singleton_iff.mp (hPC g.2)), rfl⟩
  have hzx : zpowers x ≤ U ⊓ L28Z (P : Subgroup G) :=
    le_inf (zpowers_le.mpr hxU) (zpowers_le.mpr hxZ)
  have hcardx : Nat.card (zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  have hne : U ⊓ L28Z (P : Subgroup G) ≠ U := fun h => hUZ (by
    have hle : U ≤ L28Z (P : Subgroup G) := by
      have h1 := inf_le_right (a := U) (b := L28Z (P : Subgroup G))
      rwa [h] at h1
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hUc, hZc]))
  have hdvd : Nat.card ↥(U ⊓ L28Z (P : Subgroup G)) ∣ 3 ^ 2 := by
    rw [← hUc]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have h3le : 3 ≤ Nat.card ↥(U ⊓ L28Z (P : Subgroup G)) := by
    have h1 := Subgroup.card_le_of_le hzx
    rwa [hcardx] at h1
  interval_cases i
  · rw [pow_zero] at hci
    omega
  · rw [pow_one] at hci
    exact (Subgroup.eq_of_le_of_card_ge hzx (by rw [hci, hcardx])).symm
  · exact absurd (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hci, hUc])) hne

theorem l28plane_wc {P : Sylow 3 G} {M : Subgroup G} {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} {U : Subgroup G}
    (hR : L28Prop34 3 P J x) (hV : L28InV 3 P x U) : LineWeaklyClosed x U := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hUx := l28plane_inf_center hgen hR hV
  obtain ⟨-, ⟨-, hx1, hx3, -, -⟩, -, -⟩ := hgen
  obtain ⟨-, -, hZ, hfus, -⟩ := hR
  obtain ⟨hUQ, -, -, -, -⟩ := hV
  intro g hg
  have hcard : Nat.card ↥((zpowers x).map (MulAut.conj g).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, Nat.card_zpowers,
      orderOf_eq_prime hx3 hx1]
  rcases hfus g (hg.trans (hUQ.trans inf_le_left)) with h | h
  · exact h
  · have hle' : (zpowers x).map (MulAut.conj g).toMonoidHom ≤ U ⊓ L28Z (P : Subgroup G) := by
      refine le_inf hg fun y hy => ?_
      obtain ⟨z, hz, rfl⟩ := hy
      have hy1 := hg ⟨z, hz, rfl⟩
      have hy2 : (MulAut.conj g).toMonoidHom z ∈ (P : Subgroup G) ⊓ J :=
        ⟨hUQ.trans inf_le_left hy1, h ⟨z, hz, rfl⟩⟩
      refine hZ _ hy2 ?_
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
      rw [← map_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow,
        map_one]
    rw [hUx] at hle'
    exact Subgroup.eq_of_le_of_card_ge hle' (by rw [hcard, Nat.card_zpowers,
      orderOf_eq_prime hx3 hx1])

theorem l28plane_outer {P : Sylow 3 G} {M : Subgroup G} {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} {U : Subgroup G}
    (hR : L28Prop34 3 P J x) (hV : L28InV 3 P x U) {w : G} (hwU : w ∈ U)
    (hwx : w ∉ zpowers x) : L28OuterOn J w := by
  have hUx := l28plane_inf_center hgen hR hV
  obtain ⟨-, -, -, -, hout⟩ := hR
  obtain ⟨hUQ, hUel, -, -, -⟩ := hV
  refine hout w (hUQ.trans inf_le_left hwU) (hUel.2 w hwU) fun hwZ => hwx ?_
  rw [← hUx]
  exact ⟨hwU, hwZ⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
