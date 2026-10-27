module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.CBridgeB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.A5Transfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Gz9.Shape240

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem oddInv_barOf_not_mem_commutator {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hOrb : GzOrbitFacts a z) (hNo : GzNoFacts a z) {c : G}
    (hcz : c ∈ Gx z) (hcQ : c ∉ Qz z) (hc : IsConj a c) :
    barOf z ⟨c, hcz⟩ ∉ _root_.commutator (Gbar z) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_Gbar (z := z) h
  let t : ↥(Gx z) := ⟨c, hcz⟩
  let Q : Subgroup ↥(Gx z) := CFSG.pCore 2 ↥(Gx z)
  set u : Gbar z := barOf z t with hu
  have hc2 : c ^ 2 = 1 := by
    obtain ⟨d, hd⟩ := isConj_iff.mp hc
    rw [← hd, conj_pow, ← h.orderOf_a, pow_orderOf_eq_one]
    simp
  have ht2 : (t : G) ^ 2 = 1 := hc2
  have ht2' : t ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ht2, Subgroup.coe_one]
  have hu2 : u ^ 2 = 1 := by
    rw [hu]
    change (t : Gbar z) ^ 2 = 1
    rw [← QuotientGroup.mk_pow (N := Q) t 2, ht2', QuotientGroup.mk_one]
  have hu1 : u ≠ 1 := by
    rw [hu]
    intro h1
    exact hcQ ((barOf_eq_one_iff (z := z) t).mp h1)
  have hK : Nat.card ↥(Subgroup.centralizer ({t} : Set ↥(Gx z))) = 2 ^ 8 * 15 :=
    (card_Gx_inf_eq (z := z) hcz).symm.trans (hOrb.orbit_outA.2 c ⟨hcz, hcQ, hc⟩)
  let f : ↥(Subgroup.centralizer ({t} : Set ↥(Gx z))) →* Gbar z :=
    (QuotientGroup.mk' Q).comp (Subgroup.centralizer ({t} : Set ↥(Gx z))).subtype
  have hle : f.range ≤ Subgroup.centralizer ({u} : Set (Gbar z)) := by
    rintro _ ⟨k, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hu]
    change (QuotientGroup.mk' Q) (k : ↥(Gx z)) * (QuotientGroup.mk' Q) t =
      (QuotientGroup.mk' Q) t * (QuotientGroup.mk' Q) (k : ↥(Gx z))
    have hk := Subgroup.mem_centralizer_singleton_iff.mp k.2
    rw [← map_mul, ← map_mul, hk]
  have hker_eq : f.ker = Q.comap (Subgroup.centralizer ({t} : Set ↥(Gx z))).subtype := by
    rw [← QuotientGroup.ker_mk' Q, MonoidHom.comap_ker]
  have hkerP : IsPGroup 2 ↥f.ker := by
    rw [hker_eq]
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥(Gx z))).comap_of_injective
      (Subgroup.centralizer ({t} : Set ↥(Gx z))).subtype
      (Subgroup.centralizer ({t} : Set ↥(Gx z))).subtype_injective
  have h15 : 15 ∣ Nat.card ↥(Subgroup.centralizer ({u} : Set (Gbar z))) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hkerP
    have h1 : 15 ∣ 2 ^ n * Nat.card ↥f.range := by
      rw [← hn, Subgroup.card_ker_mul_card_range f, hK]
      exact dvd_mul_left 15 (2 ^ 8)
    have hcop : Nat.Coprime (2 ^ n) 15 := by
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        norm_num
      · exact (Nat.coprime_pow_left_iff hnpos 2 15).mpr (by norm_num)
    exact dvd_trans (hcop.symm.dvd_of_dvd_mul_left h1) (Subgroup.card_dvd_of_le hle)
  rcases involution_cases_of_mulEquiv e hu2 hu1 with ⟨huout, _⟩ | ⟨huin, h240⟩ | ⟨_, h32⟩
  · exact huout
  ·
    exfalso
    refine hNo.no_twoTwoA5 ⟨t, ht2, ?_⟩
    change IsShapeTwoTwoTimesA5 ↥(Subgroup.centralizer ({barOf z t} : Set (Gbar z)))
    rw [← hu]
    exact gz9_isShapeTwoTwoTimesA5_of_mulEquiv e huin hu2 h240
  ·
    exfalso
    rw [h32] at h15
    norm_num at h15

end CFSG.EvenSporadicStandard.HNRecog.Section3
