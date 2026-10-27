module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.CBridgeB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.A5Transfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Gz9.Shape240

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem gz9_not_mem_commutator {G : Type} [Group G] [Finite G] {a z : G} (h : IsF5Type a z)
    (hOrb : GzOrbitFacts a z) (hNo : GzNoFacts a z) {a₁ : G} (ha₁z : a₁ ∈ Gx z)
    (ha₁Q : a₁ ∉ Qz z) (ha₁ : IsConj a a₁) :
    (⟨a₁, ha₁z⟩ : ↥(Gx z)) ∉ commutator ↥(Gx z) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_Gbar (z := z) h
  let t : ↥(Gx z) := ⟨a₁, ha₁z⟩
  let Q : Subgroup ↥(Gx z) := CFSG.pCore 2 ↥(Gx z)
  set u : Gbar z := barOf z t with hu
  have ha₁2 : a₁ ^ 2 = 1 := by
    obtain ⟨c, hc⟩ := isConj_iff.mp ha₁
    rw [← hc, conj_pow, ← h.orderOf_a, pow_orderOf_eq_one]
    simp
  have ht2 : (t : G) ^ 2 = 1 := ha₁2
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
    exact ha₁Q ((barOf_eq_one_iff (z := z) t).mp h1)
  have hK : Nat.card ↥(Subgroup.centralizer ({t} : Set ↥(Gx z))) = 2 ^ 8 * 15 :=
    (card_Gx_inf_eq (z := z) ha₁z).symm.trans
      (hOrb.orbit_outA.2 a₁ ⟨ha₁z, ha₁Q, ha₁⟩)
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
  rcases involution_cases_of_mulEquiv e hu2 hu1 with ⟨huout, _⟩ | ⟨huin, h240⟩ | ⟨huin, h32⟩
  ·
    intro ht
    apply huout
    have hmap : (commutator ↥(Gx z)).map (QuotientGroup.mk' Q) = commutator (Gbar z) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Q)]
    rw [← hmap, hu]
    exact Subgroup.mem_map_of_mem (QuotientGroup.mk' Q) ht
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