module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OStep1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OStep2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec5b_twoCoreIn_le_self (X : Subgroup G) : twoCoreIn X ≤ X := by
  unfold twoCoreIn CFSG.inSubgroup
  exact Subgroup.map_subtype_le _

private theorem sec5b_oddCore_le_normalizer_conj [Finite G] (h36 : Asc82Lemma36) {t : G}
    {L S : Subgroup G} {z : G} (hs : Sec5Ctx G t L S z) {g : G}
    (hg : g⁻¹ * t * g = t * z)
    (hcent : L ≤ centralizer (oddCoreIn (centralizer ({t} : Set G)) : Set G)) :
    oddCoreIn (centralizer ({t} : Set G)) ≤ normalizer (CFSG.conjugate L g : Set G) := by
  intro u hu
  have huC : u * t = t * u := by
    have h := (oddCoreIn_normal (centralizer ({t} : Set G))).1 hu
    rwa [Subgroup.mem_centralizer_singleton_iff] at h
  have hzu : u * z = z * u := hcent hs.pocket.mem u hu
  have htz : u * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u := by
    rw [hg]
    calc u * (t * z) = (u * t) * z := by group
      _ = (t * u) * z := by rw [huC]
      _ = t * (u * z) := by group
      _ = t * (z * u) := by rw [hzu]
      _ = (t * z) * u := by group
  exact sec4_mem_normalizer h36 (hs.toSec5Setting.toSec3SettingLB.conjugate g) u
    (Subgroup.mem_centralizer_singleton_iff.mpr htz)

theorem sec5_oddCore_comm_conj (h34a : Asc82Lemma34a) (h36 : Asc82Lemma36)
    (h52a : Asc82Lemma52a) (h52b : Asc82Lemma52b) (hP : Asc82FactPockets6)
    (hQ : Asc82FactQCent6) {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G}
    (hs : Sec5Ctx G t L S z) (g : G) (hg : g⁻¹ * t * g = t * z) :
    ⁅CFSG.conjugate L g, oddCoreIn (centralizer ({t} : Set G))⁆ = ⊥ := by
  have hcomm : L ≤ centralizer (oddCoreIn (centralizer ({t} : Set G)) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (sec5_oddCore_comm_L h36 hs.toSec5Setting).1
  have hΩ : IsOm6Z2 L := hs.toSec5Setting.isOm6Z2
  obtain ⟨K₁, K₂, hK₁, hK₂, -, ⟨e₁⟩, ⟨e₂⟩, hcom, hcard, hcent, -⟩ :=
    hP G L z hΩ hs.pocket
  have hQ₁ : twoCoreIn K₁ ≤ CFSG.conjugate L g :=
    sec5o_twoCoreIn_le_conj h34a h36 h52a hs hg hK₁ ⟨e₁⟩
  have hQ₂ : twoCoreIn K₂ ≤ CFSG.conjugate L g :=
    sec5o_twoCoreIn_le_conj h34a h36 h52a hs hg hK₂ ⟨e₂⟩
  have hQ₁L : twoCoreIn K₁ ≤ L :=
    (sec5b_twoCoreIn_le_self K₁).trans (hK₁.2.1.trans inf_le_left)
  have hQ₂L : twoCoreIn K₂ ≤ L :=
    (sec5b_twoCoreIn_le_self K₂).trans (hK₂.2.1.trans inf_le_left)
  have hQleL : twoCoreIn K₁ ⊔ twoCoreIn K₂ ≤ L := sup_le hQ₁L hQ₂L
  have hQle : twoCoreIn K₁ ⊔ twoCoreIn K₂ ≤ CFSG.conjugate L g := sup_le hQ₁ hQ₂
  have hinf : (twoCoreIn K₁ ⊔ twoCoreIn K₂) ⊓ centerIn (CFSG.conjugate L g) = ⊥ :=
    sec5o_inf_centerIn_conj h52b hs hg hQle hcent
  have hUnorm : oddCoreIn (centralizer ({t} : Set G)) ≤
      normalizer (CFSG.conjugate L g : Set G) :=
    sec5b_oddCore_le_normalizer_conj h36 hs hg hcomm
  have hUcent : oddCoreIn (centralizer ({t} : Set G)) ≤
      centralizer ((twoCoreIn K₁ ⊔ twoCoreIn K₂ : Subgroup G) : Set G) :=
    (Subgroup.le_centralizer_iff.mp hcomm).trans (Subgroup.centralizer_le hQleL)
  have hcentL : oddCoreIn (centralizer ({t} : Set G)) ≤ centralizer (CFSG.conjugate L g : Set G) :=
    hQ G (CFSG.conjugate L g) (isOm6Z2_conjugate hΩ g) (twoCoreIn K₁) (twoCoreIn K₂)
      hQ₁ hQ₂ ⟨e₁⟩ ⟨e₂⟩ hcom hcard hinf (oddCoreIn (centralizer ({t} : Set G)))
      (odd_card_oddCoreIn (centralizer ({t} : Set G))) hUnorm hUcent
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact Subgroup.le_centralizer_iff.mp hcentL

end CFSG.OddStandard.SmallF3.Omega
