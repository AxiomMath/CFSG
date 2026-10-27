module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3GlueC
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RHProd

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

namespace M10Config

variable {K : Type} [Group K] [Finite K] {z : K} {D : Subgroup K} (h : M10Config z D)

include h in
theorem card_centralizer_bar :
    Nat.card ↥(centralizer ({(QuotientGroup.mk z : K ⧸ fusionOddCore K)} :
      Set (K ⧸ fusionOddCore K))) = 1440 := by
  have hle : fusionOddCoreOf D ≤ centralizer ({z} : Set K) :=
    (fusionOddCoreOf_le D).trans h.D_le_C
  have hsplit : Nat.card ↥(fusionOddCoreOf D) *
      Nat.card ↥(centralizer ({(QuotientGroup.mk z : K ⧸ fusionOddCore K)} :
        Set (K ⧸ fusionOddCore K))) = Nat.card ↥(centralizer ({z} : Set K)) := by
    have h1 := Subgroup.card_ker_mul_card_of_surjective (cMap_surjective h.z_order)
    rw [h.ker_cMap, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h1
    exact h1
  have hzD : zpowers z ≤ centralizer (D : Set K) :=
    zpowers_le.2 (mem_centralizer_iff.2 fun d hd => h.z_comm d (SetLike.mem_coe.1 hd))
  have hC0 : Nat.card ↥(zpowers z ⊔ D) = 2 * Nat.card ↥D := by
    rw [card_sup_commuting hzD (fun x hx hxD => Subgroup.disjoint_def.1 h.disjoint hx hxD),
      Nat.card_zpowers, h.z_order]
  have hCcard : Nat.card ↥(centralizer ({z} : Set K)) = 4 * Nat.card ↥D := by
    have h1 := Subgroup.card_mul_index ((zpowers z ⊔ D).subgroupOf (centralizer ({z} : Set K)))
    rw [h.index_two, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.C₀_le_C).toEquiv, hC0] at h1
    rw [← h1]
    ring
  have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hD : Nat.card ↥D = 360 * Nat.card ↥(fusionOddCoreOf D) := by
    obtain ⟨e⟩ := h.quot
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (fusionOddCore ↥D)
    rw [Nat.card_congr e.toEquiv, hA6] at h1
    rw [fusionOddCoreOf, Subgroup.card_map_of_injective D.subtype_injective]
    exact h1
  have hm : 0 < Nat.card ↥(fusionOddCoreOf D) := (odd_card_fusionOddCoreOf D).pos
  refine Nat.eq_of_mul_eq_mul_left hm ?_
  rw [hsplit, hCcard, hD]
  ring

include h in
theorem center_bar_trivial {g : K ⧸ fusionOddCore K} (hg : ∀ y : K ⧸ fusionOddCore K, y * g = g * y) :
    g = 1 := by
  have hmem : QuotientGroup.mk' (fusionOddCore (K ⧸ fusionOddCore K)) g ∈
      Subgroup.center ((K ⧸ fusionOddCore K) ⧸ fusionOddCore (K ⧸ fusionOddCore K)) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (fusionOddCore (K ⧸ fusionOddCore K)) y
    rw [← map_mul, ← map_mul]
    exact congrArg (QuotientGroup.mk' (fusionOddCore (K ⧸ fusionOddCore K))) (hg x)
  have hgZ : g ∈ fusionZStar (K ⧸ fusionOddCore K) := hmem
  rw [h.fusionZStar_eq_bot, mem_bot] at hgZ
  exact hgZ

include h in
theorem map_D_le : D.map (QuotientGroup.mk' (fusionOddCore K)) ≤
    centralizer ({(QuotientGroup.mk z : K ⧸ fusionOddCore K)} : Set (K ⧸ fusionOddCore K)) := by
  rintro _ ⟨d, hd, rfl⟩
  rw [mem_centralizer_singleton_iff]
  show (QuotientGroup.mk d : K ⧸ fusionOddCore K) * QuotientGroup.mk z =
    QuotientGroup.mk z * QuotientGroup.mk d
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h.z_comm d hd]

include h in
theorem map_D_iso : Nonempty (↥(D.map (QuotientGroup.mk' (fusionOddCore K))) ≃*
    alternatingGroup (Fin 6)) := by
  obtain ⟨e⟩ := h.quot
  have hrange : ((QuotientGroup.mk' (fusionOddCore K)).comp D.subtype).range =
      D.map (QuotientGroup.mk' (fusionOddCore K)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : ((QuotientGroup.mk' (fusionOddCore K)).comp D.subtype).ker = fusionOddCore ↥D := by
    ext d
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · exact fun hd => mem_oddCore_of_mem_O D (d := d) hd
    · intro hd
      have hmem : D.subtype d ∈ fusionOddCoreOf D := Subgroup.mem_map_of_mem D.subtype hd
      exact h.oddCoreOf_le_O hmem
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans
    ((QuotientGroup.quotientKerEquivRange
      ((QuotientGroup.mk' (fusionOddCore K)).comp D.subtype)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans e))⟩

include h in
theorem card_map_two {F : Subgroup K} (hFD : F ≤ D) (hF2 : IsPGroup 2 F) :
    Nat.card ↥(F.map (QuotientGroup.mk' (fusionOddCore K))) = Nat.card ↥F := by
  have hinj : Function.Injective ((QuotientGroup.mk' (fusionOddCore K)).comp F.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ha
    have ha' : (a : K) ∈ fusionOddCore K := ha
    obtain ⟨k, hk⟩ := hF2 a
    have hk' : (a : K) ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hodd : Odd (orderOf (a : K)) :=
      Odd.of_dvd_nat (odd_natCard_fusionOddCore K) (Subgroup.orderOf_dvd_natCard _ ha')
    exact Subtype.ext (eq_one_of_odd_of_pow_two hodd k hk')
  have hrange : ((QuotientGroup.mk' (fusionOddCore K)).comp F.subtype).range =
      F.map (QuotientGroup.mk' (fusionOddCore K)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  calc Nat.card ↥(F.map (QuotientGroup.mk' (fusionOddCore K)))
      = Nat.card ↥(((QuotientGroup.mk' (fusionOddCore K)).comp F.subtype).range) := by
        rw [hrange]
    _ = Nat.card ↥((⊤ : Subgroup ↥F).map
          ((QuotientGroup.mk' (fusionOddCore K)).comp F.subtype)) := by
        rw [MonoidHom.range_eq_map]
    _ = Nat.card ↥(⊤ : Subgroup ↥F) := Subgroup.card_map_of_injective hinj
    _ = Nat.card ↥F := Subgroup.card_top

end M10Config

end CFSG.EvenSporadicStandard.Fin76b
