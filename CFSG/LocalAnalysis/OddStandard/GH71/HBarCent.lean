module

public import CFSG.LocalAnalysis.OddStandard.GH71.HBarCover
public import CFSG.LocalAnalysis.OddStandard.GH71.HBarLift
public import CFSG.LocalAnalysis.OddStandard.Solomon75Consistency
public import CFSG.LocalAnalysis.OddStandard.Solomon75GH71Pairing
public import CFSG.LocalAnalysis.OddStandard.Solomon75T11bLy

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.OddStandard.Solomon75

variable {G : Type} [Group G] [Finite G] {z : G} {S U : Subgroup G} {u : G}

namespace Ctx71

noncomputable abbrev zBar (H : Subgroup G) (hzH : z ∈ H) : HBar H :=
  QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨z, hzH⟩

theorem orderOf_zBar (h : Ctx71 G z S U u) {H : Subgroup G} (hzH : z ∈ H) :
    orderOf (zBar H hzH) = 2 := by
  have hz2 : (⟨z, hzH⟩ * ⟨z, hzH⟩ : ↥H) = 1 := Subtype.ext (h.sq_eq_one_of_mem_U h.z_mem)
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_two, ← map_mul, hz2, map_one]
  · intro h1
    have hmem : (⟨z, hzH⟩ : ↥H) ∈ pPrimeCore 2 ↥H := (QuotientGroup.eq_one_iff _).mp h1
    exact not_mem_pPrimeCore_of_involution hz2 (fun e => h.z_ne_one (congrArg Subtype.val e)) hmem

theorem zBar_comm (h : Ctx71 G z S U u) {H : Subgroup G} (hSH : S ≤ H) :
    ∀ s ∈ barIn H S, s * zBar H (hSH h.ctx.z_mem) = zBar H (hSH h.ctx.z_mem) * s := by
  rintro _ ⟨s, hs, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact mem_centralizer_singleton_iff.mp (h.S_le (Subgroup.mem_subgroupOf.mp hs))

theorem zBar_mem_center (h : Ctx71 G z S U u) {H : Subgroup G} (hSH : S ≤ H)
    (h11 : IsDoubleCoverOfAlt (HBar H) 11) : zBar H (hSH h.ctx.z_mem) ∈ center (HBar H) := by
  obtain ⟨Q, hQ⟩ := h.exists_sylow_barIn hSH
  refine mem_center_of_mem_center_sylow (n := 11) (by norm_num) h11 Q ?_ ?_
  · intro s hs
    rw [hQ] at hs
    exact h.zBar_comm hSH s hs
  · have h2 := pow_orderOf_eq_one (zBar H (hSH h.ctx.z_mem))
    rw [h.orderOf_zBar, pow_two] at h2
    exact h2


theorem pPrimeCore_centralizer_bar_eq_bot (h : Ctx71 G z S U u) {H : Subgroup G} (hSH : S ≤ H)
    (hbar : IsDoubleCoverOfAlt (HBar H) 11 ∨ Blueprint.NativeSporadic.IsSporadic (HBar H) .Ly) :
    pPrimeCore 2 ↥(centralizer ({zBar H (hSH h.ctx.z_mem)} : Set (HBar H))) = ⊥ := by
  rcases hbar with h11 | hLy
  · have hc := h.zBar_mem_center hSH h11
    have htop : centralizer ({zBar H (hSH h.ctx.z_mem)} : Set (HBar H)) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [mem_centralizer_singleton_iff]
      exact (mem_center_iff.mp hc x)
    have e : ↥(centralizer ({zBar H (hSH h.ctx.z_mem)} : Set (HBar H))) ≃* HBar H :=
      (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
    have h1 := pPrimeCore_map_iso 2 e
    rw [pPrimeCore_eq_bot_of_doubleCover h11] at h1
    have h2 : (pPrimeCore 2 ↥(centralizer ({zBar H (hSH h.ctx.z_mem)} : Set (HBar H)))).map
        e.toMonoidHom = ⊥ := h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h2
  · obtain ⟨e⟩ := hLy
    have : IsSimpleGroup (HBar H) := @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.Ly.isSimpleGroup_Ly e
    have hnonab : ∃ a b : HBar H, a * b ≠ b * a := by
      by_contra hc
      push Not at hc
      have hn : (zpowers (zBar H (hSH h.ctx.z_mem))).Normal :=
        ⟨fun n hn g => by rw [hc g n, mul_assoc, mul_inv_cancel, mul_one]; exact hn⟩
      rcases hn.eq_bot_or_eq_top with hb | ht
      · have := h.orderOf_zBar (hSH h.ctx.z_mem)
        rw [zpowers_eq_bot] at hb
        rw [hb, orderOf_one] at this; omega
      · have h1 : Nat.card (HBar H) = 2 := by
          rw [← card_top (G := HBar H), ← ht, Nat.card_zpowers, h.orderOf_zBar]
        have h2 : Nat.card (HBar H) = 51765179004000000 := by
          rw [Nat.card_congr e.toEquiv]; exact Sporadic.Ly.card_Ly'
        omega
    exact pPrimeCore_cen_eq_bot_of_Ly hnonab ⟨e⟩ (h.orderOf_zBar (hSH h.ctx.z_mem))

theorem inf_pPrimeCoreOf_le (h : Ctx71 G z S U u) {H : Subgroup G} (hSH : S ≤ H)
    (hbar : IsDoubleCoverOfAlt (HBar H) 11 ∨ Blueprint.NativeSporadic.IsSporadic (HBar H) .Ly) :
    pPrimeCoreOf 2 (Cen z) ⊓ H ≤ pPrimeCoreOf 2 H := by
  set W := pPrimeCoreOf 2 (Cen z) ⊓ H with hW
  have hzH : z ∈ H := hSH h.ctx.z_mem
  set C := centralizer ({zBar H hzH} : Set (HBar H)) with hC
  have hWodd : Odd (Nat.card W) := odd_card_of_le inf_le_left (odd_card_pPrimeCoreOf' _)
  have hWC : barIn H W ≤ C := by
    rintro _ ⟨w, hw, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (mem_centralizer_singleton_iff.mp
      (pPrimeCoreOf_le' _ (Subgroup.mem_subgroupOf.mp hw).1))
  have hnorm : C ≤ normalizer (barIn H W : Set (HBar H)) := by
    have h1 := centralizer_bar_le hzH h.orderOf_z
    have h2 : barIn H (centralizer ({z} : Set G)) = barIn H (H ⊓ Cen z) := by
      unfold barIn; congr 1; ext x; simp [Subgroup.mem_subgroupOf]
    rw [h2] at h1
    refine h1.trans (IVK812.barIn_le_normalizer ?_)
    intro y hy
    exact inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_pPrimeCoreOf' _ hy.2, le_normalizer hy.1⟩
  have hbodd : Odd (Nat.card (barIn H W)) := by
    have hd : (W ⊓ pPrimeCoreOf 2 H).relIndex W ∣ Nat.card W := relIndex_dvd_card _ _
    rw [IVK812.relIndex_eq_card_barIn (inf_le_right : W ≤ H)] at hd
    exact Odd.of_dvd_nat hWodd hd
  have hle := le_pPrimeCoreOf_of_odd hWC hbodd hnorm
  have hbot : pPrimeCoreOf 2 C = ⊥ := by
    unfold pPrimeCoreOf
    rw [h.pPrimeCore_centralizer_bar_eq_bot hSH hbar, Subgroup.map_bot]
  rw [hbot, le_bot_iff] at hle
  exact (IVK812.barIn_eq_bot_iff inf_le_right).mp hle

end Ctx71

end CFSG.OddStandard.GH71
