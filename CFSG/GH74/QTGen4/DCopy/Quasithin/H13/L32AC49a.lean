module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC48b
public import CFSG.Quasithin.H13.L32AC47a
public import CFSG.Quasithin.H13.L32AC47f

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Quasithin.H13.L32A.C.Alt6 (conjK conjK_apply)

section Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem mem_pCoreOf_of_comm_F4 (h28 : Lemma14_7_28_F4) (S : Setting147 G T L V H) {K : Subgroup G}
    (hcK : cComp H = {K}) (hL1K : l1 T L V ≤ K) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hZ : Subgroup.center (cStar K) = ⊥) {x : G} (hx : x ∈ H)
    (hxc : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K) : x ∈ pCoreOf 2 H := by
  have hK : K ∈ cComp H := by rw [hcK]; exact Set.mem_singleton K
  have hKH : K ≤ H := le_of_mem_cComp hK
  obtain ⟨e⟩ := CFSG.Quasithin.modO2_mulEquiv hK
  set N := CFSG.pCore 2 ↥H with hN
  set Kb := modO2Image H K with hKb
  have hK'n : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
  have hKbn : Kb.Normal := hK'n.map _ (QuotientGroup.mk'_surjective _)
  have hZb : Subgroup.center ↥Kb = ⊥ := by
    have hc := card_center_eq_of_mulEquiv ((cStarEquiv K).trans e)
    rw [hZ, Subgroup.card_bot] at hc
    exact Subgroup.card_eq_one.mp hc.symm
  have hC := centralizer_eq_bot_F4 h28 S hcK hL1K hKbn hZb
  have hxC : (QuotientGroup.mk (⟨x, hx⟩ : ↥H) : ↥H ⧸ N) ∈
      Subgroup.centralizer (Kb : Set (↥H ⧸ N)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨⟨k, hkH⟩, hkK, rfl⟩
    have hkK' : k ∈ K := hkK
    have h1 := A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK) (hxc k hkK')
    have h2 : (⟨x, hx⟩ : ↥H) * ⟨k, hkH⟩ * (⟨x, hx⟩ : ↥H)⁻¹ * (⟨k, hkH⟩ : ↥H)⁻¹ ∈ N := by
      rw [hN, A3.pCore_eq_openCore]
      obtain ⟨y, hy, hyx⟩ := h1
      have : y = (⟨x, hx⟩ : ↥H) * ⟨k, hkH⟩ * (⟨x, hx⟩ : ↥H)⁻¹ * (⟨k, hkH⟩ : ↥H)⁻¹ :=
        Subtype.ext hyx
      rw [← this]
      exact hy
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv] at h2
    show QuotientGroup.mk' N ⟨k, hkH⟩ * QuotientGroup.mk ⟨x, hx⟩ =
      QuotientGroup.mk ⟨x, hx⟩ * QuotientGroup.mk' N ⟨k, hkH⟩
    rw [QuotientGroup.mk'_apply]
    have h3 := mul_inv_eq_one.mp h2
    calc (QuotientGroup.mk (⟨k, hkH⟩ : ↥H) : ↥H ⧸ N) * QuotientGroup.mk ⟨x, hx⟩ =
        (QuotientGroup.mk ⟨x, hx⟩ * QuotientGroup.mk (⟨k, hkH⟩ : ↥H) *
          (QuotientGroup.mk ⟨x, hx⟩)⁻¹) * QuotientGroup.mk ⟨x, hx⟩ := by rw [h3]
      _ = QuotientGroup.mk ⟨x, hx⟩ * QuotientGroup.mk ⟨k, hkH⟩ := by group
  rw [hC, Subgroup.mem_bot, QuotientGroup.eq_one_iff, hN, A3.pCore_eq_openCore] at hxC
  exact ⟨_, hxC, rfl⟩

end Setting

end CFSG.Quasithin.H13.L32A.C
