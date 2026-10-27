module

public import CFSG.LargeExtraspecial.S4TwoMain
public import CFSG.LargeExtraspecial.S7Alt4
public import CFSG.LargeExtraspecial.DW37Statement
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial.S4

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem concl_of_isReducible [IsSimpleGroup G] (hDW : DW.DW37Statement) (hn : 5 ≤ S.width)
    {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hred : S.IsReducible) :
    Bridge.TimmesfeldConclusion G S.width S.Mbar :=
  Bridge.TimmesfeldConclusion.of_psl (hDW G S g hn haQ hne hred)

theorem irr_of_not_isReducible (hirr : ¬ S.IsReducible) : S5.Irr S := by
  intro U hU
  by_contra h
  push Not at h
  exact hirr ⟨U, h.1, h.2, fun m v hv => hU _ ⟨m, rfl⟩ v hv⟩

theorem noA2_of {g : G} (hno : ¬ S.HasTypeAInL g) : NoA2 S g :=
  fun α h1 h2 h3 => hno ⟨α, h1, h2, h3⟩

theorem hyp4_of (hTI : WeaklyClosedTITransitive.{0}) (hn : 5 ≤ S.width) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g)
    (hirr : ¬ S.IsReducible) : Hyp4 S g where
  conj_mem := haQ
  conj_ne := hne
  fixSub_eq := by
    rw [← S.fixLbar_eq_span hTI (by omega) haQ hne hno hirr]
    ext v
    rw [mem_fixSub, Setting.mem_fixLbar]
  two_lt_width := by omega

theorem cons311_of (hTI : WeaklyClosedTITransitive.{0}) (hn : 5 ≤ S.width) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g)
    (hirr : ¬ S.IsReducible) : Cons311 S g := by
  obtain ⟨hL, hX, -, -, hC⟩ := (S.lemma_3_11_two hTI (by omega) haQ hne hno).resolve_left hirr
  exact {
    weaklyClosed := fun h hh hle => S.lemma_3_11_weaklyClosed (by omega) haQ hne hno hh hle
    card_Lbar := hL
    card_QG_inf_Qa := hX
    comm_le := fun x hx s hs => S.sub_mem_clSub_of_mem_Lbar haQ hne hs hx.1
      (mem_centralizer_singleton_iff.mp hx.2)
    faithful := hC }

theorem claim_14_3 (hF2 : Form2StrongStmt) (hBen : BenderConjCountInput)
    (hTI : WeaklyClosedTITransitive.{0}) {g : G} (H : Hyp4 S g) (C : Cons311 S g)
    (hNo : NoA2 S g) (hirr : ¬ S.IsReducible) (hn : 5 ≤ S.width) :
    ∃ t ∈ S.Lbar g, t ≠ 1 ∧ Rbar S g t ≠ S.Lbar g := by
  by_contra hcon
  push Not at hcon
  have hTIset : ∀ h : S.M, S.Lbar ((h : G) * g) ⊓ S.Lbar g = ⊥ ∨
      S.Lbar ((h : G) * g) = S.Lbar g := by
    intro h
    by_cases hb : S.Lbar ((h : G) * g) ⊓ S.Lbar g = ⊥
    · exact Or.inl hb
    · right
      obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hb
      have ht1' : t ≠ 1 := fun h1 => ht1 (Subtype.ext h1)
      have hle : S.Lbar ((h : G) * g) ≤ S.Lbar g := by
        rw [← hcon t ht.2 ht1']
        exact Lbar_mul_le_Rbar ht.1
      have hcard : Nat.card (S.Lbar ((h : G) * g)) = Nat.card (S.Lbar g) := by
        rw [Lbar_mul S h g]
        exact Subgroup.card_map_of_injective (MulAut.conj (S.ρ h)).injective
      exact Subgroup.eq_of_le_of_card_ge hle hcard.ge
  have := (lemma_4_2 hF2 hBen hTI H C hNo hTIset hirr).1
  omega

theorem Nbar_eq_zpowers_of_N0bar {g : G} (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (hN0 : Nbar S g t = N0bar S g t) (hLN : S.Lbar g ⊓ Nbar S g t = zpowers t) :
    Nbar S g t = zpowers t := by
  have haQ := H.conj_mem
  refine le_antisymm ?_ (zpowers_le.mpr (S6.self_mem_Nbar H ht))
  rw [hN0]
  refine iSup₂_le fun k hk => ?_
  rintro y ⟨hyL, hyN⟩
  rw [Lbar_mul S k g] at hyL
  obtain ⟨x, hx, rfl⟩ := hyL
  have hc : S.ρ k * t = t * S.ρ k := commute_of_mem_Rbar haQ hk
  have hc' : S.ρ k⁻¹ * t = t * S.ρ k⁻¹ := by
    rw [map_inv]
    calc (S.ρ k)⁻¹ * t = (S.ρ k)⁻¹ * (t * S.ρ k) * (S.ρ k)⁻¹ := by group
      _ = (S.ρ k)⁻¹ * (S.ρ k * t) * (S.ρ k)⁻¹ := by rw [hc]
      _ = t * (S.ρ k)⁻¹ := by group
  have hy : (MulAut.conj (S.ρ k)).toMonoidHom x = S.ρ k * x * (S.ρ k)⁻¹ := rfl
  rw [hy] at hyN ⊢
  have hxN : x ∈ Nbar S g t := by
    have h1 := conj_mem_Nbar haQ hc' hyN
    rwa [map_inv, inv_inv, show (S.ρ k)⁻¹ * (S.ρ k * x * (S.ρ k)⁻¹) * S.ρ k = x by group]
      at h1
  have hxZ : x ∈ zpowers t := by
    rw [← hLN]
    exact ⟨hx, hxN⟩
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hxZ
  refine mem_zpowers_iff.mpr ⟨i, ?_⟩
  rw [(Commute.zpow_right (show Commute (S.ρ k) t from hc) i).eq, mul_inv_cancel_right]

theorem width_le_four_of_tau_not_mem {g : G} (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4)
    (hτ : spTransvection _ (beta_isAlt H C ht ht1 hVQ) (aV ht) ∉ LmodN S g t)
    (hLN : S.Lbar g ⊓ Nbar S g t = zpowers t) : S.width ≤ 4 := by
  have h1 := S6.card_Lbar_eq_mul H.conj_mem ht (t := t)
  rw [C.card_Lbar, hLN, S7.card_zpowers_eq_two H ht ht1] at h1
  have h2 := S5.card_LmodN_le_four_of_tau_not_mem H C ht ht1 hVQ h4 hτ
  have h5 : 2 ^ (S.width - 1) ≤ 2 ^ 3 := by rw [h1]; omega
  have h6 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h5
  omega

theorem claim_14_4 (hCE : CentralExtInput.{0}) {g : G} (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) (hirr : ¬ S.IsReducible) (hn : 5 ≤ S.width) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hR : Rbar S g t ≠ S.Lbar g) (hVQ : ¬ V S g t ≤ S.Qa g) :
    S.Lbar g ⊓ Nbar S g t ≠ zpowers t ∨ Bridge.TimmesfeldConclusion G S.width S.Mbar := by
  by_cases hLN : S.Lbar g ⊓ Nbar S g t = zpowers t
  · right
    rcases timmesfeld_4_5_of_not_le H hNo C ht ht1 hVQ with hSp | hA | hΩ | hP
    · exact absurd hLN (S6.timmesfeld_6_4 hCE H hNo C ht ht1 hVQ hSp).ne'
    · have := width_le_four_of_tau_not_mem H C ht ht1 hVQ hA.finrank_eq hA.tau_not_mem hLN
      omega
    · have hN := Nbar_eq_zpowers_of_N0bar H ht
        (S6.Nbar_eq_N0bar_of_omegaCase hCE H hNo C ht ht1 hVQ hΩ) hLN
      rcases Nat.lt_or_ge S.width 7 with h7 | h7
      · obtain ⟨-, -, -, h6 | ⟨h8, -⟩⟩ := S7.timmesfeld_7_6 hCE H hNo C ht ht1 hR hN hn
        · exact Bridge.TimmesfeldConclusion.of_alt4
            (S7.timmesfeldAlt4 hCE (irr_of_not_isReducible hirr) H hNo C ht ht1 hR hN h6)
        · omega
      · exact Bridge.TimmesfeldConclusion.of_alt3
          (S7.timmesfeldAlt3 hCE H hNo C ht ht1 hR hN (by omega))
    · have := width_le_four_of_tau_not_mem H C ht ht1 hVQ hP.finrank_eq hP.tau_not_mem hLN
      omega
  · exact Or.inl hLN

end CFSG.LargeExtraspecial.S14
