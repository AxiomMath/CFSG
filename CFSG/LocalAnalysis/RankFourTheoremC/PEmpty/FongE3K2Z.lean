module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmTwoZ
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongE3Sections

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.GH74.Uniqueness.SU CFSG.AGLEmbedding
  Subgroup

variable {Z : Type} [Group Z] [Finite Z] {p : ℕ}

theorem dispatchE3 (hAlt : KDI278Alt) (hChevP : KDI278ChevP) (hL2 : KDI278L2p2) (hL3 : KDI278L3)
    (hChevQ : KDI278ChevQ) (hSpor : KDI278Spor) (hSporB : KDI278SporB) (hSporC : KDI278SporCNoM)
    (hNoM : NoMonsterQuasisimple Z) (hI204 : KDL64I204U3) (hp : p.Prime) (hp5 : 5 ≤ p) (hcat : CatalogSimpleSections Z)
    (Q : Sylow p Z) (hrk : Open.pRank p (⊤ : Subgroup Z) ≤ 2)
    (hrk2 : Open.pRank p (⊤ : Subgroup Z) = 2) {B U : Subgroup Z} (hBel : IsElemAbelian p B)
    (hBc : Nat.card B = p ^ 2) (hUQ : U ≤ Q) (hUel : IsElemAbelian p U) (hUc : Nat.card U = p ^ 2)
    (hBU : ∀ g : Z, B.map (MulAut.conj g).toMonoidHom ≠ U) {w : Z} (hwQ : w ∈ (Q : Subgroup Z))
    (hwo : orderOf w = p) (hwc : ∀ q ∈ (Q : Subgroup Z), q * w = w * q)
    (hw : ∀ w ∈ (Q : Subgroup Z), orderOf w = p → (∀ q ∈ (Q : Subgroup Z), q * w = w * q) →
      ∀ g : Z, g * w * g⁻¹ ∈ B → g * w * g⁻¹ ∈ zpowers w)
    (hnc : ∃ a ∈ (Q : Subgroup Z), ∃ b ∈ (Q : Subgroup Z), a ^ p = 1 ∧ b ^ p = 1 ∧
      a * b ≠ b * a)
    {Y : Subgroup Z}
    (hΓU : ∀ S : Subgroup Z, S ≤ U → 1 ≤ Open.pRank p S → normalizer (S : Set Z) ≤ Y)
    (hΓ2 : ∀ S : Subgroup Z, S ≤ Q → 2 ≤ Open.pRank p S → normalizer (S : Set Z) ≤ Y)
    {K : Subgroup Z} (hK : IsComponentOf K ⊤) (hKn : K.Normal) (hcenK : Subgroup.center ↥K = ⊥)
    (hCK : centralizer (K : Set Z) = ⊥) (hKY : ¬ K ≤ Y)
    (hK2 : 2 ≤ Open.pRank p ((Q : Subgroup Z) ⊓ K)) :
    ∀ W : Subgroup Z, B ⊔ U ≤ normalizer (W : Set Z) → Nat.Coprime (Nat.card W) (2 * p) →
      W = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hsimple := isSimpleGroup_of_center_eq_bot hK hcenK
  have hcatK : IsCatalogGroup ↥K := hcat.simple_subgroup K hsimple.1 hsimple.2
  have hK2' : Open.pRank p (K : Subgroup Z) = 2 :=
    le_antisymm ((SU1.pRank_mono hp.one_lt le_top).trans hrk)
      (hK2.trans (SU1.pRank_mono hp.one_lt inf_le_right))
  have hsubK : K.IsSubnormal := hKn.isSubnormal
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Q hsubK
  have hSC : ∀ y ∈ centralizer (B : Set Z), y ^ p = 1 → y ∈ B := by
    intro y hy hyp
    by_contra hyB
    have hcomm : ∀ e ∈ B, e * y = y * e := fun e he => (mem_centralizer_iff.mp hy) e he
    obtain ⟨hel, hcard⟩ := isElemAbelian_card_sup_zpowers_of_card hp hBel hBc hyp hyB hcomm
    have := SU1.le_pRank hp.one_lt le_top hel (k := 3) hcard
    omega
  have hQcomm : ¬ IsMulCommutative ↥(Q : Subgroup Z) := by
    intro hcomm
    obtain ⟨a, ha, b, hb, -, -, hab⟩ := hnc
    exact hab (congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  intro W hBUW hcop
  have hBW : B ≤ normalizer (W : Set Z) := le_sup_left.trans hBUW
  rcases catalog_trichotomy hcatK hsimple.2 with halt | ⟨r, hlie⟩ | ⟨s, hspor⟩
  · exact absurd (hAlt p hp hp5 Z K hKn halt hCK hrk Q) hQcomm
  · by_cases hr : r = p
    · subst hr
      have hrk1 : Open.pRank r (⊤ : Subgroup ↥K) = 2 := by
        rw [← pRank_map_subtype hp.one_lt, Subgroup.map_top, Subgroup.range_subtype]
        exact hK2'
      rcases hChevP r hp hp5 ↥K hsimple.1 hsimple.2 hlie hrk1 with hl2 | hl3 | hu3
      · exact absurd (hL2 r hp hp5 Z K hKn hl2 hCK Q) hQcomm
      · exfalso
        have hY' := hL3 r hp hp5 ↥K hl3 P (Y.subgroupOf K) (fun S hSP hS2 => by
          have hSZ : S.map K.subtype ≤ (Q : Subgroup Z) := by
            have h1 : S.map K.subtype ≤ (P : Subgroup ↥K).map K.subtype := Subgroup.map_mono hSP
            rw [hP] at h1
            exact h1.trans inf_le_left
          have hrkS : 2 ≤ Open.pRank r (S.map K.subtype) := by
            rw [pRank_map_subtype hp.one_lt]
            exact hS2
          exact normalizer_subgroupOf_le S (fun x hx => hΓ2 _ hSZ hrkS hx.1))
        apply hKY
        intro k hk
        have : (⟨k, hk⟩ : ↥K) ∈ Y.subgroupOf K := by
          rw [hY']
          exact mem_top _
        exact this
      · exact hI204 r hp hp5 Z K hKn hu3 hCK B hBel hBc hSC W hBW hcop
    · exact absurd (hChevQ p hp hp5 Z K hKn hsimple.1 hsimple.2 ⟨r, hr, hlie⟩ hCK hK2' hrk2 Q hnc
        U hUQ hUel hUc Y hΓU) hKY
  · rcases hSpor p hp hp5 Z K hKn s hspor hCK hrk2 Q hnc with hB | hC
    · exfalso
      rcases hSporB p s hB Z K hKn hspor hCK hrk2 with h1 | h2
      · obtain ⟨b, hb, hbw⟩ : ∃ b ∈ B, b ∉ zpowers w := by
          by_contra hcon
          push Not at hcon
          have hle : B ≤ zpowers w := fun b hb => hcon b hb
          have hcard := Subgroup.card_le_of_le hle
          rw [Nat.card_zpowers, hwo, hBc] at hcard
          have := hp.two_le
          nlinarith
        have hbp : b ^ p = 1 := hBel.2 b hb
        have hb1 : b ≠ 1 := fun h => hbw (h ▸ one_mem _)
        have hbo : orderOf b = p := orderOf_eq_prime hbp hb1
        obtain ⟨g, hg⟩ := h1 w b hwo hbo
        have hgw : g * w * g⁻¹ ∈ zpowers b := by
          rw [← hg]
          exact ⟨w, mem_zpowers w, by simp⟩
        have hgB : g * w * g⁻¹ ∈ B := (zpowers_le.mpr hb) hgw
        have hgz := hw w hwQ hwo hwc g hgB
        have hbmem : b ∈ (zpowers w).map (MulAut.conj g).toMonoidHom := by
          rw [hg]
          exact mem_zpowers b
        obtain ⟨x, hx, hxb⟩ := hbmem
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
        apply hbw
        have : b = (g * w * g⁻¹) ^ k := by
          rw [← hxb]
          simp [conj_zpow]
        rw [this]
        exact Subgroup.zpow_mem _ hgz k
      · obtain ⟨g, hg⟩ := h2 B U hBel hBc hUel hUc
        exact hBU g hg
    · by_cases hsM : s = .M
      · subst hsM
        exfalso
        have hq : ↥K ⧸ Subgroup.center ↥K ≃* ↥K :=
          (QuotientGroup.quotientMulEquivOfEq hcenK).trans QuotientGroup.quotientBot
        obtain ⟨e⟩ := hspor
        exact hNoM K hK.2.2 ⟨hq.trans e⟩
      · exact hSporC p s hC hsM Z K hKn hspor hCK B hBel hBc hSC W hBW hcop


theorem two_ZE3 (hRank1 : KDI278Rank1) (hAlt : KDI278Alt) (hChevP : KDI278ChevP)
    (hL2 : KDI278L2p2) (hL3 : KDI278L3) (hChevQ : KDI278ChevQ) (hSpor : KDI278Spor)
    (hSporB : KDI278SporB) (hSporC : KDI278SporCNoM) (hNoM : NoMonsterQuasisimple Z)
    (hI204 : KDL64I204U3) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hcat : CatalogSimpleSections Z) (hZ : primeComplementCore (G := Z) p = ⊥)
    (Q : Sylow p Z) (hrk : Open.pRank p (⊤ : Subgroup Z) ≤ 2)
    (hZc : IsCyclic (center (Q : Subgroup Z))) (B U : Subgroup Z) (hBQ : B ≤ Q)
    (hBel : IsElemAbelian p B) (hBc : Nat.card B = p ^ 2) (hUQ : U ≤ Q)
    (hUel : IsElemAbelian p U) (hUc : Nat.card U = p ^ 2)
    (hBU : ∀ g : Z, B.map (MulAut.conj g).toMonoidHom ≠ U)
    (hw : ∀ w ∈ (Q : Subgroup Z), orderOf w = p → (∀ q ∈ (Q : Subgroup Z), q * w = w * q) →
      ∀ g : Z, g * w * g⁻¹ ∈ B → g * w * g⁻¹ ∈ zpowers w)
    (Y : Subgroup Z) (hY : ¬ ⊤ ≤ Y)
    (hΓU : ∀ S : Subgroup Z, S ≤ U → 1 ≤ Open.pRank p S → normalizer (S : Set Z) ≤ Y)
    (hΓ2 : ∀ S : Subgroup Z, S ≤ Q → 2 ≤ Open.pRank p S → normalizer (S : Set Z) ≤ Y) :
    ∀ W : Subgroup Z, B ⊔ U ≤ normalizer (W : Set Z) → Nat.Coprime (Nat.card W) (2 * p) →
      W = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hQrk : Open.pRank p (Q : Subgroup Z) ≤ 2 := (SU1.pRank_mono hp.one_lt le_top).trans hrk
  have hQ2 : 2 ≤ Open.pRank p (Q : Subgroup Z) := SU1.le_pRank hp.one_lt hBQ hBel (k := 2) hBc
  have hrk2 : Open.pRank p (⊤ : Subgroup Z) = 2 :=
    le_antisymm hrk (hQ2.trans (SU1.pRank_mono hp.one_lt le_top))
  have hQY : (Q : Subgroup Z) ≤ Y := Subgroup.le_normalizer.trans (hΓ2 _ le_rfl hQ2)
  have hBne : B ≠ U := by
    intro h
    apply hBU 1
    rw [← h]
    ext x
    simp
  obtain ⟨b, hb, u, hu, hbu⟩ := exists_noncomm_of_ne hp hQrk hBQ hUQ hBel hBc hUel hUc hBne
  have hnc : ∃ a ∈ (Q : Subgroup Z), ∃ b ∈ (Q : Subgroup Z), a ^ p = 1 ∧ b ^ p = 1 ∧
      a * b ≠ b * a := ⟨b, hBQ hb, u, hUQ hu, hBel.2 b hb, hUel.2 u hu, hbu⟩
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hbu (by simp)
  have hQne : (Q : Subgroup Z) ⊓ (⊤ : Subgroup Z) ≠ ⊥ := by
    intro h
    have : b ∈ (Q : Subgroup Z) ⊓ (⊤ : Subgroup Z) := ⟨hBQ hb, mem_top b⟩
    rw [h, Subgroup.mem_bot] at this
    exact hb1 this
  have hQM : (Q : Subgroup Z) ≤ normalizer (((⊤ : Subgroup Z)) : Set Z) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨w, hwT, hwo, hwc⟩ := exists_central_of_inf hp Q hQM hQne
  have hwQ : w ∈ (Q : Subgroup Z) := hwT.1
  have hwp : w ^ p = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hwo] at this
  have hw1 : w ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hwo
    exact hp.one_lt.ne hwo
  have hwU : w ∈ U := P64Free.mem_of_central_of_pRank_le_two hp hQrk hUQ hUel hUc hwQ hwp hwc
  have hwN : normalizer ((zpowers w : Subgroup Z) : Set Z) ≤ Y :=
    hΓU _ (zpowers_le.mpr hwU) (P64Free.one_le_pRank_zpowers hp hwp hw1)
  have hQnc : ¬ IsCyclic ↥(Q : Subgroup Z) := not_isCyclic_of_two_le_pRank hp hQ2
  obtain ⟨L, hL⟩ := exists_isComponentOf_Z hp hp2 hZ Q hQnc hQY hΓ2 hY
  by_cases hI : 2 ≤ Open.pRank p ((Q : Subgroup Z) ⊓ sSup {M : Subgroup Z | IsComponentOf M ⊤})
  · obtain ⟨K, hK, hKn, -, hcenK, hCK, hKY, hK2⟩ :=
      caseI hp hp5 hZ Q hZc hQrk hwQ hwo hwc hY hΓ2 hwN hL hI
    exact dispatchE3 hAlt hChevP hL2 hL3 hChevQ hSpor hSporB hSporC hNoM hI204 hp hp5 hcat Q hrk hrk2
      hBel hBc hUQ hUel hUc hBU hwQ hwo hwc hw hnc hΓU hΓ2 hK hKn hcenK hCK hKY hK2
  · exfalso
    exact caseII hRank1 hp hp5 hcat hZ Q hZc hwQ hwo hwc hL hnc (by omega)


end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm
