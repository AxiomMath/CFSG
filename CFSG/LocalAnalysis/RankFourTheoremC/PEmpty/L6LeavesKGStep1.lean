module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGCfg
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L617
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Basic
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Frattini
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Lines
import CFSG.GroupTheory.BaerSuzuki.Helpers
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L618
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (IsMaxTwoInvariantIn)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}

theorem glbPrimeCore_eq_pCoreOf (hp : p.Prime) (hp2 : p ≠ 2) (H : Subgroup G)
    (h2 : IsPGroup 2 (GLBPrimeCore p H)) : GLBPrimeCore p H = pCoreOf 2 H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · have hn : ((GLBPrimeCore p H).subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.AGLEmbedding.glbPrimeCore_le p H)).mpr
        (CFSG.AGLEmbedding.le_normalizer_glbPrimeCore p H)
    have h2' : IsPGroup 2 ((GLBPrimeCore p H).subgroupOf H) := h2.comap_subtype
    have h1 := Subgroup.map_mono (f := H.subtype)
      (CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hn h2')
    rwa [Subgroup.map_subgroupOf_eq_of_le (CFSG.AGLEmbedding.glbPrimeCore_le p H)] at h1
  · have hHn : H ≤ normalizer (pCoreOf 2 H : Set G) :=
      CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
    have hle : pCoreOf 2 H ≤ H := Subgroup.map_subtype_le _
    have hp2' : IsPGroup 2 (pCoreOf 2 H) := CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 H
    refine le_sSup ⟨hle, (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hHn, ?_⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp2'
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)

theorem kgStrongEmb_of_L613b (hL613b : KGL613b) (hS : Situation G p P M) (hx : Point P M x)
    (hz : Central P z) (hnpc : ¬ CFSG.HasNormalPComplement p ↥(centralizer ({x} : Set G))) :
    KGStrongEmb p M z := fun f hf hf2 hfp Y hYM hzY hsec' hrel =>
  hL613b G p P M x z hS hx hz hnpc Y hYM hzY hsec' f hf hf2 hfp hrel

theorem exists_kgData3 (hKF : KFact64iiL) (hS : Situation G p P M) (hx : Point P M x)
    (hz : Central P z) {H S : Subgroup G} (hopt : Optimal p M x z H S)
    (hO : GLBPrimeCore p H ≤ M)
    (hΩ : ∀ Q : Subgroup G, Q ≤ H → IsPGroup p Q → zpowers x ⊔ zpowers z ≤ Q →
      ∀ q ∈ Q, q ^ p = 1 → q ∈ zpowers x ⊔ zpowers z)
    (hnpc : ¬ CFSG.HasNormalPComplement p ↥(centralizer ({x} : Set G)))
    (h2 : IsPGroup 2 (GLBPrimeCore p H)) :
    ∃ L : Subgroup G, KGData3 p H (GLBPrimeCore p H) S (zpowers x ⊔ zpowers z) L M z := by
  have hprime := hS.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  have hp2 : p ≠ 2 := hS.ne_two
  have hHtop : H ≠ ⊤ := isTwoLocal_ne_top hS hopt.ext.pair.isTwoLocal
  have hcat : ∀ X : Subgroup G, X ≤ H → CFSG.AGLEmbedding.CatalogSimpleSections ↥X := fun X hXH =>
    CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.toGlobal.d1Global.kProper X
      (fun h => hHtop (top_le_iff.mp (h ▸ hXH)))
  have hKH : CFSG.Open.IsKGroup ↥H :=
    CFSG.AGLEmbedding.catalogSimpleSections_iff_isKGroup.mp (hcat H le_rfl)
  have hzo : orderOf z = p := orderOf_eq_prime hz.pow_eq_one hz.ne_one
  have hxz : x * z = z * x := mem_centralizer_iff.mp hz.centralizes x hx.mem
  have hxnz : x ∉ zpowers z := s622_x_not_mem_zpowers hS hx hz
  have hpl := plane_of_central hS hx hz
  have hB3 : IsPGroup p (zpowers x ⊔ zpowers z : Subgroup G) :=
    IsPGroup.of_card (n := 2) hpl.card_eq
  have hBH : zpowers x ⊔ zpowers z ≤ H := hopt.ext.pair.le
  have hB3' : IsPGroup p ↥((zpowers x ⊔ zpowers z).subgroupOf H) :=
    hB3.of_equiv (subgroupOfEquivOfLe hBH).symm
  obtain ⟨Q', hQ'⟩ := hB3'.exists_le_sylow
  set Q : Subgroup G := (Q' : Subgroup H).map H.subtype with hQ
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf p Q H := ⟨Q', rfl⟩
  have hBQ : zpowers x ⊔ zpowers z ≤ Q := by
    intro b hb
    have hbH : (⟨b, hBH hb⟩ : H) ∈ (zpowers x ⊔ zpowers z).subgroupOf H := hb
    exact ⟨⟨b, hBH hb⟩, hQ' hbH, rfl⟩
  have hQM : Q ≤ M := hopt.sylow_le Q hQsyl.isPGroup hQsyl.le hBQ
  have hΩQ := hΩ Q hQsyl.le hQsyl.isPGroup hBQ
  have hfr : x ∉ (frattini ↥Q).map Q.subtype := x_not_mem_frattini hS hx hQsyl.isPGroup
  have hwc : ∀ g ∈ H, g * z * g⁻¹ ∈ zpowers x ⊔ zpowers z → g * z * g⁻¹ ∈ zpowers z :=
    fun g _ hg => mem_zpowers_of_conj_mem_plane hS hx hz hg
  have hNZ : normalizer (zpowers z : Set G) ⊓ H ≤ M ⊓ H :=
    fun g hg => ⟨normalizer_zpowers_le hS hz hg.1, hg.2⟩
  have hcover : ¬ H ≤ (M ⊓ H) ⊔ rankThreePrimeCore p H := by
    intro hle
    exact hopt.ext.pair.not_le (hle.trans (sup_le inf_le_left hO))
  obtain ⟨L, hsec, hLH, hzL, hrk, hLnot, hMN⟩ := hKF G p H Q (M ⊓ H) x z hprime hS.p_ge hKH
    hx.order hzo hxz hxnz hQsyl hBQ hΩQ hfr hwc (le_inf hQM hQsyl.le) inf_le_right hNZ hcover
  refine ⟨L, ?_⟩
  have hDeq := glbPrimeCore_eq_pCoreOf hprime hp2 H h2
  obtain ⟨⟨-, hS2, hBS⟩, hSmax⟩ := hopt.maxInv
  have hSHM : S ≤ H ⊓ M := hopt.ext.pair.isMax.1.1
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup G) := hpl.isIsolatedPlane.1
  refine ⟨⟨hprime, hS.p_ge, CFSG.AGLEmbedding.glbPrimeCore_le p H,
    CFSG.AGLEmbedding.le_normalizer_glbPrimeCore p H, h2, hO, ?_, hSHM.trans inf_le_left,
    hSHM.trans inf_le_right, hS2, hBH,
    hBP.trans hS.sylow_le, hpl.isElemAbelian, hpl.card_eq, Subgroup.mem_sup_right
      (mem_zpowers z), hzo, hBS, ?_, ?_, normalizer_zpowers_le hS hz, hsec, hLH, hzL, hrk, ?_,
    hMN⟩, ?_,
    hopt.pRank_le, hcat, hopt.char_le⟩
  · rw [hDeq]
    exact hopt.core_lt
  · exact fun S' hS'H hS'2 hBS' hSS' => hSmax S' ⟨hS'H, hS'2, hBS'⟩ hSS'
  · intro S₀ hS₀ hS₀S hSB
    rw [hDeq] at hS₀
    exact hopt.norm_le S₀ hS₀ hS₀S hSB
  · intro hLM
    exact hLnot (fun l hl => Subgroup.mem_sup_left ⟨⟨hLM hl, hLH hl⟩, hl⟩)
  · intro g hg
    have := hS.toGlobal.d1Global.charTwo H hopt.ext.pair.isTwoLocal
    rw [← hDeq] at this
    exact this hg

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGC
