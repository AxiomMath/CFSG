module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0Sylow
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoBorel
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMDataAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Borel

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime] {Y₀ L : Subgroup Y}

theorem le_normalizer_inf_of_isCoatom [L.Normal] (Rb : Sylow p Y)
    (hNT : L ⊓ Subgroup.normalizer ((((Rb : Subgroup Y) ⊓ L : Subgroup Y)) : Set Y) ≤ Y₀)
    (hLY₀ : ¬ L ≤ Y₀) (T₁ : Sylow p L)
    (hT₁ : (T₁ : Subgroup L).map L.subtype = (Rb : Subgroup Y) ⊓ L)
    (hcoat : IsCoatom (Subgroup.normalizer ((T₁ : Subgroup L) : Set L))) :
    Y₀ ≤ Subgroup.normalizer ((((Rb : Subgroup Y) ⊓ L : Subgroup Y)) : Set Y) := by
  have hUY₀ : (Rb : Subgroup Y) ⊓ L ≤ Y₀ := fun u hu => hNT ⟨hu.2, Subgroup.le_normalizer hu⟩
  set W : Subgroup L := (Y₀ ⊓ L).subgroupOf L with hW
  have hNW : Subgroup.normalizer ((T₁ : Subgroup L) : Set L) ≤ W := by
    intro n hn
    have h1 := coe_mem_normalizer_map hn
    rw [hT₁] at h1
    exact Subgroup.mem_subgroupOf.mpr ⟨hNT h1, n.2⟩
  have hWtop : W ≠ ⊤ := by
    intro htop
    apply hLY₀
    intro k hk
    have : (⟨k, hk⟩ : L) ∈ W := htop ▸ Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp this).1
  have hWeq : W = Subgroup.normalizer ((T₁ : Subgroup L) : Set L) := by
    by_contra hne
    exact hWtop (hcoat.2 W (lt_of_le_of_ne hNW (Ne.symm hne)))
  have hY₀L : Y₀ ⊓ L ≤ Subgroup.normalizer ((((Rb : Subgroup Y) ⊓ L : Subgroup Y)) : Set Y) := by
    intro y hy
    have hyW : (⟨y, hy.2⟩ : L) ∈ W := Subgroup.mem_subgroupOf.mpr hy
    rw [hWeq] at hyW
    have h2 := (coe_mem_normalizer_map hyW).2
    rwa [hT₁] at h2
  exact le_normalizer_sylow_inf L Rb hUY₀ hY₀L

end Borel

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem D1PhaseThree.map_inf_le_normalizer_d1MapPCore {P' : Sylow p G} {M H₁ S : Subgroup G}
    (h3₁ : D1PhaseThree p P' M H₁ S) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) :
    ((H₁ ⊓ M).subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) ≤
      Subgroup.normalizer (d1MapPCore p M H₁ : Set (H₁ ⧸ primeComplementCore (G := H₁) p)) :=
  map_le_normalizer_map _ ((h3₁.pCorePreimage_le_inf h84 hD2).trans inf_le_left)
    (inf_le_right.trans (le_normalizer_pCorePreimage p M))

namespace D1OneLieKZeroData

variable {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {P' : Sylow p G} {H₁ S : Subgroup G}

theorem d1MapPCore_le_map_liftX (hc : D1OneLieKZeroData p P M H R Rbar K P' H₁ S)
    (hK : KFactOneLie) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hWK : d1MapPCore p M H ≤ K) (h3₁ : D1PhaseThree p P' M H₁ S) :
    d1MapPCore p M H₁ ≤ ((d1LiftX p H R K).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) := by
  have hd := hc.data
  have h3 := hd.toPhaseThree hK
  have hRY : R ⊓ pCorePreimage p M ≤ d1LiftX p H R K := by
    rintro r ⟨hrR, hrY⟩
    have hrH : r ∈ H := hd.cfg.ext.le_H hrR
    have hrK : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨r, hrH⟩ ∈ K :=
      hWK ⟨⟨r, hrH⟩, hrY, rfl⟩
    exact ⟨⟨r, hrH⟩, ⟨hrR, hrK⟩, rfl⟩
  have hle : R ⊓ pCorePreimage p M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    (inf_le_right.trans (pCorePreimage_le p M)).trans (localGroup_le_normalizer_pCoreOf 2 M)
  rintro _ ⟨⟨y, hyH₁⟩, hyY, rfl⟩
  have hyY' : y ∈ ((R ⊓ pCorePreimage p M ⊔ pCoreOf 2 M : Subgroup G) : Set G) := by
    rw [h3.inf_sup_twoCore_eq h84 hD2]
    exact hyY
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hyY'
  obtain ⟨a, ha, q, hq, rfl⟩ := Set.mem_mul.mp hyY'
  have haX : a ∈ d1LiftX p H R K := hRY ha
  have haH₁ : a ∈ H₁ := hc.liftX_le_H₁ haX
  have hqN : q ∈ GLBPrimeCore p H₁ := h3₁.twoCore_M_le_glbPrimeCore hq
  have hqH₁ : q ∈ H₁ := glbPrimeCore_le p H₁ hqN
  have hsplit : (⟨a * q, hyH₁⟩ : H₁) = ⟨a, haH₁⟩ * ⟨q, hqH₁⟩ := rfl
  have hq1 : QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨q, hqH₁⟩ = 1 :=
    (mk'_primeComplementCore_eq_one_iff p ⟨q, hqH₁⟩).mpr hqN
  rw [hsplit, map_mul, hq1, mul_one]
  exact ⟨⟨a, haH₁⟩, Subgroup.mem_subgroupOf.mpr haX, rfl⟩

theorem d1MapPCore_ne_bot (hc : D1OneLieKZeroData p P M H R Rbar K P' H₁ S)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥) : d1MapPCore p M H₁ ≠ ⊥ := by
  have hp := hc.escape.prime
  have hYH₁ : pCorePreimage p M ⊓ d1LiftX p H R K ≤ H₁ :=
    inf_le_right.trans hc.liftX_le_H₁
  have hXp : IsPGroup p (pCorePreimage p M ⊓ d1LiftX p H R K : Subgroup G) :=
    (hc.data.cfg.ext.isPGroup.to_le (d1LiftX_le p H R K)).to_le inf_le_right
  have hne := map_mk_ne_bot_of_isPGroup hp hYH₁ hXp hY
  exact ne_bot_of_le_ne_bot hne (Subgroup.map_mono (Subgroup.comap_mono inf_le_left))

theorem centerOf_le_d1MapPCore (hc : D1OneLieKZeroData p P M H R Rbar K P' H₁ S)
    (hK : KFactOneLie) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥) (hWK : d1MapPCore p M H ≤ K)
    (h3₁ : D1PhaseThree p P' M H₁ S) [Fact p.Prime]
    (Rb₁ : Sylow p (H₁ ⧸ primeComplementCore (G := H₁) p))
    {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)} [L.Normal]
    (hnc : ¬ IsCyclic ((Rb₁ : Subgroup _) ⊓ L : Subgroup _))
    (hNT : L ⊓ Subgroup.normalizer ((((Rb₁ : Subgroup _) ⊓ L : Subgroup _)) :
      Set (H₁ ⧸ primeComplementCore (G := H₁) p)) ≤
      ((H₁ ⊓ M).subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p)))
    (hLX : ¬ L ≤
      ((H₁ ⊓ M).subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p)))
    (hZL : Subgroup.center L = ⊥) (T₁ : Sylow p L)
    (hT₁ : (T₁ : Subgroup L).map L.subtype = (Rb₁ : Subgroup _) ⊓ L)
    (hF : OneLieFacts p L T₁) {n e : ℕ} (hTF : OneLieTorusFacts p L T₁ n e)
    (hXL : ((d1LiftX p H R K).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) ≤ L) :
    centerOf ((Rb₁ : Subgroup _) ⊓ L) ≤ d1MapPCore p M H₁ := by
  have hY₀T := le_normalizer_inf_of_isCoatom Rb₁ hNT hLX T₁ hT₁ hTF.borel_coatom
  have hWY₀ : d1MapPCore p M H₁ ≤
      ((H₁ ⊓ M).subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) :=
    Subgroup.map_mono (Subgroup.comap_mono (h3₁.pCorePreimage_le_inf h84 hD2))
  rcases centerOf_le_or_le_centralizer_of_torus hc.escape.ne_two Rb₁ hnc hNT hZL T₁ hT₁ hF hTF
      hY₀T (d1MapPCore p M H₁) hWY₀ (h3₁.map_inf_le_normalizer_d1MapPCore h84 hD2) with h | h
  · exact h
  · exfalso
    apply hc.d1MapPCore_ne_bot hY
    rw [eq_bot_iff]
    intro w hw
    have hwL : w ∈ L := hXL (hc.d1MapPCore_le_map_liftX hK h84 hD2 hWK h3₁ hw)
    have hwZ : (⟨w, hwL⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (h hw) l l.2)
    rw [hZL, Subgroup.mem_bot] at hwZ
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hwZ)

end D1OneLieKZeroData

end CFSG.AGLEmbedding
