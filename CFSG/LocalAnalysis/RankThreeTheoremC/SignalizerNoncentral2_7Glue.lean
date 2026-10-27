module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerNoncentral2_7End
public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerNoncentral2_7Reduced
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactSections3
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace NoncentralConfig

variable {p : ℕ} {P : Sylow p G} {M D U : Subgroup G} {u : G}
  (hc : NoncentralConfig G p P M D U u)

include hc

theorem u_not_mem_commutator : u ∉ ⁅(R P U : Subgroup G), (R P U : Subgroup G)⁆ := by
  intro hu
  have hle : ⁅(R P U : Subgroup G), (R P U : Subgroup G)⁆ ≤ centralizer (D : Set G) := by
    rw [Subgroup.commutator_le]
    intro y hy y' hy'
    exact hc.commutator_mem_centralizer_D hy hy'
  have huC : u ∈ centralizer (D : Set G) := hle hu
  have huD : u ∈ D := hc.U_le_D hc.uU
  apply hc.uZ
  have hz : (⟨u, huD⟩ : D) ∈ center D := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.mp huC g g.2)
  exact ⟨_, hz, rfl⟩

theorem centralizer_ne_top : centralizer ({u} : Set G) ≠ ⊤ := by
  intro htop
  have hu : u ∈ center G := by
    rw [mem_center_iff]
    intro g
    exact mem_centralizer_singleton_iff.mp (htop ▸ mem_top g : g ∈ centralizer ({u} : Set G))
  have := hc.setting.simple
  obtain ⟨a, b, hab⟩ := hc.setting.nonab
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
  · rw [h, mem_bot] at hu
    exact hc.u1 hu
  · have ha : a ∈ center G := h ▸ mem_top a
    exact hab (mem_center_iff.mp ha b).symm

theorem zpowers_eq_center {w : G} (hw : w ∈ (center D).map D.subtype) (hw1 : w ≠ 1) :
    zpowers w = (center D).map D.subtype := by
  have hp := hc.prime
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf w = p := by
    have hdvd : orderOf w ∣ p := by
      rw [← hc.card_Z]
      exact Subgroup.orderOf_dvd_natCard _ hw
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hw1
    · exact h1
  exact Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hw) (by rw [hc.card_Z, Nat.card_zpowers, hord])

theorem centralizer_le_of_fused {z g : G} (hzZ : z ∈ (center D).map D.subtype) (hz1 : z ≠ 1)
    (hgM : g ∈ M) (hgZ : g * u * g⁻¹ ∈ (center D).map D.subtype)
    (hN : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M) : centralizer ({u} : Set G) ≤ M := by
  have hgu1 : g * u * g⁻¹ ≠ 1 := fun h => hc.u1 (by simpa using h)
  have hz : zpowers (g * u * g⁻¹) = zpowers z := by
    rw [hc.zpowers_eq_center hgZ hgu1, hc.zpowers_eq_center hzZ hz1]
  intro x hx
  have hcomm : (g * x * g⁻¹) * (g * u * g⁻¹) = (g * u * g⁻¹) * (g * x * g⁻¹) := by
    have := mem_centralizer_singleton_iff.mp hx
    calc (g * x * g⁻¹) * (g * u * g⁻¹) = g * (x * u) * g⁻¹ := by group
      _ = g * (u * x) * g⁻¹ := by rw [this]
      _ = (g * u * g⁻¹) * (g * x * g⁻¹) := by group
  have hcn : centralizer ({g * u * g⁻¹} : Set G) ≤
      normalizer ((zpowers (g * u * g⁻¹) : Subgroup G) : Set G) := by
    refine le_trans ?_ (centralizer_le_normalizer _)
    rw [zpowers_eq_closure, centralizer_closure]
  have hxn : g * x * g⁻¹ ∈ normalizer ((zpowers (g * u * g⁻¹) : Subgroup G) : Set G) :=
    hcn (mem_centralizer_singleton_iff.mpr hcomm)
  rw [hz] at hxn
  have hxM : g * x * g⁻¹ ∈ M := hN hxn
  have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
  rw [this]
  exact M.mul_mem (M.mul_mem (M.inv_mem hgM) hxM) hgM

end NoncentralConfig

theorem isElemAbelian_subgroupOf {Y : Type*} [Group Y] {p : ℕ} {H K : Subgroup Y}
    (hE : IsElemAbelian p H) : IsElemAbelian p (H.subgroupOf K) :=
  CFSG.Open.IsElemAbelian.subgroupOf hE K

theorem commutator_le_of_map_eq_bot {Y : Type*} [Group Y] {O : Subgroup Y} [O.Normal]
    {B T : Subgroup Y}
    (h : ⁅B.map (QuotientGroup.mk' O), T.map (QuotientGroup.mk' O)⁆ = ⊥) : ⁅B, T⁆ ≤ O := by
  rw [Subgroup.commutator_le]
  intro b hb t ht
  have hmem : (QuotientGroup.mk' O) ⁅b, t⁆ ∈
      ⁅B.map (QuotientGroup.mk' O), T.map (QuotientGroup.mk' O)⁆ := by
    rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem _ hb)
      (Subgroup.mem_map_of_mem _ ht)
  rw [h, mem_bot] at hmem
  exact (QuotientGroup.eq_one_iff _).mp hmem

omit [Finite G] in
theorem notSecExcl3_of_noExcludedSection3' (hno : NoExcludedSection3 G) {H : Subgroup G}
    {N : Subgroup H} [N.Normal] {L : Subgroup (H ⧸ N)} (hq : CFSG.Open.IsQuasisimple L)
    (hZ : center L = ⊥) : NotSecExcl3 ↥L :=
  notSecExcl3_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
    (hno H N L hq)

theorem notBM_of_notSecExcl3' {K : Type} [Group K] (h : NotSecExcl3 K) : NotBM K :=
  ⟨h .B (by simp [sectionExcludedNames3]), h .M (by simp [sectionExcludedNames3])⟩

namespace NoncentralConfig

variable {p : ℕ} {P : Sylow p G} {M D U : Subgroup G} {u : G}
  (hc : NoncentralConfig G p P M D U u)

include hc

theorem centralizer_le_of_sylow (hD1 : TheoremD1 G) (K1 : StronglyEmbeddedRankTwoKFactNoBM)
    (K2 : StronglyEmbeddedCyclicOuterKFact) (hno : NoExcludedSection3 G)
    (KF : SignalizerTwoGroupKFact)
    (hsyl : CFSG.ABGLocalTools.IsSylowOf p (R P U) (centralizer ({u} : Set G))) :
    centralizer ({u} : Set G) ≤ M := by
  classical
  by_contra hCM
  have hprime := hc.prime
  have : Fact p.Prime := ⟨hprime⟩
  set Y : Subgroup G := centralizer ({u} : Set G) with hYdef
  have hMc := hc.ext.obstruction.1
  have hPM := hc.P_le_M
  have hRY : R P U ≤ Y := hc.R_le_centralizer
  obtain ⟨T, hT⟩ := hsyl
  have hTR : (T : Subgroup Y) = (R P U).subgroupOf Y := by
    rw [← hT, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Y.subtype_injective]
  have hTP : (T : Subgroup Y).map Y.subtype ≤ P := hT ▸ inf_le_left
  have hTrank : 3 ≤ CFSG.Open.pRank p ((T : Subgroup Y).map Y.subtype) := by
    rw [hT]
    exact hc.rank3
  have hcore : GLBPrimeCore p Y ≤ M := hc.glbPrimeCore_le_M
  obtain ⟨Tbar, hTbar, hred⟩ := reducedNongeneration_of_not_le hprime hc.odd P hPM hMc.2 hCM T
    hTP hTrank hcore
  set O : Subgroup Y := primeComplementCore (G := Y) p with hOdef
  have hO : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  set π : Y →* Y ⧸ O := QuotientGroup.mk' O with hπ
  let uY : Y := ⟨u, mem_centralizer_singleton_iff.mpr rfl⟩
  set B : Subgroup G := omegaOneOf p (R P U) with hBdef
  have hBY : B ≤ Y := (B_le_R).trans hRY
  set BY : Subgroup Y := B.subgroupOf Y with hBYdef
  have hBYp : IsPGroup p BY :=
    (CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup p B hc.isElemAbelian_B).comap_subtype
  have hBYT : BY ≤ (T : Subgroup Y) := by
    rw [hTR]
    intro x hx
    exact B_le_R (Subgroup.mem_subgroupOf.mp hx)
  have huT : uY ∈ (T : Subgroup Y) := by
    rw [hTR]
    exact Subgroup.mem_subgroupOf.mpr hc.u_mem_R
  have hTO : (T : Subgroup Y) ⊓ O = ⊥ :=
    CFSG.AGLEmbedding.inf_eq_bot_of_isPGroup hprime T.isPGroup' hO
  have hNR : NoncentralReduced p (Y ⧸ O) Tbar (((Y ⊓ M).subgroupOf Y).map π) (BY.map π) (π uY) := by
    refine ⟨hred, (catalogSimpleSections_of_isKProper hc.setting.kProper Y
      hc.centralizer_ne_top).quotient O, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hTbar]
      exact Subgroup.map_mono hBYT
    · exact CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p
        (isElemAbelian_subgroupOf hc.isElemAbelian_B) π
    · rw [CFSG.AGLEmbedding.card_map_mk_of_isPGroup hprime O hO hBYp]
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBY).toEquiv]
      exact hc.card_B
    · intro x hx hxp
      rw [hTbar] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      have hrp : r ^ p ∈ O := by
        have h1 : π (r ^ p) = 1 := by
          rw [map_pow]
          exact hxp
        exact (QuotientGroup.eq_one_iff _).mp h1
      have hmem : r ^ p ∈ (T : Subgroup Y) ⊓ O := ⟨(T : Subgroup Y).pow_mem hr p, hrp⟩
      rw [hTO, mem_bot] at hmem
      have hrR : (r : G) ∈ R P U := by
        rw [← hT]
        exact ⟨r, hr, rfl⟩
      have hrB : (r : G) ∈ B := mem_B hrR (by simpa using congrArg Subtype.val hmem)
      exact ⟨r, Subgroup.mem_subgroupOf.mpr hrB, rfl⟩
    · exact ⟨uY, Subgroup.mem_subgroupOf.mpr (hc.U_le_B hc.uU), rfl⟩
    · exact CFSG.AGLEmbedding.orderOf_mk_of_coprime hprime O hO
        (by rw [← Subgroup.orderOf_coe]; exact hc.orderOf_u)
    · exact CFSG.AGLEmbedding.mk_mem_center_centralizer O rfl
    · intro hu
      rw [hTbar, ← Subgroup.map_commutator] at hu
      obtain ⟨w, hw, hwu⟩ := hu
      have hTT : ⁅(T : Subgroup Y), (T : Subgroup Y)⁆ ≤ (T : Subgroup Y) := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        show a * b * a⁻¹ * b⁻¹ ∈ (T : Subgroup Y)
        exact (T : Subgroup Y).mul_mem ((T : Subgroup Y).mul_mem ((T : Subgroup Y).mul_mem ha hb)
          ((T : Subgroup Y).inv_mem ha)) ((T : Subgroup Y).inv_mem hb)
      have hwT : w ∈ (T : Subgroup Y) := hTT hw
      have hwO : w⁻¹ * uY ∈ O := QuotientGroup.eq.mp hwu
      have hmem : w⁻¹ * uY ∈ (T : Subgroup Y) ⊓ O :=
        ⟨(T : Subgroup Y).mul_mem ((T : Subgroup Y).inv_mem hwT) huT, hwO⟩
      rw [hTO, mem_bot, inv_mul_eq_one] at hmem
      rw [← hmem] at huT
      refine hc.u_not_mem_commutator ?_
      have hmap := Subgroup.map_commutator (T : Subgroup Y) (T : Subgroup Y) Y.subtype
      rw [hT] at hmap
      rw [← hmap]
      exact ⟨w, hw, by rw [hmem]; rfl⟩
  have hBM : ∀ L : Subgroup (Y ⧸ O), IsComponentOf L ⊤ → center L = ⊥ → NotBM ↥L :=
    fun L hL hZ => notBM_of_notSecExcl3' (notSecExcl3_of_noExcludedSection3' hno hL.2.2 hZ)
  have hconc : centralizer ({u} : Set G) ≤ M := by
    refine hc.centralizer_le_of_commutator_le hD1 fun Tg hTg2 hTgY hBN => ?_
    set TY : Subgroup Y := Tg.subgroupOf Y with hTYdef
    have hT2 : IsPGroup 2 (TY.map π) := (hTg2.comap_subtype).map π
    have hBT : BY.map π ≤ normalizer ((TY.map π : Subgroup (Y ⧸ O)) : Set (Y ⧸ O)) := by
      rintro _ ⟨b, hb, rfl⟩
      have hbN : (b : G) ∈ normalizer (Tg : Set G) := hBN (Subgroup.mem_subgroupOf.mp hb)
      have hbTY : b ∈ normalizer ((TY : Subgroup Y) : Set Y) := by
        rw [mem_normalizer_iff] at hbN ⊢
        intro y
        exact hbN (y : G)
      exact Subgroup.le_normalizer_map π ⟨b, hbTY, rfl⟩
    have hcomm := hNR.commutator_eq_bot hBM K1 K2 KF hT2 hBT
    have hle : ⁅BY, TY⁆ ≤ O := commutator_le_of_map_eq_bot hcomm
    have hmapBT := Subgroup.map_commutator BY TY Y.subtype
    rw [Subgroup.map_subgroupOf_eq_of_le hBY, Subgroup.map_subgroupOf_eq_of_le hTgY] at hmapBT
    have hOmap : O.map Y.subtype = GLBPrimeCore p Y := by
      rw [hOdef, ← glbPrimeCore_subgroupOf, Subgroup.map_subgroupOf_eq_of_le (glbPrimeCore_le p Y)]
    rw [← hmapBT, ← hOmap]
    exact Subgroup.map_mono hle
  exact hCM hconc

end NoncentralConfig

end CFSG.LocalAnalysis.RankThreeTheoremC
