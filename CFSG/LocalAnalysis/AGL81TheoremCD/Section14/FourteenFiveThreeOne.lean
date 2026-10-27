module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFiveThreeFusion
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFiveThreeAtC
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFiveThreeKFacts
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFiveThreeRank
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A11TwoSetThree
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFiveThree

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.AGL81TheoremCD

variable {G : Type} [Group G] [Finite G] {M H E Q : Subgroup G}

theorem le_map_derivedSeries_of_isPerfect {A B : Type} [Group A] [Group B] (f : A →* B)
    {P : Subgroup B} (hP : Group.IsPerfect ↥P) (hPrange : P ≤ f.range) (n : ℕ) :
    P ≤ Subgroup.map f (derivedSeries A n) := by
  induction n with
  | zero =>
      rw [derivedSeries_zero, Subgroup.map_top]
      exact hPrange
  | succ n ih =>
      have hcomm : ⁅P, P⁆ = P := (Subgroup.isPerfect_iff (H := P)).mp hP
      rw [← hcomm, derivedSeries_succ,
        Subgroup.map_commutator (H₁ := derivedSeries A n) (H₂ := derivedSeries A n) f]
      exact Subgroup.commutator_mono ih ih

namespace Ctx

variable (c : Ctx G M H E Q)

theorem exists_setting1417 {p : ℕ} (hp : p ∈ sigmaSet G M) {d : G} (hd : d ∈ kSub 3 M H ⊓ M)
    (hd3 : orderOf d = 3)
    (hs : ((c.φ ⟨d, hd.1⟩ : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)).support.card ≤ 6)
    (hrank : 2 ≤ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer ({d} : Set G))) :
    ∃ Q' F' : Subgroup G,
      O1217.Setting1417 G M Q' (Subgroup.centralizer ({d} : Set G)) F' p := by
  haveI : IsSimpleGroup G := c.choice.cstar.simple
  have hdne : d ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hd3
    norm_num at hd3
  have hCne : Subgroup.centralizer ({d} : Set G) ≠ ⊤ := by
    intro htop
    have hdC : d ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Subgroup.centralizer ({d} : Set G) := by
        rw [htop]
        exact Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.mp hg d (Set.mem_singleton d)).symm
    have hcenter : Subgroup.center G ≠ ⊥ := by
      intro hbot
      rw [hbot] at hdC
      exact hdne (Subgroup.mem_bot.mp hdC)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact hcenter h
    · obtain ⟨a, b, hab⟩ := c.choice.cstar.nonab
      have hb : b ∈ Subgroup.center G := by
        rw [h]
        exact Subgroup.mem_top b
      exact hab (Subgroup.mem_center_iff.mp hb a)
  exact O1217.Setting1417.exists_of_two_le_pRank c.choice.cstar c.choice.maxLocal
    (fun r hr => c.isStronglyPEmbedded hr) hp hCne
    (c.centralizer_not_le hd hd3 hs) hrank

theorem false_of_pPrimeCore_starImg_eq_bot (c : Ctx G M H E Q) {p : ℕ}
    (hp : p ∈ sigmaSet G M) {d : G} (hdM : d ∈ M) (hd3 : orderOf d = 3)
    (hrank : 2 ≤ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer ({d} : Set G)))
    {Q' F' : Subgroup G}
    (s : O1217.Setting1417 G M Q' (Subgroup.centralizer ({d} : Set G)) F' p)
    (hO : CFSG.pPrimeCore 3 ↥(starImg p (Subgroup.centralizer ({d} : Set G))
      (Subgroup.centralizer ({d} : Set G) ⊓ M)) = ⊥) :
    False := by
  have hpp : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  exact s.not_dvd_card_of_pPrimeCore_starImg_eq_bot hO
    (dvd_card_pPrimeCore_inf_centralizer hpp (c.five_le hp) c.mbar hdM hd3 hrank)

private abbrev cent (d : G) : Subgroup G := Subgroup.centralizer ({d} : Set G)

private noncomputable abbrev KMC (M H : Subgroup G) (d : G) : Subgroup G :=
  kSub 3 M H ⊓ M ⊓ cent d

private noncomputable abbrev KCO (M H : Subgroup G) (p : ℕ) (d : G) : Subgroup G :=
  kSub 3 M H ⊓ cent d ⊓ CFSG.Open.relPPrimeCore p (cent d)

private lemma image_inf_centralizer_singleton (c : Ctx G M H E Q) {d : G}
    (hd : d ∈ kSub 3 M H ⊓ M) (hd3 : orderOf d = 3) :
    ((KMC M H d).subgroupOf (kSub 3 M H)).map c.φ =
      a11TwoSetStab 9 10 ⊓ Subgroup.centralizer ({c.φ ⟨d, hd.1⟩}) := by
  have hsub : (KMC M H d).subgroupOf (kSub 3 M H) =
      (M ⊓ cent d).subgroupOf (kSub 3 M H) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨⟨-, hxM⟩, hxC⟩
      exact ⟨hxM, hxC⟩
    · rintro ⟨hxM, hxC⟩
      exact ⟨⟨x.2, hxM⟩, hxC⟩
  rw [hsub, c.map_φ_inf_centralizer_singleton hd.1 hd3]

private lemma image_relPPrimeCore_le_stab (c : Ctx G M H E Q) {p : ℕ} {d : G}
    (hd : d ∈ kSub 3 M H ⊓ M) {Q' F' : Subgroup G}
    (s : O1217.Setting1417 G M Q' (cent d) F' p) :
    ((KCO M H p d).subgroupOf (kSub 3 M H)).map c.φ ≤ a11TwoSetStab 9 10 := by
  intro x hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [Subgroup.mem_subgroupOf] at hy
  exact (c.mem_M_iff y).mp (s.nine.relPPrimeCore_le hy.2)

private lemma centralizer_le_normalizer_image_relPPrimeCore (c : Ctx G M H E Q) {p : ℕ} {d : G}
    (hd : d ∈ kSub 3 M H ⊓ M) (hd3 : orderOf d = 3) {Q' F' : Subgroup G}
    (s : O1217.Setting1417 G M Q' (cent d) F' p) :
    Subgroup.centralizer ({c.φ ⟨d, hd.1⟩} : Set (alternatingGroup (Fin 11))) ≤
      Subgroup.normalizer ((KCO M H p d).subgroupOf (kSub 3 M H) |>.map c.φ :
        Set (alternatingGroup (Fin 11))) := by
  let Cg : Subgroup G := cent d
  let K : Subgroup G := kSub 3 M H
  let O : Subgroup G := CFSG.Open.relPPrimeCore p Cg
  let S : Subgroup G := K ⊓ Cg ⊓ O
  have hnormS : Cg.subgroupOf K ≤
      Subgroup.normalizer ((S.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
    rw [Subgroup.le_normalizer_iff]
    intro y hy z hz
    rw [Subgroup.mem_subgroupOf] at hy hz ⊢
    have hCgnormO : Cg ≤ Subgroup.normalizer (O : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le
          (p := p) Cg)).mp
        (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
          s.qPrime Cg)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Subgroup.mul_mem K (Subgroup.mul_mem K y.2 hz.1.1) (Subgroup.inv_mem K y.2)
    · exact Subgroup.mul_mem Cg (Subgroup.mul_mem Cg hy hz.1.2) (Subgroup.inv_mem Cg hy)
    · exact (Subgroup.mem_normalizer_iff.mp (hCgnormO hy) (z : G)).mp hz.2
  have h1 : (Cg.subgroupOf K).map c.φ ≤
      Subgroup.normalizer ((S.subgroupOf K).map c.φ : Set (alternatingGroup (Fin 11))) :=
    (Subgroup.map_mono hnormS).trans (Subgroup.le_normalizer_map c.φ)
  rw [c.map_φ_centralizer_singleton hd.1 hd3] at h1
  exact h1

private lemma exists_perfect_meets_image_bot (c : Ctx G M H E Q) {p : ℕ} {d : G}
    (hd : d ∈ kSub 3 M H ⊓ M) (hd3 : orderOf d = 3)
    (hs3 : ((c.φ ⟨d, hd.1⟩ : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)).support.card = 3)
    {Q' F' : Subgroup G} (s : O1217.Setting1417 G M Q' (cent d) F' p) :
    ∃ P : Subgroup (alternatingGroup (Fin 11)),
      P ≤ a11TwoSetStab 9 10 ⊓ Subgroup.centralizer ({c.φ ⟨d, hd.1⟩}) ∧
      P ≠ ⊥ ∧ ⁅P, P⁆ = P ∧
      P ⊓ ((KCO M H p d).subgroupOf (kSub 3 M H)).map c.φ = ⊥ := by
  obtain ⟨P, hPle, hPne, hPperf, hPmeet⟩ :=
    exists_perfect_inf_eq_bot_of_card_support_eq_three
      ((c.mem_M_iff ⟨d, hd.1⟩).mp hd.2) (c.orderOf_φ hd3) hs3
  exact ⟨P, hPle, hPne, hPperf,
    hPmeet _ (image_relPPrimeCore_le_stab c hd s)
      (centralizer_le_normalizer_image_relPPrimeCore c hd hd3 s)⟩

private lemma exists_map_derivedSeries_le_image_relPPrimeCore (c : Ctx G M H E Q) {p : ℕ}
    {d : G} (hd : d ∈ kSub 3 M H ⊓ M) {Q' F' : Subgroup G}
    (s : O1217.Setting1417 G M Q' (cent d) F' p)
    (hNsolv : Group.IsSolvable ↥(starImg p (cent d) (cent d ⊓ M))) :
    ∃ n : ℕ,
      (derivedSeries ↥(KMC M H d) n).map
        (c.φ.comp (Subgroup.inclusion
          (show KMC M H d ≤ kSub 3 M H from inf_le_left.trans inf_le_left))) ≤
      ((KCO M H p d).subgroupOf (kSub 3 M H)).map c.φ := by
  let Cg : Subgroup G := cent d
  let K : Subgroup G := kSub 3 M H
  let O : Subgroup G := CFSG.Open.relPPrimeCore p Cg
  let T : Subgroup G := K ⊓ M ⊓ Cg
  let S : Subgroup G := K ⊓ Cg ⊓ O
  have hTK : T ≤ K := by dsimp only [T]; exact inf_le_left.trans inf_le_left
  have hTCg : T ≤ Cg := by dsimp only [T]; exact inf_le_right
  have hTM : T ≤ M := by dsimp only [T]; exact inf_le_left.trans inf_le_right
  let β : ↥T →* StarGroup p Cg :=
    (QuotientGroup.mk' (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore
      (G := ↥Cg) p)).comp (Subgroup.inclusion hTCg)
  have hβrange : β.range ≤ starImg p Cg (Cg ⊓ M) := by
    change ((QuotientGroup.mk' (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore
      (G := ↥Cg) p)).comp (Subgroup.inclusion hTCg)).range ≤ _
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    exact Subgroup.map_mono (Subgroup.comap_mono (le_inf hTCg hTM))
  haveI : Group.IsSolvable ↥(starImg p Cg (Cg ⊓ M)) := hNsolv
  have hβsolv : Group.IsSolvable ↥β.range :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hβrange)
      (Subgroup.inclusion_injective hβrange)
  have hqsolv : Group.IsSolvable (↥T ⧸ β.ker) := by
    haveI : Group.IsSolvable ↥β.range := hβsolv
    exact Group.isSolvable_of_surjective
      (f := (QuotientGroup.quotientKerEquivRange β).symm.toMonoidHom)
      (QuotientGroup.quotientKerEquivRange β).symm.surjective
  obtain ⟨n, hn⟩ :=
    (isSolvable_quotient_iff_exists_derivedSeries_le (G := ↥T) (N := β.ker)).mp hqsolv
  refine ⟨n, ?_⟩
  intro x hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyβ : β y = 1 := MonoidHom.mem_ker.mp (hn hy)
  have hyq : ((Subgroup.inclusion hTCg y : ↥Cg) : StarGroup p Cg) = 1 := by
    simpa [β, QuotientGroup.mk'_apply] using hyβ
  have hycore : (Subgroup.inclusion hTCg y : ↥Cg) ∈
      CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥Cg) p :=
    (QuotientGroup.eq_one_iff _).mp hyq
  have hyO : (y : G) ∈ O := by
    dsimp only [O]
    rw [CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
      s.qPrime Cg]
    exact Subgroup.mem_map_of_mem Cg.subtype hycore
  change c.φ (Subgroup.inclusion hTK y) ∈
    ((KCO M H p d).subgroupOf (kSub 3 M H)).map c.φ
  rw [Subgroup.mem_map]
  exact ⟨Subgroup.inclusion hTK y, by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨⟨hTK y.2, hTCg y.2⟩, hyO⟩, rfl⟩

private lemma not_isSolvable_starImg (c : Ctx G M H E Q) {p : ℕ} {d : G}
    (hd : d ∈ kSub 3 M H ⊓ M) (hd3 : orderOf d = 3)
    (hs3 : ((c.φ ⟨d, hd.1⟩ : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)).support.card = 3)
    {Q' F' : Subgroup G} (s : O1217.Setting1417 G M Q' (cent d) F' p) :
    ¬ Group.IsSolvable ↥(starImg p (cent d) (cent d ⊓ M)) := by
  intro hNsolv
  obtain ⟨P, hPle, hPne, hPperf, hPbot⟩ := exists_perfect_meets_image_bot c hd hd3 hs3 s
  obtain ⟨n, hn⟩ := exists_map_derivedSeries_le_image_relPPrimeCore c hd s hNsolv
  let Cg : Subgroup G := cent d
  let K : Subgroup G := kSub 3 M H
  let T : Subgroup G := K ⊓ M ⊓ Cg
  have hTK : T ≤ K := by dsimp only [T]; exact inf_le_left.trans inf_le_left
  let α : ↥T →* alternatingGroup (Fin 11) := c.φ.comp (Subgroup.inclusion hTK)
  have hαrange : α.range = a11TwoSetStab 9 10 ⊓
      Subgroup.centralizer ({c.φ ⟨d, hd.1⟩}) := by
    change (c.φ.comp (Subgroup.inclusion hTK)).range = _
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    exact image_inf_centralizer_singleton c hd hd3
  have hPmap : P ≤ (derivedSeries ↥T n).map α :=
    le_map_derivedSeries_of_isPerfect α (Subgroup.isPerfect_iff.mpr hPperf)
      (by rw [hαrange]; exact hPle) n
  have hPR : P = ⊥ := by
    have hle : P ≤ P ⊓ ((KCO M H p d).subgroupOf K).map c.φ := le_inf le_rfl (hPmap.trans hn)
    rw [hPbot] at hle
    exact le_bot_iff.mp hle
  exact hPne hPR

theorem pRank_le_one_of_card_support_eq_three (h1 : NineFourTwoSigmaGen)
    (hKF : KFactNineFourStronglyEmbedded) {p : ℕ}
    (hp : p ∈ sigmaSet G M) {d : G} (hd : d ∈ kSub 3 M H ⊓ M) (hd3 : orderOf d = 3)
    (hs : ((c.φ ⟨d, hd.1⟩ : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)).support.card = 3) :
    CFSG.Open.pRank p (M ⊓ Subgroup.centralizer ({d} : Set G)) ≤ 1 := by
  by_contra hle
  have hrank : 2 ≤ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer ({d} : Set G)) := by omega
  obtain ⟨Q', F', s⟩ := c.exists_setting1417 hp hd hd3 (by omega) hrank
  let Cg : Subgroup G := Subgroup.centralizer ({d} : Set G)
  have hns : ¬ Group.IsSolvable ↥(starImg p (Subgroup.centralizer ({d} : Set G))
      (Subgroup.centralizer ({d} : Set G) ⊓ M)) := c.not_isSolvable_starImg hd hd3 hs s
  have hlist : CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup p
      ↥(CFSG.generalizedFitting (StarGroup p Cg)) := by
    rw [s.generalizedFitting_eq_kStar h1]
    exact (s.kStructure h1).2.2.2
  have hO : CFSG.pPrimeCore 3 ↥(starImg p Cg (Cg ⊓ M)) = ⊥ :=
    hKF p (CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1) (c.five_le hp)
      (StarGroup p Cg) hlist (starImg p Cg (Cg ⊓ M)) s.isStronglyPEmbedded_starImg
      (Or.inl hns)
  exact c.false_of_pPrimeCore_starImg_eq_bot hp hd.2 hd3 hrank s hO

end Ctx

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFiveThree
