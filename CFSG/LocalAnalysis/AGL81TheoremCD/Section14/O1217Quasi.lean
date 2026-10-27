module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217Structure
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineTwelveOneSigmaThreeDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.SpTwo
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenKStar
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightFourProof
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ThreeEightFiveReduce

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G] {M Q H F : Subgroup G} {q : ℕ}

private noncomputable def kSubStarMap :
    ↥(AGL81C.kSub q M H) →* StarGroup q H :=
  (QuotientGroup.mk' (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) q)).comp
    (Subgroup.inclusion (AGL81C.kSub_le q M H))

private theorem kSubStarMap_range :
    (kSubStarMap (q := q) (M := M) (H := H)).range = AGL81C.kStar q M H := by
  have hincl_range : (Subgroup.inclusion (AGL81C.kSub_le q M H)).range =
      (AGL81C.kSub q M H).subgroupOf H := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩
  unfold kSubStarMap
  rw [MonoidHom.range_comp, hincl_range]
  rw [AGL81C.kStar_eq_starImg, AGL81C.starImg]

private theorem kSubStarMap_ker (hq : q.Prime) :
    (kSubStarMap (q := q) (M := M) (H := H)).ker =
      (AGL81C.kSub q M H ⊓ CFSG.Open.relPPrimeCore q H).subgroupOf (AGL81C.kSub q M H) := by
  ext x
  rw [MonoidHom.mem_ker]
  have hxO : (Subgroup.inclusion (AGL81C.kSub_le q M H) x : ↥H) ∈
      CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) q ↔
      (x : G) ∈ CFSG.Open.relPPrimeCore q H := by
    constructor
    · intro hx
      rw [show CFSG.Open.relPPrimeCore q H =
          (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) q).map
            H.subtype from
        CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.NineEightFour.relPPrimeCore_eq_map
          hq H]
      exact Subgroup.mem_map_of_mem H.subtype hx
    · intro hx
      rw [show CFSG.Open.relPPrimeCore q H =
          (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) q).map
            H.subtype from
        CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.NineEightFour.relPPrimeCore_eq_map
          hq H] at hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      rw [← show y = Subgroup.inclusion (AGL81C.kSub_le q M H) x from Subtype.ext hyx]
      exact hy
  show QuotientGroup.mk'
      (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) q)
      (Subgroup.inclusion (AGL81C.kSub_le q M H) x) = 1 ↔
    x ∈ (AGL81C.kSub q M H ⊓ CFSG.Open.relPPrimeCore q H).subgroupOf
      (AGL81C.kSub q M H)
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hxO,
    Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

private noncomputable def kSubStarMapToKStar :
    ↥(AGL81C.kSub q M H) →* ↥(AGL81C.kStar q M H) :=
  kSubStarMap.codRestrict (AGL81C.kStar q M H)
    (fun x => by rw [← kSubStarMap_range]; exact ⟨x, rfl⟩)

private theorem kSubStarMapToKStar_ker (hq : q.Prime) :
    (kSubStarMapToKStar (q := q) (M := M) (H := H)).ker =
      (AGL81C.kSub q M H ⊓ CFSG.Open.relPPrimeCore q H).subgroupOf (AGL81C.kSub q M H) := by
  unfold kSubStarMapToKStar
  rw [MonoidHom.ker_codRestrict, kSubStarMap_ker hq]

private theorem inf_relPPrimeCore_subgroupOf_normal (hq : q.Prime) {L : Subgroup G}
    (hLH : L ≤ H) :
    ((L ⊓ CFSG.Open.relPPrimeCore q H).subgroupOf L).Normal := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hOle : CFSG.Open.relPPrimeCore q H ≤ H :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le
      (p := q) H
  have hOnH : ((CFSG.Open.relPPrimeCore q H).subgroupOf H).Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      hq H
  have hHnorm : H ≤ Subgroup.normalizer (CFSG.Open.relPPrimeCore q H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOle).mp hOnH
  have hOK : ((CFSG.Open.relPPrimeCore q H).subgroupOf L).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hLH.trans hHnorm)
  have hNK : (L ⊓ CFSG.Open.relPPrimeCore q H).subgroupOf L =
      (CFSG.Open.relPPrimeCore q H).subgroupOf L := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  rw [hNK]
  exact hOK

private theorem kSubStarMap_surj :
    Function.Surjective (kSubStarMapToKStar (q := q) (M := M) (H := H)) := by
  intro y
  have hy : (y : StarGroup q H) ∈
      (kSubStarMap (q := q) (M := M) (H := H)).range := by
    rw [kSubStarMap_range]; exact y.2
  rw [MonoidHom.mem_range] at hy
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

private theorem kSubStarMap_inf_ne_top (s : Setting1417 G M Q H F q) (h1 : NineFourTwoSigmaGen) :
    (AGL81C.kSub q M H ⊓ CFSG.Open.relPPrimeCore q H).subgroupOf
      (AGL81C.kSub q M H) ≠ ⊤ := by
  classical
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  let g : ↥(AGL81C.kSub q M H) →* ↥(AGL81C.kStar q M H) := kSubStarMapToKStar
  have hgsurj : Function.Surjective g := kSubStarMap_surj
  have hker : g.ker = (AGL81C.kSub q M H ⊓ CFSG.Open.relPPrimeCore q H).subgroupOf
      (AGL81C.kSub q M H) := kSubStarMapToKStar_ker s.qPrime
  haveI : IsSimpleGroup ↥(AGL81C.kStar q M H) := (s.kStructure h1).2.2.2.1
  intro htop
  have hker_top : g.ker = ⊤ := by rw [hker, htop]
  have hrange_bot : g.range = ⊥ := by
    rw [MonoidHom.range_eq_map]
    exact (Subgroup.map_eq_bot_iff (⊤ : Subgroup ↥(AGL81C.kSub q M H))).mpr
      (by rw [hker_top])
  have htopbot : (⊤ : Subgroup ↥(AGL81C.kStar q M H)) = ⊥ := by
    rw [← MonoidHom.range_eq_top.mpr hgsurj, hrange_bot]
  exact (top_ne_bot : (⊤ : Subgroup ↥(AGL81C.kStar q M H)) ≠ ⊥) htopbot

private theorem solvableRadical_map_le_inf (s : Setting1417 G M Q H F q)
    (h1 : NineFourTwoSigmaGen) :
    (CFSG.solvableRadical ↥(AGL81C.kSub q M H)).map (AGL81C.kSub q M H).subtype ≤
      AGL81C.kSub q M H ⊓ CFSG.Open.relPPrimeCore q H := by
  classical
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  let K : Subgroup G := AGL81C.kSub q M H
  let R : Subgroup ↥K := CFSG.solvableRadical ↥K
  let g : ↥K →* ↥(AGL81C.kStar q M H) := kSubStarMapToKStar
  have hgsurj : Function.Surjective g := kSubStarMap_surj
  have hker : g.ker = (AGL81C.kSub q M H ⊓ CFSG.Open.relPPrimeCore q H).subgroupOf
      (AGL81C.kSub q M H) := kSubStarMapToKStar_ker s.qPrime
  haveI : Group.IsPerfect ↥K := s.isPerfect_kSub h1
  have hgperf : Group.IsPerfect ↥(AGL81C.kStar q M H) :=
    Group.IsPerfect.ofSurjective (f := g) hgsurj
  haveI : Group.IsPerfect ↥(AGL81C.kStar q M H) := hgperf
  haveI : IsSimpleGroup ↥(AGL81C.kStar q M H) := (s.kStructure h1).2.2.2.1
  have hRn : R.Normal := CFSG.ABGLocalTools.solvableRadical_normal
  have hDnormal : (R.map g).Normal := hRn.map g hgsurj
  haveI : Group.IsSolvable ↥R := CFSG.ABGLocalTools.solvableRadical_isSolvable
  have hDsolv : Group.IsSolvable ↥(R.map g) :=
    Group.isSolvable_of_surjective (f := g.subgroupMap R) (g.subgroupMap_surjective R)
  haveI : (R.map g).Normal := hDnormal
  have hDbot : R.map g = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.map g) with h | h
    · exact h
    · exfalso
      haveI : Group.IsSolvable ↥(⊤ : Subgroup ↥(AGL81C.kStar q M H)) := by
        rw [← h]
        exact hDsolv
      have hsolv : Group.IsSolvable ↥(AGL81C.kStar q M H) :=
        Group.isSolvable_of_isSolvable_injective
          (f := (Subgroup.topEquiv (G := ↥(AGL81C.kStar q M H))).symm.toMonoidHom)
          (Subgroup.topEquiv (G := ↥(AGL81C.kStar q M H))).symm.injective
      exact Group.IsPerfect.not_isSolvable ↥(AGL81C.kStar q M H) hsolv
  have hRle : R ≤ (K ⊓ CFSG.Open.relPPrimeCore q H).subgroupOf K := by
    intro z hz
    have hzD : g z ∈ R.map g := Subgroup.mem_map_of_mem g hz
    rw [hDbot, Subgroup.mem_bot] at hzD
    have hzker : z ∈ g.ker := MonoidHom.mem_ker.mpr hzD
    rw [hker] at hzker
    exact hzker
  calc R.map K.subtype ≤ ((K ⊓ CFSG.Open.relPPrimeCore q H).subgroupOf K).map K.subtype :=
        Subgroup.map_mono hRle
    _ = K ⊓ CFSG.Open.relPPrimeCore q H := Subgroup.map_subgroupOf_eq_of_le inf_le_left

private theorem inf_le_solvableRadical_map (s : Setting1417 G M Q H F q)
    (h1 : NineFourTwoSigmaGen)
    (hA6 : Nonempty (↥(AGL81C.kSub q M H) ⧸
      CFSG.solvableRadical ↥(AGL81C.kSub q M H) ≃* alternatingGroup (Fin 6))) :
    (AGL81C.kSub q M H ⊓ CFSG.Open.relPPrimeCore q H).subgroupOf (AGL81C.kSub q M H) ≤
      CFSG.solvableRadical ↥(AGL81C.kSub q M H) := by
  classical
  let K : Subgroup G := AGL81C.kSub q M H
  let R : Subgroup ↥K := CFSG.solvableRadical ↥K
  let N : Subgroup ↥K := (K ⊓ CFSG.Open.relPPrimeCore q H).subgroupOf K
  have hNn : N.Normal := inf_relPPrimeCore_subgroupOf_normal s.qPrime (AGL81C.kSub_le q M H)
  have hRle : R ≤ N := by
    intro z hz
    have hzG : (z : G) ∈ R.map K.subtype := Subgroup.mem_map_of_mem K.subtype hz
    exact solvableRadical_map_le_inf s h1 hzG
  have hNproper : N ≠ ⊤ := kSubStarMap_inf_ne_top s h1
  obtain ⟨eA⟩ := hA6
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup (↥K ⧸ R) := eA.isSimpleGroup
  let qπ : ↥K →* (↥K ⧸ R) := QuotientGroup.mk' R
  let D : Subgroup (↥K ⧸ R) := N.map qπ
  have hDnormal : D.Normal := hNn.map qπ (QuotientGroup.mk'_surjective R)
  haveI : D.Normal := hDnormal
  have hDbot : D = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal D with h | h
    · exact h
    · exfalso
      have hcomap : (N.map qπ).comap qπ = ⊤ := by
        have := congrArg (fun S : Subgroup (↥K ⧸ R) => S.comap qπ) h
        simpa using this
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hRle] at hcomap
      exact hNproper hcomap
  have hNle : N ≤ R := by
    have hmapbot : N.map qπ = ⊥ := hDbot
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmapbot
    exact hmapbot
  exact hNle

private theorem solvableRadical_map_eq_inf (s : Setting1417 G M Q H F q)
    (h1 : NineFourTwoSigmaGen)
    (hA6 : Nonempty (↥(AGL81C.kSub q M H) ⧸
      CFSG.solvableRadical ↥(AGL81C.kSub q M H) ≃* alternatingGroup (Fin 6))) :
    (CFSG.solvableRadical ↥(AGL81C.kSub q M H)).map (AGL81C.kSub q M H).subtype =
      AGL81C.kSub q M H ⊓ CFSG.Open.relPPrimeCore q H := by
  let K : Subgroup G := AGL81C.kSub q M H
  let R : Subgroup ↥K := CFSG.solvableRadical ↥K
  let N : Subgroup ↥K := (K ⊓ CFSG.Open.relPPrimeCore q H).subgroupOf K
  have hRle : R ≤ N := by
    intro z hz
    have hzG : (z : G) ∈ R.map K.subtype := Subgroup.mem_map_of_mem K.subtype hz
    exact solvableRadical_map_le_inf s h1 hzG
  have hNle : N ≤ R := inf_le_solvableRadical_map s h1 hA6
  have hEq : R = N := le_antisymm hRle hNle
  change R.map K.subtype = K ⊓ CFSG.Open.relPPrimeCore q H
  rw [hEq]
  exact Subgroup.map_subgroupOf_eq_of_le inf_le_left

private theorem card_inf_subgroupOf :
    Nat.card ((AGL81C.kSub q M H ⊓ CFSG.Open.relPPrimeCore q H).subgroupOf
      (AGL81C.kSub q M H)) =
      Nat.card ↥(AGL81C.kSub q M H ⊓ CFSG.Open.relPPrimeCore q H) :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

private theorem coprime_six_inf_subgroupOf (s : Setting1417 G M Q H F q) (hq3 : q = 3) :
    Nat.Coprime (Nat.card ((AGL81C.kSub q M H ⊓ CFSG.Open.relPPrimeCore q H).subgroupOf
      (AGL81C.kSub q M H))) 6 := by
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  set K : Subgroup G := AGL81C.kSub q M H
  set O : Subgroup G := CFSG.Open.relPPrimeCore q H
  have hoddN : Odd (Nat.card ↥(K ⊓ O)) :=
    Odd.of_dvd_nat s.odd_card_relPPrimeCore (Subgroup.card_dvd_of_le inf_le_right)
  have hcopO : Nat.Coprime q (Nat.card O) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
      s.qPrime H
  have hnot3O : ¬ 3 ∣ Nat.card O := by
    rw [hq3] at hcopO
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcopO
  have hnot3N : ¬ 3 ∣ Nat.card ↥(K ⊓ O) :=
    fun hd => hnot3O (hd.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hcard := card_inf_subgroupOf (q := q) (M := M) (H := H)
  rw [hcard]
  have h2 : Nat.Coprime (Nat.card ↥(K ⊓ O)) 2 := by
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hoddN.not_two_dvd_nat
  have h3 : Nat.Coprime (Nat.card ↥(K ⊓ O)) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hnot3N).symm
  rw [show 6 = 2 * 3 by norm_num]
  exact h2.mul_right h3

private theorem pRank_inf_subgroupOf_le_three (s : Setting1417 G M Q H F q) {r : ℕ}
    (hr : r.Prime) :
    CFSG.Open.pRank r ((AGL81C.kSub q M H ⊓ CFSG.Open.relPPrimeCore q H).subgroupOf
      (AGL81C.kSub q M H)) ≤ 3 := by
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  set K : Subgroup G := AGL81C.kSub q M H
  set O : Subgroup G := CFSG.Open.relPPrimeCore q H
  have hNK : (K ⊓ O).subgroupOf K = O.subgroupOf K := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  rw [hNK]
  calc CFSG.Open.pRank r (O.subgroupOf K)
      ≤ CFSG.Open.pRank r ((O.subgroupOf K).map K.subtype) :=
        CFSG.SectionRank.pRank_le_map hr.one_lt K.subtype K.subtype_injective _
    _ = CFSG.Open.pRank r (K ⊓ O) := by
        rw [Subgroup.subgroupOf_map_subtype, inf_comm]
    _ ≤ CFSG.Open.pRank r O := CFSG.SectionRank.pRank_mono hr.one_lt inf_le_right
    _ ≤ 3 := s.pRank_relPPrimeCore_le_three hr

private theorem isQuasisimple_of_altSix (s : Setting1417 G M Q H F q)
    (h1 : NineFourTwoSigmaGen) (hA6 : KFactAltSixCoreCentral)
    (hA6case : q = 3 ∧ Nonempty (↥(AGL81C.kSub q M H) ⧸
      CFSG.solvableRadical ↥(AGL81C.kSub q M H) ≃* alternatingGroup (Fin 6))) :
    CFSG.IsQuasisimple ↥(AGL81C.kSub q M H) := by
  classical
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  set K : Subgroup G := AGL81C.kSub q M H
  let R : Subgroup ↥K := CFSG.solvableRadical ↥K
  let N : Subgroup ↥K := (K ⊓ CFSG.Open.relPPrimeCore q H).subgroupOf K
  obtain ⟨hq3, hA6e⟩ := hA6case
  have hNnormal : N.Normal := inf_relPPrimeCore_subgroupOf_normal s.qPrime (AGL81C.kSub_le q M H)
  have hReq : R = N := by
    have hmap : R.map K.subtype = K ⊓ CFSG.Open.relPPrimeCore q H :=
      solvableRadical_map_eq_inf s h1 hA6e
    have hsub : (R.map K.subtype).subgroupOf K = R := by
      apply Subgroup.map_injective K.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le R)]
    calc R = (R.map K.subtype).subgroupOf K := hsub.symm
      _ = (K ⊓ CFSG.Open.relPPrimeCore q H).subgroupOf K := by rw [hmap]
      _ = N := rfl
  have hNsolv : Group.IsSolvable ↥N := by
    rw [← hReq]
    exact CFSG.ABGLocalTools.solvableRadical_isSolvable
  have hNcop : Nat.Coprime (Nat.card N) 6 := coprime_six_inf_subgroupOf s hq3
  have hNrank : ∀ r : ℕ, r.Prime → CFSG.Open.pRank r N ≤ 3 := by
    intro r hr
    exact pRank_inf_subgroupOf_le_three s hr
  have hNleCenter : N ≤ Subgroup.center ↥K :=
    hA6 K (s.isPerfect_kSub h1) N hNnormal hNsolv hNcop
      ⟨(QuotientGroup.quotientMulEquivOfEq hReq.symm).trans (Classical.choice hA6e)⟩ hNrank
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hA6q : CFSG.IsQuasisimple (alternatingGroup (Fin 6)) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.isQuasisimple_alternatingGroup_six
  let eN : (↥K ⧸ N) ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq hReq.symm).trans (Classical.choice hA6e)
  have hquotq : CFSG.IsQuasisimple (↥K ⧸ N) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eN.symm hA6q
  exact (CFSG.LocalCores.isQuasisimple_iff_of_surjective (s.isPerfect_kSub h1)
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    (by rw [QuotientGroup.ker_mk']; exact hNleCenter)).mpr hquotq

private theorem kStar_center_eq_bot (s : Setting1417 G M Q H F q)
    (h1 : NineFourTwoSigmaGen) :
    Subgroup.center ↥(AGL81C.kStar q M H) = ⊥ := by
  classical
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  let K : Subgroup G := AGL81C.kSub q M H
  let g : ↥K →* ↥(AGL81C.kStar q M H) := kSubStarMapToKStar
  have hgsurj : Function.Surjective g := kSubStarMap_surj
  haveI : Group.IsPerfect ↥K := s.isPerfect_kSub h1
  haveI : Group.IsPerfect ↥(AGL81C.kStar q M H) :=
    Group.IsPerfect.ofSurjective (f := g) hgsurj
  haveI : IsSimpleGroup ↥(AGL81C.kStar q M H) := (s.kStructure h1).2.2.2.1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.center ↥(AGL81C.kStar q M H)) with h | h
  · exact h
  · exfalso
    haveI : IsMulCommutative ↥(AGL81C.kStar q M H) := ⟨⟨fun a b => by
      have hb : b ∈ Subgroup.center ↥(AGL81C.kStar q M H) := h ▸ Subgroup.mem_top b
      exact Subgroup.mem_center_iff.mp hb a⟩⟩
    haveI : Subsingleton ↥(AGL81C.kStar q M H) :=
      Group.IsPerfect.subsingleton_of_isMulCommutative
    exact (not_subsingleton_iff_nontrivial (α := ↥(AGL81C.kStar q M H))).mpr
      inferInstance inferInstance

private theorem center_le_inf_subgroupOf (s : Setting1417 G M Q H F q)
    (h1 : NineFourTwoSigmaGen) :
    Subgroup.center ↥(AGL81C.kSub q M H) ≤
      (AGL81C.kSub q M H ⊓ CFSG.Open.relPPrimeCore q H).subgroupOf
        (AGL81C.kSub q M H) := by
  classical
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  let K : Subgroup G := AGL81C.kSub q M H
  let g : ↥K →* ↥(AGL81C.kStar q M H) := kSubStarMapToKStar
  have hgsurj : Function.Surjective g := kSubStarMap_surj
  have hker : g.ker = (AGL81C.kSub q M H ⊓ CFSG.Open.relPPrimeCore q H).subgroupOf
      (AGL81C.kSub q M H) := kSubStarMapToKStar_ker s.qPrime
  have hcenter := kStar_center_eq_bot s h1
  intro z hz
  have hgz : g z ∈ Subgroup.center ↥(AGL81C.kStar q M H) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨w, rfl⟩ := hgsurj y
    simpa only [map_mul] using congrArg g (Subgroup.mem_center_iff.mp hz w)
  have hg1 : g z = 1 := by
    rw [hcenter] at hgz
    simpa using hgz
  have hzker : z ∈ g.ker := MonoidHom.mem_ker.mpr hg1
  rwa [hker] at hzker

private theorem inf_subgroupOf_le_center (s : Setting1417 G M Q H F q)
    (h1 : NineFourTwoSigmaGen) (hq : CFSG.IsQuasisimple ↥(AGL81C.kSub q M H)) :
    (AGL81C.kSub q M H ⊓ CFSG.Open.relPPrimeCore q H).subgroupOf
        (AGL81C.kSub q M H) ≤ Subgroup.center ↥(AGL81C.kSub q M H) := by
  have hNn : ((AGL81C.kSub q M H ⊓ CFSG.Open.relPPrimeCore q H).subgroupOf
      (AGL81C.kSub q M H)).Normal :=
    inf_relPPrimeCore_subgroupOf_normal s.qPrime (AGL81C.kSub_le q M H)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hNn with htop | hcenter
  · exact absurd htop (kSubStarMap_inf_ne_top s h1)
  · exact hcenter

private theorem isQuasisimple_of_twoPrime (s : Setting1417 G M Q H F q)
    {L : Subgroup G} (hTwo : AGL81C.IsTwoPrimeComponentIn L H) :
    CFSG.IsQuasisimple ↥L := by
  classical
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLH : L ≤ H := hTwo.1
  have hLsn : (L.subgroupOf H).IsSubnormal := hTwo.2.1
  have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := hTwo.2.2.1
  have hcoreH : CFSG.pCore 2 ↥H = ⊥ := by
    have hmap : (CFSG.pCore 2 ↥H).map H.subtype = ⊥ := s.pCoreOf_two_eq_bot
    exact Subgroup.map_injective H.subtype_injective
      (by rw [hmap, Subgroup.map_bot])
  have hT : CFSG.Open.IsSubnormal (L.subgroupOf H) ⊤ :=
    CFSG.Open.IsSubnormal.top_iff.mpr hLsn
  have hcoreSub : CFSG.pCore 2 ↥(L.subgroupOf H) = ⊥ :=
    CFSG.AGLEmbedding.CZeroLift.pCore_eq_bot_of_isSubnormal hT hcoreH
  have hcoreL : CFSG.pCore 2 ↥L = ⊥ := by
    have hmap := CFSG.pCore_map_iso 2 (Subgroup.subgroupOfEquivOfLe hLH :
      ↥(L.subgroupOf H) ≃* ↥L)
    rw [hcoreSub, Subgroup.map_bot] at hmap
    exact hmap.symm
  let e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hcoreL).trans QuotientGroup.quotientBot
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq

theorem Setting1417.isQuasisimple_kSub (s : Setting1417 G M Q H F q)
    (h1 : NineFourTwoSigmaGen) (h2 : NineTwelveOneSigmaStrong) (h3 : NineTwelveOneSigmaThree)
    (hA6 : KFactAltSixCoreCentral) :
    CFSG.IsQuasisimple ↥(AGL81C.kSub q M H) := by
  classical
  obtain ⟨L, hL, hLM, hk⟩ := s.exists_eq_kSub h1
  rcases s.nineTwelveOne h2 h3 hL hLM with hTwo | hAlt
  · rw [← hk] at hTwo
    exact isQuasisimple_of_twoPrime s hTwo
  · rw [← hk] at hAlt
    exact isQuasisimple_of_altSix s h1 hA6 hAlt

theorem Setting1417.map_center_kSub_of_isQuasisimple (s : Setting1417 G M Q H F q)
    (h1 : NineFourTwoSigmaGen) (hK : CFSG.IsQuasisimple ↥(AGL81C.kSub q M H)) :
    (Subgroup.center ↥(AGL81C.kSub q M H)).map (AGL81C.kSub q M H).subtype =
      AGL81C.kSub q M H ⊓ CFSG.Open.relPPrimeCore q H := by
  let K : Subgroup G := AGL81C.kSub q M H
  let O : Subgroup G := CFSG.Open.relPPrimeCore q H
  have hle : Subgroup.center ↥K ≤ (K ⊓ O).subgroupOf K :=
    center_le_inf_subgroupOf s h1
  have hge : (K ⊓ O).subgroupOf K ≤ Subgroup.center ↥K :=
    inf_subgroupOf_le_center s h1 hK
  have hcenter : Subgroup.center ↥K = (K ⊓ O).subgroupOf K := le_antisymm hle hge
  calc (Subgroup.center ↥K).map K.subtype = ((K ⊓ O).subgroupOf K).map K.subtype := by
        rw [hcenter]
    _ = K ⊓ O := Subgroup.map_subgroupOf_eq_of_le inf_le_left

theorem Setting1417.map_center_kSub (s : Setting1417 G M Q H F q)
    (h1 : NineFourTwoSigmaGen) (h2 : NineTwelveOneSigmaStrong) (h3 : NineTwelveOneSigmaThree)
    (hA6 : KFactAltSixCoreCentral) :
    (Subgroup.center ↥(AGL81C.kSub q M H)).map (AGL81C.kSub q M H).subtype =
      AGL81C.kSub q M H ⊓ CFSG.Open.relPPrimeCore q H :=
  s.map_center_kSub_of_isQuasisimple h1 (s.isQuasisimple_kSub h1 h2 h3 hA6)

theorem Setting1417.odd_card_center_kSub (s : Setting1417 G M Q H F q)
    (h1 : NineFourTwoSigmaGen) (h2 : NineTwelveOneSigmaStrong) (h3 : NineTwelveOneSigmaThree)
    (hA6 : KFactAltSixCoreCentral) :
    Odd (Nat.card (Subgroup.center ↥(AGL81C.kSub q M H))) := by
  let K : Subgroup G := AGL81C.kSub q M H
  let O : Subgroup G := CFSG.Open.relPPrimeCore q H
  have hcard : Nat.card (Subgroup.center ↥K) = Nat.card ↥(K ⊓ O) := by
    calc Nat.card (Subgroup.center ↥K) = Nat.card ↥((Subgroup.center ↥K).map K.subtype) :=
          (Subgroup.card_map_of_injective K.subtype_injective).symm
      _ = Nat.card ↥(K ⊓ O) := by rw [s.map_center_kSub h1 h2 h3 hA6]
  rw [hcard]
  exact Odd.of_dvd_nat s.odd_card_relPPrimeCore (Subgroup.card_dvd_of_le inf_le_right)

theorem Setting1417.not_dvd_card_center_kSub (s : Setting1417 G M Q H F q)
    (h1 : NineFourTwoSigmaGen) (h2 : NineTwelveOneSigmaStrong) (h3 : NineTwelveOneSigmaThree)
    (hA6 : KFactAltSixCoreCentral) :
    ¬ q ∣ Nat.card (Subgroup.center ↥(AGL81C.kSub q M H)) := by
  let K : Subgroup G := AGL81C.kSub q M H
  let O : Subgroup G := CFSG.Open.relPPrimeCore q H
  have hcard : Nat.card (Subgroup.center ↥K) = Nat.card ↥(K ⊓ O) := by
    calc Nat.card (Subgroup.center ↥K) = Nat.card ↥((Subgroup.center ↥K).map K.subtype) :=
          (Subgroup.card_map_of_injective K.subtype_injective).symm
      _ = Nat.card ↥(K ⊓ O) := by rw [s.map_center_kSub h1 h2 h3 hA6]
  rw [hcard]
  have hcopO : Nat.Coprime q (Nat.card O) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
      s.qPrime H
  have hnotO : ¬ q ∣ Nat.card O := (Nat.Prime.coprime_iff_not_dvd s.qPrime).mp hcopO
  exact fun hd => hnotO (hd.trans (Subgroup.card_dvd_of_le inf_le_right))

theorem Setting1417.nineFourListGroup_quot_center_of_isQuasisimple (s : Setting1417 G M Q H F q)
    (h1 : NineFourTwoSigmaGen) (hK : CFSG.IsQuasisimple ↥(AGL81C.kSub q M H)) :
    CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup q
      (↥(AGL81C.kSub q M H) ⧸ Subgroup.center ↥(AGL81C.kSub q M H)) := by
  classical
  let K : Subgroup G := AGL81C.kSub q M H
  let O : Subgroup G := CFSG.Open.relPPrimeCore q H
  let N : Subgroup ↥K := (K ⊓ O).subgroupOf K
  have hNn : N.Normal := inf_relPPrimeCore_subgroupOf_normal s.qPrime (AGL81C.kSub_le q M H)
  haveI : N.Normal := hNn
  have hcenter : Subgroup.center ↥K = N := by
    apply Subgroup.map_injective K.subtype_injective
    exact (s.map_center_kSub_of_isQuasisimple h1 hK).trans
      (Subgroup.map_subgroupOf_eq_of_le inf_le_left).symm
  have hlist : CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup q
      ↥(AGL81C.kStar q M H) := (s.kStructure h1).2.2.2
  let e1 : (↥K ⧸ Subgroup.center ↥K) ≃* (↥K ⧸ N) :=
    QuotientGroup.quotientMulEquivOfEq hcenter
  let e2 : (↥K ⧸ N) ≃* ↥(AGL81C.kStar q M H) :=
    (QuotientGroup.quotientMulEquivOfEq (kSubStarMap_ker s.qPrime).symm).trans
      ((QuotientGroup.quotientKerEquivRange kSubStarMap).trans
        (MulEquiv.subgroupCongr kSubStarMap_range))
  exact CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup.of_mulEquiv hlist
    (e1.trans e2).symm

theorem Setting1417.nineFourListGroup_quot_center (s : Setting1417 G M Q H F q)
    (h1 : NineFourTwoSigmaGen) (h2 : NineTwelveOneSigmaStrong) (h3 : NineTwelveOneSigmaThree)
    (hA6 : KFactAltSixCoreCentral) :
    CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup q
      (↥(AGL81C.kSub q M H) ⧸ Subgroup.center ↥(AGL81C.kSub q M H)) :=
  s.nineFourListGroup_quot_center_of_isQuasisimple h1 (s.isQuasisimple_kSub h1 h2 h3 hA6)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217
