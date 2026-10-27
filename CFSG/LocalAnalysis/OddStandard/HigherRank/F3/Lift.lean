module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Transfer
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Center
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitSchur
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Tools
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP1Section18
public import CFSG.ClassicalInvolution.Asc77.WP1Section6
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Ord
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Std
public import CFSG.ClassicalInvolution.Q3.Step
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Steinberg.CentralExt.PSL2Multiplier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogSchreierCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesC
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Props
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1FourGroup
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36SporMult
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModels
public import CFSG.LocalAnalysis.ComponentClassification.OddSelector
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdFamilies
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.Monster.B.TwoA.Base.FourNorm
public import CFSG.Monster.SteinbergMY443SimpleIsomorphism
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import CFSG.Walter.J1
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.Parabolic2CheckB
public import CFSG.YGroups.Y443.Native.Parabolic2CheckW
public import Certificates.Certificate10025
public import Certificates.Certificate7233Base
public import Certificates.Certificate8171
public import Certificates.Kernel.J4Count.FixC
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase
public import Certificates.Kernel.SporSch.J4S.NoCP

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.Open CFSG.ComponentClassification.HarrisLit
open scoped commutatorElement

theorem classBShape_of_surjective_odd {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) (hker : ¬ 2 ∣ Nat.card f.ker)
    (h : ClassBShape B) : ClassBShape A := by
  obtain ⟨τ, n, hm, hs⟩ := h
  obtain ⟨eZ⟩ :=
    ComponentClassification.GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective f hf hker
  exact ⟨τ, n, ComponentClassification.GSThmB.OddQuot.lieModel_of_equiv eZ.symm hm, hs⟩

theorem partialCentre_iff_of_surjective_odd {A B : Type} [Group A] [Group B] [Finite A]
    [Finite B] (f : A →* B) (hf : Function.Surjective f) (hker : ¬ 2 ∣ Nat.card f.ker) :
    PartialCentre A ↔ PartialCentre B := by
  obtain ⟨eZ⟩ :=
    ComponentClassification.GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective f hf hker
  have hM : Nat.card (Open.griessHopfMultiplier (A ⧸ Open.fusionZStar A)) =
      Nat.card (Open.griessHopfMultiplier (B ⧸ Open.fusionZStar B)) :=
    Nat.card_congr (LieType.Steinberg.CentralExt.griessHopfMultiplierCongr eZ).toEquiv
  have hcard : Nat.card ↥(Open.fusionZStar A) = Nat.card f.ker * Nat.card ↥(Open.fusionZStar B) :=
    card_fusionZStar_of_surjective f hf hker
  have hk0 : Nat.card f.ker ≠ 0 := Nat.card_pos.ne'
  have hB0 : Nat.card ↥(Open.fusionZStar B) ≠ 0 := Nat.card_pos.ne'
  have hodd : Nat.factorization (Nat.card f.ker) 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hker
  have hZ : ordProj[2] (Nat.card ↥(Open.fusionZStar A)) =
      ordProj[2] (Nat.card ↥(Open.fusionZStar B)) := by
    rw [hcard, Nat.factorization_mul hk0 hB0, Finsupp.add_apply, hodd, zero_add]
  unfold PartialCentre
  rw [hZ, hM]

theorem isMTypeSchur_of_surjective_odd {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) (hker : ¬ 2 ∣ Nat.card f.ker)
    (hA : Group.IsPerfect A) {p : ℕ} (hB : IsMTypeSchur p B) : IsMTypeSchur p A := by
  obtain ⟨e⟩ :=
    ComponentClassification.GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective f hf hker
  rcases hB with hB1 | ⟨hp3, ⟨e'⟩⟩
  · have h2q : IsTwoQuasisimple A :=
      ⟨hA, LocalCores.isQuasisimple_of_mulEquiv e.symm hB1.1.2⟩
    exact T1.isMTypeSchur_of_bar_equiv (A := B) (B := A) (.inl hB1) h2q e.symm
  · exact .inr ⟨hp3, ⟨e.trans e'⟩⟩

theorem comap_center_eq_of_central_cover {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) (hk : f.ker ≤ center A) (hA : Group.IsPerfect A) :
    (center B).comap f = center A := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_comap] at hx
    have hcomm : ∀ y : A, ⁅x, y⁆ ∈ f.ker := by
      intro y
      rw [MonoidHom.mem_ker]
      have h1 : f y * f x = f x * f y := Subgroup.mem_center_iff.mp hx (f y)
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact h1.symm
    have hcenter : QuotientGroup.mk' (center A) x ∈ center (A ⧸ center A) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center A) q
      have h1 : ⁅QuotientGroup.mk' (center A) x, QuotientGroup.mk' (center A) y⁆ = 1 := by
        rw [← map_commutatorElement, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hk (hcomm y)
      exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
    haveI : Group.IsPerfect A := hA
    have hbot := Group.IsPerfect.center_quotient_center_eq_bot A
    have hx1 : QuotientGroup.mk' (center A) x = 1 := by
      rw [← Subgroup.mem_bot, ← hbot]
      exact hcenter
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
  · intro hx
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro b
    obtain ⟨a, rfl⟩ := hf b
    have h1 := Subgroup.mem_center_iff.mp hx a
    rw [← map_mul, ← map_mul, h1]

theorem nonempty_quotient_center_equiv_of_central_cover {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f) (hk : f.ker ≤ center A)
    (hA : Group.IsPerfect A) : Nonempty (A ⧸ center A ≃* B ⧸ center B) := by
  set φ := (QuotientGroup.mk' (center B)).comp f with hφ
  have hφs : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hf
  have hφk : center A = φ.ker := by
    rw [hφ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      comap_center_eq_of_central_cover f hf hk hA]
  exact ⟨QuotientGroup.liftEquiv _ hφs hφk⟩

private theorem card_comap_of_surjective {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) (H : Subgroup B) :
    Nat.card ↥(H.comap f) = Nat.card f.ker * Nat.card ↥H := by
  have h1 := Subgroup.card_mul_index (H.comap f)
  rw [Subgroup.index_comap_of_surjective _ hf] at h1
  have h2 := Subgroup.card_mul_index H
  have h3 := Subgroup.card_ker_mul_card_of_surjective (f := f) hf
  have hi : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hmul : Nat.card ↥(H.comap f) * H.index = Nat.card f.ker * Nat.card ↥H * H.index := by
    rw [h1, ← h3, ← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi) hmul

theorem card_center_of_central_cover {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) (hk : f.ker ≤ center A)
    (hA : Group.IsPerfect A) :
    Nat.card ↥(center A) = Nat.card f.ker * Nat.card ↥(center B) := by
  rw [← comap_center_eq_of_central_cover f hf hk hA]
  exact card_comap_of_surjective f hf (center B)

theorem isQuasisimple_of_central_cover {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f) (hk : f.ker ≤ center A)
    (hA : Group.IsPerfect A) (hB : IsQuasisimple B) : IsQuasisimple A := by
  obtain ⟨e⟩ := nonempty_quotient_center_equiv_of_central_cover f hf hk hA
  refine ⟨hA, ?_, ?_⟩
  · haveI := hB.2.1
    exact e.isSimpleGroup
  · obtain ⟨a, b, hab⟩ := hB.2.2
    exact ⟨e.symm a, e.symm b, fun h => hab (by
      simpa using congrArg (fun z => e z) h)⟩

theorem not_two_dvd_card_ker_of_full_cover {A B : Type} [Group A] [Group B] [Finite A]
    [Finite B] (f : A →* B) (hf : Function.Surjective f) (hk : f.ker ≤ center A)
    (hA : Group.IsPerfect A) (hB : IsQuasisimple B) (hO : pPrimeCore 2 B = ⊥)
    (hP : ¬ PartialCentre B) : ¬ 2 ∣ Nat.card f.ker := by
  have hAq : IsQuasisimple A := isQuasisimple_of_central_cover f hf hk hA hB
  obtain ⟨e⟩ := nonempty_quotient_center_equiv_of_central_cover f hf hk hA
  have hM : Nat.card (Open.griessHopfMultiplier (A ⧸ center A)) =
      Nat.card (Open.griessHopfMultiplier (B ⧸ center B)) :=
    Nat.card_congr (LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).toEquiv
  have hcard : Nat.card ↥(center A) = Nat.card f.ker * Nat.card ↥(center B) :=
    card_center_of_central_cover f hf hk hA
  have hZ : Open.fusionZStar B = center B := fusionZStar_eq_center_of_pPrimeCore_eq_bot hO
  have h1 := Center47.card_center_dvd_card_griessHopfMultiplier hAq
  haveI : Finite (Open.griessHopfMultiplier (B ⧸ center B)) := by
    haveI : Group.IsPerfect B := hB.1
    haveI : Group.IsPerfect (B ⧸ center B) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center B))
        (QuotientGroup.mk'_surjective _)
    haveI : Finite (RankThree.PerfectCover.hopfMultiplier (B ⧸ center B)) :=
      RankThree.PerfectCover.finite_hopfMultiplier inferInstance
    exact Finite.of_equiv (RankThree.PerfectCover.hopfMultiplier (B ⧸ center B))
      (RankThree.PerfectCover.hopfMultiplierEquivGriess (B ⧸ center B)).symm.toEquiv
  haveI : Nonempty (Open.griessHopfMultiplier (B ⧸ center B)) := ⟨1⟩
  haveI : Finite (Open.griessHopfMultiplier (A ⧸ center A)) :=
    Finite.of_equiv (Open.griessHopfMultiplier (B ⧸ center B))
      (LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).symm.toEquiv
  haveI : Nonempty (Open.griessHopfMultiplier (A ⧸ center A)) := ⟨1⟩
  have h1v : Nat.factorization (Nat.card ↥(center A)) 2 ≤
      Nat.factorization (Nat.card (Open.griessHopfMultiplier (A ⧸ center A))) 2 :=
    (Nat.factorization_le_iff_dvd (d := Nat.card ↥(center A))
      (n := Nat.card (Open.griessHopfMultiplier (A ⧸ center A)))
      (Nat.card_pos.ne') (Nat.card_pos.ne')).mpr h1 2
  have hZc : Nat.card ↥(Open.fusionZStar B) = Nat.card ↥(center B) :=
    congrArg (fun H : Subgroup B => Nat.card ↥H) hZ
  have hMc : Nat.card (Open.griessHopfMultiplier (B ⧸ Open.fusionZStar B)) =
      Nat.card (Open.griessHopfMultiplier (B ⧸ center B)) :=
    Nat.card_congr (LieType.Steinberg.CentralExt.griessHopfMultiplierCongr
      (QuotientGroup.quotientMulEquivOfEq hZ)).toEquiv
  have hP' : Nat.factorization (Nat.card (Open.griessHopfMultiplier (B ⧸ center B))) 2 ≤
      Nat.factorization (Nat.card ↥(center B)) 2 := by
    unfold PartialCentre at hP
    have h := not_lt.mp hP
    rw [hZc, hMc] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp h
  have hZA : Nat.factorization (Nat.card ↥(center A)) 2 =
      Nat.factorization (Nat.card f.ker) 2 + Nat.factorization (Nat.card ↥(center B)) 2 := by
    rw [hcard, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'), Finsupp.add_apply]
  have hMv : Nat.factorization (Nat.card (Open.griessHopfMultiplier (A ⧸ center A))) 2 =
      Nat.factorization (Nat.card (Open.griessHopfMultiplier (B ⧸ center B))) 2 :=
    congrArg (fun n => Nat.factorization n 2) hM
  have hker0 : Nat.factorization (Nat.card f.ker) 2 = 0 := by
    have hle : Nat.factorization (Nat.card f.ker) 2 +
        Nat.factorization (Nat.card ↥(center B)) 2 ≤
        Nat.factorization (Nat.card ↥(center B)) 2 := by
      calc Nat.factorization (Nat.card f.ker) 2 +
            Nat.factorization (Nat.card ↥(center B)) 2
          = Nat.factorization (Nat.card ↥(center A)) 2 := hZA.symm
        _ ≤ Nat.factorization
            (Nat.card (Open.griessHopfMultiplier (A ⧸ center A))) 2 := h1v
        _ = Nat.factorization
            (Nat.card (Open.griessHopfMultiplier (B ⧸ center B))) 2 := hMv
        _ ≤ Nat.factorization (Nat.card ↥(center B)) 2 := hP'
    omega
  rw [Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two (Nat.card_pos.ne'), hker0]
  norm_num

theorem exists_perfect_cover_subgroup {L Q : Type} [Group L] [Finite L] [Group Q] [Finite Q]
    (π : L →* Q) (hπ : Function.Surjective π) (J' : Subgroup Q) (hJ' : ⁅J', J'⁆ = J') :
    ∃ J : Subgroup L, J ≤ J'.comap π ∧ (J.subgroupOf (J'.comap π)).Normal ∧ ⁅J, J⁆ = J ∧
      J.map π = J' := by
  refine ⟨Quasithin.perfectCore (J'.comap π), Quasithin.perfectCore_le _,
    Quasithin.perfectCore_normal _, Quasithin.perfectCore_perfect _, ?_⟩
  rw [Quasithin.map_perfectCore, Subgroup.map_comap_eq_self_of_surjective hπ J',
    Quasithin.perfectCore_eq_self_of_perfect hJ']

theorem exists_hom_of_map_eq {L Q : Type} [Group L] [Group Q] (π : L →* Q)
    (hk : π.ker ≤ center L) {J : Subgroup L} {J' : Subgroup Q} (h : J.map π = J') :
    ∃ ρ : J →* J', Function.Surjective ρ ∧ (∀ x : J, ((ρ x : J') : Q) = π (x : L)) ∧
      ρ.ker ≤ center J := by
  let ρ : J →* J' := (π.comp J.subtype).codRestrict J' fun x => by
    rw [← h]
    exact Subgroup.mem_map_of_mem π x.2
  have hρ : ∀ x : J, ((ρ x : J') : Q) = π (x : L) := fun x => rfl
  refine ⟨ρ, ?_, hρ, ?_⟩
  · intro y
    have hy : (y : Q) ∈ J.map π := by rw [h]; exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  · intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hx1 : π (x : L) = 1 := by
      have h2 : ((ρ x : J') : Q) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      rwa [hρ x] at h2
    have hcx : (x : L) ∈ center L := hk (MonoidHom.mem_ker.mpr hx1)
    simpa using Subgroup.mem_center_iff.mp hcx (y : L)

theorem exists_involution_lift {A B : Type} [Group A] [Group B] (ρ : A →* B)
    (hρ : Function.Surjective ρ) (hker : ¬ 2 ∣ Nat.card ρ.ker) {b : B} (hb : orderOf b = 2) :
    ∃ a : A, orderOf a = 2 ∧ ρ a = b := by
  obtain ⟨a₀, ha₀⟩ := hρ b
  have hb2 : b ^ 2 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hkodd : Odd (Nat.card ρ.ker) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hker)
  have hb_ne : b ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hb
    omega
  have ha₀2 : a₀ ^ 2 ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_pow, ha₀, hb2]
  have hpow : (a₀ ^ 2) ^ Nat.card ρ.ker = 1 := by
    have hmem : (⟨a₀ ^ 2, ha₀2⟩ : ρ.ker) ^ Nat.card ρ.ker = 1 := pow_card_eq_one'
    simpa using congrArg Subtype.val hmem
  have hρu : ρ (a₀ ^ Nat.card ρ.ker) = b := by
    rw [map_pow, ha₀]
    obtain ⟨m, hm⟩ := hkodd
    rw [hm, pow_succ, pow_mul, hb2, one_pow, one_mul]
  have hu2 : (a₀ ^ Nat.card ρ.ker) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    exact hpow
  have hu_ne_one : a₀ ^ Nat.card ρ.ker ≠ 1 := by
    intro h
    apply hb_ne
    rw [← hρu, h, map_one]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨a₀ ^ Nat.card ρ.ker, orderOf_eq_prime hu2 hu_ne_one, hρu⟩

theorem HasCleanFullClassBMember.lift {L Q : Type} [Group L] [Finite L] [Group Q] [Finite Q]
    (π : L →* Q) (hπ : Function.Surjective π) (hk : π.ker ≤ center L)
    (h : HasCleanFullClassBMember Q) : HasFullClassBMember L := by
  obtain ⟨J', ū, hJ, hshape, hpart, hqs, hO⟩ := h
  have hJ'perf : ⁅J', J'⁆ = J' := Subgroup.isPerfect_iff.mp hJ.perfect
  obtain ⟨J, hJle, hJnorm, hJperf, hJmap⟩ := exists_perfect_cover_subgroup π hπ J' hJ'perf
  obtain ⟨ρ, hρs, hρπ, hρk⟩ := exists_hom_of_map_eq π hk hJmap
  haveI : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJperf
  have hodd : ¬ 2 ∣ Nat.card ρ.ker :=
    not_two_dvd_card_ker_of_full_cover ρ hρs hρk inferInstance hqs hO hpart
  let b : ↥J' := ⟨ū, hJ.mem⟩
  have hb2 : orderOf b = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hJ.orderOf_eq_two
  have hbcenter : b ∈ center ↥J' := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hy := hJ.subnormal.le y.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    exact hy
  obtain ⟨u, hu2, huρ⟩ := exists_involution_lift ρ hρs hodd hb2
  have hcenter : (center ↥J').comap ρ = center ↥J :=
    comap_center_eq_of_central_cover ρ hρs hρk inferInstance
  have hu_center : u ∈ center ↥J := by
    rw [← hcenter, Subgroup.mem_comap, huρ]
    exact hbcenter
  let u' : L := (u : L)
  have hu'2 : orderOf u' = 2 := by
    show orderOf ((u : ↥J) : L) = 2
    rw [Subgroup.orderOf_coe]
    exact hu2
  have hπu : π u' = ū := by
    have h := hρπ u
    rw [huρ] at h
    exact h.symm
  have hu'mem : u' ∈ J := by
    show ((u : ↥J) : L) ∈ J
    exact u.2
  have hJcent : J ≤ Subgroup.centralizer ({u'} : Set L) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    show x * ((u : ↥J) : L) = ((u : ↥J) : L) * x
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hu_center (⟨x, hx⟩ : ↥J))
  have hsub : IsSubnormal J (Subgroup.centralizer ({u'} : Set L)) := by
    have hchain : IsSubnormal J ((Subgroup.centralizer ({ū} : Set Q)).comap π) :=
      IsSubnormal.trans (IsSubnormal.step hJle hJnorm (IsSubnormal.refl _))
        (IsSubnormal.comap π hJ.subnormal)
    have hcentle : Subgroup.centralizer ({u'} : Set L) ≤
        (Subgroup.centralizer ({ū} : Set Q)).comap π := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff] at hx
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      rw [← hπu]
      simpa using congrArg π hx
    have h := hchain.inf_of_le hcentle
    rwa [inf_eq_left.mpr hJcent] at h
  have hu'_not_center : u' ∉ center L := by
    intro hc
    apply hJ.not_mem_center
    rw [← hπu]
    rw [Subgroup.mem_center_iff] at hc
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := hπ q
    rw [← map_mul, ← map_mul, hc l]
  have hmtype : IsMTypeSchur 3 ↥J :=
    isMTypeSchur_of_surjective_odd ρ hρs hodd inferInstance hJ.mtype
  have hshape' : ClassBShape ↥J := classBShape_of_surjective_odd ρ hρs hodd hshape
  have hpart' : ¬ PartialCentre ↥J := fun h' =>
    hpart ((partialCentre_iff_of_surjective_odd ρ hρs hodd).mp h')
  exact ⟨J, u', ⟨hu'2, hu'mem, hu'_not_center, inferInstance, hsub, hmtype⟩, hshape', hpart'⟩

end CFSG.OddStandard.HigherRank.F3
