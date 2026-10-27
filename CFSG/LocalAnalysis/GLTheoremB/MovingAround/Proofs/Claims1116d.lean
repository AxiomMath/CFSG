module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1116c
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeAFinal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1Seven
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFi24Seven
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Co1Seven
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Fi7Gen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRu3
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicOne
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFiveKit
public import CFSG.Quasithin.H13.GoldschmidtC137S168Main
public import CFSG.Sporadic.Recognition.JankoWongLemma17d
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.GH74.KGroups.A5
public import CFSG.LargeExtraspecial.S12TriG2
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.GLTheoremB.BarXTools
public import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.Sporadic.Suz.Simple
import CFSG.Walter.PSL2Facts.Even
import CFSG.LocalAnalysis.GLTheoremA.S4S.Common
import CFSG.RankThree.PerfectCover.CentralQuotientPrimeSupport
import Mathlib.Tactic.Simproc.Factors
public import Certificates.Certificate6001
public import Certificates.Certificate6002
public import Certificates.Certificate6003
public import Certificates.Certificate6004
public import Certificates.Certificate6005
public import Certificates.Certificate6007
public import Certificates.Certificate16026
public import CFSG.GH74.KGroups.L34Aut
public import CFSG.HardMathSupport.Dickson.I271.SporGenBM
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveHN
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveShape
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3All
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Glue
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Easy
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeKFacts
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OrdU2
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma36Inputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitStatement412
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporCheck
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporFiveB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporTh7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFiveB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporRu3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporThreeSmall
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1113
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input319
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1310a5b
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
public import Certificates.Certificate41501
public import Certificates.Data.TabCo1ThreeE

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1116d

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1116c
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple PSimple PQuot)

set_option linter.unusedSectionVars false

section Seven

variable {G : Type} [Group G] [Finite G]

theorem prime_dvd_card_pSimple {p : ℕ} (hp : p.Prime) {X I : Subgroup G}
    (hI : GLAPComponent p X I) : p ∣ Nat.card (PSimple p I) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsPerfect (PQuot p I) :=
    ⟨(CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hI).1⟩
  by_contra h
  exact CFSG.RankThree.PerfectCover.perfect_central_quotient_prime_support hp h
    (CFSG.LocalAnalysis.GLTheoremA.dvd_card_pQuot_of_component hp hI)

theorem isElemAbelian_two_of_sq {H : Type*} [Group H] {V : Subgroup H}
    (h : ∀ x ∈ V, x ^ 2 = 1) : IsElemAbelian 2 V := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, h⟩
  have hinv : ∀ x ∈ V, x⁻¹ = x := fun x hx =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h x hx)
  apply Subtype.ext
  have e := hinv _ (V.mul_mem a.2 b.2)
  rw [mul_inv_rev, hinv _ b.2, hinv _ a.2] at e
  exact e.symm

theorem false_of_pSimple_L28 {p : ℕ} {C I : Subgroup G} (hIC : I ≤ C)
    (h16 : ¬ 16 ∣ Nat.card C) (hR : CFSG.HardMathSupport.Dickson.I271.RankOK 7 C)
    (e : PSimple p I ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3)) :
    False := by
  let π : ↥I →* PSimple p I := (QuotientGroup.mk' (Subgroup.center (PQuot p I))).comp
    (QuotientGroup.mk' (GLAPPrimeCore p ↥I))
  have hπ : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  let φ : ↥I →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3) :=
    e.toMonoidHom.comp π
  have hφ : Function.Surjective φ := e.surjective.comp hπ
  have hT : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3)) = 504 := by
    have h := CFSG.Walter.psl2_even_card (f := 3) (by norm_num)
    norm_num at h
    exact h
  have hker : Nat.card φ.ker * 504 = Nat.card ↥I := by
    rw [← hT]
    exact Subgroup.card_ker_mul_card_of_surjective hφ
  have hIC' : Nat.card ↥I ∣ Nat.card C := Subgroup.card_dvd_of_le hIC
  have hodd : ¬ 2 ∣ Nat.card φ.ker := by
    rintro ⟨m, hm⟩
    exact h16 ((show 16 ∣ Nat.card ↥I from ⟨63 * m, by rw [← hker, hm]; ring⟩).trans hIC')
  have hI0 : Nat.card ↥I ≠ 0 := Nat.card_pos.ne'
  have h8 : 2 ^ 3 ∣ Nat.card ↥I := ⟨63 * Nat.card φ.ker, by rw [← hker]; ring⟩
  have hv : (Nat.card ↥I).factorization 2 = 3 := by
    have h1 := (Nat.prime_two.pow_dvd_iff_le_factorization hI0).1 h8
    have h2 : ¬ 4 ≤ (Nat.card ↥I).factorization 2 := fun h =>
      h16 (((Nat.prime_two.pow_dvd_iff_le_factorization hI0).2 h).trans hIC')
    omega
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥I) := inferInstance
  have hP8 : Nat.card (P : Subgroup ↥I) = 8 := by
    rw [P.card_eq_multiplicity, hv]
    norm_num
  obtain ⟨U, hU⟩ := (P.isPGroup'.map φ).exists_le_sylow
  haveI := (CFSG.Walter.psl2_even_sylow_two (f := 3) (by norm_num) U).1
  have hsq : ∀ x ∈ (P : Subgroup ↥I), x ^ 2 = 1 := by
    intro x hx
    have hx2 : x ^ 2 ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian (φ x) (hU (Subgroup.mem_map_of_mem φ hx))
    have hxP : x ^ 2 ∈ (P : Subgroup ↥I) := Subgroup.pow_mem _ hx 2
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 P.isPGroup' ⟨x ^ 2, hxP⟩
    rw [Subgroup.orderOf_mk] at hk
    have hd : orderOf (x ^ 2) ∣ Nat.card φ.ker := Subgroup.orderOf_dvd_natCard φ.ker hx2
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact orderOf_eq_one_iff.1 hk
    · exact absurd ((dvd_pow_self 2 (Nat.succ_ne_zero k)).trans (hk ▸ hd)) hodd
  let V : Subgroup G := (P : Subgroup ↥I).map I.subtype
  have hV8 : Nat.card V = 8 := by
    rw [Subgroup.card_map_of_injective I.subtype_injective, hP8]
  have hVsq : ∀ v ∈ V, v ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hsq x hx, map_one]
  have hVne : V ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hV8
    norm_num at hV8
  exact hR 2 Nat.prime_two (by norm_num) V ((Subgroup.map_subtype_le _).trans hIC)
    (isElemAbelian_two_of_sq hVsq) hVne (by rw [hV8])

end Seven

section SevenCert


theorem downCompOK_seven {s : TauCeti.SporadicName} {Q : Type} [Group Q] [Finite Q] {k : Q}
    (hR : CFSG.HardMathSupport.Dickson.I271.RankOK 7 (Subgroup.centralizer ({k} : Set Q)))
    (h16 : ¬ 16 ∣ Nat.card (Subgroup.centralizer ({k} : Set Q)))
    (hd : ∀ I : Subgroup Q, GLAPComponent 7 (Subgroup.centralizer ({k} : Set Q)) I →
      Nat.card (PSimple 7 I) ∣ 2520) :
    DownCompOK s 7 k := by
  intro I hI q hq hq2 hq7 hC
  exfalso
  obtain ⟨hsI, hnab⟩ := CFSG.LocalAnalysis.GLTheoremA.KDSpor.pSimple_simple_nonab (by norm_num) hI
  haveI := hsI
  have h7 := prime_dvd_card_pSimple (by norm_num : Nat.Prime 7) hI
  rcases CFSG.LocalAnalysis.GLTheoremA.I1416Rows.chev_card_dvd_2520_cases
      CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds hnab hC (hd I hI) with
    h | h | ⟨h, -⟩ | ⟨-, ⟨e⟩⟩
  · rw [h] at h7
    norm_num at h7
  · exact not_isChevSimple_of_card_bound h (by norm_num) (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide)
      q hq hq2 hq7 hC
  · rw [h] at h7
    norm_num at h7
  · obtain ⟨e2⟩ := CFSG.GH74.KGroups.L28.equiv_psl_P
    exact false_of_pSimple_L28 hI.1 h16 hR (e.trans (e2.symm.trans
      (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv
        (CFSG.ClassicalModels.finiteFieldEquivGaloisField _ 2 3 (by norm_num)
          CFSG.GH74.KGroups.L28.card_GF8) (Fin 2))))

end SevenCert

section RowCo1Seven


theorem sporDownRow_Co1_seven : SporDownRow .Co1 7 := by
  obtain ⟨hfin, -, -, ⟨b⟩⟩ := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S.co1_model
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hrow := @sporDownRow_of_model' .Co1 7 (by norm_num) ↥CFSG.Sporadic.Co1Schreier.GA _ hfin b
  refine hrow fun k hk => downCompOK_seven ?_ ?_ fun I hI =>
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S.card_pSimple_dvd_2520 k hk hI
  · have h := CFSG.HardMathSupport.Dickson.I271.co1_rankOK_all Certificates.certificate13696
      Certificates.certificate17302 k hk
    rwa [top_inf_eq] at h
  · rcases CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S.card_centralizer_seven k hk with
      h | h <;> rw [h] <;> norm_num

end RowCo1Seven

section RowFi24Seven


theorem sporDownRow_Fi24_seven : SporDownRow .Fi24Prime 7 := by
  obtain ⟨hfin, -, -, ⟨b⟩⟩ := CFSG.HardMathSupport.Dickson.I271.Fi7.fi24_model
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hrow := @sporDownRow_of_model' .Fi24Prime 7 (by norm_num) ↥CFSG.Sporadic.Fi24.J _ hfin b
  refine hrow fun k hk => downCompOK_seven
    (CFSG.HardMathSupport.Dickson.I271.Fi7.fi7_rankOK
      CFSG.HardMathSupport.Dickson.I271.Fi7.fi7_order_four k hk) ?_
    fun I hI => CFSG.HardMathSupport.Dickson.I271.Fi7.card_pSimple_dvd_2520 k hk hI
  obtain ⟨g, hg | hg⟩ := CFSG.HardMathSupport.Dickson.I271.Fi7.fi7_conj_class k hk
  · rw [← CFSG.LocalAnalysis.GLTheoremA.I1416Rows.card_centralizer_conj' g k, hg,
      CFSG.HardMathSupport.Dickson.I271.Fi7.card_centralizer_Y7]
    norm_num
  · rw [← CFSG.LocalAnalysis.GLTheoremA.I1416Rows.card_centralizer_conj' g k, hg,
      CFSG.HardMathSupport.Dickson.I271.Fi7.card_centralizer_C7]
    norm_num

end RowFi24Seven

section GoodSuz


theorem downTypeOK_of_goodSpor_suz {s : TauCeti.SporadicName} {T : Type} [Group T]
    (h : CFSG.HardMathSupport.Dickson.I271.GoodSpor 3 [.Suz] T) : DownTypeOK s 3 T := by
  rcases h with hl | ⟨-, ⟨f⟩⟩ | ⟨S, hS, ⟨f⟩⟩
  · exact downTypeOK_of_leafType Nat.prime_three (by norm_num) hl
  · exact downTypeOK_of_chevP (by norm_num) (isChevSimple_three_of_A6 f)
  · rw [List.mem_singleton] at hS
    subst hS
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Suz
    have hc : Nat.card T = 448345497600 :=
      (Nat.card_congr (f.trans b.symm).toEquiv).trans CFSG.Sporadic.Suz.card_Suz
    haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
    exact downTypeOK_of_not_chev (not_isChevSimple_of_card_bound hc (by norm_num) (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide))

end GoodSuz

section RowCo1Three


theorem sporDownRow_Co1_three : SporDownRow .Co1 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Co1
  exact sporDownRow_of_centShape Nat.prime_three b
    (CFSG.HardMathSupport.Dickson.I271.CentShape.of_centShapeRk
      (CFSG.HardMathSupport.Dickson.I271.TabCo1.centShapeRk_Co1_three
        CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
        (CFSG.HardMathSupport.Dickson.I271.TabCo1.co1ThreeAShape_holds
          CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
          CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group)))
    fun _ _ h => downTypeOK_of_goodSpor_suz h

end RowCo1Three

section A5

variable {X : Type} [Group X] [Finite X]

theorem normal_of_component_card_sixty {L : Subgroup X} (hL : CFSG.IsComponent L)
    (h60 : Nat.card (↥L ⧸ Subgroup.center ↥L) = 60) (hX : Nat.card X ∣ 2160) : L.Normal := by
  have hLZ : Nat.card L = 60 * Nat.card (Subgroup.center ↥L) := by
    rw [← h60]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  refine ⟨fun n hn g => ?_⟩
  have hL' := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hL
  rcases CFSG.LocalCores.distinct_components_commute hL hL' with heq | hcomm
  · rw [heq]
    exact Subgroup.mem_map.2 ⟨n, hn, by simp⟩
  · exfalso
    have hcen : L.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer (L : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1
        (by rw [Subgroup.commutator_comm]; exact hcomm)
    have hcard' : Nat.card (L.map (MulAut.conj g).toMonoidHom) = Nat.card L :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have hinf : Nat.card ↥(L ⊓ L.map (MulAut.conj g).toMonoidHom) ≤
        Nat.card (Subgroup.center ↥L) := by
      have hle : (L ⊓ L.map (MulAut.conj g).toMonoidHom).subgroupOf L ≤ Subgroup.center ↥L := by
        intro z hz
        rw [Subgroup.mem_center_iff]
        intro w
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.1 (hcen (Subgroup.mem_subgroupOf.1 hz).2) w w.2
      calc Nat.card ↥(L ⊓ L.map (MulAut.conj g).toMonoidHom)
          = Nat.card ((L ⊓ L.map (MulAut.conj g).toMonoidHom).subgroupOf L) :=
            (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
        _ ≤ _ := Subgroup.card_le_of_le hle
    have h1 := CFSG.Sporadic.Recognition.JankoWong.card_sup_mul_card_inf_ge L
      (L.map (MulAut.conj g).toMonoidHom)
    have h2 : Nat.card ↥(L ⊔ L.map (MulAut.conj g).toMonoidHom) ≤ 2160 :=
      (Subgroup.card_le_card_group _).trans (Nat.le_of_dvd (by norm_num) hX)
    have hZ0 : 0 < Nat.card (Subgroup.center ↥L) := Nat.card_pos
    rw [hcard', hLZ] at h1
    have h3 := h1.trans (Nat.mul_le_mul h2 hinf)
    nlinarith

theorem false_of_component_card_sixty {L : Subgroup X}
    (hL : CFSG.IsComponent L) (h60 : Nat.card (↥L ⧸ Subgroup.center ↥L) = 60)
    (hX : Nat.card X ∣ 2160) (h27 : 27 ∣ Nat.card X)
    (hP : ∀ B : Subgroup X, Nat.card B = 27 → ∃ a ∈ B, ∃ b ∈ B, a * b ≠ b * a) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : L.Normal := normal_of_component_card_sixty hL h60 hX
  haveI : Group.IsPerfect ↥L := hL.1.1
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.1.2.1
  let ψ : X →* MulAut (↥L ⧸ Subgroup.center ↥L) :=
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥L).comp
      MulAut.conjNormal
  have hker : ∀ g ∈ ψ.ker, ∀ l ∈ L, g * l * g⁻¹ = l := by
    intro g hg l hl
    have h1 : MulAut.conjNormal g = (1 : MulAut ↥L) :=
      CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective ↥L
        (by rw [map_one]; exact hg)
    have h2 := congrArg (fun φ : MulAut ↥L => ((φ ⟨l, hl⟩ : ↥L) : X)) h1
    simpa [MulAut.conjNormal_apply] using h2
  obtain ⟨fA⟩ :=
    CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty h60
  obtain ⟨e5⟩ := CFSG.GH74.KGroups.A5.equiv_of_alt fA
  have hrange : Nat.card ψ.range ∣ 120 := by
    rw [← CFSG.GH74.KGroups.A5.card_mulAut e5]
    exact Subgroup.card_subgroup_dvd_card _
  have h9 : 9 ∣ Nat.card ψ.ker := by
    have h1 : Nat.card X ∣ Nat.card ψ.ker * 120 := by
      rw [← Subgroup.card_ker_mul_card_range ψ]
      exact Nat.mul_dvd_mul_left _ hrange
    have h2 := h27.trans h1
    omega
  obtain ⟨R₀⟩ : Nonempty (Sylow 3 ↥ψ.ker) := inferInstance
  let R : Subgroup X := (R₀ : Subgroup ↥ψ.ker).map ψ.ker.subtype
  have hRker : R ≤ ψ.ker := Subgroup.map_subtype_le _
  have hRp : IsPGroup 3 R := R₀.isPGroup'.map _
  have hR9 : 9 ∣ Nat.card R := by
    rw [Subgroup.card_map_of_injective ψ.ker.subtype_injective, R₀.card_eq_multiplicity]
    have h2 : 2 ≤ (Nat.card ψ.ker).factorization 3 :=
      (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 (by norm_num; exact h9)
    exact (show (9 : ℕ) = 3 ^ 2 by norm_num) ▸ pow_dvd_pow 3 h2
  obtain ⟨Q₁⟩ : Nonempty (Sylow 3 ↥L) := inferInstance
  have hsurj : Function.Surjective (QuotientGroup.mk' (Subgroup.center ↥L)) :=
    QuotientGroup.mk'_surjective _
  obtain ⟨y, hyQ, hy⟩ : ∃ y ∈ (Q₁ : Subgroup ↥L),
      QuotientGroup.mk' (Subgroup.center ↥L) y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : ((Q₁.mapSurjective hsurj : Sylow 3 _) : Subgroup (↥L ⧸ Subgroup.center ↥L)) =
        ⊥ := by
      rw [Sylow.coe_mapSurjective, eq_bot_iff]
      rintro _ ⟨z, hz, rfl⟩
      exact hcon z hz
    have hc := (Q₁.mapSurjective hsurj).card_eq_multiplicity
    rw [hbot, Subgroup.card_bot, h60, show (60 : ℕ) = 3 ^ 1 * 20 by norm_num,
      Nat.factorization_mul_apply_of_coprime (by norm_num), Nat.Prime.factorization_pow
        Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 20)] at hc
    norm_num at hc
  let Q₀ : Subgroup X := Subgroup.zpowers (y : X)
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 Q₁.isPGroup' ⟨y, hyQ⟩
  rw [Subgroup.orderOf_mk] at hk
  have hyk : orderOf (y : X) = 3 ^ k := (Subgroup.orderOf_coe y).trans hk
  have hQ₀ : Nat.card Q₀ = 3 ^ k := by rw [Nat.card_zpowers, hyk]
  have hQ₀p : IsPGroup 3 Q₀ := IsPGroup.of_card hQ₀
  have hyR : (y : X) ∉ R := by
    intro hyR
    apply hy
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    have h1 := hker (y : X) (hRker hyR) w w.2
    calc ((w * y : ↥L) : X) = (y : X) * w * (y : X)⁻¹ * y := by rw [h1]; rfl
      _ = ((y * w : ↥L) : X) := by simp
  have hinf : Nat.card ↥(R ⊓ Q₀) * 3 ≤ Nat.card Q₀ := by
    have hdvd : Nat.card ↥(R ⊓ Q₀) ∣ 3 ^ k := hQ₀ ▸ Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hjk : j ≠ k := by
      rintro rfl
      have heq : R ⊓ Q₀ = Q₀ :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hQ₀, hj'])
      exact hyR (heq.symm ▸ Subgroup.mem_zpowers (y : X) : (y : X) ∈ R ⊓ Q₀).1
    rw [hj', hQ₀, ← pow_succ]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hQ₀R : Q₀ ≤ Subgroup.centralizer (R : Set X) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro r hr
    have h1 := hker r (hRker hr) (y : X) y.2
    calc r * (y : X) = r * (y : X) * r⁻¹ * r := by group
      _ = (y : X) * r := by rw [h1]
  have hge : 3 * Nat.card R ≤ Nat.card ↥(R ⊔ Q₀) := by
    have hJ := CFSG.Sporadic.Recognition.JankoWong.card_sup_mul_card_inf_ge R Q₀
    have hpos : 0 < Nat.card ↥(R ⊓ Q₀) := Nat.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc 3 * Nat.card R * Nat.card ↥(R ⊓ Q₀)
        = Nat.card R * (Nat.card ↥(R ⊓ Q₀) * 3) := by ring
      _ ≤ Nat.card R * Nat.card Q₀ := Nat.mul_le_mul_left _ hinf
      _ ≤ _ := hJ
  have hsupP : IsPGroup 3 ↥(R ⊔ Q₀) := IsPGroup.to_sup_of_normal_left' hRp hQ₀p
    (hQ₀R.trans (Subgroup.centralizer_le_normalizer _))
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hsupP
  have hm3 : m ≤ 3 := by
    by_contra h
    push Not at h
    have : 3 ^ 4 ∣ 2160 := (pow_dvd_pow 3 h).trans
      (hm ▸ (Subgroup.card_subgroup_dvd_card _).trans hX)
    norm_num at this
  have hle27 : Nat.card ↥(R ⊔ Q₀) ≤ 27 := by
    rw [hm]
    exact (Nat.pow_le_pow_right (by norm_num) hm3).trans (by norm_num)
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have hRcard : Nat.card R = 9 := by
    obtain ⟨c, hc⟩ := hR9
    have h1 := hge.trans hle27
    rw [hc] at h1 hRpos ⊢
    have hc1 : c = 1 := by omega
    rw [hc1]
  have hsup27 : Nat.card ↥(R ⊔ Q₀) = 27 := by
    have h1 := hge
    rw [hRcard] at h1
    exact le_antisymm hle27 h1
  have hRab : R ≤ Subgroup.centralizer (R : Set X) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro r' hr'
    have := IsPGroup.commutative_of_card_eq_prime_sq (p := 3) (G := ↥R) (by rw [hRcard]; norm_num)
      ⟨r', hr'⟩ ⟨r, hr⟩
    exact congrArg Subtype.val this
  have hQab : Q₀ ≤ Subgroup.centralizer (Q₀ : Set X) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (Commute.zpow_self (y : X) n).eq
  have hab : R ⊔ Q₀ ≤ Subgroup.centralizer ((R ⊔ Q₀ : Subgroup X) : Set X) := by
    refine sup_le ?_ ?_
    · exact Subgroup.le_centralizer_iff.2 (sup_le hRab hQ₀R)
    · exact Subgroup.le_centralizer_iff.2 (sup_le (Subgroup.le_centralizer_iff.2 hQ₀R) hQab)
  obtain ⟨a, ha, b, hb, hne⟩ := hP (R ⊔ Q₀) hsup27
  exact hne (Subgroup.mem_centralizer_iff.1 (hab hb) a ha)

end A5

section A5Comp

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem card_map_of_ker_inf {H K : Type*} [Group H] [Group K] (f : H →* K) (P : Subgroup H)
    (h : ∀ x ∈ P, f x = 1 → x = 1) : Nat.card (P.map f) = Nat.card P := by
  have hinj : Function.Injective (f.comp P.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    exact Subtype.ext (h x x.2 hx)
  rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, MonoidHom.range_comp,
    Subgroup.range_subtype]

theorem false_of_glaPComponent_sixty {C I : Subgroup G}
    (hI : GLAPComponent 3 C I) (h60 : Nat.card (PSimple 3 I) = 60)
    (hC : Nat.card C ∣ 2160) (h27 : 27 ∣ Nat.card C)
    (hP : ∀ B : Subgroup G, B ≤ C → Nat.card B = 27 → ∃ a ∈ B, ∃ b ∈ B, a * b ≠ b * a) :
    False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL : CFSG.IsComponent (barX 3 C I) := (CFSG.isComponent_iff_open _).2 hI.2.2.1
  have e := quotEquivBarX Nat.prime_three hI.1 hI.2.1
  have h60' : Nat.card (↥(barX 3 C I) ⧸ Subgroup.center ↥(barX 3 C I)) = 60 := by
    rw [← h60]
    exact (Nat.card_congr (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).toEquiv).symm
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥C)) := CFSG.pPrimeCore_coprime_card
  have hCX : Nat.card ↥C = Nat.card (↥C ⧸ GLAPPrimeCore 3 ↥C) * Nat.card (GLAPPrimeCore 3 ↥C) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hX : Nat.card (↥C ⧸ GLAPPrimeCore 3 ↥C) ∣ 2160 :=
    (Subgroup.card_quotient_dvd_card _).trans hC
  have h27X : 27 ∣ Nat.card (↥C ⧸ GLAPPrimeCore 3 ↥C) := by
    have h1 : 3 ^ 3 ∣ Nat.card (↥C ⧸ GLAPPrimeCore 3 ↥C) * Nat.card (GLAPPrimeCore 3 ↥C) := by
      rw [← hCX]
      norm_num
      exact h27
    have := (Nat.Coprime.pow_left 3 hcop).dvd_of_dvd_mul_right h1
    norm_num at this
    exact this
  refine false_of_component_card_sixty hL h60' hX h27X fun B hB => ?_
  by_contra hcomm
  push Not at hcomm
  let π : ↥C →* ↥C ⧸ GLAPPrimeCore 3 ↥C := QuotientGroup.mk' _
  let B' : Subgroup ↥C := B.comap π
  let πB : ↥B' →* ↥B := (π.comp B'.subtype).codRestrict B (fun x => x.2)
  have hπB : Function.Surjective πB := by
    rintro ⟨b, hb⟩
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥C) b
    exact ⟨⟨c, hb⟩, rfl⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥B') := inferInstance
  have hinj : ∀ x ∈ (P : Subgroup ↥B'), πB x = 1 → x = 1 := by
    intro x hx h1
    have hxO : ((x : ↥C)) ∈ GLAPPrimeCore 3 ↥C :=
      (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val h1)
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 P.isPGroup' ⟨x, hx⟩
    rw [Subgroup.orderOf_mk] at hk
    have hdO : orderOf (x : ↥C) ∣ Nat.card (GLAPPrimeCore 3 ↥C) :=
      Subgroup.orderOf_dvd_natCard _ hxO
    rw [Subgroup.orderOf_coe, hk] at hdO
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact orderOf_eq_one_iff.1 hk
    · exact absurd ((dvd_pow_self 3 (Nat.succ_ne_zero k)).trans hdO)
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop)
  have hPcard : Nat.card (P : Subgroup ↥B') = 27 := by
    rw [← card_map_of_ker_inf πB _ hinj, ← Sylow.coe_mapSurjective hπB P,
      Sylow.card_eq_multiplicity, hB, show (27 : ℕ) = 3 ^ 3 by norm_num,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same]
  let ι : ↥B' →* G := C.subtype.comp B'.subtype
  have hι : Function.Injective ι := C.subtype_injective.comp B'.subtype_injective
  obtain ⟨a, ha, b, hb, hne⟩ := hP ((P : Subgroup ↥B').map ι)
    (fun z hz => by
      obtain ⟨w, -, rfl⟩ := hz
      exact (w : ↥C).2)
    (by rw [Subgroup.card_map_of_injective hι, hPcard])
  obtain ⟨a₀, ha₀, rfl⟩ := ha
  obtain ⟨b₀, hb₀, rfl⟩ := hb
  apply hne
  have hab : a₀ * b₀ = b₀ * a₀ := by
    have h1 : πB (a₀ * b₀ * (b₀ * a₀)⁻¹) = 1 := by
      have hc := hcomm (πB a₀) (πB a₀).2 (πB b₀) (πB b₀).2
      have hc' : πB a₀ * πB b₀ = πB b₀ * πB a₀ := Subtype.ext hc
      rw [map_mul, map_inv, map_mul, map_mul, hc', mul_inv_cancel]
    have := hinj _ (P.mul_mem (P.mul_mem ha₀ hb₀) (P.inv_mem (P.mul_mem hb₀ ha₀))) h1
    exact mul_inv_eq_one.1 this
  rw [← map_mul, hab, map_mul]

theorem factorization_three_eq_three {N : ℕ} (hN : N ≠ 0) (h27 : 27 ∣ N) (h81 : ¬ 81 ∣ N) :
    N.factorization 3 = 3 := by
  have h1 := (Nat.prime_three.pow_dvd_iff_le_factorization hN).1
    (show 3 ^ 3 ∣ N by norm_num; exact h27)
  have h2 : ¬ 4 ≤ N.factorization 3 := fun h => h81
    (by have := (Nat.prime_three.pow_dvd_iff_le_factorization hN).2 h; norm_num at this; exact this)
  omega

theorem noncomm_of_card_27 {Q : Type} [Group Q] [Finite Q]
    (hnc : CFSG.RankThree.PartOne.StrongP.HasNoncommPair 3 Q)
    (hQ : (Nat.card Q).factorization 3 = 3) (B : Subgroup Q) (hB : Nat.card B = 27) :
    ∃ a ∈ B, ∃ b ∈ B, a * b ≠ b * a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, b, -, -, hab, hpg⟩ := hnc
  obtain ⟨P₁, hP₁⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q P₁ (Sylow.ofCard B (by rw [hB, hQ]; norm_num))
  have hmem : ∀ x ∈ (P₁ : Subgroup Q), g * x * g⁻¹ ∈ B := by
    intro x hx
    have h1 : MulAut.conj g • x ∈ MulAut.conj g • (P₁ : Subgroup Q) :=
      Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) _ hx
    rw [← Sylow.coe_subgroup_smul, hg] at h1
    simpa [MulAut.smul_def] using h1
  have ha : a ∈ (P₁ : Subgroup Q) := hP₁ (Subgroup.subset_closure (Set.mem_insert a {b}))
  have hb : b ∈ (P₁ : Subgroup Q) :=
    hP₁ (Subgroup.subset_closure (Set.mem_insert_of_mem a rfl))
  refine ⟨g * a * g⁻¹, hmem a ha, g * b * g⁻¹, hmem b hb, fun h => hab ?_⟩
  have h2 : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
    calc g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) := by group
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := h
      _ = g * (b * a) * g⁻¹ := by group
  simpa using h2

end A5Comp

section ThreeCert


theorem not_isChevSimple_of_card_dvd_720 {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hnab : ∃ a b : T, a * b ≠ b * a) (hd : Nat.card T ∣ 720) (h60 : Nat.card T ≠ 60) :
    ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ 3 → ¬ IsChevSimple q T := by
  have hns : ¬ Group.IsSolvable T := fun h => by
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.2 h) a b)
  have h60' : 60 ≤ Nat.card T := by
    by_contra h
    exact hns (CFSG.GroupTheory.groups_order_below_sixty_solvable (by omega))
  have hcases : Nat.card T = 72 ∨ Nat.card T = 80 ∨ Nat.card T = 144 ∨ Nat.card T = 90 ∨
      Nat.card T = 120 ∨ Nat.card T = 180 ∨ Nat.card T = 240 ∨ Nat.card T = 360 ∨
      Nat.card T = 720 := by
    obtain ⟨c, hc⟩ := hd
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc
    have hc12 : c ≤ 12 := by
      by_contra h
      have : Nat.card T * 13 ≤ Nat.card T * c := Nat.mul_le_mul_left _ (by omega)
      omega
    interval_cases c <;> omega
  rcases hcases with h | h | h | h | h | h | h | h | h
  · exact (hns (CFSG.LocalAnalysis.GLTheoremA.KDSpor.isSolvable_of_card_eq Nat.prime_two
      Nat.prime_three (by norm_num) (a := 3) (b := 2) (by rw [h]; norm_num))).elim
  · exact (hns (CFSG.LocalAnalysis.GLTheoremA.KDSpor.isSolvable_of_card_eq Nat.prime_two
      Nat.prime_five (by norm_num) (a := 4) (b := 1) (by rw [h]; norm_num))).elim
  · exact (hns (CFSG.LocalAnalysis.GLTheoremA.KDSpor.isSolvable_of_card_eq Nat.prime_two
      Nat.prime_three (by norm_num) (a := 4) (b := 2) (by rw [h]; norm_num))).elim
  · exact fun q _ _ _ => CFSG.LocalAnalysis.GLTheoremA.I1416QRows.not_isChevSimple_of_not_lieOrder
      CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds h
      (fun d hd => CFSG.LocalAnalysis.GLTheoremA.I1416Rows.Order90.lieOrderFormula_ne_90 hd)
      (by decide) (by decide) (by decide) q
  · exact fun q _ _ _ => CFSG.LocalAnalysis.GLTheoremA.I1416QRows.not_isChevSimple_of_not_lieOrder
      CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds h
      (fun d hd => CFSG.LocalAnalysis.GLTheoremA.I1416Rows.Order120.lieOrderFormula_ne_120 hd)
      (by decide) (by decide) (by decide) q
  all_goals
    exact not_isChevSimple_of_card_bound h (by norm_num) (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide)

theorem downCompOK_three_of_card_dvd_2160 {s : TauCeti.SporadicName} {Q : Type} [Group Q]
    [Finite Q] {k : Q} (hk3 : orderOf k = 3)
    (hC : Nat.card (Subgroup.centralizer ({k} : Set Q)) ∣ 2160)
    (h27 : 27 ∣ Nat.card (Subgroup.centralizer ({k} : Set Q)))
    (hP : ∀ B : Subgroup Q, Nat.card B = 27 → ∃ a ∈ B, ∃ b ∈ B, a * b ≠ b * a) :
    DownCompOK s 3 k := by
  intro I hI q hq hq2 hq3 hChev
  exfalso
  obtain ⟨hsI, hnab⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KDSpor.pSimple_simple_nonab Nat.prime_three hI
  haveI := hsI
  have h3 : 3 * Nat.card (PSimple 3 I) ∣ 2160 :=
    (CFSG.LocalAnalysis.GLTheoremA.I1416Rows.prime_mul_card_pSimple_dvd_cent Nat.prime_three hk3
      hI.1).trans hC
  have hd : Nat.card (PSimple 3 I) ∣ 720 :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) (h3.trans (by norm_num))
  by_cases h60 : Nat.card (PSimple 3 I) = 60
  · exact false_of_glaPComponent_sixty hI h60 hC h27 fun B _ hB => hP B hB
  · exact not_isChevSimple_of_card_dvd_720 hnab hd h60 q hq hq2 hq3 hChev

theorem downCompOK_three_of_card_dvd_504 {s : TauCeti.SporadicName} (hs : s = .M24 ∨ s = .He)
    {Q : Type} [Group Q] [Finite Q] {k : Q} (hk3 : orderOf k = 3)
    (hk : Nat.card (Subgroup.centralizer ({k} : Set Q)) ∣ 504) : DownCompOK s 3 k := by
  intro I hI
  obtain ⟨hs', hnab⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KDSpor.pSimple_simple_nonab Nat.prime_three hI
  haveI := hs'
  have h3 : 3 * Nat.card (PSimple 3 I) ∣ 504 :=
    (CFSG.LocalAnalysis.GLTheoremA.I1416Rows.prime_mul_card_pSimple_dvd_cent Nat.prime_three hk3
      hI.1).trans hk
  have hd : Nat.card (PSimple 3 I) ∣ 168 :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) (h3.trans (by norm_num))
  obtain ⟨e⟩ := CFSG.Quasithin.H13.U3.GC137.SQ.S168.nonempty_mulEquiv_psl_seven
    (CFSG.LocalAnalysis.GLTheoremA.I1416Rows.card_eq_168_of_dvd hnab hd)
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact fun _ _ _ _ _ => Or.inr (Or.inl ⟨rfl, hs, ⟨ZMod 7, inferInstance, inferInstance,
    by rw [Nat.card_eq_fintype_card, ZMod.card],
    ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 (ZMod 7))⟩⟩⟩)

theorem sporDownRow_three_of_check {s : TauCeti.SporadicName}
    (D : CFSG.HardMathSupport.Solomon.Coordinator.B3S3.Data)
    (hD : CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check D = true)
    {A B : Equiv.Perm (Fin D.n)}
    (hA : CFSG.Monster.B.Co2.Rep D.n D.A A) (hB : CFSG.Monster.B.Co2.Rep D.n D.B B)
    (b : ↥(Subgroup.closure {A, B}) ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hnc : CFSG.RankThree.PartOne.StrongP.HasNoncommPair 3 ↥(Subgroup.closure {A, B}))
    (h27 : 27 ∣ D.ord) (h81 : ¬ 81 ∣ D.ord)
    (hcases : ∀ c < D.cases.size, (D.cases[c]!.card ∣ 2160 ∧ 27 ∣ D.cases[c]!.card) ∨
      D.cases[c]!.card < 60 ∨ (D.cases[c]!.card ∣ 504 ∧ (s = .M24 ∨ s = .He))) :
    SporDownRow s 3 := by
  obtain ⟨hcardP, hcls⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check_card_order_sound D hA hB hD
  have hf : (Nat.card ↥(Subgroup.closure {A, B})).factorization 3 = 3 := by
    rw [hcardP]
    exact factorization_three_eq_three (hcardP ▸ Nat.card_pos.ne') h27 h81
  refine sporDownRow_of_model' Nat.prime_three b fun x hx => ?_
  have hx3 : orderOf (x : Equiv.Perm (Fin D.n)) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨c, hc, hcc⟩ := hcls x x.2 hx3
  have hcc' : Nat.card (Subgroup.centralizer ({x} : Set ↥(Subgroup.closure {A, B}))) =
      D.cases[c]!.card := by
    have hmapc := CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype
      (Subgroup.closure {A, B}) x
    rw [← hcc, ← hmapc, Subgroup.card_map_of_injective (Subgroup.closure {A, B}).subtype_injective]
  rcases hcases c hc with ⟨h1, h2⟩ | h1 | ⟨h1, hs⟩
  · exact downCompOK_three_of_card_dvd_2160 hx (by rw [hcc']; exact h1) (by rw [hcc']; exact h2)
      (noncomm_of_card_27 hnc hf)
  · exact downCompOK_of_no_comp fun I hI =>
      CFSG.LocalAnalysis.GLTheoremA.KDSpor.false_of_glaPComponent_of_solvable Nat.prime_three
        (CFSG.GroupTheory.groups_order_below_sixty_solvable (by rw [hcc']; exact h1)) hI
  · exact downCompOK_three_of_card_dvd_504 hs hx (by rw [hcc']; exact h1)

end ThreeCert

section RowM24Three


theorem sporDownRow_M24_three : SporDownRow .M24 3 :=
  sporDownRow_three_of_check CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m24S3Data
    Certificates.certificate13512 CFSG.HardMathSupport.Solomon.Coordinator.rep_m24A
    CFSG.HardMathSupport.Solomon.Coordinator.rep_m24B
    (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .M24).some
    CFSG.HardMathSupport.Timmesfeld.Tables.Census.pair_M24_three
    (by rw [show CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m24S3Data.ord = 244823040 from rfl]
        norm_num)
    (by rw [show CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m24S3Data.ord = 244823040 from rfl]
        norm_num)
    (by decide +kernel)

end RowM24Three

section RowJ2Three


theorem sporDownRow_J2_three : SporDownRow .J2 3 := by
  have h := Certificates.certificate13513
  obtain ⟨hvA, hvB⟩ := CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check_valid h
  have e : CFSG.Blueprint.NativeSporadic.J2 ≃* ↥CFSG.Sporadic.Schreier.j2P :=
    CFSG.Sporadic.Schreier.j2PermEquiv
  exact sporDownRow_three_of_check CFSG.HardMathSupport.Solomon.Coordinator.B3S3.j2S3Data h
    (CFSG.RankThree.Native.rep_of_validA hvA) (CFSG.RankThree.Native.rep_of_validA hvB)
    (e.symm.trans (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .J2).some)
    (CFSG.RankThree.PartOne.StrongP.HasNoncommPair.map e.toMonoidHom e.injective
      CFSG.HardMathSupport.Timmesfeld.Tables.Census.pair_J2_three)
    (by rw [show CFSG.HardMathSupport.Solomon.Coordinator.B3S3.j2S3Data.ord = 604800 from rfl]
        norm_num)
    (by rw [show CFSG.HardMathSupport.Solomon.Coordinator.B3S3.j2S3Data.ord = 604800 from rfl]
        norm_num)
    (by decide +kernel)

end RowJ2Three

section RowRuThree

open CFSG.Sporadic.Schreier CFSG.Sporadic.RuSchreier CFSG.EvenSporadicStandard.RuStd.S2


theorem sporDownRow_Ru_three : SporDownRow .Ru 3 := by
  have e : CFSG.Blueprint.NativeSporadic.Ru ≃* ↥ruP := ruEquivP
  have hfin : Finite ↥ruP := Finite.of_equiv _ e.toEquiv
  have hc : Nat.card ↥ruP = 145926144000 :=
    (Nat.card_congr e.toEquiv).symm.trans CFSG.Sporadic.Ru.card_Ru
  have b : ↥ruP ≃* (TauCeti.CFSGIndex.sporadic .Ru).Group :=
    e.symm.trans (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Ru).some
  let φ : CFSG.Blueprint.NativeSporadic.Carrier .Ru ≃* ↥ruP :=
    (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Ru).some.trans b.symm
  have hnc : CFSG.RankThree.PartOne.StrongP.HasNoncommPair 3 ↥ruP :=
    CFSG.RankThree.PartOne.StrongP.HasNoncommPair.map φ.toMonoidHom φ.injective
      CFSG.HardMathSupport.Timmesfeld.Tables.Census.pair_Ru_three
  have hf : (Nat.card ↥ruP).factorization 3 = 3 := by
    rw [hc]
    exact factorization_three_eq_three (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨hC0eq, hC0card⟩ := ruThreeC0_spec
  have hcard0 : Nat.card (Subgroup.centralizer ({ruThreeX0} : Set ↥ruP)) = 2160 := by
    have hmapc := CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype ruP ruThreeX0
    rw [← Subgroup.card_map_of_injective ruP.subtype_injective, hmapc, ← hC0card, hC0eq]
    rfl
  have hrow := @sporDownRow_of_model' .Ru 3 Nat.prime_three ↥ruP _ hfin b
  refine hrow fun k hk => ?_
  obtain ⟨c, hcz⟩ := exists_conj_ruThree k hk
  have hcent : Subgroup.centralizer ({k} : Set ↥ruP) =
      Subgroup.centralizer ({c * ruThreeX0 * c⁻¹} : Set ↥ruP) :=
    (CFSG.HardMathSupport.Solomon.Coordinator.centralizer_singleton_eq_of_zpowers hcz).symm
  have hck : Nat.card (Subgroup.centralizer ({k} : Set ↥ruP)) = 2160 := by
    rw [hcent, CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.centralizer_conj c ruThreeX0,
      Subgroup.card_map_of_injective (MulAut.conj c).injective, hcard0]
  exact downCompOK_three_of_card_dvd_2160 hk (by rw [hck]) (by rw [hck]; norm_num)
    (noncomm_of_card_27 hnc hf)

end RowRuThree


structure SporDownResidual' : Prop where
  B_three : SporDownRow .B 3
  M_three : SporDownRow .M 3
  Fi23_five : SporDownRow .Fi23 5
  Fi24Prime_five : SporDownRow .Fi24Prime 5
  B_five : SporDownRow .B 5
  M_five : SporDownRow .M 5
  B_seven : SporDownRow .B 7
  M_eleven : SporDownRow .M 11
  M_thirteen : SporDownRow .M 13

section Residual


theorem sporDownResidual_of_residual' (h : SporDownResidual') : SporDownResidual :=
  ⟨sporDownRow_M24_three, sporDownRow_J2_three, sporDownRow_Ru_three, sporDownRow_Co1_three,
    h.B_three, h.M_three, h.Fi23_five, h.Fi24Prime_five, h.B_five, h.M_five,
    sporDownRow_Co1_seven, sporDownRow_Fi24_seven, h.B_seven, h.M_eleven, h.M_thirteen⟩

end Residual

section Assembly


theorem inputSporDownChev_of_residual'
    (h : SporDownResidual') : Claims1116b.InputSporDownChev :=
  inputSporDownChev_of_residual (sporDownResidual_of_residual' h)

end Assembly

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1116d

end
