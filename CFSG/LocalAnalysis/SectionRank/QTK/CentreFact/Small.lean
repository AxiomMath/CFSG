module

public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Defs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Open.StatedDefs
public import Certificates.Certificate13
public import Certificates.Certificate14
public import Certificates.Certificate15
public import Certificates.Certificate16
public import Certificates.Certificate17
public import Certificates.Certificate18
public import Certificates.Certificate19
public import Certificates.Certificate20
public import Certificates.Certificate21
public import Certificates.Certificate22
public import Certificates.Certificate23
public import Certificates.Certificate24
public import Certificates.Certificate25
public import Certificates.Certificate26
public import Certificates.Certificate27
public import Certificates.Certificate28
public import Certificates.Certificate29
public import Certificates.Certificate30
public import Certificates.Certificate31
public import Certificates.Certificate32
public import Certificates.Certificate33
public import Certificates.Certificate34
public import Certificates.Certificate35
public import Certificates.Certificate36
public import Certificates.Certificate37
public import Certificates.Certificate38
public import Certificates.Certificate39
public import Certificates.Certificate40
public import Certificates.Certificate41
public import Certificates.Certificate3029
public import Certificates.Certificate3119
public import Certificates.Certificate3120
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.Alternating
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.LocalAnalysis.SectionRank.OddCover.ScalarCover
import CFSG.Adapters.StatedPSLTwoNine
import CFSG.LieType.SeitzGeneration.UnitaryHyperDiag
import CFSG.Sporadic.Mathieu.M11
import CFSG.Sporadic.Mathieu.M22
import CFSG.Sporadic.Mathieu.M23
import CFSG.Sporadic.M23.M23Properties
import CFSG.Sporadic.J1
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.QTK.Section
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43
import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
import CFSG.Foundations
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
import CFSG.LieType.SeitzGeneration.UnitaryBlocks
import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
import CFSG.RankThree.PartTwo.Sec4.Census.Interface

public section

namespace CFSG.SectionRank.QTK.CentreFact

open Subgroup CFSG.Open

theorem small_oddBound_of_pRank_top {S : Type} [Group S] [Finite S] {r : ℕ} (hr : 1 < r)
    (h : CFSG.Open.pRank r (⊤ : Subgroup S) ≤ 2) : OddBound r S :=
  fun _ _ _ => (CFSG.SectionRank.pRank_mono hr le_top).trans h

theorem small_oddBound_of_mulEquiv {S T : Type} [Group S] [Group T] [Finite S] [Finite T] {r : ℕ}
    (hr : 1 < r) (e : S ≃* T) (h : OddBound r T) : OddBound r S := by
  intro R hR hR2
  have hR' : R.map e.toMonoidHom ≠ ⊥ := fun hb =>
    hR ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hb)
  calc CFSG.Open.pRank r (normalizer (R : Set S))
      ≤ CFSG.Open.pRank r ((normalizer (R : Set S)).map e.toMonoidHom) :=
        CFSG.SectionRank.pRank_le_map hr e.toMonoidHom e.injective _
    _ ≤ CFSG.Open.pRank r (normalizer ((R.map e.toMonoidHom : Subgroup T) : Set T)) :=
        CFSG.SectionRank.pRank_mono hr (Subgroup.le_normalizer_map _)
    _ ≤ 2 := h _ hR' (hR2.map _)

theorem small_oddBound_of_localRank {S : Type} [Group S] [Finite S] {r : ℕ} (hr : 1 < r)
    (h : CFSG.Assembly.RankThreeEven.localRank r S ≤ 2) : OddBound r S := by
  intro R hR hR2
  refine le_trans ?_ h
  refine le_csSup ⟨Nat.card S, fun k hk => ?_⟩ ⟨_, ⟨R, hR, hR2, rfl⟩, rfl⟩
  obtain ⟨H, -, rfl⟩ := hk
  refine csSup_le' fun j hj => ?_
  obtain ⟨F, -, -, hF⟩ := hj
  have h1 : j < r ^ j := Nat.lt_pow_self hr
  have h2 : Nat.card F ≤ Nat.card S := Subgroup.card_le_card_group F
  omega

theorem small_pRank_top_le_two_of_not_dvd {S : Type} [Group S] [Finite S] {r : ℕ} (hr : r.Prime)
    (h : ¬ r ^ 3 ∣ Nat.card S) : CFSG.Open.pRank r (⊤ : Subgroup S) ≤ 2 := by
  refine CFSG.SectionRank.pRank_le hr.one_lt fun E _ hE => ?_
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hk⟩ : ∃ k, Nat.card E = r ^ k :=
    IsPGroup.iff_card.1 fun g => ⟨1, Subtype.ext (by
      rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hE.2 _ g.2)⟩
  rw [hk]
  by_contra hlt
  push Not at hlt
  have h3 : r ^ 3 ∣ r ^ k := Nat.pow_dvd_pow r (by
    by_contra h'
    push Not at h'
    have : r ^ k ≤ r ^ 2 := Nat.pow_le_pow_right hr.pos (by omega)
    omega)
  exact h (h3.trans (hk ▸ Subgroup.card_subgroup_dvd_card E))

theorem small_oddBound_of_not_dvd {S : Type} [Group S] [Finite S] {r : ℕ} (hr : r.Prime)
    (h : ¬ r ^ 3 ∣ Nat.card S) : OddBound r S :=
  small_oddBound_of_pRank_top hr.one_lt (small_pRank_top_le_two_of_not_dvd hr h)

theorem oddBound_of_alternating {S : Type} [Group S] [Finite S] {n : ℕ} (hn : n ≤ 8)
    (e : S ≃* alternatingGroup (Fin n)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) : OddBound r S :=
  small_oddBound_of_mulEquiv hr.one_lt e
    (small_oddBound_of_pRank_top hr.one_lt (CFSG.SectionRank.pRank_alternating_le_two hn hr hr2))

theorem oddBound_of_psl_two_nine {S : Type} [Group S] [Finite S]
    (h : StatedClassicalModel S .PSL 2 3 2) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    OddBound r S := by
  obtain ⟨e⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_alternating_six_of_psl_two_nine h
  exact oddBound_of_alternating (by norm_num) e hr hr2

theorem oddBound_of_alternating_nine_of_ne_three {S : Type} [Group S] [Finite S]
    (e : S ≃* alternatingGroup (Fin 9)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) :
    OddBound r S := by
  refine small_oddBound_of_not_dvd hr ?_
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  intro hd
  have h2 : r ^ 2 ∣ 2 ^ 6 * 3 ^ 4 * 35 := by
    rw [show 2 ^ 6 * 3 ^ 4 * 35 = Nat.factorial 9 / 2 by decide]
    exact (pow_dvd_pow r (by norm_num : 2 ≤ 3)).trans hd
  exact CFSG.SectionRank.not_sq_dvd_of_not_sq_dvd_cofactor hr hr2 hr3
    (CFSG.SectionRank.not_sq_dvd_of_bound (B := 6) (by norm_num) (by norm_num) (by decide) hr hr2
      hr3) h2

section ThreeRank

open CFSG.SectionRank.OddCover Matrix

theorem small_card_scalars_statedSL_three {K : Type} [Field K] [Finite K]
    (h3 : 3 ∣ Nat.card K - 1) :
    Nat.card ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)) = 3 := by
  set D := (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)
  have hdvd : Nat.card D ∣ 3 := card_scalars_dvd (by norm_num) _ fun x c hc => by
    have hdet := det_of_mem_statedSL x.1.2
    rw [hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [card_units_eq]; exact h3)
  have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hcS : (GeneralLinearGroup.scalar (Fin 3) c) ∈ StatedSL 3 K := by
    refine Subgroup.subset_closure ?_
    change ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Units.val_pow_eq_pow_val, hc3,
      Units.val_one]
  have hx : (⟨GeneralLinearGroup.scalar (Fin 3) c, hcS⟩ : StatedSL 3 K) ∈ D :=
    Subgroup.mem_subgroupOf.2 ⟨c, rfl⟩
  have hne : D ≠ ⊥ := by
    intro hbot
    have h1 := (Subgroup.mem_bot.1 (hbot ▸ hx))
    have h2 := scalar_injective (K := K) (n := 3) (by norm_num)
      (congrArg (fun g : StatedSL 3 K => (g : GL (Fin 3) K)) h1 |>.trans (map_one _).symm)
    rw [h2, orderOf_one] at hc
    omega
  have hcard : Nat.card D ≠ 1 := fun h => hne (Subgroup.eq_bot_of_card_eq D h)
  exact (Nat.dvd_prime Nat.prime_three).1 hdvd |>.resolve_left hcard

theorem small_pRank_three_statedSL_le_two {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (h3 : 3 ∣ p ^ f - 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSL 3 K))) ≤ 2 := by
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have hq2 : 2 ≤ p ^ f :=
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact (not_three_dvd_pow_add_sub hf).2 h3
  refine three_pRank_statedProj_le_two monomialData_statedSL ?_
    (small_card_scalars_statedSL_three (by rwa [hK]))
  have hM : Nat.card (⊤ : Subgroup Kˣ) = p ^ f - 1 := by
    rw [Subgroup.card_top, card_units_eq, hK]
  rw [card_statedSL_three, hK, hM, ← factorization_six_mul_three (by
    have : 0 < p ^ f - 1 := by omega
    positivity)]
  have e1 : (p ^ f) ^ 2 - 1 = (p ^ f - 1) * (p ^ f + 1) := by
    zify [hq1, Nat.one_le_pow 2 _ hq1]; ring
  have e2 : (p ^ f) ^ 3 - 1 = (p ^ f - 1) * ((p ^ f) ^ 2 + p ^ f + 1) := by
    zify [hq1, Nat.one_le_pow 3 _ hq1]; ring
  rw [e1, e2]
  exact factorization_order_eq Nat.prime_three (by norm_num) (by positivity) (by omega)
    (by omega) (by positivity)
    (fun h => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm)
    (by omega) (factorization_sq_add_add_one Nat.prime_three hq1 h3)

end ThreeRank

theorem oddBound_three_of_psl_three {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : StatedClassicalModel S .PSL 3 p f) (h3 : 3 ∣ p ^ f - 1) : OddBound 3 S := by
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  exact small_oddBound_of_mulEquiv (by norm_num) e
    (small_oddBound_of_pRank_top (by norm_num) (small_pRank_three_statedSL_le_two hp hf hK h3))

theorem oddBound_three_of_psu_three {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : StatedClassicalModel S .PSU 3 p f) (h3 : 3 ∣ p ^ f + 1) : OddBound 3 S := by
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  exact small_oddBound_of_mulEquiv (by norm_num) e
    (small_oddBound_of_pRank_top (by norm_num)
      (CFSG.LieType.SeitzGeneration.pRank_three_projSU_three_le hU h3))

theorem oddBound_of_psl_three {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : StatedClassicalModel S .PSL 3 p f) {r : ℕ} (hr : r.Prime) (hr3 : r ∣ 3)
    (hrq : r ∣ p ^ f - 1) : OddBound r S := by
  obtain rfl : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 hr3
  exact oddBound_three_of_psl_three h hrq

theorem oddBound_of_psu_three {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : StatedClassicalModel S .PSU 3 p f) {r : ℕ} (hr : r.Prime) (hr3 : r ∣ 3)
    (hrq : r ∣ p ^ f + 1) : OddBound r S := by
  obtain rfl : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 hr3
  exact oddBound_three_of_psu_three h hrq

section Sporadic

open CFSG.Blueprint

theorem small_not_pow_three_dvd {n : ℕ}
    (hn : n = 7920 ∨ n = 443520 ∨ n = 10200960 ∨ n = 175560) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) : ¬ r ^ 3 ∣ n := by
  obtain ⟨h3, hr'⟩ := CFSG.SectionRank.small_sporadic_order_conditions hn
  by_cases hr3 : r = 3
  · subst hr3
    exact h3
  · exact fun hd => hr' r hr hr2 hr3 ((pow_dvd_pow r (by norm_num : 2 ≤ 3)).trans hd)

theorem oddBound_of_M11 {S : Type} [Group S] [Finite S]
    (e : S ≃* NativeSporadic.Carrier .M11) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    OddBound r S := by
  refine small_oddBound_of_not_dvd hr ?_
  rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .M11) = 7920 from
    CFSG.Sporadic.Mathieu.card_M11]
  exact small_not_pow_three_dvd (Or.inl rfl) hr hr2

theorem oddBound_of_M22 {S : Type} [Group S] [Finite S]
    (e : S ≃* NativeSporadic.Carrier .M22) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    OddBound r S := by
  refine small_oddBound_of_not_dvd hr ?_
  rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .M22) = 443520 from
    CFSG.Sporadic.Mathieu.card_M22]
  exact small_not_pow_three_dvd (Or.inr (Or.inl rfl)) hr hr2

theorem oddBound_of_M23
    {S : Type} [Group S] [Finite S]
    (e : S ≃* NativeSporadic.Carrier .M23) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    OddBound r S := by
  refine small_oddBound_of_not_dvd hr ?_
  rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .M23) = 10200960 from by
    change Nat.card NativeSporadic.M23 = _
    rw [CFSG.Sporadic.Mathieu.nativeM23_eq, Nat.card_eq_fintype_card]
    exact CFSG.M23.M23Group.card_M23]
  exact small_not_pow_three_dvd (Or.inr (Or.inr (Or.inl rfl))) hr hr2

theorem oddBound_of_J1 {S : Type} [Group S] [Finite S]
    (e : S ≃* NativeSporadic.Carrier .J1) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    OddBound r S := by
  refine small_oddBound_of_not_dvd hr ?_
  rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .J1) = 175560 from
    CFSG.Sporadic.J1.card_J1]
  exact small_not_pow_three_dvd (Or.inr (Or.inr (Or.inr rfl))) hr hr2

end Sporadic

end CFSG.SectionRank.QTK.CentreFact
