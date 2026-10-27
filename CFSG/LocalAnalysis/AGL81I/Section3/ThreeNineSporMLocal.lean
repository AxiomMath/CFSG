module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporBigOvergroup
public import CFSG.LocalAnalysis.StandardType.GGSporKF1F4At
import CFSG.LocalAnalysis.StandardType.GGSporKM7Wide
import CFSG.LocalAnalysis.StandardType.GGSporKBMTransportA
import CFSG.LocalAnalysis.StandardType.GGSporKCompConj
import CFSG.Assembly.LargeEvenGLABridge
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporBurnside

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporBig

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Open
open CFSG.Monster.Generated (Gmat)
open CFSG.AGLEmbedding.Norton.MON5_7 (dG zG tG)
open CFSG.HardMathSupport.Dickson.I271.TabMSeven
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance (orderOf_dG orderOf_zG orderOf_tG
  isTwoBCentralizer_tG centralizer_pow_eq_of_prime)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenCensus (monsterSevenClasses)
open CFSG.StandardType.SporadicShape (BMPCentralF1At BMOpCent)
open CFSG.Assembly (LargeEvenPComponent)

private theorem factorization_monster_seven :
    (808017424794512875886459904961710757005754368000000000 : ℕ).factorization 7 = 6 := by
  rw [show (808017424794512875886459904961710757005754368000000000 : ℕ) =
      7 ^ 6 * 6868034788179354485685895374900855570432000000000 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

private theorem dvd_of_dvd_monster_of_dvd_GL {n r s : ℕ} (hr : r ≤ 6)
    (hM : n ∣ 808017424794512875886459904961710757005754368000000000)
    (hG : n ∣ 7 ^ s * ∏ i : Fin r, (7 ^ r - 7 ^ (i : ℕ))) :
    n ∣ 2 ^ 16 * 3 ^ 8 * 5 ^ 2 * 7 ^ 6 * 19 := by
  have hP : ∏ i : Fin r, (7 ^ r - 7 ^ (i : ℕ)) ∣
      7 ^ 15 * (2 ^ 16 * 3 ^ 8 * 5 ^ 2 * 19 ^ 2 * 43 * 2801) := by
    interval_cases r <;> simp [Fin.prod_univ_succ]
  have h1 : n ∣ 7 ^ (s + 15) * (2 ^ 16 * 3 ^ 8 * 5 ^ 2 * 19 ^ 2 * 43 * 2801) := by
    rw [pow_add, mul_assoc]
    exact hG.trans (mul_dvd_mul_left _ hP)
  refine (Nat.dvd_gcd hM h1).trans ?_
  rw [Nat.Coprime.gcd_mul _ (Nat.Coprime.pow_left _ (by norm_num))]
  have h7 : Nat.gcd 808017424794512875886459904961710757005754368000000000 (7 ^ (s + 15)) ∣
      7 ^ 6 := by
    rw [show (808017424794512875886459904961710757005754368000000000 : ℕ) =
        7 ^ 6 * 6868034788179354485685895374900855570432000000000 by norm_num,
      Nat.Coprime.gcd_mul_right_cancel _ (Nat.Coprime.pow_right _ (by norm_num))]
    exact Nat.gcd_dvd_left _ _
  have hg : Nat.gcd 808017424794512875886459904961710757005754368000000000
      (2 ^ 16 * 3 ^ 8 * 5 ^ 2 * 19 ^ 2 * 43 * 2801) = 2 ^ 16 * 3 ^ 8 * 5 ^ 2 * 19 := by
    norm_num
  rw [hg, show 2 ^ 16 * 3 ^ 8 * 5 ^ 2 * 7 ^ 6 * 19 = 7 ^ 6 * (2 ^ 16 * 3 ^ 8 * 5 ^ 2 * 19) by ring]
  exact mul_dvd_mul_right h7 _

private theorem not_pow_dvd_monster_bound {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) (hd7 : d ≠ 7)
    (hd19 : d ≠ 19) (hdM : d ∣ 808017424794512875886459904961710757005754368000000000)
    (h : d ^ (808017424794512875886459904961710757005754368000000000 : ℕ).factorization d ∣
      2 ^ 22 * 3 ^ 12 * 5 ^ 2 * 7 ^ 9 * 19 ^ 2) : False := by
  have hmem := mem_of_prime_dvd hd
    (qs := [(2, 46), (3, 20), (5, 9), (7, 6), (11, 2), (13, 3), (17, 1), (19, 1), (23, 1),
      (29, 1), (31, 1), (41, 1), (47, 1), (59, 1), (71, 1)]) (by norm_num)
    (by norm_num; exact hdM)
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
  have hN : (808017424794512875886459904961710757005754368000000000 : ℕ) ≠ 0 := by norm_num
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact hd2 rfl
  · exact not_pow_dvd_of_factorization (q := 3) (e := 20) (by norm_num) hN (by norm_num)
      (by norm_num) h
  · exact not_pow_dvd_of_factorization (q := 5) (e := 9) (by norm_num) hN (by norm_num)
      (by norm_num) h
  · exact hd7 rfl
  · exact not_pow_dvd_of_factorization (q := 11) (e := 2) (by norm_num) hN (by norm_num)
      (by norm_num) h
  · exact not_pow_dvd_of_factorization (q := 13) (e := 3) (by norm_num) hN (by norm_num)
      (by norm_num) h
  · exact not_pow_dvd_of_factorization (q := 17) (e := 1) (by norm_num) hN (by norm_num)
      (by norm_num) h
  · exact hd19 rfl
  · exact not_pow_dvd_of_factorization (q := 23) (e := 1) (by norm_num) hN (by norm_num)
      (by norm_num) h
  · exact not_pow_dvd_of_factorization (q := 29) (e := 1) (by norm_num) hN (by norm_num)
      (by norm_num) h
  · exact not_pow_dvd_of_factorization (q := 31) (e := 1) (by norm_num) hN (by norm_num)
      (by norm_num) h
  · exact not_pow_dvd_of_factorization (q := 41) (e := 1) (by norm_num) hN (by norm_num)
      (by norm_num) h
  · exact not_pow_dvd_of_factorization (q := 47) (e := 1) (by norm_num) hN (by norm_num)
      (by norm_num) h
  · exact not_pow_dvd_of_factorization (q := 59) (e := 1) (by norm_num) hN (by norm_num)
      (by norm_num) h
  · exact not_pow_dvd_of_factorization (q := 71) (e := 1) (by norm_num) hN (by norm_num)
      (by norm_num) h

section Monster

private theorem gmat_sevenA :
    Nat.card ↥(Subgroup.centralizer ({dG} : Set Gmat)) = 7 * 4030387200 ∧
      (∃ t : Gmat, orderOf t = 2 ∧ t * dG = dG * t ∧
        Nat.card ↥(Subgroup.centralizer ({t} : Set Gmat)) = 2 * CFSG.Open.monsterBabyOrder) ∧
      (∃ u : Gmat, orderOf u = 2 ∧ u * dG = dG * u ∧
        Nat.card ↥(Subgroup.centralizer ({u} : Set Gmat)) =
          CFSG.Monster.Existence.twoBCentralizerOrder ∧
        35280 < Nat.card ↥(Subgroup.centralizer ({u} : Set Gmat) ⊓
          Subgroup.centralizer ({dG} : Set Gmat))) ∧
      (∀ u : Gmat, orderOf u = 2 → u * dG = dG * u →
        Nat.card ↥(Subgroup.centralizer ({u} : Set Gmat)) =
          CFSG.Monster.Existence.twoBCentralizerOrder →
        Nat.card ↥(Subgroup.centralizer ({u} : Set Gmat) ⊓
          Subgroup.centralizer ({dG} : Set Gmat)) = 150528) := by
  have : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  obtain ⟨hcls, h2A, h2B, hG5⟩ := gmat_seven_bounds
  obtain ⟨hHk, ⟨e⟩⟩ := tabMSeven_he_le_cent_dG
  exact tabMSeven_sevenA_facts hePE8 hcls h2A h2B hG5 orderOf_dG hHk e

private theorem gmat_zG_not_conj_dG : ∀ (g : Gmat) (m : ℕ), g * zG * g⁻¹ ≠ dG ^ m := by
  intro g m h
  by_cases hm : dG ^ m = 1
  · rw [hm] at h
    apply CFSG.AGLEmbedding.Norton.MON5_7.zG_ne_one
    have h' := congrArg (fun x => g⁻¹ * x * g) h
    simpa [mul_assoc] using h'
  · have h1 : Nat.card ↥(Subgroup.centralizer ({zG} : Set Gmat)) = 7 * 4030387200 := by
      have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      rw [← card_centralizer_conj g zG, h, centralizer_pow_eq_of_prime orderOf_dG hm,
        gmat_sevenA.1]
    have h6 := seven_pow_dvd_card_cent_zG
    rw [h1] at h6
    norm_num at h6

private theorem gmat_sevenB : ∃ z f : Gmat, IsConj z zG ∧ orderOf f = 5 ∧ z * f = f * z ∧
    ∃ S : Subgroup Gmat, S ≤ Subgroup.centralizer ({z} : Set Gmat) ∧
      Nonempty (↥S ≃* QuaternionGroup 4) := by
  obtain ⟨z, f, hz, hf, hzf, hzt, hft, S, hSz, hS⟩ := tabMSeven_sevenB_data
  refine ⟨z, f, ?_, hf, hzf, S, hSz, hS⟩
  rcases monsterSevenClasses z hz with h | h
  · exfalso
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    have huo : orderOf (c * tG * c⁻¹) = 2 := by rw [orderOf_conj_eq, orderOf_tG]
    have hud : c * tG * c⁻¹ * dG = dG * (c * tG * c⁻¹) := by
      rw [← hc]
      exact Commute.conj hzt.symm c
    have huc : Nat.card ↥(Subgroup.centralizer ({c * tG * c⁻¹} : Set Gmat)) =
        CFSG.Monster.Existence.twoBCentralizerOrder := by
      rw [card_centralizer_conj]
      exact isTwoBCentralizer_tG.2.2.2.2.1
    have hf' : c * f * c⁻¹ ∈ Subgroup.centralizer ({c * tG * c⁻¹} : Set Gmat) ⊓
        Subgroup.centralizer ({dG} : Set Gmat) := by
      refine ⟨Subgroup.mem_centralizer_singleton_iff.2 (Commute.conj hft c),
        Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      rw [← hc]
      exact Commute.conj hzf.symm c
    have h5 := Subgroup.orderOf_dvd_natCard _ hf'
    rw [gmat_sevenA.2.2.2 _ huo hud huc, orderOf_conj_eq, hf] at h5
    norm_num at h5
  · exact h

private theorem gmat_noComp_zG :
    ∀ J : Subgroup Gmat, ¬ GLAPComponent 7 (Subgroup.centralizer ({zG} : Set Gmat)) J := by
  have : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  obtain ⟨-, htA, huB, -⟩ := gmat_sevenA
  have hQ : ∃ S : Subgroup Gmat, S ≤ Subgroup.centralizer ({zG} : Set Gmat) ∧
      Nonempty (↥S ≃* QuaternionGroup 4) := by
    obtain ⟨z, -, hz, -, -, S, hSz, ⟨eS⟩⟩ := gmat_sevenB
    obtain ⟨c, hc⟩ := isConj_iff.1 hz
    refine ⟨S.map (MulAut.conj c).toMonoidHom, ?_,
      ⟨(S.equivMapOfInjective _ (MulAut.conj c).injective).symm.trans eS⟩⟩
    rintro _ ⟨s, hs, rfl⟩
    have hsz := Subgroup.mem_centralizer_singleton_iff.1 (hSz hs)
    rw [Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      ← hc]
    exact Commute.conj hsz c
  exact CFSG.HardMathSupport.Dickson.BMRows.census_M_seven_noComp orderOf_zG
    gmat_zG_not_conj_dG htA huB hQ

private theorem gmat_isConj_zG {x : Gmat} (hx : orderOf x = 7)
    (h76 : 7 ^ 6 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set Gmat))) : IsConj x zG := by
  rcases monsterSevenClasses x hx with h | h
  · rw [card_centralizer_eq_of_isConj h, gmat_sevenA.1] at h76
    norm_num at h76
  · exact h

private theorem gmat_no_largeEvenPComponent {x : Gmat} (hx : orderOf x = 7)
    (h76 : 7 ^ 6 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set Gmat))) :
    ∀ C : Subgroup Gmat,
      ¬ LargeEvenPComponent 7 (Subgroup.centralizer ({x} : Set Gmat)) C := by
  have : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  intro C hC
  obtain ⟨c, hc⟩ := isConj_iff.1 (gmat_isConj_zG hx h76)
  obtain ⟨C', hC'⟩ := CFSG.StandardType.SporadicShape.bmPComponent_of_conj_pow
    Nat.prime_seven hx (k := 1) (m := c⁻¹) (s := zG) (by norm_num)
    (by rw [← hc]; group) ⟨C, hC⟩
  exact gmat_noComp_zG C'
    ((CFSG.Assembly.LargeEven.largeEvenPComponent_iff_glaPComponent 7 _ C').1 hC')

private theorem gmat_bmPCentralF1At {x : Gmat} (hx : orderOf x = 7)
    (h76 : 7 ^ 6 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set Gmat))) :
    BMPCentralF1At 7 x := by
  have : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  exact CFSG.StandardType.SporadicShape.ggSporK_bmPCentralF1F4_gmat_seven.1 x hx
    (gmat_no_largeEvenPComponent hx h76)

private theorem gmat_card_centralizer_zG_dvd :
    Nat.card ↥(Subgroup.centralizer ({zG} : Set Gmat)) ∣ 2 ^ 16 * 3 ^ 8 * 5 ^ 2 * 7 ^ 6 * 19 := by
  have : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  set C := Subgroup.centralizer ({zG} : Set Gmat)
  obtain ⟨-, -, -, hle⟩ := gmat_bmPCentralF1At orderOf_zG seven_pow_dvd_card_cent_zG
  have hpc : Subgroup.centralizer (CFSG.pCore 7 C : Set C) ≤ CFSG.pCore 7 C := by
    intro c hc
    have hmem : (c : Gmat) ∈ BMOpCent 7 zG := by
      refine hle ⟨c.2, Subgroup.mem_centralizer_iff.2 ?_⟩
      rintro _ ⟨q, hq, rfl⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hc q hq)
    obtain ⟨q, hq, hqc⟩ := Subgroup.mem_map.1 hmem
    rwa [Subtype.val_injective hqc] at hq
  obtain ⟨r, s, hr, hs⟩ := exists_card_dvd_of_centralizer_pCore_le hpc
  have hCM : Nat.card C ∣ 808017424794512875886459904961710757005754368000000000 := by
    have h := Subgroup.card_subgroup_dvd_card C
    rwa [CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder, CFSG.Open.monsterOrder] at h
  have hr6 : r ≤ 6 := by
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 7) (G := C)).exists_card_eq
    have h7a : 7 ^ a ∣ 808017424794512875886459904961710757005754368000000000 :=
      ha ▸ (Subgroup.card_subgroup_dvd_card _).trans hCM
    have ha6 : a ≤ 6 := by
      by_contra h
      have h77 : 7 ^ 7 ∣ 808017424794512875886459904961710757005754368000000000 :=
        (pow_dvd_pow 7 (by omega)).trans h7a
      norm_num at h77
    rw [ha] at hr
    exact ((Nat.pow_le_pow_iff_right (by norm_num)).1 hr).trans ha6
  exact dvd_of_dvd_monster_of_dvd_GL hr6 hCM hs

private theorem nonempty_mulEquiv_gmat_M {L : Type} [Group L] (e : L ≃* Carrier .M) :
    Nonempty (L ≃* Gmat) := by
  have : IsSimpleGroup (Carrier .M) :=
    CFSG.Blueprint.NativeSporadic.MonsterModel.isSimpleGroup_y443Derived
  have : IsSimpleGroup L := MulEquiv.isSimpleGroup e
  exact CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e

theorem oPrimeCoreTrivialAt_M_seven {L : Type} [Group L] [Finite L] (e : L ≃* Carrier .M) :
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OPrimeCoreTrivialAt 7 L := by
  obtain ⟨f⟩ := nonempty_mulEquiv_gmat_M e
  exact CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OPrimeCoreTrivialAt.of_mulEquiv f
    (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.oPrimeCoreTrivialAt_seven_Gmat_of_classes
      monsterSevenClasses)

theorem card_centralizer_dvd_M_of_seven_central {L : Type} [Group L] [Finite L]
    (e : L ≃* Carrier .M) {z : L} (hz : orderOf z = 7)
    (h76 : 7 ^ 6 ∣ Nat.card (Subgroup.centralizer ({z} : Set L))) :
    Nat.card (Subgroup.centralizer ({z} : Set L)) ∣ 2 ^ 16 * 3 ^ 8 * 5 ^ 2 * 7 ^ 6 * 19 := by
  obtain ⟨f⟩ := nonempty_mulEquiv_gmat_M e
  rw [← natCard_centralizer_map f z] at h76 ⊢
  have hfz : orderOf (f z) = 7 := by rw [MulEquiv.orderOf_eq]; exact hz
  rw [card_centralizer_eq_of_isConj (gmat_isConj_zG hfz h76)]
  exact gmat_card_centralizer_zG_dvd

theorem not_pow_dvd_card_mul_card_centralizer_M {L : Type} [Group L] [Finite L]
    (e : L ≃* Carrier .M) {d : ℕ} {Y : Subgroup L} (h : SporOvergroupData L 7 d Y) (hd : d ≠ 19) :
    ∀ z : L, orderOf z = 7 →
      7 ^ (Nat.card L).factorization 7 ∣ Nat.card (Subgroup.centralizer ({z} : Set L)) →
      ¬ d ^ (Nat.card L).factorization d ∣ (7 ^ 3 - 1) * (7 ^ 3 - 7) * (7 ^ 3 - 7 ^ 2) *
        Nat.card (Subgroup.centralizer ({z} : Set L)) := by
  obtain ⟨f⟩ := nonempty_mulEquiv_gmat_M e
  have hL : Nat.card L = 808017424794512875886459904961710757005754368000000000 := by
    rw [Nat.card_congr f.toEquiv, CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder]
    norm_num [CFSG.Open.monsterOrder]
  obtain ⟨-, -, -, -, hdY, -, -, -, -, -⟩ := coreOfData h
  have hdvd : d ∣ 808017424794512875886459904961710757005754368000000000 := by
    rw [← hL]
    exact hdY.trans (Subgroup.card_subgroup_dvd_card Y)
  intro z hz h76 hd'
  rw [hL, factorization_monster_seven] at h76
  have hN0 : (7 ^ 3 - 1) * (7 ^ 3 - 7) * (7 ^ 3 - 7 ^ 2) *
      Nat.card (Subgroup.centralizer ({z} : Set L)) ∣ 2 ^ 22 * 3 ^ 12 * 5 ^ 2 * 7 ^ 9 * 19 ^ 2 := by
    have hP : (7 ^ 3 - 1) * (7 ^ 3 - 7) * (7 ^ 3 - 7 ^ 2) = 2 ^ 6 * 3 ^ 4 * 7 ^ 3 * 19 := by
      norm_num
    rw [hP]
    exact (Nat.mul_dvd_mul (dvd_refl _)
      (card_centralizer_dvd_M_of_seven_central e hz h76)).trans (by norm_num)
  have hdiv : d ^ (Nat.card L).factorization d ∣ 2 ^ 22 * 3 ^ 12 * 5 ^ 2 * 7 ^ 9 * 19 ^ 2 :=
    hd'.trans hN0
  rw [hL] at hdiv
  exact not_pow_dvd_monster_bound h.d_prime h.d_ne_two h.d_ne hd hdvd hdiv

theorem five_dvd_card_centralizer_M_seven {L : Type} [Group L] [Finite L]
    (e : L ≃* Carrier .M) {x : L} (hx : orderOf x = 7) :
    5 ∣ Nat.card (Subgroup.centralizer ({x} : Set L)) := by
  obtain ⟨f⟩ := nonempty_mulEquiv_gmat_M e
  rw [← natCard_centralizer_map f x]
  have hfx : orderOf (f x) = 7 := by rw [MulEquiv.orderOf_eq]; exact hx
  rcases monsterSevenClasses (f x) hfx with h | h
  · rw [card_centralizer_eq_of_isConj h, gmat_sevenA.1]
    norm_num
  · obtain ⟨z, g, hz, hg, hzg, -⟩ := gmat_sevenB
    rw [card_centralizer_eq_of_isConj h, ← card_centralizer_eq_of_isConj hz, ← hg]
    exact Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_centralizer_singleton_iff.2 hzg.symm)

theorem bmPCentralF1At_of_seven_central_M {L : Type} [Group L] [Finite L]
    (e : L ≃* Carrier .M) {z : L} (hz : orderOf z = 7)
    (h76 : 7 ^ 6 ∣ Nat.card (Subgroup.centralizer ({z} : Set L))) :
    CFSG.StandardType.SporadicShape.BMPCentralF1At 7 z := by
  have : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  obtain ⟨f⟩ := nonempty_mulEquiv_gmat_M e
  have hF1 : CFSG.StandardType.SporadicShape.BMPCentralF1 7 L :=
    CFSG.StandardType.SporadicShape.bmPCentralF1_of_mulEquiv 7 f.symm
      CFSG.StandardType.SporadicShape.ggSporK_bmPCentralF1F4_gmat_seven.1
  refine hF1 z hz fun C hC => ?_
  have hfz : orderOf (f z) = 7 := by rw [MulEquiv.orderOf_eq]; exact hz
  have h76' : 7 ^ 6 ∣ Nat.card (Subgroup.centralizer ({f z} : Set Gmat)) := by
    rw [natCard_centralizer_map]; exact h76
  apply gmat_no_largeEvenPComponent hfz h76' (C.map f.toMonoidHom)
  rw [← CFSG.Fischer.Classification.Recognition.map_centralizer_singleton f z]
  exact (CFSG.StandardType.SporadicShape.largeEvenPComponent_map_mulEquiv 7 f _ C).2 hC

end Monster

end CFSG.LocalAnalysis.AGL81I.Section3.SporBig
