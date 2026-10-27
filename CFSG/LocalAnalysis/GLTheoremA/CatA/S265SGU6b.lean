module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.LinUnitUnitaryBlocks
import CFSG.Assembly.LargeEvenGLABridge
import CFSG.CGT.Timmesfeld75.L2Basic
import CFSG.CGT.Timmesfeld75.L2Sylow
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherUnitary
import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUFrame
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Det
import CFSG.LocalAnalysis.StandardType.GGSixLinearModelSUTorus
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeThree
import CFSG.LocalAnalysis.StandardType.GGTableBUnitarySixThreeCases
import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SLFacts
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SUFacts
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.UnitaryInner
import CFSG.Assembly.OpenBridges

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Yardstones.Md0ec50421ce4 Polynomial CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCPrimary
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly CFSG.StandardType
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

private theorem two_pow_mul_odd_inj {a b u v : ℕ} (hu : Odd u) (hv : Odd v)
    (h : 2 ^ a * u = 2 ^ b * v) : a = b ∧ u = v := by
  have hu' : ¬ 2 ∣ u := by have := Nat.odd_iff.mp hu; omega
  have hv' : ¬ 2 ∣ v := by have := Nat.odd_iff.mp hv; omega
  have hab : a = b := by
    have h1 := congrArg (padicValNat 2) h
    rwa [padicValNat.mul (by positivity) hu.pos.ne', padicValNat.mul (by positivity) hv.pos.ne',
      padicValNat.prime_pow, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hu',
      padicValNat.eq_zero_of_not_dvd hv', add_zero, add_zero] at h1
  subst hab
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by positivity) h⟩

private theorem two_pow_odd {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k - 1) ∧ Odd (2 ^ k + 1) := by
  have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  exact ⟨Nat.odd_iff.mpr (by omega), Nat.odd_iff.mpr (by omega)⟩

private theorem false_of_card_sl_two {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (h : (2 ^ n) ^ 3 * ((2 ^ n) ^ 6 - 1) * 3 =
        (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) ∨
      (2 ^ n) ^ 3 * ((2 ^ n) ^ 6 - 1) * 3 =
        (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1))) : False := by
  suffices H : ∀ w : ℕ, Odd w → w ≤ (2 ^ m) ^ 3 + 1 →
      (2 ^ n) ^ 3 * ((2 ^ n) ^ 6 - 1) * 3 = (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * w) → False by
    have h3 := two_pow_odd (k := m * 3) (by omega)
    rw [pow_mul] at h3
    rcases h with h | h
    · exact H _ h3.1 (by omega) h
    · exact H _ h3.2 le_rfl h
  intro w hw hwle h
  have h6 := (two_pow_odd (k := n * 6) (by omega)).1
  have h2 := (two_pow_odd (k := m * 2) (by omega)).1
  simp only [← pow_mul] at h
  rw [mul_assoc] at h
  obtain ⟨hnm, h'⟩ := two_pow_mul_odd_inj (h6.mul (by decide)) (h2.mul hw) h
  have hmn : m = n := by omega
  rw [hmn, pow_mul, pow_mul] at h'
  rw [hmn] at hwle
  have hq : 2 ≤ 2 ^ n := Nat.one_lt_two_pow (by omega)
  generalize 2 ^ n = q at h' hwle hq
  have hfac : q ^ 6 - 1 = (q ^ 2 - 1) * (q ^ 4 + q ^ 2 + 1) := by
    zify [Nat.one_le_pow 2 q (by omega), Nat.one_le_pow 6 q (by omega)]
    ring
  have h2q : 2 ≤ q ^ 2 := hq.trans (Nat.le_self_pow (by norm_num) q)
  rw [hfac, mul_assoc] at h'
  have h'' := Nat.eq_of_mul_eq_mul_left (by omega : 0 < q ^ 2 - 1) h'
  have h34 : q ^ 3 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  omega

variable {K : Type} [Field K] {n : ℕ}

theorem SGU6.card_quot_center_of_field (h : UnitaryFieldData 2 n K)
    (A : primeFormUnitary h (idGram K 6)) {c : Kˣ}
    (hA : (A : GL (Fin 6) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c)
    (hc : ∀ t : Kˣ, t ^ 3 ≠ c) {T : Subgroup (primeFormP h (idGram K 6))}
    (hT : CFSG.Open.IsComponentOf T (fixSubgroup (primeFormConjHom h (idGram K 6) A))) :
    Nat.card (↥T ⧸ Subgroup.center ↥T) = (2 ^ n) ^ 3 * ((2 ^ n) ^ 6 - 1) := by
  classical
  haveI := h.finite
  have hq : 2 ≤ 2 ^ n := Nat.one_lt_two_pow (by have := h.one_le; omega)
  set x : LinearMap.GeneralLinearGroup K (Fin 6 → K) :=
    Matrix.GeneralLinearGroup.toLin (A : GL (Fin 6) K) with hx
  have H : UnitaryPrimaryData h.bar (idForm h 6) x :=
    UnitaryBlocks.primaryData_toLin' h A.2 Nat.prime_three (by decide) hA
  obtain ⟨a, haT⟩ := UnitaryBlocks.exists_good_block_of_component hq A hx H T hT
  have hc' : ∀ d : K, d ^ 3 ≠ (c : K) := fun d hd => hc (Units.mk0 d fun h0 => c.ne_zero
    (by rw [← hd, h0, zero_pow three_ne_zero])) (Units.ext (by simp [hd]))
  have hirr := Line63.H5.irreducible_X_pow_three_sub_C_of_not_cube hc'
  have hPx : aeval (x : Module.End K (Fin 6 → K)) (X ^ 3 - C (c : K)) = 0 := by
    have h1 : (x : Module.End K (Fin 6 → K)) =
        Matrix.toLin' ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by rw [hx]; rfl
    rw [map_sub, map_pow, aeval_X, aeval_C, h1, ← Matrix.toLin'_pow, ← Units.val_pow_eq_pow_val,
      hA]
    ext v i
    by_cases hi : i = v <;> simp [hi]
  have hmon : (X ^ 3 - C (c : K) : K[X]).Monic := monic_X_pow_sub_C _ (by norm_num)
  have hmin : minpoly K (x : Module.End K (Fin 6 → K)) = X ^ 3 - C (c : K) :=
    (minpoly.eq_of_irreducible_of_monic hirr hPx hmon).symm
  have honly : ∀ b ∈ primaryFactors (x : Module.End K (Fin 6 → K)), b = X ^ 3 - C (c : K) := by
    intro b hb
    obtain ⟨hbirr, hbmon, hbdvd⟩ := mem_primaryFactors.mp hb
    rw [hmin] at hbdvd
    exact eq_of_monic_of_associated hbmon hmon (hbirr.associated_of_dvd hirr hbdvd)
  have hac : (a.1 : K[X]) = X ^ 3 - C (c : K) := honly _ a.1.2
  have hself : dualPoly h.bar (a.1 : K[X]) = a.1 := by
    rw [honly _ (dualPoly_mem_primaryFactors H a.1.2), hac]
  have hdeg : (a.1 : K[X]).natDegree = 3 := by rw [hac]; exact natDegree_X_pow_sub_C
  have hV : Module.finrank (AdjoinRoot (a.1 : K[X]))
      (primaryComponent (x : Module.End K (Fin 6 → K)) (a.1 : K[X])) = 2 := by
    have hfr := finrank_primaryComponent (x : Module.End K (Fin 6 → K)) (a.1 : K[X])
    have h6 : Module.finrank K
        (primaryComponent (x : Module.End K (Fin 6 → K)) (a.1 : K[X])) = 6 := by
      have htop : primaryComponent (x : Module.End K (Fin 6 → K)) (a.1 : K[X]) = ⊤ := by
        rw [eq_top_iff]
        intro v _
        rw [mem_primaryComponent, hac, hPx, LinearMap.zero_apply]
      rw [htop, finrank_top, Module.finrank_fin_fun]
    rw [h6, hdeg] at hfr
    omega
  obtain ⟨hE, Hf, hHf, hHfl, ⟨e⟩⟩ := UnitaryBlocks.nonempty_specialBlock_mulEquiv_sesqSU hself
    (CFSG.RankThree.PartOne.selfDualPrimaryBlock H a.1 hself)
  obtain ⟨e2⟩ :=
    CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf hHfl hV
  haveI : Finite (AdjoinRoot (a.1 : K[X])) := Module.finite_of_finite K
  letI : Fintype hE.fixedField := Fintype.ofFinite _
  have hcardF : Nat.card hE.fixedField = 2 ^ (n * 3) := hE.card_fixedField.trans (by rw [hdeg])
  haveI : CharP hE.fixedField 2 :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hcardF)
  let F := (specialBlock (idForm h 6) x (a.1 : K[X])).comap (UnitaryBlocks.toLinSU h 6)
  have hFmap : F.map (UnitaryBlocks.toLinSU h 6) = specialBlock (idForm h 6) x (a.1 : K[X]) :=
    Subgroup.map_comap_eq_self fun g hg => UnitaryBlocks.mem_range_toLinSU
      (specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq a.1 a.2 hg)
  let ε : Matrix.SpecialLinearGroup (Fin 2) hE.fixedField ≃* ↥F := (e.trans e2).symm.trans
    ((F.equivMapOfInjective _ UnitaryBlocks.toLinSU_injective).trans
      (MulEquiv.subgroupCongr hFmap)).symm
  have hZF : Subgroup.center ↥F = ⊥ := by
    rw [← Subgroup.map_center_eq ε, CFSG.CGT.Timmesfeld75.center_sl2_eq_bot, Subgroup.map_bot]
  let π := QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 6)) 6)
  have hinj : Function.Injective (π.subgroupMap F) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZF]
    intro u hu
    rw [MonoidHom.mem_ker] at hu
    have h1 : π (u : ↥(gramSU h (idGram K 6))) = 1 := congrArg Subtype.val hu
    have h3 := normOneScalars_le_center h _ 6 ((QuotientGroup.eq_one_iff _).1 h1)
    exact Subgroup.mem_center_iff.2 fun w => Subtype.ext (Subgroup.mem_center_iff.1 h3 _)
  let ε' := ε.trans ((MulEquiv.ofBijective (π.subgroupMap F)
    ⟨hinj, MonoidHom.subgroupMap_surjective π F⟩).trans (MulEquiv.subgroupCongr haT.symm))
  have hZT : Subgroup.center ↥T = ⊥ := by
    rw [← Subgroup.map_center_eq ε', CFSG.CGT.Timmesfeld75.center_sl2_eq_bot, Subgroup.map_bot]
  rw [hZT, Nat.card_congr (QuotientGroup.quotientBot : ↥T ⧸ (⊥ : Subgroup ↥T) ≃* ↥T).toEquiv,
    ← Nat.card_congr ε'.toEquiv, CFSG.CGT.Timmesfeld75.card_sl2, hcardF, pow_mul,
    show (2 ^ n) ^ 6 = ((2 ^ n) ^ 3) ^ 2 by ring]

theorem SGU6.false_of_layer_tyF [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (hpq : 3 ∣ 2 ^ n + 1) {φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))}
    (hφ : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGUSet (Fin 6) K (2 ^ n)))
    (h1 : φ ≠ 1) (h3 : φ ^ 3 = 1)
    (hL : CFSG.Open.IsComponentOf (CFSG.Open.GLALayer (fixSubgroup φ)) (fixSubgroup φ))
    (hty : catalogIs (↥(CFSG.Open.GLALayer (fixSubgroup φ)) ⧸
      Subgroup.center ↥(CFSG.Open.GLALayer (fixSubgroup φ))) (tyF 3)) : False := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr fun h0 => by subst h0; norm_num at hpq
  have hKd : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨U, hUU, hUN, hφU⟩ : ∃ U ∈ primeFormUnitary hKd (idGram K 6), ∃ hUN : U ∈
      Subgroup.normalizer (LargeEvenSUGroup (Fin 6) K (2 ^ n) : Set (GL (Fin 6) K)),
        φ = TableB.projConj _ ⟨U, hUN⟩ := by
    obtain ⟨M, hM, hφM⟩ := hφ
    have hMN : M ∈ Subgroup.normalizer (LargeEvenSUGroup (Fin 6) K (2 ^ n) : Set (GL (Fin 6) K)) :=
      TableBUE.gu_subset_normalizer hKd hM
    obtain ⟨u, hUU⟩ := TableBU63.exists_unitary_of_gu hKd hM
    have hsc : Matrix.GeneralLinearGroup.scalar (Fin 6) u ∈ LargeEvenScalars (Fin 6) K := ⟨u, rfl⟩
    have hsN := TableB.scalar_mem_normalizer (LargeEvenSUGroup (Fin 6) K (2 ^ n)) hsc
    refine ⟨_, hUU, mul_mem hsN hMN, ?_⟩
    rw [show (⟨_, mul_mem hsN hMN⟩ : Subgroup.normalizer (LargeEvenSUGroup (Fin 6) K (2 ^ n) :
        Set (GL (Fin 6) K))) = ⟨_, hsN⟩ * ⟨M, hMN⟩ from rfl, map_mul,
      TableB.projConj_of_scalar (LargeEvenSUGroup (Fin 6) K (2 ^ n)) hsc, one_mul]
    refine MulEquiv.ext fun y => QuotientGroup.induction_on y fun s => ?_
    rw [TableB.projConj_mk]
    exact hφM s ((LargeEvenSUGroup (Fin 6) K (2 ^ n)).normalizerMonoidHom ⟨M, hMN⟩ s) rfl
  obtain ⟨c, hc⟩ := TableBUE.mem_scalars_of_projConj_eq_one hKd hK (by norm_num) (by simp)
    Nat.prime_three hpq (M := ⟨U, hUN⟩ ^ 3) (by rw [map_pow, ← hφU, h3])
  have hU3 : U ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c := hc.symm
  have hUs : U ∉ LargeEvenScalars (Fin 6) K := fun hz =>
    h1 (hφU.trans (TableB.projConj_of_scalar _ hz))
  by_cases hcube : ∃ t : Kˣ, t ^ 3 = c
  · obtain ⟨t, ht⟩ := hcube
    have hcU := (SUTorus.scalar_mem_primeFormUnitary_iff (n := 6) hKd c).mp
      (by rw [← hU3]; exact pow_mem hUU 3)
    rw [hKd.bar_apply, ← pow_succ] at hcU
    have ht1 : t⁻¹ ^ (2 ^ n + 1) = 1 := by
      rw [inv_pow, SUTorus.pow_add_one_eq_one_of_pow hKd Nat.prime_three (by norm_num) hpq ht
        (Units.ext (by rw [Units.val_pow_eq_pow_val, hcU, Units.val_one])), inv_one]
    have hsc : Matrix.GeneralLinearGroup.scalar (Fin 6) t⁻¹ ∈ LargeEvenScalars (Fin 6) K :=
      ⟨t⁻¹, rfl⟩
    have hsN := TableB.scalar_mem_normalizer (LargeEvenSUGroup (Fin 6) K (2 ^ n)) hsc
    have hV3 : (Matrix.GeneralLinearGroup.scalar (Fin 6) t⁻¹ * U) ^ 3 = 1 := by
      rw [(CFSG.ClassicalGroups.UnitaryFlag.commute_scalar t⁻¹ U).symm.mul_pow, hU3,
        ← map_pow, ← map_mul, inv_pow, ht, inv_mul_cancel, map_one]
    have hVs : Matrix.GeneralLinearGroup.scalar (Fin 6) t⁻¹ * U ∉ LargeEvenScalars (Fin 6) K := by
      rintro ⟨w, hw⟩
      refine hUs ⟨t * w, ?_⟩
      rw [map_mul, hw, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
    have hφV : φ = TableB.projConj _ ⟨_, mul_mem hsN hUN⟩ := by
      rw [hφU, show (⟨_, mul_mem hsN hUN⟩ : Subgroup.normalizer
        (LargeEvenSUGroup (Fin 6) K (2 ^ n) : Set (GL (Fin 6) K))) = ⟨_, hsN⟩ * ⟨U, hUN⟩ from rfl,
        map_mul, TableB.projConj_of_scalar (LargeEvenSUGroup (Fin 6) K (2 ^ n)) hsc, one_mul]
    have hfix : fixSubgroup φ = ggFix φ := Subgroup.ext fun _ => Iff.rfl
    rw [hfix, ← CFSG.Assembly.LargeEven.largeEvenLayer_eq_glaLayer, hφV] at hL hty
    exact SGU6.false_of_cube_tyF hKd hpq (mul_mem (SUModel.scalar_mem_unitary hKd ht1) hUU) hV3
      hVs (mul_mem hsN hUN) (CFSG.Assembly.isComponentOf_iff_open.mpr hL) hty
  · have hcon : MulAut.congr (InndiagSU.projEquiv hKd (d := 6) (by norm_num)) φ =
        primeFormConjHom hKd (idGram K 6) ⟨U, hUU⟩ := by
      subst hφU
      refine MulEquiv.ext fun y => QuotientGroup.induction_on y fun s => ?_
      rw [primeFormConjHom_mk, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        InndiagSU.projEquiv_symm_mk, TableB.projConj_mk, InndiagSU.projEquiv_mk]
      rfl
    obtain ⟨f, hf, hfix⟩ : ∃ f : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)) →*
        primeFormP hKd (idGram K 6), Function.Injective f ∧
          fixSubgroup (primeFormConjHom hKd (idGram K 6) ⟨U, hUU⟩) = (fixSubgroup φ).map f :=
      ⟨InndiagSU.projEquiv hKd (d := 6) (by norm_num),
        (InndiagSU.projEquiv hKd (d := 6) (by norm_num)).injective, by
          rw [← hcon]
          exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr _ φ⟩
    have hT := CFSG.Assembly.isComponentOf_iff_open.mp
      (CFSG.StandardType.isComponentOf_map_of_injective f hf
        (CFSG.Assembly.isComponentOf_iff_open.mpr hL))
    rw [← hfix] at hT
    let ε := (CFSG.Open.GLALayer (fixSubgroup φ)).equivMapOfInjective f hf
    have hcard := (Nat.card_congr (QuotientGroup.congr _ _ ε
      (Subgroup.map_center_eq ε)).toEquiv).trans
        (SGU6.card_quot_center_of_field hKd ⟨U, hUU⟩ hU3 (fun t ht => hcube ⟨t, ht⟩) hT)
    obtain ⟨m, hm, hQ⟩ := SGU6.card_mul_three_of_tyF hty
    rw [hcard] at hQ
    exact false_of_card_sl_two hKd.one_le hm (hQ.imp And.right And.right)

end CFSG.LocalAnalysis.GLTheoremA.S265

end
