module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SKSympSel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDLinOrder
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTorus
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSpecial
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAlt6
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicFixed
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix
public import CFSG.LieType.Universal.Symplectic
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.GroupTheory.PLayer.PIndex
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.Descent
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD42Spec
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.LocalAnalysis.GL83PartI.I713.Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Res
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDescN
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DSGen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GSz
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDOrthSplit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDSel
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Alt
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieReduce
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcomp
public import CFSG.Quasithin.Recognition.CertTrialityCheckInputs
public import CFSG.RankThree.PartOne.K159.AutCore
public import CFSG.RankThree.PartOne.K159.AutSzIso
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs
public import CFSG.RankThree.ThinCatalog.EvenLinearTwoLocal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SK

open Module CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Generic

variable {H : Type*} [Group H]

theorem sk_commutator_eq_ker {A : Type*} [CommGroup A] (D : H →* A) (hperf : Group.IsPerfect ↥D.ker) :
    commutator H = D.ker := by
  refine le_antisymm ?_ ?_
  · rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  · calc D.ker = ⁅D.ker, D.ker⁆ := (Subgroup.isPerfect_iff.mp hperf).symm
      _ ≤ ⁅(⊤ : Subgroup H), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator H := (_root_.commutator_def H).symm

theorem skGood_of_quasisimple {p : ℕ} (hq : CFSG.IsQuasisimple H) (hZ : Subgroup.center H = ⊥) :
    SkGood p H := by
  have htop : commutator H = ⊤ := Group.isPerfect_def.mp hq.1
  refine ⟨?_, fun z _ hc n _ => ?_, Or.inr fun w _ => by rw [htop]; exact Subgroup.mem_top w⟩
  · rw [htop]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq
  · have hzc : z ∈ Subgroup.center H :=
      Subgroup.mem_center_iff.2 fun g => (hc g (by rw [htop]; exact Subgroup.mem_top g)).symm
    rw [hZ] at hzc
    exact Subgroup.mem_bot.1 hzc

theorem skBad_of_comm {p : ℕ} (h : ∀ u v : H, u * v = v * u) : SkBad p H := fun u v _ => h u v

theorem skBad_of_coprime [Finite H] {p : ℕ} (hcop : Nat.Coprime p (Nat.card H)) : SkBad p H := by
  intro u v hu
  have h1 : orderOf u ∣ p := orderOf_dvd_of_pow_eq_one hu
  have h2 : orderOf u = 1 := (Nat.Coprime.coprime_dvd_left h1 hcop).eq_one_of_dvd (orderOf_dvd_natCard u)
  rw [orderOf_eq_one_iff.1 h2, one_mul, mul_one]

theorem sk_eq_one_of_pow_two_pow {F : Type*} [Field F] [CharP F 2] {c : F} {k : ℕ} (h : c ^ 2 ^ k = 1) :
    c = 1 := by
  have h1 : (c - 1) ^ 2 ^ k = 0 := by
    rw [sub_pow_char_pow (p := 2), one_pow, h, sub_self]
  exact sub_eq_zero.1 ((pow_eq_zero_iff (pow_ne_zero k two_ne_zero)).1 h1)

end Generic

section GenLin

variable {E : Type} [Field E] [Finite E]

theorem skGood_GL [CharP E 2] {m : ℕ} (hm : 2 ≤ m) (h4 : 4 ≤ Nat.card E) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card E - 1) : SkGood p (GL (Fin m) E) := by
  classical
  have hNq : CFSG.IsQuasisimple ↥(Matrix.GeneralLinearGroup.det : GL (Fin m) E →* Eˣ).ker :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Matrix.SpecialLinearGroup.toGLKerEquiv
      (CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le hm (Or.inr h4))
  have hcomm := sk_commutator_eq_ker (Matrix.GeneralLinearGroup.det : GL (Fin m) E →* Eˣ) hNq.1
  rw [SkGood, hcomm]
  refine ⟨hNq, fun z _ hc n hzn => ?_, Or.inl ?_⟩
  ·
    obtain ⟨c, hc'⟩ : (z : Matrix (Fin m) (Fin m) E) ∈ Set.range (Matrix.scalar (Fin m)) := by
      refine Matrix.mem_range_scalar_of_commute_transvectionStruct fun t => ?_
      have ht : (⟨t.toMatrix, t.inv.toMatrix, t.mul_inv, t.inv_mul⟩ : GL (Fin m) E) ∈
          (Matrix.GeneralLinearGroup.det : GL (Fin m) E →* Eˣ).ker := by
        rw [MonoidHom.mem_ker]
        exact Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]; exact t.det)
      have h1 := congrArg Units.val (hc _ ht)
      rw [Units.val_mul, Units.val_mul] at h1
      exact h1.symm
    haveI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
    have hz1 : (z : Matrix (Fin m) (Fin m) E) ^ 2 ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, hzn, Units.val_one]
    rw [← hc', ← map_pow, ← (Matrix.scalar (Fin m)).map_one, Matrix.scalar_inj] at hz1
    have hc1 : c = 1 := sk_eq_one_of_pow_two_pow hz1
    refine Units.ext ?_
    rw [← hc', hc1, map_one, Units.val_one]
  ·
    obtain ⟨g, hg⟩ := SD.Lin.exists_orderOf_eq_of_dvd_units hm hp hpq
    rw [← Nat.card_congr Matrix.SpecialLinearGroup.toGLKerEquiv.toEquiv, ← hg]
    exact orderOf_dvd_natCard g

theorem skBad_GL_of_le_one {m : ℕ} (hm : m ≤ 1) (p : ℕ) : SkBad p (GL (Fin m) E) := by
  refine skBad_of_comm fun u v => ?_
  haveI : Subsingleton (Fin m) := Fin.subsingleton_iff_le_one.2 hm
  apply Units.ext
  ext i j
  obtain rfl : j = i := Subsingleton.elim j i
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_subsingleton _ j,
    Fintype.sum_subsingleton _ j, mul_comm]

end GenLin

section GU

variable {f' : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData 2 f' E) {W : Type*} [AddCommGroup W]
  [Module E W] [FiniteDimensional E W] {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E}

include hE in
theorem skGood_GU (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft) (hm : 2 ≤ finrank E W)
    (hQ : 4 ≤ 2 ^ f') {p : ℕ} (hp : p.Prime) (hpQ : p ∣ 2 ^ f' + 1) : SkGood p ↥(sesqUnitaryGroup Hf) := by
  classical
  haveI : CharP E 2 := hE.charP
  have hq : (finrank E W = 2 → 4 ≤ 2 ^ f') ∧ (finrank E W = 3 → 3 ≤ 2 ^ f') :=
    ⟨fun _ => hQ, fun _ => by omega⟩
  obtain ⟨-, hSU, -, -, hker, -, -⟩ :=
    CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl rfl (by omega : 1 ≤ finrank E W)
  have hSUq : CFSG.IsQuasisimple ↥(sesqSpecialUnitaryGroup Hf) :=
    CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hE hHf hHfl hm hq
  have hNq : CFSG.IsQuasisimple ↥(CFSG.LinearGroups.unitaryDet Hf).ker := by
    rw [hker]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)).symm hSUq
  have hcomm := sk_commutator_eq_ker (CFSG.LinearGroups.unitaryDet Hf) hNq.1
  rw [SkGood, hcomm]
  refine ⟨hNq, fun z _ hc n hzn => ?_, Or.inl ?_⟩
  ·
    set γ : Module.End E W := ((z : LinearMap.GeneralLinearGroup E W) : Module.End E W) with hγ
    have hcomm' : ∀ δ ∈ sesqSpecialUnitaryGroup Hf, Commute γ (δ : Module.End E W) := by
      intro δ hδ
      have hδ' : (⟨δ, sesqSpecialUnitaryGroup_le Hf hδ⟩ : ↥(sesqUnitaryGroup Hf)) ∈
          (CFSG.LinearGroups.unitaryDet Hf).ker := by
        rw [hker, Subgroup.mem_subgroupOf]
        exact hδ
      have h1 := congrArg (fun g : ↥(sesqUnitaryGroup Hf) =>
        ((g : LinearMap.GeneralLinearGroup E W) : Module.End E W)) (hc _ hδ')
      have h2 : ((z : LinearMap.GeneralLinearGroup E W) : Module.End E W) * (δ : Module.End E W) =
          (δ : Module.End E W) * ((z : LinearMap.GeneralLinearGroup E W) : Module.End E W) := by
        simpa [Subgroup.coe_mul, Units.val_mul] using h1
      exact h2
    obtain ⟨c, hcw⟩ := CFSG.RankThree.PartOne.KCUnitary.exists_smul_of_commute_special_unitary hE hHf hHfl
      hm (by omega) γ hcomm'
    haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (R := E) (by omega)
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    have hγpow : ∀ k : ℕ, (γ ^ k) w = c ^ k • w := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, Module.End.mul_apply, hcw, map_smul, ih, smul_smul, pow_succ, mul_comm]
    have hz1 : γ ^ 2 ^ n = 1 := by
      have h2 := congrArg (fun g : ↥(sesqUnitaryGroup Hf) =>
        ((g : LinearMap.GeneralLinearGroup E W) : Module.End E W)) hzn
      simpa [hγ, Subgroup.coe_pow, Units.val_pow_eq_pow_val] using h2
    have h3 : (c ^ 2 ^ n - 1) • w = 0 := by
      rw [sub_smul, one_smul, ← hγpow, hz1, Module.End.one_apply, sub_self]
    have hc1 : c = 1 := sk_eq_one_of_pow_two_pow (sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right hw))
    have hγ1 : γ = 1 := LinearMap.ext fun v => by rw [hcw, hc1, one_smul, Module.End.one_apply]
    exact Subtype.ext (Units.ext hγ1)
  ·
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)).toEquiv]
    have hpz : (p : ℤ) ∣ ((2 ^ f' : ℕ) : ℤ) ^ 2 - (-1) ^ 2 := by
      have h1 : (p : ℤ) ∣ ((2 ^ f' : ℕ) : ℤ) + 1 := by exact_mod_cast Int.natCast_dvd_natCast.2 hpQ
      have h2 : ((2 ^ f' : ℕ) : ℤ) ^ 2 - (-1) ^ 2 = (((2 ^ f' : ℕ) : ℤ) - 1) * (((2 ^ f' : ℕ) : ℤ) + 1) := by
        ring
      rw [h2]
      exact dvd_mul_of_dvd_right h1 _
    have hmem : 2 ∈ Finset.Icc 2 (finrank E W) := Finset.mem_Icc.2 ⟨le_rfl, hm⟩
    have hdvd : (p : ℤ) ∣ (Nat.card ↥(sesqSpecialUnitaryGroup Hf) : ℤ) := by
      rw [hSU]
      exact dvd_mul_of_dvd_right
        (hpz.trans (Finset.dvd_prod_of_mem (fun i => ((2 ^ f' : ℕ) : ℤ) ^ i - (-1) ^ i) hmem)) _
    exact Int.natCast_dvd_natCast.1 hdvd

theorem skBad_GU_of_le_one (hm : finrank E W ≤ 1) (p : ℕ) : SkBad p ↥(sesqUnitaryGroup Hf) := by
  refine skBad_of_comm fun u v => Subtype.ext (Units.ext ?_)
  have := (CFSG.RankThree.PartOne.KCUnitary.End_commute_of_finrank_le_one (E := E) (W := W) hm
    ((u : LinearMap.GeneralLinearGroup E W) : Module.End E W)
    ((v : LinearMap.GeneralLinearGroup E W) : Module.End E W)).eq
  simpa [Subgroup.coe_mul, Units.val_mul] using this

end GU

section Sp

variable {K : Type} [Field K] [Finite K]

theorem sk_center_statedSp [CharP K 2] {s : ℕ} [NeZero s] : Subgroup.center ↥(StatedSp s K) = ⊥ := by
  rw [CFSG.LieType.Universal.Symplectic.center_eq]
  exact UnitaryHigher.spScalars_eq_bot_of_charTwo

theorem sk_card_eq_two_of_lt_four [CharP K 2] (h : Nat.card K < 4) : Nat.card K = 2 := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hn] at h ⊢
  have hn1 : 1 ≤ (n : ℕ) := n.pos
  have hn2 : (n : ℕ) < 2 := by
    by_contra h2
    push Not at h2
    have : 2 ^ 2 ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) h2
    omega
  rw [show (n : ℕ) = 1 by omega, pow_one]

theorem skGood_statedSp [CharP K 2] {s : ℕ} (hs : 1 ≤ s) (hK : 4 ≤ Nat.card K ∨ 3 ≤ s) (p : ℕ) :
    SkGood p ↥(StatedSp s K) := by
  haveI : NeZero s := ⟨by omega⟩
  refine skGood_of_quasisimple (CFSG.LieType.Universal.Symplectic.isQuasisimple s K hs ?_) sk_center_statedSp
  by_cases h4 : 4 ≤ Nat.card K
  · exact Or.inl (Or.inr h4)
  · exact Or.inr (Or.inr ⟨sk_card_eq_two_of_lt_four (by omega), hK.resolve_left h4⟩)

theorem skBad_statedSp_one (hK2 : Nat.card K = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    SkBad p ↥(StatedSp 1 K) := by
  refine skBad_of_coprime ?_
  have h6 : Nat.card ↥(StatedSp 1 K) = 2 * 3 := by
    rw [SymplecticFlag.card_statedSp, hK2]
    norm_num [Finset.Icc_self]
  rw [h6]
  exact Nat.Coprime.mul_right ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    ((Nat.coprime_primes hp Nat.prime_three).2 hp3)

open CFSG.ComponentClassification.PresentationLocal in
theorem skGood_sympFour {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : SkGood p ↥sympFour := by
  obtain ⟨hq, hin⟩ := CFSG.RankThree.PartOne.derived_of_mulEquiv_sympFour (MulEquiv.refl ↥sympFour)
  refine ⟨hq, fun z hz hc n _ => ?_, Or.inr fun w hw => hin hp hp2 w hw⟩
  haveI := isSimpleGroup_commutator_sympFour
  have hZ : Subgroup.center ↥(commutator ↥sympFour) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(commutator ↥sympFour)) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hq.2.2
      apply hab
      induction a using QuotientGroup.induction_on with
      | H a =>
        induction b using QuotientGroup.induction_on with
        | H b =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, h]
          exact Subgroup.mem_top _
  have hzc : (⟨z, hz⟩ : ↥(commutator ↥sympFour)) ∈ Subgroup.center ↥(commutator ↥sympFour) :=
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (hc g g.2).symm
  rw [hZ] at hzc
  exact congrArg Subtype.val (Subgroup.mem_bot.1 hzc)

theorem sk_goodOrBad_alt [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Nontrivial V] {B : LinearMap.BilinForm K V} (hB : B.IsAlt) (hn : B.Nondegenerate) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK3 : p = 3 → 4 ≤ Nat.card K) :
    SkGood p ↥(sesqUnitaryGroup B) ∨ SkBad p ↥(sesqUnitaryGroup B) := by
  obtain ⟨s, hs, ⟨e⟩⟩ := CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp hB hn
  have hs1 : 1 ≤ s := by
    have := Module.finrank_pos (R := K) (M := V)
    omega
  by_cases h4 : 4 ≤ Nat.card K
  · exact Or.inl (skGood_of_mulEquiv e (skGood_statedSp hs1 (Or.inl h4) p))
  · have hK2 : Nat.card K = 2 := sk_card_eq_two_of_lt_four (by omega)
    have hp3 : p ≠ 3 := fun h => h4 (hK3 h)
    rcases (show s = 1 ∨ s = 2 ∨ 3 ≤ s by omega) with rfl | rfl | h3
    · exact Or.inr (skBad_of_mulEquiv e (skBad_statedSp_one hK2 hp hp2 hp3))
    · obtain ⟨e4⟩ := CFSG.RankThree.PartOne.nonempty_mulEquiv_sympFour hK2 hB hn (by omega)
      exact Or.inl (skGood_of_mulEquiv e4 (skGood_sympFour hp hp2))
    · exact Or.inl (skGood_of_mulEquiv e (skGood_statedSp hs1 (Or.inr h3) p))

end Sp

end CFSG.LocalAnalysis.GLTheoremA.T263.SK

end
