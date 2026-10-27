module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2323b
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearUnitaryComps
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141d2
import all CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympInner
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympFieldExport
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympAut
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryFieldExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthInnerExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthFieldExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthAssembly
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SymplecticOrthogonalComps
import CFSG.RankThree.PartOne.S11d.OrthSubfieldDickson
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSRT
import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311c2
import CFSG.LieType.SeitzGeneration.OuterLinearTwo
import CFSG.RankThree.PartOne.SEITZ10.SzMain
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearAut

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2323b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.CALinearPrimary
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup PerfectInLayer)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (glA specialFactor IsGoodFactor
  squarefree_minpoly_glA mem_fixSubgroup_slConjugation_iff specialFactor_le_fixSubgroup)

section Small

theorem coprime_two_pow_mul_three_pow {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (a b : ℕ) :
    Nat.Coprime p (2 ^ a * 3 ^ b) := by
  refine Nat.Coprime.mul_right (Nat.Coprime.pow_right a ?_) (Nat.Coprime.pow_right b ?_)
  · exact (Nat.coprime_primes hp Nat.prime_two).2 (by omega)
  · exact (Nat.coprime_primes hp Nat.prime_three).2 (by omega)

theorem coprime_card_specialLinearGroup_small {E : Type} [Field E] [Finite E] {m : ℕ}
    (hm : m ≤ 1 ∨ (m = 2 ∧ Nat.card E ≤ 3)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    Nat.Coprime p (Nat.card (Matrix.SpecialLinearGroup (Fin m) E)) := by
  classical
  haveI := Fintype.ofFinite E
  have hq : Nat.card E = Fintype.card E := Nat.card_eq_fintype_card
  have hq2 : 2 ≤ Fintype.card E := by
    have := Finite.one_lt_card (α := E)
    omega
  rcases hm with hm | ⟨rfl, hE⟩
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm with rfl | rfl
    · have h1 : Nat.card (Matrix.SpecialLinearGroup (Fin 0) E) = 1 := by
        rw [Nat.card_eq_one_iff_unique]
        refine ⟨⟨fun a b => Subtype.ext (Matrix.ext fun i => Fin.elim0 i)⟩, ⟨1⟩⟩
      rw [h1]
      exact Nat.coprime_one_right p
    · have h1 : Nat.card (Matrix.SpecialLinearGroup (Fin 1) E) = 1 := by
        rw [Matrix.card_SL_field (𝔽 := E) 1]
        simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.val_zero, pow_zero, pow_one,
          Finset.prod_singleton]
        exact Nat.div_self (by omega)
      rw [h1]
      exact Nat.coprime_one_right p
  · rw [Matrix.card_SL_field (𝔽 := E) 2, Fin.prod_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    have hE' : Fintype.card E = 2 ∨ Fintype.card E = 3 := by omega
    rcases hE' with h | h
    · rw [h]
      exact coprime_two_pow_mul_three_pow hp hp5 1 1
    · rw [h]
      exact coprime_two_pow_mul_three_pow hp hp5 3 1

theorem commutator_eq_self_of_isQuasisimple {G : Type*} [Group G] {H : Subgroup G} (hH : CFSG.IsQuasisimple ↥H) :
    ⁅H, H⁆ = H := by
  have h1 : commutator ↥H = ⊤ := Group.isPerfect_def.mp hH.1
  have h2 : (commutator ↥H).map H.subtype = ⁅H, H⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← h2, h1, Subgroup.map_top, Subgroup.range_subtype]

end Small

section Linear

variable {n : ℕ} {k : Type} [Field k] [Finite k] [CharP k 2]

theorem twoInCoreLayer_conjAut (hn : 1 ≤ n) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {A : GL (Fin n) k} {c : kˣ}
    (hA : A ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    TwoInCoreLayer p (LinearFlag.conjAut n k A) := by
  classical
  have hpk : (p : k) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff k 2] at h0
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h0
    omega
  have hsq := squarefree_minpoly_glA hpk hA
  have hαβ : ∀ x, LinearFlag.proj n k (CatalogueBHigherLinearAction.slConjugation n k A x) =
      LinearFlag.conjAut n k A (LinearFlag.proj n k x) := fun x => (LinearFlag.conjAut_proj A x).symm
  refine twoInCoreLayer_of_cover (LinearFlag.proj n k) (LinearFlag.proj_surjective n k)
    Inputs141c.ker_proj_le_center (Inputs141c.coprime_two_card_ker_proj hn) _ _ hαβ hp
    (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_conjAut hpk hA)
    (fun b : primaryFactors (glA A : Module.End k (Fin n → k)) => specialFactor A b)
    (fun b => specialFactor_le_fixSubgroup A b) (fun b => ?_) ?_
  · by_cases hgood : IsGoodFactor A b
    · left
      exact commutator_eq_self_of_isQuasisimple
        (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isQuasisimple_specialFactor hsq b.2 hgood)
    · right
      refine ⟨?_, fun c hc g hg =>
        CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.conj_mem_specialFactor hc hg⟩
      obtain ⟨e⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_mulEquiv_specialFactor hsq b.2
      rw [← Nat.card_congr e.toEquiv]
      haveI : Fact (Irreducible (b : k[X])) := ⟨irreducible_of_mem_primaryFactors b.2⟩
      haveI : Finite (AdjoinRoot (b : k[X])) := Module.finite_of_finite k
      refine coprime_card_specialLinearGroup_small ?_ hp hp5
      unfold IsGoodFactor at hgood
      omega
  · intro g hg hg2
    obtain ⟨m, hm⟩ := hg2 ⟨g, Subgroup.mem_zpowers g⟩
    have hgm : (⟨g, hg⟩ : ↥(fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A))) ^ (2 ^ m) = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hm)
    exact Inputs141c.mem_iSup_specialFactor_of_two hsq ⟨g, hg⟩ hgm

theorem twoInCoreLayer_fieldAut (hn : 2 ≤ n) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (σ : k ≃+* k)
    (hσ : orderOf σ = p) : TwoInCoreLayer p (LinearFlag.fieldAut n k σ) := by
  classical
  have hαβ : ∀ x, LinearFlag.proj n k (CatalogueBHigherLinearField.slFieldAut (Fin n) k σ x) =
      LinearFlag.fieldAut n k σ (LinearFlag.proj n k x) :=
    fun x => (LinearFlag.descendAut_proj n k _ x).symm
  have hlay : PerfectInLayer (LinearFlag.fieldAut n k σ) := by
    rcases Nat.lt_or_ge n 3 with h | h
    · obtain rfl : n = 2 := by omega
      exact CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_fieldAut_two σ
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_fieldAut h hp (by omega) σ hσ
  have hk : ∀ x, x ∈ CFSG.GH74.GLS.IVK.fixedField σ ↔ σ x = x := CFSG.GH74.GLS.IVK.mem_fixedField_iff σ
  have hC := Inputs141c.fixSubgroup_slFieldAut_eq_range' (n := n) hk
  let e : Matrix.SpecialLinearGroup (Fin n) (CFSG.GH74.GLS.IVK.fixedField σ) ≃*
      ↥(fixSubgroup (CatalogueBHigherLinearField.slFieldAut (Fin n) k σ)) :=
    (MonoidHom.ofInjective (Inputs141c.injective_map_subtype' _)).trans (MulEquiv.subgroupCongr hC.symm)
  refine twoInCoreLayer_of_cover (LinearFlag.proj n k) (LinearFlag.proj_surjective n k)
    Inputs141c.ker_proj_le_center (Inputs141c.coprime_two_card_ker_proj (by omega)) _ _ hαβ hp hlay
    (fun _ : Unit => fixSubgroup (CatalogueBHigherLinearField.slFieldAut (Fin n) k σ)) (fun _ => le_rfl)
    (fun _ => ?_) (fun g hg _ => Subgroup.mem_iSup_of_mem () hg)
  by_cases hperf : 3 ≤ n ∨ 4 ≤ Nat.card (CFSG.GH74.GLS.IVK.fixedField σ)
  · left
    exact commutator_eq_self_of_isQuasisimple (CFSG.LocalCores.isQuasisimple_of_mulEquiv e
      (CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le hn hperf))
  · right
    refine ⟨?_, fun c hc g hg => (fixSubgroup _).mul_mem ((fixSubgroup _).mul_mem hc hg) ((fixSubgroup _).inv_mem hc)⟩
    rw [← Nat.card_congr e.toEquiv]
    exact coprime_card_specialLinearGroup_small (by omega) hp hp5

theorem twoInCoreLayer_projectiveSL (hn : 2 ≤ n) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (β : MulAut (LinearFlag.projectiveSL n k)) (hβ : β ^ p = 1) : TwoInCoreLayer p β := by
  have hcases : (∃ (A : GL (Fin n) k) (c : kˣ), A ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c ∧
      β = LinearFlag.conjAut n k A) ∨
      (∃ (h : MulAut (LinearFlag.projectiveSL n k)) (σ : k ≃+* k), orderOf σ = p ∧
        β = h * LinearFlag.fieldAut n k σ * h⁻¹) := by
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · obtain rfl : n = 2 := by omega
      exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.linear_cases_two hp β hβ
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.linear_cases_of_three_le hp (by omega) hn3 β hβ
  rcases hcases with ⟨A, c, hA, rfl⟩ | ⟨h, σ, hσ, rfl⟩
  · exact twoInCoreLayer_conjAut (by omega) hp hp5 hA
  · refine twoInCoreLayer_of_conj h⁻¹ hp ?_
    have e1 : h⁻¹ * (h * LinearFlag.fieldAut n k σ * h⁻¹) * h⁻¹⁻¹ = LinearFlag.fieldAut n k σ := by group
    rw [e1]
    exact twoInCoreLayer_fieldAut hn hp hp5 σ hσ

theorem input14_1BadSimpleOn_linear :
    Input14_1BadSimpleOn fun _ d => ∃ r q, d = TauCeti.LieTypeIndex.A r q := by
  intro p hp hp5 S _ _ _ _ d hd hchar he β hβp _
  obtain ⟨d, hv⟩ := d
  obtain ⟨r, q, rfl⟩ := hd
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hq2 : q.p = 2 := by
    have h1 : (TauCeti.LieTypeIndex.A r q).characteristic = q.p := TauCeti.LieTypeIndex.characteristic_A r q
    rw [← h1]
    exact hchar
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  obtain ⟨e⟩ := he
  let e' : S ≃* LinearFlag.projectiveSL (r + 1) (GaloisField q.p q.exponent) :=
    e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) _))
  haveI : CharP (GaloisField q.p q.exponent) 2 := by
    rw [← hq2]
    infer_instance
  refine twoInCoreLayer_of_congr e' hp (twoInCoreLayer_projectiveSL (by omega) hp hp5 _ ?_)
  rw [← map_pow, hβp, map_one]

end Linear

section TwoGood

@[expose] def TwoGood (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∃ M : Subgroup G, M.Normal ∧ (∀ g : G, IsPGroup 2 ↥(Subgroup.zpowers g) → g ∈ M) ∧
    (⁅M, M⁆ = M ∨ Nat.Coprime p (Nat.card M))

theorem twoGood_of_mulEquiv {G H : Type*} [Group G] [Group H] {p : ℕ} (e : G ≃* H) (h : TwoGood p H) :
    TwoGood p G := by
  obtain ⟨M, hMn, h2, hM⟩ := h
  refine ⟨M.map e.symm.toMonoidHom, hMn.map _ e.symm.surjective, fun g hg => ?_, ?_⟩
  · have hg' : IsPGroup 2 ↥(Subgroup.zpowers (e g)) := by
      have h1 := hg.map e.toMonoidHom
      rwa [MonoidHom.map_zpowers] at h1
    exact ⟨e g, h2 (e g) hg', by simp⟩
  · rcases hM with hM | hM
    · left
      rw [← Subgroup.map_commutator, hM]
    · right
      rwa [Subgroup.card_map_of_injective e.symm.injective]

theorem twoGood_of_perfect {G : Type*} [Group G] {p : ℕ} (h : commutator G = ⊤) : TwoGood p G :=
  ⟨⊤, Subgroup.normal_top, fun g _ => Subgroup.mem_top g, Or.inl (by rw [← commutator_def, h])⟩

theorem twoGood_of_coprime {G : Type*} [Group G] {p : ℕ} (h : Nat.Coprime p (Nat.card G)) : TwoGood p G :=
  ⟨⊤, Subgroup.normal_top, fun g _ => Subgroup.mem_top g, Or.inr (by rwa [Subgroup.card_top])⟩

theorem twoGood_of_odd {G : Type*} [Group G] [Finite G] {p : ℕ} (h : Odd (Nat.card G)) : TwoGood p G := by
  refine ⟨⊥, Subgroup.normal_bot, fun g hg => ?_, Or.inl (Subgroup.commutator_bot_left ⊥)⟩
  obtain ⟨k, hk⟩ := hg ⟨g, Subgroup.mem_zpowers g⟩
  have hgk : g ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hgk
  have h2 : orderOf g ∣ Nat.card G := orderOf_dvd_natCard g
  have h3 : Nat.Coprime (2 ^ k) (Nat.card G) := Nat.Coprime.pow_left k (Nat.coprime_two_left.2 h)
  rw [Subgroup.mem_bot, ← orderOf_eq_one_iff]
  exact Nat.eq_one_of_dvd_coprimes h3 h1 h2

theorem twoGood_generalLinearGroup {E W : Type} [Field E] [Finite E] [CharP E 2] [AddCommGroup W]
    [Module E W] [FiniteDimensional E W] (p : ℕ) (h4 : 3 ≤ Module.finrank E W ∨ ∃ s : Finset E, s.card = 4) :
    TwoGood p (LinearMap.GeneralLinearGroup E W) := by
  classical
  by_cases hm : 2 ≤ Module.finrank E W
  · have hq := CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_ker_det hm h4
    refine ⟨(Units.map (LinearMap.det : Module.End E W →* E)).ker, inferInstance, fun g hg => ?_,
      Or.inl (commutator_eq_self_of_isQuasisimple hq)⟩
    obtain ⟨m, hm'⟩ := Inputs141d.exists_pow_eq_one_of_isPGroup hg
    rw [MonoidHom.mem_ker]
    exact Units.ext (Inputs141d.det_eq_one_of_pow_two hm')
  · apply twoGood_of_odd
    haveI := Fintype.ofFinite E
    obtain ⟨m, hm'⟩ : ∃ m, Module.finrank E W = m := ⟨_, rfl⟩
    let b : Module.Basis (Fin m) E W := Module.finBasisOfFinrankEq E W hm'
    let e : LinearMap.GeneralLinearGroup E W ≃* GL (Fin m) E :=
      (LinearMap.GeneralLinearGroup.congrLinearEquiv b.equivFun).trans Matrix.GeneralLinearGroup.toLin.symm
    rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field]
    obtain ⟨n, -, hn⟩ := FiniteField.card E 2
    have hn1 : 1 ≤ (n : ℕ) := n.2
    rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
    · simp
    · simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.val_zero, pow_zero, pow_one,
        Finset.prod_singleton, hn]
      have h2 : Even (2 ^ (n : ℕ)) := (Nat.even_pow' (by omega)).2 even_two
      have h3 : 1 ≤ 2 ^ (n : ℕ) := Nat.one_le_two_pow
      exact Nat.Even.sub_odd h3 h2 odd_one

open CFSG.LocalAnalysis.ComponentInitial in
theorem twoGood_sesqUnitaryGroup {f' : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData 2 f' E) {W : Type}
    [AddCommGroup W] [Module E W] [FiniteDimensional E W] {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : TwoGood p ↥(sesqUnitaryGroup Hf) := by
  haveI : CharP E 2 := hE.charP
  haveI : Finite E := hE.finite
  have hf1 : 1 ≤ f' := hE.one_le
  have hq2 : 2 ≤ 2 ^ f' := by
    have := Nat.one_lt_pow (by omega : f' ≠ 0) (by norm_num : 1 < 2)
    omega
  have : Finite (LinearMap.GeneralLinearGroup E W) := by
    have : Finite W := Module.finite_of_finite E
    have : Finite (Module.End E W) := Finite.of_injective _ (DFunLike.coe_injective (F := W →ₗ[E] W))
    exact Finite.of_injective _ Units.val_injective
  by_cases hm : 2 ≤ Module.finrank E W
  · by_cases hq : (Module.finrank E W = 2 → 4 ≤ 2 ^ f') ∧ (Module.finrank E W = 3 → 3 ≤ 2 ^ f')
    · have hSU := CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hE hHf hHfl hm hq
      have hSU' : CFSG.IsQuasisimple ↥((sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf)) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv
          (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)).symm hSU
      have hnorm : ((sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf)).Normal := by
        rw [sesqSpecialUnitaryGroup, Subgroup.inf_subgroupOf_left]
        infer_instance
      refine ⟨(sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf), hnorm, fun g hg => ?_,
        Or.inl (commutator_eq_self_of_isQuasisimple hSU')⟩
      · obtain ⟨m, hm'⟩ := Inputs141d.exists_pow_eq_one_of_isPGroup hg
        have hm'' : (g : LinearMap.GeneralLinearGroup E W) ^ (2 ^ m) = 1 := by
          simpa using congrArg Subtype.val hm'
        exact Subgroup.mem_subgroupOf.2 (mem_sesqSpecialUnitaryGroup.2 ⟨g.2, Inputs141d.det_eq_one_of_pow_two hm''⟩)
    · apply twoGood_of_coprime
      obtain ⟨hcard, -, -, -, -, -⟩ := CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl rfl
        (by omega : 1 ≤ Module.finrank E W)
      have hexc : (Module.finrank E W = 2 ∧ 2 ^ f' = 2) ∨ (Module.finrank E W = 3 ∧ 2 ^ f' = 2) := by
        have h2f : 2 ^ f' = 2 ∨ 4 ≤ 2 ^ f' := by
          rcases Nat.lt_or_ge f' 2 with hf | hf
          · left
            obtain rfl : f' = 1 := by omega
            norm_num
          · right
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ f' := Nat.pow_le_pow_right (by norm_num) hf
        by_contra hn
        push Not at hn
        apply hq
        refine ⟨fun h2' => ?_, fun h3' => ?_⟩
        · rcases h2f with h | h
          · exact absurd h (hn.1 h2')
          · exact h
        · rcases h2f with h | h
          · exact absurd h (hn.2 h3')
          · omega
      rcases hexc with ⟨hm2, hQ⟩ | ⟨hm3, hQ⟩
      · rw [hm2, hQ] at hcard
        have e : ((2 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
            ∏ i ∈ Finset.Icc 1 2, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 18 := by decide +kernel
        have h18 : Nat.card ↥(sesqUnitaryGroup Hf) = 18 := by exact_mod_cast hcard.trans e
        rw [h18, show (18 : ℕ) = 2 ^ 1 * 3 ^ 2 by norm_num]
        exact coprime_two_pow_mul_three_pow hp hp5 1 2
      · rw [hm3, hQ] at hcard
        have e : ((2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
            ∏ i ∈ Finset.Icc 1 3, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 648 := by decide +kernel
        have h648 : Nat.card ↥(sesqUnitaryGroup Hf) = 648 := by exact_mod_cast hcard.trans e
        rw [h648, show (648 : ℕ) = 2 ^ 3 * 3 ^ 4 by norm_num]
        exact coprime_two_pow_mul_three_pow hp hp5 3 4
  · apply twoGood_of_odd
    rcases (show Module.finrank E W = 0 ∨ Module.finrank E W = 1 by omega) with h0 | h1
    · have : Subsingleton W := Module.finrank_zero_iff.1 h0
      have : Subsingleton ↥(sesqUnitaryGroup Hf) := by
        refine ⟨fun a b => Subtype.ext (Units.ext (LinearMap.ext fun w => Subsingleton.elim _ _))⟩
      rw [Nat.card_unique]
      exact odd_one
    · obtain ⟨hcard, -, -, -, -, -⟩ := CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl h1 le_rfl
      simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_div, pow_zero, one_mul, Finset.Icc_self,
        Finset.prod_singleton, pow_one] at hcard
      have h2 : (Nat.card ↥(sesqUnitaryGroup Hf) : ℤ) = ((2 ^ f' + 1 : ℕ) : ℤ) := by
        rw [hcard]
        push_cast
        ring
      rw [Nat.cast_inj.1 h2]
      have : Even (2 ^ f') := (Nat.even_pow' (by omega)).2 even_two
      exact this.add_one

theorem twoGood_statedSp (s : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : 7 ≤ p ∨ 4 ≤ Nat.card K) : TwoGood p ↥(StatedSp s K) := by
  have hcard := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := K) s
  have hK2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
  have hK3 : Nat.card K ≠ 3 := by
    intro h
    haveI : Fintype K := Fintype.ofFinite K
    have h2 := FiniteField.cast_card_eq_zero K
    rw [Fintype.card_eq_nat_card, h] at h2
    have h3' : ((3 : ℕ) : K) = 1 := by
      have : ((2 : ℕ) : K) = 0 := CharP.cast_eq_zero K 2
      rw [show (3 : ℕ) = 2 + 1 by norm_num, Nat.cast_add, this, zero_add, Nat.cast_one]
    rw [h3'] at h2
    exact one_ne_zero h2
  by_cases hs : 1 ≤ s
  · by_cases hq : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ s) ∨ (Nat.card K = 2 ∧ 3 ≤ s)
    · exact twoGood_of_perfect (Group.isPerfect_def.mp (CFSG.LieType.Universal.Symplectic.isQuasisimple s K hs hq).1)
    · apply twoGood_of_coprime
      have hK4 : Nat.card K = 2 := by
        by_contra h
        exact hq (Or.inl (Or.inr (by omega)))
      rcases (show s = 1 ∨ s = 2 by
          by_contra h
          exact hq (Or.inr (Or.inr ⟨hK4, by omega⟩))) with rfl | rfl
      · rw [hcard, hK4, show 2 ^ 1 ^ 2 * ∏ j ∈ Finset.Icc 1 1, (2 ^ (2 * j) - 1) = 2 ^ 1 * 3 ^ 1 by decide]
        exact coprime_two_pow_mul_three_pow hp hp5 1 1
      · have hp7 : 7 ≤ p := hK.resolve_right (by omega)
        rw [hcard, hK4, show 2 ^ 2 ^ 2 * ∏ j ∈ Finset.Icc 1 2, (2 ^ (2 * j) - 1) = 720 by decide]
        rw [show (720 : ℕ) = 2 ^ 4 * 3 ^ 2 * 5 by norm_num]
        refine Nat.Coprime.mul_right (coprime_two_pow_mul_three_pow hp hp5 4 2) ?_
        exact (Nat.coprime_primes hp Nat.prime_five).2 (by omega)
  · apply twoGood_of_coprime
    obtain rfl : s = 0 := by omega
    rw [hcard]
    simp

end TwoGood

section Family

theorem fixSubgroup_conj_eq_centralizer' {X : Type*} [Group X] (x : X) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set X) := by
  ext g
  rw [mem_fixSubgroup, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * x = x * g * x⁻¹ * x := by rw [h]
      _ = x * g := by group
  · intro h
    rw [← h]
    group

theorem conj_mem_map_of_family {G : Type*} [Group G] {ι : Type*} (A : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b) {i : ι} {M : Subgroup ↥(A i)} (hM : M.Normal)
    {c : G} (hcmem : c ∈ ⨆ j, A j) {b : G} (hb : b ∈ M.map (A i).subtype) : c * b * c⁻¹ ∈ M.map (A i).subtype := by
  refine Subgroup.iSup_induction A (C := fun c => ∀ b ∈ M.map (A i).subtype, c * b * c⁻¹ ∈ M.map (A i).subtype)
    hcmem ?_ ?_ ?_ b hb
  · intro j c hcj b hb
    by_cases hij : i = j
    · subst hij
      obtain ⟨b', hb', rfl⟩ := hb
      exact ⟨⟨c, hcj⟩ * b' * ⟨c, hcj⟩⁻¹, hM.conj_mem b' hb' _, rfl⟩
    · have hcb : Commute c b := hc j i (Ne.symm hij) c hcj b (Subgroup.map_subtype_le _ hb)
      rw [hcb.eq, mul_inv_cancel_right]
      exact hb
  · intro b hb
    simpa using hb
  · intro c d hc' hd' b hb
    have e : c * d * b * (c * d)⁻¹ = c * (d * b * d⁻¹) * c⁻¹ := by group
    rw [e]
    exact hc' _ (hd' b hb)

theorem twoInCoreLayer_conj_of_family {X T : Type} [Group X] [Group T] [Finite X] [Finite T] (π : X →* T)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center X) (hodd : Nat.Coprime 2 (Nat.card π.ker))
    {p : ℕ} (hp : p.Prime) (x : X) (hlay : PerfectInLayer (MulAut.conj (π x))) {ι : Type} [Finite ι]
    (A : ι → Subgroup X) (hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b)
    (hjoin : ⨆ i, A i = Subgroup.centralizer ({x} : Set X)) (h2 : ∀ i, TwoGood p ↥(A i)) :
    TwoInCoreLayer p (MulAut.conj (π x)) := by
  classical
  choose M hMn hM2 hM using h2
  set B : ι → Subgroup X := fun i => (M i).map (A i).subtype with hBdef
  have hfix : fixSubgroup (MulAut.conj x) = ⨆ i, A i := by
    rw [hjoin, fixSubgroup_conj_eq_centralizer']
  have hBA : ∀ i, B i ≤ A i := fun i => Subgroup.map_subtype_le _
  have hαβ : ∀ g, π (MulAut.conj x g) = MulAut.conj (π x) (π g) := fun g => by
    simp only [MulAut.conj_apply, map_mul, map_inv]
  refine twoInCoreLayer_of_cover π hπ hker hodd (MulAut.conj x) (MulAut.conj (π x)) hαβ hp hlay B
    (fun i => (hBA i).trans (hfix ▸ le_iSup A i)) (fun i => ?_) ?_
  · rcases hM i with hperf | hcop
    · left
      show ⁅(M i).map (A i).subtype, (M i).map (A i).subtype⁆ = (M i).map (A i).subtype
      rw [← Subgroup.map_commutator, hperf]
    · right
      refine ⟨by rwa [Subgroup.card_map_of_injective (A i).subtype_injective], fun c hcmem b hb => ?_⟩
      rw [hfix] at hcmem
      exact conj_mem_map_of_family A hc (hMn i) hcmem hb
  · intro g hg hg2
    rw [hfix] at hg
    refine Inputs141d.mem_iSup_of_two A B hc (fun i y hy hy2 => ?_) hg hg2
    obtain ⟨m, hm⟩ := Inputs141d.exists_pow_eq_one_of_isPGroup hy2
    have hy2' : IsPGroup 2 ↥(Subgroup.zpowers (⟨y, hy⟩ : ↥(A i))) :=
      Inputs141d.isPGroup_zpowers_of_pow (m := m) (Subtype.ext (by simpa using hm))
    exact ⟨⟨y, hy⟩, hM2 i _ hy2', rfl⟩

theorem twoInCoreLayer_of_fixSubgroup {S : Type} [Group S] [Finite S] {β : MulAut S} {p : ℕ} (hp : p.Prime)
    (hlay : PerfectInLayer β)
    (h : ⁅fixSubgroup β, fixSubgroup β⁆ = fixSubgroup β ∨ Nat.Coprime p (Nat.card (fixSubgroup β))) :
    TwoInCoreLayer p β := by
  intro x hx _
  rcases h with h | h
  · exact (hlay _ le_rfl h).trans (glaLayer_le_core_sup_layer hp _) hx
  · have h1 : fixSubgroup β ≤ GLAPPrimeCoreOf p (fixSubgroup β) :=
      le_glaPPrimeCoreOf_of_isSubnormal hp (CFSG.Open.IsSubnormal.refl _) h
    exact Subgroup.mem_sup_left (h1 hx)

end Family

section Symplectic

open Polynomial CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldAut)
open CFSG.RankThree.PartOne.KCSpIsotypic (exists_mulEquiv_sesqUnitaryGroup_statedSp)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (exists_finset_card_four_of_paired)

variable {r : ℕ} {K : Type} [Field K]

theorem twoGood_spSupported [Finite K] [CharP K 2] {f p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 2 ≤ 2 ^ f)
    (hK : 7 ≤ p ∨ 4 ≤ Nat.card K) {x : StatedSp r K} {a : StatedProj (StatedSp r K)}
    (blocks : SpPrimaryBlocks 2 f p x a) (O : reciprocalOrbits (spEnd x)) :
    TwoGood p ↥(spSupported x (O : Set K[X])) := by
  obtain ⟨O, h, hh, rfl⟩ := O
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  by_cases hself : CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial h = h
  · have hO : ({h, CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial h} : Set K[X]) = {h} := by
      rw [hself, Set.pair_eq_singleton]
    show TwoGood p ↥(spSupported x {h, CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial h})
    rw [hO]
    by_cases h1 : h = X - 1
    · subst h1
      obtain ⟨φ, -⟩ := blocks.fixedFactor hh
      obtain ⟨s, -, ⟨e⟩⟩ := exists_mulEquiv_sesqUnitaryGroup_statedSp
        (B := (spForm r K).restrict (primaryComponent (spEnd x) (X - 1)))
        (fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)) blocks.fixed_nondegenerate
      exact twoGood_of_mulEquiv (φ.trans e) (twoGood_statedSp s K hp hp5 hK)
    · obtain ⟨d, -, -, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, -⟩ :=
        (blocks.selfDual ⟨h, hh⟩ h1 hself).exists_half
      exact twoGood_of_mulEquiv φ (twoGood_sesqUnitaryGroup hE hHf hHfl hp hp5)
  · have hP := blocks.paired ⟨h, hh⟩ (fun e => hself e.symm)
    obtain ⟨φ, -, -⟩ := hP.factor
    haveI : CharP (AdjoinRoot ((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X])) 2 :=
      charP_of_injective_algebraMap
        (algebraMap K (AdjoinRoot ((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X]))).injective 2
    haveI : Finite (AdjoinRoot ((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X])) := Module.finite_of_finite K
    exact twoGood_of_mulEquiv φ
      (twoGood_generalLinearGroup p (Or.inr (exists_finset_card_four_of_paired (by omega) hq hP)))

theorem twoInCoreLayer_conj_sp [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) (hr : 1 ≤ r) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : 7 ≤ p ∨ 4 ≤ 2 ^ f) (x : StatedSp r K) (hx : x ^ p = 1)
    (hx1 : proj r K x ≠ 1) : TwoInCoreLayer p (MulAut.conj (proj r K x)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  have ha : orderOf (proj r K x) = p := orderOf_eq_prime (by rw [← map_pow, hx, map_one]) hx1
  have hx1' : x ≠ 1 := fun h => hx1 (by rw [h, map_one])
  have hxp : orderOf x = p := orderOf_eq_prime hx hx1'
  have blocks := (symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two hf hK hp
    (by omega) (by omega) hr _ ha).2 x rfl hxp
  have hpK' : ((p : ℕ) : K) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff K 2] at h0
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h0
    omega
  have hsq := (altPrimaryData_spLin hpK' hx).squarefree
  haveI : Finite (reciprocalOrbits (spEnd x)) := (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hker : (proj r K).ker ≤ Subgroup.center ↥(StatedSp r K) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj]
    exact CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars_le_center
  have hodd : Nat.Coprime 2 (Nat.card (proj r K).ker) := by
    rw [CFSG.RankThree.PartOne.KCSpFull.ker_proj_eq_bot_of_even hr (by rw [hK]; exact dvd_pow_self 2 (by omega)),
      Subgroup.card_bot]
    exact Nat.coprime_one_right 2
  have hA := fun O : reciprocalOrbits (spEnd x) =>
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.quasisimple_or_solvable_spSupported (by omega) hq hsq
      blocks O
  have hlay := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_conj_of_orbit_family (proj r K)
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective hker x
    (fun O : reciprocalOrbits (spEnd x) => spSupported x (O : Set K[X]))
    (fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb) hjoin hA
  refine twoInCoreLayer_conj_of_family (proj r K) CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective
    hker hodd hp x hlay (fun O : reciprocalOrbits (spEnd x) => spSupported x (O : Set K[X]))
    (fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb) hjoin
    (fun O => twoGood_spSupported hp hp5 hq (by rwa [hK]) blocks O)

open CFSG.ComponentClassification.UnbalancedCatalog (descentField)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (nonempty_fixSubgroup_equiv)

theorem twoInCoreLayer_fieldAut_sp (hr : 2 ≤ r) [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (σ : K ≃+* K)
    (hσ : orderOf σ = p) (hex : p = 5 → ¬ (r = 2 ∧ Nat.card ↥(descentField σ) = 2)) :
    TwoInCoreLayer p (fieldAut r K σ) := by
  haveI : NeZero r := ⟨by omega⟩
  have hσp : σ ^ p = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  obtain ⟨e⟩ := nonempty_fixSubgroup_equiv (r := r) (hp.odd_of_ne_two (by omega)) hσp
  haveI : Finite ↥(descentField σ) := Subtype.finite
  have hlay := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_fieldAut_sp hr hp (by omega) σ hσp
  refine twoInCoreLayer_of_fixSubgroup hp hlay ?_
  by_cases hsmall : r = 2 ∧ Nat.card ↥(descentField σ) = 2
  · right
    obtain ⟨rfl, hk2⟩ := hsmall
    have hp7 : 7 ≤ p := by
      by_contra h
      rcases (show p = 5 ∨ p = 6 by omega) with h5 | h6
      · exact hex h5 ⟨rfl, hk2⟩
      · rw [h6] at hp
        norm_num at hp
    have hC : Nat.card ↥(fixSubgroup (fieldAut 2 K σ)) ∣ 720 := by
      rw [Nat.card_congr e.toEquiv]
      have h1 : Nat.card (StatedProj (StatedSp 2 ↥(descentField σ))) ∣ Nat.card ↥(StatedSp 2 ↥(descentField σ)) :=
        Subgroup.card_quotient_dvd_card _
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hk2] at h1
      exact h1.trans (by decide)
    refine Nat.Coprime.coprime_dvd_right hC ?_
    rw [show (720 : ℕ) = 2 ^ 4 * 3 ^ 2 * 5 by norm_num]
    refine Nat.Coprime.mul_right (coprime_two_pow_mul_three_pow hp hp5 4 2) ?_
    exact (Nat.coprime_primes hp Nat.prime_five).2 (by omega)
  · left
    obtain ⟨hs, hperf⟩ := CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj (k := ↥(descentField σ)) hr hsmall
    have hperf' : commutator (StatedProj (StatedSp r ↥(descentField σ))) = ⊤ := Group.isPerfect_def.mp hperf
    have hC : commutator ↥(fixSubgroup (fieldAut r K σ)) = ⊤ := by
      have h1 : (commutator (StatedProj (StatedSp r ↥(descentField σ)))).map e.symm.toMonoidHom =
          commutator ↥(fixSubgroup (fieldAut r K σ)) := by
        rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          MonoidHom.range_eq_top.2 e.symm.surjective]
      rw [← h1, hperf', Subgroup.map_top, MonoidHom.range_eq_top.2 e.symm.surjective]
    have h2 : (commutator ↥(fixSubgroup (fieldAut r K σ))).map (fixSubgroup (fieldAut r K σ)).subtype =
        ⁅fixSubgroup (fieldAut r K σ), fixSubgroup (fieldAut r K σ)⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← h2, hC, Subgroup.map_top, Subgroup.range_subtype]

end Symplectic

section SymplecticCatalogue

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldAut spLinearAutGroup spSemilinearAutGroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)

theorem pow_eq_one_of_conj_pow_eq_one {S : Type} [Group S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    {p : ℕ} {a : S} (h : MulAut.conj a ^ p = 1) : a ^ p = 1 := by
  have hc : a ^ p ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut S => φ g) (show MulAut.conj (a ^ p) = 1 by rw [map_pow]; exact h)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * a ^ p = a ^ p * g * (a ^ p)⁻¹ * a ^ p := by rw [h1]
      _ = a ^ p * g := by group
  rw [CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hna, Subgroup.mem_bot] at hc
  exact hc

theorem input14_1BadSimpleOn_symplectic :
    Input14_1BadSimpleOn fun p d => ∃ r q, d = TauCeti.LieTypeIndex.B r q ∧
      ¬ (p = 5 ∧ (q.card = 2 ∨ (r = 2 ∧ q.card = 32))) := by
  intro p hp hp5 S _ _ hs hna idx hd hchar he β hβ hβ1
  haveI := hs
  obtain ⟨d, hv⟩ := idx
  obtain ⟨r, q, rfl, hexc⟩ := hd
  have hq2 : q.p = 2 := by
    rw [← TauCeti.LieTypeIndex.characteristic_B r q]
    exact hchar
  obtain ⟨e⟩ := he
  have hr0 := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hM : CFSG.Open.StatedClassicalModel S .PSp r q.p q.exponent := by
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · exact CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
    · exact CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq2 hr3 e
  obtain ⟨⟨-, hf, hr, -⟩, K, _, _, hK, ⟨e'⟩⟩ := hM
  rw [hq2] at hK
  have hqc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq2]
  have hβ' : MulAut.congr e' β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hβ1' : MulAut.congr e' β ≠ 1 := fun h1 =>
    hβ1 ((MulAut.congr e').injective (h1.trans (map_one _).symm))
  refine twoInCoreLayer_of_congr e' hp ?_
  have hO := CFSG.RankThree.PartOne.KCSpComm.spOuter (K := K) Nat.prime_two hf hr hK
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (orderOf (MulAut.congr e' β)) :=
    (hp.odd_of_ne_two (by omega)).of_dvd_nat (orderOf_dvd_of_pow_eq_one hβ')
  have hE : MulAut.congr e' β ∈ spSemilinearAutGroup r K :=
    CFSG.RankThree.PartOne.KCSpComm.mem_of_odd_orderOf_of_index_dvd_two _ hO.index_dvd hodd
  by_cases hD : MulAut.congr e' β ∈ spLinearAutGroup r K
  ·
    have : (inner (StatedProj (StatedSp r K))).Normal := inner_normal _
    have hrel : (inner (StatedProj (StatedSp r K))).relIndex (spLinearAutGroup r K) ∣ 2 :=
      hO.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)
    obtain ⟨t, ht⟩ := CFSG.RankThree.PartOne.KCSpComm.mem_of_pow_eq_one_of_relIndex_dvd_two hrel hp (by omega) hD
      hβ'
    have hna' : ∃ a b : StatedProj (StatedSp r K), a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hna
      exact ⟨e' a, e' b, fun h => hab (e'.injective (by rw [map_mul, map_mul, h]))⟩
    haveI : IsSimpleGroup (StatedProj (StatedSp r K)) := e'.symm.isSimpleGroup
    have htp : t ^ p = 1 := pow_eq_one_of_conj_pow_eq_one hna' (by rw [ht]; exact hβ')
    obtain ⟨x, hx, hxp⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_proj_eq_pow_eq_one_sp
      (by omega) hp (by omega) htp
    have hx1 : proj r K x ≠ 1 := by
      rw [hx]
      intro h1
      apply hβ1'
      rw [← ht, h1, map_one]
    have hpK : 7 ≤ p ∨ 4 ≤ 2 ^ q.exponent := by
      by_cases h5 : p = 5
      · right
        have h2 : 2 ^ q.exponent ≠ 2 := fun h => hexc ⟨h5, Or.inl (hqc.trans h)⟩
        have h4 : 2 ≤ 2 ^ q.exponent := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) q.exponent_pos
        have h3 : 2 ^ q.exponent ≠ 3 := by
          intro h
          have : Even (2 ^ q.exponent) := (Nat.even_pow' q.exponent_pos.ne').2 even_two
          rw [h] at this
          exact absurd this (by decide)
        omega
      · left
        rcases (show p = 6 ∨ 7 ≤ p by omega) with h6 | h7
        · rw [h6] at hp
          norm_num at hp
        · exact h7
    rw [← ht, ← hx]
    exact twoInCoreLayer_conj_sp hK hf (by omega) hp hp5 hpK x hxp hx1
  ·
    have hord : orderOf (MulAut.congr e' β) = p := orderOf_eq_prime hβ' hβ1'
    obtain ⟨-, σ, hσ, h, -, hβeq⟩ := hO.descent p hp _ hE hD hord
    refine twoInCoreLayer_of_conj h⁻¹ hp ?_
    rw [hβeq, show h⁻¹ * (h * fieldAut r K σ * h⁻¹) * h⁻¹⁻¹ = fieldAut r K σ by group]
    refine twoInCoreLayer_fieldAut_sp hr hp hp5 σ hσ fun h5 ⟨hr2, hk2⟩ => hexc ⟨h5, Or.inr ⟨hr2, ?_⟩⟩
    have h1 := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.card_descentField_pow σ
    rw [hσ, hk2, hK, h5] at h1
    rw [hqc, ← h1]
    norm_num

end SymplecticCatalogue


section Unitary

open Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (toLinSU toLinSU_injective mem_range_toLinSU
  toLinSU_mem_unitaryCentralizer toLinSU_mem_sesqSpecialUnitaryGroup mem_fixSubgroup_primeFormConjSU_iff
  primaryData_toLin' nonempty_statedSU_mulEquiv_fixSubgroup)
open scoped commutatorElement

theorem twoGood_supportedUnitary {ℓ f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData ℓ f K) (hℓ : ℓ = 2)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
    {x : LinearMap.GeneralLinearGroup K V} (H : UnitaryPrimaryData hK.bar B x) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (O : CFSG.RankThree.PartOne.adjointOrbits hK x) :
    TwoGood p ↥(supportedUnitary B x (O : Set K[X])) := by
  obtain ⟨O, a, ha, rfl⟩ := O
  subst hℓ
  haveI := hK.finite
  haveI : CharP K 2 := hK.charP
  have hq : 2 ≤ 2 ^ f := by
    have := Nat.one_lt_pow (by have := hK.one_le; omega : f ≠ 0) (by norm_num : 1 < 2)
    omega
  haveI : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
  by_cases hself : dualPoly hK.bar a = a
  · have hO : ({a, dualPoly hK.bar a} : Set K[X]) = {a} := by rw [hself, Set.pair_eq_singleton]
    show TwoGood p ↥(supportedUnitary B x {a, dualPoly hK.bar a})
    rw [hO]
    obtain ⟨-, hE, -, -, Hf, hHf, hHfl, -, -, φ, -⟩ := CFSG.RankThree.PartOne.selfDualPrimaryBlock H ⟨a, ha⟩ hself
    exact twoGood_of_mulEquiv φ (twoGood_sesqUnitaryGroup hE hHf hHfl hp hp5)
  · obtain ⟨-, -, -, -, -, φ, -, -⟩ := CFSG.RankThree.PartOne.pairedPrimaryBlock H ⟨a, ha⟩ (Ne.symm hself)
    haveI : CharP (AdjoinRoot a) 2 := charP_of_injective_algebraMap (algebraMap K (AdjoinRoot a)).injective 2
    haveI : Finite (AdjoinRoot a) := Module.finite_of_finite K
    exact twoGood_of_mulEquiv φ (twoGood_generalLinearGroup p (Or.inr (exists_finset_card_four hK hq)))

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem twoInCoreLayer_primeFormConjHom (h : UnitaryFieldData ℓ f K) (hℓ : ℓ = 2) (hn : 1 ≤ n) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (A : primeFormUnitary h (idGram K n)) {c : Kˣ}
    (hA : (A : GL (Fin n) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    TwoInCoreLayer p (primeFormConjHom h (idGram K n) A) := by
  classical
  haveI := h.finite
  haveI : CharP K 2 := hℓ ▸ h.charP
  have hpℓ : p ≠ ℓ := by omega
  set X := gramSU h (idGram K n) with hX
  let π : ↥X →* primeFormP h (idGram K n) := QuotientGroup.mk' (normOneScalars h X n)
  have hker : π.ker ≤ Subgroup.center ↥X := by
    rw [QuotientGroup.ker_mk']
    exact normOneScalars_le_center h _ n
  have hodd : Nat.Coprime 2 (Nat.card π.ker) := by
    rw [QuotientGroup.ker_mk']
    exact Inputs141d.coprime_two_card_normOneScalars h hℓ hn _
  have hαβ : ∀ g, π (primeFormConjSU h (idGram K n) A g) = primeFormConjHom h (idGram K n) A (π g) :=
    fun g => (primeFormConjHom_mk h (idGram K n) A g).symm
  have hlay := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_primeFormConjHom h hp hpℓ A hA
  set x : LinearMap.GeneralLinearGroup K (Fin n → K) := Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) with hx
  have H : UnitaryPrimaryData h.bar (idForm h n) x := primaryData_toLin' h A.2 hp hpℓ hA
  obtain ⟨hcomm, -, hgen⟩ := (CFSG.RankThree.PartOne.r3e_unitary_semisimple_primary_algebra_and_full_centralizer h
    (idForm h n) H.symm H.sep x H.isom H.squarefree).directProduct
  haveI : Finite (CFSG.RankThree.PartOne.adjointOrbits h x) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  set A' : CFSG.RankThree.PartOne.adjointOrbits h x → Subgroup (LinearMap.GeneralLinearGroup K (Fin n → K)) :=
    fun O => supportedUnitary (idForm h n) x (O : Set K[X]) with hA'
  have hc' : ∀ O O' : CFSG.RankThree.PartOne.adjointOrbits h x, O ≠ O' → ∀ a ∈ A' O, ∀ b ∈ A' O', Commute a b :=
    fun O O' hne => hcomm O O.2 O' O'.2 (fun e => hne (Subtype.ext e))
  have hTG : ∀ O, TwoGood p ↥(A' O) := fun O => twoGood_supportedUnitary h hℓ H hp hp5 O
  choose M hMn hM2 hM using hTG
  set B' : CFSG.RankThree.PartOne.adjointOrbits h x → Subgroup (LinearMap.GeneralLinearGroup K (Fin n → K)) :=
    fun O => (M O).map (A' O).subtype ⊓ sesqSpecialUnitaryGroup (idForm h n) with hB'
  set B : CFSG.RankThree.PartOne.adjointOrbits h x → Subgroup ↥X := fun O => (B' O).comap (toLinSU h n) with hB
  have hB'le : ∀ O, B' O ≤ (toLinSU h n).range := fun O g hg => mem_range_toLinSU hg.2
  have hmapB : ∀ O, (B O).map (toLinSU h n) = B' O := fun O => Subgroup.map_comap_eq_self (hB'le O)
  have hfixmem : ∀ g : ↥X, toLinSU h n g ∈ unitaryCentralizer (idForm h n) x →
      g ∈ fixSubgroup (primeFormConjSU h (idGram K n) A) := fun g hg =>
    (mem_fixSubgroup_primeFormConjSU_iff A hx g).2 (Subgroup.mem_inf.mp hg).2
  refine twoInCoreLayer_of_cover π (QuotientGroup.mk'_surjective _) hker hodd _ _ hαβ hp hlay B
    (fun O g hg => hfixmem g (supportedUnitary_le_unitaryCentralizer _ (Subgroup.map_subtype_le _ hg.1))) (fun O => ?_) ?_
  · rcases hM O with hperf | hcop
    ·
      left
      have hMSU : (M O).map (A' O).subtype ≤ sesqSpecialUnitaryGroup (idForm h n) := by
        have hP : ⁅(M O).map (A' O).subtype, (M O).map (A' O).subtype⁆ = (M O).map (A' O).subtype := by
          rw [← Subgroup.map_commutator, hperf]
        rw [← hP, Subgroup.commutator_le]
        intro a ha b hb
        have haU : a ∈ sesqUnitaryGroup (idForm h n) :=
          (Subgroup.mem_inf.mp (supportedUnitary_le_unitaryCentralizer _ (Subgroup.map_subtype_le _ ha))).1
        have hbU : b ∈ sesqUnitaryGroup (idForm h n) :=
          (Subgroup.mem_inf.mp (supportedUnitary_le_unitaryCentralizer _ (Subgroup.map_subtype_le _ hb))).1
        refine mem_sesqSpecialUnitaryGroup.2 ⟨?_, ?_⟩
        · rw [commutatorElement_def]
          exact (sesqUnitaryGroup _).mul_mem ((sesqUnitaryGroup _).mul_mem ((sesqUnitaryGroup _).mul_mem haU hbU)
            ((sesqUnitaryGroup _).inv_mem haU)) ((sesqUnitaryGroup _).inv_mem hbU)
        · have h1 := map_commutatorElement (Units.map (LinearMap.det : Module.End K (Fin n → K) →* K)) a b
          have h2 : ⁅(Units.map (LinearMap.det : Module.End K (Fin n → K) →* K)) a,
              (Units.map (LinearMap.det : Module.End K (Fin n → K) →* K)) b⁆ = 1 :=
            commutatorElement_eq_one_iff_commute.2 (Commute.all _ _)
          rw [h2] at h1
          exact congrArg Units.val h1
      have hB'eq : B' O = (M O).map (A' O).subtype := inf_eq_left.2 hMSU
      apply Subgroup.map_injective (toLinSU_injective (h := h) (n := n))
      rw [Subgroup.map_commutator, hmapB, hB'eq, ← Subgroup.map_commutator, hperf]
    · right
      refine ⟨?_, fun g hg b hb => ?_⟩
      · have h1 : Nat.card ↥(B O) ∣ Nat.card ↥((M O).map (A' O).subtype) := by
          rw [← Subgroup.card_map_of_injective (toLinSU_injective (h := h) (n := n)), hmapB]
          exact Subgroup.card_dvd_of_le inf_le_left
        rw [Subgroup.card_map_of_injective (A' O).subtype_injective] at h1
        exact Nat.Coprime.coprime_dvd_right h1 hcop
      · show toLinSU h n (g * b * g⁻¹) ∈ B' O
        rw [map_mul, map_mul, map_inv]
        have hgC : toLinSU h n g ∈ ⨆ O', A' O' := by
          rw [hA', hgen]
          exact toLinSU_mem_unitaryCentralizer A hx hg
        refine ⟨conj_mem_map_of_family A' hc' (hMn O) hgC hb.1, ?_⟩
        have hgS := toLinSU_mem_sesqSpecialUnitaryGroup (h := h) (n := n) g
        exact (sesqSpecialUnitaryGroup _).mul_mem ((sesqSpecialUnitaryGroup _).mul_mem hgS hb.2)
          ((sesqSpecialUnitaryGroup _).inv_mem hgS)
  ·
    intro g hg hg2
    have hgU : toLinSU h n g ∈ ⨆ O, A' O := by
      rw [hA', hgen]
      exact toLinSU_mem_unitaryCentralizer A hx hg
    have hg2' : IsPGroup 2 ↥(Subgroup.zpowers (toLinSU h n g)) := by
      have h1 := hg2.map (toLinSU h n)
      rwa [MonoidHom.map_zpowers] at h1
    have hmem : toLinSU h n g ∈ ⨆ O, B' O := by
      refine Inputs141d.mem_iSup_of_two A' B' hc' (fun O y hy hy2 => ?_) hgU hg2'
      obtain ⟨m, hm⟩ := Inputs141d.exists_pow_eq_one_of_isPGroup hy2
      have hyU : y ∈ unitaryCentralizer (idForm h n) x := supportedUnitary_le_unitaryCentralizer _ hy
      refine ⟨⟨⟨y, hy⟩, hM2 O _ (Inputs141d.isPGroup_zpowers_of_pow (m := m) (Subtype.ext (by simpa using hm))),
        rfl⟩, ?_⟩
      exact mem_sesqSpecialUnitaryGroup.2 ⟨(mem_unitaryCentralizer.mp hyU).1, Inputs141d.det_eq_one_of_pow_two hm⟩
    have hmap : (⨆ O, B' O) = (⨆ O, B O).map (toLinSU h n) := by
      rw [Subgroup.map_iSup]
      exact iSup_congr fun O => (hmapB O).symm
    rw [hmap] at hmem
    obtain ⟨g', hg', hgg'⟩ := hmem
    rwa [← toLinSU_injective hgg']

theorem twoInCoreLayer_primeFormFieldHom (h : UnitaryFieldData ℓ f K) (hℓ : ℓ = 2) (hn : 3 ≤ n)
    (hC : IsPrimeFormGram (1 : GL (Fin n) K)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (σ : K ≃+* K)
    (hσ : orderOf σ = p) : TwoInCoreLayer p (primeFormFieldHom h hC σ) := by
  haveI := h.finite
  set X := gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hX
  let π : ↥X →* primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    QuotientGroup.mk' (normOneScalars h X n)
  have hker : π.ker ≤ Subgroup.center ↥X := by
    rw [QuotientGroup.ker_mk']
    exact normOneScalars_le_center h _ n
  have hodd : Nat.Coprime 2 (Nat.card π.ker) := by
    rw [QuotientGroup.ker_mk']
    exact Inputs141d.coprime_two_card_normOneScalars h hℓ (by omega) _
  have hαβ : ∀ x, π (primeFormFieldSU h hC σ x) = primeFormFieldHom h hC σ (π x) := fun x =>
    (primeFormFieldAut_mk h hC σ x).symm
  have hlay : PerfectInLayer (primeFormFieldHom h hC σ) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_primeFormFieldHom h hn hp (by omega) σ hσ
  have h₀ : UnitaryFieldData ℓ (f / p) (CFSG.LieType.Chevalley.fixSubfield σ) :=
    CFSG.RankThree.Classical.fixSubfield_unitaryFieldData h hp (by omega) hσ
  have hbar := CFSG.RankThree.Classical.fixSubfield_unitaryFieldData_bar h hp (by omega) hσ
  obtain ⟨e⟩ := nonempty_statedSU_mulEquiv_fixSubgroup (n := n) h h₀ hbar hC
  refine twoInCoreLayer_of_cover π (QuotientGroup.mk'_surjective _) hker hodd _ _ hαβ hp hlay
    (fun _ : Unit => fixSubgroup (primeFormFieldSU h hC σ)) (fun _ => le_rfl) (fun _ => ?_)
    (fun g hg _ => Subgroup.mem_iSup_of_mem () hg)
  by_cases hq₀ : n = 3 ∧ ℓ ^ (f / p) = 2
  · right
    refine ⟨?_, fun c hc g hg => (fixSubgroup _).mul_mem ((fixSubgroup _).mul_mem hc hg) ((fixSubgroup _).inv_mem hc)⟩
    obtain ⟨hn3, hq2⟩ := hq₀
    subst hn3
    haveI := h₀.finite
    have hB := gramForm_isSymm h₀ (G := (1 : Matrix (Fin 3) (Fin 3) (CFSG.LieType.Chevalley.fixSubfield σ))) (by
      rw [Matrix.map_one _ (map_zero h₀.bar) (map_one h₀.bar), Matrix.transpose_one])
    have hBl := gramForm_separatingLeft h₀ (G := (1 : Matrix (Fin 3) (Fin 3) (CFSG.LieType.Chevalley.fixSubfield σ)))
      (by simp)
    have hdim : Module.finrank (CFSG.LieType.Chevalley.fixSubfield σ)
        (Fin 3 → CFSG.LieType.Chevalley.fixSubfield σ) = 3 := Module.finrank_fin_fun _
    have hS := (CFSG.LinearGroups.unitary_full_group_order h₀ hB hBl hdim (by norm_num)).2.1
    rw [hq2] at hS
    have hS' : Nat.card (gramSU h₀ ((1 : GL (Fin 3) (CFSG.LieType.Chevalley.fixSubfield σ)) :
        Matrix (Fin 3) (Fin 3) (CFSG.LieType.Chevalley.fixSubfield σ))) = 216 := by
      rw [Units.val_one, card_gramSU]
      have h1 : ((2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) * ∏ i ∈ Finset.Icc 2 3,
          (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 216 := by decide
      exact_mod_cast hS.trans h1
    have hcard : Nat.card ↥(fixSubgroup (primeFormFieldSU h hC σ)) = 216 := by
      rw [← Nat.card_congr e.toEquiv, ← hS']
      exact Nat.card_congr (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h₀ 3)).toEquiv
    rw [hcard, show (216 : ℕ) = 2 ^ 3 * 3 ^ 3 by norm_num]
    exact coprime_two_pow_mul_three_pow hp hp5 3 3
  · left
    haveI : Fact ℓ.Prime := ⟨h.prime⟩
    have hcard : Nat.card (CFSG.LieType.Chevalley.fixSubfield σ) = (ℓ ^ (f / p)) ^ 2 := by
      rw [h₀.card, ← pow_mul, mul_comm]
    have hq := CFSG.LocalCores.isQuasisimple_of_mulEquiv e
      (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hcard hn
        (fun heq => hq₀ ⟨(Prod.mk.inj heq).1, (Prod.mk.inj heq).2⟩)).1
    exact commutator_eq_self_of_isQuasisimple hq

end Unitary

section UnitaryCatalogue

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

theorem input14_1BadSimpleOn_unitary :
    Input14_1BadSimpleOn fun _ d => ∃ r q, d = TauCeti.LieTypeIndex.twistedA r q := by
  intro p hp hp5 S _ _ _ _ d hd hchar he β hβ hβ1
  obtain ⟨d, hv⟩ := d
  obtain ⟨r, q, rfl⟩ := hd
  have hq2 : q.p = 2 := by
    rw [← TauCeti.LieTypeIndex.characteristic_twistedA r q]
    exact hchar
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e⟩ := he
  obtain ⟨⟨hℓ, hf, hn3, hq⟩, K, _, _, hK, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := r + 1) (K := K))
  let e' : S ≃* primeFormP h (idGram K (r + 1)) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  have hq' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun h3 => hq (Prod.ext h3.1 h3.2)
  have hC : IsPrimeFormGram (1 : GL (Fin (r + 1)) K) := isPrimeFormGram_idGram
  have hβ' : MulAut.congr e' β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  haveI : Fact p.Prime := ⟨hp⟩
  refine twoInCoreLayer_of_congr e' hp ?_
  obtain ⟨-, -, hker1, -, -, -, -, hkerD, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn3 hq'
  by_cases hσ : primeFormFieldFactor h hC hn3 hq' (MulAut.congr e' β) = 1
  ·
    have hβD : MulAut.congr e' β ∈ (primeFormFieldFactor h hC hn3 hq').ker := hσ
    rw [hkerD, primeFormD, MonoidHom.mem_range] at hβD
    obtain ⟨A, hA⟩ := hβD
    have h1 : primeFormPsi h hC ⟨A ^ p, 1⟩ = 1 := by
      rw [primeFormPsi_apply, map_pow, hA, hβ', map_one, one_mul]
    obtain ⟨-, c, -, hc⟩ := (hker1 _).1 h1
    have hAp : (A : GL (Fin (r + 1)) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) c := by
      rwa [SubgroupClass.coe_pow] at hc
    rw [← hA]
    exact twoInCoreLayer_primeFormConjHom h hq2 (by omega) hp hp5 A hAp
  ·
    have hne : MulAut.congr e' β ≠ 1 := fun h1 => hσ (by rw [h1, map_one])
    have hord : orderOf (MulAut.congr e' β) = p := orderOf_eq_prime hβ' hne
    have hσp : orderOf (primeFormFieldFactor h hC hn3 hq' (MulAut.congr e' β)) = p :=
      orderOf_eq_prime (by rw [← map_pow, hβ', map_one]) hσ
    obtain ⟨-, -, -, -, -, M, hM⟩ :=
      CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.unitary_prime_descent_char h hn3 hq' hp (by omega)
        (MulAut.congr e' β) hord _ rfl hσp
    refine twoInCoreLayer_of_conj (primeFormConjHom h (idGram K (r + 1)) M)⁻¹ hp ?_
    rw [inv_inv, hM]
    exact twoInCoreLayer_primeFormFieldHom h hq2 hn3 hC hp hp5 _ hσp

end UnitaryCatalogue

theorem input14_1BadSimpleOn_linearUnitary :
    Input14_1BadSimpleOn fun _ d =>
      CFSG.Yardstones.Md42047359a2a.lieFamily d = CFSG.Yardstones.Md42047359a2a.LieFamily.linearUnitary := by
  intro p hp hp5 S _ _ hS hnc d hd
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q => exact input14_1BadSimpleOn_linear p hp hp5 S hS hnc ⟨_, hv⟩ ⟨r, q, rfl⟩
  | twistedA r q => exact input14_1BadSimpleOn_unitary p hp hp5 S hS hnc ⟨_, hv⟩ ⟨r, q, rfl⟩
  | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hd

section OrthHelpers

open Module

theorem commutator_iSup_eq_of_perfect {G : Type*} [Group G] {ι : Type*} (F : ι → Subgroup G)
    (hF : ∀ i, ⁅F i, F i⁆ = F i) : ⁅⨆ i, F i, ⨆ i, F i⁆ = ⨆ i, F i := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · refine iSup_le fun i => ?_
    rw [← hF i]
    exact Subgroup.commutator_mono (le_iSup F i) (le_iSup F i)

theorem commutator_subgroupOf_eq {G : Type*} [Group G] {H Ω : Subgroup G} (hH : H ≤ Ω) (hP : ⁅H, H⁆ = H) :
    ⁅H.subgroupOf Ω, H.subgroupOf Ω⁆ = H.subgroupOf Ω := by
  apply Subgroup.map_injective Ω.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hH, hP]

theorem sub_one_sq_eq {K W : Type*} [Field K] [CharP K 2] [AddCommGroup W] [Module K W] (a : Module.End K W) :
    (a - 1) ^ 2 = a ^ 2 - 1 := by
  have h2 : (2 : Module.End K W) = 0 := by
    rw [← one_add_one_eq_two, ← two_smul K (1 : Module.End K W), CharTwo.two_eq_zero, zero_smul]
  have e : (a - 1) ^ 2 = a ^ 2 - 1 - 2 * (a - 1) := by noncomm_ring
  rw [e, h2, zero_mul, sub_zero]

theorem eq_one_of_pow_two_of_even_finrank_commSpace {K W : Type*} [Field K] [CharP K 2] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] (hW : finrank K W ≤ 2) {g : W ≃ₗ[K] W} {m : ℕ} (hg : g ^ (2 ^ m) = 1)
    (he : Even (finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace g))) : g = 1 := by
  set a : Module.End K W := (g : W →ₗ[K] W) with ha
  have hpow : ∀ k : ℕ, (a - 1) ^ (2 ^ k) = a ^ (2 ^ k) - 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_mul, ih, sub_one_sq_eq, ← pow_mul]
  have hag : a ^ (2 ^ m) = 1 := by
    have h1 := congrArg LinearEquiv.automorphismGroup.toLinearMapMonoidHom hg
    rw [map_pow, map_one] at h1
    exact h1
  have hN : (a - 1) ^ (2 ^ m) = 0 := by rw [hpow, hag, sub_self]
  by_contra hne
  have hN0 : a - 1 ≠ 0 := by
    intro h0
    apply hne
    refine LinearEquiv.ext fun w => ?_
    have := LinearMap.congr_fun h0 w
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.zero_apply, sub_eq_zero] at this
    exact this
  have hpos : 0 < finrank K (LinearMap.range (a - 1)) :=
    Nat.pos_of_ne_zero fun h => hN0 (LinearMap.range_eq_bot.1 (Submodule.finrank_eq_zero.1 h))
  have hle : finrank K (LinearMap.range (a - 1)) ≤ finrank K W := Submodule.finrank_le _
  have heq : finrank K (LinearMap.range (a - 1)) = finrank K W := by
    have he' : Even (finrank K (LinearMap.range (a - 1))) := he
    obtain ⟨k, hk⟩ := he'
    omega
  have htop : LinearMap.range (a - 1) = ⊤ := Submodule.eq_top_of_finrank_eq heq
  have hsurj : Function.Surjective ⇑(a - 1) := LinearMap.range_eq_top.1 htop
  have hinj : Function.Injective ⇑(a - 1) := (LinearMap.injective_iff_surjective).2 hsurj
  have hinjN : Function.Injective ⇑((a - 1) ^ (2 ^ m) : Module.End K W) := by
    rw [Module.End.coe_pow]
    exact hinj.iterate _
  rw [hN] at hinjN
  have hsub : Subsingleton W := ⟨fun u v => hinjN (by simp)⟩
  have h0 : finrank K W = 0 := Module.finrank_zero_of_subsingleton
  omega

end OrthHelpers

section OrthBlocksP

open Module QuadraticMap Polynomial CFSG.RankThree.OrthogonalInvolutions CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

variable [CharP K 2]

theorem exists_two_decomp_p (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (hx : OddOrderIsometry Q p x) (hp : Odd p)
    {Rep : Finset K[X]} (hRep : IsOrbitRepresentatives x Rep) {y : V ≃ₗ[K] V}
    (hy : y ∈ isometryCentralizer Q x) (hyΩ : y ∈ orthDerived Q) (hy2 : IsPGroup 2 ↥(Subgroup.zpowers y)) :
    ∃ w ∈ supportedBlock Q x (X - 1), w ∈ orthDerived Q ∧ IsPGroup 2 ↥(Subgroup.zpowers w) ∧
      ∃ z ∈ ⨆ r : {r : ↥Rep // (r : K[X]) ≠ X - 1}, specialBlock Q x ((r.1 : K[X])), y = w * z := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  set A : {r : ↥Rep // (r : K[X]) ≠ X - 1} → Subgroup (V ≃ₗ[K] V) := fun r => supportedBlock Q x (r.1 : K[X])
    with hA
  have hle : isometryCentralizer Q x ≤ supportedBlock Q x (X - 1) ⊔ ⨆ r, A r := by
    rw [← hx.blocks_iSup_eq hRep]
    refine iSup_le fun i => ?_
    by_cases hi : (i : K[X]) = X - 1
    · rw [hi]
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup A ⟨i, hi⟩)
  have hcomm : ∀ a ∈ supportedBlock Q x (X - 1), ∀ c ∈ ⨆ r, A r, a * c = c * a := by
    intro a ha c hc
    have hle' : (⨆ r, A r) ≤ Subgroup.centralizer (supportedBlock Q x (X - 1) : Set (V ≃ₗ[K] V)) :=
      iSup_le fun r g hg => Subgroup.mem_centralizer_iff.2 fun a ha =>
        (Inputs141d.commute_fixed_supportedBlock hx (hRep.1 r.1.2) r.2 ha hg).eq
    exact Subgroup.mem_centralizer_iff.1 (hle' hc) a ha
  obtain ⟨a, ha, c, hc, rfl⟩ := Input183.mem_sup_of_commute hcomm (hle hy)
  have hac : Commute a c := hcomm a ha c hc
  obtain ⟨k, hk, hak, hck⟩ := Inputs141d.exists_two_parts hac hy2
  have hck' : c ^ k ∈ ⨆ r : {r : ↥Rep // (r : K[X]) ≠ X - 1}, specialBlock Q x ((r.1 : K[X])) := by
    refine Inputs141d.mem_iSup_of_two A (fun r => specialBlock Q x ((r.1 : K[X]))) ?_ ?_ (pow_mem hc k) hck
    · intro r s hrs g hg g' hg'
      exact hx.blocks_commute hRep (fun e => hrs (Subtype.ext e)) g g' hg hg'
    · intro r g hg hg2
      obtain ⟨m, hm⟩ := Inputs141d.exists_pow_eq_one_of_isPGroup hg2
      haveI : Fact (Irreducible ((r.1 : K[X]))) := ⟨irreducible_of_mem_primaryFactors (hRep.1 r.1.2)⟩
      haveI : CharP (AdjoinRoot ((r.1 : K[X]))) 2 :=
        charP_of_injective_algebraMap (algebraMap K (AdjoinRoot ((r.1 : K[X])))).injective 2
      refine mem_specialBlock.mpr ⟨hg, Inputs141c.eq_one_of_pow_two_pow_eq_one (m := m) ?_⟩
      have e1 : (⟨g, hg⟩ : ↥(supportedBlock Q x ((r.1 : K[X])))) ^ (2 ^ m) = 1 :=
        Subtype.ext (by simpa using hm)
      rw [← map_pow, e1, map_one]
  have hMΩ : (⨆ r : {r : ↥Rep // (r : K[X]) ≠ X - 1}, specialBlock Q x ((r.1 : K[X]))) ≤ orthDerived Q :=
    iSup_le fun r => (specialBlock_le_supportedBlock _).trans
      (Inputs141d.supportedBlock_le_orthDerived hQ hT hx hp (hRep.1 r.1.2) r.2)
  refine ⟨a ^ k, pow_mem ha k, ?_, hak, c ^ k, hck', ?_⟩
  · have e2 : a ^ k = (a * c) ^ k * (c ^ k)⁻¹ := by rw [hac.mul_pow, mul_inv_cancel_right]
    rw [e2, hk]
    exact mul_mem hyΩ (inv_mem (hMΩ hck'))
  · rw [← hac.mul_pow, hk]

end OrthBlocksP

section OrthInnerP

open Module QuadraticMap Polynomial CFSG.RankThree.OrthogonalInvolutions
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived ProjOrthDerived)

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} [CharP K 2]

theorem card_ne_three_of_charTwo : Nat.card K ≠ 3 := by
  intro h
  haveI : Fintype K := Fintype.ofFinite K
  have h2 := FiniteField.cast_card_eq_zero K
  rw [Fintype.card_eq_nat_card, h] at h2
  have h3' : ((3 : ℕ) : K) = 1 := by
    have : ((2 : ℕ) : K) = 0 := CharP.cast_eq_zero K 2
    rw [show (3 : ℕ) = 2 + 1 by norm_num, Nat.cast_add, this, zero_add, Nat.cast_one]
  rw [h3'] at h2
  exact one_ne_zero h2

theorem twoInCoreLayer_conj_orth (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (a : ProjOrthDerived Q) (ha : a ^ p = 1) (ha1 : a ≠ 1) : TwoInCoreLayer p (MulAut.conj a) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have : Nontrivial V := by
    obtain ⟨U, hU, -⟩ := hT
    exact Module.nontrivial_of_finrank_pos (R := K)
      (lt_of_lt_of_le (by norm_num : 0 < 3) (hU ▸ Submodule.finrank_le U))
  have hpℓ : p ≠ ringChar K := by rw [ringChar.eq K 2]; omega
  have hp2 : p ≠ 2 := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hao : orderOf a = p := orderOf_eq_prime ha ha1
  obtain ⟨-, -, -, -, -, -, -, -, hlift⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  obtain ⟨x, ⟨hxa, hxp⟩, -, hcent⟩ := hlift p hp hp2 a hao
  have hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V) := oddOrderIsometry_of_orthDerived hp hpℓ hQ x hxp
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) with hρ
  set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with hxe
  have hker : ρ.ker ≤ Subgroup.center ↥(orthDerived Q) := by
    rw [QuotientGroup.ker_mk']
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨c, hc⟩ : ∃ c : K, ∀ v, (z : V ≃ₗ[K] V) v = c • v := mem_scalars.mp (Subgroup.mem_subgroupOf.mp hz)
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, hc, map_smul]
  have hodd : Nat.Coprime 2 (Nat.card ρ.ker) := by
    rw [QuotientGroup.ker_mk']
    exact Inputs141d.coprime_two_card_scalars_orthDerived
  have hαβ : ∀ g, ρ (MulAut.conj x g) = MulAut.conj a (ρ g) := fun g => by
    rw [← hxa]
    show ρ (x * g * x⁻¹) = ρ x * ρ g * (ρ x)⁻¹
    rw [map_mul, map_mul, map_inv]
  have hlay := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_conj_projOrth_of_orderOf hQ hT
    hp hp2 hpℓ a hao
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  obtain ⟨n, F, hFq, -, hFsup, -⟩ := Inputs141d.exists_fixedFactors_comm hx
  have hspecle : ∀ r : {r : ↥Rep // (r : K[X]) ≠ X - 1}, specialBlock Q xe ((r.1 : K[X])) ≤ orthDerived Q :=
    fun r => (specialBlock_le_supportedBlock _).trans
      (Inputs141d.supportedBlock_le_orthDerived hQ hT hx hpodd (hRep.1 r.1.2) r.2)
  have hspecperf : ∀ r : {r : ↥Rep // (r : K[X]) ≠ X - 1},
      ⁅specialBlock Q xe ((r.1 : K[X])), specialBlock Q xe ((r.1 : K[X]))⁆ = specialBlock Q xe ((r.1 : K[X])) := by
    intro r
    have hr := hRep.1 r.1.2
    haveI : Fact (Irreducible ((r.1 : K[X]))) := ⟨irreducible_of_mem_primaryFactors hr⟩
    have hm1 : 1 ≤ primaryMultiplicity xe.toLinearMap ((r.1 : K[X])) := by
      have hne := primaryComponent_ne_bot hx.squarefree_minpoly hr
      have : Nontrivial ↥(primaryComponent xe.toLinearMap ((r.1 : K[X]))) := Submodule.nontrivial_iff_ne_bot.mpr hne
      exact Module.finrank_pos
    rcases (show primaryMultiplicity xe.toLinearMap ((r.1 : K[X])) = 1 ∨
        2 ≤ primaryMultiplicity xe.toLinearMap ((r.1 : K[X])) by omega) with h1 | h2
    · rw [hx.specialBlock_eq_bot_of_finrank_eq_one hr h1]
      exact Subgroup.commutator_bot_left ⊥
    · by_cases hself : (r.1 : K[X]) = reciprocalPolynomial (r.1 : K[X])
      · exact commutator_eq_self_of_isQuasisimple
          (hx.isQuasisimple_specialBlock_selfDual hp (by omega) hr r.2 hself h2)
      · exact commutator_eq_self_of_isQuasisimple
          (hx.isQuasisimple_specialBlock_paired hp (by omega) hr r.2 hself h2)
  have hsBC : ∀ w (hwΩ : w ∈ orthDerived Q), w ∈ supportedBlock Q xe (X - 1) →
      (⟨w, hwΩ⟩ : ↥(orthDerived Q)) ∈ fixSubgroup (MulAut.conj x) := by
    intro w hwΩ hw
    rw [fixSubgroup_conj_eq_centralizer', Subgroup.mem_centralizer_singleton_iff]
    have h1 := (Subgroup.mem_inf.mp (supportedBlock_le_isometryCentralizer (X - 1) hw)).2
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    exact Subtype.ext h1
  have hW : ∃ BW : Subgroup ↥(orthDerived Q),
      (BW ≤ fixSubgroup (MulAut.conj x)) ∧
      (⁅BW, BW⁆ = BW ∨ (Nat.Coprime p (Nat.card BW) ∧
        ∀ c ∈ fixSubgroup (MulAut.conj x), ∀ b ∈ BW, c * b * c⁻¹ ∈ BW)) ∧
      ∀ w ∈ supportedBlock Q xe (X - 1), ∀ hwΩ : w ∈ orthDerived Q, IsPGroup 2 ↥(Subgroup.zpowers w) →
        (⟨w, hwΩ⟩ : ↥(orthDerived Q)) ∈ BW := by
    by_cases hlist : FixedLayerListed Q xe
    ·
      refine ⟨(supportedFixedDerived Q xe).subgroupOf (orthDerived Q), fun g hg => ?_, Or.inl ?_, ?_⟩
      · exact hsBC _ g.2 (supportedFixedDerived_le_supportedBlock (Subgroup.mem_subgroupOf.1 hg))
      · refine commutator_subgroupOf_eq hx.supportedFixedDerived_le_orthDerived ?_
        rw [← hFsup hlist]
        exact commutator_iSup_eq_of_perfect F fun i => commutator_eq_self_of_isQuasisimple (hFq i).1
      · intro w hw hwΩ _
        exact Subgroup.mem_subgroupOf.2
          (Inputs141d.mem_supportedFixedDerived_of_mem_orthDerived hQ hx hpodd hlist hw hwΩ)
    · by_cases hsmall : SmallFixedException (Q.comp (fixedSpace xe).subtype)
      ·
        have hQW := hx.polarBilin_fixed_nondegenerate
        have hcopO : Nat.Coprime p
            (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace xe).subtype))) := by
          rw [Nat.Prime.coprime_iff_not_dvd hp]
          intro hdvd
          rcases hsmall with ⟨-, h3⟩ | ⟨h4, hK23⟩
          · exact card_ne_three_of_charTwo h3
          · obtain ⟨hprimes, -⟩ :=
              (CFSG.LocalAnalysis.ComponentInitial.orthogonal_low_dimensional_fixed_derived_component_coverage
                (Q.comp (fixedSpace xe).subtype) hQW (Or.inr (Or.inr h4))).1 (Or.inr ⟨h4, hK23⟩)
            rcases hprimes p hp hdvd with h | h <;> omega
        have hcardSB : Nat.card ↥(supportedBlock Q xe (X - 1)) =
            Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace xe).subtype)) := by
          refine Nat.card_congr (Equiv.ofBijective
            (fun g => (⟨restrictFixed Q xe g, restrictFixed_mem_orthogonalGroup g⟩ :
              ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace xe).subtype))))
            ⟨fun g g' h => restrictFixed_injective hx (congrArg Subtype.val h), fun φ => ?_⟩)
          obtain ⟨g, hg⟩ := restrictFixed_surjective hx φ.1 φ.2
          exact ⟨g, Subtype.ext hg⟩
        refine ⟨(supportedBlock Q xe (X - 1)).subgroupOf (orthDerived Q), fun g hg => hsBC _ g.2
          (Subgroup.mem_subgroupOf.1 hg), Or.inr ⟨?_, fun c hc b hb => ?_⟩, fun w hw hwΩ _ =>
            Subgroup.mem_subgroupOf.2 hw⟩
        · have h1 : Nat.card ↥((supportedBlock Q xe (X - 1)).subgroupOf (orthDerived Q)) ∣
              Nat.card ↥(supportedBlock Q xe (X - 1)) := by
            rw [← Subgroup.card_map_of_injective (orthDerived Q).subtype_injective,
              Subgroup.subgroupOf_map_subtype]
            exact Subgroup.card_dvd_of_le inf_le_left
          exact Nat.Coprime.coprime_dvd_right (h1.trans hcardSB.dvd) hcopO
        · rw [Subgroup.mem_subgroupOf] at hb ⊢
          have hcC : (c : V ≃ₗ[K] V) ∈ isometryCentralizer Q xe := by
            refine Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup c.2, ?_⟩
            rw [fixSubgroup_conj_eq_centralizer', Subgroup.mem_centralizer_singleton_iff] at hc
            rw [Subgroup.mem_centralizer_singleton_iff]
            exact congrArg Subtype.val hc
          exact conj_mem_supportedBlock hcC hb
      ·
        refine ⟨⊥, bot_le, Or.inl (Subgroup.commutator_bot_left ⊥), fun w hw hwΩ hw2 => ?_⟩
        have hdim : finrank K (fixedSpace xe) ≤ 2 := by
          by_contra hd
          exact hlist ⟨by omega, hsmall⟩
        obtain ⟨m, hm⟩ := Inputs141d.exists_pow_eq_one_of_isPGroup hw2
        have hφm : restrictFixed Q xe ⟨w, hw⟩ ^ (2 ^ m) = 1 := by
          rw [← map_pow]
          have e1 : (⟨w, hw⟩ : ↥(supportedBlock Q xe (X - 1))) ^ (2 ^ m) = 1 := Subtype.ext (by simpa using hm)
          rw [e1, map_one]
        have hφ1 : restrictFixed Q xe ⟨w, hw⟩ = 1 := by
          by_cases hX : (X - 1 : K[X]) ∈ primaryFactors xe.toLinearMap
          · have hD := hx.dicksonHom_eq_restrict_of_mem_supportedBlock hpodd hQ hX hw
            have hwev := (mem_omegaGroup.mp (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ hwΩ)).2
            have hw1 : dicksonHom Q hQ ⟨w, (Subgroup.mem_inf.mp (supportedBlock_le_isometryCentralizer _ hw)).1⟩ =
                1 := by
              rw [dicksonHom_apply, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff]
              exact (ZMod.natCast_eq_zero_iff_even).mpr hwev
            rw [hw1, dicksonHom_apply, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff] at hD
            have hev : Even (finrank K (commSpace (restrictFixed Q xe ⟨w, hw⟩))) :=
              (ZMod.natCast_eq_zero_iff_even).mp hD.symm
            exact eq_one_of_pow_two_of_even_finrank_commSpace hdim hφm hev
          · refine LinearEquiv.ext fun v => Subtype.ext ?_
            have hv : (v : V) ∈ (⊥ : Submodule K V) := by
              rw [← fixedSpace_eq_bot_of_not_mem hX]
              exact v.2
            have h0 : (v : V) = 0 := (Submodule.mem_bot K).1 hv
            have h1 : ((restrictFixed Q xe ⟨w, hw⟩ v : fixedSpace xe) : V) ∈ (⊥ : Submodule K V) := by
              rw [← fixedSpace_eq_bot_of_not_mem hX]
              exact (restrictFixed Q xe ⟨w, hw⟩ v).2
            rw [(Submodule.mem_bot K).1 h1]
            exact h0.symm
        have hw1 : w = 1 := hx.eq_one_of_restrictFixed_eq_one hw hφ1
        rw [Subgroup.mem_bot]
        exact Subtype.ext hw1
  obtain ⟨BW, hBWC, hBW, hBW2⟩ := hW
  let B : Option {r : ↥Rep // (r : K[X]) ≠ X - 1} → Subgroup ↥(orthDerived Q) := fun o =>
    match o with
    | none => BW
    | some r => (specialBlock Q xe ((r.1 : K[X]))).subgroupOf (orthDerived Q)
  refine twoInCoreLayer_of_cover ρ (QuotientGroup.mk'_surjective _) hker hodd (MulAut.conj x) (MulAut.conj a) hαβ
    hp hlay B ?_ ?_ ?_
  · rintro (_ | r)
    · exact hBWC
    · intro g hg
      rw [fixSubgroup_conj_eq_centralizer', Subgroup.mem_centralizer_singleton_iff]
      have h1 := (Subgroup.mem_inf.mp (specialBlock_le_isometryCentralizer _ (Subgroup.mem_subgroupOf.1 hg))).2
      rw [Subgroup.mem_centralizer_singleton_iff] at h1
      exact Subtype.ext h1
  · rintro (_ | r)
    · exact hBW
    · left
      exact commutator_subgroupOf_eq (hspecle r) (hspecperf r)
  · intro g hg hg2
    have hgx : g ∈ Subgroup.centralizer ({x} : Set ↥(orthDerived Q)) := by
      rw [← fixSubgroup_conj_eq_centralizer']
      exact hg
    have hgC : (g : V ≃ₗ[K] V) ∈ isometryCentralizer Q xe := by
      refine Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup g.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hgx ⊢
      exact congrArg Subtype.val hgx
    have hg2' : IsPGroup 2 ↥(Subgroup.zpowers (g : V ≃ₗ[K] V)) := by
      have h1 := hg2.map (orthDerived Q).subtype
      rwa [MonoidHom.map_zpowers] at h1
    obtain ⟨w, hw, hwΩ, hw2, z, hz, hgwz⟩ := exists_two_decomp_p hQ hT hx hpodd hRep hgC g.2 hg2'
    have hzΩ : z ∈ orthDerived Q := by
      have e2 : z = w⁻¹ * (g : V ≃ₗ[K] V) := by rw [hgwz, inv_mul_cancel_left]
      rw [e2]
      exact mul_mem (inv_mem hwΩ) g.2
    have hgeq : g = ⟨w, hwΩ⟩ * ⟨z, hzΩ⟩ := Subtype.ext hgwz
    rw [hgeq]
    refine mul_mem (Subgroup.mem_iSup_of_mem none (hBW2 w hw hwΩ hw2)) ?_
    have hzmem : (⟨z, hzΩ⟩ : ↥(orthDerived Q)) ∈
        ⨆ r : {r : ↥Rep // (r : K[X]) ≠ X - 1}, (specialBlock Q xe ((r.1 : K[X]))).subgroupOf (orthDerived Q) := by
      rw [← subgroupOf_iSup_of_le _ _ hspecle]
      exact Subgroup.mem_subgroupOf.mpr hz
    exact (iSup_le fun r => le_iSup B (some r) : (⨆ r : {r : ↥Rep // (r : K[X]) ≠ X - 1},
      (specialBlock Q xe ((r.1 : K[X]))).subgroupOf (orthDerived Q)) ≤ ⨆ o, B o) hzmem

end OrthInnerP

section OrthCatalogue

open Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.RankThree.Classical2 (orthDerived ProjOrthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)

theorem input14_1BadSimpleOn_orthogonal :
    Input14_1BadSimpleOn fun _ d => ∃ r q, d = TauCeti.LieTypeIndex.D r q ∨ d = TauCeti.LieTypeIndex.twistedD r q := by
  intro p hp hp5 S _ _ hS hna idx hd hchar he β hβ hβ1
  haveI := hS
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := he
  have hor : (∃ r q, idx.1 = TauCeti.LieTypeIndex.B r q ∧ q.p ≠ 2 ∧ 3 ≤ r) ∨
      (∃ r q, idx.1 = TauCeti.LieTypeIndex.D r q) ∨ ∃ r q, idx.1 = TauCeti.LieTypeIndex.twistedD r q := by
    obtain ⟨r, q, hrq | hrq⟩ := hd
    · exact Or.inr (Or.inl ⟨r, q, hrq⟩)
    · exact Or.inr (Or.inr ⟨r, q, hrq⟩)
  obtain ⟨t, n, f, ht, hG⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_statedClassicalModel_orth idx hor e
  have hℓ2 : CFSG.HardMathSupport.Solomon.Coordinator.lieIndexChar idx.1 = 2 := by
    rw [Inputs141d.lieIndexChar_eq_characteristic]
    exact hchar
  rw [hℓ2] at hG
  by_cases hin : ∃ a : S, MulAut.conj a = β
  ·
    obtain ⟨a, rfl⟩ := hin
    obtain ⟨K, _, _, V, _, _, _, Q, hQ, hT, hring, ⟨e'⟩⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_projOrth_model ht hG
    haveI : CharP K 2 := hring ▸ ringChar.charP K
    have hap : a ^ p = 1 := pow_eq_one_of_conj_pow_eq_one hna hβ
    have ha1 : e' a ≠ 1 := by
      intro h1
      apply hβ1
      rw [show a = 1 from e'.injective (h1.trans (map_one e').symm), map_one]
    refine twoInCoreLayer_of_congr e' hp ?_
    rw [Inputs141d.congr_conj_eq]
    exact twoInCoreLayer_conj_orth hQ hT hp hp5 (e' a) (by rw [← map_pow, hap, map_one]) ha1
  ·
    have hout : ∀ a : S, MulAut.conj a ≠ β := fun a h => hin ⟨a, h⟩
    have hc : CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OmegaFieldConj S β 2 p := by
      rcases ht with rfl | rfl | rfl
      · exfalso
        exact hG.1.2.2.2 rfl
      · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.omegaFieldConj_plus hp (by omega) hG
          (fun _ => by omega) β hβ hout
      · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.omegaFieldConj_minus hp (by omega) hG β hβ hout
    obtain ⟨K, _, _, k', d, Q₀, Q, σ, Sf, e', -, hch, he'⟩ := hc.out
    haveI : CharP K 2 := hch ▸ ringChar.charP K
    have hd0 : 0 < d := three_le_of_totallySingular k' Sf.hT₀
    have hfix : fixSubgroup (fieldAutT Q σ Sf.hQσ) = subfieldDerivedImage k' Sf.hext := by
      have h1 : fixSubgroup (fieldAutT Q σ Sf.hQσ) = subfieldFixedGroup k' Q₀ Q :=
        Subgroup.ext fun t => (mem_fixSubgroup).trans (fieldAutT_apply_iff Sf t)
      rw [h1]
      exact le_antisymm (CFSG.RankThree.PartOne.FieldFix.subfieldFixedGroup_le_derivedImage Sf.hext Sf.hnd₀ Sf.hT₀
        Sf.hnd) (subfieldDerivedImage_le k' Sf.hext)
    obtain ⟨hsimp, hnonab⟩ := matrix_simple_nonabelian hd0 Sf.hnd₀ Sf.hT₀
    have hJq : CFSG.IsQuasisimple ↥(subfieldDerivedImage k' Sf.hext) :=
      CFSG.IsQuasisimple.of_mulEquiv (inclEquiv k' Sf.hext hd0).symm
        (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isQuasisimple_of_isSimpleGroup hsimp hnonab)
    have hmodel : ⁅fixSubgroup (MulAut.congr e' β), fixSubgroup (MulAut.congr e' β)⁆ =
        fixSubgroup (MulAut.congr e' β) := by
      rw [he', hfix]
      exact commutator_eq_self_of_isQuasisimple hJq
    rw [Inputs141c.fixSubgroup_congr] at hmodel
    have hperf : ⁅fixSubgroup β, fixSubgroup β⁆ = fixSubgroup β := by
      apply Subgroup.map_injective (f := e'.toMonoidHom) e'.injective
      rw [Subgroup.map_commutator]
      exact hmodel
    have hF : CFSG.Yardstones.Md42047359a2a.lieFamily idx.1 =
        CFSG.Yardstones.Md42047359a2a.LieFamily.symplecticOrthogonal := by
      obtain ⟨r, q, hrq | hrq⟩ := hd <;> rw [hrq] <;> rfl
    have hlay : PerfectInLayer β :=
      (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieCompsOn_symplecticOrthogonal hp hp5 S hS hna idx hF ⟨e⟩
        β hβ hβ1 (Or.inl (by rw [hℓ2]; omega))).layer
    exact twoInCoreLayer_of_fixSubgroup hp hlay (Or.inl hperf)

end OrthCatalogue

theorem input14_1BadSimpleOn_symplecticOrthogonal :
    Input14_1BadSimpleOn fun p d =>
      CFSG.Yardstones.Md42047359a2a.lieFamily d = CFSG.Yardstones.Md42047359a2a.LieFamily.symplecticOrthogonal ∧
      ¬ (p = 5 ∧ ∃ r q, d = TauCeti.LieTypeIndex.B r q ∧ (q.card = 2 ∨ (r = 2 ∧ q.card = 32))) := by
  intro p hp hp5 S _ _ hS hnc d hd hchar
  obtain ⟨d, hv⟩ := d
  obtain ⟨hF, hexc⟩ := hd
  cases d with
  | B r q =>
    have hR : ∃ r' q', TauCeti.LieTypeIndex.B r q = TauCeti.LieTypeIndex.B r' q' ∧
        ¬ (p = 5 ∧ (q'.card = 2 ∨ (r' = 2 ∧ q'.card = 32))) :=
      ⟨r, q, rfl, fun h => hexc ⟨h.1, r, q, rfl, h.2⟩⟩
    exact input14_1BadSimpleOn_symplectic p hp hp5 S hS hnc ⟨_, hv⟩ hR hchar
  | C r q =>
    exfalso
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    have hq2 : q.p = 2 := by
      rw [← TauCeti.LieTypeIndex.characteristic_C r q]
      exact hchar
    exact hr.2 hq2
  | D r q => exact input14_1BadSimpleOn_orthogonal p hp hp5 S hS hnc ⟨_, hv⟩ ⟨r, q, Or.inl rfl⟩ hchar
  | twistedD r q => exact input14_1BadSimpleOn_orthogonal p hp hp5 S hS hnc ⟨_, hv⟩ ⟨r, q, Or.inr rfl⟩ hchar
  | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hF

section Suzuki

open CFSG.Blueprint CFSG.LieType.Ree CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)
open CFSG.HardMathSupport.Dickson.SuzukiReeB (exists_eq_conj_of_mem_range fixSubgroup_conj)

theorem twoInCoreLayer_of_isQuasisimple_fixSubgroup {S : Type} [Group S] [Finite S] {β : MulAut S} {p : ℕ}
    (hp : p.Prime) (hq : CFSG.Open.IsQuasisimple ↥(fixSubgroup β)) : TwoInCoreLayer p β := fun x hx _ =>
  le_core_sup_layer_of_isComponentOf hp ⟨le_rfl, CFSG.Open.IsSubnormal.refl _, hq⟩ hx

theorem twoInCoreLayer_of_coprime_fixSubgroup {S : Type} [Group S] [Finite S] {β : MulAut S} {p : ℕ}
    (hp : p.Prime) (h : Nat.Coprime p (Nat.card (fixSubgroup β))) : TwoInCoreLayer p β := fun x hx _ =>
  Subgroup.mem_sup_left (le_glaPPrimeCoreOf_of_isSubnormal hp (CFSG.Open.IsSubnormal.refl _) h hx)

theorem twoInCoreLayer_suzukiGroup {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hexc : p = 5 → a ≠ 2)
    {β : MulAut (suzukiGroup a K)} (hβ : β ^ p = 1) (hβ1 : β ≠ 1) : TwoInCoreLayer p β := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hfin : Finite (suzukiGroup a K) := (suzuki_simple ha hK).1
  have hord : orderOf β = p := orderOf_eq_prime hβ hβ1
  have hp2 : p ≠ 2 := by omega
  by_cases hin : β ∈ inner (suzukiGroup a K)
  · obtain ⟨x, rfl, hxp, hx1⟩ := exists_eq_conj_of_mem_range
      (CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot ha hK) hin hβ hβ1
    have hodd : Odd (orderOf x) := by
      rw [orderOf_eq_prime hxp hx1]
      exact hp.odd_of_ne_two hp2
    obtain ⟨hcard, -⟩ :=
      (CFSG.RankThree.Suzuki_involution_centralizers_and_inner_odd_centralizers ha hK).2 x hx1 hodd
    intro g hg hg2
    rw [fixSubgroup_conj] at hg
    have hg1 : g = 1 := by
      obtain ⟨k₀, hk₀⟩ := hg2 ⟨g, Subgroup.mem_zpowers g⟩
      have hgk : g ^ (2 ^ k₀) = 1 := by simpa using congrArg Subtype.val hk₀
      have h1 : orderOf g ∣ 2 ^ k₀ := orderOf_dvd_of_pow_eq_one hgk
      have h2 : orderOf g ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set (suzukiGroup a K))) := by
        rw [← Subgroup.orderOf_mk g hg]
        exact orderOf_dvd_natCard _
      have h3 : Nat.Coprime (2 ^ k₀) (Nat.card ↥(Subgroup.centralizer ({x} : Set (suzukiGroup a K)))) :=
        Nat.Coprime.pow_left k₀ (Nat.coprime_two_left.2 hcard)
      exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes h3 h1 h2)
    rw [hg1]
    exact one_mem _
  · obtain ⟨σ, h, b, k, _, _, -, hab, hk, hconj, ⟨efix⟩⟩ :=
      CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent a ha K hK p hp hp2 β hord hin
    refine twoInCoreLayer_of_conj (MulAut.conj h) hp ?_
    rw [hconj]
    rcases Nat.eq_zero_or_pos b with hb0 | hb1
    · subst hb0
      have hk2 : Nat.card k = 2 := by rw [hk]; norm_num
      have hcard := (suzuki_two_normal_five_complement_core_trivial hk2).1
      have hp7 : 7 ≤ p := by
        have hpa : p = 2 * a + 1 := by omega
        rcases (show p = 5 ∨ p = 6 ∨ 7 ≤ p by omega) with h5 | h6 | h7
        · exact absurd (by omega : a = 2) (hexc h5)
        · rw [h6] at hp
          norm_num at hp
        · exact h7
      refine twoInCoreLayer_of_coprime_fixSubgroup hp ?_
      have h1 : Nat.card ↥(fixSubgroup (szFieldAut a K σ)) = 20 :=
        (Nat.card_congr efix.toEquiv).trans hcard
      rw [h1, show (20 : ℕ) = 2 ^ 2 * 5 by norm_num]
      refine Nat.Coprime.mul_right (Nat.Coprime.pow_right 2 ((Nat.coprime_primes hp Nat.prime_two).2 hp2)) ?_
      exact (Nat.coprime_primes hp Nat.prime_five).2 (by omega)
    · obtain ⟨hfink, hsk, hnck⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suzukiGroup_simple_nonab hb1 hk
      haveI := hfink
      haveI := hsk
      haveI : IsSimpleGroup ↥(fixSubgroup (szFieldAut a K σ)) := efix.isSimpleGroup
      have hnc : ∃ x y : ↥(fixSubgroup (szFieldAut a K σ)), x * y ≠ y * x := by
        obtain ⟨x, y, hxy⟩ := hnck
        exact ⟨efix.symm x, efix.symm y, fun h => hxy (efix.symm.injective (by
          rw [map_mul, map_mul]
          exact h))⟩
      exact twoInCoreLayer_of_isQuasisimple_fixSubgroup hp
        (CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_isQuasisimple_of_simple hnc)

theorem input14_1BadSimpleOn_suzuki :
    Input14_1BadSimpleOn fun p d => ∃ m, d = TauCeti.LieTypeIndex.suzuki m ∧ ¬ (p = 5 ∧ m = 2) := by
  intro p hp hp5 S _ _ _ _ d hd _ he β hβ hβ1
  obtain ⟨d, hv⟩ := d
  obtain ⟨m, rfl, hexc⟩ := hd
  obtain ⟨e⟩ := he
  obtain ⟨-, a, ha, K, _, _, hf, hK', ⟨θ⟩⟩ := CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK', hf]
  have ham : a = m := by omega
  refine twoInCoreLayer_of_congr (e.trans θ) hp ?_
  refine twoInCoreLayer_suzukiGroup ha hK hp hp5 (fun h5 h2 => hexc ⟨h5, ham ▸ h2⟩)
    (by rw [← map_pow, hβ, map_one]) ?_
  intro h
  exact hβ1 ((MulAut.congr (e.trans θ)).injective (by rw [h, map_one]))

end Suzuki

theorem input14_1BadOn_exc5 : Input14_1BadOn fun p d =>
    p = 5 ∧ (d = TauCeti.LieTypeIndex.suzuki 2 ∨ d = TauCeti.LieTypeIndex.reeF4 2 ∨ d = TauCeti.LieTypeIndex.tits) := by
  intro p _ _ X _ _ K Z _ d hd _ he _ _ _ _ hexc _ _ _
  exfalso
  obtain ⟨h5, hd⟩ := hd
  apply hexc h5
  rcases hd with hd | hd | hd
  · exact Or.inr (Or.inr ⟨d, hd, he⟩)
  · exact Or.inr (Or.inl ⟨d, hd, he⟩)
  · exact Or.inl ⟨d, hd, he⟩

theorem input14_1BadOn_char_ne_two : Input14_1BadOn fun _ d => d.characteristic ≠ 2 :=
  fun _ _ _ _ _ _ _ _ _ _ hd hchar => absurd hchar hd

section Tits


theorem false_of_plane_tits (d : TauCeti.ValidLieTypeIndex) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hd : d.1 = TauCeti.LieTypeIndex.tits ∧ p ≠ 5) (E : Subgroup (MulAut (CFSG.LieType.SeitzGeneration.Cat d)))
    (hc : Nat.card E = p ^ 2) : False := by
  obtain ⟨d, hv⟩ := d
  obtain ⟨hd, h5⟩ := hd
  subst hd
  exact CFSG.LieType.SeitzGeneration.no_plane_tits hv hp (by omega) (by omega) h5 hc

theorem input14_1BadOn_tits : Input14_1BadOn fun p d => d = TauCeti.LieTypeIndex.tits ∧ p ≠ 5 :=
  input14_1BadOn_of_noPlane fun d _ hp hp5 hd _ E _ hc => false_of_plane_tits d hp hp5 hd E hc

theorem input23_11TwoOn_tits : Input23_11TwoOn fun p d => d = TauCeti.LieTypeIndex.tits ∧ p ≠ 5 :=
  input23_11TwoOn_of_noPlane fun d _ hp hp5 hd _ E _ hc => false_of_plane_tits d hp hp5 hd E hc

end Tits

@[expose] def Input14_1BadRest : Prop :=
  Input14_1BadOn fun p d =>
    CFSG.Yardstones.Md42047359a2a.lieFamily d = CFSG.Yardstones.Md42047359a2a.LieFamily.exceptional ∨
      (∃ m, d = TauCeti.LieTypeIndex.reeF4 m ∧ ¬ (p = 5 ∧ m = 2)) ∨
      (p = 5 ∧ ∃ r q, d = TauCeti.LieTypeIndex.B r q ∧ (q.card = 2 ∨ (r = 2 ∧ q.card = 32)))

section Assembly


theorem input14_1Bad_of_rest (h : Input14_1BadRest) : Inputs2323.Input14_1Bad := by
  apply input14_1Bad_of_on
  have hLU := input14_1BadOn_of_simple input14_1BadSimpleOn_linearUnitary
  have hSO := input14_1BadOn_of_simple input14_1BadSimpleOn_symplecticOrthogonal
  have hSz := input14_1BadOn_of_simple input14_1BadSimpleOn_suzuki
  have hall := input14_1BadOn_or (input14_1BadOn_or (input14_1BadOn_or hLU hSO) (input14_1BadOn_or hSz
    input14_1BadOn_exc5)) (input14_1BadOn_or (input14_1BadOn_or input14_1BadOn_char_ne_two input14_1BadOn_tits) h)
  refine Input14_1BadOn.mono (fun p d _ => ?_) hall
  cases d with
  | A r q => exact Or.inl (Or.inl (Or.inl rfl))
  | twistedA r q => exact Or.inl (Or.inl (Or.inl rfl))
  | B r q =>
    by_cases hb : p = 5 ∧ (q.card = 2 ∨ (r = 2 ∧ q.card = 32))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hb.1, r, q, rfl, hb.2⟩)))
    · refine Or.inl (Or.inl (Or.inr ⟨rfl, fun h' => hb ⟨h'.1, ?_⟩⟩))
      obtain ⟨-, r', q', he', hq'⟩ := h'
      cases he'
      exact hq'
  | C r q =>
    refine Or.inl (Or.inl (Or.inr ⟨rfl, fun h' => ?_⟩))
    obtain ⟨-, r', q', he', -⟩ := h'
    cases he'
  | D r q => exact Or.inl (Or.inl (Or.inr ⟨rfl, fun h' => by obtain ⟨-, r', q', he', -⟩ := h'; cases he'⟩))
  | twistedD r q => exact Or.inl (Or.inl (Or.inr ⟨rfl, fun h' => by obtain ⟨-, r', q', he', -⟩ := h'; cases he'⟩))
  | E6 q => exact Or.inr (Or.inr (Or.inl rfl))
  | E7 q => exact Or.inr (Or.inr (Or.inl rfl))
  | E8 q => exact Or.inr (Or.inr (Or.inl rfl))
  | F4 q => exact Or.inr (Or.inr (Or.inl rfl))
  | G2 q => exact Or.inr (Or.inr (Or.inl rfl))
  | twistedE6 q => exact Or.inr (Or.inr (Or.inl rfl))
  | trialityD4 q => exact Or.inr (Or.inr (Or.inl rfl))
  | suzuki m =>
    by_cases hm : p = 5 ∧ m = 2
    · obtain ⟨h5, rfl⟩ := hm
      exact Or.inl (Or.inr (Or.inr ⟨h5, Or.inl rfl⟩))
    · exact Or.inl (Or.inr (Or.inl ⟨m, rfl, hm⟩))
  | reeG2 m => exact Or.inr (Or.inl (Or.inl (by rw [TauCeti.LieTypeIndex.characteristic_reeG2]; norm_num)))
  | reeF4 m =>
    by_cases hm : p = 5 ∧ m = 2
    · obtain ⟨h5, rfl⟩ := hm
      exact Or.inl (Or.inr (Or.inr ⟨h5, Or.inr (Or.inl rfl)⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rfl, hm⟩)))
  | tits =>
    by_cases h5 : p = 5
    · exact Or.inl (Or.inr (Or.inr ⟨h5, Or.inr (Or.inr rfl)⟩))
    · exact Or.inr (Or.inl (Or.inr ⟨rfl, h5⟩))

theorem input23_23N_of_rest (hI11 : Inputs2323.Input23_11Two) (h : Input14_1BadRest) : Claims1314c2.Input23_23N :=
  Inputs2323.input23_23N_of_inputs hI11 (input14_1Bad_of_rest h)

end Assembly

section LinearGen

open CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartOne.CTP (FieldAutData)
open CFSG.GorensteinWalter (PSL2)

theorem uniPlaneGen_outer_A1_even {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) (hq2 : q.p = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hex : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException p (.A 1 q))
    {E : Subgroup (MulAut (Cat ⟨.A 1 q, hv⟩))} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hout : ¬ InnerPlane ⟨.A 1 q, hv⟩ p E) : Inputs2311c.UniPlaneGen q.p E := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Fact p.Prime := ⟨hp⟩
  let e : Cat ⟨.A 1 q, hv⟩ ≃* PSL2 (GaloisField q.p q.exponent) :=
    CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have h4 : 4 ≤ q.card := hrange.2 rfl
  have hfour : 3 ≤ 2 ∨ ∃ s : Finset (GaloisField q.p q.exponent), s.card = 4 := by
    right
    have : Fintype (GaloisField q.p q.exponent) := Fintype.ofFinite _
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ :
      Finset (GaloisField q.p q.exponent))) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcardF]; exact h4)
    exact ⟨s, hs⟩
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (n := 2)
    (K := GaloisField q.p q.exponent) le_rfl hfour
  have hperf := (CFSG.LinearGroups.linear_projective_perfect (n := 2)
    (K := GaloisField q.p q.exponent) le_rfl hfour).commutator_eq_top
  have hnab : ∃ a b : PSL2 (GaloisField q.p q.exponent), a * b ≠ b * a :=
    exists_noncomm_of_perfect hperf
  have hchar : ringChar (GaloisField q.p q.exponent) = q.p := ringChar.eq _ _
  have hd : FieldAutData (PSL2 (GaloisField q.p q.exponent)) p := by
    refine fieldAutData_psl2_even_odd_prime hp hp2 ?_ (by rw [hchar, hq2])
    rintro ⟨hp3, h8⟩
    apply hex
    refine Or.inl ⟨hp3, Or.inl ⟨q, hq2, ?_, rfl⟩⟩
    rw [hcardF, TauCeti.PrimePower.card_def, hq2] at h8
    exact Nat.pow_right_injective (le_refl 2) (by simpa using h8)
  have hEi : CFSG.IsElementaryAbelian p (E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = p ^ 2 := by
    rw [card_map_congr, hc]
  have hout' : ¬ ∀ φ ∈ E.map (MulAut.congr e).toMonoidHom, ∃ g, φ = MulAut.conj g := by
    intro h
    exact not_le_range_conj_map_congr e hout fun φ hφ => (h φ hφ).imp fun g hg => hg.symm
  have h := Inputs2311c.uniPlaneGen_of_fieldAutData hnab hp hd
    (fun τ hτ => Inputs2311c.fixedSubgroup_le_closure_psl2 hp (hp.odd_of_ne_two hp2) hτ)
    (E.map (MulAut.congr e).toMonoidHom) hc' hout'
  rw [hchar] at h
  exact (Inputs2311c.uniPlaneGen_map_congr e _ E).1 h

theorem uniSeitzPlanes_outer_A1_even :
    Inputs2311c.UniSeitzPlanes fun d p E =>
      ¬ InnerPlane d p E ∧ (∃ q, d.1 = .A 1 q) ∧ d.1.characteristic = 2 := by
  rintro ⟨d, hv⟩ p hp hp2 _ hex E hE hc ⟨hout, ⟨q, hd⟩, hq2⟩
  subst hd
  have hq2' : q.p = 2 := by simpa using hq2
  have h := uniPlaneGen_outer_A1_even hv hq2' hp hp2 hex hE hc hout
  simpa using h

theorem uniSeitzPlanes_linear_even :
    Inputs2311c.UniSeitzPlanes fun d p _ =>
      IsLinearIndex d.1 ∧ d.1.characteristic = 2 ∧ CentralPrimeFree p d.1 := by
  have hout : Inputs2311c.UniSeitzPlanes fun d p E =>
      ¬ InnerPlane d p E ∧ IsLinearIndex d.1 ∧ d.1.characteristic = 2 ∧ CentralPrimeFree p d.1 := by
    refine Inputs2311c.UniSeitzPlanes.of_cover ?_ Inputs2311c.uniSeitzPlanes_outer_linear
      uniSeitzPlanes_outer_A1_even
    rintro ⟨d, hv⟩ p _ _ E ⟨hin, ⟨m, q, hd⟩, hchar, hcpf⟩
    have hm : 1 ≤ m := by
      subst hd
      exact ((TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
    rcases Nat.lt_or_ge m 2 with h | h
    · right
      have hm1 : m = 1 := by omega
      subst hm1
      exact ⟨hin, ⟨q, hd⟩, hchar⟩
    · left
      exact ⟨hin, ⟨m, q, hd, h⟩, hcpf⟩
  refine Inputs2311c.UniSeitzPlanes.of_cover ?_ Inputs2311c.uniSeitzPlanes_inner_linear hout
  intro d p _ _ E ⟨hlin, hchar, hcpf⟩
  by_cases hin : InnerPlane d p E
  · exact Or.inl ⟨hin, hlin, hcpf⟩
  · exact Or.inr ⟨hin, hlin, hchar, hcpf⟩

theorem input23_11TwoOn_linear :
    Input23_11TwoOn fun p d =>
      CFSG.LieType.SeitzGeneration.IsLinearIndex d ∧ CFSG.LieType.SeitzGeneration.CentralPrimeFree p d :=
  input23_11TwoOn_of_uniSeitzPlanes uniSeitzPlanes_linear_even fun _ _ _ _ hR hchar _ _ _ => ⟨hR.1, hchar, hR.2⟩

end LinearGen

section SuzukiGen

open CFSG.Blueprint CFSG.LieType.Ree CFSG.LieType.SeitzGeneration
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)
open CFSG.RankThree.PartOne.CTP (FieldAutData IsOuterOfOrder fixedSubgroup)

theorem normal_closure_pow_eq_one (F : Type*) [Group F] (n : ℕ) :
    (Subgroup.closure {x : F | x ^ n = 1}).Normal := by
  refine ⟨fun y hy g => ?_⟩
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    have hx' : x ^ n = 1 := hx
    exact Subgroup.subset_closure (show (g * x * g⁻¹) ^ n = 1 by rw [conj_pow, hx', mul_one, mul_inv_cancel])
  | one => rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have he : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [he]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have he : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [he]
    exact Subgroup.inv_mem _ hx

theorem closure_pow_four_eq_top_of_simple {F : Type*} [Group F] [Finite F] [IsSimpleGroup F]
    (h2 : 2 ∣ Nat.card F) : Subgroup.closure {x : F | x ^ 4 = 1} = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := normal_closure_pow_eq_one F 4
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.closure {x : F | x ^ 4 = 1}) with h | h
  · exfalso
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hmem : x ∈ Subgroup.closure {x : F | x ^ 4 = 1} := Subgroup.subset_closure (show x ^ 4 = 1 by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ← hx, pow_orderOf_eq_one, one_pow])
    rw [h, Subgroup.mem_bot] at hmem
    rw [hmem, orderOf_one] at hx
    omega
  · exact h

theorem closure_pow_four_eq_top_of_card_twenty {F : Type*} [Group F] [Finite F] (hF : Nat.card F = 20)
    (hR : ∀ R : Subgroup F, R.Normal → Nat.Coprime (Nat.card R) 5 → R = ⊥) :
    Subgroup.closure {x : F | x ^ 4 = 1} = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := normal_closure_pow_eq_one F 4
  obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 2) (by rw [hF]; norm_num)
  have hSC : S ≤ Subgroup.closure {x : F | x ^ 4 = 1} := fun x hx => by
    refine Subgroup.subset_closure (show x ^ 4 = 1 from ?_)
    have h : (⟨x, hx⟩ : ↥S) ^ Nat.card S = 1 := pow_card_eq_one'
    rw [hS] at h
    simpa using congrArg Subtype.val h
  have h4 : 4 ∣ Nat.card (Subgroup.closure {x : F | x ^ 4 = 1}) := by
    have h := Subgroup.card_dvd_of_le hSC
    rwa [hS] at h
  have h20 : Nat.card (Subgroup.closure {x : F | x ^ 4 = 1}) ∣ 20 := by
    rw [← hF]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨c, hc⟩ := h4
  obtain ⟨d, hd⟩ := h20
  rw [hc] at hd
  have hcd : 5 = c * d := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 4 by norm_num)
    rw [← mul_assoc, ← hd]
  rcases (Nat.dvd_prime Nat.prime_five).1 ⟨d, hcd⟩ with rfl | rfl
  · exfalso
    have h1 := hR _ inferInstance (by rw [hc]; norm_num)
    rw [h1, Subgroup.card_bot] at hc
    omega
  · exact Subgroup.eq_top_of_card_eq _ (by rw [hc, hF])

theorem fixedSubgroup_le_closure_suzuki {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {τ : MulAut (suzukiGroup a K)} (hτ : IsOuterOfOrder p τ) :
    fixedSubgroup τ ≤ Subgroup.closure {x | τ x = x ∧ x ^ 4 = 1} := by
  obtain ⟨hord, hτout⟩ := hτ
  have hin : τ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (suzukiGroup a K) := by
    rintro ⟨g, hg⟩
    exact hτout g hg.symm
  obtain ⟨σ, h, b, k, _, _, -, -, hk, hconj, ⟨efix⟩⟩ :=
    CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent a ha K hK p hp hp2 τ hord hin
  have hF : Subgroup.closure {y : ↥((szFieldAut a K σ).toMonoidHom.eqLocus (MonoidHom.id (suzukiGroup a K))) |
      y ^ 4 = 1} = ⊤ := by
    have h1 : Subgroup.closure {z : suzukiGroup b k | z ^ 4 = 1} = ⊤ := by
      rcases Nat.eq_zero_or_pos b with hb0 | hb1
      · subst hb0
        have hk2 : Nat.card k = 2 := by rw [hk]; norm_num
        obtain ⟨hcard, -, -, -, -, hR⟩ := suzuki_two_normal_five_complement_core_trivial hk2
        haveI : Finite (suzukiGroup 0 k) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
        exact closure_pow_four_eq_top_of_card_twenty hcard hR
      · obtain ⟨hfink, hsk, -⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suzukiGroup_simple_nonab hb1 hk
        haveI := hfink
        haveI := hsk
        refine closure_pow_four_eq_top_of_simple ?_
        rw [suzuki_order hk]
        exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow (dvd_pow_self 2 (by omega)) two_ne_zero) _) _
    rw [eq_top_iff]
    intro y _
    have h2 : efix y ∈ Subgroup.closure {z : suzukiGroup b k | z ^ 4 = 1} := by
      rw [h1]
      exact Subgroup.mem_top _
    have h3 : efix.symm (efix y) ∈
        (Subgroup.closure {z : suzukiGroup b k | z ^ 4 = 1}).map efix.symm.toMonoidHom :=
      Subgroup.mem_map_of_mem _ h2
    rw [MulEquiv.symm_apply_apply, MonoidHom.map_closure] at h3
    refine Subgroup.closure_mono ?_ h3
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z ^ 4 = 1 := hz
    show (efix.symm z) ^ 4 = 1
    rw [← map_pow, hz', map_one]
  have hτf : ∀ w, τ w = h⁻¹ * szFieldAut a K σ (h * w * h⁻¹) * h := by
    intro w
    have h1 : szFieldAut a K σ (h * w * h⁻¹) =
        (MulAut.conj h * τ * (MulAut.conj h)⁻¹) (h * w * h⁻¹) := by rw [hconj]
    have e1 : h⁻¹ * (h * w * h⁻¹) * h = w := by group
    rw [h1]
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, e1]
    group
  intro x hx
  have hx' : τ x = x := hx
  have hyL : h * x * h⁻¹ ∈ (szFieldAut a K σ).toMonoidHom.eqLocus (MonoidHom.id (suzukiGroup a K)) := by
    show szFieldAut a K σ (h * x * h⁻¹) = h * x * h⁻¹
    have h1 := hτf x
    rw [hx'] at h1
    calc szFieldAut a K σ (h * x * h⁻¹) = h * (h⁻¹ * szFieldAut a K σ (h * x * h⁻¹) * h) * h⁻¹ := by group
      _ = h * x * h⁻¹ := by rw [← h1]
  have hmem : (⟨h * x * h⁻¹, hyL⟩ :
      ↥((szFieldAut a K σ).toMonoidHom.eqLocus (MonoidHom.id (suzukiGroup a K)))) ∈
      Subgroup.closure {y : ↥((szFieldAut a K σ).toMonoidHom.eqLocus (MonoidHom.id (suzukiGroup a K))) |
        y ^ 4 = 1} := by
    rw [hF]
    exact Subgroup.mem_top _
  have hmap := Subgroup.mem_map_of_mem ((MulAut.conj h⁻¹).toMonoidHom.comp
    ((szFieldAut a K σ).toMonoidHom.eqLocus (MonoidHom.id (suzukiGroup a K))).subtype) hmem
  rw [MonoidHom.map_closure] at hmap
  have hxe : ((MulAut.conj h⁻¹).toMonoidHom.comp
      ((szFieldAut a K σ).toMonoidHom.eqLocus (MonoidHom.id (suzukiGroup a K))).subtype) ⟨h * x * h⁻¹, hyL⟩ = x := by
    show MulAut.conj h⁻¹ (h * x * h⁻¹) = x
    rw [MulAut.conj_apply]
    group
  rw [hxe] at hmap
  refine Subgroup.closure_mono ?_ hmap
  rintro _ ⟨z, hz, rfl⟩
  have hz4 : z ^ 4 = 1 := hz
  have hzL : szFieldAut a K σ (z : suzukiGroup a K) = z := z.2
  have hze : ((MulAut.conj h⁻¹).toMonoidHom.comp
      ((szFieldAut a K σ).toMonoidHom.eqLocus (MonoidHom.id (suzukiGroup a K))).subtype) z =
      MulAut.conj h⁻¹ (z : suzukiGroup a K) := rfl
  rw [hze]
  refine ⟨?_, ?_⟩
  · rw [hτf]
    have e1 : h * MulAut.conj h⁻¹ (z : suzukiGroup a K) * h⁻¹ = z := by
      rw [MulAut.conj_apply]
      group
    rw [e1, hzL, MulAut.conj_apply]
    group
  · rw [← map_pow, ← SubgroupClass.coe_pow, hz4, OneMemClass.coe_one, map_one]

theorem uniPlaneGen_suzukiGroup {a : ℕ} (ha : 1 ≤ a)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hne : a = 2 → p ≠ 5) (E : Subgroup (MulAut (suzukiGroup a K))) [CFSG.IsElementaryAbelian p E]
    (hc : Nat.card E = p ^ 2) (hout : ¬ ∀ φ ∈ E, ∃ g : suzukiGroup a K, φ = MulAut.conj g) :
    Inputs2311c.UniPlaneGen 2 E := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨-, -, hnab⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suzukiGroup_simple_nonab ha hK
  haveI := (suzuki_simple ha hK).2.2
  have hd : FieldAutData (suzukiGroup a K) p := CFSG.RankThree.PartOne.SEITZ2.fieldAutData_suzuki
    CFSG.RankThree.PartOne.SEITZ10.subfieldPairSz_holds hp hp5 ha hK hne
  have h4 := Inputs2311c.uniPlaneGen_of_fieldAutData hnab hp hd
    (fun τ hτ => fixedSubgroup_le_closure_suzuki ha hK hp hp2 hτ) E hc hout
  unfold Inputs2311c.UniPlaneGen Inputs2311c.uniPlaneClosure at h4 ⊢
  rw [eq_top_iff] at h4 ⊢
  refine h4.trans (Subgroup.closure_mono ?_)
  rintro s ⟨e, he, he1, hes, n, hn⟩
  refine ⟨e, he, he1, hes, 2 * n, ?_⟩
  have h22 : (2 : ℕ) ^ (2 * n) = 4 ^ n := by rw [pow_mul]; norm_num
  rw [h22]
  exact hn

theorem uniSeitzPlanes_suzuki :
    Inputs2311c.UniSeitzPlanes fun d p _ => (∃ m, d.1 = TauCeti.LieTypeIndex.suzuki m) ∧ 5 ≤ p := by
  rintro ⟨d, hv⟩ p hp hp2 _ hex E hE hc ⟨⟨m, hd⟩, hp5⟩
  subst hd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, a, ha, K, _, _, hf, hK', ⟨θ⟩⟩ := CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK', hf]
  have ham : a = m := by omega
  have hne : a = 2 → p ≠ 5 := fun h2 h5 => hex (Or.inr ⟨h5, Or.inr (by
    show TauCeti.LieTypeIndex.suzuki m = TauCeti.LieTypeIndex.suzuki 2
    rw [show m = 2 by omega])⟩)
  haveI hEi : CFSG.IsElementaryAbelian p (E.map (MulAut.congr θ).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mpr (isElemAbelian_map_congr θ hE)
  have hc' : Nat.card (E.map (MulAut.congr θ).toMonoidHom) = p ^ 2 := by rw [card_map_congr, hc]
  have hout' : ¬ ∀ φ ∈ E.map (MulAut.congr θ).toMonoidHom, ∃ g, φ = MulAut.conj g := by
    intro h
    exact not_le_range_conj_map_congr θ (not_innerPlane_suzuki hv hp hp2 hE hc) fun φ hφ =>
      (h φ hφ).imp fun g hg => hg.symm
  have h := uniPlaneGen_suzukiGroup ha hK hp hp5 hne _ hc' hout'
  show Inputs2311c.UniPlaneGen (TauCeti.LieTypeIndex.suzuki m).characteristic E
  rw [TauCeti.LieTypeIndex.characteristic_suzuki]
  exact (Inputs2311c.uniPlaneGen_map_congr θ _ E).1 h

theorem input23_11TwoOn_suzuki :
    Input23_11TwoOn fun _ d => ∃ m, d = TauCeti.LieTypeIndex.suzuki m :=
  input23_11TwoOn_of_uniSeitzPlanes uniSeitzPlanes_suzuki fun _ _ _ hp5 hR _ _ _ _ => ⟨hR, hp5⟩

end SuzukiGen

@[expose] def Input23_11TwoRest : Prop :=
  Input23_11TwoOn fun p d => d.characteristic = 2 ∧
    ¬ (CFSG.LieType.SeitzGeneration.IsLinearIndex d ∧ CFSG.LieType.SeitzGeneration.CentralPrimeFree p d) ∧
    (∀ m, d ≠ TauCeti.LieTypeIndex.suzuki m) ∧ d ≠ TauCeti.LieTypeIndex.tits ∧
    ¬ (p = 5 ∧ d = TauCeti.LieTypeIndex.reeF4 2)

@[expose] def Uni23_11TwoCpfRest : Prop :=
  Inputs2311c.UniSeitzPlanes fun d p _ => d.1.characteristic = 2 ∧ 5 ≤ p ∧
    CFSG.LieType.SeitzGeneration.CentralPrimeFree p d.1 ∧ ¬ CFSG.LieType.SeitzGeneration.IsLinearIndex d.1 ∧
    (∀ m, d.1 ≠ TauCeti.LieTypeIndex.suzuki m) ∧ d.1 ≠ TauCeti.LieTypeIndex.tits ∧
    ¬ (p = 5 ∧ d.1 = TauCeti.LieTypeIndex.reeF4 2)

@[expose] def Input23_11TwoNonCpf : Prop :=
  Input23_11TwoOn fun p d => d.characteristic = 2 ∧ ¬ CFSG.LieType.SeitzGeneration.CentralPrimeFree p d

theorem input23_11TwoRest_of_uni (hU : Uni23_11TwoCpfRest) (hN : Input23_11TwoNonCpf) : Input23_11TwoRest := by
  have hU' : Input23_11TwoOn fun p d => d.characteristic = 2 ∧ CFSG.LieType.SeitzGeneration.CentralPrimeFree p d ∧
      ¬ CFSG.LieType.SeitzGeneration.IsLinearIndex d ∧ (∀ m, d ≠ TauCeti.LieTypeIndex.suzuki m) ∧
      d ≠ TauCeti.LieTypeIndex.tits ∧ ¬ (p = 5 ∧ d = TauCeti.LieTypeIndex.reeF4 2) :=
    input23_11TwoOn_of_uniSeitzPlanes hU fun _ _ _ hp5 hR _ _ _ _ =>
      ⟨hR.1, hp5, hR.2.1, hR.2.2.1, hR.2.2.2.1, hR.2.2.2.2.1, hR.2.2.2.2.2⟩
  refine Input23_11TwoOn.mono (fun p d hd => ?_) (input23_11TwoOn_or hU' hN)
  obtain ⟨hc, hl, hs, ht, he⟩ := hd
  by_cases hcpf : CFSG.LieType.SeitzGeneration.CentralPrimeFree p d
  · exact Or.inl ⟨hc, hcpf, fun h => hl ⟨h, hcpf⟩, hs, ht, he⟩
  · exact Or.inr ⟨hc, hcpf⟩

@[expose] def Input23_23NRest : Prop :=
  Input23_11TwoRest ∧ Input14_1BadRest

section Assembly2


theorem input23_11Two_of_rest (h : Input23_11TwoRest) : Inputs2323.Input23_11Two := by
  apply input23_11Two_of_on
  refine Input23_11TwoOn.mono (fun p d _ => ?_)
    (input23_11TwoOn_or (input23_11TwoOn_or input23_11TwoOn_linear input23_11TwoOn_suzuki)
      (input23_11TwoOn_or (input23_11TwoOn_or input23_11TwoOn_exc5 input23_11TwoOn_tits)
        (input23_11TwoOn_or input23_11TwoOn_char_ne_two h)))
  by_cases hc : d.characteristic = 2
  · by_cases hl : CFSG.LieType.SeitzGeneration.IsLinearIndex d ∧ CFSG.LieType.SeitzGeneration.CentralPrimeFree p d
    · exact Or.inl (Or.inl hl)
    · by_cases hs : ∃ m, d = TauCeti.LieTypeIndex.suzuki m
      · exact Or.inl (Or.inr hs)
      · have hs' : ∀ m, d ≠ TauCeti.LieTypeIndex.suzuki m := fun m hm => hs ⟨m, hm⟩
        by_cases ht : d = TauCeti.LieTypeIndex.tits
        · by_cases h5 : p = 5
          · exact Or.inr (Or.inl (Or.inl ⟨h5, Or.inr (Or.inr ht)⟩))
          · exact Or.inr (Or.inl (Or.inr ⟨ht, h5⟩))
        · by_cases he : p = 5 ∧ d = TauCeti.LieTypeIndex.reeF4 2
          · exact Or.inr (Or.inl (Or.inl ⟨he.1, Or.inr (Or.inl he.2)⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨hc, hl, hs', ht, he⟩))
  · exact Or.inr (Or.inr (Or.inl hc))

theorem input23_23N_of_rests (hI11 : Input23_11TwoRest) (h : Input14_1BadRest) :
    Claims1314c2.Input23_23N :=
  input23_23N_of_rest (input23_11Two_of_rest hI11) h

theorem input23_23N_of_rest2 (h : Input23_23NRest) : Claims1314c2.Input23_23N :=
  input23_23N_of_rests h.1 h.2

end Assembly2

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2323b

end
