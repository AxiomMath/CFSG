module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsL33
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympFieldExport
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympAut
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSp
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33c

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33 (isLpType_of_mulEquiv
  card_of_isLpType_three_three exists_card_eq_three_pow sl_l33 su_l33_false
  isComponentOf_map_congr isLpType_center_map congr_self_eq exists_card_eq_pow_ringChar)

section Central

theorem not_isLpType_of_surj {X H : Type*} [Group X] [Group H] (hX : commutator X = ⊤)
    (f : X →* H) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center X)
    (hno : ¬ IsLpType 3 3 (X ⧸ Subgroup.center X)) : ¬ IsLpType 3 3 (H ⧸ Subgroup.center H) := by
  intro hL
  obtain ⟨e⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
    hX f hf hk
  exact hno (isLpType_of_mulEquiv e hL)

theorem ker_mulEquiv_le_center {X H : Type*} [Group X] [Group H] (e : X ≃* H) :
    e.toMonoidHom.ker ≤ Subgroup.center X := by
  intro x hx
  have : x = 1 := e.injective (by rw [map_one]; exact hx)
  rw [this]
  exact one_mem _

theorem not_isLpType_of_equiv_sl_two {E : Type} [Field E] [Finite E] (hE : ringChar E = 3)
    {G : Type} [Group G] (e : Matrix.SpecialLinearGroup (Fin 2) E ≃* G) :
    ¬ IsLpType 3 3 (G ⧸ Subgroup.center G) := fun hL => by
  have := (sl_l33 hE le_rfl e.toMonoidHom e.surjective (ker_mulEquiv_le_center e) hL).1
  omega

end Central

section SpOrder

theorem sp_l33_false {K : Type} [Field K] [Finite K] (hK : ringChar K = 3) {s : ℕ} (hs : 2 ≤ s)
    {T : Type*} [Group T] (g : ↥(StatedSp s K) →* T) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center _) (hL : IsLpType 3 3 (T ⧸ Subgroup.center T)) : False := by
  obtain ⟨a, ha, hKa⟩ := exists_card_eq_three_pow hK
  have h3 : 3 ≤ Nat.card K := by
    rw [hKa]
    exact Nat.le_self_pow (by omega) 3
  have hqs : CFSG.IsQuasisimple (StatedSp s K) := by
    refine CFSG.LieType.Universal.Symplectic.isQuasisimple s K (by omega) ?_
    rcases Nat.lt_or_ge (Nat.card K) 4 with h4 | h4
    · exact Or.inr (Or.inl ⟨by omega, hs⟩)
    · exact Or.inl (Or.inr h4)
  obtain ⟨e⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
    hqs.1.commutator_eq_top g hg hker
  have hKZ := card_of_isLpType_three_three hL
  have hZ : Nat.card ↥(Subgroup.center (StatedSp s K)) = Nat.gcd 2 (Nat.card K - 1) := by
    rw [CFSG.LieType.Universal.Symplectic.center_eq]
    exact card_spScalars_eq_gcd K (by omega)
  have hcard : Nat.card (StatedSp s K) = 5616 * Nat.gcd 2 (Nat.card K - 1) := by
    rw [(Subgroup.center (StatedSp s K)).card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr e.toEquiv, hKZ, hZ]
  have hdvd : 3 ^ (a * s ^ 2) ∣ 5616 * Nat.gcd 2 (Nat.card K - 1) := by
    rw [← hcard, SymplecticFlag.card_statedSp, hKa, ← pow_mul]
    exact Dvd.intro _ rfl
  have hcop : Nat.Coprime (3 ^ (a * s ^ 2)) (Nat.gcd 2 (Nat.card K - 1)) :=
    Nat.Coprime.pow_left _ (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left _ _) (by norm_num))
  have h5616 : 3 ^ (a * s ^ 2) ∣ 5616 := hcop.dvd_of_dvd_mul_right hdvd
  have h4 : 4 ≤ a * s ^ 2 := by
    have : 4 ≤ s ^ 2 := by nlinarith
    nlinarith
  have h81 : 3 ^ 4 ∣ 5616 := (pow_dvd_pow 3 h4).trans h5616
  omega

end SpOrder

section Good

@[expose] def L33Good (H : Type) [Group H] : Prop :=
  (CFSG.IsQuasisimple ↥(commutator H) ∧
      ¬ IsLpType 3 3 (↥(commutator H) ⧸ Subgroup.center ↥(commutator H))) ∨ Group.IsSolvable H

theorem L33Good.of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H) (h : L33Good H) :
    L33Good G := by
  rcases h with ⟨hq, hno⟩ | hs
  · left
    have hmap : (commutator G).map e.toMonoidHom = commutator H := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
        ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 e.surjective]
    let e' : ↥(commutator G) ≃* ↥(commutator H) :=
      ((commutator G).equivMapOfInjective e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hmap)
    refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e'.symm hq, fun hL => hno ?_⟩
    exact isLpType_of_mulEquiv (QuotientGroup.congr _ _ e' (Subgroup.map_center_eq e')).symm hL
  · right
    haveI := hs
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem l33Good_of_commutator_eq {H : Type} [Group H] (N : Subgroup H) (hN : commutator H = N)
    (hq : CFSG.IsQuasisimple ↥N) (hno : ¬ IsLpType 3 3 (↥N ⧸ Subgroup.center ↥N)) :
    L33Good H := by
  subst hN
  exact Or.inl ⟨hq, hno⟩

theorem l33Good_of_isQuasisimple {H : Type} [Group H] (hq : CFSG.IsQuasisimple H)
    (hno : ¬ IsLpType 3 3 (H ⧸ Subgroup.center H)) : L33Good H := by
  have hcomm : commutator H = ⊤ := Group.isPerfect_def.mp hq.1
  let e : ↥(⊤ : Subgroup H) ≃* H := Subgroup.topEquiv
  refine l33Good_of_commutator_eq _ hcomm
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq) fun hL => hno ?_
  exact isLpType_of_mulEquiv (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).symm hL

theorem commutator_eq_ker_of_perfect {G A : Type*} [Group G] [CommGroup A] (D : G →* A)
    (hperf : Group.IsPerfect ↥D.ker) : commutator G = D.ker := by
  have hle : commutator G ≤ D.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  have hge : D.ker ≤ commutator G := by
    have h1 := Subgroup.isPerfect_iff.mp hperf
    calc D.ker = ⁅D.ker, D.ker⁆ := h1.symm
      _ ≤ ⁅(⊤ : Subgroup G), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator G := (_root_.commutator_def G).symm
  exact le_antisymm hle hge

theorem dich_of_l33Good {X : Type} [Group X] (A : Subgroup X) (h : L33Good ↥A) :
    (CFSG.IsQuasisimple ↥⁅A, A⁆ ∧ ¬ IsLpType 3 3 (↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆)) ∨
      Group.IsSolvable ↥A := by
  rcases h with ⟨hq, hno⟩ | hs
  · left
    let e : ↥(commutator ↥A) ≃* ↥⁅A, A⁆ :=
      ((commutator ↥A).equivMapOfInjective A.subtype A.subtype_injective).trans
        (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator A))
    refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, fun hL => hno ?_⟩
    exact isLpType_of_mulEquiv (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)) hL
  · right
    exact hs

theorem tame_of_l33Good {X : Type} [Group X] (A : Subgroup X) (h : L33Good ↥A) :
    CFSG.IsQuasisimple ↥⁅A, A⁆ ∨ Group.IsSolvable ↥A :=
  (dich_of_l33Good A h).imp And.left id

theorem not_isLpType_of_l33Good {X : Type} [Group X] (A : Subgroup X) (h : L33Good ↥A)
    (hq : CFSG.IsQuasisimple ↥⁅A, A⁆) :
    ¬ IsLpType 3 3 (↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆) := by
  rcases dich_of_l33Good A h with ⟨-, hno⟩ | hs
  · exact hno
  · exfalso
    have hle : ⁅A, A⁆ ≤ A := by
      refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
      rw [commutatorElement_def]
      exact A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb)
    haveI : Group.IsSolvable ↥⁅A, A⁆ := Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hle) (Subgroup.inclusion_injective _)
    haveI : Group.IsPerfect ↥⁅A, A⁆ := hq.1
    haveI : Nontrivial ↥⁅A, A⁆ := CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact Group.IsPerfect.not_isSolvable _ ‹_›

end Good

section Factors

theorem l33Good_statedSp {K : Type} [Field K] [Finite K] (hK : ringChar K = 3)
    (hK4 : 4 ≤ Nat.card K) {s : ℕ} (hs : 1 ≤ s) : L33Good (StatedSp s K) := by
  refine l33Good_of_isQuasisimple
    (CFSG.LieType.Universal.Symplectic.isQuasisimple s K hs (Or.inl (Or.inr hK4))) ?_
  rcases Nat.lt_or_ge s 2 with hs1 | hs2
  · obtain rfl : s = 1 := by omega
    exact not_isLpType_of_equiv_sl_two hK
      (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K)
  · intro hL
    exact sp_l33_false hK hs2 (MulEquiv.refl _).toMonoidHom (MulEquiv.refl _).surjective
      (ker_mulEquiv_le_center _) hL

theorem l33Good_matrixGL {E : Type} [Field E] [Finite E] (hE : ringChar E = 3)
    (h4 : 4 ≤ Nat.card E) (m : ℕ) : L33Good (Matrix.GeneralLinearGroup (Fin m) E) := by
  by_cases hm : 2 ≤ m
  · have h4' : ∃ s : Finset E, s.card = 4 :=
      CFSG.RankThree.PartOne.KCSpIsotypic.exists_finset_card_four_of_card h4
    have hSL : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin m) E) :=
      CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_SL hm (Or.inr h4')
    let eK : Matrix.SpecialLinearGroup (Fin m) E ≃* ↥(Matrix.GeneralLinearGroup.det :
        Matrix.GeneralLinearGroup (Fin m) E →* Eˣ).ker := Matrix.SpecialLinearGroup.toGLKerEquiv
    have hkq : CFSG.IsQuasisimple ↥(Matrix.GeneralLinearGroup.det :
        Matrix.GeneralLinearGroup (Fin m) E →* Eˣ).ker :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hSL
    refine l33Good_of_commutator_eq _ (commutator_eq_ker_of_perfect _ hkq.1) hkq fun hL => ?_
    have := (sl_l33 hE hm eK.toMonoidHom eK.surjective (ker_mulEquiv_le_center eK) hL).2
    omega
  · right
    have hsub : Subsingleton (Fin m) := by
      have : m ≤ 1 := by omega
      interval_cases m <;> infer_instance
    refine Group.isSolvable_of_comm fun a b => Units.ext (Matrix.ext fun i j => ?_)
    have hj : j = i := Subsingleton.elim _ _
    subst hj
    simp only [Units.val_mul, Matrix.mul_apply]
    rw [Fintype.sum_subsingleton _ j, Fintype.sum_subsingleton _ j, mul_comm]

theorem l33Good_sesqUnitaryGroup {ℓ g : ℕ} (hℓ3 : ℓ = 3) {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ g E) (hq : 4 ≤ ℓ ^ g) {W : Type} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft) : L33Good ↥(sesqUnitaryGroup Hf) := by
  haveI := hE.finite
  by_cases hm : 2 ≤ Module.finrank E W
  · obtain ⟨-, -, -, -, hker, -⟩ :=
      CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl rfl (by omega)
    let eN : ↥((sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf)) ≃*
        ↥(sesqSpecialUnitaryGroup Hf) :=
      Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)
    have hQ : CFSG.IsQuasisimple ↥(sesqSpecialUnitaryGroup Hf) :=
      CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hE hHf hHfl
        hm ⟨fun _ => hq, fun _ => by omega⟩
    have hNq : CFSG.IsQuasisimple
        ↥((sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv eN.symm hQ
    have hcomm : commutator ↥(sesqUnitaryGroup Hf) =
        (sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf) := by
      rw [← hker]
      exact commutator_eq_ker_of_perfect (CFSG.LinearGroups.unitaryDet Hf)
        (by rw [hker]; exact hNq.1)
    refine l33Good_of_commutator_eq _ hcomm hNq fun hL => ?_
    haveI : Fact ℓ.Prime := ⟨hE.prime⟩
    rcases Nat.lt_or_ge (Module.finrank E W) 3 with h2 | h3
    · have hV : Module.finrank E W = 2 := by omega
      obtain ⟨φ⟩ :=
        CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf hHfl hV
      haveI : Finite ↥hE.fixedField := inferInstance
      letI : Fintype ↥hE.fixedField := Fintype.ofFinite _
      have hcardF : Fintype.card ↥hE.fixedField = ℓ ^ g := by
        rw [← Nat.card_eq_fintype_card]
        exact hE.card_fixedField
      haveI : CharP ↥hE.fixedField ℓ := charP_of_card_eq_prime_pow hcardF
      have hcharF : ringChar ↥hE.fixedField = 3 := by rw [ringChar.eq _ ℓ, hℓ3]
      exact not_isLpType_of_equiv_sl_two hcharF (eN.trans φ).symm hL
    · obtain ⟨b, hb⟩ := hE.exists_orthonormal_basis hHf hHfl
      obtain ⟨φ⟩ := CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE b
        (G := (1 : Matrix (Fin (Module.finrank E W)) (Fin (Module.finrank E W)) E))
        (fun i j => by rw [hb i j, Matrix.one_apply])
      let e3 : ↥((sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf)) ≃*
          ↥(StatedSU (Module.finrank E W) (ℓ ^ g) E) :=
        (eN.trans φ).trans (MulEquiv.subgroupCongr
          (CFSG.ClassicalGroups.UnitaryFlag.unitarySU_eq_gramSU hE _).symm)
      exact su_l33_false hE hℓ3 h3 e3.symm.toMonoidHom e3.symm.surjective
        (ker_mulEquiv_le_center e3.symm) hL
  · right
    refine Group.isSolvable_of_comm fun a b => Subtype.ext (Units.ext ?_)
    have := (CFSG.RankThree.PartOne.KCUnitary.End_commute_of_finrank_le_one (E := E) (W := W)
      (by omega) ((a : LinearMap.GeneralLinearGroup E W) : Module.End E W)
      ((b : LinearMap.GeneralLinearGroup E W) : Module.End E W)).eq
    simpa [Subgroup.coe_mul, Units.val_mul] using this

end Factors

section SpInner

open Polynomial CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

variable {r : ℕ} {K : Type} [Field K]

theorem l33Good_spSupported_of_factor [Finite K] {ℓ f p : ℕ} (hℓ3 : ℓ = 3) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hK4 : 4 ≤ Nat.card K) {x : StatedSp r K}
    {a : StatedProj (StatedSp r K)} (hsq : Squarefree (minpoly K (spEnd x)))
    (blocks : SpPrimaryBlocks ℓ f p x a) (h : primaryFactors (spEnd x)) :
    L33Good ↥(spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}) := by
  haveI := Fintype.ofFinite K
  have hcardK : Fintype.card K = ℓ ^ f := by rw [Fintype.card_eq_nat_card, hK]
  haveI : Fact ℓ.Prime := ⟨hℓ3 ▸ Nat.prime_three⟩
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (f := f) hcardK
  have hKℓ : ringChar K = 3 := by rw [ringChar.eq K ℓ, hℓ3]
  have hdeg : 1 ≤ (h : K[X]).natDegree :=
    Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors h.2)
  by_cases hself : reciprocalPolynomial (h : K[X]) = h
  · have hO' : ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]) = {(h : K[X])} := by
      rw [hself, Set.pair_eq_singleton]
    rw [hO']
    by_cases h1 : (h : K[X]) = X - 1
    · obtain ⟨h0, hm⟩ := h
      change h0 = X - 1 at h1
      subst h1
      obtain ⟨φ, -⟩ := blocks.fixedFactor hm
      have : Nontrivial (primaryComponent (spEnd x) (X - 1)) :=
        Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq hm)
      obtain ⟨s, hs, ⟨e⟩⟩ := exists_mulEquiv_sesqUnitaryGroup_statedSp
        (B := (spForm r K).restrict (primaryComponent (spEnd x) (X - 1)))
        (fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)) blocks.fixed_nondegenerate
      have hs1 : 1 ≤ s := by
        have := Module.finrank_pos (R := K) (M := primaryComponent (spEnd x) (X - 1))
        omega
      exact L33Good.of_mulEquiv (φ.trans e) (l33Good_statedSp hKℓ hK4 hs1)
    · obtain ⟨d, hd, -, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, -⟩ :=
        (blocks.selfDual h h1 hself).exists_half
      have hd1 : 1 ≤ d := by omega
      have hq : 4 ≤ ℓ ^ (f * d) := by
        calc 4 ≤ ℓ ^ f := by rw [← hK]; exact hK4
          _ ≤ ℓ ^ (f * d) := Nat.pow_le_pow_right (by rw [hℓ3]; norm_num)
            (Nat.le_mul_of_pos_right f hd1)
      exact L33Good.of_mulEquiv φ (l33Good_sesqUnitaryGroup hℓ3 hE hq hHf hHfl)
  · have hP := blocks.paired h (fun e => hself e.symm)
    obtain ⟨φ⟩ := hP.matrixFactor
    haveI : Finite (AdjoinRoot (h : K[X])) := Module.finite_of_finite K
    have hEℓ : ringChar (AdjoinRoot (h : K[X])) = 3 :=
      (Algebra.ringChar_eq K (AdjoinRoot (h : K[X]))).symm.trans hKℓ
    have h4 : 4 ≤ Nat.card (AdjoinRoot (h : K[X])) := by
      rw [hP.card_field, ← hK]
      exact hK4.trans (Nat.le_self_pow (by omega) _)
    exact L33Good.of_mulEquiv φ (l33Good_matrixGL hEℓ h4 _)

theorem noL33_conj_sp [Finite K] {ℓ f p : ℕ} (hℓ3 : ℓ = 3) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hK4 : 4 ≤ Nat.card K) (hr : 1 ≤ r) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpℓ : p ≠ ℓ) (x : StatedSp r K) (hx : x ^ p = 1) (K' : Subgroup (StatedProj (StatedSp r K)))
    (hK' : IsComponentOf K' (fixSubgroup (MulAut.conj (SymplecticFlag.proj r K x)))) :
    ¬ IsLpType 3 3 (↥K' ⧸ Subgroup.center ↥K') := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hℓ : ℓ.Prime := hℓ3 ▸ Nat.prime_three
  haveI := Fintype.ofFinite K
  have hcardK : Fintype.card K = ℓ ^ f := by rw [Fintype.card_eq_nat_card, hK]
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (f := f) hcardK
  have hKℓ : ringChar K = 3 := by rw [ringChar.eq K ℓ, hℓ3]
  have hZc : (SymplecticFlag.proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [SymplecticHigher.ker_proj]
    exact SymplecticHigher.spScalars_le_center
  obtain ⟨ι, hι, A, hc, hjoin, hgood⟩ : ∃ (ι : Type) (_ : Finite ι)
      (A : ι → Subgroup (StatedSp r K)),
      (∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b) ∧
      ⨆ i, A i = Subgroup.centralizer ({x} : Set (StatedSp r K)) ∧ ∀ i, L33Good ↥(A i) := by
    by_cases hx1 : x = 1
    · subst hx1
      refine ⟨Unit, inferInstance, fun _ => ⊤, fun i j hij => absurd (Subsingleton.elim i j) hij,
        ?_, fun _ => L33Good.of_mulEquiv Subgroup.topEquiv (l33Good_statedSp hKℓ hK4 hr)⟩
      ext g
      simp [Subgroup.mem_centralizer_iff]
    · have hZp : Nat.Coprime (Nat.card (SymplecticFlag.proj r K).ker) p := by
        rw [SymplecticHigher.ker_proj, card_spScalars_eq_gcd K hr]
        exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left 2 _)
          ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
      have ha1 : SymplecticFlag.proj r K x ≠ 1 := fun h =>
        hx1 (CFSG.RankThree.Classical.eq_of_map_eq_of_pow_eq_one_of_coprime (a := 1) (b := 0)
          (SymplecticFlag.proj r K) hZc hZp (by rwa [pow_one]) (by simp)
          (by rw [h, map_one]))
      have ha : orderOf (SymplecticFlag.proj r K x) = p :=
        orderOf_eq_prime (by rw [← map_pow, hx, map_one]) ha1
      have hxp : orderOf x = p := orderOf_eq_prime hx hx1
      have blocks := (symplectic_cross_prime_primary_centralizer_blocks hℓ hf hK hp hp2 hpℓ hr _
        ha).2 x rfl hxp
      have hpK : (p : K) ≠ 0 := by
        intro h
        rw [CharP.cast_eq_zero_iff K ℓ] at h
        exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h).symm
      have hsq := (altPrimaryData_spLin hpK hx).squarefree
      haveI : Finite (reciprocalOrbits (spEnd x)) :=
        (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
      obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
      refine ⟨reciprocalOrbits (spEnd x), inferInstance,
        fun O => spSupported x (O : Set K[X]),
        fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb,
        hjoin, ?_⟩
      rintro ⟨O, h, hh, rfl⟩
      exact l33Good_spSupported_of_factor hℓ3 hf hK hK4 hsq blocks ⟨h, hh⟩
  haveI := hι
  obtain ⟨i, hq, rfl⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_conj_of_orbit_family
      (SymplecticFlag.proj r K) SymplecticHigher.proj_surjective hZc x A hc hjoin
      (fun i => tame_of_l33Good _ (hgood i)) K' hK'
  refine not_isLpType_of_surj hq.1.commutator_eq_top
    ((SymplecticFlag.proj r K).subgroupMap ⁅A i, A i⁆)
    (MonoidHom.subgroupMap_surjective _ _) (fun d hd => ?_)
    (not_isLpType_of_l33Good _ (hgood i) hq)
  have h1 : SymplecticFlag.proj r K (d : StatedSp r K) = 1 := congrArg Subtype.val hd
  have h2 : (d : StatedSp r K) ∈ Subgroup.center (StatedSp r K) := hZc h1
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (Subgroup.mem_center_iff.1 h2 y)

end SpInner

section SpField

open CFSG.ComponentClassification.UnbalancedCatalog (descentField)

theorem noL33_fieldAut_sp {r : ℕ} (hr : 2 ≤ r) {K : Type} [Field K] [Finite K]
    (hK3 : ringChar K = 3) (σ : K ≃+* K) {p : ℕ} (hp : Odd p) (hσ : σ ^ p = 1)
    (K' : Subgroup (StatedProj (StatedSp r K)))
    (hK' : IsComponentOf K' (fixSubgroup (SymplecticHigher.fieldAut r K σ))) :
    ¬ IsLpType 3 3 (↥K' ⧸ Subgroup.center ↥K') := by
  have hchar : ringChar ↥(descentField σ) = 3 := by
    rw [Algebra.ringChar_eq (descentField σ) K, hK3]
  have hex : ¬(r = 2 ∧ Nat.card ↥(descentField σ) = 2) := by
    rintro ⟨-, h2⟩
    obtain ⟨a, ha, hcard⟩ := exists_card_eq_three_pow hchar
    have : 3 ≤ 3 ^ a := Nat.le_self_pow (by omega) 3
    omega
  obtain ⟨-, hcover⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.sp_fieldAut_comp_generic
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFactorFacts_holds hp hr σ hσ hex
  obtain ⟨g, hg, hgk⟩ := hcover K' hK'
  exact fun hL => sp_l33_false hchar hr g hg hgk hL

end SpField

section SpCatalogue

open SymplecticHigher

theorem center_eq_bot_of_simple {S : Type} [Group S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ Subgroup.center S := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 ha b).symm

theorem pow_eq_one_of_conj_pow {S : Type} [Group S] (hZ : Subgroup.center S = ⊥) {p : ℕ}
    {a : S} (h : MulAut.conj a ^ p = 1) : a ^ p = 1 := by
  have hc : a ^ p ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut S => φ g)
      (show MulAut.conj (a ^ p) = 1 by rw [map_pow]; exact h)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * a ^ p = a ^ p * g * (a ^ p)⁻¹ * a ^ p := by rw [h1]
      _ = a ^ p * g := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc

theorem congr_conj_apply {S G : Type} [Group S] [Group G] (e : S ≃* G) (s : S) :
    MulAut.congr e (MulAut.conj s) = MulAut.conj (e s) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem exists_model_psp {S : Type} [Group S] (idx : TauCeti.ValidLieTypeIndex)
    (hsp : (∃ q, idx.1 = .B 2 q) ∨ ∃ r q, idx.1 = .C r q) (hc3 : idx.1.characteristic = 3)
    (hfo : idx.1.fieldOrder ≠ 3) (e : S ≃* (TauCeti.CFSGIndex.lie idx).Group) :
    ∃ (r f : ℕ) (k : Type) (_ : Field k) (_ : Finite k), 2 ≤ r ∧ 1 ≤ f ∧
      Nat.card k = 3 ^ f ∧ 4 ≤ Nat.card k ∧ Nonempty (S ≃* StatedProj (StatedSp r k)) := by
  obtain ⟨d, hv⟩ := idx
  have key : ∀ (r : ℕ) (q : TauCeti.PrimePower), q.p = 3 → q.card ≠ 3 →
      StatedClassicalModel S .PSp r q.p q.exponent →
      ∃ (r f : ℕ) (k : Type) (_ : Field k) (_ : Finite k), 2 ≤ r ∧ 1 ≤ f ∧
        Nat.card k = 3 ^ f ∧ 4 ≤ Nat.card k ∧ Nonempty (S ≃* StatedProj (StatedSp r k)) := by
    intro r q hq3 hq hmod
    obtain ⟨⟨-, hf, hr, -⟩, k, _, _, hk, ⟨e'⟩⟩ := hmod
    rw [hq3] at hk
    refine ⟨r, q.exponent, k, inferInstance, inferInstance, hr, hf, hk, ?_, ⟨e'⟩⟩
    have hf1 : q.exponent ≠ 1 := by
      intro h1
      apply hq
      rw [TauCeti.PrimePower.card_def, hq3, h1, pow_one]
    have hf2 : 2 ≤ q.exponent := by omega
    rw [hk]
    calc 4 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hf2
  rcases hsp with ⟨q, hd⟩ | ⟨r, q, hd⟩
  · dsimp only at hd
    subst hd
    exact key 2 q (by simpa using hc3) (by simpa using hfo)
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e)
  · dsimp only at hd
    subst hd
    exact key r q (by simpa using hc3) (by simpa using hfo)
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e)

theorem noL33_symplectic {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (idx : TauCeti.ValidLieTypeIndex)
    (hsp : (∃ q, idx.1 = .B 2 q) ∨ ∃ r q, idx.1 = .C r q) (hc3 : idx.1.characteristic = 3)
    (hfo : idx.1.fieldOrder ≠ 3) (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group))
    {α : MulAut S} (hα : α ^ 13 = 1) {K : Subgroup S} (hK : IsComponentOf K (fixSubgroup α)) :
    ¬ IsLpType 3 3 (↥K ⧸ Subgroup.center ↥K) := by
  haveI := hs
  obtain ⟨e⟩ := he
  obtain ⟨r, f, k, _, _, hr, hf, hk, hk4, ⟨e'⟩⟩ := exists_model_psp idx hsp hc3 hfo e
  have hp13 : (13 : ℕ).Prime := by norm_num
  haveI : Fact (13 : ℕ).Prime := ⟨hp13⟩
  haveI : Finite (StatedProj (StatedSp r k)) := Finite.of_equiv S e'.toEquiv
  have hchar : ringChar k = 3 := by
    obtain ⟨a, ha, hpa, hka⟩ := exists_card_eq_pow_ringChar (K := k)
    have h1 : ringChar k ∣ 3 ^ f := by
      rw [← hk, hka]
      exact dvd_pow_self _ (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hpa Nat.prime_three).1 (hpa.dvd_of_dvd_pow h1)
  have hβ' : MulAut.congr e' α ^ 13 = 1 := by rw [← map_pow, hα, map_one]
  have hO := CFSG.RankThree.PartOne.KCSpComm.spOuter (K := k) Nat.prime_three hf hr hk
  have hodd : Odd (orderOf (MulAut.congr e' α)) :=
    (by decide : Odd 13).of_dvd_nat (orderOf_dvd_of_pow_eq_one hβ')
  have hE : MulAut.congr e' α ∈ spSemilinearAutGroup r k :=
    CFSG.RankThree.PartOne.KCSpComm.mem_of_odd_orderOf_of_index_dvd_two _ hO.index_dvd hodd
  have hK1 := isComponentOf_map_congr e' hK
  intro hL
  have hL1 := isLpType_center_map e' hL
  by_cases hD : MulAut.congr e' α ∈ spLinearAutGroup r k
  ·
    have : (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (StatedProj (StatedSp r k))).Normal :=
      CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
    have hrel : (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (StatedProj (StatedSp r k))).relIndex (spLinearAutGroup r k) ∣ 2 :=
      hO.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)
    obtain ⟨t, ht⟩ := CFSG.RankThree.PartOne.KCSpComm.mem_of_pow_eq_one_of_relIndex_dvd_two hrel
      hp13 (by norm_num) hD hβ'
    have hαs : α = MulAut.conj (e'.symm t) := by
      apply (MulAut.congr e').injective
      rw [← ht, congr_conj_apply, MulEquiv.apply_symm_apply]
    have hs13 : (e'.symm t) ^ 13 = 1 :=
      pow_eq_one_of_conj_pow (center_eq_bot_of_simple hna) (by rw [← hαs]; exact hα)
    have ht13 : t ^ 13 = 1 := by
      have := congrArg e' hs13
      rwa [map_pow, MulEquiv.apply_symm_apply, map_one] at this
    obtain ⟨x, hx, hxp⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_proj_eq_pow_eq_one_sp
        (by omega) hp13 (by norm_num) ht13
    rw [← ht, ← hx] at hK1
    exact noL33_conj_sp rfl hf hk hk4 (by omega) hp13 (by norm_num) (by norm_num) x hxp _ hK1 hL1
  ·
    have hne1 : MulAut.congr e' α ≠ 1 := fun h1 => hD (h1 ▸ one_mem _)
    have hord : orderOf (MulAut.congr e' α) = 13 := orderOf_eq_prime hβ' hne1
    obtain ⟨-, σ, hσ, h, -, hβeq⟩ := hO.descent 13 hp13 _ hE hD hord
    have hβφ : MulAut.congr (h⁻¹ : MulAut _) (MulAut.congr e' α) = fieldAut r k σ := by
      rw [congr_self_eq, hβeq]
      group
    have hK2 := isComponentOf_map_congr (h⁻¹ : MulAut _) hK1
    rw [hβφ] at hK2
    have hL2 := isLpType_center_map (h⁻¹ : MulAut _) hL1
    have hσ13 : σ ^ 13 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
    exact noL33_fieldAut_sp hr hchar σ (by decide) hσ13 _ hK2 hL2

end SpCatalogue

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33c
