module

public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalOrthTwoBasic
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalOrthTwoPlane
public import CFSG.HardMathSupport.Dickson.Bal207.CoreFreeInner
public import CFSG.HardMathSupport.Dickson.Bal207.OrthEightFixed
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwoAux.Unitary

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two

open Polynomial Module QuadraticMap CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.GroupTheory.WeirSylow CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.OrthogonalInvolutions
  CFSG.RankThree.Classical2 CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
  CFSG.LocalAnalysis.ComponentInitial

section Special

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem noNormalPPrime_specialBlock_cyc3 (hK : Nat.card K = 2) (hx : OddOrderIsometry Q 3 x)
    (hh : cyc3 K ∈ primaryFactors x.toLinearMap) :
    NoNormalPPrime 3 (specialBlock Q x (cyc3 K)) := by
  classical
  have := charP_two hK
  have hirr := irreducible_cyc3 hK
  haveI : Fact (Irreducible (cyc3 K)) := ⟨hirr⟩
  obtain ⟨d, ℓ, f, hU, B, -, hq, hBsymm, hBl, hrange⟩ :=
    orth2_exists_unitary_model hx (Nat.odd_iff.2 rfl) hh (cyc3_ne_X_sub_one K)
      (reciprocal_cyc3 K).symm
  have e₁ : ↥(specialBlock Q x (cyc3 K)) ≃* ↥(sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
      (MulEquiv.subgroupCongr hrange)
  have hℓ : ℓ = 2 := ((Nat.Prime.pow_eq_iff Nat.prime_two).1 (hq.symm.trans hK)).1
  subst hℓ
  have : Module.Finite K (AdjoinRoot (cyc3 K)) := (AdjoinRoot.powerBasis hirr.ne_zero).finite
  have hcardE : Nat.card (AdjoinRoot (cyc3 K)) = Nat.card K ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := K), (AdjoinRoot.powerBasis hirr.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, natDegree_cyc3]
  have hg : 2 ^ (f * d) = 2 := by
    have h1 := hU.card
    rw [hcardE, hK, show (2 : ℕ) ^ 2 = 2 ^ 2 from rfl] at h1
    have h2 := Nat.pow_right_injective le_rfl h1
    have h3 : f * d = 1 := by omega
    rw [h3, pow_one]
  have hN : NoNormalPPrime 3 (sesqSpecialUnitaryGroup B) :=
    W2.noNormalPPrime_three_sesqSpecialUnitaryGroup hU hg hBsymm hBl
  rw [← W2.noNormalPPrime_top_iff] at hN ⊢
  exact W2.noNormalPPrime_top_of_mulEquiv e₁ hN

end Special

section Orders

variable {K : Type} [Field K] [Finite K] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {R : QuadraticForm K W}

theorem three_dvd_natCard_orthogonalGroup_two (hK : Nat.card K = 2)
    (hR : (polarBilin R).Nondegenerate) {m : ℕ} (hdim : finrank K W = 2 * (m + 1)) (hm : 1 ≤ m) :
    3 ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup R) := by
  have hq : ((Nat.card K : ℕ) : ℤ) = 2 := by exact_mod_cast hK
  have hO : ∀ ε : ℤ, ((ε = 1 ∧ IsPlusType R) ∨ (ε = -1 ∧ ¬ IsPlusType R)) →
      (3 : ℤ) ∣ (Nat.card (TauCeti.QuadraticMap.orthogonalGroup R) : ℤ) := by
    intro ε hε
    rw [natCard_orthogonalGroup_of_type hR hdim hε, hq]
    have h1 : (1 : ℕ) ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr ⟨le_rfl, hm⟩
    exact Dvd.dvd.mul_left ((by norm_num : (3 : ℤ) ∣ ((2 : ℤ) ^ 2) ^ 1 - 1).trans
      (Finset.dvd_prod_of_mem (fun i : ℕ => ((2 : ℤ) ^ 2) ^ i - 1) h1)) _
  have hZ : (3 : ℤ) ∣ (Nat.card (TauCeti.QuadraticMap.orthogonalGroup R) : ℤ) := by
    by_cases hp : IsPlusType R
    · exact hO 1 (Or.inl ⟨rfl, hp⟩)
    · exact hO (-1) (Or.inr ⟨rfl, hp⟩)
  exact_mod_cast hZ

end Orders

section Layer

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem noNormalPPrime_supportedFixedDerived (hK : Nat.card K = 2)
    (hx : OddOrderIsometry Q 3 x) (hQ : (polarBilin Q).Nondegenerate)
    (h6 : 6 ≤ finrank K (fixedSpace x)) : NoNormalPPrime 3 (supportedFixedDerived Q x) := by
  classical
  have := charP_two hK
  have h3 : 3 ≤ finrank K (fixedSpace x) := by omega
  have hnexc : ¬ SmallFixedException (Q.comp (fixedSpace x).subtype) := by
    rintro (⟨h, -⟩ | ⟨⟨h, -⟩, -⟩) <;> omega
  have hns : ¬ (finrank K (fixedSpace x) = 4 ∧ ∃ S : Submodule K (fixedSpace x),
      finrank K S = 2 ∧ ∀ u ∈ S, (Q.comp (fixedSpace x).subtype) u = 0) := by
    rintro ⟨h, -⟩
    omega
  have hqO := orthogonal_regular_space_derived_quasisimple (Q.comp (fixedSpace x).subtype)
    hx.polarBilin_fixed_nondegenerate h3 hnexc hns
  have e1 : ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (fixedSpace x).subtype))) ≃* ↥(orthDerived (Q.comp (fixedSpace x).subtype)) :=
    (Subgroup.equivMapOfInjective _
      (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)).subtype
      (TauCeti.QuadraticMap.orthogonalGroup _).subtype_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator _))
  have hq : CFSG.IsQuasisimple ↥(supportedFixedDerived Q x) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (e1.trans (supportedFixedDerivedEquiv hx).symm) hqO
  obtain ⟨a, ha⟩ := hx.even_finrank_fixed
  have hdim : finrank K (fixedSpace x) = 2 * ((a - 1) + 1) := by omega
  have h3O : 3 ∣ Nat.card
      (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) :=
    three_dvd_natCard_orthogonalGroup_two hK hx.polarBilin_fixed_nondegenerate hdim (by omega)
  obtain ⟨U, hU3, hU1, -⟩ := OrthEight.exists_supportedBlock_pow_three hx h3O
  have hUs : (U : V ≃ₗ[K] V) ∈ supportedFixedDerived Q x :=
    orth2_mem_supportedFixedDerived hK hx Nat.prime_three (by norm_num) h6 U.2
      (congrArg Subtype.val hU3)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hUo : orderOf (U : V ≃ₗ[K] V) = 3 :=
    orderOf_eq_prime (congrArg Subtype.val hU3) fun h => hU1 (Subtype.ext h)
  have h3S : 3 ∣ Nat.card ↥(supportedFixedDerived Q x) := by
    rw [← hUo]
    exact Subgroup.orderOf_dvd_natCard _ hUs
  have hZ : ∀ z ∈ supportedFixedDerived Q x,
      (∀ t ∈ supportedFixedDerived Q x, z * t = t * z) → z = 1 := by
    intro z hz hzc
    obtain ⟨hzO, hzx⟩ := Subgroup.mem_inf.mp (supportedFixedDerived_le_isometryCentralizer hz)
    exact eq_one_of_fixes hK hx
      (orth2_fixes_fixedSpace hK hQ hx h6 hzO (Subgroup.mem_centralizer_singleton_iff.mp hzx)
        fun f hf => hzc f hf)
      (fixes_cyc3_of_mem_supportedBlock_fixed hK (supportedFixedDerived_le_supportedBlock hz))
  exact noNormalPPrime_of_isQuasisimple Nat.prime_three hq h3S fun z hz hzc _ => hZ z hz hzc

end Layer

section Braid3

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem noNormalPPrime_closure_braidSet {W : Submodule K V} (hs : IsSmall (Q.comp W.subtype)) :
    NoNormalPPrime 3 (Subgroup.closure (braidSet Q W)) := by
  have hcomm : (braidSet Q W).Pairwise Commute :=
    fun a ha b hb _ => braidSet_comm hs ha hb
  letI : CommGroup ↥(Subgroup.closure (braidSet Q W)) := Subgroup.closureCommGroupOfComm hcomm
  have hJ3 : ∀ g ∈ Subgroup.closure (braidSet Q W), g ^ 3 = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem s hs' => exact braidSet_pow_three hs'
    | one => exact one_pow 3
    | mul a b ha hb iha ihb =>
      have hab : Commute a b := by
        have := mul_comm (⟨a, ha⟩ : ↥(Subgroup.closure (braidSet Q W))) ⟨b, hb⟩
        exact congrArg Subtype.val this
      rw [hab.mul_pow, iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  intro N hNJ _ hNc
  refine (Subgroup.eq_bot_iff_forall N).2 fun n hn => ?_
  have hdvd3 : orderOf n ∣ 3 := orderOf_dvd_of_pow_eq_one (hJ3 n (hNJ hn))
  have hdvdN : orderOf n ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hn
  exact orderOf_eq_one_iff.1
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvdN hNc.symm) hdvd3)

end Braid3

section Factors

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem exists_hFactor (hK : Nat.card K = 2) (hx : OddOrderIsometry Q 3 x)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    ∃ J : Subgroup (V ≃ₗ[K] V), J ≤ isometryCentralizer Q x ⊓ orthDerived Q ∧
      (∀ f ∈ isometryCentralizer Q x ⊓ orthDerived Q, ∀ n ∈ J, f * n * f⁻¹ ∈ J) ∧
      NoNormalPPrime 3 J ∧
      ∀ {G : V ≃ₗ[K] V}, G * x = x * G → ∀ {k : ℕ}, Nat.Coprime 3 k → G ^ k = 1 →
        (∀ f ∈ J, G * f = f * G) →
          ∀ v ∈ primaryComponent x.toLinearMap (cyc3 K), G v = v := by
  classical
  by_cases hm : 2 ≤ primaryMultiplicity x.toLinearMap (cyc3 K)
  · have hh : cyc3 K ∈ primaryFactors x.toLinearMap := cyc3_mem_primaryFactors hK (by omega)
    refine ⟨specialBlock Q x (cyc3 K),
      le_inf (specialBlock_le_isometryCentralizer _) (specialBlock_le_orthDerived hK hx hQ hT hh),
      fun f hf n hn => conj_mem_specialBlock (Subgroup.mem_inf.mp hf).1 hn,
      noNormalPPrime_specialBlock_cyc3 hK hx hh, ?_⟩
    intro G hGx k hk hGk hcomm
    exact fixes_cyc3 hK hx hGx hk hGk fun _ f hf => hcomm f hf
  · refine ⟨⊥, bot_le, ?_, fun N hN _ _ => le_bot_iff.mp hN, ?_⟩
    · intro f _ n hn
      rw [Subgroup.mem_bot] at hn ⊢
      rw [hn, mul_one, mul_inv_cancel]
    · intro G hGx k hk hGk _
      exact fixes_cyc3 hK hx hGx hk hGk fun h => absurd h hm

theorem exists_wFactor_small (hK : Nat.card K = 2) (hx : OddOrderIsometry Q 3 x)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hs : IsSmall (Q.comp (fixedSpace x).subtype)) :
    ∃ J : Subgroup (V ≃ₗ[K] V), J ≤ isometryCentralizer Q x ⊓ orthDerived Q ∧
      (∀ f ∈ isometryCentralizer Q x ⊓ orthDerived Q, ∀ n ∈ J, f * n * f⁻¹ ∈ J) ∧
      NoNormalPPrime 3 J ∧
      ∀ {G : V ≃ₗ[K] V}, G * x = x * G → ∀ {k : ℕ}, Nat.Coprime 3 k → G ^ k = 1 →
        (∀ f ∈ J, G * f = f * G) → ∀ w ∈ fixedSpace x, G w = w := by
  classical
  have := charP_two hK
  obtain ⟨-, -, -, -, -, -, hodd, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hρL : ∀ ρ ∈ braidSet Q (fixedSpace x),
      ρ ∈ isometryCentralizer Q x ⊓ orthDerived Q := by
    intro ρ hρ
    have hO := braidSet_mem_orth hρ
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hO, ?_⟩, ?_⟩
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (braidSet_comm_of_fixed hx.mem (fun w hw => mem_fixedSpace.mp hw) hρ).symm
    · exact hodd ρ hO
        (Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one (braidSet_pow_three hρ)))
  refine ⟨Subgroup.closure (braidSet Q (fixedSpace x)), (Subgroup.closure_le _).2 hρL, ?_,
    noNormalPPrime_closure_braidSet hs, ?_⟩
  · intro f hf n hn
    obtain ⟨hfO, hfx⟩ := Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hf).1
    have hfx' : f * x = x * f := Subgroup.mem_centralizer_singleton_iff.mp hfx
    refine conj_mem_closure_braidSet hfO (fun w hw => ?_) hn
    rw [mem_fixedSpace] at hw ⊢
    have := congrArg (fun e : V ≃ₗ[K] V => e w) hfx'
    simp only [LinearEquiv.mul_apply] at this
    rw [← this, hw]
  · intro G _ k hk hGk hcomm
    exact fixes_of_commute_braidSet hK hs (fun ρ hρ => hcomm ρ (Subgroup.subset_closure hρ)) hk hGk

theorem exists_wFactor (hK : Nat.card K = 2) (hx : OddOrderIsometry Q 3 x)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hpar : IsPlusType Q ↔ Even (finrank K V / 2)) :
    ∃ J : Subgroup (V ≃ₗ[K] V), J ≤ isometryCentralizer Q x ⊓ orthDerived Q ∧
      (∀ f ∈ isometryCentralizer Q x ⊓ orthDerived Q, ∀ n ∈ J, f * n * f⁻¹ ∈ J) ∧
      NoNormalPPrime 3 J ∧
      ∀ {G : V ≃ₗ[K] V}, G ∈ TauCeti.QuadraticMap.orthogonalGroup Q → G * x = x * G →
        ∀ {k : ℕ}, Nat.Coprime 3 k → G ^ k = 1 → (∀ f ∈ J, G * f = f * G) →
          ∀ w ∈ fixedSpace x, G w = w := by
  classical
  have := charP_two hK
  obtain ⟨a, ha⟩ := hx.even_finrank_fixed
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ 3 ≤ a by omega) with h0 | h1 | h2 | h3
  · refine ⟨⊥, bot_le, ?_, fun N hN _ _ => le_bot_iff.mp hN, ?_⟩
    · intro f _ n hn
      rw [Subgroup.mem_bot] at hn ⊢
      rw [hn, mul_one, mul_inv_cancel]
    · intro G _ _ k _ _ _ w hw
      have hbot : fixedSpace x = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
      rw [hbot, Submodule.mem_bot] at hw
      rw [hw, map_zero]
  · have hs : IsSmall (Q.comp (fixedSpace x).subtype) :=
      ⟨hK, hx.polarBilin_fixed_nondegenerate, Or.inl ⟨by omega, fun hp => by
        have := (isPlusType_fixedSpace_iff hK hx hpar).1 hp
        rw [show finrank K (fixedSpace x) / 2 = 1 by omega] at this
        exact absurd this (by decide)⟩⟩
    obtain ⟨J, hJL, hJn, hJ, hJfix⟩ := exists_wFactor_small hK hx hQ hT hs
    exact ⟨J, hJL, hJn, hJ, fun _ hGx _ hk hGk hcomm => hJfix hGx hk hGk hcomm⟩
  · have hs : IsSmall (Q.comp (fixedSpace x).subtype) :=
      ⟨hK, hx.polarBilin_fixed_nondegenerate, Or.inr ⟨by omega,
        (isPlusType_fixedSpace_iff hK hx hpar).2 (by
          rw [show finrank K (fixedSpace x) / 2 = 2 by omega]
          decide)⟩⟩
    obtain ⟨J, hJL, hJn, hJ, hJfix⟩ := exists_wFactor_small hK hx hQ hT hs
    exact ⟨J, hJL, hJn, hJ, fun _ hGx _ hk hGk hcomm => hJfix hGx hk hGk hcomm⟩
  · have h6 : 6 ≤ finrank K (fixedSpace x) := by omega
    refine ⟨supportedFixedDerived Q x, le_inf supportedFixedDerived_le_isometryCentralizer
      hx.supportedFixedDerived_le_orthDerived,
      fun f hf n hn => hx.conj_mem_supportedFixedDerived (Subgroup.mem_inf.mp hf).1 hn,
      noNormalPPrime_supportedFixedDerived hK hx hQ h6, ?_⟩
    intro G hGO hGx k hk hGk hcomm
    exact orth2_fixes_fixedSpace hK hQ hx h6 hGO hGx hcomm

end Factors

section Centralizer

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem noNormalPPrime_isometryCentralizer_inf_orthDerived (hK : Nat.card K = 2)
    (hx : OddOrderIsometry Q 3 x) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hpar : IsPlusType Q ↔ Even (finrank K V / 2)) :
    NoNormalPPrime 3 (isometryCentralizer Q x ⊓ orthDerived Q) := by
  classical
  obtain ⟨Jh, hJhL, hJhn, hJh, hJhfix⟩ := exists_hFactor hK hx hQ hT
  obtain ⟨JW, hJWL, hJWn, hJW, hJWfix⟩ := exists_wFactor hK hx hQ hT hpar
  refine noNormalPPrime_of_components (fun b : Bool => cond b Jh JW) (fun b => ?_)
    (fun b => ?_) (fun b => ?_) ?_
  · cases b
    · exact hJWL
    · exact hJhL
  · cases b
    · exact hJWn
    · exact hJhn
  · cases b
    · exact hJW
    · exact hJh
  intro r hr hrc hro
  obtain ⟨hrM, -⟩ := Subgroup.mem_inf.mp hr
  obtain ⟨hrO, hrx⟩ := Subgroup.mem_inf.mp hrM
  have hrx' : r * x = x * r := Subgroup.mem_centralizer_singleton_iff.mp hrx
  exact eq_one_of_fixes hK hx
    (hJWfix hrO hrx' hro (pow_orderOf_eq_one r) fun f hf => hrc false f hf)
    (hJhfix hrx' hro (pow_orderOf_eq_one r) fun f hf => hrc true f hf)

theorem eq_one_of_commute_isometryCentralizer_inf (hK : Nat.card K = 2)
    (hx : OddOrderIsometry Q 3 x) (hxΩ : x ∈ orthDerived Q) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hpar : IsPlusType Q ↔ Even (finrank K V / 2)) {G : V ≃ₗ[K] V}
    (hG : G ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {k : ℕ} (hk : Nat.Coprime 3 k)
    (hGk : G ^ k = 1)
    (hcomm : ∀ f ∈ isometryCentralizer Q x ⊓ orthDerived Q, G * f = f * G) : G = 1 := by
  classical
  obtain ⟨Jh, hJhL, -, -, hJhfix⟩ := exists_hFactor hK hx hQ hT
  obtain ⟨JW, hJWL, -, -, hJWfix⟩ := exists_wFactor hK hx hQ hT hpar
  have hxM : x ∈ isometryCentralizer Q x :=
    Subgroup.mem_inf.mpr ⟨hx.mem, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hGx : G * x = x * G := hcomm x (Subgroup.mem_inf.mpr ⟨hxM, hxΩ⟩)
  exact eq_one_of_fixes hK hx
    (hJWfix hG hGx hk hGk fun f hf => hcomm f (hJWL hf))
    (hJhfix hGx hk hGk fun f hf => hcomm f (hJhL hf))

end Centralizer

end CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two

end
