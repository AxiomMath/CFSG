module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6B4
public import CFSG.RankThree.PartOne.TCX.F4.A2Unitary
public import CFSG.RankThree.PartOne.KE.E6TwFourData
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourDescent
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import CFSG.RankThree.Chevalley.SteinbergBNF4Block
public import CFSG.Sporadic.Suz.Simple

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Matrix
open CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.SL3RootPermuting

section Certs

variable {Ω : Type} [Field Ω] [CharP Ω 2]

namespace TwE6B

noncomputable def twE6BlockPhi {Fr : Ω →+* Ω} {n : ℕ} (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    [IsAlgClosed Ω] : Matrix.SpecialLinearGroup (Fin 3) Ω ≃*
      Matrix.SpecialLinearGroup (Fin 3) Ω :=
  Classical.choose (twE6_block_Phi (Ω := Ω) (Fr := Fr) (n := n) hFr)

theorem twE6BlockPhi_spec {Fr : Ω →+* Ω} {n : ℕ} (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    [IsAlgClosed Ω] :
    ∃ b : Fin 3 → Fin 3 → Ωˣ,
      (∀ g : ↥(subsystemGroup Tag.E6 Ω support56),
        ((twE6BlockPhi (Ω := Ω) hFr (a2Equiv₂ Ω g) :
          Matrix.SpecialLinearGroup (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
          a2Mat₂ (TwistedDiag.theta Fr (g : ModGL Tag.E6 Ω))) ∧
      (∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
        ((twE6BlockPhi (Ω := Ω) hFr
            (Matrix.SpecialLinearGroup.transvection hij t) :
          Matrix.SpecialLinearGroup (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
          1 + single j i ((b i j : Ω) * frobPow (Ω := Ω) n t)) :=
  Classical.choose_spec (twE6_block_Phi (Ω := Ω) (Fr := Fr) (n := n) hFr)

private theorem twE6BlockPhi_fixed {Fr : Ω →+* Ω}
    {Φ : Matrix.SpecialLinearGroup (Fin 3) Ω ≃* Matrix.SpecialLinearGroup (Fin 3) Ω}
    (hΦ : ∀ g : ↥(subsystemGroup Tag.E6 Ω support56),
      ((Φ (a2Equiv₂ Ω g) : Matrix.SpecialLinearGroup (Fin 3) Ω) :
        Matrix (Fin 3) (Fin 3) Ω) =
        a2Mat₂ (TwistedDiag.theta Fr (g : ModGL Tag.E6 Ω)))
    {g : ↥(subsystemGroup Tag.E6 Ω support56)}
    (hfix : TwistedDiag.theta Fr (g : ModGL Tag.E6 Ω) = (g : ModGL Tag.E6 Ω)) :
    Φ (a2Equiv₂ Ω g) = a2Equiv₂ Ω g := by
  apply Subtype.ext
  rw [hΦ g, hfix, a2Equiv₂_apply, coe_a2Rep₂]

private theorem twE6Block_symm_mem {Fr : Ω →+* Ω}
    {Φ : Matrix.SpecialLinearGroup (Fin 3) Ω ≃* Matrix.SpecialLinearGroup (Fin 3) Ω}
    (hΦ : ∀ g : ↥(subsystemGroup Tag.E6 Ω support56),
      ((Φ (a2Equiv₂ Ω g) : Matrix.SpecialLinearGroup (Fin 3) Ω) :
        Matrix (Fin 3) (Fin 3) Ω) =
        a2Mat₂ (TwistedDiag.theta Fr (g : ModGL Tag.E6 Ω)))
    (hQ : ∀ g ∈ subsystemGroup Tag.E6 Ω support56,
      TwistedDiag.theta Fr g ∈ subsystemGroup Tag.E6 Ω support56)
    (Y : ↥(fixSubgroup Φ)) :
    ((a2Equiv₂ Ω).symm Y.1 : ↥(subsystemGroup Tag.E6 Ω support56)).1 ∈ twE6Block Fr := by
  rw [mem_twE6Block]
  refine ⟨((a2Equiv₂ Ω).symm Y.1).2, ?_⟩
  rw [TwistedDiag.mem_thetaFixed]
  refine ⟨CFSG.RankThree.Chevalley.subsystemGroup_le_adjointGroup_of_any
    (τ := Tag.E6) (L := Ω) support56 ((a2Equiv₂ Ω).symm Y.1).2, ?_⟩
  have hY : Φ Y.1 = Y.1 := (mem_fixSubgroup Φ).1 Y.2
  have hmaps : Φ (a2Equiv₂ Ω ((a2Equiv₂ Ω).symm Y.1)) =
      a2Equiv₂ Ω ⟨TwistedDiag.theta Fr
        ((a2Equiv₂ Ω).symm Y.1 : ↥(subsystemGroup Tag.E6 Ω support56)).1,
        hQ _ ((a2Equiv₂ Ω).symm Y.1).2⟩ := by
    apply Subtype.ext
    rw [hΦ ((a2Equiv₂ Ω).symm Y.1), a2Equiv₂_apply, coe_a2Rep₂]
  have hθX : (⟨TwistedDiag.theta Fr
      ((a2Equiv₂ Ω).symm Y.1 : ↥(subsystemGroup Tag.E6 Ω support56)).1,
      hQ _ ((a2Equiv₂ Ω).symm Y.1).2⟩ :
        ↥(subsystemGroup Tag.E6 Ω support56)) = (a2Equiv₂ Ω).symm Y.1 := by
    apply (a2Equiv₂ Ω).injective
    rw [← hmaps, MulEquiv.apply_symm_apply, hY]
  exact congrArg Subtype.val hθX

noncomputable def twE6BlockEquivFix {Fr : Ω →+* Ω}
    {Φ : Matrix.SpecialLinearGroup (Fin 3) Ω ≃* Matrix.SpecialLinearGroup (Fin 3) Ω}
    (hΦ : ∀ g : ↥(subsystemGroup Tag.E6 Ω support56),
      ((Φ (a2Equiv₂ Ω g) : Matrix.SpecialLinearGroup (Fin 3) Ω) :
        Matrix (Fin 3) (Fin 3) Ω) =
        a2Mat₂ (TwistedDiag.theta Fr (g : ModGL Tag.E6 Ω)))
    (hQ : ∀ g ∈ subsystemGroup Tag.E6 Ω support56,
      TwistedDiag.theta Fr g ∈ subsystemGroup Tag.E6 Ω support56) :
    ↥(twE6Block Fr) ≃* ↥(fixSubgroup Φ) where
  toFun g :=
    ⟨a2Equiv₂ Ω ⟨g.1, (mem_twE6Block.1 g.2).1⟩, by
      rw [mem_fixSubgroup]
      exact twE6BlockPhi_fixed (Ω := Ω) hΦ
        ((TwistedDiag.mem_thetaFixed (Fr := Fr)).1 (mem_twE6Block.1 g.2).2).2⟩
  invFun Y := ⟨_, twE6Block_symm_mem (Ω := Ω) hΦ hQ Y⟩
  left_inv g := Subtype.ext (by
    show ((a2Equiv₂ Ω).symm (a2Equiv₂ Ω ⟨g.1, (mem_twE6Block.1 g.2).1⟩)).1 = g.1
    rw [MulEquiv.symm_apply_apply])
  right_inv Y := Subtype.ext (by
    refine (congrArg (a2Equiv₂ Ω) (show (⟨((a2Equiv₂ Ω).symm Y.1).1,
        (mem_twE6Block.1 (twE6Block_symm_mem (Ω := Ω) hΦ hQ Y)).1⟩ :
          ↥(subsystemGroup Tag.E6 Ω support56)) = (a2Equiv₂ Ω).symm Y.1
      from Subtype.ext rfl)).trans ?_
    exact MulEquiv.apply_symm_apply (a2Equiv₂ Ω) Y.1)
  map_mul' g h := Subtype.ext (by
    simpa using map_mul (a2Equiv₂ Ω)
      (⟨g.1, (mem_twE6Block.1 g.2).1⟩ : ↥(subsystemGroup Tag.E6 Ω support56))
      (⟨h.1, (mem_twE6Block.1 h.2).1⟩ : ↥(subsystemGroup Tag.E6 Ω support56)))

theorem twE6Block_nonempty_mulEquiv_statedSU {Fr : Ω →+* Ω} {n : ℕ} {K : Type} [Field K]
    [Algebra K Ω] [IsAlgClosure K Ω] (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 3 ≤ n) (hod : Odd n) :
    Nonempty (↥(twE6Block Fr) ≃* ↥(CFSG.Open.StatedSU 3 (2 ^ n) K)) := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK']; positivity)
  haveI : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hK'
  haveI : CharP Ω 2 :=
    charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  obtain ⟨b, hΦmat, hΦt⟩ := twE6BlockPhi_spec (Ω := Ω) (Fr := Fr) (n := n) hFr
  have hinjθ : Function.Injective (TwistedDiag.theta Fr) :=
    (MulAut.conj (TwistedDiag.n0 Ω)).injective.comp
      (twistHom_injective TwistTag.E6 Ω Fr)
  have hθ' : ∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
      TwistedDiag.theta Fr (pinnedX Tag.E6 Ω (chainRoot chain56 i j) c) =
        pinnedX Tag.E6 Ω (chainRoot chain56 j i) (e * frobPow (Ω := Ω) n c) := by
    intro i j hij
    refine ⟨1, by norm_num, fun c => ?_⟩
    rw [theta_pinnedX (Ω := Ω) hFr (isRoot_chainRoot56 hij) c,
      (chainRoot_swap chain56 i j).symm, frobPow_apply, one_mul]
  have hQ : ∀ g ∈ subsystemGroup Tag.E6 Ω support56,
      TwistedDiag.theta Fr g ∈ subsystemGroup Tag.E6 Ω support56 :=
    twE6_theta_maps_block_of_chainRoot (Ω := Ω) n (TwistedDiag.theta Fr) hinjθ hθ'
  let σ : K ≃+* K := iterateFrobeniusEquiv K 2 n
  let k : Subfield K := CFSG.LieType.Chevalley.fixSubfield σ
  have hσ : ∀ c : K, σ c = c ^ (2 ^ n) := fun c =>
    iterateFrobeniusEquiv_def (R := K) (p := 2) (n := n) c
  have hkcard : Nat.card k = 2 ^ n :=
    CFSG.RankThree.PartOne.KE.card_fixSubfield_twisted Nat.prime_two (by omega) hK σ hσ
  haveI hkalg : IsAlgClosure k Ω := by
    have : Module.Finite k K := Module.Finite.of_finite
    have : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.of_finite _ K
    exact IsAlgClosure.ofAlgebraic k K Ω
  have htrans : ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
      ((twE6BlockPhi (Ω := Ω) (Fr := Fr) (n := n) hFr
          (Matrix.SpecialLinearGroup.transvection hij t) :
        Matrix.SpecialLinearGroup (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
        1 + single ((Equiv.refl (Fin 3)) j) ((Equiv.refl (Fin 3)) i)
          ((b i j : Ω) * t ^ 2 ^ n) := by
    intro i j hij t
    simpa only [frobPow_apply, Equiv.refl_apply] using hΦt i j hij t
  obtain ⟨-, ⟨H, hH⟩, -, -, -⟩ :=
    sl3_root_permuting_frobenius_fixed_unitary (ℓ := 2) (f := n) (k := k) (Ω := Ω)
      Nat.prime_two (by omega) hkcard (Equiv.refl (Fin 3))
      (twE6BlockPhi (Ω := Ω) (Fr := Fr) (n := n) hFr) b htrans
  have hι : ∀ y : Ω, y ^ 2 ^ (2 * n) = y ↔ ∃ c : K, algebraMap K Ω c = y := by
    intro y
    rw [← hK']
    exact TauCeti.FiniteField.pow_natCard_eq_self_iff_mem_range_algebraMap y
  obtain ⟨ψ, hψinj, hψrange⟩ :=
    CFSG.RankThree.PartOne.TCX.F4.exists_unitary_hom_of_fix (L := Ω) (g := n) (K₂ := K)
      (algebraMap K Ω) hK hι (twE6BlockPhi (Ω := Ω) (Fr := Fr) (n := n) hFr) H hH
  refine ⟨(twE6BlockEquivFix (Ω := Ω) hΦmat hQ).trans ?_⟩
  exact ((MonoidHom.ofInjective hψinj).trans (MulEquiv.subgroupCongr hψrange)).symm

theorem twE6_block_finite {Fr : Ω →+* Ω} {n : ℕ} {K : Type} [Field K]
    [Algebra K Ω] [IsAlgClosure K Ω] (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 3 ≤ n) (hod : Odd n) :
    Finite ↥(twE6Block Fr) := by
  obtain ⟨e⟩ := twE6Block_nonempty_mulEquiv_statedSU (Ω := Ω) hFr hK hn hod
  have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK']; positivity)
  haveI : Finite ↥(CFSG.Open.StatedSU 3 (2 ^ n) K) := inferInstance
  exact Finite.of_equiv _ e.symm.toEquiv

theorem twE6_block_isQuasisimple {Fr : Ω →+* Ω} {n : ℕ} {K : Type} [Field K]
    [Algebra K Ω] [IsAlgClosure K Ω] (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 3 ≤ n) (hod : Odd n) :
    CFSG.Open.IsQuasisimple ↥(twE6Block Fr) ∧
      3 ∣ Nat.card (↥(twE6Block Fr) ⧸ Subgroup.center ↥(twE6Block Fr)) := by
  have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK']; positivity)
  obtain ⟨e⟩ := twE6Block_nonempty_mulEquiv_statedSU (Ω := Ω) hFr hK hn hod
  exact isQuasisimple_and_three_dvd_of_mulEquiv_statedSU (by omega) hK e

theorem twE6Block_le_C {Fr : Ω →+* Ω} {n : ℕ} {K : Type} [Field K]
    [Algebra K Ω] [IsAlgClosure K Ω] (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 3 ≤ n) (hod : Odd n) :
    twE6Block Fr ≤ twE6C Fr := by
  haveI : Finite ↥(twE6Block Fr) :=
    twE6_block_finite (Ω := Ω) hFr hK hn hod
  have hq := twE6_block_isQuasisimple (Ω := Ω) hFr hK hn hod
  have hperf : ⁅twE6Block Fr, twE6Block Fr⁆ = twE6Block Fr := by
    have h := Subgroup.map_subtype_commutator (H := twE6Block Fr)
    rw [hq.1.1, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
    exact h.symm
  exact twE6Block_le_C_of_perfect Fr hperf

def eBarTuple (ω : Ωˣ) : Fin Tag.E6.rank → Ωˣ := fun i => if i.val = 3 then ω ^ 2 else 1

def fBarTuple (ω : Ωˣ) : Fin Tag.E6.rank → Ωˣ :=
  fun i => if i.val = 0 ∨ i.val = 2 ∨ i.val = 3 then ω ^ 2 else 1

noncomputable abbrev eBar (ω : Ωˣ) : ModGL Tag.E6 Ω := rootDiagUnit Tag.E6 (eBarTuple ω)

noncomputable abbrev fBar (ω : Ωˣ) : ModGL Tag.E6 Ω := rootDiagUnit Tag.E6 (fBarTuple ω)

private theorem cartan4_val (i : Fin Tag.E6.rank) :
    Tag.E6.cartan 4 i =
      (if i.val = 3 then (-1 : ℤ) else if i.val = 4 then 2 else if i.val = 5 then -1 else 0) := by
  fin_cases i <;> decide

private theorem cartan5_val (i : Fin Tag.E6.rank) :
    Tag.E6.cartan 5 i = (if i.val = 4 then (-1 : ℤ) else if i.val = 5 then 2 else 0) := by
  fin_cases i <;> decide

private theorem cartan2_val (i : Fin Tag.E6.rank) :
    Tag.E6.cartan 2 i =
      (if i.val = 0 then (-1 : ℤ) else if i.val = 2 then 2 else if i.val = 3 then -1 else 0) := by
  fin_cases i <;> decide

theorem eBar_eq_torusElt {ω : Ωˣ} (hω3 : ω ^ 3 = 1) :
    eBar (Ω := Ω) ω = torusElt Tag.E6 Ω 4 ω * torusElt Tag.E6 Ω 5 (ω ^ 2) := by
  have hω3z : ω ^ (3 : ℤ) = 1 := by simpa using hω3
  have hωinv : ω⁻¹ = ω ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, show ω * ω ^ 2 = ω ^ 3 by group, hω3]
  rw [eBar, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
  congr 1
  funext i
  simp only [Pi.mul_apply, cartan4_val, cartan5_val, eBarTuple]
  fin_cases i <;>
    (rw [show ω ^ 2 = ω ^ (2 : ℤ) by norm_num [zpow_ofNat],
      ← _root_.zpow_mul, ← _root_.zpow_add, zpow_eq_zpow_emod' _ hω3z]
     norm_num [hω3, hωinv])

theorem fBar_eq_torusElt {ω : Ωˣ} (hω3 : ω ^ 3 = 1) :
    fBar (Ω := Ω) ω = torusElt Tag.E6 Ω 2 ω := by
  have hω3z : ω ^ (3 : ℤ) = 1 := by simpa using hω3
  have hωinv : ω⁻¹ = ω ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, show ω * ω ^ 2 = ω ^ 3 by group, hω3]
  rw [fBar, torusElt_eq_rootDiagUnit]
  congr 1
  funext i
  simp only [Pi.mul_apply, cartan2_val, fBarTuple]
  fin_cases i <;>
    (rw [show ω ^ 2 = ω ^ (2 : ℤ) by norm_num [zpow_ofNat],
      zpow_eq_zpow_emod' _ hω3z]
     norm_num [hω3, hωinv])

private theorem three_dvd_two_pow_add_one_of_odd {n : ℕ} (hn : Odd n) : 3 ∣ 2 ^ n + 1 := by
  have h : ((2 : ZMod 3) ^ n) = -1 := by
    have h2 : (2 : ZMod 3) = -1 := by decide
    rw [h2]
    exact hn.neg_one_pow
  have h0 : ((2 ^ n + 1 : ℕ) : ZMod 3) = 0 := by
    push_cast
    rw [h]
    ring
    decide
  exact (ZMod.natCast_eq_zero_iff (2 ^ n + 1) 3).mp h0

private theorem omega_pow_Q_add_one {ω : Ωˣ} {n : ℕ} (hω3 : ω ^ 3 = 1) (hn : Odd n) :
    ω ^ (2 ^ n + 1) = 1 := by
  obtain ⟨k, hk⟩ := three_dvd_two_pow_add_one_of_odd hn
  rw [hk, pow_mul, hω3, one_pow]

theorem commute_rootDiagUnit_pinnedX {a : Fin Tag.E6.rank → Ωˣ}
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (hχ : rootChar a α = 1) (c : Ω) :
    Commute (rootDiagUnit Tag.E6 a) (pinnedX Tag.E6 Ω α c) := by
  have h := rootDiagUnit_conj_pinnedX (τ := Tag.E6) (K := Ω) a hα c
  rw [hχ, Units.val_one, one_mul] at h
  exact (mul_inv_eq_iff_eq_mul).mp h

theorem rootDiagUnit_centralizes_rootSpan {a : Fin Tag.E6.rank → Ωˣ}
    {S : Set (Fin Tag.E6.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot Tag.E6 α)
    (hχ : ∀ α ∈ S, rootChar a α = 1) :
    rootSpan Tag.E6 Ω S ≤ Subgroup.centralizer
      ({rootDiagUnit Tag.E6 a} : Set (ModGL Tag.E6 Ω)) := by
  refine iSup₂_le fun α hα => ?_
  rw [rootSubgroup, Subgroup.closure_le]
  rintro _ ⟨c, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.2
    (commute_rootDiagUnit_pinnedX (hS α hα) (hχ α hα) c).symm

theorem rootChar_eBar_of_mem_support56 {ω : Ωˣ}
    {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ parabolicRoots Tag.E6 support56) :
    rootChar (eBarTuple ω) α = 1 := by
  rw [rootChar]
  refine Finset.prod_eq_one fun i _ => ?_
  by_cases h : i.val = 3
  · have hi : i ∉ support56 := by
      rw [mem_support56]
      rintro (h4 | h5)
      · have hv : i.val = 4 := by rw [h4]; decide
        omega
      · have hv : i.val = 5 := by rw [h5]; decide
        omega
    rw [eBarTuple, if_pos h, hα.2 i hi, _root_.zpow_zero]
  · rw [eBarTuple, if_neg h]; exact _root_.one_zpow _

theorem rootChar_fBar_of_mem_support56 {ω : Ωˣ}
    {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ parabolicRoots Tag.E6 support56) :
    rootChar (fBarTuple ω) α = 1 := by
  rw [rootChar]
  refine Finset.prod_eq_one fun i _ => ?_
  by_cases h : i.val = 0 ∨ i.val = 2 ∨ i.val = 3
  · have hi : i ∉ support56 := by
      rw [mem_support56]
      rintro (h4 | h5)
      · have hv : i.val = 4 := by rw [h4]; decide
        rcases h with h0 | h2 | h3 <;> omega
      · have hv : i.val = 5 := by rw [h5]; decide
        rcases h with h0 | h2 | h3 <;> omega
    rw [fBarTuple, if_pos h, hα.2 i hi, _root_.zpow_zero]
  · rw [fBarTuple, if_neg h]; exact _root_.one_zpow _

theorem twE6Block_le_centralizer_eBar {Fr : Ω →+* Ω} {ω : Ωˣ} :
    twE6Block Fr ≤ Subgroup.centralizer ({eBar (Ω := Ω) ω} : Set (ModGL Tag.E6 Ω)) := by
  have h := rootDiagUnit_centralizes_rootSpan (a := eBarTuple ω)
    (S := parabolicRoots Tag.E6 support56) (hS := fun α hα => hα.1)
    (hχ := fun α hα => rootChar_eBar_of_mem_support56 (ω := ω) hα)
  have h' : subsystemGroup Tag.E6 Ω support56 ≤
      Subgroup.centralizer ({eBar (Ω := Ω) ω} : Set (ModGL Tag.E6 Ω)) := by
    rw [subsystemGroup_eq_rootSpan]
    exact h
  exact (twE6Block_le_subsystem Fr).trans h'

theorem twE6Block_le_centralizer_fBar {Fr : Ω →+* Ω} {ω : Ωˣ} :
    twE6Block Fr ≤ Subgroup.centralizer ({fBar (Ω := Ω) ω} : Set (ModGL Tag.E6 Ω)) := by
  have h := rootDiagUnit_centralizes_rootSpan (a := fBarTuple ω)
    (S := parabolicRoots Tag.E6 support56) (hS := fun α hα => hα.1)
    (hχ := fun α hα => rootChar_fBar_of_mem_support56 (ω := ω) hα)
  have h' : subsystemGroup Tag.E6 Ω support56 ≤
      Subgroup.centralizer ({fBar (Ω := Ω) ω} : Set (ModGL Tag.E6 Ω)) := by
    rw [subsystemGroup_eq_rootSpan]
    exact h
  exact (twE6Block_le_subsystem Fr).trans h'

private theorem sq_pow_Q_add_one {ω : Ωˣ} {n : ℕ} (hωQ : ω ^ (2 ^ n + 1) = 1) :
    (ω ^ 2) ^ (2 ^ n + 1) = 1 := by
  calc (ω ^ 2) ^ (2 ^ n + 1) = ω ^ (2 * (2 ^ n + 1)) := by rw [pow_mul]
    _ = ω ^ ((2 ^ n + 1) * 2) := by rw [mul_comm]
    _ = (ω ^ (2 ^ n + 1)) ^ 2 := by rw [← pow_mul]
    _ = 1 := by rw [hωQ, one_pow]

theorem theta_eBar_eq {Fr : Ω →+* Ω} {ω : Ωˣ} {n : ℕ}
    (hFr : ∀ c, Fr c = c ^ (2 ^ n)) (hωQ : ω ^ (2 ^ n + 1) = 1) :
    TwistedDiag.theta Fr (eBar (Ω := Ω) ω) = eBar (Ω := Ω) ω := by
  rw [eBar, (TwistedDiag.theta_rootDiagUnit_eq_iff Fr hFr _).2]
  intro i
  by_cases h : i.val = 3
  · rw [eBarTuple, if_pos h]
    exact sq_pow_Q_add_one hωQ
  · rw [eBarTuple, if_neg h]
    exact one_pow _

theorem eBar_mem_twE6Block {Fr : Ω →+* Ω} {ω : Ωˣ} {n : ℕ}
    (hFr : ∀ c, Fr c = c ^ (2 ^ n)) (hω3 : ω ^ 3 = 1) (hn : Odd n) :
    eBar (Ω := Ω) ω ∈ twE6Block Fr := by
  have hsub : eBar (Ω := Ω) ω ∈ subsystemGroup Tag.E6 Ω support56 := by
    rw [eBar_eq_torusElt hω3]
    exact mul_mem
      (subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus
        (i := e6Index 4) (by rw [mem_support56]; left; rfl) ω))
      (subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus
        (i := e6Index 5) (by rw [mem_support56]; right; rfl) (ω ^ 2)))
  rw [mem_twE6Block]
  refine ⟨hsub, ?_⟩
  rw [TwistedDiag.mem_thetaFixed]
  exact ⟨(CFSG.RankThree.Chevalley.subsystemGroup_le_adjointGroup_of_any
    (τ := Tag.E6) (L := Ω) support56) hsub,
    theta_eBar_eq hFr (omega_pow_Q_add_one hω3 hn)⟩

theorem eBar_mem_C {Fr : Ω →+* Ω} {ω : Ωˣ} {n : ℕ} {K : Type} [Field K]
    [Algebra K Ω] [IsAlgClosure K Ω] (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 3 ≤ n) (hod : Odd n) (hω3 : ω ^ 3 = 1) :
    eBar (Ω := Ω) ω ∈ twE6C Fr :=
  twE6Block_le_C (Ω := Ω) hFr hK hn hod (eBar_mem_twE6Block hFr hω3 hod)

private theorem sq_pow_three {ω : Ωˣ} (hω3 : ω ^ 3 = 1) : (ω ^ 2) ^ 3 = 1 := by
  rw [show (ω ^ 2) ^ 3 = (ω ^ 3) ^ 2 by group, hω3, one_pow]

theorem eBar_pow_three {ω : Ωˣ} (hω3 : ω ^ 3 = 1) : eBar (Ω := Ω) ω ^ 3 = 1 := by
  change (rootDiagUnitHom Tag.E6 Ω) (eBarTuple ω) ^ 3 = 1
  rw [← map_pow]
  have h : eBarTuple ω ^ 3 = 1 := by
    funext i
    fin_cases i <;> simp [eBarTuple, hω3, sq_pow_three hω3]
  rw [h, map_one]

theorem fBar_pow_three {ω : Ωˣ} (hω3 : ω ^ 3 = 1) : fBar (Ω := Ω) ω ^ 3 = 1 := by
  change (rootDiagUnitHom Tag.E6 Ω) (fBarTuple ω) ^ 3 = 1
  rw [← map_pow]
  have h : fBarTuple ω ^ 3 = 1 := by
    funext i
    fin_cases i <;> simp [fBarTuple, hω3, sq_pow_three hω3]
  rw [h, map_one]

theorem eBar_ne_one {ω : Ωˣ} (hω : orderOf ω = 3) : eBar (Ω := Ω) ω ≠ 1 := by
  intro h
  change rootDiagUnit Tag.E6 (eBarTuple ω) = 1 at h
  have h1 : eBarTuple ω = 1 := rootDiagUnit_injective (h.trans rootDiagUnit_one.symm)
  have h2 := congrFun h1 ⟨3, by decide⟩
  simp only [eBarTuple, Pi.one_apply, if_pos rfl] at h2
  have hdvd : orderOf ω ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
  rw [hω] at hdvd
  norm_num at hdvd

theorem fBar_ne_one {ω : Ωˣ} (hω : orderOf ω = 3) : fBar (Ω := Ω) ω ≠ 1 := by
  intro h
  change rootDiagUnit Tag.E6 (fBarTuple ω) = 1 at h
  have h1 : fBarTuple ω = 1 := rootDiagUnit_injective (h.trans rootDiagUnit_one.symm)
  have h2 := congrFun h1 ⟨0, by decide⟩
  simp only [fBarTuple, Pi.one_apply, if_pos (Or.inl rfl)] at h2
  have hdvd : orderOf ω ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
  rw [hω] at hdvd
  norm_num at hdvd

theorem orderOf_eBar {ω : Ωˣ} (hω3 : ω ^ 3 = 1) (hω : orderOf ω = 3) :
    orderOf (eBar (Ω := Ω) ω) = 3 :=
  orderOf_eq_prime (eBar_pow_three hω3) (eBar_ne_one hω)

theorem orderOf_fBar {ω : Ωˣ} (hω3 : ω ^ 3 = 1) (hω : orderOf ω = 3) :
    orderOf (fBar (Ω := Ω) ω) = 3 :=
  orderOf_eq_prime (fBar_pow_three hω3) (fBar_ne_one hω)

theorem commute_eBar_fBar {ω : Ωˣ} : Commute (eBar (Ω := Ω) ω) (fBar (Ω := Ω) ω) := by
  change rootDiagUnit Tag.E6 (eBarTuple ω) * rootDiagUnit Tag.E6 (fBarTuple ω) =
    rootDiagUnit Tag.E6 (fBarTuple ω) * rootDiagUnit Tag.E6 (eBarTuple ω)
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul]
  congr 1
  exact mul_comm _ _

end TwE6B

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
