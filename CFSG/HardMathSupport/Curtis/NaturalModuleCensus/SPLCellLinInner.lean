module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellLinOuter
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellLinBlock
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellG
public import CFSG.HardMathSupport.Curtis.Coordinator.SPLCellSp
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellLin

open Matrix Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm
open CFSG.HardMathSupport.Curtis.Coordinator
open CFSG.HardMathSupport.Curtis.Coordinator.SPLCell
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.RankThree.UnitaryDescent (twistedNorm twistedNorm_succ')

section GammaHat

variable {n : ℕ} {K : Type} [Field K]

@[expose] noncomputable def gammaHat (M : GL (Fin n) K) (σ : K ≃+* K) : MulAut (GL (Fin n) K) :=
  MulAut.conj M * glAut σ

theorem gammaHat_apply (M : GL (Fin n) K) (σ : K ≃+* K) (e : GL (Fin n) K) :
    gammaHat M σ e = M * glAut σ e * M⁻¹ := rfl

theorem glAut_mul_conj (σ : K ≃+* K) (A : GL (Fin n) K) :
    glAut σ * MulAut.conj A * (glAut σ)⁻¹ = MulAut.conj (glAut σ A) := by
  ext e
  simp [MulAut.conj_apply]

theorem gammaHat_pow (M : GL (Fin n) K) (σ : K ≃+* K) (k : ℕ) :
    gammaHat M σ ^ k = MulAut.conj (twistedNorm σ M k) * glAut (σ ^ k) := by
  induction k with
  | zero => simp [CFSG.RankThree.UnitaryDescent.twistedNorm_zero]
  | succ k ih =>
    rw [pow_succ', ih, gammaHat, twistedNorm_succ', map_mul, pow_succ', map_mul]
    have h := glAut_mul_conj σ (twistedNorm σ M k)
    calc MulAut.conj M * glAut σ * (MulAut.conj (twistedNorm σ M k) * glAut (σ ^ k))
        = MulAut.conj M * (glAut σ * MulAut.conj (twistedNorm σ M k) * (glAut σ)⁻¹) *
            (glAut σ * glAut (σ ^ k)) := by group
      _ = _ := by rw [h]

theorem gammaHat_pow_eq_one (M : GL (Fin n) K) (σ : K ≃+* K) {m : ℕ} (hσ : σ ^ m = 1)
    {c : Kˣ} (hc : GeneralLinearGroup.scalar (Fin n) c = twistedNorm σ M m) :
    gammaHat M σ ^ m = 1 := by
  rw [gammaHat_pow, hσ, map_one, mul_one, ← hc]
  ext e
  have : GeneralLinearGroup.scalar (Fin n) c ∈ Subgroup.center (GL (Fin n) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  simp only [MulAut.conj_apply, MulAut.one_apply]
  rw [(Subgroup.mem_center_iff.1 this e).symm, mul_inv_cancel_right]

theorem conjAut_gammaHat (M : GL (Fin n) K) (σ : K ≃+* K) (e : GL (Fin n) K) :
    conjAut n K (gammaHat M σ e) =
      MulAut.conj (conjAut n K M * fieldAut n K σ) (conjAut n K e) := by
  obtain ⟨-, -, htrans, -⟩ := standard_automorphism_transport (K := K) (n := n)
  rw [gammaHat_apply, map_mul, map_mul, map_inv, ← CFSG.RankThree.LinearDescent.map_eq_glAut,
    ← htrans, MulAut.conj_apply]
  group

end GammaHat

section Step3

open scoped IsMulCommutative

variable {n : ℕ} {K : Type} [Field K]

theorem aut_mul_conj_mul_inv {S : Type*} [Group S] (ζ : MulAut S) (x : S) :
    ζ * MulAut.conj x * ζ⁻¹ = MulAut.conj (ζ x) := by
  ext y
  simp [MulAut.conj_apply]

theorem conj_injective_projectiveSL (hn : 3 ≤ n) :
    Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)) := by
  have hc := CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (k := K) hn
  rw [injective_iff_map_eq_one]
  intro x hx
  have hmem : x ∈ Subgroup.center (projectiveSL n K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun a : MulAut (projectiveSL n K) => a g) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  rw [hc] at hmem
  exact Subgroup.mem_bot.1 hmem

theorem conjAut_ker_le_center [Finite K] (hn : 3 ≤ n) :
    (conjAut n K).ker ≤ Subgroup.center (GL (Fin n) K) := by
  intro B hB
  obtain ⟨c, rfl⟩ := exists_scalar_of_conjAut_eq_one hn (MonoidHom.mem_ker.1 hB)
  rw [GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨c, rfl⟩

theorem isCyclic_conjAut_ker [Finite K] (hn : 3 ≤ n) : IsCyclic (conjAut n K).ker := by
  let R : Subgroup (GL (Fin n) K) := (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range
  have hR : IsCyclic R :=
    isCyclic_of_surjective (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  have hle : (conjAut n K).ker ≤ R := by
    intro B hB
    have := conjAut_ker_le_center hn hB
    rwa [GeneralLinearGroup.center_eq_range_scalar] at this
  have : IsCyclic ↥((conjAut n K).ker.subgroupOf R) := Subgroup.isCyclic _
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hle).surjective

theorem map_conj_data [Finite K] (hn : 3 ≤ n) {p : ℕ} (Ē : Subgroup (projectiveSL n K))
    (hEc : IsMulCommutative Ē) (hEp : ∀ x ∈ Ē, x ^ p = 1) (hcard : Nat.card Ē = p ^ 4)
    (γ : MulAut (projectiveSL n K)) (hγE : ∀ x ∈ Ē, γ x ∈ Ē) (hnt : ∃ x ∈ Ē, γ x ≠ x) :
    IsMulCommutative (Ē.map (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K))) ∧
    (∀ x ∈ Ē.map (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)), x ^ p = 1) ∧
    Nat.card (Ē.map (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K))) = p ^ 4 ∧
    (∀ x ∈ Ē.map (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)),
      ∃ e : GL (Fin n) K, conjAut n K e = x) ∧
    (∀ x ∈ Ē.map (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)),
      MulAut.conj γ x ∈ Ē.map (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K))) ∧
    (∃ x ∈ Ē.map (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)),
      MulAut.conj γ x ≠ x) := by
  classical
  have hinj := conj_injective_projectiveSL (K := K) hn
  let Ē' : Subgroup (MulAut (projectiveSL n K)) :=
    Ē.map (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K))
  have hcard' : Nat.card Ē' = p ^ 4 := (Subgroup.card_map_of_injective hinj).trans hcard
  have hEc' : IsMulCommutative Ē' := by
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨a0, ha0, ha⟩ := a.2
    obtain ⟨b0, hb0, hb⟩ := b.2
    apply Subtype.ext
    change (a : MulAut (projectiveSL n K)) * b = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hEc.is_comm.comm (⟨a0, ha0⟩ : ↥Ē) ⟨b0, hb0⟩)
  have hEp' : ∀ x ∈ Ē', x ^ p = 1 := by
    rintro _ ⟨a0, ha0, rfl⟩
    rw [← map_pow, hEp a0 ha0, map_one]
  have hπE : ∀ x ∈ Ē', ∃ e : GL (Fin n) K, conjAut n K e = x := by
    rintro _ ⟨a0, ha0, rfl⟩
    obtain ⟨g, rfl⟩ := proj_surjective n K a0
    exact ⟨SpecialLinearGroup.toGL g, conjAut_toGL g⟩
  have hγE' : ∀ x ∈ Ē', MulAut.conj γ x ∈ Ē' := by
    rintro _ ⟨a0, ha0, rfl⟩
    refine ⟨γ a0, hγE a0 ha0, ?_⟩
    rw [MulAut.conj_apply]
    exact (aut_mul_conj_mul_inv γ a0).symm
  have hnt' : ∃ x ∈ Ē', MulAut.conj γ x ≠ x := by
    obtain ⟨a0, ha0, hne⟩ := hnt
    refine ⟨MulAut.conj a0, ⟨a0, ha0, rfl⟩, fun h => hne (hinj ?_)⟩
    rw [MulAut.conj_apply, aut_mul_conj_mul_inv] at h
    exact h
  exact ⟨hEc', hEp', hcard', hπE, hγE', hnt'⟩

theorem lin_step3 [Finite K] (hn : 3 ≤ n) {p r k : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hrp : ¬ r ∣ p - 1) (hr2 : ¬ r ∣ p ^ 2 - 1) (hr3 : ¬ r ∣ p ^ 3 - 1) (hrne : r ≠ p)
    (Ē : Subgroup (projectiveSL n K)) (hEc : IsMulCommutative Ē) (hEp : ∀ x ∈ Ē, x ^ p = 1)
    (hcard : Nat.card Ē = p ^ 4) (y M : GL (Fin n) K) (σ : K ≃+* K) (c : Kˣ)
    (hyp : y ^ p = GeneralLinearGroup.scalar (Fin n) c)
    (hζE : ∀ x ∈ Ē, conjAut n K y x = x)
    (hγ : (conjAut n K M * fieldAut n K σ) ^ r ^ k = 1)
    (hγE : ∀ x ∈ Ē, (conjAut n K M * fieldAut n K σ) x ∈ Ē)
    (hcomm : (conjAut n K M * fieldAut n K σ) * conjAut n K y =
      conjAut n K y * (conjAut n K M * fieldAut n K σ))
    (hnt : ∃ x ∈ Ē, (conjAut n K M * fieldAut n K σ) x ≠ x) :
    ∀ e : GL (Fin n) K, conjAut n K e ∈ Ē.map (MulAut.conj : projectiveSL n K →* _) →
      y * e = e * y := by
  classical
  set γ : MulAut (projectiveSL n K) := conjAut n K M * fieldAut n K σ with hγdef
  obtain ⟨hEc', hEp', hcard', hπE, hγE', hnt'⟩ := map_conj_data hn Ē hEc hEp hcard γ hγE hnt
  have hπE' : ∀ e : GL (Fin n) K,
      conjAut n K e ∈ Ē.map (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)) →
      ∃ a0 ∈ Ē, conjAut n K e = MulAut.conj a0 :=
    fun e he => by
      obtain ⟨a0, ha0, h⟩ := he
      exact ⟨a0, ha0, h.symm⟩
  have hγ' : ∀ e, conjAut n K (gammaHat M σ e) = MulAut.conj γ (conjAut n K e) :=
    fun e => conjAut_gammaHat M σ e
  have hγ'' : MulAut.conj γ ^ r ^ k = 1 := by rw [← map_pow, hγ, map_one]
  have hy : y ^ p ∈ Subgroup.center (GL (Fin n) K) := by
    rw [hyp, GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  have hyE : ∀ e : GL (Fin n) K, conjAut n K e ∈
      Ē.map (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)) →
      conjAut n K (y * e * y⁻¹) = conjAut n K e := by
    intro e he
    obtain ⟨a0, ha0, h⟩ := hπE' e he
    rw [map_mul, map_mul, map_inv, h, aut_mul_conj_mul_inv, hζE a0 ha0]
  have hγy : gammaHat M σ y * y⁻¹ ∈ Subgroup.center (GL (Fin n) K) := by
    obtain ⟨c', hc'⟩ := exists_scalar_of_comm hn hcomm
    rw [gammaHat_apply, ← CFSG.RankThree.LinearDescent.map_eq_glAut, hc', mul_inv_cancel_right,
      GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c', rfl⟩
  exact central_of_gamma_commutes hp hr hrp hr2 hr3 hrne (conjAut n K) (conjAut_ker_le_center hn)
    (isCyclic_conjAut_ker hn) _ hEc' hEp' hcard' hπE y hy hyE (MulAut.conj γ) (gammaHat M σ) hγ'
    hγ'' hγE' hnt' hγy

theorem scalar_injective_fin {n : ℕ} {K : Type} [Field K] (hn : 0 < n) :
    Function.Injective (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K) := by
  intro a b h
  apply Units.ext
  have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩) h
  simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this

theorem not_elemAbelian_of_le_cyclic {A : Type*} [Group A] {p : ℕ} (hp : p.Prime)
    (R E : Subgroup A) [Finite R] [IsCyclic R] (hER : E ≤ R) (hEp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 4) : False := by
  classical
  have : Fintype R := Fintype.ofFinite R
  have hle : Nat.card E ≤ Nat.card {a : R // a ^ p = 1} := by
    refine Nat.card_le_card_of_injective
      (fun a : E => (⟨⟨a.1, hER a.2⟩, Subtype.ext (hEp a.1 a.2)⟩ : {a : R // a ^ p = 1})) ?_
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun t : {a : R // a ^ p = 1} => ((t.1 : R) : A)) hab
  have h2 : Nat.card {a : R // a ^ p = 1} ≤ p := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsCyclic.card_pow_eq_one_le hp.pos
  rw [hcard] at hle
  have : p ^ 1 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  rw [pow_one] at this
  omega

theorem lin_caseII_false [Finite K] [CharP K 2] (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (MulAut (projectiveSL n K))) (hEp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 4) (y : GL (Fin n) K) (c : Kˣ)
    (hyp : y ^ p = GeneralLinearGroup.scalar (Fin n) c) (hnp : ∀ b : K, b ^ p ≠ c)
    (hsolv : Group.IsSolvable ↥(autFix (conjAut n K y)))
    (hC : ∀ x ∈ E, ∃ e : GL (Fin n) K, conjAut n K e = x ∧ y * e = e * y) : False := by
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_charP_two hp hp2
  by_cases h2p : 2 * p ≤ n
  · exact not_isSolvable_autFix_of_scalar_pow_irreducible hp hpK c hyp hnp h2p hsolv
  · push Not at h2p
    obtain ⟨hmin, hirr⟩ := minpoly_linEnd_of_pow_scalar_irreducible hp c hyp hnp (by omega)
    obtain ⟨a⟩ : Nonempty (primaryFactors (linEnd y)) :=
      ⟨⟨_, minpoly_mem_primaryFactors hirr⟩⟩
    have hdeg : (minpoly K (linEnd y)).natDegree = p := by
      rw [hmin, Polynomial.natDegree_X_pow_sub_C]
    have hnm := finrank_eq_natDegree_mul_mult hirr a
    rw [hdeg] at hnm
    have hnp' : n = p := by
      rcases hm : mult (linEnd y) a with _ | _ | m
      · rw [hm] at hnm; omega
      · rw [hm] at hnm; omega
      · rw [hm] at hnm
        nlinarith [hp.two_le]
    have hcyc := isCyclic_centralizer_of_scalar_pow_irreducible hp c hyp hnp hnp'
    let f : Subgroup.centralizer ({y} : Set (GL (Fin n) K)) →* MulAut (projectiveSL n K) :=
      (conjAut n K).comp (Subgroup.centralizer ({y} : Set (GL (Fin n) K))).subtype
    have : IsCyclic f.range :=
      isCyclic_of_surjective f.rangeRestrict (MonoidHom.rangeRestrict_surjective _)
    refine not_elemAbelian_of_le_cyclic hp f.range E ?_ hEp hcard
    intro x hx
    obtain ⟨e, rfl, hye⟩ := hC x hx
    exact ⟨⟨e, Subgroup.mem_centralizer_singleton_iff.2 hye.symm⟩, rfl⟩

@[expose] noncomputable def glRep (n : ℕ) (K : Type) [Field K] :
    GL (Fin n) K →* ((Fin n → K) ≃ₗ[K] (Fin n → K)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n → K)).toMonoidHom.comp
    (GeneralLinearGroup.toLin : GL (Fin n) K ≃* _).toMonoidHom

theorem glRep_apply (e : GL (Fin n) K) (v : Fin n → K) :
    glRep n K e v = (e : Matrix (Fin n) (Fin n) K) *ᵥ v := rfl

theorem glRep_injective : Function.Injective (glRep n K) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n → K)).injective.comp
    (GeneralLinearGroup.toLin : GL (Fin n) K ≃* _).injective

theorem semiMap_gammaHat (M : GL (Fin n) K) (σ : K ≃+* K) (e : GL (Fin n) K) (v : Fin n → K) :
    semiMap M σ (glRep n K e v) = glRep n K (gammaHat M σ e) (semiMap M σ v) := by
  rw [glRep_apply, glRep_apply, semiMap_mulVec]
  rfl

theorem lin_caseI_false [Finite K] [CharP K 2] (hn : 3 ≤ n) {f : ℕ} (hK : Nat.card K = 2 ^ f)
    {p r k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime) (hr5 : 5 ≤ r) (hrp : ¬ r ∣ p - 1)
    (hr2 : ¬ r ∣ p ^ 2 - 1) (hr3 : ¬ r ∣ p ^ 3 - 1) (hrne : r ≠ p)
    (E : Subgroup (MulAut (projectiveSL n K))) (hEc : IsMulCommutative E)
    (hEp : ∀ x ∈ E, x ^ p = 1) (hcard : Nat.card E = p ^ 4)
    (hπE : ∀ x ∈ E, ∃ e : GL (Fin n) K, conjAut n K e = x)
    (y M : GL (Fin n) K) (σ : K ≃+* K) (hyp : y ^ p = 1)
    (hsolv : Group.IsSolvable ↥(autFix (conjAut n K y)))
    (hC : ∀ e : GL (Fin n) K, conjAut n K e ∈ E → y * e = e * y)
    (hγ : (conjAut n K M * fieldAut n K σ) ^ r ^ k = 1)
    (hγE : ∀ x ∈ E, MulAut.conj (conjAut n K M * fieldAut n K σ) x ∈ E)
    (hnt : ∃ x ∈ E, MulAut.conj (conjAut n K M * fieldAut n K σ) x ≠ x)
    (hcomm : (conjAut n K M * fieldAut n K σ) * conjAut n K y =
      conjAut n K y * (conjAut n K M * fieldAut n K σ)) : False := by
  classical
  have hn0 : 0 < n := by omega
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_charP_two hp hp2
  obtain ⟨hσ, T, hT⟩ := conjAut_mul_fieldAut_pow_eq_one hn hγ
  have hγ'k : gammaHat M σ ^ r ^ k = 1 := gammaHat_pow_eq_one M σ hσ hT
  obtain ⟨c', hc'⟩ := exists_scalar_of_comm hn hcomm
  have hγy : gammaHat M σ y = GeneralLinearGroup.scalar (Fin n) c' * y := by
    rw [gammaHat_apply, ← CFSG.RankThree.LinearDescent.map_eq_glAut]
    exact hc'
  have hc1 : c' = 1 := by
    have hscal : ∀ u : Kˣ, GeneralLinearGroup.scalar (Fin n) u * y =
        y * GeneralLinearGroup.scalar (Fin n) u := fun u => GeneralLinearGroup.scalar_commute u y
    have key := eq_one_of_gamma_smul (p := p) (r := r) (k := k) hp hr hrne (gammaHat M σ) hγ'k y
      (GeneralLinearGroup.scalar (Fin n) c') hyp (hscal c') hγy ?_
    · exact scalar_injective_fin hn0 (by rw [key, map_one])
    · intro hcp
      have hcp' : c' ^ p = 1 :=
        scalar_injective_fin hn0 (by rw [map_pow, hcp, map_one])
      have hfix : σ (c' : K) = c' :=
        fieldAut_apply_eq_of_pow_eq_one hp hp2 hr hrp hK σ hσ
          (by rw [← Units.val_pow_eq_pow_val, hcp', Units.val_one])
      rw [gammaHat_apply, ← CFSG.RankThree.LinearDescent.map_eq_glAut,
        GeneralLinearGroup.map_scalar]
      have : Units.map (σ : K →+* K) c' = c' := Units.ext hfix
      rw [this, ← GeneralLinearGroup.scalar_commute c' M, mul_inv_cancel_right]
  subst hc1
  have hγy' : gammaHat M σ y = y := by rw [hγy, map_one, one_mul]
  have hx := squarefree_minpoly_linEnd_of_pow_scalar hpK (y := y) 1
    (by rw [hyp, map_one])
  have hab : ∀ e e' : GL (Fin n) K, conjAut n K e ∈ E → conjAut n K e' ∈ E → e * e' = e' * e := by
    by_cases hK4 : 4 ≤ Nat.card K
    · intro e e' he he'
      rcases autFix_not_isSolvable_or_centralizer_commute hx hK4 with h | h
      · exact absurd hsolv h
      · exact h e (Subgroup.mem_centralizer_singleton_iff.2 (hC e he).symm) e'
          (Subgroup.mem_centralizer_singleton_iff.2 (hC e' he').symm)
    · intro e e' he he'
      have h2 : Nat.card K = 2 := by
        have h1 : 1 < Nat.card K := Finite.one_lt_card
        have : 2 ^ f < 4 := by rw [← hK]; omega
        have hf : f ≤ 1 := by
          by_contra h
          push Not at h
          have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h
          omega
        interval_cases f
        · simp at hK; omega
        · simpa using hK
      have hcomm' : conjAut n K e * conjAut n K e' = conjAut n K e' * conjAut n K e :=
        congrArg Subtype.val (hEc.is_comm.comm (⟨_, he⟩ : ↥E) ⟨_, he'⟩)
      have hker : conjAut n K (e * e' * (e' * e)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_inv, map_mul, hcomm', mul_inv_cancel]
      obtain ⟨u, hu⟩ := exists_scalar_of_conjAut_eq_one hn hker
      have hu1 : u = 1 := by
        have : Fintype K := Fintype.ofFinite K
        have hcK : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, h2]
        have h0 := FiniteField.pow_card_sub_one_eq_one (u : K) u.ne_zero
        rw [hcK] at h0
        exact Units.ext (by simpa using h0)
      rw [hu1, map_one] at hu
      have := mul_inv_eq_one.1 hu.symm
      exact this
  have hfz : ∀ v, semiMap M σ (linEnd y v) = linEnd y (semiMap M σ v) := by
    intro v
    have := semiMap_gammaHat M σ y v
    rw [hγy'] at this
    exact this
  have hzp : (linEnd y) ^ p = 1 := by
    have h1 := aeval_linEnd_X_pow_sub_C (y := y) 1 (by rw [hyp, map_one])
    simpa [sub_eq_zero] using h1
  have hz : ∀ e : GL (Fin n) K, conjAut n K e ∈ E →
      Commute (linEnd y) ((glRep n K e : (Fin n → K) ≃ₗ[K] (Fin n → K)) : Module.End K (Fin n → K)) := by
    intro e he
    refine LinearMap.ext fun v => ?_
    have h1 := hC e he
    have h2 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) *ᵥ v) h1
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec] at h2
    change linEnd y (glRep n K e v) = glRep n K e (linEnd y v)
    simpa [linEnd, glRep_apply] using h2
  obtain ⟨h, hmem, -, h5⟩ := exists_Omega_big_factor (K := K) (V := Fin n → K) (H := GL (Fin n) K)
    (S := MulAut (projectiveSL n K)) (f := f) (p := p) (r := r) (k := k) hK hp hp2 hr hr5 hrp hr2
    hr3 hrne (conjAut n K) (conjAut_ker_le_center hn) (isCyclic_conjAut_ker hn) E hEc hEp hcard hπE
    hab (glRep n K) glRep_injective (linEnd y) hzp hz (MulAut.conj (conjAut n K M * fieldAut n K σ))
    (gammaHat M σ) (fun e => conjAut_gammaHat M σ e) (by rw [← map_pow, hγ, map_one]) hγ'k hγE hnt
    σ hσ (semiMap M σ) (semiMap_bijective _ _) (fun e v => semiMap_gammaHat M σ e v) hfz
  exact not_isSolvable_autFix_of_mult_three hx ⟨h, hmem⟩ (le_trans (by norm_num) h5) hsolv

theorem conjAut_scalar (u : Kˣ) : conjAut n K (GeneralLinearGroup.scalar (Fin n) u) = 1 :=
  LinearFlag.conjAut_scalar u

theorem lin_cell_false [Finite K] [CharP K 2] (hn : 3 ≤ n) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrp : ¬ r ∣ p - 1) (hr2 : ¬ r ∣ p ^ 2 - 1) (hr3 : ¬ r ∣ p ^ 3 - 1) (hrne : r ≠ p)
    (Ē : Subgroup (projectiveSL n K)) (hE : CFSG.Open.IsElemAbelian p Ē)
    (hcard : Nat.card Ē = p ^ 4) (ζ γ : MulAut (projectiveSL n K))
    (hζp : ζ ^ p = 1) (hζE : ∀ x ∈ Ē, ζ x = x) (hsolv : Group.IsSolvable ↥(autFix ζ))
    (hγ : ∃ k : ℕ, γ ^ r ^ k = 1) (hγE : ∀ x ∈ Ē, γ x ∈ Ē) (hcomm : γ * ζ = ζ * γ)
    (hnt : ∃ x ∈ Ē, γ x ≠ x) : False := by
  classical
  obtain ⟨k, hk⟩ := hγ
  have hrodd : Odd (r ^ k) := (hr.odd_of_ne_two (by omega)).pow
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hγmem := mem_semilinearAutGroup_of_pow_eq_one hn hrodd hk
  have hζmem := mem_semilinearAutGroup_of_pow_eq_one hn hpodd hζp
  by_cases hD : ζ ∈ linearAutGroup n K
  swap
  · exact lin_outer_false hn hf hK hp hp2 hζmem hD hζp hsolv
  obtain ⟨y, rfl, c, hc⟩ := exists_conjAut_of_mem_linearAutGroup hn hD hζp
  obtain ⟨M, σ, rfl⟩ := mem_semilinearAutGroup_iff.1 hγmem
  have hEc : IsMulCommutative Ē := hE.1
  have hEp : ∀ x ∈ Ē, x ^ p = 1 := hE.2
  have hyp : y ^ p = GeneralLinearGroup.scalar (Fin n) c := hc.symm
  obtain ⟨hEc', hEp', hcard', hπE, hγE', hnt'⟩ :=
    map_conj_data hn Ē hEc hEp hcard (conjAut n K M * fieldAut n K σ) hγE hnt
  by_cases hpow : ∃ b : K, b ^ p = (c : K)
  · obtain ⟨b, hb⟩ := hpow
    have hb0 : b ≠ 0 := by
      rintro rfl
      apply c.ne_zero
      rw [← hb, zero_pow hp.ne_zero]
    let u : Kˣ := Units.mk0 b hb0
    have hup : u ^ p = c := Units.ext (by simpa [u] using hb)
    set y' : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) u⁻¹ * y with hy'
    have hy'c : conjAut n K y' = conjAut n K y := by
      rw [hy', map_mul, conjAut_scalar, one_mul]
    have hy'p : y' ^ p = 1 := by
      rw [hy', Commute.mul_pow (GeneralLinearGroup.scalar_commute _ _), hyp, ← map_pow, ← map_mul,
        inv_pow, hup, inv_mul_cancel, map_one]
    have hζE' : ∀ x ∈ Ē, conjAut n K y' x = x := by
      rw [hy'c]
      exact hζE
    have hcomm' := hcomm
    rw [← hy'c] at hcomm'
    have hC := lin_step3 hn hp hr hrp hr2 hr3 hrne Ē hEc hEp hcard y' M σ 1
      (by rw [hy'p, map_one]) hζE' hk hγE hcomm' hnt
    exact lin_caseI_false hn hK hp hp2 hr hr5 hrp hr2 hr3 hrne _ hEc' hEp' hcard' hπE y' M σ hy'p
      (by rw [hy'c]; exact hsolv) hC hk hγE' hnt' hcomm'
  · push Not at hpow
    have hC := lin_step3 hn hp hr hrp hr2 hr3 hrne Ē hEc hEp hcard y M σ c hyp hζE hk hγE hcomm hnt
    refine lin_caseII_false hn hp hp2 _ hEp' hcard' y c hyp hpow hsolv fun x hx => ?_
    obtain ⟨e, he⟩ := hπE x hx
    exact ⟨e, he, hC e (he ▸ hx)⟩

end Step3

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellLin
