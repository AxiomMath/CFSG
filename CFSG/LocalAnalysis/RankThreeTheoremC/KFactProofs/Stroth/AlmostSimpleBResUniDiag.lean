module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UnLift
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleTowerSylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

abbrev idCn (n : ℕ) (K : Type) [Field K] : Matrix (Fin n) (Fin n) K :=
  ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

section Diag

variable {ℓ f : ℕ} {K : Type} [Field K] (hU : UnitaryFieldData ℓ f K)

theorem inner_le_primeFormD {n : ℕ} :
    inner (primeFormP hU (idCn n K)) ≤ primeFormD hU (idCn n K) := fun α hα => by
  obtain ⟨s, rfl⟩ := (mem_inner_primeFormP hU (idCn n K) α).1 hα
  exact ⟨_, rfl⟩

theorem dvd_of_mem_primeFormD_not_inner {n p : ℕ} (hp : p.Prime)
    {a : MulAut (primeFormP hU (idCn n K))} (haD : a ∈ primeFormD hU (idCn n K))
    (hai : a ∉ inner (primeFormP hU (idCn n K))) (hap : a ^ p = 1) : p ∣ ℓ ^ f + 1 := by
  haveI : (inner (primeFormP hU (idCn n K))).Normal := inner_normal _
  have hIDle := inner_le_primeFormD hU (n := n)
  by_contra hq
  apply hai
  refine mem_of_pPow_eq_one_of_not_dvd_relIndex hp hIDle ?_ haD (k := 1) (by rw [pow_one]; exact hap)
  intro hd
  have hc := card_primeFormD_quotient_dvd hU (1 : GL (Fin n) K)
  have hrel : (inner (primeFormP hU (idCn n K))).relIndex (primeFormD hU (idCn n K)) =
      Nat.card (primeFormD hU (idCn n K) ⧸
        (inner (primeFormP hU (idCn n K))).subgroupOf (primeFormD hU (idCn n K))) := by
    rw [Subgroup.relIndex, Subgroup.index]
  rw [hrel] at hd
  exact hq (hd.trans hc)

theorem mem_inner_of_mem_primeFormD_of_not_dvd {n p : ℕ} (hn : 3 ≤ n) (hp : p.Prime)
    (hpn : ¬ p ∣ n) {a : MulAut (primeFormP hU (idCn n K))}
    (haD : a ∈ primeFormD hU (idCn n K)) (hap : a ^ p = 1) :
    a ∈ inner (primeFormP hU (idCn n K)) := by
  classical
  obtain ⟨A, rfl⟩ := haD
  have hA1 : primeFormConjHom hU (idCn n K) (A ^ p) = 1 := by rw [map_pow]; exact hap
  obtain ⟨c, hcA, hcq⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.UnC.ker_u hU hn (A ^ p) hA1
  set d : Kˣ := GeneralLinearGroup.det (A : GL (Fin n) K) with hd
  have hdq : d ^ (ℓ ^ f + 1) = 1 := by
    have h1 := norm_det_eq_one hU (1 : GL (Fin n) K) A.2
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ, mul_comm, ← hU.bar_apply]
    have h2 : ((d : Kˣ) : K) = ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det := rfl
    rw [h2]
    simpa [UnitaryFieldData.norm] using h1
  have hdp : d ^ p = c ^ n := by
    apply Units.ext
    have h1 := congrArg (fun g : GL (Fin n) K =>
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det) hcA
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Matrix.det_pow,
      GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
    exact h1
  have hcop : IsCoprime (p : ℤ) (n : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn)
  obtain ⟨u, v, huv⟩ := hcop
  have huv' : (p : ℤ) * u + (n : ℤ) * v = 1 := by linarith
  let M : Subgroup Kˣ := (powMonoidHom (ℓ ^ f + 1) : Kˣ →* Kˣ).ker
  have hcM : c ∈ M := by
    rw [MonoidHom.mem_ker]
    exact hcq
  have hdM : d ∈ M := by
    rw [MonoidHom.mem_ker]
    exact hdq
  set μ : Kˣ := c ^ u * d ^ v with hμ
  have hμM : μ ∈ M := M.mul_mem (M.zpow_mem hcM u) (M.zpow_mem hdM v)
  have hμq : μ ^ (ℓ ^ f + 1) = 1 := by
    have := hμM
    rwa [MonoidHom.mem_ker] at this
  have hμn : μ ^ n = d := by
    have e1 : (c ^ u) ^ n = (c ^ n) ^ u := by
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast]
    have e2 : (d ^ v) ^ n = (d ^ n) ^ v := by
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast]
    calc μ ^ n = (c ^ u) ^ n * (d ^ v) ^ n := by rw [hμ, mul_pow]
      _ = (c ^ n) ^ u * (d ^ n) ^ v := by rw [e1, e2]
      _ = (d ^ p) ^ u * (d ^ n) ^ v := by rw [hdp]
      _ = d ^ ((p : ℤ) * u) * d ^ ((n : ℤ) * v) := by
        rw [← zpow_natCast d p, ← zpow_natCast d n, ← _root_.zpow_mul, ← _root_.zpow_mul]
      _ = d ^ ((p : ℤ) * u + (n : ℤ) * v) := by rw [_root_.zpow_add]
      _ = d := by rw [huv', zpow_one]
  have hμinvq : μ⁻¹ ^ (ℓ ^ f + 1) = 1 := by rw [inv_pow, hμq, inv_one]
  have hscal : GeneralLinearGroup.scalar (Fin n) μ⁻¹ ∈ primeFormUnitary hU (idCn n K) :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.UnC.scalar_mem_of_pow_succ_eq_one hU hμinvq
  let Z : primeFormUnitary hU (idCn n K) := ⟨_, hscal⟩
  have hZ : primeFormConjHom hU (idCn n K) Z = 1 :=
    (CFSG.GH74.GLS.Stage2.Bender.Thm1.UnC.conj_eq_one_iff hU hn Z).2 ⟨μ⁻¹, rfl⟩
  let A' : primeFormUnitary hU (idCn n K) := Z * A
  have hA'det : ((A' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
    have hdet : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = ((μ : Kˣ) : K) ^ n := by
      have : ((d : Kˣ) : K) = ((μ ^ n : Kˣ) : K) := by rw [hμn]
      rw [Units.val_pow_eq_pow_val] at this
      exact this
    have hZdet : ((Z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = ((μ⁻¹ : Kˣ) : K) ^ n := by
      change ((GeneralLinearGroup.scalar (Fin n) μ⁻¹ : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K).det = _
      simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal]
    change ((((Z : GL (Fin n) K) * (A : GL (Fin n) K) : GL (Fin n) K)) :
      Matrix (Fin n) (Fin n) K).det = 1
    rw [Units.val_mul, Matrix.det_mul, hdet, hZdet, ← mul_pow, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, one_pow]
  refine (mem_inner_primeFormP hU (idCn n K) _).2
    ⟨⟨(A' : GL (Fin n) K), (mem_gramSU_iff_unitary hU).2 ⟨A'.2, hA'det⟩⟩, ?_⟩
  change primeFormConjHom hU (idCn n K) A = primeFormConjHom hU (idCn n K) (Z * A)
  rw [map_mul, hZ, one_mul]

end Diag

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
