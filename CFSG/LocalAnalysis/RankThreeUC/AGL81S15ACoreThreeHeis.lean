module

public import CFSG.LocalAnalysis.SectionRank.OddCover.ThreeRank
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.ACore

open CFSG.Open CFSG.SectionRank.OddCover

variable {K : Type} [Field K]

theorem three_dvd_of_cycGL_zpow_eq_diagHom {k : ℤ} {e : Fin 3 → Kˣ}
    (h : (cycGL : GL (Fin 3) K) ^ k = diagHom 3 e) : (3 : ℤ) ∣ k := by
  have hk : (cycGL : GL (Fin 3) K) ^ k = cycGL ^ (k % 3).toNat := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))]
    have h' := zpow_mod_orderOf (cycGL : GL (Fin 3) K) k
    rw [orderOf_cycGL] at h'
    exact h'.symm
  rw [hk] at h
  have hlt : (k % 3).toNat < 3 := by omega
  interval_cases hj : (k % 3).toNat
  · omega
  · have := congrFun (congrFun (congrArg (fun g : GL (Fin 3) K =>
      (g : Matrix (Fin 3) (Fin 3) K)) h) 1) 0
    simp [coe_cycGL, cycMat, coe_diagHom] at this
  · have := congrFun (congrFun (congrArg (fun g : GL (Fin 3) K =>
      (g : Matrix (Fin 3) (Fin 3) K)) h) 2) 0
    simp [coe_cycGL, cycMat, coe_diagHom, sq, Matrix.mul_apply, Fin.sum_univ_three] at this

theorem cycGL_conj_diagHom_cubeRoot {ω : Kˣ} (h3 : ω ^ 3 = 1) :
    cycGL * diagHom 3 ![1, ω, ω⁻¹] * cycGL⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) ω⁻¹ * diagHom 3 ![1, ω, ω⁻¹] := by
  rw [cycGL_conj_diagHom, scalar_eq_diagHom, ← map_mul]
  congr 1
  funext i
  have h2 : ω⁻¹ * ω⁻¹ = ω := by
    have h' : ω * ω * ω = 1 := by rw [← pow_three']; exact h3
    calc ω⁻¹ * ω⁻¹ = ω⁻¹ * ω⁻¹ * (ω * ω * ω) := by rw [h', mul_one]
      _ = ω := by group
  fin_cases i
  · simp
  · simp
  · simp [h2]

theorem two_le_pRank_statedProj_of_monomialData [Finite K] {H : Subgroup (GL (Fin 3) K)}
    {M : Subgroup Kˣ} (hH : MonomialData H M) {ω : Kˣ} (hωM : ω ∈ M) (hω : orderOf ω = 3) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj H)) := by
  have h3 : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω
  have hdH : diagHom 3 ![1, ω, ω⁻¹] ∈ H := hH.diag_mem _ (fun i => by
    fin_cases i
    · exact M.one_mem
    · exact hωM
    · exact M.inv_mem hωM) (by simp)
  obtain ⟨d, hd⟩ : ∃ d : H, (d : GL (Fin 3) K) = diagHom 3 ![1, ω, ω⁻¹] := ⟨⟨_, hdH⟩, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : H, (c : GL (Fin 3) K) = cycGL := ⟨⟨_, hH.cyc_mem⟩, rfl⟩
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
  refine CFSG.two_le_pRank_of_commute_independent (e₁ := (d : StatedProj H))
    (e₂ := (c : StatedProj H)) Nat.prime_three ?_ ?_ ?_ ?_
  ·
    show (d : StatedProj H) * c = c * d
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    refine ⟨ω⁻¹, ?_⟩
    have hcd : (cycGL : GL (Fin 3) K) * diagHom 3 ![1, ω, ω⁻¹] =
        Matrix.GeneralLinearGroup.scalar (Fin 3) ω⁻¹ * diagHom 3 ![1, ω, ω⁻¹] * cycGL := by
      rw [← cycGL_conj_diagHom_cubeRoot h3]
      group
    have hs := (scalar_commute ω⁻¹ (diagHom 3 ![1, ω, ω⁻¹] * cycGL)).eq
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_mul, hd, hc, hcd,
      mul_assoc, hs, inv_mul_cancel_left]
  ·
    have hd3 : d ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hd, Subgroup.coe_one, ← map_pow, ← map_one (diagHom (K := K) 3)]
      congr 1
      funext i
      fin_cases i <;> simp [h3, inv_pow]
    rw [← QuotientGroup.mk_pow, hd3, QuotientGroup.mk_one]
  ·
    have hc3 : c ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hc, Subgroup.coe_one, cycGL_pow_three]
    rw [← QuotientGroup.mk_pow, hc3, QuotientGroup.mk_one]
  ·
    intro i j hij
    rw [← QuotientGroup.mk_zpow, ← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hij
    obtain ⟨z, hz⟩ := hij
    rw [Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_zpow, hd, hc] at hz
    have hcj : (cycGL : GL (Fin 3) K) ^ j =
        diagHom 3 ((![1, ω, ω⁻¹] ^ i)⁻¹ * fun _ => z) := by
      rw [map_mul, map_inv, map_zpow, ← scalar_eq_diagHom z, hz, inv_mul_cancel_left]
    obtain ⟨k, rfl⟩ := three_dvd_of_cycGL_zpow_eq_diagHom hcj
    rw [zpow_mul, zpow_ofNat, cycGL_pow_three, one_zpow, mul_one, scalar_eq_diagHom,
      ← map_zpow] at hz
    have hfun := diagHom_injective 3 hz
    have e0 := congrFun hfun 0
    have e1 := congrFun hfun 1
    simp only [Pi.pow_apply, Matrix.cons_val_zero, Matrix.cons_val_one, one_zpow] at e0 e1
    have hdvd := orderOf_dvd_iff_zpow_eq_one.2 (e1.symm.trans e0)
    rw [hω] at hdvd
    exact ⟨by exact_mod_cast hdvd, by exact_mod_cast dvd_mul_right (3 : ℤ) k⟩

end CFSG.LocalAnalysis.RankThreeUC.S15.ACore
