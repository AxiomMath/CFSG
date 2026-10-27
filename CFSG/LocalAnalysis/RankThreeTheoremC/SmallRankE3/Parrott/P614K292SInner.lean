module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsForm
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsLifts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K292S

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts (centerDescend)
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

theorem exists_cube_of_pow_two_pow {G : Type*} [CommGroup G] {u w : G} {n : ℕ}
    (h : u ^ (2 ^ n) = w ^ 3) : ∃ v : G, v ^ 3 = u := by
  have h4 : 4 ^ n % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have hk : 3 * (4 ^ n / 3) + 1 = 4 ^ n := by
    have := Nat.div_add_mod (4 ^ n) 3
    rw [h4] at this
    exact this
  set k := 4 ^ n / 3
  have hu : u ^ (4 ^ n) = (w ^ (2 ^ n)) ^ 3 := by
    rw [show (4 : ℕ) ^ n = 2 ^ n * 2 ^ n by rw [← mul_pow]; norm_num, pow_mul, h, ← pow_mul,
      ← pow_mul, mul_comm]
  refine ⟨w ^ (2 ^ n) * (u ^ k)⁻¹, ?_⟩
  rw [mul_pow, inv_pow, ← hu, ← hk, pow_add, pow_one, ← pow_mul, mul_comm k 3,
    mul_comm (u ^ (3 * k)) u, mul_assoc, mul_inv_cancel, mul_one]

variable {X : Type} [Group X] {L : Subgroup X} {π : Bool} {p f : ℕ} {K : Type} [Field K]
  {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L}

theorem mem_of_isLiftAt_two [L.Normal] (M : LModel L π p f K ν)
    (hcent : centralizer (L : Set X) = CFSG.pCore 3 X) {t : X} (ht : IsPGroup 2 (zpowers t))
    {c : GL (Fin 3) K} (hc : IsLiftAt ν t c) : t ∈ L := by
  obtain ⟨n, hn⟩ := ht ⟨t, mem_zpowers t⟩
  have htn : t ^ (2 ^ n) = 1 := by
    have h1 := congrArg Subtype.val hn
    simpa using h1
  have hz : c ^ (2 ^ n) ∈ zPi π 3 (p ^ f) K := by
    have h1 := hc.pow M (2 ^ n)
    rw [htn] at h1
    have h2 := (isLiftAt_one_of_mem_centralizer (ν := ν)
      (one_mem (centralizer (L : Set X)))).inv_mul_mem_zPi M h1
    rwa [inv_one, one_mul] at h2
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau M.piField M.modThree
  obtain ⟨ξ, hξ, hξc⟩ := exists_scalar_of_mem_zPi M.piField M.modThree hτ hτ1 hz
  have hdet : detRoot M.piField hc.mem ^ (2 ^ n) =
      (⟨ξ, hξ⟩ : ↥(rootsOfUnity (qSubPi π (p ^ f)) K)) ^ 3 := by
    apply Subtype.ext
    simp only [detRoot, SubgroupClass.coe_pow]
    rw [← map_pow, ← hξc, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
  obtain ⟨μ, hμ⟩ := exists_cube_of_pow_two_pow hdet
  obtain ⟨l, hl, hlc⟩ := hc.exists_of_isInnerMat M (isInnerMat_of_detRoot M.piField hc.mem hμ)
  rw [hcent] at hlc
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 3) (G := X)) ⟨_, hlc⟩
  have hm' : (l⁻¹ * t) ^ (3 ^ m) = 1 := by
    have h1 := congrArg Subtype.val hm
    simpa using h1
  have hl1 : (QuotientGroup.mk' L) l = 1 := (QuotientGroup.eq_one_iff l).2 hl
  have hq : (QuotientGroup.mk' L) t = (QuotientGroup.mk' L) (l⁻¹ * t) := by
    rw [map_mul, map_inv, hl1, inv_one, one_mul]
  have h2 : orderOf ((QuotientGroup.mk' L) t) ∣ 2 ^ n :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, htn, map_one])
  have h3 : orderOf ((QuotientGroup.mk' L) t) ∣ 3 ^ m :=
    orderOf_dvd_of_pow_eq_one (by rw [hq, ← map_pow, hm', map_one])
  have h1 : orderOf ((QuotientGroup.mk' L) t) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow n m (by norm_num)) h2 h3
  rw [orderOf_eq_one_iff] at h1
  exact (QuotientGroup.eq_one_iff t).1 h1

theorem exists_isLiftAt_commutator [L.Normal] (M : LModel L π p f K ν) (g h : X) :
    ∃ c : GL (Fin 3) K, IsLiftAt ν (g * h * g⁻¹ * h⁻¹) c := by
  obtain ⟨pkg⟩ := exists_etaPkg M.piField M.two_lt
  set e := M.barEquiv.symm.trans pkg.η with he
  set τ : X →* MulAut pkg.M := (MulAut.congr e).toMonoidHom.comp
    ((centerDescend ↥L).comp (MulAut.conjNormal : X →* MulAut ↥L)) with hτ
  set w := g * h * g⁻¹ * h⁻¹ with hw
  have hκ : τ w ∈ pkg.P.inndiag := by
    refine pkg.good.down ?_
    rw [hw, ← commutatorElement_def, map_commutatorElement, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  obtain ⟨H, hH, hHeq⟩ := M.exists_conjBy_of_mem_inndiag pkg hκ
  have hτ' : MulAut.congr pkg.η.symm (τ w) =
      MulAut.congr M.barEquiv.symm (centerDescend ↥L (MulAut.conjNormal w)) := by
    show MulAut.congr pkg.η.symm
      (MulAut.congr e (centerDescend ↥L (MulAut.conjNormal w))) = _
    rw [he, congr_trans', congr_symm_congr]
  rw [hτ'] at hHeq
  refine ⟨H, hH, fun s t ht => ?_⟩
  rw [M.conj_eq_of_congr hHeq s]
  congr 2
  exact Subtype.ext ((M.coe_conjBy hH s).trans ht.symm)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K292S
