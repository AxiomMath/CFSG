module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveHeisTransfer
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2
public import CFSG.LocalAnalysis.SectionRank.OddCover.LinearThree
public import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

open CFSG.SectionRank.OddCover
open scoped commutatorElement

theorem exists_cube_root_of_unity (K : Type) [Field K] [Finite K] (h : 3 ∣ Nat.card K - 1) :
    ∃ ω : K, ω ≠ 1 ∧ ω ^ 3 = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcard : Nat.card Kˣ = Nat.card K - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  have h3 : 3 ∣ Nat.card Kˣ := hcard ▸ h
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h3
  refine ⟨(g : K), fun h1 => ?_, ?_⟩
  · have : g = 1 := Units.ext h1
    rw [this, orderOf_one] at hg
    omega
  · have := pow_orderOf_eq_one g
    rw [hg] at this
    exact congrArg Units.val this |>.trans (by simp)

theorem linesData_PSL2_25 {Q : Type} [Group Q]
    (hQ : CFSG.Open.StatedClassicalModel Q .PSL 2 5 2) : LinesData Q := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e0⟩⟩ := hQ
  let e : Q ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 K) := e0
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hK' : Nat.card K = 5 ^ 2 := hK
  obtain ⟨-, -, hcardS, hinj, -, hconj, -⟩ :=
    odd_psl_two_sylow_data (p := 5) (f := 2) (by norm_num) hK'
  have hchar : CharP K 5 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK'])
  obtain ⟨ω, hω1, hω3⟩ := exists_cube_root_of_unity K (by rw [hK']; norm_num)
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω3
  have hω2 : ω ^ 2 + ω + 1 = 0 := by
    have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
      have : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
      rw [this, hω3, sub_self]
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hω1)
  let u : Kˣ := Units.mk0 (ω ^ 2) (pow_ne_zero 2 hω0)
  have hu : ((u : Kˣ) : K) ^ 2 = ω := by
    show (ω ^ 2) ^ 2 = ω
    calc (ω ^ 2) ^ 2 = ω * ω ^ 3 := by ring
      _ = ω := by rw [hω3, mul_one]
  have hone : (Multiplicative.ofAdd (1 : K)) ≠ 1 := fun h => one_ne_zero (ofAdd_eq_one.mp h)
  refine ⟨e.symm (stU K (Multiplicative.ofAdd 1)), e.symm (stU K (Multiplicative.ofAdd ω)),
    e.symm (stD u), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h1 : stU K (Multiplicative.ofAdd 1) = 1 := by
      have := e.symm.injective (h.trans (map_one e.symm).symm)
      exact this
    exact hone (hinj (h1.trans (map_one (stU K)).symm))
  · rw [← map_pow, ← map_pow, ← ofAdd_nsmul]
    have h5 : (5 : ℕ) • (1 : K) = 0 := by
      rw [nsmul_eq_mul, mul_one]
      exact CharP.cast_eq_zero K 5
    rw [h5, ofAdd_zero, map_one, map_one]
  · exact ((Commute.all _ _).map (stU K)).map e.symm
  · rw [← map_inv, ← map_mul, ← map_mul, hconj u 1, hu, mul_one]
  · have key : ((u : Kˣ) : K) ^ 2 * ω = ω ^ 2 := by rw [hu]; ring
    rw [← map_inv, ← map_mul, ← map_mul, hconj u ω, key, ← map_mul, ← map_mul, ← map_inv,
      ← map_inv, ← ofAdd_add, ← ofAdd_neg]
    congr 3
    linear_combination hω2
  · have hcard : Nat.card Q = 5 ^ 2 * (((5 ^ 2) ^ 2 - 1) / 2) := by
      rw [Nat.card_congr e.toEquiv]
      exact hcardS
    rw [hcard]
    norm_num

open CFSG.Assembly.LowTwoRank in
theorem u3_not_mem_scalars {K : Type} [Field K] :
    ((u3SL (0 : K) 0 1 : StatedSL 3 K) : GL (Fin 3) K) ∉ StatedScalars (Fin 3) K := by
  rintro ⟨r, hr⟩
  have h := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 2) hr
  simp [coe_u3SL, u3Mat, Matrix.GeneralLinearGroup.scalar] at h

open CFSG.Assembly.LowTwoRank in
theorem heisData_PSL3_5 {Q : Type} [Group Q]
    (hQ : CFSG.Open.StatedClassicalModel Q .PSL 3 5 1) : HeisData Q := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e0⟩⟩ := hQ
  let e : Q ≃* StatedProj (StatedSL 3 K) := e0
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hK' : Nat.card K = 5 := by simpa using hK
  let π : StatedSL 3 K →* StatedProj (StatedSL 3 K) :=
    QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K))
  have hz1 : ⁅π slX, π slY⁆ ≠ 1 := by
    rw [← map_commutatorElement, commutator_slX_slY]
    intro h
    have h' : (QuotientGroup.mk (u3SL (0 : K) 0 1 : StatedSL 3 K) :
        StatedProj (StatedSL 3 K)) = 1 := h
    exact u3_not_mem_scalars ((QuotientGroup.eq_one_iff (u3SL (0 : K) 0 1 : StatedSL 3 K)).mp h')
  have hcard : Nat.card (StatedProj (StatedSL 3 K)) ∣ Nat.card (StatedSL 3 K) :=
    Subgroup.card_dvd_of_surjective (f := π) (QuotientGroup.mk'_surjective _)
  refine ⟨e.symm (π slY), e.symm (π slX), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, ← map_pow, slY_pow_p hK', map_one, map_one]
  · rw [← map_pow, ← map_pow, slX_pow_p hK', map_one, map_one]
  · rw [← map_commutatorElement, ← map_commutatorElement]
    exact ((commute_slZ_slY (K := K)).map π).map e.symm
  · rw [← map_commutatorElement, ← map_commutatorElement]
    exact ((commute_slZ_slX (K := K)).map π).map e.symm
  · rw [← map_commutatorElement, ← map_commutatorElement]
    intro h
    exact hz1 (e.symm.injective (h.trans (map_one e.symm).symm))
  · have hc : Nat.card Q ∣ Nat.card (StatedSL 3 K) := by
      rw [Nat.card_congr e.toEquiv]
      exact hcard
    intro h
    exact not_pow_four_dvd_card_statedSL (p := 5) hK' ((by norm_num : 5 ^ 4 ∣ 5 ^ 4).trans
      (h.trans hc) |> fun x => x)

end CFSG.CGT.PushingUpLit.CGT6M
