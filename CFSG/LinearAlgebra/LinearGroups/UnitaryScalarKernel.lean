module

public import CFSG.LieType.Universal.Unitary.Comparison

public section

namespace CFSG.LinearGroups

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

theorem scalar_mem_statedSU_iff {K : Type} [Field K] {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (hn : 1 ≤ n) (c : Kˣ) :
    GeneralLinearGroup.scalar (Fin n) c ∈ StatedSU n (p ^ f) K ↔
      c ^ n = 1 ∧ c ^ (p ^ f + 1) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (pow_ne_zero _ hp.ne_zero))
  have := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (f := 2 * f)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm])
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  rw [← SUid_eq_statedSU hK n, mem_SUid, GeneralLinearGroup.coe_scalar]
  have hconj : conjTr (unitaryInvolution K p f) (Matrix.scalar (Fin n) (c : K)) =
      Matrix.scalar (Fin n) (unitaryInvolution K p f c) := by
    ext i j
    simp [conjTr, Matrix.scalar_apply, Matrix.diagonal_apply, eq_comm]
  have hdet : (Matrix.scalar (Fin n) (c : K)).det = (c : K) ^ n := by
    rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  rw [hconj, ← map_mul, hdet, ← map_one (Matrix.scalar (Fin n)),
    Matrix.scalar_inj, unitaryInvolution_apply, ← pow_succ,
    Units.ext_iff, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
    Units.val_one]

theorem card_rootsOfUnity_of_dvd {K : Type*} [Field K] [Finite K] {d : ℕ} [NeZero d]
    (hd : d ∣ Nat.card K - 1) : Nat.card (rootsOfUnity d K) = d := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, Fintype.card_units,
      Nat.card_eq_fintype_card]
  have hprim : IsPrimitiveRoot g (Nat.card K - 1) := hord ▸ IsPrimitiveRoot.orderOf g
  obtain ⟨m, hm⟩ := hd
  have hK1 : 0 < Nat.card K - 1 := by
    have := Finite.one_lt_card (α := K)
    omega
  have hm0 : m ≠ 0 := by
    rintro rfl
    omega
  have hdm := hprim.pow_of_dvd hm0 (Dvd.intro_left d hm.symm)
  rw [hm, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)] at hdm
  exact (IsPrimitiveRoot.coe_units_iff.mpr hdm).card_rootsOfUnity

theorem unitary_scalar_kernel {K : Type} [Field K] {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (hn : 1 ≤ n) :
    (StatedSU n (p ^ f) K : Set (GL (Fin n) K)) =
      {A : GL (Fin n) K | (A : Matrix (Fin n) (Fin n) K).det = 1 ∧
      ((A : Matrix (Fin n) (Fin n) K).map (· ^ p ^ f))ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1} ∧
    (∀ c : Kˣ, GeneralLinearGroup.scalar (Fin n) c ∈ StatedSU n (p ^ f) K ↔
      c ^ n = 1 ∧ c ^ (p ^ f + 1) = 1) ∧
      Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K)) =
        Nat.gcd n (p ^ f + 1) := by
  have hmem := scalar_mem_statedSU_iff hp hK hn
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (pow_ne_zero _ hp.ne_zero))
  have hset : (StatedSU n (p ^ f) K : Set (GL (Fin n) K)) = {A : GL (Fin n) K |
      (A : Matrix (Fin n) (Fin n) K).det = 1 ∧
        ((A : Matrix (Fin n) (Fin n) K).map (· ^ p ^ f))ᵀ * (A : Matrix (Fin n) (Fin n) K) =
          1} := by
    have : Fact p.Prime := ⟨hp⟩
    have := Fintype.ofFinite K
    have : CharP K p := charP_of_card_eq_prime_pow (f := 2 * f)
      (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm])
    ext A
    rw [SetLike.mem_coe, ← SUid_eq_statedSU hK n, mem_SUid]
    have hσ : ⇑(unitaryInvolution K p f) = (· ^ p ^ f) := funext (unitaryInvolution_apply K p f)
    simp only [conjTr, hσ, Set.mem_ofPred_eq]
  refine ⟨hset, hmem, ?_⟩
  set d := Nat.gcd n (p ^ f + 1) with hd
  have : NeZero d := ⟨Nat.gcd_ne_zero_right (Nat.succ_ne_zero _)⟩
  have hdK : d ∣ Nat.card K - 1 := by
    refine (Nat.gcd_dvd_right n (p ^ f + 1)).trans ⟨p ^ f - 1, ?_⟩
    have h1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
    rw [hK]
    zify [h1, Nat.one_le_pow 2 (p ^ f) (by omega)]
    ring
  have hroot : ∀ c : Kˣ, c ∈ rootsOfUnity d K ↔ c ^ n = 1 ∧ c ^ (p ^ f + 1) = 1 := by
    intro c
    rw [mem_rootsOfUnity, hd, pow_gcd_eq_one]
  have hinj : Function.Injective (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K) := by
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    intro c c' hcc'
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hcc'
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_inj] at this
    exact Units.ext this
  rw [← card_rootsOfUnity_of_dvd hdK]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun c : rootsOfUnity d K => (⟨⟨GeneralLinearGroup.scalar (Fin n) (c : Kˣ),
      (hmem _).mpr ((hroot _).mp c.2)⟩, ⟨(c : Kˣ), rfl⟩⟩ :
        (StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K))) ⟨?_, ?_⟩)
  · intro c c' hcc'
    exact Subtype.ext (hinj (congrArg (fun z : (StatedScalars (Fin n) K).subgroupOf
      (StatedSU n (p ^ f) K) => ((z : StatedSU n (p ^ f) K) : GL (Fin n) K)) hcc'))
  · rintro ⟨⟨g, hgSU⟩, hgZ⟩
    obtain ⟨c, hc⟩ := hgZ
    have hcg : GeneralLinearGroup.scalar (Fin n) c = g := hc
    subst hcg
    exact ⟨⟨c, (hroot c).mpr ((hmem c).mp hgSU)⟩, rfl⟩

end CFSG.LinearGroups
