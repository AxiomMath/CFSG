module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieU5

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open Matrix CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.Steinberg CFSG.LieType.BorelTits
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem

variable {F : Type} [Field F] [Finite F] [CharP F 2]

include F in
theorem center_su_five_eq_bot (hF : Nat.card F = (2 ^ 1) ^ 2) :
    Subgroup.center (SU (unitaryInvolution F 2 1) 5) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨u, hu⟩ := exists_scalar_eq_mat_of_mem_center hF (by norm_num) (by simp) hz
  have hdet := z.2.1
  have hunit := z.2.2
  have h5 : u ^ 5 = 1 := by
    have : ((z : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = Matrix.scalar (Fin 5) u := hu
    rw [this, Matrix.scalar_apply, Matrix.det_diagonal] at hdet
    simpa using hdet
  have h3 : u ^ 3 = 1 := by
    have hz' : ((z : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = u • (1 : Matrix (Fin 5) (Fin 5) F) := by
      have hm : ((z : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) =
          mat (unitaryInvolution F 2 1) 5 z := rfl
      rw [hm, hu]
      ext a b
      simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
    rw [hz'] at hunit
    have hc : conjTr (unitaryInvolution F 2 1) (u • (1 : Matrix (Fin 5) (Fin 5) F)) =
        (unitaryInvolution F 2 1 u) • (1 : Matrix (Fin 5) (Fin 5) F) := by
      ext a b
      by_cases hab : a = b <;> simp [conjTr, Matrix.one_apply, eq_comm, hab]
    rw [hc, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, smul_smul] at hunit
    have h := congrFun (congrFun hunit ⟨0, by norm_num⟩) ⟨4, by norm_num⟩
    simp [antidiag, unitaryInvolution_apply] at h
    have h' : u * u ^ 2 = 1 := by simpa [frobenius_def] using h
    calc u ^ 3 = u * u ^ 2 := by ring
      _ = 1 := h'
  have h2 : u ^ 2 = 1 := by
    have : u ^ 5 = u ^ 3 * u ^ 2 := by ring
    rw [h5, h3, one_mul] at this
    exact this.symm
  have hu1 : u = 1 := by
    have : u ^ 3 = u * u ^ 2 := by ring
    rw [h3, h2, mul_one] at this
    exact this.symm
  apply Subtype.ext
  apply Units.ext
  change mat (unitaryInvolution F 2 1) 5 z = mat (unitaryInvolution F 2 1) 5 1
  rw [hu, hu1, map_one]
  simp

theorem exists_last_node_le (hF : Nat.card F = (2 ^ 1) ^ 2) {n : ℕ} {Y : Type} [Group Y]
    [Finite Y] {ζ : traceZero (unitaryInvolution F 2 1)}
    {π' : SU (unitaryInvolution F 2 1) n →* Y}
    (hQ : BorelQuotient (rootDatum hF n)
      (levelWeyl (unitaryInvolution_involutive hF) ζ) (levelTorus (unitaryInvolution F 2 1))
      π' (Nat.card F - 1)) (J : Subgroup Y)
    (hBJ : ∀ b ∈ borel (rootDatum hF n) (levelTorus (unitaryInvolution F 2 1)), π' b ∈ J)
    (hne : J.comap π' ≠ borel (rootDatum hF n) (levelTorus (unitaryInvolution F 2 1)))
    (hperf : ∀ V : Subgroup Y, V ≤ J → ⁅V, V⁆ = V → Nat.Coprime 3 (Nat.card V)) :
    ∃ k : Fin (n / 2), ¬ k.val + 1 < n / 2 ∧
      rankOne (rootGroup (unitaryInvolution F 2 1) (unitaryInvolution_involutive hF) n) k ≤
        J.comap π' := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBA : borel (rootDatum hF n) (levelTorus (unitaryInvolution F 2 1)) ≤ J.comap π' :=
    fun b hb => hBJ b hb
  obtain ⟨i, hi⟩ := exists_negRoot_le_of_borel_lt hQ.ct hQ.extras hBA hne
  have hroot : ∀ i : Fin (rootDatum hF n).rank,
      (Pi.single i 1 : Fin (rootDatum hF n).rank → ℤ) ∈ (rootDatum hF n).roots := fun i =>
    (RootSystem.ofCartan (rootDatum hF n).isFiniteType (rootDatum hF n).divisible).single_mem i
  have hLJ : rankOne (rootDatum hF n).rootGroup i ≤ J.comap π' :=
    sup_le ((rootGroup_le_borel (hroot i) (ht_single_pos i)).trans hBA) hi
  refine ⟨i, ?_, hLJ⟩
  intro hk
  obtain ⟨x, hx, y, hy, h3, c, hc⟩ := hasOrderThree_su hF i
  have hxyL : x * y ∈ rankOne (rootDatum hF n).rootGroup i :=
    mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hy)
  have hxyc : x * y ∉ Subgroup.center (SU (unitaryInvolution F 2 1) n) := fun hcen =>
    hc (Subgroup.mem_center_iff.1 hcen c).symm
  have hp := commutator_eq_self_of_isPerfect (su_short_isPerfect hF hk)
  have hord : orderOf (π' (x * y)) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, h3, map_one]) fun h1 => hxyc (hQ.ker_central _ h1)
  have hdvd : 3 ∣ Nat.card ((rankOne (rootDatum hF n).rootGroup i).map π') := by
    have := Subgroup.orderOf_dvd_natCard ((rankOne (rootDatum hF n).rootGroup i).map π')
      ⟨x * y, hxyL, rfl⟩
    rwa [hord] at this
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
    (hperf _ (Subgroup.map_le_iff_le_comap.2 hLJ) (by rw [← Subgroup.map_commutator, hp])) hdvd

theorem three_le_pRank_su_five (hF : Nat.card F = (2 ^ 1) ^ 2) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedSU 5 (2 ^ 1) F)) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJne : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y))
    (hperf : ∀ V : Subgroup Y, V ≤ J → ⁅V, V⁆ = V → Nat.Coprime 3 (Nat.card V)) :
    3 ≤ CFSG.Open.pRank 3 J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hB := borelQuotient_su hF (by norm_num) ζ hζ e
  obtain ⟨π', hπ's, hπ'k, hT⟩ := hB.exists_conj_eq T
  have hQ : BorelQuotient (rootDatum hF 5)
      (levelWeyl (unitaryInvolution_involutive hF) ζ) (levelTorus (unitaryInvolution F 2 1))
      π' (Nat.card F - 1) :=
    { ct := hB.ct, extras := hB.extras, pGroup := hB.pGroup, surj := hπ's, odd := hB.odd,
      torus_pow := hB.torus_pow, ker_central := fun z hz => hB.ker_central z (hπ'k ▸ hz),
      ker_pow := fun z hz => hB.ker_pow z (hπ'k ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hBJ : ∀ b ∈ borel (rootDatum hF 5) (levelTorus (unitaryInvolution F 2 1)), π' b ∈ J :=
    fun b hb => hNJ (by rw [hNπ]; exact ⟨b, hb, rfl⟩)
  have hne : J.comap π' ≠ borel (rootDatum hF 5) (levelTorus (unitaryInvolution F 2 1)) := by
    intro he
    apply hJne
    rw [hNπ, ← he, Subgroup.map_comap_eq_self_of_surjective hπ's]
  obtain ⟨k, hk, hLJ⟩ := exists_last_node_le hF hQ J hBJ hne hperf
  have hinj : Function.Injective π' := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hzc := hQ.ker_central z hz
    rw [center_su_five_eq_bot hF] at hzc
    exact hzc
  exact three_le_pRank_of_su_odd_node hF (by norm_num) (by decide) hk π' hinj J hBJ hLJ

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
