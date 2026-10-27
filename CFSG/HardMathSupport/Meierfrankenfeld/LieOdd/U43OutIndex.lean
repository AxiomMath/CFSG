module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inputs
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitOrder
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneUnitaryData

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open scoped Pointwise

theorem card_le_four_mul_of_index_le_eight {G : Type} [Group G] [Finite G] (N : Subgroup G)
    [N.Normal] (hidx : N.index ≤ 8) (g₀ : G) (hg₀ : g₀ * g₀ ∉ N) (B : Subgroup G)
    (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hs : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ 4 * Nat.card ↥(B ⊓ N) := by
  have hmul := Subgroup.relIndex_mul_card (H := N) (K := B)
  rw [inf_comm] at hmul
  have hdvd : N.relIndex B ∣ N.index := Subgroup.relIndex_dvd_index_of_normal N B
  have hpos : 0 < N.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have hk8 : N.relIndex B ≤ 8 := (Nat.le_of_dvd hpos hdvd).trans hidx
  have hp : IsPGroup 2 B := fun g => ⟨1, by
    have := hs g g.2
    apply Subtype.ext
    simpa [pow_two] using this⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hp
  have hkB : N.relIndex B ∣ 2 ^ j := by rw [← hj]; exact Subgroup.relIndex_dvd_card N B
  obtain ⟨i, hi, hik⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hkB
  have hk8' : N.relIndex B ≠ 8 := by
    intro h8
    have h1 : N.relIndex (N ⊔ B) = 8 := by rw [Subgroup.relIndex_sup_left]; exact h8
    have h2 := Subgroup.relIndex_mul_index (H := N) (K := N ⊔ B) le_sup_left
    have hidx8 : N.index = 8 := by
      have := Nat.le_of_dvd hpos hdvd
      omega
    rw [h1, hidx8] at h2
    have h3 : (N ⊔ B).index = 1 := by omega
    have htop : N ⊔ B = ⊤ := Subgroup.index_eq_one.1 h3
    have hmem : g₀ ∈ (N : Set G) * (B : Set G) := by
      rw [← Subgroup.normal_mul, htop]; exact Subgroup.mem_top g₀
    obtain ⟨n, hn, b, hb, rfl⟩ := hmem
    apply hg₀
    have e : n * b * (n * b) = n * (b * n * b⁻¹) * (b * b) := by group
    rw [e, hs b hb, mul_one]
    exact N.mul_mem hn (Subgroup.Normal.conj_mem inferInstance n hn b)
  have hk4 : N.relIndex B ≤ 4 := by
    rw [hik] at hk8 hk8' ⊢
    have : i ≤ 3 := by
      by_contra h3
      have : 2 ^ 4 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases i <;> simp_all
  calc Nat.card B = N.relIndex B * Nat.card ↥(B ⊓ N) := hmul.symm
    _ ≤ 4 * Nat.card ↥(B ⊓ N) := Nat.mul_le_mul_right _ hk4

section OuterModel

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {K : Type} [Field K] (h : UnitaryFieldData 3 1 K)

@[expose] noncomputable def dEntries (a : Kˣ) : HypIndex 2 0 → K :=
  torusEntries h ![a, 1] (fun k => Fin.elim0 k)

theorem dEntries_isometry (a : Kˣ) :
    ((diagonal (dEntries h a)).map h.bar)ᵀ * hypGram 2 0 K * diagonal (dEntries h a) =
      hypGram 2 0 K :=
  diagonal_torusEntries_isometry h ![a, 1] (fun k => Fin.elim0 k)

theorem det_dEntries (a : Kˣ) : (diagonal (dEntries h a)).det = (a : K) / h.bar a := by
  rw [dEntries, det_diagonal_torusEntries, torusRatio]
  simp [Fin.prod_univ_two]

theorem det_dEntries_ne_zero (a : Kˣ) : (diagonal (dEntries h a)).det ≠ 0 := by
  rw [det_dEntries]
  exact div_ne_zero a.ne_zero ((map_ne_zero h.bar).2 a.ne_zero)

@[expose] noncomputable def dA (a : Kˣ) : GL (HypIndex 2 0) K :=
  GeneralLinearGroup.mkOfDetNeZero (diagonal (dEntries h a)) (det_dEntries_ne_zero h a)

theorem dA_coe (a : Kˣ) :
    ((dA h a : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      diagonal (dEntries h a) := rfl

theorem dA_mem_unitary (a : Kˣ) : dA h a ∈ hypUnitary h 2 0 := by
  rw [mem_hypUnitary, dA_coe]
  exact dEntries_isometry h a

theorem unitary_mem_lin {A : GL (HypIndex 2 0) K} (hA : A ∈ hypUnitary h 2 0) :
    A ∈ linearSimilitudes h 2 0 :=
  mem_linearSimilitudes.2 ⟨1, one_ne_zero, map_one _, by rw [one_smul]; exact hA⟩

theorem norm_eq_one_of_scalar_mem {c : Kˣ}
    (hU : (GeneralLinearGroup.scalar (HypIndex 2 0) c : GL (HypIndex 2 0) K) ∈
      hypUnitary h 2 0) : h.norm (c : K) = 1 := by
  rw [mem_hypUnitary, GeneralLinearGroup.coe_scalar, scalar_gram] at hU
  have h2 := congrFun (congrFun hU (.inl ⟨0, by norm_num⟩)) (hypPartner (.inl ⟨0, by norm_num⟩))
  simpa [hypGram_apply] using h2

theorem linearSimAut_hypSU (s : hypSU h 2 0) :
    linearSimAut h (by norm_num : 1 ≤ 2) (Nat.zero_le 1)
      ⟨(s : GL (HypIndex 2 0) K), unitary_mem_lin h (mem_hypSU.1 s.2).1⟩ =
        MulAut.conj (hypProj h 2 0 s) := by
  ext p
  obtain ⟨g, rfl⟩ := hypProj_surjective h 2 0 p
  rw [linearSimAut_apply]
  change hypProj h 2 0 _ = hypProj h 2 0 s * hypProj h 2 0 g * (hypProj h 2 0 s)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem linearSimAut_dA_sq_not_inner (a : Kˣ) (ha : (a : K) ^ 4 ≠ 1) :
    linearSimAut h (by norm_num : 1 ≤ 2) (Nat.zero_le 1)
        ⟨dA h a, unitary_mem_lin h (dA_mem_unitary h a)⟩ *
      linearSimAut h (by norm_num : 1 ≤ 2) (Nat.zero_le 1)
        ⟨dA h a, unitary_mem_lin h (dA_mem_unitary h a)⟩ ∉
      (MulAut.conj : hypPSU h 2 0 →* MulAut (hypPSU h 2 0)).range := by
  rintro ⟨y, hy⟩
  obtain ⟨s, rfl⟩ := hypProj_surjective h 2 0 y
  have hsU : (s : GL (HypIndex 2 0) K) ∈ hypUnitary h 2 0 := (mem_hypSU.1 s.2).1
  let x : linearSimilitudes h 2 0 := ⟨dA h a, unitary_mem_lin h (dA_mem_unitary h a)⟩
  let xs : linearSimilitudes h 2 0 := ⟨(s : GL (HypIndex 2 0) K), unitary_mem_lin h hsU⟩
  have h1 : linearSimAut h (by norm_num : 1 ≤ 2) (Nat.zero_le 1) (x * x * xs⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, linearSimAut_hypSU, hy, mul_inv_cancel]
  obtain ⟨c, hc⟩ := (linearSimAut_eq_one_iff h (by norm_num : 1 ≤ 2) (Nat.zero_le 1)
    (by norm_num) _).1 h1
  have hc' : (dA h a) * (dA h a) * (s : GL (HypIndex 2 0) K)⁻¹ =
      GeneralLinearGroup.scalar (HypIndex 2 0) c := hc
  have hU : (GeneralLinearGroup.scalar (HypIndex 2 0) c : GL (HypIndex 2 0) K) ∈
      hypUnitary h 2 0 := by
    rw [← hc']
    exact mul_mem (mul_mem (dA_mem_unitary h a) (dA_mem_unitary h a)) (inv_mem hsU)
  have hN := norm_eq_one_of_scalar_mem h hU
  have hc4 : (c : K) ^ 4 = 1 := by
    have : h.norm (c : K) = (c : K) ^ 4 := by
      rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply]
      ring
    rw [← this, hN]
  have hGL : dA h a * dA h a = GeneralLinearGroup.scalar (HypIndex 2 0) c *
      (s : GL (HypIndex 2 0) K) := (mul_inv_eq_iff_eq_mul).1 hc'
  have hdet := congrArg (fun g : GL (HypIndex 2 0) K =>
    (g : Matrix (HypIndex 2 0) (HypIndex 2 0) K).det) hGL
  simp only [Units.val_mul, det_mul, dA_coe, GeneralLinearGroup.coe_scalar] at hdet
  rw [(mem_hypSU.1 s.2).2, mul_one, det_dEntries, Matrix.scalar_apply, det_diagonal] at hdet
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin] at hdet
  apply ha
  have h4 : (a : K) / h.bar a * ((a : K) / h.bar a) * (a : K) ^ 4 = 1 := by
    rw [UnitaryFieldData.bar_apply]
    have : (a : K) ≠ 0 := a.ne_zero
    field_simp
    ring
  rw [hdet] at h4
  have : (c : K) ^ (2 + (0 + 2)) = (c : K) ^ 4 := by norm_num
  rw [this, hc4] at h4
  simpa using h4

end OuterModel

section Assembly

open CFSG.Assembly.LowTwoRank CFSG.LieType.Multipliers.U43 CFSG.LocalAnalysis.ComponentInitial

instance innNormal {G : Type} [Group G] :
    (MulAut.conj : G →* MulAut G).range.Normal where
  conj_mem := by
    rintro _ ⟨x, rfl⟩ α
    refine ⟨α x, ?_⟩
    ext z
    simp [MulAut.conj_apply]

theorem not_inner_transport {P Y : Type} [Group P] [Group Y] (φ : P ≃* Y) {γ : MulAut P}
    (hγ : γ * γ ∉ (MulAut.conj : P →* MulAut P).range) :
    MulAut.congr φ γ * MulAut.congr φ γ ∉ (MulAut.conj : Y →* MulAut Y).range := by
  rintro ⟨y, hy⟩
  apply hγ
  refine ⟨φ.symm y, ?_⟩
  have h1 : (MulAut.congr φ).symm (MulAut.congr φ γ * MulAut.congr φ γ) = γ * γ := by
    rw [← map_mul]; exact MulEquiv.symm_apply_apply _ _
  rw [← h1, ← hy]
  ext p
  simp [MulAut.congr_symm_apply, MulAut.conj_apply]

theorem u43_card_mulAut_le : Nat.card (MulAut X₀) ≤ 26127360 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card F9 = (3 ^ 1) ^ 2 := by
    rw [Nat.card_eq_fintype_card, F9.card_eq]
    norm_num
  have h := card_mulAut_psu_le (p := 3) (e := 1) (n := 4) (K := F9) (by norm_num) hK
    (by norm_num)
  have hU := unitaryFieldData_of_card (p := 3) (e := 1) (K := F9) hK
  have hint := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int hU (n := 4) (by norm_num)
  have hSU : Nat.card (StatedSU 4 (3 ^ 1) F9) = 13063680 := by
    have h2 : ((Nat.card (StatedSU 4 (3 ^ 1) F9) : ℕ) : ℤ) = 13063680 := by
      rw [hint]
      decide
    exact_mod_cast h2
  rw [hSU] at h
  exact h

theorem u43_conj_injective : Function.Injective (MulAut.conj : X₀ →* MulAut X₀) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hxc : x ∈ Subgroup.center X₀ := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h1 := congrArg (fun f : MulAut X₀ => f z) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  rw [u43_center_eq_bot] at hxc
  exact hxc

theorem u43_inn_index_le : (MulAut.conj : X₀ →* MulAut X₀).range.index ≤ 8 := by
  have hcard : Nat.card (MulAut.conj : X₀ →* MulAut X₀).range = 3265920 := by
    rw [← card_X₀]
    exact (Nat.card_congr (MonoidHom.ofInjective u43_conj_injective).toEquiv).symm
  have h1 := Subgroup.index_mul_card (MulAut.conj : X₀ →* MulAut X₀).range
  have h2 := u43_card_mulAut_le
  rw [hcard] at h1
  omega

theorem u43_exists_outer_sq : ∃ γ : MulAut X₀, γ * γ ∉ (MulAut.conj : X₀ →* MulAut X₀).range := by
  obtain ⟨φ⟩ := hypPSU_equiv_X₀
  have hK : Nat.card F9 = 9 := by rw [Nat.card_eq_fintype_card, F9.card_eq]
  obtain ⟨a, ha⟩ : ∃ a : F9ˣ, (a : F9) ^ 4 ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := F9ˣ)
    have h8 : Nat.card F9ˣ = 8 := by rw [Nat.card_units, hK]
    have h9 := orderOf_eq_card_of_forall_mem_zpowers hg
    rw [h8] at h9
    have h4 : g ^ 4 = 1 := Units.ext (by simpa using hcon g)
    have := orderOf_dvd_of_pow_eq_one h4
    rw [h9] at this
    omega
  exact ⟨MulAut.congr φ _, not_inner_transport φ (linearSimAut_dA_sq_not_inner F9_unitaryData a ha)⟩

theorem u43_outElemIndexLE : OutElemIndexLE X₀ 4 := by
  obtain ⟨γ, hγ⟩ := u43_exists_outer_sq
  have : Finite (MulAut X₀) := by
    have : Finite X₀ := Nat.finite_of_card_ne_zero (by rw [card_X₀]; norm_num)
    exact Finite.of_injective (fun f : MulAut X₀ => (f : X₀ → X₀)) DFunLike.coe_injective
  intro B hc hs
  exact card_le_four_mul_of_index_le_eight _ u43_inn_index_le γ hγ B hc hs

end Assembly

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
