module

public import CFSG.Timmesfeld.Orders.Bang
public import CFSG.Timmesfeld.Transvection.Statement
public import CFSG.Timmesfeld.LieEmbed.UnitaryForms
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniMatrix
import CFSG.RankThree.GF2n.Tim81.Cited.UnitaryTIModulePpd
import CFSG.RankThree.GF2n.Tim79aSUGenSteps

public section

namespace CFSG.LieType.Universal.Unitary

open Matrix CFSG.Timmesfeld CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.LieEmbed CFSG.LieType.BorelTits
  CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput CFSG.AGLEmbedding.LeviBlock

@[expose] def midIndexFun (k : ℕ) (i : Fin k) : Fin (k + 2) :=
  if (i : ℕ) < k / 2 then ⟨i, by omega⟩ else ⟨i + 2, by omega⟩

theorem midIndexFun_injective (k : ℕ) : Function.Injective (midIndexFun k) := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  by_cases hi' : (i : ℕ) < k / 2 <;> by_cases hj' : (j : ℕ) < k / 2
  · simp only [midIndexFun, if_pos hi', if_pos hj', Fin.mk.injEq] at hij
    exact Fin.ext hij
  · simp only [midIndexFun, if_pos hi', if_neg hj', Fin.mk.injEq] at hij
    omega
  · simp only [midIndexFun, if_neg hi', if_pos hj', Fin.mk.injEq] at hij
    omega
  · simp only [midIndexFun, if_neg hi', if_neg hj', Fin.mk.injEq] at hij
    exact Fin.ext (by omega)

@[expose] def midIndex (k : ℕ) : Fin k ↪ Fin (k + 2) :=
  ⟨midIndexFun k, midIndexFun_injective k⟩

@[simp] theorem midIndex_apply (k : ℕ) (i : Fin k) : midIndex k i = midIndexFun k i := rfl

theorem midIndex_apply_of_lt {k : ℕ} {i : Fin k} (h : (i : ℕ) < k / 2) :
    midIndex k i = ⟨i, by omega⟩ := by
  simp [midIndexFun, h]

theorem midIndex_apply_of_ge {k : ℕ} {i : Fin k} (h : ¬ (i : ℕ) < k / 2) :
    midIndex k i = ⟨i + 2, by omega⟩ := by
  simp [midIndexFun, h]

theorem midIndex_ne_left (k : ℕ) (i : Fin k) :
    midIndex k i ≠ (⟨k / 2, by omega⟩ : Fin (k + 2)) := by
  have hi := i.isLt
  by_cases h : (i : ℕ) < k / 2
  · rw [midIndex_apply_of_lt h]
    intro hj
    simp only [Fin.mk.injEq] at hj
    omega
  · rw [midIndex_apply_of_ge h]
    intro hj
    simp only [Fin.mk.injEq] at hj
    omega

theorem midIndex_ne_right (k : ℕ) (i : Fin k) :
    midIndex k i ≠ (⟨k / 2 + 1, by omega⟩ : Fin (k + 2)) := by
  have hi := i.isLt
  by_cases h : (i : ℕ) < k / 2
  · rw [midIndex_apply_of_lt h]
    intro hj
    simp only [Fin.mk.injEq] at hj
    omega
  · rw [midIndex_apply_of_ge h]
    intro hj
    simp only [Fin.mk.injEq] at hj
    omega

theorem range_midIndex (k : ℕ) :
    Set.range (midIndex k) =
      {x : Fin (k + 2) | (x : ℕ) ≠ k / 2 ∧ (x : ℕ) ≠ k / 2 + 1} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨fun h => midIndex_ne_left k i (Fin.ext h),
      fun h => midIndex_ne_right k i (Fin.ext h)⟩
  · rintro ⟨h1, h2⟩
    have hx := x.isLt
    by_cases h : (x : ℕ) < k / 2
    · refine ⟨⟨x, by omega⟩, ?_⟩
      rw [midIndex_apply_of_lt h]
    · by_cases h' : (x : ℕ) < k / 2 + 1
      · exact absurd (by omega : (x : ℕ) = k / 2) h1
      · have hx2 : ¬ (x - 2 : ℕ) < k / 2 := by omega
        refine ⟨⟨x - 2, by omega⟩, ?_⟩
        rw [midIndex_apply_of_ge (i := ⟨x - 2, by omega⟩) (by simpa using hx2)]
        ext
        simp only [Fin.val_mk]
        omega

theorem midIndex_rev {k : ℕ} (hk : Even k) (i : Fin k) :
    midIndex k (Fin.rev i) = Fin.rev (midIndex k i) := by
  have hk2 : 2 * (k / 2) = k := Nat.two_mul_div_two_of_even hk
  have hi := i.isLt
  have hrev : (Fin.rev i : ℕ) = k - 1 - i := by
    rw [Fin.val_rev]
    omega
  by_cases h : (i : ℕ) < k / 2
  · have hge : ¬ (Fin.rev i : ℕ) < k / 2 := by rw [hrev]; omega
    have hmid : (midIndex k i : ℕ) = i := by rw [midIndex_apply_of_lt h]
    apply Fin.ext
    rw [midIndex_apply_of_ge hge]
    simp only [Fin.val_rev, Fin.val_mk]
    rw [hmid]
    omega
  · have hlt : (Fin.rev i : ℕ) < k / 2 := by rw [hrev]; omega
    have hmid : (midIndex k i : ℕ) = i + 2 := by rw [midIndex_apply_of_ge h]
    apply Fin.ext
    rw [midIndex_apply_of_lt hlt]
    simp only [Fin.val_rev, Fin.val_mk]
    rw [hmid]
    omega

noncomputable def midBlockHom {F : Type} [Field F] (σ : F ≃+* F) {k : ℕ} (hk : Even k) :
    SU σ k →* SU σ (k + 2) :=
  suEmbed σ (τ := midIndex k) (midIndex k).injective (midIndex_rev hk)

theorem midBlockHom_injective {F : Type} [Field F] (σ : F ≃+* F) {k : ℕ} (hk : Even k) :
    Function.Injective (midBlockHom σ hk) :=
  suEmbed_injective σ (midIndex k).injective (midIndex_rev hk)

theorem suMat_midBlockHom {F : Type} [Field F] (σ : F ≃+* F) {k : ℕ} (hk : Even k)
    (A : SU σ k) :
    suMat σ (k + 2) (midBlockHom σ hk A) =
      extendMat (φ := midIndex k) (midIndex k).injective (suMat σ k A) :=
  CFSG.Timmesfeld.Transvection.ModelRank.suMat_suEmbed_eq σ
    (midIndex k).injective (midIndex_rev hk) A

theorem commute_midBlockHom_rootGroup {F : Type} [Field F] {σ : F ≃+* F}
    (hσ : ∀ c, σ (σ c) = c) {k : ℕ} (hk : Even k) {A : SU σ k}
    {u : SU σ (k + 2)}
    (hu : u ∈ rootGroup σ hσ (k + 2) (unitaryLongRoot (k + 2) (by omega))) :
    Commute (midBlockHom σ hk A) u := by
  let v : Fin (k + 2) → F :=
    Pi.single (lowIdx (n := k + 2) ⟨(k + 2) / 2 - 1, by omega⟩) 1
  have hUT :=
    CFSG.Timmesfeld.Transvection.ModelRank.isUTransGroup_rootGroup_unitaryLongRoot hσ
      (m := k + 2) (by omega)
  obtain ⟨c, hc, hsu⟩ := (hUT.1 u).1 hu
  have hdiv : (k + 2) / 2 - 1 = k / 2 := by
    have hk2 := Nat.two_mul_div_two_of_even hk
    have h : (k + 2) / 2 = k / 2 + 1 := by
      have h1 : k + 2 = 2 * (k / 2) + 2 := by omega
      calc (k + 2) / 2 = (2 * (k / 2) + 2) / 2 := by rw [h1]
        _ = (2 * (k / 2 + 1)) / 2 := by
          rw [show 2 * (k / 2) + 2 = 2 * (k / 2 + 1) by ring]
        _ = k / 2 + 1 := Nat.mul_div_right _ (by norm_num : 0 < 2)
    omega
  have hv : v = Pi.single (⟨k / 2, by omega⟩ : Fin (k + 2)) 1 := by
    unfold v
    congr 1
    apply Fin.ext
    simp [lowIdx, hdiv]
  have hi : (⟨k / 2, by omega⟩ : Fin (k + 2)) ∉ Set.range (midIndex k) := by
    rw [range_midIndex]
    simp
  have hfix : extendMat (φ := midIndex k) (midIndex k).injective (suMat σ k A) *ᵥ v = v := by
    rw [hv]
    exact CFSG.Timmesfeld.Transvection.ModelRank.extendMat_mulVec_single
      (τ := midIndex k) (midIndex k).injective _ hi
  have hN : suMat σ (k + 2) (midBlockHom σ hk A) * uNil σ v =
      uNil σ v * suMat σ (k + 2) (midBlockHom σ hk A) := by
    have h := suMat_mul_uNil σ (midBlockHom σ hk A) v
    rw [suMat_midBlockHom] at h
    rw [hfix] at h
    rw [suMat_midBlockHom]
    exact h
  have hT : suMat σ (k + 2) (midBlockHom σ hk A) * uTrans σ v c =
      uTrans σ v c * suMat σ (k + 2) (midBlockHom σ hk A) := by
    simp only [uTrans, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_smul, Matrix.smul_mul, hN]
  refine suMat_injective σ ?_
  rw [map_mul, map_mul, hsu, hT]

theorem exists_ppd_commute_rootGroup_unitaryLongRoot {F : Type} [Field F] [Finite F]
    [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) {m : ℕ} (hm : 6 ≤ m)
    (he : Even m) :
    ∃ (r : ℕ) (y : SU (unitaryInvolution F 2 f) m),
      IsPrimitivePrimeDivisor r (2 * f * (m - 3)) ∧
      orderOf y = r ∧ y ∉ Subgroup.center (SU (unitaryInvolution F 2 f) m) ∧
      ∀ u ∈ (rootDatum hF m).rootGroup (unitaryLongRoot m (by omega)), Commute y u := by
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hk : Even k := by
    obtain ⟨t, ht⟩ := he
    exact ⟨t - 1, by omega⟩
  have hkodd : Odd (k - 1) := by
    obtain ⟨t, ht⟩ := hk
    exact ⟨t - 1, by omega⟩
  have hk3 : 3 ≤ k - 1 := by omega
  have hle : k - 1 ≤ k := by omega
  obtain ⟨r, g, hr, hgord, hgZ⟩ :=
    CFSG.RankThree.GF2n.Tim81.TIModule.exists_ppd_SU (n := k) hF hf hkodd hk3 hle
  have hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c :=
    unitaryInvolution_involutive hF
  refine ⟨r, midBlockHom (unitaryInvolution F 2 f) hk g, ?_, ?_, ?_, ?_⟩
  · have hsub : k + 2 - 3 = k - 1 := by omega
    rwa [hsub]
  · exact (orderOf_injective _ (midBlockHom_injective _ hk) g).trans hgord
  · intro hy
    apply hgZ
    rw [Subgroup.mem_center_iff] at hy ⊢
    intro h
    apply midBlockHom_injective (unitaryInvolution F 2 f) hk
    calc midBlockHom (unitaryInvolution F 2 f) hk (h * g) =
        midBlockHom (unitaryInvolution F 2 f) hk h *
          midBlockHom (unitaryInvolution F 2 f) hk g := map_mul _ _ _
      _ = midBlockHom (unitaryInvolution F 2 f) hk g *
          midBlockHom (unitaryInvolution F 2 f) hk h := hy _
      _ = midBlockHom (unitaryInvolution F 2 f) hk (g * h) := (map_mul _ _ _).symm
  · intro u hu
    exact commute_midBlockHom_rootGroup hσ hk hu

theorem exists_ppd_commute_map_conjSub {X : Type*} [Group X] {f : ℕ} (hf : 2 ≤ f) {m : ℕ}
    (hm : 6 ≤ m) (he : Even m)
    (Φ : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m →* X)
    (hker : Φ.ker = Subgroup.center _)
    (x : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m) :
    ∃ (r : ℕ) (y : X), IsPrimitivePrimeDivisor r (2 * f * (m - 3)) ∧ orderOf y = r ∧
      ∀ v ∈ (conjSub ((rootDatum (card_galoisField_two_mul (by omega : 1 ≤ f)) m).rootGroup
        (unitaryLongRoot m (by omega))) x).map Φ, Commute y v := by
  obtain ⟨r, y₀, hr, hord, hy₀Z, hcomm⟩ :=
    exists_ppd_commute_rootGroup_unitaryLongRoot (F := GaloisField 2 (2 * f)) (f := f)
      (card_galoisField_two_mul (by omega : 1 ≤ f)) hf hm he
  let z : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m := x * y₀ * x⁻¹
  refine ⟨r, Φ z, hr, ?_, ?_⟩
  · have hy₀pow : y₀ ^ r = 1 := by rw [← hord, pow_orderOf_eq_one]
    have hzpow : z ^ r = 1 := by
      rw [show z = MulAut.conj x y₀ by simp only [z, MulAut.conj_apply], ← map_pow,
        hy₀pow, map_one]
    have hypow : (Φ z) ^ r = 1 := by
      rw [← map_pow, hzpow, map_one]
    have hzZ : z ∉ Subgroup.center
        (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m) := by
      intro hz
      apply hy₀Z
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro h
      have h1 := hz (x * h * x⁻¹)
      calc h * y₀ = x⁻¹ * ((x * h * x⁻¹) * (x * y₀ * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * y₀ * x⁻¹) * (x * h * x⁻¹)) * x := by rw [h1]
        _ = y₀ * h := by group
    have hzne : Φ z ≠ 1 := by
      intro h
      apply hzZ
      rw [← hker]
      exact MonoidHom.mem_ker.mpr h
    haveI : Fact r.Prime := ⟨hr.prime⟩
    exact orderOf_eq_prime hypow hzne
  · intro v hv
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hv
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp ha
    have hzu : Commute z (MulAut.conj x u) := by
      have h := (hcomm u hu).map (MulAut.conj x).toMonoidHom
      simpa [z, MulAut.conj_apply] using h
    exact hzu.map Φ

end CFSG.LieType.Universal.Unitary
