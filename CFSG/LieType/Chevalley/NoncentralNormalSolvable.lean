module

public import CFSG.LieType.Chevalley.NormalBorelSaturation
public import CFSG.LieType.Chevalley.HeightSeries

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley
open scoped Pointwise commutatorElement

variable (τ : Tag)

theorem exists_maxHeight_lt_two_pow
    : ∃ d : ℕ, maxHeight τ < 2 ^ d := by
  have h1 := one_le_maxHeight τ
  have h2 : (maxHeight τ).toNat < 2 ^ (maxHeight τ).toNat := Nat.lt_two_pow_self
  have h3 : ((maxHeight τ).toNat : ℤ) = maxHeight τ := Int.toNat_of_nonneg (by omega)
  refine ⟨(maxHeight τ).toNat, ?_⟩
  calc maxHeight τ = ((maxHeight τ).toNat : ℤ) := h3.symm
    _ < ((2 ^ (maxHeight τ).toNat : ℕ) : ℤ) := by exact_mod_cast h2
    _ = 2 ^ (maxHeight τ).toNat := by push_cast; ring

open _root_.Classical in
@[expose] def solvableDegree : ℕ :=
  Nat.find (exists_maxHeight_lt_two_pow τ)

theorem maxHeight_lt_two_pow_solvableDegree :
    maxHeight τ < 2 ^ solvableDegree τ := by
  classical
  exact Nat.find_spec (exists_maxHeight_lt_two_pow τ)

theorem two_pow_le_maxHeight_of_lt_solvableDegree
    {d : ℕ} (hd : d < solvableDegree τ) :
    2 ^ d ≤ maxHeight τ := by
  classical
  have h := Nat.find_min (exists_maxHeight_lt_two_pow τ) hd
  push Not at h
  exact h

variable {τ} {K : Type} [Field K]

theorem heightSeries_antitone
    {h h' : ℤ} (hh : h ≤ h') :
    heightSeries τ K h' ≤ heightSeries τ K h :=
  biSup_mono fun _ hα => ⟨hα.1, hα.2.1, hh.trans hα.2.2⟩

theorem commutator_borelGroup_le
    : ⁅borelGroup τ K, borelGroup τ K⁆ ≤ posUnipotent τ K := by
  obtain ⟨hab, -, hN, -, -, hUH, -⟩ := triangular_borel_structure.{0, 0} τ K
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have h1 : g₁ ∈ (posUnipotent τ K : Set (ModGL τ K)) * (torusGroup τ K : Set (ModGL τ K)) :=
    hUH ▸ hg₁
  have h2 : g₂ ∈ (posUnipotent τ K : Set (ModGL τ K)) * (torusGroup τ K : Set (ModGL τ K)) :=
    hUH ▸ hg₂
  obtain ⟨u₁, hu₁, t₁, ht₁, rfl⟩ := h1
  obtain ⟨u₂, hu₂, t₂, ht₂, rfl⟩ := h2
  have hc : t₂ * t₁⁻¹ = t₁⁻¹ * t₂ := by
    calc t₂ * t₁⁻¹ = t₁⁻¹ * (t₁ * t₂) * t₁⁻¹ := by group
      _ = t₁⁻¹ * (t₂ * t₁) * t₁⁻¹ := by rw [hab t₁ ht₁ t₂ ht₂]
      _ = t₁⁻¹ * t₂ := by group
  have hconj : ∀ t ∈ torusGroup τ K, ∀ u ∈ posUnipotent τ K, t * u * t⁻¹ ∈ posUnipotent τ K :=
    fun t ht u hu => (Subgroup.mem_normalizer_iff.1 (hN ht) u).1 hu
  have e : ⁅u₁ * t₁, u₂ * t₂⁆ = u₁ * (t₁ * u₂ * t₁⁻¹) * (t₂ * u₁⁻¹ * t₂⁻¹) * u₂⁻¹ := by
    calc ⁅u₁ * t₁, u₂ * t₂⁆ = u₁ * t₁ * u₂ * (t₂ * t₁⁻¹) * u₁⁻¹ * t₂⁻¹ * u₂⁻¹ := by group
      _ = u₁ * t₁ * u₂ * (t₁⁻¹ * t₂) * u₁⁻¹ * t₂⁻¹ * u₂⁻¹ := by rw [hc]
      _ = u₁ * (t₁ * u₂ * t₁⁻¹) * (t₂ * u₁⁻¹ * t₂⁻¹) * u₂⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem (mul_mem hu₁ (hconj t₁ ht₁ u₂ hu₂)) (hconj t₂ ht₂ _ (inv_mem hu₁)))
    (inv_mem hu₂)

theorem map_derivedSeries_borelGroup_le
    (k : ℕ) :
    (derivedSeries (borelGroup τ K) (k + 1)).map (borelGroup τ K).subtype ≤
      heightSeries τ K (2 ^ k) := by
  induction k with
  | zero =>
    rw [derivedSeries_succ, derivedSeries_zero, Subgroup.map_commutator,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype, pow_zero, heightSeries_one]
    exact commutator_borelGroup_le
  | succ k ih =>
    rw [derivedSeries_succ, Subgroup.map_commutator]
    calc ⁅(derivedSeries (borelGroup τ K) (k + 1)).map (borelGroup τ K).subtype,
          (derivedSeries (borelGroup τ K) (k + 1)).map (borelGroup τ K).subtype⁆ ≤
          ⁅heightSeries τ K (2 ^ k), heightSeries τ K (2 ^ k)⁆ :=
          Subgroup.commutator_mono ih ih
      _ ≤ heightSeries τ K (2 ^ k + 2 ^ k) := commutator_heightSeries_le K _ _
      _ = heightSeries τ K (2 ^ (k + 1)) := by rw [pow_succ, mul_two]

theorem derivedSeries_borelGroup_eq_bot :
    derivedSeries (borelGroup τ K) (solvableDegree τ + 1) = ⊥ := by
  have h := map_derivedSeries_borelGroup_le (τ := τ) (K := K) (solvableDegree τ)
  have hle : heightSeries τ K (2 ^ solvableDegree τ) ≤ heightSeries τ K (maxHeight τ + 1) :=
    heightSeries_antitone (Int.add_one_le_iff.2 (maxHeight_lt_two_pow_solvableDegree τ))
  rw [heightSeries_maxHeight_add_one] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ (borelGroup τ K).subtype_injective).1
    (eq_bot_iff.2 (h.trans hle))

variable (τ K) in
theorem noncentral_normal_solvable_quotient
    (M : Subgroup (adjointGroup τ K)) [M.Normal]
    (hM : ¬M ≤ Subgroup.center (adjointGroup τ K)) :
    (maxHeight τ < 2 ^ solvableDegree τ ∧ ∀ d < solvableDegree τ, 2 ^ d ≤ maxHeight τ) ∧
      Group.IsSolvable (adjointGroup τ K ⧸ M) ∧
      derivedSeries (adjointGroup τ K ⧸ M) (solvableDegree τ + 1) = ⊥ := by
  have hBC : borelGroup τ K ≤ adjointGroup τ K :=
    ((triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.2.2.2 K).1
  rcases normal_borel_saturation τ K M with hZ | ⟨hMB, hP⟩
  · exact absurd hZ hM
  set ψ : borelGroup τ K →* adjointGroup τ K ⧸ M :=
    (QuotientGroup.mk' M).comp (Subgroup.inclusion hBC)
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective M q
    have hg : (g : ModGL τ K) ∈ (M.map (adjointGroup τ K).subtype : Set (ModGL τ K)) *
        (borelGroup τ K : Set (ModGL τ K)) := by
      rw [hMB, hP]
      exact g.2
    obtain ⟨_, ⟨m, hm, rfl⟩, b, hb, hmb⟩ := hg
    refine ⟨⟨b, hb⟩, ?_⟩
    have hgm : g = m * Subgroup.inclusion hBC ⟨b, hb⟩ :=
      Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_inclusion]; exact hmb.symm)
    rw [hgm, map_mul, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff m).2 hm, one_mul]
    rfl
  have hbot : derivedSeries (adjointGroup τ K ⧸ M) (solvableDegree τ + 1) = ⊥ := by
    rw [← map_derivedSeries_eq hψ, derivedSeries_borelGroup_eq_bot, Subgroup.map_bot]
  exact ⟨⟨maxHeight_lt_two_pow_solvableDegree τ,
    fun d hd => two_pow_le_maxHeight_of_lt_solvableDegree τ hd⟩, ⟨⟨_, hbot⟩⟩, hbot⟩

end CFSG.LieType.Chevalley
