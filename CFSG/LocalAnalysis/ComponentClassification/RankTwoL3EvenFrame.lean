module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3EvenAut
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoL3Even

open Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag FieldFourCover CFSG.LieType.Chevalley
open scoped commutatorElement

variable {F : Type} [Field F]

abbrev conjP (F : Type) [Field F] : projectiveSL 3 F →* MulAut (projectiveSL 3 F) :=
  MulAut.conj

abbrev innerP (F : Type) [Field F] : Subgroup (MulAut (projectiveSL 3 F)) :=
  (conjP F).range

@[expose] def leviA (γ : MulAut (projectiveSL 3 F)) : Subgroup (MulAut (projectiveSL 3 F)) :=
  ((projLevi F).range.map (conjP F)).map (MulAut.conj γ).toMonoidHom

@[expose] def unipA (γ : MulAut (projectiveSL 3 F)) : Subgroup (MulAut (projectiveSL 3 F)) :=
  ((projUnip F).map (conjP F)).map (MulAut.conj γ).toMonoidHom

@[expose] def centerA (γ : MulAut (projectiveSL 3 F)) : Subgroup (MulAut (projectiveSL 3 F)) :=
  ((projCenterW F).map (conjP F)).map (MulAut.conj γ).toMonoidHom

theorem mem_leviA {γ s : MulAut (projectiveSL 3 F)} :
    s ∈ leviA γ ↔ ∃ B : SL2 F, s = γ * MulAut.conj (projLevi F B) * γ⁻¹ := by
  constructor
  · rintro ⟨_, ⟨_, ⟨B, rfl⟩, rfl⟩, rfl⟩
    exact ⟨B, rfl⟩
  · rintro ⟨B, rfl⟩
    exact ⟨_, ⟨_, ⟨B, rfl⟩, rfl⟩, rfl⟩

theorem mem_unipA {γ s : MulAut (projectiveSL 3 F)} :
    s ∈ unipA γ ↔ ∃ u ∈ projUnip F, s = γ * MulAut.conj u * γ⁻¹ := by
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨_, ⟨u, hu, rfl⟩, rfl⟩

theorem mem_centerA {γ s : MulAut (projectiveSL 3 F)} :
    s ∈ centerA γ ↔ ∃ z ∈ projCenterW F, s = γ * MulAut.conj z * γ⁻¹ := by
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨_, ⟨z, hz, rfl⟩, rfl⟩

theorem conj_mem_innerP (γ : MulAut (projectiveSL 3 F)) (p : projectiveSL 3 F) :
    γ * MulAut.conj p * γ⁻¹ ∈ innerP F :=
  ⟨γ p, conj_map_eq γ p⟩

theorem leviA_le_innerP (γ : MulAut (projectiveSL 3 F)) : leviA γ ≤ innerP F := by
  intro s hs
  obtain ⟨B, rfl⟩ := mem_leviA.1 hs
  exact conj_mem_innerP γ _

theorem unipA_le_innerP (γ : MulAut (projectiveSL 3 F)) : unipA γ ≤ innerP F := by
  intro s hs
  obtain ⟨u, -, rfl⟩ := mem_unipA.1 hs
  exact conj_mem_innerP γ _

theorem projCenterW_le_range_projLevi : projCenterW F ≤ (projLevi F).range := by
  intro z hz
  obtain ⟨c, rfl⟩ := mem_projCenterW.1 hz
  exact ⟨uSL c, (proj_unipU_center_eq_projLevi c).symm⟩

theorem centerA_le_leviA (γ : MulAut (projectiveSL 3 F)) : centerA γ ≤ leviA γ :=
  map_mono (map_mono projCenterW_le_range_projLevi)

theorem centerA_le_unipA (γ : MulAut (projectiveSL 3 F)) : centerA γ ≤ unipA γ := by
  have h : projCenterW F ≤ projUnip F := (projCenterW_le_projRad 0).trans (projRad_le_projUnip 0)
  exact map_mono (map_mono h)

theorem commutator_leviA [Group.IsPerfect (SL2 F)] (γ : MulAut (projectiveSL 3 F)) :
    ⁅leviA γ, leviA γ⁆ = leviA γ := by
  rw [leviA, ← map_commutator, ← map_commutator, commutator_range_projLevi]

theorem leviA_injective (γ : MulAut (projectiveSL 3 F)) :
    Function.Injective fun B : SL2 F => γ * MulAut.conj (projLevi F B) * γ⁻¹ := by
  intro B B' h
  have h1 : MulAut.conj (projLevi F B) = MulAut.conj (projLevi F B') := by
    simpa using h
  exact projLevi_injective (conj_injective_projectiveSL h1)

@[expose] def leviAHom (γ : MulAut (projectiveSL 3 F)) : SL2 F →* MulAut (projectiveSL 3 F) :=
  (MulAut.conj γ).toMonoidHom.comp ((conjP F).comp (projLevi F))

theorem range_leviAHom (γ : MulAut (projectiveSL 3 F)) : (leviAHom γ).range = leviA γ := by
  rw [leviAHom, MonoidHom.range_comp, MonoidHom.range_comp, leviA]

@[expose] def leviAEquiv (γ : MulAut (projectiveSL 3 F)) : SL2 F ≃* leviA γ :=
  (MonoidHom.ofInjective (f := leviAHom γ) (leviA_injective γ)).trans
    (MulEquiv.subgroupCongr (range_leviAHom γ))

theorem isSimpleGroup_leviA [IsSimpleGroup (SL2 F)] (γ : MulAut (projectiveSL 3 F)) :
    IsSimpleGroup (leviA γ) :=
  (leviAEquiv γ).symm.isSimpleGroup

theorem center_leviA [IsSimpleGroup (SL2 F)] (hnab : ∃ a b : SL2 F, a * b ≠ b * a)
    (γ : MulAut (projectiveSL 3 F)) : center (leviA γ) = ⊥ := by
  have := isSimpleGroup_leviA γ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (leviA γ)) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply (leviAEquiv γ).injective
    rw [map_mul, map_mul]
    have hc := (mem_center_iff.1 (h ▸ mem_top (leviAEquiv γ b))) (leviAEquiv γ a)
    exact hc

theorem conjAut_torusGL_commute_conj (b : Fˣ) (B : SL2 F) :
    conjAut 3 F (torusGL b) * MulAut.conj (projLevi F B) =
      MulAut.conj (projLevi F B) * conjAut 3 F (torusGL b) := by
  have h := conj_map_eq (conjAut 3 F (torusGL b)) (projLevi F B)
  rw [conjAut_torusGL_projLevi] at h
  rw [← mul_inv_eq_iff_eq_mul, ← h]

theorem commute_torus_leviA (b : Fˣ) (γ : MulAut (projectiveSL 3 F)) {s : MulAut (projectiveSL 3 F)}
    (hs : s ∈ leviA γ) :
    γ * conjAut 3 F (torusGL b) * γ⁻¹ * s = s * (γ * conjAut 3 F (torusGL b) * γ⁻¹) := by
  obtain ⟨B, rfl⟩ := mem_leviA.1 hs
  calc γ * conjAut 3 F (torusGL b) * γ⁻¹ * (γ * MulAut.conj (projLevi F B) * γ⁻¹)
      = γ * (conjAut 3 F (torusGL b) * MulAut.conj (projLevi F B)) * γ⁻¹ := by group
    _ = γ * (MulAut.conj (projLevi F B) * conjAut 3 F (torusGL b)) * γ⁻¹ := by
        rw [conjAut_torusGL_commute_conj]
    _ = γ * MulAut.conj (projLevi F B) * γ⁻¹ * (γ * conjAut 3 F (torusGL b) * γ⁻¹) := by group

theorem conj_inv_pow {M : Type*} [Group M] (γ σ : M) (n : ℕ) :
    (γ⁻¹ * σ * γ) ^ n = γ⁻¹ * σ ^ n * γ := by
  have h := conj_pow (a := γ⁻¹) (b := σ) (i := n)
  rwa [inv_inv] at h

theorem commute_conj_iff {M : Type*} [Group M] (γ σ x : M) :
    σ * (γ * x * γ⁻¹) = γ * x * γ⁻¹ * σ ↔ γ⁻¹ * σ * γ * x = x * (γ⁻¹ * σ * γ) := by
  constructor
  · intro h
    calc γ⁻¹ * σ * γ * x = γ⁻¹ * (σ * (γ * x * γ⁻¹)) * γ := by group
      _ = γ⁻¹ * (γ * x * γ⁻¹ * σ) * γ := by rw [h]
      _ = x * (γ⁻¹ * σ * γ) := by group
  · intro h
    calc σ * (γ * x * γ⁻¹) = γ * (γ⁻¹ * σ * γ * x) * γ⁻¹ := by group
      _ = γ * (x * (γ⁻¹ * σ * γ)) * γ⁻¹ := by rw [h]
      _ = γ * x * γ⁻¹ * σ := by group

theorem eq_one_of_commute_leviA [Finite F] [CharP F 2] {b : Fˣ} (hb : b ≠ 1)
    {γ σ : MulAut (projectiveSL 3 F)} {k : ℕ} (hk : σ ^ 2 ^ k = 1)
    (hc : σ * (γ * conjAut 3 F (torusGL b) * γ⁻¹) = γ * conjAut 3 F (torusGL b) * γ⁻¹ * σ)
    (hL : ∀ s ∈ leviA γ, σ * s = s * σ) : σ = 1 := by
  have h1 : γ⁻¹ * σ * γ = 1 := by
    refine eq_one_of_commute_of_fix_projLevi hb (k := k) ?_ ((commute_conj_iff γ σ _).1 hc) ?_
    · rw [conj_inv_pow, hk, mul_one, inv_mul_cancel]
    · intro B
      have h2 := (commute_conj_iff γ σ _).1 (hL _ (mem_leviA.2 ⟨B, rfl⟩))
      have h3 : MulAut.conj ((γ⁻¹ * σ * γ) (projLevi F B)) = MulAut.conj (projLevi F B) := by
        rw [conj_map_eq, h2, mul_inv_cancel_right]
      exact conj_injective_projectiveSL h3
  calc σ = γ * (γ⁻¹ * σ * γ) * γ⁻¹ := by group
    _ = 1 := by rw [h1, mul_one, mul_inv_cancel]

theorem mem_normalizer_leviA [Group.IsPerfect (SL2 F)] {b : Fˣ} (hb : b ≠ 1)
    {γ σ : MulAut (projectiveSL 3 F)}
    (hc : σ * (γ * conjAut 3 F (torusGL b) * γ⁻¹) = γ * conjAut 3 F (torusGL b) * γ⁻¹ * σ) :
    σ ∈ normalizer (leviA γ : Set (MulAut (projectiveSL 3 F))) := by
  have key : ∀ τ : MulAut (projectiveSL 3 F),
      τ * (γ * conjAut 3 F (torusGL b) * γ⁻¹) = γ * conjAut 3 F (torusGL b) * γ⁻¹ * τ →
        ∀ s ∈ leviA γ, τ * s * τ⁻¹ ∈ leviA γ := by
    intro τ hτ s hs
    obtain ⟨B, rfl⟩ := mem_leviA.1 hs
    have h1 := (commute_conj_iff γ τ _).1 hτ
    obtain ⟨B', hB'⟩ := map_projLevi_mem_of_commute hb h1 B
    refine mem_leviA.2 ⟨B', ?_⟩
    rw [hB', conj_map_eq]
    group
  have hc' : σ⁻¹ * (γ * conjAut 3 F (torusGL b) * γ⁻¹) =
      γ * conjAut 3 F (torusGL b) * γ⁻¹ * σ⁻¹ := by
    calc σ⁻¹ * (γ * conjAut 3 F (torusGL b) * γ⁻¹)
        = σ⁻¹ * (γ * conjAut 3 F (torusGL b) * γ⁻¹ * σ) * σ⁻¹ := by group
      _ = σ⁻¹ * (σ * (γ * conjAut 3 F (torusGL b) * γ⁻¹)) * σ⁻¹ := by rw [hc]
      _ = γ * conjAut 3 F (torusGL b) * γ⁻¹ * σ⁻¹ := by group
  refine mem_normalizer_iff.2 fun s => ⟨key σ hc s, fun hs => ?_⟩
  have := key σ⁻¹ hc' _ hs
  simpa [mul_assoc] using this

theorem commute_centerA_unipA {γ z u : MulAut (projectiveSL 3 F)} (hz : z ∈ centerA γ)
    (hu : u ∈ unipA γ) : z * u = u * z := by
  obtain ⟨z₀, hz₀, rfl⟩ := mem_centerA.1 hz
  obtain ⟨u₀, hu₀, rfl⟩ := mem_unipA.1 hu
  have h := commute_of_mem_projCenterW hz₀ hu₀
  calc γ * MulAut.conj z₀ * γ⁻¹ * (γ * MulAut.conj u₀ * γ⁻¹)
      = γ * MulAut.conj (z₀ * u₀) * γ⁻¹ := by rw [map_mul]; group
    _ = γ * MulAut.conj (u₀ * z₀) * γ⁻¹ := by rw [h]
    _ = γ * MulAut.conj u₀ * γ⁻¹ * (γ * MulAut.conj z₀ * γ⁻¹) := by rw [map_mul]; group

theorem mem_centerA_of_commute {γ σ : MulAut (projectiveSL 3 F)} (hσ : σ ∈ unipA γ)
    (h1 : σ * (γ * MulAut.conj (proj 3 F (unipU F 1 0 0)) * γ⁻¹) =
      γ * MulAut.conj (proj 3 F (unipU F 1 0 0)) * γ⁻¹ * σ)
    (h2 : σ * (γ * MulAut.conj (proj 3 F (unipU F 0 1 0)) * γ⁻¹) =
      γ * MulAut.conj (proj 3 F (unipU F 0 1 0)) * γ⁻¹ * σ) : σ ∈ centerA γ := by
  obtain ⟨u, hu, rfl⟩ := mem_unipA.1 hσ
  have key : ∀ v : projectiveSL 3 F,
      γ * MulAut.conj u * γ⁻¹ * (γ * MulAut.conj v * γ⁻¹) =
        γ * MulAut.conj v * γ⁻¹ * (γ * MulAut.conj u * γ⁻¹) → u * v = v * u := by
    intro v h
    have h' : γ * MulAut.conj (u * v) * γ⁻¹ = γ * MulAut.conj (v * u) * γ⁻¹ := by
      rw [map_mul, map_mul]
      calc γ * (MulAut.conj u * MulAut.conj v) * γ⁻¹
          = γ * MulAut.conj u * γ⁻¹ * (γ * MulAut.conj v * γ⁻¹) := by group
        _ = γ * MulAut.conj v * γ⁻¹ * (γ * MulAut.conj u * γ⁻¹) := h
        _ = γ * (MulAut.conj v * MulAut.conj u) * γ⁻¹ := by group
    exact conj_injective_projectiveSL (mul_right_cancel (mul_left_cancel h'))
  exact mem_centerA.2 ⟨u, mem_projCenterW_of_commute hu (key _ h1) (key _ h2), rfl⟩

theorem card_unipA [Finite F] (γ : MulAut (projectiveSL 3 F)) :
    Nat.card (unipA γ) = Nat.card F * Nat.card F * Nat.card F := by
  rw [unipA, card_map_of_injective (MulAut.conj γ).injective,
    card_map_of_injective conj_injective_projectiveSL, card_projUnip]

theorem isPGroup_unipA [Finite F] {m : ℕ} (hF : Nat.card F = 2 ^ m)
    (γ : MulAut (projectiveSL 3 F)) : IsPGroup 2 (unipA γ) := by
  refine IsPGroup.of_card (n := 3 * m) ?_
  rw [card_unipA, hF, ← pow_add, ← pow_add]
  ring_nf

end CFSG.ComponentClassification.RankTwoL3Even
