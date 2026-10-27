module

public import CFSG.LieType.ChevTwo.OppCl.FormsCasesUrad
public import CFSG.LieType.ChevTwo.OppCl.FormsCasesSplit
public import CFSG.LieType.ChevTwo.OppCl.FormsCasesRank

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits

namespace FormsCases

section CaseM

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [Finite V] {H : Type} [Group H]

variable {Φ : ReflForm F V} {Sing : V → Prop} {TS : Submodule F V → Prop}
  {ρ : H →* Module.End F V} {p : ℕ} [Fact p.Prime]
  {Rh : Subgroup (Equiv.Perm V)} {X : ℕ → Submodule F V} {m : ℕ} {M W' : Submodule F V}

theorem realize_mid_rank_one (C : RaiseCtx Φ Sing TS ρ p Rh X m M W') {x w' : V} (hx : x ∈ M)
    (hw' : w' ∈ W') :
    ∃ u ∈ Urad Φ ρ W', ∀ w ∈ X m,
      ρ u w - w - (Φ.β w' w • x) ∈ W' := by
  have hW' : Φ.IsTotallyIsotropic W' := C.hTS _ C.hsplit.ts_W'
  have hβ : Φ.β w' x = 0 := Φ.refl _ _ (C.hsplit.perp_MW' _ hx w' hw')
  obtain ⟨c, h, hh⟩ := C.hE1 w' x (C.hTSsing _ C.hsplit.ts_W' w' hw') hβ
  refine ⟨h, ?_, fun w _ => ?_⟩
  · rw [mem_Urad_iff hW' C.hρ]
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [hh v, (Φ.mem_perp.mp (hW' hv)) w' hw', C.hsplit.perp_MW' _ hx v hv, zero_smul, zero_smul,
        add_zero, sub_zero]
    · have : ρ h v - v = -(Φ.β x v • w') := by
        rw [hh v, (Φ.mem_perp.mp hv) w' hw', zero_smul, add_zero]
        abel
      rw [this]
      exact neg_mem (Submodule.smul_mem _ _ hw')
  · have : ρ h w - w - (Φ.β w' w • x) = (Φ.β w' w * c - Φ.β x w) • w' := by
      rw [hh w, sub_smul, mul_smul, smul_add]
      abel
    rw [this]
    exact Submodule.smul_mem _ _ hw'

theorem realize_mid_core (C : RaiseCtx Φ Sing TS ρ p Rh X m M W') (a : V →ₗ[F] V)
    (ha : ∀ v, a v ∈ M) (ha0 : ∀ v ∈ M ⊔ W', a v = 0) :
    ∃ u ∈ Urad Φ ρ W', ∀ w ∈ X m, ρ u w - w - a w ∈ W' := by
  haveI : FiniteDimensional F V := Module.Finite.of_finite
  have hW : Φ.IsTotallyIsotropic (X m) := C.hTS _ (C.hXts m)
  have hW' : Φ.IsTotallyIsotropic W' := C.hTS _ C.hsplit.ts_W'
  have hMperp : M ≤ Φ.perp W' := fun μ hμ w' hw' => Φ.refl _ _ (C.hsplit.perp_MW' μ hμ w' hw')
  let 𝓜 : AddSubmonoid (V →ₗ[F] V) :=
    { carrier := {a' | (∀ v, a' v ∈ M) ∧
        ∃ u ∈ Urad Φ ρ W', ∀ w ∈ X m, ρ u w - w - a' w ∈ W'}
      zero_mem' := ⟨fun v => by simp, 1, one_mem _, fun w _ => by simp⟩
      add_mem' := by
        rintro a₁ a₂ ⟨hM₁, u₁, hu₁, h₁⟩ ⟨hM₂, u₂, hu₂, h₂⟩
        refine ⟨fun v => by simpa using add_mem (hM₁ v) (hM₂ v), u₁ * u₂, mul_mem hu₁ hu₂,
          fun w hw => ?_⟩
        obtain ⟨hu₁W, hu₁P⟩ := (mem_Urad_iff hW' C.hρ).mp hu₁
        have hδ₂ : ρ u₁ (ρ u₂ w - w - a₂ w) = ρ u₂ w - w - a₂ w := hu₁W _ (h₂ w hw)
        have hδ₃ : ρ u₁ (a₂ w) - a₂ w ∈ W' := hu₁P _ (hMperp (hM₂ w))
        have key : ρ (u₁ * u₂) w - w - (a₁ + a₂) w =
            (ρ u₁ w - w - a₁ w) + (ρ u₁ (a₂ w) - a₂ w) + (ρ u₂ w - w - a₂ w) := by
          have e : ρ u₂ w = w + a₂ w + (ρ u₂ w - w - a₂ w) := by abel
          rw [map_mul, Module.End.mul_apply, LinearMap.add_apply]
          conv_lhs => rw [e, map_add, map_add, hδ₂]
          abel
        rw [key]
        exact add_mem (add_mem (h₁ w hw) hδ₃) (h₂ w hw) }
  obtain ⟨ι, hι, x, φ, hx, hφ, hsum⟩ := exists_rank_decomp a
  have hterm : ∀ j, (φ j).smulRight (x j) ∈ 𝓜 := by
    intro j
    obtain ⟨w', hw', hβ⟩ :=
      split3_exists_dual_W' C.hsplit hW hW' (φ j) fun v hv => hφ j v (ha0 v hv)
    have hxM : x j ∈ M := by
      obtain ⟨v, hv⟩ := hx j
      rw [← hv]
      exact ha v
    obtain ⟨u, hu, h⟩ := realize_mid_rank_one C hxM hw'
    refine ⟨fun v => Submodule.smul_mem _ _ hxM, u, hu, fun w hw => ?_⟩
    have := h w hw
    rwa [hβ w] at this
  have hmem : a ∈ 𝓜 := by
    rw [hsum]
    exact AddSubmonoid.sum_mem _ fun j _ => hterm j
  obtain ⟨-, u, hu, h⟩ := hmem
  exact ⟨u, hu, h⟩

end CaseM

end FormsCases

end CFSG.LieType.ChevTwo.OppCl
