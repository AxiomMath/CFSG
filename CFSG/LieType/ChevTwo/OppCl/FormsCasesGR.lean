module

public import CFSG.LieType.ChevTwo.OppCl.FormsCasesSplit
public import CFSG.LieType.ChevTwo.OppCl.FormsCasesRank

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits

namespace FormsCases

section CaseG

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [Finite V] {H : Type} [Group H]

variable {Φ : ReflForm F V} {Sing : V → Prop} {TS : Submodule F V → Prop}
  {ρ : H →* Module.End F V} {p : ℕ} [Fact p.Prime]
  {Rh : Subgroup (Equiv.Perm V)} {X : ℕ → Submodule F V} {m : ℕ} {M W' : Submodule F V}

theorem realize_levi_mul {W Z : Submodule F V} (hZW : Z ≤ W) {g₁ g₂ : V →ₗ[F] V} {u₁ u₂ : H}
    (h₁ : ∀ v, g₁ v ∈ Z) (h₂ : ∀ v, g₂ v ∈ Z) (hz₁ : ∀ z ∈ Z, g₁ z = 0)
    (hu₁ : LevProp Φ ρ W g₁ u₁) (hu₂ : LevProp Φ ρ W g₂ u₂) :
    LevProp Φ ρ W (g₁ + g₂) (u₁ * u₂) := by
  obtain ⟨a₁, b₁⟩ := hu₁
  obtain ⟨a₂, b₂⟩ := hu₂
  refine ⟨fun w hw => ?_, fun y hy => ?_⟩
  · have hg₂w : g₂ w ∈ W := hZW (h₂ w)
    rw [map_mul, Module.End.mul_apply, a₂ w hw, map_add, a₁ w hw, a₁ _ hg₂w, hz₁ _ (h₂ w),
      LinearMap.add_apply]
    abel
  · obtain ⟨e₂, he₂⟩ : ∃ e₂, e₂ = ρ u₂ y - y := ⟨_, rfl⟩
    have hy₂ : e₂ ∈ W := he₂ ▸ b₂ y hy
    have hρ : ρ u₂ y = y + e₂ := by rw [he₂]; abel
    have e : ρ (u₁ * u₂) y - y = (ρ u₁ y - y) + (e₂ + g₁ e₂) := by
      rw [map_mul, Module.End.mul_apply, hρ, map_add, a₁ e₂ hy₂]
      abel
    rw [e]
    exact W.add_mem (b₁ y hy) (W.add_mem hy₂ (hZW (h₁ e₂)))

theorem realize_levi_core (C : RaiseCtx Φ Sing TS ρ p Rh X m M W') (g : V →ₗ[F] V)
    (hg2 : ∀ v, g (g v) = 0) (hgW : ∀ v, g v ∈ X m) (hgD : ∀ v ∈ M ⊔ W', g v = 0) :
    ∃ u : H, LevProp Φ ρ (X m) g u := by
  have hW : Φ.IsTotallyIsotropic (X m) := C.hTS _ (C.hXts m)
  have hW' : Φ.IsTotallyIsotropic W' := C.hTS _ C.hsplit.ts_W'
  obtain ⟨ι, hι, x, φ, hx, hφ, hsum⟩ := exists_rank_decomp g
  have hZW : LinearMap.range g ≤ X m := by
    rintro _ ⟨v, rfl⟩
    exact hgW v
  have hxW : ∀ j, x j ∈ X m := fun j => hZW (hx j)
  have hφZ : ∀ j, ∀ z ∈ LinearMap.range g, φ j z = 0 := by
    rintro j _ ⟨v, rfl⟩
    exact hφ j _ (hg2 v)
  have hφD : ∀ j, ∀ v ∈ M ⊔ W', φ j v = 0 := fun j v hv => hφ j v (hgD v hv)
  have hP := Finset.sum_induction (s := Finset.univ) (fun j => (φ j).smulRight (x j))
    (fun g' : V →ₗ[F] V => (∀ v, g' v ∈ LinearMap.range g) ∧ (∀ z ∈ LinearMap.range g, g' z = 0) ∧
      ∃ u : H, LevProp Φ ρ (X m) g' u)
    (fun g₁ g₂ ⟨h₁, hz₁, u₁, hu₁⟩ ⟨h₂, hz₂, u₂, hu₂⟩ =>
      ⟨fun v => (LinearMap.range g).add_mem (h₁ v) (h₂ v), fun z hz => by
        rw [LinearMap.add_apply, hz₁ z hz, hz₂ z hz, add_zero],
        u₁ * u₂, realize_levi_mul hZW h₁ h₂ hz₁ hu₁ hu₂⟩)
    ⟨fun v => (LinearMap.range g).zero_mem, fun z _ => rfl, 1,
      fun w _ => by rw [map_one, Module.End.one_apply, LinearMap.zero_apply, add_zero],
      fun y _ => by rw [map_one, Module.End.one_apply, sub_self]; exact (X m).zero_mem⟩
    (fun j _ => by
      obtain ⟨w', hw', hw'v⟩ := split3_exists_dual_W' C.hsplit hW hW' (φ j) (hφD j)
      have hxZ : x j ∈ LinearMap.range g := hx j
      have hβ : Φ.β w' (x j) = 0 := by rw [hw'v, hφZ j _ hxZ]
      obtain ⟨u, hu⟩ := C.hE0 w' (x j) (C.hTSsing _ C.hsplit.ts_W' w' hw')
        (C.hTSsing _ (C.hXts m) (x j) (hxW j)) hβ
      refine ⟨fun v => ?_, fun z hz => ?_, u, fun w hw => ?_, fun y hy => ?_⟩
      · rw [LinearMap.smulRight_apply]
        exact (LinearMap.range g).smul_mem _ hxZ
      · rw [LinearMap.smulRight_apply, hφZ j z hz, zero_smul]
      · rw [hu, hW hw (x j) (hxW j), zero_smul, sub_zero, hw'v, LinearMap.smulRight_apply]
      · rw [hu, hy (x j) (hxW j), zero_smul, sub_zero, add_sub_cancel_left]
        exact (X m).smul_mem _ (hxW j))
  rw [← hsum] at hP
  exact hP.2.2

end CaseG

end FormsCases

end CFSG.LieType.ChevTwo.OppCl
