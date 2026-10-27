module

public import CFSG.LieType.ChevTwo.OppCl.Defs
import CFSG.LieType.ChevTwo.OppCl.FormsCasesBase

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits

namespace FormsCases

section Ctx

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {H : Type} [Group H]
variable {Φ : ReflForm F V} {Sing : V → Prop} {TS : Submodule F V → Prop}
  {ρ : H →* Module.End F V} {p : ℕ} {Rh : Subgroup (Equiv.Perm V)} {X : ℕ → Submodule F V}
  {m : ℕ} {M W' : Submodule F V}

theorem ctx_hW (C : RaiseCtx Φ Sing TS ρ p Rh X m M W') : Φ.IsTotallyIsotropic (X m) :=
  C.hTS _ (C.hXts m)

theorem ctx_hW' (C : RaiseCtx Φ Sing TS ρ p Rh X m M W') : Φ.IsTotallyIsotropic W' :=
  C.hTS _ C.hsplit.ts_W'

theorem sup_inv {A B : Submodule F V} (hs : Rh ≤ semilinGroup F V)
    (hA : ∀ r ∈ Rh, ∀ v ∈ A, r v ∈ A) (hB : ∀ r ∈ Rh, ∀ v ∈ B, r v ∈ B) :
    ∀ r ∈ Rh, ∀ v ∈ A ⊔ B, r v ∈ A ⊔ B := by
  intro r hr v hv
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  rw [(hs hr).1]
  exact Submodule.add_mem_sup (hA r hr a ha) (hB r hr b hb)

theorem ctx_sup_inv (C : RaiseCtx Φ Sing TS ρ p Rh X m M W') :
    ∀ r ∈ Rh, ∀ v ∈ M ⊔ W', r v ∈ M ⊔ W' :=
  sup_inv C.hs C.hMinv C.hW'inv

theorem ctx_disj (C : RaiseCtx Φ Sing TS ρ p Rh X m M W') : Disjoint (X m) (M ⊔ W') :=
  C.hsplit.disj_W

theorem ctx_disj' (C : RaiseCtx Φ Sing TS ρ p Rh X m M W') : Disjoint (X m) W' :=
  C.hsplit.disj_W.mono_right le_sup_right

theorem ctx_M_le_perp (C : RaiseCtx Φ Sing TS ρ p Rh X m M W') : M ≤ Φ.perp (X m) :=
  fun μ hμ w hw => C.hsplit.perp_WM w hw μ hμ

theorem fk_low {x : H} (hx : x ∈ flagKernel ρ (isoCompletion Φ X m)) {k : ℕ} (hk : k < m)
    {v : V} (hv : v ∈ X (k + 1)) : ρ x v - v ∈ X k := by
  have h := hx.2 k v (by rw [isoCompletion_of_le (by omega)]; exact hv)
  rwa [isoCompletion_of_le hk.le] at h

theorem fk_mid {x : H} (hx : x ∈ flagKernel ρ (isoCompletion Φ X m)) {v : V}
    (hv : v ∈ Φ.perp (X m)) : ρ x v - v ∈ X m := by
  have h1 : isoCompletion Φ X m (m + 1) = Φ.perp (X m) := by
    have := isoCompletion_perp (F := Φ) (X := X) (m := m) (le_refl m)
    rwa [show 2 * m + 1 - m = m + 1 by omega] at this
  have h := hx.2 m v (by rw [h1]; exact hv)
  rwa [isoCompletion_of_le le_rfl] at h

theorem fs_apply {y : H} (hy : y ∈ flagStab ρ (isoCompletion Φ X m)) {k : ℕ} (hk : k ≤ m)
    {v : V} (hv : v ∈ X k) : ρ y v ∈ X k := by
  have h := hy k v (by rw [isoCompletion_of_le hk]; exact hv)
  rw [isoCompletion_of_le hk] at h
  exact h.1

theorem comm_sub_one {x : H} (hxc : CommR ρ Rh x) (hs : Rh ≤ semilinGroup F V) :
    ∀ r ∈ Rh, ∀ v, r ((ρ x - 1) v) = (ρ x - 1) (r v) := by
  intro r hr v
  simp only [LinearMap.sub_apply, Module.End.one_apply]
  rw [semilin_sub (hs hr), hxc r hr v]

end Ctx

end FormsCases

end CFSG.LieType.ChevTwo.OppCl
