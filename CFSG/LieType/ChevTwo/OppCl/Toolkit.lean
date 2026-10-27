module

public import CFSG.LieType.ChevTwo.OppCl.Defs
public import CFSG.LieType.ChevTwo.Defs
public import CFSG.LieType.BorelTits.OrthogonalSingular
import CFSG.LieType.ChevTwo.OppositeFixedExcBase
import CFSG.LieType.ChevTwo.OppCl.ToolkitAutLift
import CFSG.LieType.ChevTwo.OppCl.ToolkitAssembly
import CFSG.LieType.ChevTwo.OppCl.ToolkitSwap
import CFSG.LieType.ChevTwo.OppCl.ToolkitFixCoset
import CFSG.LieType.ChevTwo.OppCl.ToolkitFlagFix
import CFSG.LieType.ChevTwo.OppCl.ToolkitFlagSing

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits

section Generic

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
variable {H K : Type} [Group H] [Group K]

theorem oppositeFixed_of_mulEquiv {K' : Type} [Group K'] (e : K ≃* K') (h : OppositeFixed K) :
    OppositeFixed K' := CFSG.LieType.ChevTwo.oppositeFixed_of_mulEquiv e.symm h

theorem autLift_of_induced [Finite V] [Finite K] {π : H →* K} {ρ : H →* Module.End F V}
    (P : Equiv.Perm V → Prop) (hP1 : P 1) (hPm : ∀ r s, P r → P s → P (r * s))
    (hPi : ∀ r, P r → P r⁻¹) (p : ℕ) [Fact p.Prime] (R : Subgroup (MulAut K))
    (hR : IsPGroup p R)
    (hind : ∀ α ∈ R, ∃ r : Equiv.Perm V, r ∈ semilinGroup F V ∧ P r ∧ Induces π ρ r α) :
    ∃ Rh : Subgroup (Equiv.Perm V), Rh ≤ semilinGroup F V ∧ (∀ r ∈ Rh, P r) ∧ IsPGroup p Rh ∧
      (∀ r ∈ Rh, NormH ρ r) ∧ (∀ α ∈ R, ∃ r ∈ Rh, Induces π ρ r α) ∧
      (∀ r ∈ Rh, ∃ α ∈ R, Induces π ρ r α) :=
  TK.autLift_of_induced P hP1 hPm hPi p R hR hind

theorem oppFixed_of_raise [Finite H] (Z : Subgroup H) [Z.Normal] (hZc : Z ≤ Subgroup.center H)
    (hZo : Nat.Coprime (Nat.card Z) 2) [Finite F] [CharP F 2] [Finite V]
    (P : Equiv.Perm V → Prop) (ρ : H →* Module.End F V) (hρ : Function.Injective ρ)
    (𝔉 : Subgroup H → ℕ → Submodule F V)
    (hnorm : ∀ Q : Subgroup H, IsPGroup 2 Q → Subgroup.normalizer (Q : Set H) ≤ flagStab ρ (𝔉 Q))
    (hker : ∀ Q : Subgroup H, IsPGroup 2 Q → Q ≤ flagKernel ρ (𝔉 Q))
    (hlift : AutLift P (QuotientGroup.mk' Z) ρ)
    (hraise : ∀ p : ℕ, p.Prime → p ≠ 2 → RaiseProp P ρ 𝔉 p) :
    OppositeFixed (H ⧸ Z) :=
  TK.oppFixed_of_raise Z hZc hZo P ρ hρ 𝔉 hnorm hker hlift hraise

end Generic

section Toolkit

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

theorem exists_invariant_compl [CharP F 2] [Finite V] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (Rh : Subgroup (Equiv.Perm V)) (hs : Rh ≤ semilinGroup F V) (hR : IsPGroup p Rh)
    (W : Submodule F V) (hW : ∀ r ∈ Rh, ∀ v ∈ W, r v ∈ W) :
    ∃ C : Submodule F V, IsCompl W C ∧ ∀ r ∈ Rh, ∀ v ∈ C, r v ∈ C :=
  TK.exists_invariant_compl p hp2 Rh hs hR W hW

theorem exists_equivariant_swap [CharP F 2] [Finite V] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (Rh : Subgroup (Equiv.Perm V)) (hs : Rh ≤ semilinGroup F V) (hR : IsPGroup p Rh)
    (A B D : Submodule F V) (hA : ∀ r ∈ Rh, ∀ v ∈ A, r v ∈ A) (hB : ∀ r ∈ Rh, ∀ v ∈ B, r v ∈ B)
    (hD : ∀ r ∈ Rh, ∀ v ∈ D, r v ∈ D) (hDB : Disjoint D B)
    (f : V →ₗ[F] V) (hfc : ∀ r ∈ Rh, ∀ v, r (f v) = f (r v)) (hfAB : ∀ v ∈ A, f v ∈ B)
    (hf0 : ∃ v ∈ A, f v ≠ 0) :
    ∃ g : V →ₗ[F] V, (∀ r ∈ Rh, ∀ v, r (g v) = g (r v)) ∧ (∀ v, g v ∈ A) ∧ (∀ v ∈ D, g v = 0) ∧
      ∃ v ∈ B, g v ≠ 0 :=
  TK.exists_equivariant_swap p hp2 Rh hs hR A B D hA hB hD hDB f hfc hfAB hf0

theorem exists_fixed_coset [Finite V] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (Rh : Subgroup (Equiv.Perm V)) (hR : IsPGroup p Rh)
    (G : Subgroup (Equiv.Perm V)) (hG : ∀ r ∈ Rh, ∀ g ∈ G, r * g * r⁻¹ ∈ G)
    (N : Subgroup (Equiv.Perm V)) (hNG : N ≤ G) (hNn : (N.subgroupOf G).Normal)
    (hN2 : IsPGroup 2 N) (g : Equiv.Perm V) (hgG : g ∈ G)
    (hg : ∀ r ∈ Rh, g⁻¹ * (r * g * r⁻¹) ∈ N) :
    ∃ c ∈ G, (∀ r ∈ Rh, r * c = c * r) ∧ c⁻¹ * g ∈ N :=
  TK.exists_fixed_coset p hp2 Rh hR G hG N hNG hNn hN2 g hgG hg

theorem exists_raising [CharP F 2] [Finite V] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (Rh : Subgroup (Equiv.Perm V)) (hs : Rh ≤ semilinGroup F V) (hR : IsPGroup p Rh)
    (Fl : ℕ → Submodule F V) (hFl0 : Fl 0 = ⊥) (hmono : Monotone Fl)
    (hinv : ∀ r ∈ Rh, ∀ k, ∀ v ∈ Fl k, r v ∈ Fl k) (W D : Submodule F V) (hFW : ∀ k, Fl k ≤ W)
    (hD : ∀ r ∈ Rh, ∀ v ∈ D, r v ∈ D) (hWD : Disjoint W D)
    (N : V →ₗ[F] V) (hN : ∀ k, ∀ v ∈ Fl (k + 1), N v ∈ Fl k)
    (hNc : ∀ r ∈ Rh, ∀ v, r (N v) = N (r v)) (hN0 : ∃ k, ∃ v ∈ Fl k, N v ≠ 0) :
    ∃ (g : V →ₗ[F] V) (k : ℕ), (∀ r ∈ Rh, ∀ v, r (g v) = g (r v)) ∧ (∀ v, g (g v) = 0) ∧
      (∀ v, g v ∈ W) ∧ (∀ v ∈ D, g v = 0) ∧ ∃ v ∈ Fl k, g v ∉ Fl k :=
  TK.exists_raising p hp2 Rh hs hR Fl hFl0 hmono hinv W D hFW hD hWD N hN hNc hN0

variable {H : Type} [Group H]

theorem fixFlag_inv (ρ : H →* Module.End F V) (r : Equiv.Perm V) (hr : r ∈ semilinGroup F V)
    (Q : Subgroup H) (h1 : NormQ ρ r Q) (h2 : NormQ ρ r⁻¹ Q) :
    ∀ k, ∀ v ∈ fixFlag ρ Q k, r v ∈ fixFlag ρ Q k :=
  TK.fixFlag_inv ρ r hr Q h1 h2

theorem isoFlag_inv (Φ : ReflForm F V) (ρ : H →* Module.End F V) (hρ : IsIsometric Φ ρ)
    (r : Equiv.Perm V) (hr : r ∈ semilinGroup F V) (hΦ : SemiIso Φ r) (Q : Subgroup H)
    (h1 : NormQ ρ r Q) (h2 : NormQ ρ r⁻¹ Q) :
    ∀ k, ∀ v ∈ isoFlag Φ ρ Q k, r v ∈ isoFlag Φ ρ Q k :=
  TK.isoFlag_inv Φ ρ hρ r hr hΦ Q h1 h2

theorem singFlag_inv (Φ : QuadForm F V) (ρ : H →* Module.End F V)
    (hQ : ∀ h v, Φ.Q (ρ h v) = Φ.Q v) (r : Equiv.Perm V) (hr : r ∈ semilinGroup F V)
    (hΦ : SemiIsoQ Φ r) (Q : Subgroup H) (h1 : NormQ ρ r Q) (h2 : NormQ ρ r⁻¹ Q) :
    ∀ k, ∀ v ∈ singFlag Φ ρ Q k, r v ∈ singFlag Φ ρ Q k :=
  TK.singFlag_inv Φ ρ hQ r hr hΦ Q h1 h2

end Toolkit

end CFSG.LieType.ChevTwo.OppCl
