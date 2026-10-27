module

public import CFSG.LieType.ChevTwo.OppCl.ToolkitAsmNorm
public import CFSG.LieType.ChevTwo.OppCl.ToolkitAsmFix
import CFSG.LieType.BorelTits.CentralQuotient

public section

namespace CFSG.LieType.ChevTwo.OppCl.TK

open CFSG.Open CFSG.LieType.BorelTits

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {H : Type} [Group H]

theorem oppFixed_of_raise [Finite H] (Z : Subgroup H) [Z.Normal] (hZc : Z ≤ Subgroup.center H)
    (hZo : Nat.Coprime (Nat.card Z) 2) [Finite F] [CharP F 2] [Finite V]
    (P : Equiv.Perm V → Prop) (ρ : H →* Module.End F V) (hρ : Function.Injective ρ)
    (𝔉 : Subgroup H → ℕ → Submodule F V)
    (hnorm : ∀ Q : Subgroup H, IsPGroup 2 Q → Subgroup.normalizer (Q : Set H) ≤ flagStab ρ (𝔉 Q))
    (hker : ∀ Q : Subgroup H, IsPGroup 2 Q → Q ≤ flagKernel ρ (𝔉 Q))
    (hlift : AutLift P (QuotientGroup.mk' Z) ρ)
    (hraise : ∀ p : ℕ, p.Prime → p ≠ 2 → RaiseProp P ρ 𝔉 p) :
    OppositeFixed (H ⧸ Z) := by
  intro p hp hp2 R hR Q hQ0 hQ2 hcore hNtop hRQ hCN
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Qt, hQt2, hQtmap⟩ := exists_isPGroup_map_eq (r := 2) Z hQ2
  obtain ⟨Rh, hRhs, hRhP, hRhp, hRhN, hRhA, hRhB⟩ := hlift p hp hp2 R hR
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  obtain ⟨hxC, hxQ⟩ := Subgroup.mem_inf.mp hx
  rw [← hQtmap] at hxQ
  obtain ⟨xt, hxt, rfl⟩ := Subgroup.mem_map.mp hxQ
  have hRQt : ∀ α ∈ R, (Qt.map (QuotientGroup.mk' Z)).map α.toMonoidHom =
      Qt.map (QuotientGroup.mk' Z) := by
    intro α hα
    rw [hQtmap]
    exact hRQ α hα
  have hNQ : ∀ r ∈ Rh, NormQ ρ r Qt := by
    intro r hr
    obtain ⟨α, hαR, hind⟩ := hRhB r hr
    exact normQ_of_induces Z hZc hZo hρ hQt2 hRQt hαR hind
  have hCommR : CommR ρ Rh xt := commR_of_fixed Z hZo hρ hQt2 hRhB hNQ hxt hxC
  have hxt1 : xt ≠ 1 := fun h => hx1 (by rw [h, map_one])
  obtain ⟨y, hyC, hyN⟩ := hraise p hp hp2 Rh hRhs hRhP hRhp hRhN Qt hQt2 hNQ xt
    (hker Qt hQt2 hxt) hxt1 hCommR
  apply hyN
  apply hnorm Qt hQt2
  rw [normalizer_eq_comap_normalizer_map Z hZc hZo hQt2, Subgroup.mem_comap, hQtmap]
  exact hCN (fixed_of_commR Z hρ hRhA hyC)

end CFSG.LieType.ChevTwo.OppCl.TK
