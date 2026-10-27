module

public import CFSG.LieType.ChevTwo.OppCl.ToolkitBase

public section

namespace CFSG.LieType.ChevTwo.OppCl.TK

open CFSG.Open CFSG.LieType.BorelTits

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

theorem exists_conj_linear {r : Equiv.Perm V} (hr : r ∈ semilinGroup F V) (f : V →ₗ[F] V) :
    ∃ g : V →ₗ[F] V, ∀ v, g v = r (f (r⁻¹ v)) := by
  have hr' : r⁻¹ ∈ semilinGroup F V := inv_mem hr
  obtain ⟨hadd, σ, hσ⟩ := hr
  obtain ⟨hadd', σ', hσ'⟩ := hr'
  have key : ∀ (c : F) (w : V), σ (σ' c) • w = c • w := by
    intro c w
    have h1 : r (r⁻¹ (c • w)) = c • w := perm_apply_inv r _
    rw [hσ' c w, hσ, perm_apply_inv] at h1
    exact h1
  refine ⟨{ toFun := fun v => r (f (r⁻¹ v))
            map_add' := fun u v => ?_
            map_smul' := fun c v => ?_ }, fun v => rfl⟩
  · show r (f (r⁻¹ (u + v))) = r (f (r⁻¹ u)) + r (f (r⁻¹ v))
    rw [hadd' u v, map_add, hadd]
  · show r (f (r⁻¹ (c • v))) = c • r (f (r⁻¹ v))
    rw [hσ' c v, map_smul, hσ, key]

theorem card_smul_eq_self [CharP F 2] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (G : Type) [Group G]
    [Finite G] (hG : IsPGroup p G) (w : V) : Nat.card G • w = w := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hG
  have hodd : Odd (Nat.card G) := by
    rw [hn]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  rw [← Nat.cast_smul_eq_nsmul F, natCast_eq_one_of_odd_of_two_eq_zero hodd
    (CharTwo.two_eq_zero : (2 : F) = 0), one_smul]

theorem exists_invariant_compl [CharP F 2] [Finite V] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (Rh : Subgroup (Equiv.Perm V)) (hs : Rh ≤ semilinGroup F V) (hR : IsPGroup p Rh)
    (W : Submodule F V) (hW : ∀ r ∈ Rh, ∀ v ∈ W, r v ∈ W) :
    ∃ C : Submodule F V, IsCompl W C ∧ ∀ r ∈ Rh, ∀ v ∈ C, r v ∈ C := by
  classical
  obtain ⟨π₀, hπ₀W, hπ₀id⟩ : ∃ π₀ : V →ₗ[F] V, (∀ v, π₀ v ∈ W) ∧ ∀ w ∈ W, π₀ w = w := by
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective W.subtype W.ker_subtype
    refine ⟨W.subtype ∘ₗ g, fun v => (g v).2, fun w hw => ?_⟩
    have := LinearMap.congr_fun hg ⟨w, hw⟩
    simpa using congrArg Subtype.val this
  haveI : Fintype Rh := Fintype.ofFinite Rh
  choose c hc using fun r : Rh => exists_conj_linear (hs r.2) π₀
  let Pi : V →ₗ[F] V := ∑ r : Rh, c r
  have hPi : ∀ v, Pi v = ∑ r : Rh, (r : Equiv.Perm V) (π₀ ((r : Equiv.Perm V)⁻¹ v)) := by
    intro v
    simp only [Pi, LinearMap.sum_apply, hc]
  have hPW : ∀ v, Pi v ∈ W := fun v => by
    rw [hPi]
    exact Submodule.sum_mem _ fun r _ => hW r r.2 _ (hπ₀W _)
  have hPid : ∀ w ∈ W, Pi w = w := by
    intro w hw
    rw [hPi]
    have : ∀ r : Rh, (r : Equiv.Perm V) (π₀ ((r : Equiv.Perm V)⁻¹ w)) = w := by
      intro r
      rw [hπ₀id _ (hW _ (inv_mem r.2) w hw), perm_apply_inv]
    simp only [this, Finset.sum_const, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card]
    exact card_smul_eq_self (F := F) p hp2 Rh hR w
  have hPeq : ∀ s ∈ Rh, ∀ v, Pi (s v) = s (Pi v) := by
    intro s hs' v
    rw [hPi, hPi]
    have hsadd : s (∑ t : Rh, (t : Equiv.Perm V) (π₀ ((t : Equiv.Perm V)⁻¹ v))) =
        ∑ t : Rh, s ((t : Equiv.Perm V) (π₀ ((t : Equiv.Perm V)⁻¹ v))) :=
      map_sum (AddMonoidHom.mk' s (hs hs').1) _ _
    rw [hsadd]
    refine (Fintype.sum_equiv (Equiv.mulLeft (⟨s, hs'⟩ : Rh)) _ _ fun t => ?_).symm
    show s ((t : Equiv.Perm V) (π₀ ((t : Equiv.Perm V)⁻¹ v))) =
      (s * (t : Equiv.Perm V)) (π₀ ((s * (t : Equiv.Perm V))⁻¹ (s v)))
    simp only [mul_inv_rev, Equiv.Perm.mul_apply, perm_inv_apply]
  let Pi' : V →ₗ[F] W := Pi.codRestrict W hPW
  have hcompl : IsCompl W (LinearMap.ker Pi') :=
    LinearMap.isCompl_of_proj fun x => Subtype.ext (hPid x x.2)
  have hker : LinearMap.ker Pi' = LinearMap.ker Pi := LinearMap.ker_codRestrict _ _ _
  refine ⟨LinearMap.ker Pi', hcompl, fun r hr v hv => ?_⟩
  rw [hker, LinearMap.mem_ker] at hv ⊢
  rw [hPeq r hr, hv, semilin_map_zero (hs hr)]

end CFSG.LieType.ChevTwo.OppCl.TK
