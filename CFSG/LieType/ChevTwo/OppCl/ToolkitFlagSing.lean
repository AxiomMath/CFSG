module

public import CFSG.LieType.ChevTwo.OppCl.ToolkitFlagIso
public import CFSG.LieType.BorelTits.OrthogonalSingular

public section

namespace CFSG.LieType.ChevTwo.OppCl.TK

open CFSG.Open CFSG.LieType.BorelTits

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {H : Type} [Group H]

theorem semiIso_polar_of_semiIsoQ (Φ : QuadForm F V) {r : Equiv.Perm V}
    (hr : r ∈ semilinGroup F V) (hΦ : SemiIsoQ Φ r) : SemiIso Φ.polar r := by
  obtain ⟨τ, hτ⟩ := hΦ
  refine ⟨τ, fun u v => ?_⟩
  have h := Φ.Q_add (r u) (r v)
  rw [← semilin_map_add hr u v] at h
  simp only [hτ] at h
  rw [Φ.Q_add u v, map_add, map_add] at h
  linear_combination -h

theorem singSeq_map_of_semiIsoQ (Φ : QuadForm F V) (ρ : H →* Module.End F V) (Q : Subgroup H)
    {s : Equiv.Perm V} (hs : s ∈ semilinGroup F V) (hsΦ : SemiIsoQ Φ s)
    (hsN : NormQ ρ s Q) (hs'N : NormQ ρ s⁻¹ Q) :
    ∀ j, ∀ w ∈ singSeq Φ ρ Q j, s w ∈ singSeq Φ ρ Q j := by
  have hpol : SemiIso Φ.polar s := semiIso_polar_of_semiIsoQ Φ hs hsΦ
  obtain ⟨τ, hτ⟩ := hsΦ
  intro j w hw
  have hw' := mem_singSeq.mp hw
  exact mem_singSeq.mpr ⟨isoSeq_inv_aux Φ.polar ρ Q j s hs hpol hsN hs'N w hw'.1,
    by rw [hτ w, hw'.2, map_zero]⟩

theorem singFlag_inv (Φ : QuadForm F V) (ρ : H →* Module.End F V)
    (hQ : ∀ h v, Φ.Q (ρ h v) = Φ.Q v) (r : Equiv.Perm V) (hr : r ∈ semilinGroup F V)
    (hΦ : SemiIsoQ Φ r) (Q : Subgroup H) (h1 : NormQ ρ r Q) (h2 : NormQ ρ r⁻¹ Q) :
    ∀ k, ∀ v ∈ singFlag Φ ρ Q k, r v ∈ singFlag Φ ρ Q k := by
  intro k v hv
  have hsing : ∀ j, ∀ w ∈ singSeq Φ ρ Q j, r w ∈ singSeq Φ ρ Q j :=
    singSeq_map_of_semiIsoQ Φ ρ Q hr hΦ h1 h2
  have hsing' : ∀ j, ∀ w ∈ singSeq Φ ρ Q j, r⁻¹ w ∈ singSeq Φ ρ Q j :=
    singSeq_map_of_semiIsoQ Φ ρ Q (inv_mem hr) (semiIsoQ_inv Φ hΦ) h2
      (by rw [inv_inv]; exact h1)
  have hPolar : SemiIso Φ.polar r := semiIso_polar_of_semiIsoQ Φ hr hΦ
  unfold singFlag isoCompletion at hv ⊢
  split_ifs at hv ⊢
  · exact hsing k v hv
  · exact perp_semiIso_inv Φ.polar hPolar (hsing' (2 * Module.finrank F V + 1 - k)) v hv
  · exact Submodule.mem_top

end CFSG.LieType.ChevTwo.OppCl.TK
