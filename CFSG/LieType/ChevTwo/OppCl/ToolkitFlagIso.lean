module

public import CFSG.LieType.ChevTwo.OppCl.ToolkitBase

public section

namespace CFSG.LieType.ChevTwo.OppCl.TK

open CFSG.Open CFSG.LieType.BorelTits

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {H : Type} [Group H]

theorem perp_semiIso_inv (Φ : ReflForm F V) {r : Equiv.Perm V} (hΦ : SemiIso Φ r)
    {W : Submodule F V} (hW : ∀ w ∈ W, r⁻¹ w ∈ W) : ∀ v ∈ Φ.perp W, r v ∈ Φ.perp W := by
  obtain ⟨τ, hτ⟩ := hΦ
  intro v hv
  rw [ReflForm.mem_perp] at hv ⊢
  intro w hw
  have h := hτ (r⁻¹ w) v
  rw [perm_apply_inv, hv (r⁻¹ w) (hW w hw), map_zero] at h
  exact h

theorem relFix_semiIso_map (Φ : ReflForm F V) (ρ : H →* Module.End F V) (Q : Subgroup H)
    {W : Submodule F V} {s : Equiv.Perm V} (hs : s ∈ semilinGroup F V) (hsΦ : SemiIso Φ s)
    (hsN : NormQ ρ s⁻¹ Q) (hsW : ∀ w ∈ W, s w ∈ W) (hs'W : ∀ w ∈ W, s⁻¹ w ∈ W) :
    ∀ v ∈ relFix Φ ρ W Q, s v ∈ relFix Φ ρ W Q := by
  intro v hv
  rw [mem_relFix] at hv ⊢
  refine ⟨perp_semiIso_inv Φ hsΦ hs'W v hv.1, fun g hg => ?_⟩
  obtain ⟨x', hx', hx'eq⟩ := hsN g hg
  have hgv : ρ g (s v) = s (ρ x' v) := by
    have h := hx'eq (s v)
    rw [perm_inv_apply] at h
    rw [← h, perm_apply_inv]
  rw [hgv, ← semilin_map_sub hs]
  exact hsW _ (hv.2 x' hx')

theorem isoSeq_inv_aux (Φ : ReflForm F V) (ρ : H →* Module.End F V) (Q : Subgroup H) (k : ℕ) :
    ∀ r : Equiv.Perm V, r ∈ semilinGroup F V → SemiIso Φ r → NormQ ρ r Q → NormQ ρ r⁻¹ Q →
      ∀ v ∈ isoSeq Φ ρ Q k, r v ∈ isoSeq Φ ρ Q k := by
  induction k with
  | zero =>
    intro r hr _ _ _ v hv
    rw [isoSeq_zero, Submodule.mem_bot] at hv ⊢
    rw [hv]
    exact semilin_map_zero hr
  | succ k ih =>
    intro r hr hΦ h1 h2 v hv
    have hrW : ∀ w ∈ isoSeq Φ ρ Q k, r w ∈ isoSeq Φ ρ Q k := ih r hr hΦ h1 h2
    have hr'W : ∀ w ∈ isoSeq Φ ρ Q k, r⁻¹ w ∈ isoSeq Φ ρ Q k :=
      ih r⁻¹ (inv_mem hr) (semiIso_inv Φ hΦ) h2 (by rw [inv_inv]; exact h1)
    have hA := relFix_semiIso_map Φ ρ Q hr hΦ h2 hrW hr'W
    have hB := relFix_semiIso_map Φ ρ Q (inv_mem hr) (semiIso_inv Φ hΦ)
      (by rw [inv_inv]; exact h1) hr'W (fun w hw => by rw [inv_inv]; exact hrW w hw)
    rw [isoSeq_succ] at hv ⊢
    unfold isoNext at hv ⊢
    exact ⟨hA v hv.1, perp_semiIso_inv Φ hΦ hB v hv.2⟩

theorem isoFlag_inv (Φ : ReflForm F V) (ρ : H →* Module.End F V) (hρ : IsIsometric Φ ρ)
    (r : Equiv.Perm V) (hr : r ∈ semilinGroup F V) (hΦ : SemiIso Φ r) (Q : Subgroup H)
    (h1 : NormQ ρ r Q) (h2 : NormQ ρ r⁻¹ Q) :
    ∀ k, ∀ v ∈ isoFlag Φ ρ Q k, r v ∈ isoFlag Φ ρ Q k := by
  intro k v hv
  have hinv : ∀ j, ∀ w ∈ isoSeq Φ ρ Q j, r⁻¹ w ∈ isoSeq Φ ρ Q j := fun j =>
    isoSeq_inv_aux Φ ρ Q j r⁻¹ (inv_mem hr) (semiIso_inv Φ hΦ) h2 (by rw [inv_inv]; exact h1)
  unfold isoFlag at hv ⊢
  split_ifs at hv ⊢
  · exact isoSeq_inv_aux Φ ρ Q k r hr hΦ h1 h2 v hv
  · exact perp_semiIso_inv Φ hΦ (hinv _) v hv
  · exact Submodule.mem_top

end CFSG.LieType.ChevTwo.OppCl.TK
