module

public import CFSG.Quasithin.Background.E2TwoProofFam
public import CFSG.Milestones.AT_alternating_automorphism_permutation
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix

public section

namespace CFSG.Quasithin.B69K

namespace AltPl

theorem eq_of_conj_eq {m : ℕ} (hm4 : 4 ≤ m) {σ τ : Equiv.Perm (Fin m)}
    (h : ∀ g : alternatingGroup (Fin m),
      σ * (g : Equiv.Perm (Fin m)) * σ⁻¹ = τ * (g : Equiv.Perm (Fin m)) * τ⁻¹) : σ = τ := by
  have hc : σ⁻¹ * τ ∈
      Subgroup.centralizer (alternatingGroup (Fin m) : Set (Equiv.Perm (Fin m))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : σ * x * σ⁻¹ = τ * x * τ⁻¹ := h ⟨x, hx⟩
    have key : σ⁻¹ * τ * x * (σ⁻¹ * τ)⁻¹ = x := by
      calc σ⁻¹ * τ * x * (σ⁻¹ * τ)⁻¹ = σ⁻¹ * (τ * x * τ⁻¹) * σ := by group
        _ = σ⁻¹ * (σ * x * σ⁻¹) * σ := by rw [← hx']
        _ = x := by group
    rw [mul_inv_eq_iff_eq_mul] at key
    exact key.symm
  have hcard : 4 ≤ Nat.card (Fin m) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    exact hm4
  rw [CFSG.ComponentClassification.PresentationLocal.centralizer_alternatingGroup_eq_bot hcard,
    Subgroup.mem_bot] at hc
  exact inv_mul_eq_one.mp hc

section Aut

variable {X : Type} [Group X] [Finite X] {K T M : Subgroup X}

theorem autC_mul_apply {C : Type} [Group C] (hX : E2P.ASHyp K T M) (e : ↥K ≃* C) (t s : X)
    (c : C) : hX.autC e (t * s) c = hX.autC e t (hX.autC e s c) := by
  rw [E2P.ASHyp.autC_apply hX e (t * s) c, E2P.ASHyp.autC_apply hX e t (hX.autC e s c),
    E2P.ASHyp.autC_apply hX e s c, MulEquiv.symm_apply_apply]
  congr 1
  apply Subtype.ext
  dsimp only
  group

theorem autC_one_apply {C : Type} [Group C] (hX : E2P.ASHyp K T M) (e : ↥K ≃* C) (c : C) :
    hX.autC e 1 c = c := by
  rw [E2P.ASHyp.autC_apply hX e 1 c]
  conv_rhs => rw [← e.apply_symm_apply c]
  congr 1
  apply Subtype.ext
  simp

theorem autC_inv_apply {C : Type} [Group C] (hX : E2P.ASHyp K T M) (e : ↥K ≃* C) (t : X)
    (c : C) : hX.autC e t (hX.autC e t⁻¹ c) = c := by
  rw [← autC_mul_apply hX e t t⁻¹ c, mul_inv_cancel, autC_one_apply hX e c]

noncomputable def permGroup {m : ℕ} (hX : E2P.ASHyp K T M)
    (e : ↥K ≃* alternatingGroup (Fin m)) : Subgroup (Equiv.Perm (Fin m)) where
  carrier := {σ | ∃ t ∈ T, ∀ g : alternatingGroup (Fin m),
    ((hX.autC e t g : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) =
      σ * (g : Equiv.Perm (Fin m)) * σ⁻¹}
  one_mem' := ⟨1, T.one_mem, fun g => by rw [autC_one_apply hX e g]; simp⟩
  mul_mem' := by
    rintro σ₁ σ₂ ⟨t₁, ht₁, h₁⟩ ⟨t₂, ht₂, h₂⟩
    refine ⟨t₁ * t₂, T.mul_mem ht₁ ht₂, fun g => ?_⟩
    rw [autC_mul_apply hX e t₁ t₂ g, h₁, h₂]
    group
  inv_mem' := by
    rintro σ ⟨t, ht, h⟩
    refine ⟨t⁻¹, T.inv_mem ht, fun g => ?_⟩
    have hg := h (hX.autC e t⁻¹ g)
    rw [autC_inv_apply hX e t g] at hg
    rw [inv_inv, hg]
    group

theorem pow_rep {m : ℕ} (hX : E2P.ASHyp K T M) (e : ↥K ≃* alternatingGroup (Fin m)) (t : X)
    {σ : Equiv.Perm (Fin m)}
    (hσ : ∀ g : alternatingGroup (Fin m),
      ((hX.autC e t g : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) =
        σ * (g : Equiv.Perm (Fin m)) * σ⁻¹)
    (n : ℕ) : ∀ g : alternatingGroup (Fin m),
      ((hX.autC e (t ^ n) g : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) =
        σ ^ n * (g : Equiv.Perm (Fin m)) * (σ ^ n)⁻¹ := by
  induction n with
  | zero =>
    intro g
    simp only [pow_zero, autC_one_apply hX e g, one_mul, inv_one, mul_one]
  | succ n ih =>
    intro g
    rw [pow_succ t n, autC_mul_apply hX e (t ^ n) t g, ih (hX.autC e t g), hσ g, pow_succ σ n]
    simp only [mul_assoc, mul_inv_rev]

theorem isPGroup_permGroup {m : ℕ} (hX : E2P.ASHyp K T M) (hm4 : 4 ≤ m)
    (e : ↥K ≃* alternatingGroup (Fin m)) : IsPGroup 2 (permGroup hX e) := by
  intro g
  obtain ⟨t, ht, hrep⟩ := g.2
  obtain ⟨k, hk⟩ := hX.minPar.isSylow.2.1 ⟨t, ht⟩
  have htk : t ^ 2 ^ k = 1 := by
    have h := congrArg Subtype.val hk
    simpa using h
  have hpow := pow_rep hX e t hrep (2 ^ k)
  rw [htk] at hpow
  have h1 : ∀ x : alternatingGroup (Fin m), (x : Equiv.Perm (Fin m)) =
      (g : Equiv.Perm (Fin m)) ^ 2 ^ k * (x : Equiv.Perm (Fin m)) *
        ((g : Equiv.Perm (Fin m)) ^ 2 ^ k)⁻¹ := by
    intro x
    have h := hpow x
    rwa [autC_one_apply hX e x] at h
  have hcent : (g : Equiv.Perm (Fin m)) ^ 2 ^ k = 1 := by
    apply eq_of_conj_eq hm4
    intro x
    simp only [one_mul, inv_one, mul_one]
    exact (h1 x).symm
  refine ⟨k, Subtype.ext ?_⟩
  simpa using hcent

theorem exists_rep {m : ℕ} (hX : E2P.ASHyp K T M) (hm : m = 5 ∨ 7 ≤ m)
    (e : ↥K ≃* alternatingGroup (Fin m)) {t : X} (ht : t ∈ T) :
    ∃ σ ∈ permGroup hX e, ∀ g : alternatingGroup (Fin m),
      ((hX.autC e t g : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) =
        σ * (g : Equiv.Perm (Fin m)) * σ⁻¹ := by
  obtain ⟨σ, hσ⟩ := CFSG.Milestones.alternating_automorphism_permutation hm (hX.autC e t)
  exact ⟨σ, ⟨t, ht, hσ⟩, hσ⟩

theorem invariant {m : ℕ} (hX : E2P.ASHyp K T M) (hm : m = 5 ∨ 7 ≤ m)
    (e : ↥K ≃* alternatingGroup (Fin m)) {Q : Subgroup (alternatingGroup (Fin m))}
    (hcl : ∀ τ ∈ permGroup hX e, ∀ g ∈ Q, ∀ h : τ * (g : Equiv.Perm (Fin m)) * τ⁻¹ ∈
      alternatingGroup (Fin m), (⟨τ * (g : Equiv.Perm (Fin m)) * τ⁻¹, h⟩ :
        alternatingGroup (Fin m)) ∈ Q) :
    ∀ t ∈ T, Q.map (hX.autC e t).toMonoidHom = Q := by
  have hmem : ∀ t ∈ T, ∀ g ∈ Q, hX.autC e t g ∈ Q := by
    intro t ht g hg
    obtain ⟨σ, hσS, hσ⟩ := exists_rep hX hm e ht
    have h : σ * (g : Equiv.Perm (Fin m)) * σ⁻¹ ∈ alternatingGroup (Fin m) := by
      rw [← hσ g]
      exact (hX.autC e t g).2
    have heq : hX.autC e t g = ⟨σ * (g : Equiv.Perm (Fin m)) * σ⁻¹, h⟩ :=
      Subtype.ext (hσ g)
    rw [heq]
    exact hcl σ hσS g hg h
  intro t ht
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact hmem t ht g hg
  · intro g hg
    exact Subgroup.mem_map.mpr ⟨hX.autC e t⁻¹ g, hmem t⁻¹ (T.inv_mem ht) g hg,
      autC_inv_apply hX e t g⟩

theorem sub_pull {m : ℕ} (hX : E2P.ASHyp K T M) (e : ↥K ≃* alternatingGroup (Fin m))
    {Q : Subgroup (alternatingGroup (Fin m))}
    (hcl : ∀ u : alternatingGroup (Fin m), (u : Equiv.Perm (Fin m)) ∈ permGroup hX e → u ∈ Q) :
    T ⊓ K ≤ (Q.map e.symm.toMonoidHom).map K.subtype := by
  rintro x ⟨hxT, hxK⟩
  have hA : ∀ c : alternatingGroup (Fin m),
      hX.autC e x c = e ⟨x, hxK⟩ * c * (e ⟨x, hxK⟩)⁻¹ := by
    intro c
    have h1 : hX.autC e x c = e (⟨x, hxK⟩ * e.symm c * (⟨x, hxK⟩ : ↥K)⁻¹) := rfl
    rw [h1]
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hgS : ((e ⟨x, hxK⟩ : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) ∈
      permGroup hX e := by
    refine ⟨x, hxT, fun c => ?_⟩
    rw [hA c]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  refine Subgroup.mem_map.mpr ⟨e.symm (e ⟨x, hxK⟩),
    Subgroup.mem_map.mpr ⟨e ⟨x, hxK⟩, hcl _ hgS, rfl⟩, ?_⟩
  simp

end Aut

end AltPl

theorem false_of_alt_pair {X : Type} [Group X] [Finite X] {K T M : Subgroup X}
    (hX : E2P.ASHyp K T M) {m : ℕ} (hm : m = 5 ∨ 7 ≤ m) (e : ↥K ≃* alternatingGroup (Fin m))
    (hpair : ∀ T' : Subgroup (Equiv.Perm (Fin m)), IsPGroup 2 T' →
      ∃ Q₀ Q₁ : Subgroup (alternatingGroup (Fin m)), Q₀ ≠ ⊤ ∧ Q₁ ≠ ⊤ ∧ Q₀ ⊔ Q₁ = ⊤ ∧
        ∀ Q ∈ ({Q₀, Q₁} : Set (Subgroup (alternatingGroup (Fin m)))),
          (∀ τ ∈ T', ∀ g ∈ Q, ∀ h : τ * (g : Equiv.Perm (Fin m)) * τ⁻¹ ∈ alternatingGroup (Fin m),
            (⟨τ * (g : Equiv.Perm (Fin m)) * τ⁻¹, h⟩ : alternatingGroup (Fin m)) ∈ Q) ∧
          (∀ u : alternatingGroup (Fin m), (u : Equiv.Perm (Fin m)) ∈ T' → u ∈ Q)) :
    False := by
  have hm4 : 4 ≤ m := by
    rcases hm with h | h <;> omega
  obtain ⟨Q₀, Q₁, hQ₀, hQ₁, hsup, hQ⟩ :=
    hpair (AltPl.permGroup hX e) (AltPl.isPGroup_permGroup hX hm4 e)
  obtain ⟨h0₁, h0₂⟩ := hQ Q₀ (Set.mem_insert _ _)
  obtain ⟨h1₁, h1₂⟩ := hQ Q₁ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  refine hX.false_of_pair (E2P.pull_le e Q₀) (E2P.pull_le e Q₁)
    (AltPl.sub_pull hX e h0₂) (AltPl.sub_pull hX e h1₂)
    (E2P.pull_ne e hQ₀) (E2P.pull_ne e hQ₁)
    (hX.normalizes_pull e (AltPl.invariant hX hm e h0₁))
    (hX.normalizes_pull e (AltPl.invariant hX hm e h1₁)) ?_
  rw [← E2P.pull_sup, hsup, E2P.pull_top]

end CFSG.Quasithin.B69K

end
