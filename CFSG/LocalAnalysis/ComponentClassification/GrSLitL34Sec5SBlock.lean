module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34Make
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL2Outer

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.GrSLit

@[expose] def Pres (g : Equiv.Perm (Fin 42)) : Prop :=
  ∀ i : Fin 42, ((g i).val < 21 ↔ i.val < 21)

@[expose] def Swaps (g : Equiv.Perm (Fin 42)) : Prop :=
  ∀ i : Fin 42, ((g i).val < 21 ↔ ¬ i.val < 21)

theorem pres_mul {g h : Equiv.Perm (Fin 42)} (hg : Pres g) (hh : Pres h) : Pres (g * h) :=
  fun i => (hg (h i)).trans (hh i)

theorem swaps_of_pres_swaps {g h : Equiv.Perm (Fin 42)} (hg : Pres g) (hh : Swaps h) :
    Swaps (g * h) :=
  fun i => (hg (h i)).trans (hh i)

theorem swaps_of_swaps_pres {g h : Equiv.Perm (Fin 42)} (hg : Swaps g) (hh : Pres h) :
    Swaps (g * h) :=
  fun i => (hg (h i)).trans (not_congr (hh i))

theorem pres_of_swaps_swaps {g h : Equiv.Perm (Fin 42)} (hg : Swaps g) (hh : Swaps h) :
    Pres (g * h) :=
  fun i => (hg (h i)).trans ((not_congr (hh i)).trans not_not)

theorem pres_inv {g : Equiv.Perm (Fin 42)} (hg : Pres g) : Pres g⁻¹ := fun i => by
  have h := hg (g⁻¹ i)
  rw [show g (g⁻¹ i) = i from g.apply_symm_apply i] at h
  exact h.symm

theorem swaps_inv {g : Equiv.Perm (Fin 42)} (hg : Swaps g) : Swaps g⁻¹ := fun i => by
  have h := hg (g⁻¹ i)
  rw [show g (g⁻¹ i) = i from g.apply_symm_apply i] at h
  constructor
  · intro h1 h2
    exact (h.mp h2) h1
  · intro h1
    by_contra h2
    exact h1 (h.mpr h2)

theorem not_pres_of_swaps {g : Equiv.Perm (Fin 42)} (hs : Swaps g) : ¬ Pres g := fun hp => by
  have h1 := hp 0
  have h2 := hs 0
  simp only [Fin.val_zero, Nat.ofNat_pos, iff_true, not_true_eq_false, iff_false] at h1 h2
  exact h2 h1

@[expose] def blockGroup : Subgroup (Equiv.Perm (Fin 42)) where
  carrier := {g | Pres g ∨ Swaps g}
  one_mem' := Or.inl fun _ => Iff.rfl
  mul_mem' := by
    rintro g h (hg | hg) (hh | hh)
    · exact Or.inl (pres_mul hg hh)
    · exact Or.inr (swaps_of_pres_swaps hg hh)
    · exact Or.inr (swaps_of_swaps_pres hg hh)
    · exact Or.inl (pres_of_swaps_swaps hg hh)
  inv_mem' := by
    rintro g (hg | hg)
    · exact Or.inl (pres_inv hg)
    · exact Or.inr (swaps_inv hg)

theorem pres_rho (A : GL (Fin 3) F4) : Pres (rho A) := by
  intro i
  rw [rho_apply, rhoFun]
  split_ifs with h
  · have := vIdx_lt (Matrix.mulVec (A : Matrix (Fin 3) (Fin 3) F4) (vecOf i))
    simp only [h, iff_true]
    exact this
  · simp only [h, iff_false, not_lt]
    omega

theorem pres_g₅ : Pres g₅ := by
  intro i
  change (g5Fun i).val < 21 ↔ i.val < 21
  have := vIdx_lt (fun k => vecOf i k ^ 2)
  have hi := i.isLt
  simp only [g5Fun]
  constructor
  · intro h
    by_contra h'
    have : i.val / 21 = 1 := by omega
    omega
  · intro h
    have : i.val / 21 = 0 := by omega
    omega

theorem swaps_g₆ : Swaps g₆ := by
  intro i
  change (g6Fun i).val < 21 ↔ ¬ i.val < 21
  have hi := i.isLt
  unfold g6Fun
  split_ifs with h
  · simp only [h, not_true_eq_false, iff_false, not_lt]
    omega
  · simp only [h, not_false_eq_true, iff_true]
    omega

theorem R_le_blockGroup : R ≤ blockGroup := by
  refine (closure_le _).mpr ?_
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (pres_rho _)
  · exact Or.inl (pres_rho _)
  · exact Or.inl (pres_rho _)
  · exact Or.inl (pres_rho _)
  · exact Or.inl pres_g₅
  · exact Or.inr swaps_g₆

theorem swaps_r₄ : Swaps r₄ := swaps_of_pres_swaps pres_g₅ swaps_g₆

theorem pres_conj_iff {a b : Equiv.Perm (Fin 42)} (ha : a ∈ blockGroup) (hb : b ∈ blockGroup) :
    Pres (a * b * a⁻¹) ↔ Pres b := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact ⟨fun _ => hb, fun _ => pres_mul (pres_mul ha hb) (pres_inv ha)⟩
  · have hs : Swaps (a * b * a⁻¹) :=
      swaps_of_swaps_pres (swaps_of_pres_swaps ha hb) (pres_inv ha)
    exact ⟨fun h => absurd h (not_pres_of_swaps hs), fun h => absurd h (not_pres_of_swaps hb)⟩
  · exact ⟨fun _ => hb, fun _ => pres_of_swaps_swaps (swaps_of_swaps_pres ha hb) (swaps_inv ha)⟩
  · have hs : Swaps (a * b * a⁻¹) :=
      swaps_of_pres_swaps (pres_of_swaps_swaps ha hb) (swaps_inv ha)
    exact ⟨fun h => absurd h (not_pres_of_swaps hs), fun h => absurd h (not_pres_of_swaps hb)⟩

theorem pres_r₄_mul_iff {b : Equiv.Perm (Fin 42)} (hb : b ∈ blockGroup) :
    Pres (r₄ * b) ↔ ¬ Pres b := by
  rcases hb with hb | hb
  · exact ⟨fun h => absurd h (not_pres_of_swaps (swaps_of_swaps_pres swaps_r₄ hb)),
      fun h => absurd hb h⟩
  · exact ⟨fun _ => not_pres_of_swaps hb, fun _ => pres_of_swaps_swaps swaps_r₄ hb⟩

theorem not_pres_conj_r₄ {a b : Equiv.Perm (Fin 42)} (ha : a ∈ R) (hb : b ∈ R) :
    a * b * a⁻¹ ≠ r₄ * b := by
  intro h
  have h1 := pres_conj_iff (R_le_blockGroup ha) (R_le_blockGroup hb)
  rw [h, pres_r₄_mul_iff (R_le_blockGroup hb)] at h1
  exact not_iff_self h1

variable {G : Type} [Group G] [Finite G]

theorem false_of_unitary_conj {K : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hL : IsL34Type (K ⧸ Open.fusionZStar K)) {x s w : G} (hx : IsL34Unitary K x)
    (hs : s ∈ normalizer (K : Set G)) (hw : w ∈ normalizer (K : Set G))
    (hsw : s * w * s⁻¹ = x * w) : False := by
  obtain ⟨ρ, hρ⟩ := HSFLit.AutL34.exists_real_unitary hK hL hx
  have h1 : (⟨s, hs⟩ : ↥(normalizer (K : Set G))) * ⟨w, hw⟩ * ⟨s, hs⟩⁻¹ =
      ⟨x, hx.1⟩ * ⟨w, hw⟩ := Subtype.ext hsw
  have h2 := congrArg ρ.φ h1
  rw [map_mul, map_mul, map_inv, map_mul, hρ] at h2
  exact not_pres_conj_r₄ (ρ.mem_R _) (ρ.mem_R _) h2

theorem false_of_l2_conj
    {a x : G} {J R : Subgroup G} (hT : GSUnbalancingTriple a x J)
    (htype : IsL2Type 5 (J ⧸ pPrimeCore 2 J) ∨ IsL2Type 7 (J ⧸ pPrimeCore 2 J))
    (hR : IsPGroup 2 R) (hRN : R ≤ normalizer (J : Set G)) (hRx : R ≤ centralizer ({x} : Set G))
    {s w : G} (hs : s ∈ R) (hw : w ∈ R) (hsw : s * w * s⁻¹ = x * w) : False := by
  obtain ⟨h1, -⟩ := HSFLit.AutL2.l2UnbalancingAutFact G a x J R hT htype hR
  obtain ⟨hsq, -⟩ := h1 (le_inf hRN hRx)
  have hx : x = s * w * (s * w) * (w⁻¹ * (s * s)⁻¹ * w⁻¹⁻¹) * (w * w)⁻¹ := by
    have e : x = s * w * s⁻¹ * w⁻¹ := by rw [hsw]; group
    rw [e]
    group
  have hC1 := hsq (s * w) (mul_mem hs hw)
  have hC2 : w⁻¹ * (s * s)⁻¹ * w⁻¹⁻¹ ∈ coreActionKernel J :=
    conj_mem_coreActionKernel (inv_mem (hRN hw)) (inv_mem (hsq s hs))
  have hC3 : (w * w)⁻¹ ∈ coreActionKernel J := inv_mem (hsq w hw)
  have hxC : x ∈ coreActionKernel J := by
    rw [hx]
    exact mul_mem (mul_mem hC1 hC2) hC3
  exact HSFLit.AutL2.l2UnbalancingOuter G a x J hT htype 1 (one_mem _) (by rwa [inv_one, one_mul])

end CFSG.ComponentClassification.GrSLit.GrS5S
