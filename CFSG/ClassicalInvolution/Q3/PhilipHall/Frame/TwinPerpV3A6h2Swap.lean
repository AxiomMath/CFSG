module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6h2Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6SF

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6h2

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S CFSG.Open CFSG.ClassicalInvolution.Generic

@[expose] def AE6EdgeSwapMem : Prop :=
  ∀ k : Fin 3, ∃ c ∈ ae6ModelV k, ∀ s : Fin 2,
    ae6Word ((ae6KWord ⟨s.val, by omega⟩).map (ae6EdgeSwap k)) ∈ conjSub c ae6ModelK

theorem members_conj {k : Fin 3} {g : AE6Om} (hg : g ∈ ae6ModelV k) :
    ∀ J ∈ ae6ConjIn (ae6ModelV k) ae6ModelK, ∃ J' ∈ ae6ConjIn (ae6ModelV k) ae6ModelK,
      ∀ x : AE6Om, x ∈ J ↔ g⁻¹ * x * g ∈ J' := by
  rintro _ ⟨h, hh, rfl⟩
  refine ⟨conjSub (g⁻¹ * h) ae6ModelK, ⟨g⁻¹ * h, mul_mem (inv_mem hg) hh, rfl⟩, fun x => ?_⟩
  rw [mem_conjSub_iff, mem_conjSub_iff]
  have : (g⁻¹ * h)⁻¹ * (g⁻¹ * x * g) * (g⁻¹ * h) = h⁻¹ * x * h := by group
  rw [this]

theorem aut_ae6Word {τ : MulAut AE6Om} {π : Fin 8 → Fin 8}
    (hτ : ∀ i, τ (A6.curtisGen i) = A6.curtisGen (π i)) (w : List (Fin 8)) :
    τ (ae6Word w) = ae6Word (w.map π) := by
  unfold ae6Word
  rw [← MulEquiv.coe_toMonoidHom, map_list_prod, List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => hτ i

theorem aut_K_eq {τ : MulAut AE6Om} {c : AE6Om} (h : ∀ s : Fin 2, τ (ae6Word (ae6KWord ⟨s.val, by omega⟩)) ∈
    conjSub c ae6ModelK) : ∀ y, y ∈ ae6ModelK ↔ τ y ∈ conjSub c ae6ModelK := by
  have hle : ae6ModelK.map τ.toMonoidHom ≤ conjSub c ae6ModelK := by
    rw [ae6ModelK, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    have h0 := h 0
    have h1 := h 1
    rcases hx with rfl | rfl
    · exact h0
    · exact h1
  have hcard : Nat.card (conjSub c ae6ModelK) ≤ Nat.card (ae6ModelK.map τ.toMonoidHom) := by
    rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj c).injective,
      Subgroup.card_map_of_injective τ.injective]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  intro y
  rw [← heq]
  exact (Subgroup.mem_map_iff_mem (f := τ.toMonoidHom) τ.injective).symm

theorem members_swap {k : Fin 3} {τ : MulAut AE6Om} (hτV : ∀ x, x ∈ ae6ModelV k ↔ τ x ∈ ae6ModelV k)
    {c : AE6Om} (hc : c ∈ ae6ModelV k) (hτK : ∀ y, y ∈ ae6ModelK ↔ τ y ∈ conjSub c ae6ModelK) :
    ∀ J ∈ ae6ConjIn (ae6ModelV k) ae6ModelK, ∃ J' ∈ ae6ConjIn (ae6ModelV k) ae6ModelK,
      ∀ x : AE6Om, x ∈ J ↔ τ x ∈ J' := by
  rintro _ ⟨h, hh, rfl⟩
  refine ⟨conjSub (τ h * c) ae6ModelK, ⟨τ h * c, mul_mem ((hτV h).1 hh) hc, rfl⟩, fun x => ?_⟩
  rw [mem_conjSub_iff, mem_conjSub_iff, hτK, mem_conjSub_iff]
  have : (τ h * c)⁻¹ * τ x * (τ h * c) = c⁻¹ * (τ (h⁻¹ * x * h)) * c := by
    simp only [map_mul, map_inv]
    group
  rw [this]

theorem ae6ModelEdgePairsMem_of_fin (h : AE6EdgePairsFin) (hS : AE6EdgeSwapMem) :
    AE6ModelEdgePairsMem := by
  intro k l m hkl hkm hlm E E' hE hE' _ _ hcE hcE' hcEE'
  obtain ⟨g, hgV, hgU⟩ := ae6_exists_conj_U h k (inf_le_left.trans hE) hcEE'
  set c : MulAut AE6Om := MulAut.conj g with hc
  have hcV : ∀ x, x ∈ ae6ModelV k ↔ c x ∈ ae6ModelV k := fun x => by
    simp only [hc, MulAut.conj_apply]
    constructor
    · intro hx; exact mul_mem (mul_mem hgV hx) (inv_mem hgV)
    · intro hx
      convert mul_mem (mul_mem (inv_mem hgV) hx) hgV using 1
      group
  have hclass : ∀ X : Subgroup AE6Om, X ≤ ae6ModelV k → Nat.card X = 86016 →
      (∀ u ∈ ae6ModelU, ∃ t ∈ X, g * t * g⁻¹ = u) → ∃ l', l' ≠ k ∧ ∀ x, x ∈ X ↔ c x ∈ ae6ModelE k l' := by
    intro X hX hcX hUX
    set F := X.map c.toMonoidHom with hF
    have hFU : ae6ModelU ≤ F := fun u hu => by
      obtain ⟨t, ht, rfl⟩ := hUX u hu
      exact ⟨t, ht, rfl⟩
    have hFV : F ≤ ae6ModelV k := by
      rintro _ ⟨t, ht, rfl⟩
      exact (hcV t).1 (hX ht)
    obtain ⟨A, hA0, hAH, hFA⟩ := ae6_overgroup h k hFU hFV
    have hAk : ae6Omit k ∉ A := fun hk => gen_omit_not_mem (h.2.1 k) (hFV (hAH _ hk))
    have hcF : Nat.card (ae6LetterSub ↑A) = 86016 := by
      rw [← hFA, hF, Subgroup.card_map_of_injective c.injective, hcX]
    obtain ⟨l', hl', rfl⟩ := h.2.2.1 k A hA0 hAk hcF
    refine ⟨l', hl', fun x => ?_⟩
    rw [ae6ModelE_eq h, ← hFA, hF]
    exact (Subgroup.mem_map_iff_mem (f := c.toMonoidHom) c.injective).symm
  obtain ⟨l₁, hl₁, h₁⟩ := hclass E hE hcE fun u hu => by
    obtain ⟨t, ht, e⟩ := hgU u hu
    exact ⟨t, ht.1, e⟩
  obtain ⟨l₂, hl₂, h₂⟩ := hclass E' hE' hcE' fun u hu => by
    obtain ⟨t, ht, e⟩ := hgU u hu
    exact ⟨t, ht.2, e⟩
  have hne : l₁ ≠ l₂ := by
    rintro rfl
    have hEE : E = E' := by ext x; rw [h₁, h₂]
    rw [hEE, inf_idem, hcE'] at hcEE'
    norm_num at hcEE'
  have hinv : ∀ k : Fin 3, ∀ i, ae6EdgeSwap k (ae6EdgeSwap k i) = i := by decide
  obtain ⟨τ, hτ⟩ := ae6_aut_of_perm (ae6EdgeSwap k) (Function.LeftInverse.surjective (hinv k)) (h.2.2.2.2.2 k)
  have himV : ∀ k : Fin 3, (ae6VertexLetters k).image (ae6EdgeSwap k) = ae6VertexLetters k := by decide
  have himE : ∀ k l m : Fin 3, k ≠ l → k ≠ m → l ≠ m →
      (ae6EdgeLetters k l).image (ae6EdgeSwap k) = ae6EdgeLetters k m := by decide
  have hτV : ∀ x, x ∈ ae6ModelV k ↔ τ x ∈ ae6ModelV k := fun x => by
    rw [ae6ModelV_eq, mem_letterSub_aut hτ, ← Finset.coe_image, himV]
  have hτE : ∀ l m, k ≠ l → k ≠ m → l ≠ m → ∀ x, x ∈ ae6ModelE k l ↔ τ x ∈ ae6ModelE k m :=
    fun l m hkl hkm hlm x => by
      rw [ae6ModelE_eq h, ae6ModelE_eq h, mem_letterSub_aut hτ, ← Finset.coe_image, himE k l m hkl hkm hlm]
  obtain ⟨c₀, hc₀, hτc₀⟩ := hS k
  have hτK : ∀ y, y ∈ ae6ModelK ↔ τ y ∈ conjSub c₀ ae6ModelK :=
    aut_K_eq fun s => by rw [aut_ae6Word hτ]; exact hτc₀ s
  have hmτ := members_swap hτV hc₀ hτK
  have hmc := members_conj hgV
  have key : ∀ φ : MulAut AE6Om, (∀ x, x ∈ ae6ModelV k ↔ φ x ∈ ae6ModelV k) →
      (∀ x, x ∈ ae6ModelE k l ↔ φ x ∈ E) → (∀ x, x ∈ ae6ModelE k m ↔ φ x ∈ E') →
      (∀ J ∈ ae6ConjIn (ae6ModelV k) ae6ModelK, ∃ J' ∈ ae6ConjIn (ae6ModelV k) ae6ModelK,
        ∀ x, x ∈ J ↔ φ x ∈ J') →
      ∃ β : MulAut ↥(ae6ModelV k),
        ((ae6ModelE k l).subgroupOf (ae6ModelV k)).map β.toMonoidHom = E.subgroupOf (ae6ModelV k) ∧
          ((ae6ModelE k m).subgroupOf (ae6ModelV k)).map β.toMonoidHom = E'.subgroupOf (ae6ModelV k) ∧
          ∀ J ∈ ae6ConjIn (ae6ModelV k) ae6ModelK, ∃ J' ∈ ae6ConjIn (ae6ModelV k) ae6ModelK,
            ∀ x : ↥(ae6ModelV k), (x : AE6Om) ∈ J ↔ ((β x : ↥(ae6ModelV k)) : AE6Om) ∈ J' := by
    intro φ hφV hφl hφm hφJ
    obtain ⟨β, hβ⟩ := ae6_restrict φ hφV
    refine ⟨β, ae6_restrict_map hβ hφl, ae6_restrict_map hβ hφm, fun J hJ => ?_⟩
    obtain ⟨J', hJ', hJJ'⟩ := hφJ J hJ
    exact ⟨J', hJ', fun x => by rw [hβ]; exact hJJ' x⟩
  have hcV' : ∀ x, x ∈ ae6ModelV k ↔ c.symm x ∈ ae6ModelV k := fun x => by
    rw [hcV (c.symm x), MulEquiv.apply_symm_apply]
  have hc_symm : ∀ x, c.symm x = g⁻¹ * x * g := fun x => by
    simp [hc, MulAut.conj_symm_apply]
  rcases fin3_pair_cases k l m l₁ l₂ hkl hkm hlm hl₁ hl₂ hne with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ <;>
    rw [e₁] at h₁ <;> rw [e₂] at h₂
  · refine key c.symm hcV' (fun x => ?_) (fun x => ?_) (fun J hJ => ?_)
    · rw [h₁ (c.symm x), MulEquiv.apply_symm_apply]
    · rw [h₂ (c.symm x), MulEquiv.apply_symm_apply]
    · obtain ⟨J', hJ', hx⟩ := hmc J hJ
      exact ⟨J', hJ', fun x => by rw [hc_symm]; exact hx x⟩
  · refine key (τ.trans c.symm) (fun x => ?_) (fun x => ?_) (fun x => ?_) (fun J hJ => ?_)
    · rw [MulEquiv.trans_apply, ← hcV', hτV]
    · rw [MulEquiv.trans_apply, h₁ (c.symm (τ x)), MulEquiv.apply_symm_apply, hτE l m hkl hkm hlm]
    · rw [MulEquiv.trans_apply, h₂ (c.symm (τ x)), MulEquiv.apply_symm_apply, hτE m l hkm hkl hlm.symm]
    · obtain ⟨J₁, hJ₁, hx₁⟩ := hmτ J hJ
      obtain ⟨J₂, hJ₂, hx₂⟩ := hmc J₁ hJ₁
      exact ⟨J₂, hJ₂, fun x => by rw [MulEquiv.trans_apply, hc_symm]; exact (hx₁ x).trans (hx₂ (τ x))⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6h2
