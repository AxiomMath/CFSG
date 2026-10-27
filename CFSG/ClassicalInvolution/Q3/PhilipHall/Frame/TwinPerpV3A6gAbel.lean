module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6eVec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6gCoord

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TC.Thin
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e (aeBar8)
open CFSG.ClassicalInvolution.Asc77 (IsElemAbelian2)
open scoped Matrix

theorem pi_add_cancel (f g : Fin 8 → ZMod 2) : f + g + g = f := by
  funext i
  simp only [Pi.add_apply]
  generalize f i = x
  generalize g i = y
  revert x y
  decide

theorem aff_sq_aux : ∀ (a : Fin 3 → ZMod 2) (c : ZMod 2) (b : Fin 3 → ZMod 2),
    ModPi (aff a c + sh b (aff a c)) 0 := by decide +kernel

theorem aff_dd_sq_aux : ∀ (b a : Fin 3 → ZMod 2) (c : ZMod 2),
    ModPi ((aff a c + dd b) + sh b (aff a c + dd b)) 0 := by decide +kernel

theorem AT_sq : ∀ x ∈ AT, x * x = 1 := by
  intro x hx
  obtain ⟨f, b, ⟨a, c, rfl⟩, rfl⟩ := mem_AT.mp hx
  exact (E8_sq_iff _ _).mpr (aff_sq_aux a c b)

theorem AD_sq : ∀ x ∈ AD, x * x = 1 := by
  intro x hx
  obtain ⟨f, b, ⟨a, c, hf⟩, rfl⟩ := mem_AD.mp hx
  have e : f = aff a c + dd b := by rw [← hf, pi_add_cancel]
  rw [E8_sq_iff, e]
  exact aff_dd_sq_aux b a c

theorem vbar_mem_E3p {f : Fin 8 → ZMod 2} (hf : AffP f) : vbar 8 f ∈ E3p :=
  mem_E3p.mpr ⟨f, hf, by rw [E8, tl_zero, mul_one]⟩

theorem eq_zero_of_aperm_one_eq_one {b : Fin 3 → ZMod 2} (h : aperm 1 b = 1) : b = 0 :=
  (aperm_inj (h.trans aperm_one_zero.symm)).2

theorem affP_of_vbar_mem_AT {h : Fin 8 → ZMod 2} (hm : vbar 8 h ∈ AT) : AffP h := by
  obtain ⟨f, b, hf, he⟩ := mem_AT.mp hm
  have hp : permBar 8 (vbar 8 h) = aperm 1 b := by rw [he, permBar_E8]
  have hp1 : permBar 8 (vbar 8 h) = 1 := permBar_mkQ _
  have hb : b = 0 := eq_zero_of_aperm_one_eq_one (hp.symm.trans hp1)
  subst hb
  rw [E8, tl_zero, mul_one] at he
  exact AffP.of_modPi hf (vbar_eq_iff.mp he)

theorem affP_of_vbar_mem_AD {h : Fin 8 → ZMod 2} (hm : vbar 8 h ∈ AD) : AffP h := by
  obtain ⟨f, b, hf, he⟩ := mem_AD.mp hm
  have hp : permBar 8 (vbar 8 h) = aperm 1 b := by rw [he, permBar_E8]
  have hp1 : permBar 8 (vbar 8 h) = 1 := permBar_mkQ _
  have hb : b = 0 := eq_zero_of_aperm_one_eq_one (hp.symm.trans hp1)
  subst hb
  rw [dd_zero, add_zero] at hf
  rw [E8, tl_zero, mul_one] at he
  exact AffP.of_modPi hf (vbar_eq_iff.mp he)

theorem plane_of_affP_ind : ∀ s : Finset (Fin 8), AffP (ind s) → s.card = 4 → s ∈ affinePlanes := by
  decide +kernel

theorem planes_of_actV {σ : Equiv.Perm (Fin 8)} (h : ∀ f, AffP f → AffP (actV σ f)) :
    ∀ δ ∈ affinePlanes, δ.map σ.toEmbedding ∈ affinePlanes := by
  intro δ hδ
  have h2 : actV σ (ind δ) = ind (δ.map σ.toEmbedding) := by
    funext z
    show ind δ (σ.symm z) = _
    unfold ind
    simp [Finset.mem_map_equiv]
  have h3 : AffP (ind (δ.map σ.toEmbedding)) := h2 ▸ h _ (affP_ind δ hδ)
  exact plane_of_affP_ind _ h3 (by rw [Finset.card_map]; exact affinePlanes_card δ hδ)

theorem mem_e29Sub_of_normalizes {S : Subgroup (AEQ 8)} (hS : E3p ≤ S)
    (hv : ∀ h, vbar 8 h ∈ S → AffP h) {g : AEQ 8} (hg : g ∈ aeBar8)
    (hn : ∀ a, a ∈ S ↔ g * a * g⁻¹ ∈ S) : g ∈ e29Sub := by
  obtain ⟨w, hw, rfl⟩ := hg
  have key : ∀ f, AffP f → AffP (actV w.perm f) := by
    intro f hf
    have h1 : mkQ 8 w * vbar 8 f * (mkQ 8 w)⁻¹ ∈ S := (hn _).mp (hS (vbar_mem_E3p hf))
    rw [conj_vbar (permBar_mkQ w)] at h1
    exact hv _ h1
  have key' : ∀ f, AffP f → AffP (actV w.perm⁻¹ f) := by
    intro f hf
    have h0 : (mkQ 8 w)⁻¹ * vbar 8 f * ((mkQ 8 w)⁻¹)⁻¹ ∈ S := by
      refine (hn _).mpr ?_
      have : mkQ 8 w * ((mkQ 8 w)⁻¹ * vbar 8 f * ((mkQ 8 w)⁻¹)⁻¹) * (mkQ 8 w)⁻¹ = vbar 8 f := by
        group
      rw [this]
      exact hS (vbar_mem_E3p hf)
    have hp : permBar 8 (mkQ 8 w)⁻¹ = w.perm⁻¹ := by
      rw [← map_inv, permBar_mkQ]
      rfl
    rw [conj_vbar hp] at h0
    exact hv _ h0
  have hσ : w.perm ∈ agl32 := fun s hs => ⟨planes_of_actV key s hs, planes_of_actV key' s hs⟩
  exact ⟨w, ⟨hw, hσ⟩, rfl⟩

theorem normalizer_AT_le {g : AEQ 8} (hg : g ∈ aeBar8) (hn : ∀ a, a ∈ AT ↔ g * a * g⁻¹ ∈ AT) :
    g ∈ e29Sub :=
  mem_e29Sub_of_normalizes E3p_le_AT (fun _ => affP_of_vbar_mem_AT) hg hn

theorem normalizer_AD_le {g : AEQ 8} (hg : g ∈ aeBar8) (hn : ∀ a, a ∈ AD ↔ g * a * g⁻¹ ∈ AD) :
    g ∈ e29Sub :=
  mem_e29Sub_of_normalizes E3p_le_AD (fun _ => affP_of_vbar_mem_AD) hg hn

@[expose] def b₁ : Fin 3 → ZMod 2 := ![1, 0, 0]

@[expose] def σ₀ : Equiv.Perm (Fin 8) := aperm 1 b₁

theorem b₁_ne_zero : b₁ ≠ 0 := by decide

theorem σ₀_apply : ∀ z : Fin 8, σ₀ z = ![1, 0, 3, 2, 5, 4, 7, 6] z := by decide +kernel

theorem x_class {x : AEQ 8} (hx : x ∈ aeBar8) (hp : permQ 8 x = σ₀) (hsq : x * x = 1) :
    x ∈ AT ∨ x ∈ AD := by
  obtain ⟨w, hw, rfl⟩ := hx
  have hperm : w.perm = aperm 1 b₁ := hp
  have hx' : mkQ 8 w = E8 w.vec b₁ := by
    unfold E8 vbar tl
    rw [← map_mul, ← hperm]
    exact congrArg (mkQ 8) (eq_ofVec_mul_ofPerm w)
  have hEv : EvF w.vec := hw.1
  rw [hx'] at hsq ⊢
  rcases inv_class _ hEv b₁ ((E8_sq_iff _ _).mp hsq) with h0 | h1 | h2
  · exact absurd h0 b₁_ne_zero
  · exact Or.inl (mem_AT.mpr ⟨_, _, h1, rfl⟩)
  · exact Or.inr (mem_AD.mpr ⟨_, _, h2, rfl⟩)

theorem exists_not_mem_four (δ : Finset (Fin 8)) (h : δ.card = 4) : ∃ z, z ∉ δ := by
  by_contra hcon
  push Not at hcon
  have : δ = Finset.univ := Finset.eq_univ_of_forall hcon
  rw [this] at h
  simp at h

theorem eq_one_of_fixed_aperm : ∀ (b : Fin 3 → ZMod 2) (z : Fin 8), aperm 1 b z = z → b = 0 := by
  decide +kernel

theorem eq_one_of_mem_translSub_fix {σ : Equiv.Perm (Fin 8)} (hσ : σ ∈ translSub) {z : Fin 8}
    (hz : σ z = z) : σ = 1 := by
  obtain ⟨b, rfl⟩ := exists_eq_aperm_of_mem_translSub hσ
  rw [eq_one_of_fixed_aperm b z hz]
  exact aperm_one_zero

theorem memBar_inf_nBar {δ : Finset (Fin 8)} {h : δ.card = 4} {c : Bool} {g : AEQ 8}
    (hg : g ∈ memBar δ h c) (hn : permQ 8 g ∈ translSub) : g = 1 ∨ g = zBar δ h := by
  obtain ⟨a, ha, rfl⟩ := hg
  have hperm : a.perm ∈ translSub := hn
  obtain ⟨z, hz⟩ := exists_not_mem_four δ h
  have hzr : z ∉ Set.range (emb δ h) := by
    rw [range_emb]
    exact hz
  have h1 : a.perm = 1 :=
    eq_one_of_mem_translSub_fix hperm ((supportedOn_of_mem_memAt ha z hzr).2)
  have h2 : a = ofVec a.vec := Wr.ext rfl h1
  have h3 : a * a = 1 := by
    conv_lhs => rw [h2]
    exact TL4.ofVec_mul_self _
  rcases eq_of_mem_memAt_mul_self ha h3 with rfl | rfl
  · exact Or.inl (map_one _)
  · exact Or.inr rfl

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g
