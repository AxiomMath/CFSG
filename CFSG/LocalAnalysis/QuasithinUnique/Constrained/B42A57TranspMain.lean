module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Transp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Real
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Basic

public section

namespace CFSG.QuasithinUnique.B42A57

open CFSG.Quasithin CFSG.Open Multiplicative Equiv

theorem exists_disp_of_index_le_two {S : Type} [CommGroup S] [Finite S] (hS : ∀ s : S, s * s = 1)
    (t : MulAut S) (ht1 : t ≠ 1) (hidx : (fixSub t).index ≤ 2) :
    ∃ w₀ : S, w₀ ≠ 1 ∧ Disp t = {1, w₀} := by
  have hne : fixSub t ≠ ⊤ := by
    intro h
    apply ht1
    apply MulEquiv.ext
    intro s
    have : s ∈ fixSub t := by rw [h]; trivial
    exact this
  have h2 : (fixSub t).index = 2 := by
    have h1 : (fixSub t).index ≠ 1 := fun h => hne (Subgroup.index_eq_one.1 h)
    have h0 : (fixSub t).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 h2
  have haH : a ∉ fixSub t := by
    rcases ha 1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd (Subgroup.one_mem _) h2
    · rwa [one_mul] at h2
  have hta : t a ≠ a := haH
  refine ⟨t a * a⁻¹, fun h => hta (mul_inv_eq_one.1 h), ?_⟩
  ext w
  constructor
  · rintro ⟨s, rfl⟩
    by_cases hs : s ∈ fixSub t
    · left
      have : t s = s := hs
      rw [this, mul_inv_cancel]
    · right
      have hsa : s * a ∈ fixSub t := by
        rcases ha s with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact h1
        · exact absurd h1 hs
      have h3 : t s * t a = s * a := by
        have : t (s * a) = s * a := hsa
        rwa [map_mul] at this
      have e1 : (t s * s⁻¹) * (t a * a⁻¹) = 1 := by
        rw [mul_mul_mul_comm, h3, ← mul_inv, mul_inv_cancel]
      rw [eq_inv_of_mul_eq_one_left e1]
      exact inv_eq_of_mul_eq_one_right (hS _)
  · rintro (h | h)
    · exact ⟨1, by rw [h]; simp⟩
    · exact ⟨a, by rw [h]⟩

theorem altDn7_ker' : Subgroup.zpowers (G6.allOnes 7) ⊓ G6.coreMod 7 =
    (⊥ : Subgroup (G6.PermMod 7)) := by
  rw [eq_bot_iff]
  rintro z ⟨hz1, hz2⟩
  rw [Subgroup.mem_bot]
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz1
  have hsq : G6.allOnes 7 * G6.allOnes 7 = 1 := by decide +kernel
  have hnot : G6.allOnes 7 ∉ G6.coreMod 7 := by
    rw [G6.mem_coreMod]
    decide +kernel
  have hord : orderOf (G6.allOnes 7) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hsq) (by decide +kernel)
  have hmod := zpow_mod_orderOf (G6.allOnes 7) k
  rw [hord] at hmod
  simp only [Nat.cast_ofNat] at hmod
  rw [← hmod]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h, zpow_zero]
  · exfalso
    apply hnot
    rw [← hmod, h, zpow_one] at hz2
    exact hz2

theorem altDn7_ker : (FFModel.altDn 7).ker = ⊥ := altDn7_ker'

theorem alternatingNatural_seven_of_transvection {S : Type} [CommGroup S] [Finite S]
    (hS : ∀ s : S, s * s = 1) {G L : Subgroup (MulAut S)} (C : Bridge.Alt57.Ctx G L 7)
    (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup S) ⊤)
    (ι : ↥L ≃* ↥(alternatingGroup (Fin 7))) (e : ↥G →* Perm (Fin 7)) (he : Function.Injective e)
    (hL : ∀ l : ↥L, e ⟨(l : MulAut S), C.le_G l.2⟩ = (ι l : Perm (Fin 7)))
    (t : ↥G) (a b : Fin 7) (hab : a ≠ b) (het : e t = swap a b)
    (hidx : (fixSub (t : MulAut S)).index ≤ 2) : AlternatingNatural L ⊤ ⊥ 7 := by
  have hsurj : Function.Surjective e := by
    intro σ
    by_cases hσ : σ ∈ alternatingGroup (Fin 7)
    · obtain ⟨l, hl⟩ := ι.surjective ⟨σ, hσ⟩
      exact ⟨⟨(l : MulAut S), C.le_G l.2⟩, by rw [hL, hl]⟩
    · have hodd : Perm.sign σ = -1 := by
        rcases Int.units_eq_one_or (Perm.sign σ) with h | h
        · exact absurd (Equiv.Perm.mem_alternatingGroup.2 h) hσ
        · exact h
      have hσ' : σ * swap a b ∈ alternatingGroup (Fin 7) := by
        rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab, hodd]
        decide
      obtain ⟨l, hl⟩ := ι.surjective ⟨σ * swap a b, hσ'⟩
      refine ⟨⟨(l : MulAut S), C.le_G l.2⟩ * t, ?_⟩
      rw [map_mul, hL, hl, het]
      simp
  let eEquiv : ↥G ≃* Perm (Fin 7) := MulEquiv.ofBijective e ⟨he, hsurj⟩
  let ρ : Perm (Fin 7) →* MulAut S := G.subtype.comp eEquiv.symm.toMonoidHom
  have hρι : ∀ l : ↥L, ρ (ι l : Perm (Fin 7)) = (l : MulAut S) := by
    intro l
    have : eEquiv.symm (ι l : Perm (Fin 7)) = ⟨(l : MulAut S), C.le_G l.2⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact (hL l).symm
    show ((eEquiv.symm (ι l : Perm (Fin 7)) : ↥G) : MulAut S) = _
    rw [this]
  have hρinj : Function.Injective ρ := fun x y h => eEquiv.symm.injective (Subtype.ext h)
  have hρt : ρ (swap a b) = (t : MulAut S) := by
    have : eEquiv.symm (swap a b) = t := by
      rw [MulEquiv.symm_apply_eq]
      exact het.symm
    show ((eEquiv.symm (swap a b) : ↥G) : MulAut S) = _
    rw [this]
  have ht1 : (t : MulAut S) ≠ 1 := by
    intro h
    have : t = 1 := Subtype.ext h
    rw [this, map_one] at het
    exact hab (by simpa [Equiv.swap_eq_one_iff] using het.symm)
  obtain ⟨w, hw1, hwD⟩ := exists_disp_of_index_le_two hS (t : MulAut S) ht1 hidx
  have e01 : swap 0 1 = (gOf a b)⁻¹ * swap a b * gOf a b := by
    have h1 : swap a b = gOf a b * swap 0 1 * (gOf a b)⁻¹ := by
      rw [← Equiv.swap_apply_apply, gOf_zero _ _ hab, gOf_one _ _ hab]
    rw [h1]
    group
  have hD01 : Disp (ρ (swap 0 1)) = {1, ρ (gOf a b)⁻¹ w} := by
    have : ρ (swap 0 1) = ρ (gOf a b)⁻¹ * ρ (swap a b) * (ρ (gOf a b)⁻¹)⁻¹ := by
      rw [e01]
      simp only [map_mul, map_inv, inv_inv]
    rw [this, Disp_conj, hρt, hwD, Set.image_pair, map_one]
  have T : TransvData ρ (ρ (gOf a b)⁻¹ w) :=
    ⟨hρinj, hS, fun h => hw1 ((ρ (gOf a b)⁻¹).injective (by rw [h, map_one])), hD01⟩
  have hirrρ : ∀ U : Subgroup S, (∀ σ ∈ alternatingGroup (Fin 7), ∀ u ∈ U, ρ σ u ∈ U) →
      U = ⊥ ∨ U = ⊤ := by
    intro U hU
    have hinv : XMod.IsInv ↥L U := by
      intro x u hu
      have := hU (ι x : Perm (Fin 7)) (ι x).2 u hu
      rwa [hρι] at this
    exact hirr.2 U hinv bot_le le_top
  obtain ⟨β, hβ⟩ := exists_iso_coreMod T hirrρ
  have hfin : (FFModel.altDn 7).IsActionModel := FFModel.altDn_isActionModel 7
  refine realizesMod_of_equivariant hfin altDn7_ker L ι.symm.toMonoidHom ι.symm.surjective β ?_
  intro (γ : ↥(alternatingGroup (Fin 7))) s
  have h1 : ρ (γ : Perm (Fin 7)) = ((ι.symm γ : ↥L) : MulAut S) := by
    have := hρι (ι.symm γ)
    rwa [MulEquiv.apply_symm_apply] at this
  have h2 := hβ (γ : Perm (Fin 7)) s
  rw [h1] at h2
  exact h2

end CFSG.QuasithinUnique.B42A57
