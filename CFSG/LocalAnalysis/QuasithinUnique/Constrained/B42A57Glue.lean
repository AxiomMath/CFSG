module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57R4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Types7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57TranspMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Dim
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Min

public section

namespace CFSG.QuasithinUnique.B42A57

open CFSG.Quasithin CFSG.Open Equiv

variable {S : Type} [CommGroup S] {G L : Subgroup (MulAut S)}

theorem exists_rho (C : Bridge.Alt57.Ctx G L 7) (ι : ↥L ≃* ↥(alternatingGroup (Fin 7)))
    (e : ↥G →* Perm (Fin 7)) (he : Function.Injective e)
    (hL : ∀ l : ↥L, e ⟨(l : MulAut S), C.le_G l.2⟩ = (ι l : Perm (Fin 7)))
    (t : ↥G) (a b : Fin 7) (hab : a ≠ b) (het : e t = swap a b) :
    ∃ ρ : Perm (Fin 7) →* MulAut S, Function.Injective ρ ∧ (∀ g : ↥G, ρ (e g) = (g : MulAut S)) ∧
      (∀ σ, ρ σ ∈ G) ∧ ∀ l : ↥L, ρ (ι l : Perm (Fin 7)) = (l : MulAut S) := by
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
  refine ⟨G.subtype.comp eEquiv.symm.toMonoidHom,
    fun x y h => eEquiv.symm.injective (Subtype.ext h), ?_, ?_, ?_⟩
  · intro g
    show ((eEquiv.symm (e g) : ↥G) : MulAut S) = g
    rw [show e g = eEquiv g from rfl, MulEquiv.symm_apply_apply]
  · intro σ
    exact (eEquiv.symm σ).2
  · intro l
    have : eEquiv.symm (ι l : Perm (Fin 7)) = ⟨(l : MulAut S), C.le_G l.2⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact (hL l).symm
    show ((eEquiv.symm (ι l : Perm (Fin 7)) : ↥G) : MulAut S) = _
    rw [this]

variable [Finite S]

theorem minOffData_of (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup S) ⊤) {A₀ : Subgroup (MulAut S)}
    (hA₀ : IsFFStarOffender G A₀)
    (hmin : ∀ B : Subgroup (MulAut S), IsFFStarOffender G B → Nat.card A₀ ≤ Nat.card B)
    (ι : ↥L ≃* ↥(alternatingGroup (Fin 7))) (ρ : Perm (Fin 7) →* MulAut S)
    (hρinj : Function.Injective ρ) (hρG : ∀ σ, ρ σ ∈ G)
    (hρι : ∀ l : ↥L, ρ (ι l : Perm (Fin 7)) = (l : MulAut S))
    {E₀ : Subgroup (Perm (Fin 7))} (hE₀ : E₀.map ρ = A₀) (hbig : 32 ≤ Nat.card S) :
    MinOffData ρ E₀ := by
  refine ⟨hρinj, ?_, ?_, hbig, ?_⟩
  · intro U hU
    have hinv : XMod.IsInv ↥L U := by
      intro x u hu
      have := hU (ι x : Perm (Fin 7)) (ι x).2 u hu
      rwa [hρι] at this
    exact hirr.2 U hinv bot_le le_top
  · have h1 := hA₀.card_le (bot_le : (⊥ : Subgroup (MulAut S)) ≤ A₀)
    rw [B1.card_bot_mul_card_fixV] at h1
    have e1 : Nat.card E₀ = Nat.card A₀ := by
      rw [← hE₀]
      exact (Subgroup.card_map_of_injective hρinj).symm
    have e2 : Cs ρ E₀ = fixV A₀ := by
      unfold Cs
      rw [hE₀]
    rw [e1, e2]
    exact h1
  · intro σ B hB hB1 hc
    obtain ⟨hA₁, hmin₁⟩ := isMinOff_conj hA₀ hmin (hρG σ)
    have hmapE : (conjE σ E₀).map ρ = A₀.map (MulAut.conj (ρ σ)).toMonoidHom := by
      rw [← hE₀]
      unfold conjE
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply]
    have hB' : B.map ρ ≤ A₀.map (MulAut.conj (ρ σ)).toMonoidHom := by
      rw [← hmapE]
      exact Subgroup.map_mono hB
    have hB1' : B.map ρ ≠ ⊥ := fun h => hB1 ((Subgroup.map_eq_bot_iff_of_injective B hρinj).1 h)
    have hcard : Nat.card (A₀.map (MulAut.conj (ρ σ)).toMonoidHom) = 2 * Nat.card (B.map ρ) := by
      rw [← hmapE, Subgroup.card_map_of_injective hρinj, Subgroup.card_map_of_injective hρinj]
      exact hc
    have := fixV_eq_of_maximal hA₁ hmin₁ hB' hB1' hcard
    unfold Cs
    rw [hmapE]
    exact this

theorem ne_of_nodup4 {a b c d : Fin 7} (h : [a, b, c, d].Nodup) : a ≠ b := by
  simp at h
  tauto

theorem ne_of_nodup6 {a b c d e f : Fin 7} (h : [a, b, c, d, e, f].Nodup) : e ≠ f := by
  simp at h
  tauto

theorem ne_of_nodup6' {a b c d e f : Fin 7} (h : [a, b, c, d, e, f].Nodup) : a ≠ b := by
  simp at h
  tauto

theorem alternatingNatural_seven_of_offender
    (hS : ∀ s : S, s * s = 1)
    (C : Bridge.Alt57.Ctx G L 7) (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup S) ⊤)
    {A : Subgroup (MulAut S)} (hA : IsFFStarOffender G A) (hbig : 32 ≤ Nat.card S) :
    AlternatingNatural L ⊤ ⊥ 7 := by
  obtain ⟨A₀, hA₀, hmin⟩ := exists_minimal_offender hA
  obtain ⟨ι, e, hinj, hL, -⟩ := exists_embedding C
  obtain ⟨h1, hc, h2, hcard⟩ := offender_image hA₀ e hinj
  rcases classify7 h1 hc h2 with ⟨r, f, hf, hbound, hcl⟩ | hres
  · exfalso
    have := card_le_of_cert C hirr hA₀ ι e hinj hL f hf (N := 2 ^ 4)
      (by rw [← hcard]; exact hbound) hcl
    omega
  · have hex : ∃ a b : Fin 7, a ≠ b ∧ swap a b ∈ (A₀.subgroupOf G).map e := by
      rcases hres with ⟨-, a, b, hab, h⟩ | ⟨-, a, b, c', d, hnd, h, -⟩ |
        ⟨-, a, b, c', d, e', f', hnd, h, -, -⟩ | ⟨-, a, b, c', d, e', f', hnd, h, -, -⟩
      · exact ⟨a, b, hab, h⟩
      · exact ⟨a, b, ne_of_nodup4 hnd, h⟩
      · exact ⟨a, b, ne_of_nodup6' hnd, h⟩
      · exact ⟨e', f', ne_of_nodup6 hnd, h⟩
    obtain ⟨a, b, hab, hsw⟩ := hex
    obtain ⟨t, htA, het⟩ := Subgroup.mem_map.1 hsw
    obtain ⟨ρ, hρinj, hρe, hρG, hρι⟩ := exists_rho C ι e hinj hL t a b hab het
    have hE : ((A₀.subgroupOf G).map e).map ρ = A₀ := by
      rw [Subgroup.map_map]
      have : ρ.comp e = G.subtype := MonoidHom.ext hρe
      rw [this, Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.2 hA₀.1
    have D := minOffData_of hirr hA₀ hmin ι ρ hρinj hρG hρι hE hbig
    rcases hres with ⟨hc2, -⟩ | ⟨hc4, a', b', c', d', hnd, hs1, hs2⟩ |
      ⟨hc8, a', b', c', d', e', f', hnd, hs1, hs2, hs3⟩ |
      ⟨hc8, a', b', c', d', e', f', hnd, hs1, hs2, hs3⟩
    · have htA' : (t : MulAut S) ∈ A₀ := Subgroup.mem_subgroupOf.1 htA
      have hle : fixV A₀ ≤ fixSub (t : MulAut S) := fun v hv => hv _ htA'
      have hdvd := Subgroup.index_dvd_of_le hle
      have hidx : (fixSub (t : MulAut S)).index ≤ 2 := by
        have h3 : (fixSub (t : MulAut S)).index ≤ (fixV A₀).index :=
          Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hdvd
        have h4 := index_fixV_le hA₀
        omega
      exact alternatingNatural_seven_of_transvection hS C hirr ι e hinj hL t a b hab het hidx
    · exact (R2_false D hc4 hnd hs1 hs2).elim
    · exact (R3_false D hc8 hnd hs1 hs2 hs3).elim
    · exact (R4_false D hc8 hnd hs1 hs2 hs3).elim

end CFSG.QuasithinUnique.B42A57
