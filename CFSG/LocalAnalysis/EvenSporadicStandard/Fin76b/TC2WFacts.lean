module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Weak

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

section Transport

variable {G : Type*} [Group G]

theorem eq_map_rootGroup [Finite G] {L : Subgroup G} {t : G} (htL : t ∈ L) {E : Subgroup G}
    (hEL : E ≤ L) (hgen : E = closure {e | e ∈ E ∧ e * e = t})
    (hge : 20 ≤ Set.ncard {e | e ∈ E ∧ e * e = t}) (hRf : RootFactsFor ↥L ⟨t, htL⟩) :
    E = (rootGroup ↥L ⟨t, htL⟩).map L.subtype := by
  have hsub : {e | e ∈ E ∧ e * e = t} ⊆ L.subtype '' {x : ↥L | x * x = ⟨t, htL⟩} := by
    rintro e ⟨he, he2⟩
    exact ⟨⟨e, hEL he⟩, Subtype.ext he2, rfl⟩
  have hcard : (L.subtype '' {x : ↥L | x * x = ⟨t, htL⟩}).ncard ≤ 20 := by
    rw [Set.ncard_image_of_injective _ L.subtype_injective]
    exact hRf.roots_le
  have heq : {e | e ∈ E ∧ e * e = t} = L.subtype '' {x : ↥L | x * x = ⟨t, htL⟩} :=
    Set.eq_of_subset_of_ncard_le hsub (le_trans hcard hge) (Set.toFinite _)
  calc E = closure {e | e ∈ E ∧ e * e = t} := hgen
    _ = closure (L.subtype '' {x : ↥L | x * x = ⟨t, htL⟩}) := by rw [heq]
    _ = (rootGroup ↥L ⟨t, htL⟩).map L.subtype := (MonoidHom.map_closure _ _).symm

theorem wFacts_of_rootFactsFor {L : Subgroup G} {t : G} (htL : t ∈ L) {E : Subgroup G}
    (hEL : E ≤ L) (hRf : RootFactsFor ↥L ⟨t, htL⟩)
    (hE : E = (rootGroup ↥L ⟨t, htL⟩).map L.subtype) : WFacts L t E := by
  set t' : ↥L := ⟨t, htL⟩ with ht'
  have hι : Function.Injective L.subtype := L.subtype_injective
  have hcentι : L ⊓ centralizer ({t} : Set G) = (centralizer ({t'} : Set ↥L)).map L.subtype := by
    ext g
    constructor
    · rintro ⟨hgL, hg⟩
      exact ⟨⟨g, hgL⟩, mem_centralizer_singleton_iff.2 (Subtype.ext
        (mem_centralizer_singleton_iff.1 hg)), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hx))⟩
  refine ⟨?_, ?_, hEL, ?_, ?_, ?_⟩
  · rw [hcentι, Subgroup.card_map_of_injective hι]
    exact hRf.card_cent
  · rw [hE, Subgroup.card_map_of_injective hι]
    exact hRf.card_E
  · intro w hwL hwt e he
    rw [hE] at he ⊢
    obtain ⟨f, hf, rfl⟩ := he
    let x : ↥L := ⟨w, hwL⟩
    have hxt : x * t' = t' * x := Subtype.ext hwt
    refine ⟨x * f * x⁻¹, ?_, rfl⟩
    have hconj : ∀ y : ↥L, y * y = t' → x * y * x⁻¹ * (x * y * x⁻¹) = t' := by
      intro y hy
      calc x * y * x⁻¹ * (x * y * x⁻¹) = x * (y * y) * x⁻¹ := by group
        _ = x * t' * x⁻¹ := by rw [hy]
        _ = t' := by rw [hxt]; group
    have hle : (rootGroup ↥L t').map (MulAut.conj x).toMonoidHom ≤ rootGroup ↥L t' := by
      rw [rootGroup, MonoidHom.map_closure, closure_le]
      rintro _ ⟨y, hy, rfl⟩
      exact subset_closure (by simpa [MulAut.conj_apply] using hconj y hy)
    simpa [MulAut.conj_apply] using hle ⟨f, hf, rfl⟩
  · intro l hlL hl
    have hy := hRf.cent_E ⟨l, hlL⟩ (fun r hr => by
      have hrE : (r : G) ∈ E := by
        rw [hE]
        exact ⟨r, subset_closure hr, rfl⟩
      exact Subtype.ext (hl _ hrE))
    rcases hy with hy | hy
    · exact Or.inl (congrArg Subtype.val hy)
    · exact Or.inr (congrArg Subtype.val hy)
  · obtain ⟨β, hβt, hβ3, hcard, d₁, hd₁, d₂, hd₂, hne⟩ := hRf.beta
    have himg : E ⊓ centralizer ({(β : G)} : Set G) =
        (rootGroup ↥L t' ⊓ centralizer ({β} : Set ↥L)).map L.subtype := by
      ext g
      constructor
      · rintro ⟨hgE, hg⟩
        rw [hE] at hgE
        obtain ⟨f, hf, rfl⟩ := hgE
        exact ⟨f, ⟨hf, mem_centralizer_singleton_iff.2 (Subtype.ext
          (mem_centralizer_singleton_iff.1 hg))⟩, rfl⟩
      · rintro ⟨f, ⟨hf, hfc⟩, rfl⟩
        exact ⟨by rw [hE]; exact ⟨f, hf, rfl⟩, mem_centralizer_singleton_iff.2
          (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hfc))⟩
    refine ⟨(β : G), β.2, congrArg Subtype.val hβt, ?_, ?_, (d₁ : G), ?_, (d₂ : G), ?_, ?_⟩
    · rw [← hβ3]
      exact Subgroup.orderOf_coe β
    · rw [himg, Subgroup.card_map_of_injective hι]
      exact hcard
    · rw [himg]
      exact ⟨d₁, hd₁, rfl⟩
    · rw [himg]
      exact ⟨d₂, hd₂, rfl⟩
    · intro hc
      exact hne (Subtype.ext hc)

end Transport

section Outer

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}

theorem OuterE.wFacts (h : OuterE G L z t T E) (hR : RootFactsClass ↥L)
    (hgen : E = closure {e | e ∈ E ∧ e * e = t})
    (hge : 20 ≤ Set.ncard {e | e ∈ E ∧ e * e = t}) : WFacts L t E := by
  have htL : t ∈ L := h.cfg.t_mem_A
  have ht2 : orderOf (⟨t, htL⟩ : ↥L) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      exact Subtype.ext h.cfg.t_sq
    · intro h1
      exact h.cfg.t_ne (congrArg Subtype.val h1)
  have hsq : ∃ g : ↥L, g * g = ⟨t, htL⟩ := by
    obtain ⟨g, hg, hg4⟩ := h.cfg.t_fourth
    exact ⟨⟨g * g, mul_mem hg hg⟩, Subtype.ext hg4⟩
  have hRf := hR ⟨t, htL⟩ ht2 hsq
  exact wFacts_of_rootFactsFor htL h.E_le_L hRf (eq_map_rootGroup htL h.E_le_L hgen hge hRf)

end Outer

end CFSG.EvenSporadicStandard.Fin76b
