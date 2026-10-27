module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.Quasithin.EmptyFaithful.GoldschmidtEmbedLocA7Aut

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem sec5pe8s_aut_eq_one_of_alt7 {Y : Type} [Group Y] (P : Sylow 2 Y)
    (e : Y ≃* alternatingGroup (Fin 7)) (κ : MulAut Y) (hodd : Odd (orderOf κ))
    (hfix : ∀ x ∈ (P : Subgroup Y), κ x = x) : κ = 1 := by
  haveI : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  let σ : MulAut (alternatingGroup (Fin 7)) := MulAut.congr e κ
  have hσapply : ∀ x : Y, σ (e x) = e (κ x) := by
    intro x
    change (e.symm.trans (κ.trans e)) (e x) = e (κ x)
    simp
  have hordσ : orderOf σ = orderOf κ := MulEquiv.orderOf_eq (MulAut.congr e) κ
  have hoddσ : Odd (orderOf σ) := by rw [hordσ]; exact hodd
  let D : Sylow 2 (alternatingGroup (Fin 7)) :=
    Sylow.mapSurjective (f := e.toMonoidHom) e.surjective P
  have hfixD : ∀ x : alternatingGroup (Fin 7), x ∈ (D : Subgroup _) → σ x = x := by
    intro x hx
    change x ∈ P.map e.toMonoidHom at hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    change σ (e p) = e p
    rw [hσapply p, hfix p hp]
  have hσD : ∀ x : alternatingGroup (Fin 7),
      x ∈ (D : Subgroup _) ↔ σ x ∈ (D : Subgroup _) := by
    intro x
    constructor
    · intro hx
      rw [hfixD x hx]
      exact hx
    · intro hx
      have h2 : σ (σ x) = σ x := hfixD (σ x) hx
      have h3 : σ x = x := σ.injective h2
      rw [← h3]
      exact hx
  have hσ1 : σ = 1 := CFSG.Quasithin.EmbedLoc.alt7_aut_eq_one_of_odd σ hoddσ D hσD
  ext x
  apply e.injective
  have h := hσapply x
  rw [hσ1] at h
  simpa using h.symm

end CFSG.OddStandard.SmallF3.Omega
