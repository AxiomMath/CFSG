module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Embed
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2

public section

namespace CFSG.ClassicalInvolution.Models.SymplecticPairs

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

variable {K : Type} [Field K] {m : ℕ}

theorem range_succAbove (k : Fin (m + 1)) :
    Set.range (Sum.map k.succAbove k.succAbove) = (coords k)ᶜ := by
  ext a
  rcases a with a | a
  · constructor
    · rintro ⟨x, hx⟩
      rcases x with l | l
      · have h : k.succAbove l = a := Sum.inl_injective hx
        rintro h'
        rcases mem_coords.1 h' with h'' | h''
        · exact Fin.succAbove_ne k l (h.trans (Sum.inl_injective h''))
        · exact absurd h'' Sum.inl_ne_inr
      · exact absurd hx Sum.inr_ne_inl
    · intro ha
      have hak : a ≠ k := fun h => ha (h ▸ inl_mem_coords k)
      obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hak
      exact ⟨Sum.inl l, by simp [hl]⟩
  · constructor
    · rintro ⟨x, hx⟩
      rcases x with l | l
      · exact absurd hx Sum.inl_ne_inr
      · have h : k.succAbove l = a := Sum.inr_injective hx
        rintro h'
        rcases mem_coords.1 h' with h'' | h''
        · exact absurd h'' Sum.inr_ne_inl
        · exact Fin.succAbove_ne k l (h.trans (Sum.inr_injective h''))
    · intro ha
      have hak : a ≠ k := fun h => ha (h ▸ inr_mem_coords k)
      obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hak
      exact ⟨Sum.inr l, by simp [hl]⟩

theorem complGroup_longInv_eq_range (h2 : (2 : K) ≠ 0) (k : Fin (m + 1)) :
    complGroup (longInv K (m + 1) k) =
      (spEmbed (K := K) k.succAbove (Fin.succAbove_right_injective)).range := by
  rw [complGroup_longInv h2, range_spEmbed, range_succAbove]

theorem nonempty_mulEquiv_complGroup_longInv (h2 : (2 : K) ≠ 0) (k : Fin (m + 1)) :
    Nonempty (StatedSp m K ≃* complGroup (longInv K (m + 1) k)) :=
  ⟨(MonoidHom.ofInjective (spEmbed_injective (Fin.succAbove_right_injective (p := k)))).trans
    (MulEquiv.subgroupCongr (complGroup_longInv_eq_range h2 k).symm)⟩

variable {L : Subgroup (StatedSp (m + 1) K)} {i : StatedSp (m + 1) K}

theorem IsLongRootSp2.nonempty_mulEquiv_complGroup (h2 : (2 : K) ≠ 0) (h : IsLongRootSp2 L i) :
    Nonempty (StatedSp m K ≃* complGroup i) := by
  obtain ⟨k, g, rfl, rfl⟩ := h
  obtain ⟨e⟩ := nonempty_mulEquiv_complGroup_longInv h2 k
  exact ⟨e.trans ((Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr (complGroup_conj _ g).symm))⟩

theorem IsLongRootSp2.nonempty_mulEquiv_centralizer_prod (h2 : (2 : K) ≠ 0)
    (h : IsLongRootSp2 L i) :
    Nonempty (Subgroup.centralizer ({i} : Set (StatedSp (m + 1) K)) ≃*
      (SL(2, K) × StatedSp m K)) := by
  obtain ⟨e₁⟩ := h.nonempty_mulEquiv_centralizer h2
  obtain ⟨e₂⟩ := h.nonempty_mulEquiv_complGroup h2
  exact ⟨e₁.symm.trans (MulEquiv.prodCongr (MulEquiv.refl _) e₂.symm)⟩

end CFSG.ClassicalInvolution.Models.SymplecticPairs
