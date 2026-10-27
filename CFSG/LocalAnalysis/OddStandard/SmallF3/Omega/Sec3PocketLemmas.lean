module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Trans

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem inFStar_of_isL3Eps3 {X H : Subgroup G} (hX : IsComponentIn X H) (h : IsL3Eps3 X) :
    InFStar X := by
  refine Or.inr ⟨hX.isQuasisimple, ?_⟩
  rcases h with h | h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem Sec3PocketData.conjugate {x y : G} {X K : Subgroup G} (h : Sec3PocketData x X y K)
    (g : G) :
    Sec3PocketData (g⁻¹ * x * g) (CFSG.conjugate X g) (g⁻¹ * y * g) (CFSG.conjugate K g) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h' := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) x
    rwa [MulAut.conj_apply, inv_inv, h.involution_x] at h'
  · have h' := h.component.map_mulEquiv (MulAut.conj g⁻¹)
    change IsComponentIn (CFSG.conjugate X g)
      (CFSG.conjugate (centralizer ({x} : Set G)) g) at h'
    rw [conjugate_centralizer_singleton x g] at h'
    exact h'
  · exact h.inFStar.conjugate g
  · have h' := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) y
    rwa [MulAut.conj_apply, inv_inv, h.involution_y] at h'
  · change g⁻¹ * y * g ∈ X.map (MulAut.conj g⁻¹).toMonoidHom
    exact Subgroup.mem_map.mpr ⟨y, h.mem, by simp [MulAut.conj_apply]⟩
  · exact Subgroup.map_mono h.le
  · have hp := h.pocket.conjugate g
    rw [conjugate_centralizer_singleton x g] at hp
    exact hp

theorem conjugate_eq_self_of_lemma36 [Finite G] (h36 : Asc82Lemma36) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) : ∀ c ∈ centralizer ({t} : Set G), CFSG.conjugate L c = L := by
  intro c hc
  have h1 : IsComponentIn (CFSG.conjugate L c) (centralizer ({t} : Set G)) :=
    hS.component.conjugate hc
  have h2 : InFStar (CFSG.conjugate L c) := by
    have hLstar : InFStar L := Or.inl hS.inF
    exact hLstar.conjugate c
  exact (h36 G t L hS t L hS.involution hS.component (Or.inl hS.inF)).2
    (CFSG.conjugate L c) h1 h2

theorem exists_sec3PocketData_of_isI4PlusIn {t : G} {L : Subgroup G} (ht : orderOf t = 2)
    (hL : IsComponentIn L (centralizer ({t} : Set G))) (hLF : InFStar L)
    (hnorm : ∀ c ∈ centralizer ({t} : Set G), CFSG.conjugate L c = L) {z : G}
    (hz : IsI4PlusIn L z) : ∃ K : Subgroup G, Sec3PocketData t L z K := by
  obtain ⟨hz2, K, hK⟩ := hz
  exact ⟨K, ⟨ht, hL, hLF, hz2, (hK.2.1 hK.1).1, hK.2.1.trans inf_le_left,
    hK.of_normal hL.le hnorm⟩⟩

theorem inSubgroup_layer_eq_bot_of_forall {H : Subgroup G}
    (h : ∀ J : Subgroup G, ¬ IsComponentIn J H) : CFSG.inSubgroup CFSG.layer H = ⊥ := by
  have hs : sSup {K : Subgroup ↥H | IsComponent K} = ⊥ := by
    rw [sSup_eq_bot]
    intro a ha
    exact False.elim (h (a.map H.subtype) ⟨Subgroup.map_subtype_le a, by
      show IsComponent ((a.map H.subtype).comap H.subtype)
      rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective a]
      exact ha⟩)
  unfold CFSG.inSubgroup
  rw [CFSG.layer.eq_sSup, hs, Subgroup.map_bot]

end CFSG.OddStandard.SmallF3.Omega
