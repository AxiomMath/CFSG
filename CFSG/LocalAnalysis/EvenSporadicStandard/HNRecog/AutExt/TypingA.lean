module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.InvCover
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.CentOrders

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'}

theorem iso_mem_inv {K : Subgroup G} {K' : Subgroup G'} {φ : G → G'} (hφ : IsIsoOn K K' φ)
    {t : G} (ht : t ∈ InvIn K) : φ t ∈ InvIn K' :=
  ⟨hφ.mem t ht.1, (hφ.orderOf_eq ht.1).trans ht.2⟩

theorem card_Gxy_iso {φ : G → G'} (hφ : IsIsoOn (Gx a) (Gx a') φ) {t : G} (ht : t ∈ Gx a) :
    Nat.card ↥(Gxy a' (φ t)) = Nat.card ↥(Gxy a t) := by
  rw [Gxy_eq_inf, Gxy_eq_inf]
  exact (hφ.restrict_cent ht).natCard_eq.symm

theorem typing_2A (h : F5Std a z) (h' : F5Std a' z') {φ : G → G'}
    (hφ : IsIsoOn (Gx a) (Gx a') φ) {b : G} (hb : b ∈ orb2A a a) : φ b ∈ orb2A a' a' := by
  have hbG : b ∈ Gx a := h.mem_Gx_of_orb2A (IsConj.refl a) hb
  have hcard : Nat.card ↥(Gxy a' (φ b)) = 80640 := by
    rw [card_Gxy_iso hφ hbG, card_Gxy_2A h hb]
  rcases inv_cover h' (iso_mem_inv hφ ⟨hbG, h.orderOf_eq_two (Or.inl hb.1)⟩) with
    h1 | h2 | h3 | h4 | h5
  · exfalso
    have hx : Nat.card ↥(Gxy a' a') = 177408000 := by
      rw [Gxy_eq_inf, inf_idem, card_Gx_a h']
    rw [h1] at hcard
    omega
  · exact h2
  · exfalso
    have := card_Gxy_2B h' h3
    omega
  · exfalso
    have := card_Gxy_2AB h' h4
    omega
  · exfalso
    have := card_Gxy_2BB h' h5
    omega

theorem typing_2BB (h : F5Std a z) (h' : F5Std a' z') {φ : G → G'}
    (hφ : IsIsoOn (Gx a) (Gx a') φ) {w : G} (hw : w ∈ orb2BB a z a) :
    φ w ∈ orb2BB a' z' a' := by
  have hwG : w ∈ Gx a := h.mem_Gx_of_orb2BB (IsConj.refl a) hw
  have hcard : Nat.card ↥(Gxy a' (φ w)) = 3840 := by
    rw [card_Gxy_iso hφ hwG, card_Gxy_2BB h hw]
  rcases inv_cover h' (iso_mem_inv hφ ⟨hwG, h.orderOf_eq_two (Or.inr hw.1)⟩) with
    h1 | h2 | h3 | h4 | h5
  · exfalso
    have hx : Nat.card ↥(Gxy a' a') = 177408000 := by
      rw [Gxy_eq_inf, inf_idem, card_Gx_a h']
    rw [h1] at hcard
    omega
  · exfalso
    have := card_Gxy_2A h' h2
    omega
  · exfalso
    have := card_Gxy_2B h' h3
    omega
  · exfalso
    have := card_Gxy_2AB h' h4
    omega
  · exact h5

end CFSG.EvenSporadicStandard.HNRecog.Section4
