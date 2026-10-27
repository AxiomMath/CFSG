module

public import CFSG.GH74.Defs
public import CFSG.Quasithin.Vol2.Ch12Sec8OneHat

public section

namespace CFSG.GH74.QTGen4

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Open

theorem hatModel_finrank_le {G : Type} [Group G] (hG : Gen4 G) {U : Subgroup G}
    (hU : IsPGroup 2 U) (D : HatModelU U) : Module.finrank (ZMod 2) D.V ≤ 4 := by
  classical
  obtain ⟨s, hs, hsU⟩ := hG U hU
  have h1 : D.π 1 = 0 := by
    have := D.π_mul 1 U.one_mem 1 U.one_mem
    simpa using this
  have hinv : ∀ x ∈ U, D.π x⁻¹ = - D.π x := by
    intro x hx
    have := D.π_mul x hx x⁻¹ (U.inv_mem hx)
    rw [mul_inv_cancel, h1] at this
    exact (neg_eq_of_add_eq_zero_right this.symm).symm
  let S : Submodule (ZMod 2) D.V := Submodule.span (ZMod 2) ((s.image D.π : Finset D.V) : Set D.V)
  have hS : ∀ u ∈ U, D.π u ∈ S := by
    intro u hu
    rw [← hsU] at hu
    induction hu using Subgroup.closure_induction with
    | mem x hx => exact Submodule.subset_span (by simpa using ⟨x, hx, rfl⟩)
    | one => rw [h1]; exact S.zero_mem
    | mul a b ha hb iha ihb =>
      rw [D.π_mul a (hsU ▸ ha) b (hsU ▸ hb)]
      exact S.add_mem iha ihb
    | inv a ha iha =>
      rw [hinv a (hsU ▸ ha)]
      exact S.neg_mem iha
  have htop : S = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨u, hu, rfl⟩ := D.π_surj v
    exact hS u hu
  calc Module.finrank (ZMod 2) D.V = Module.finrank (ZMod 2) S := by rw [htop]; simp
    _ ≤ (s.image D.π).card := finrank_span_finset_le_card _
    _ ≤ s.card := Finset.card_image_le
    _ ≤ 4 := hs

end CFSG.GH74.QTGen4
