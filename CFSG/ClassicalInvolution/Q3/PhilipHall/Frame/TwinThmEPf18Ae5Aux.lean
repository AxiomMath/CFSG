module

public import CFSG.ClassicalInvolution.Q3.AE.Bar

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr

namespace Ae5Aux

theorem perm_ne_of_mem_kList : ∀ a ∈ kList, a * a ≠ 1 → ∀ i, a.perm i ≠ i := by
  decide +kernel

theorem perm_ne_of_mem_kStarList : ∀ a ∈ kStarList, a * a ≠ 1 → ∀ i, a.perm i ≠ i := by
  decide +kernel

theorem perm_ne_of_mem_memAt {β : Finset (Fin 5)} {h' : β.card = 4} {c : Bool} {a : Wr 5}
    (ha : a ∈ memAt β h' c) (ha2 : a * a ≠ 1) (i : Fin 4) :
    a.perm (emb β h' i) ≠ emb β h' i := by
  have key : ∀ a₀ : Wr 4, (a₀ ∈ kList ∨ a₀ ∈ kStarList) → a₀ * a₀ ≠ 1 →
      embed (emb β h') a₀ * embed (emb β h') a₀ = a * a → a = embed (emb β h') a₀ →
      a.perm (emb β h' i) ≠ emb β h' i := by
    intro a₀ hk h2 _ rfl
    rw [embed_perm, embedPerm_apply]
    intro e
    rcases hk with hk | hk
    · exact perm_ne_of_mem_kList a₀ hk h2 i ((emb β h').injective e)
    · exact perm_ne_of_mem_kStarList a₀ hk h2 i ((emb β h').injective e)
  cases c
  · obtain ⟨a₀, ha₀, rfl⟩ := ha
    have h2 : a₀ * a₀ ≠ 1 := fun e => ha2 (by rw [← map_mul, e, map_one])
    exact key a₀ (Or.inr ha₀) h2 (by rw [← map_mul]) rfl
  · obtain ⟨a₀, ha₀, rfl⟩ := ha
    have h2 : a₀ * a₀ ≠ 1 := fun e => ha2 (by rw [← map_mul, e, map_one])
    exact key a₀ (Or.inl ha₀) h2 (by rw [← map_mul]) rfl

theorem eq_of_comm_zBar {α β : Finset (Fin 5)} {h : α.card = 4} {h' : β.card = 4} {c : Bool}
    {x : AEQ 5} (hx : x ∈ memBar β h' c) (hx2 : x * x ≠ 1)
    (hc : zBar α h * x = x * zBar α h) : α = β := by
  classical
  obtain ⟨a, ha, rfl⟩ := hx
  have ha2 : a * a ≠ 1 := fun e => hx2 (by rw [← map_mul, e, map_one])
  have hs := supportedOn_of_mem_memAt ha
  rcases comm_or_of_mkQ_comm (a := zOf (emb α h)) (b := a) hc with h1 | h1
  · by_contra hne
    have hex : ∃ m, m ∈ β ∧ m ∉ α := by
      by_contra hall
      push Not at hall
      exact hne (Finset.eq_of_subset_of_card_le hall (by rw [h, h'])).symm
    obtain ⟨m, hmβ, hmα⟩ := hex
    have hP : ∀ y ∈ α, a.perm y ∈ α := by
      intro y hy
      have hy' : y ∈ Set.range (emb α h) := by rw [range_emb]; exact_mod_cast hy
      have := perm_mem_of_comm_zOf h1 hy'
      rw [range_emb] at this
      exact_mod_cast this
    have hPm : a.perm m ∉ α := by
      intro hm
      have himg : α.image a.perm = α := by
        refine Finset.eq_of_subset_of_card_le ?_ ?_
        · intro z hz
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
          exact hP y hy
        · rw [Finset.card_image_of_injective _ a.perm.injective]
      rw [← himg] at hm
      obtain ⟨y, hy, hym⟩ := Finset.mem_image.mp hm
      exact hmα (a.perm.injective hym ▸ hy)
    have hcompl : (αᶜ).card ≤ 1 := by
      rw [Finset.card_compl, Fintype.card_fin, h]
    have heq : a.perm m = m :=
      Finset.card_le_one.mp hcompl _ (Finset.mem_compl.mpr hPm) _ (Finset.mem_compl.mpr hmα)
    have hmr : m ∈ Set.range (emb β h') := by rw [range_emb]; exact_mod_cast hmβ
    obtain ⟨i, rfl⟩ := hmr
    exact perm_ne_of_mem_memAt ha ha2 i heq
  · exfalso
    have hex : ∃ x, x ∉ β := by
      by_contra hall
      push Not at hall
      have : β = Finset.univ := Finset.eq_univ_of_forall hall
      rw [this, Finset.card_univ, Fintype.card_fin] at h'
      omega
    obtain ⟨x, hxβ⟩ := hex
    have hx' : x ∉ Set.range (emb β h') := by rw [range_emb]; exact_mod_cast hxβ
    have h2 := congrFun (congrArg Wr.vec h1) x
    rw [mul_vec, mul_vec, mul_vec, zOf_perm, mul_perm] at h2
    have hbx : a.vec x = 0 := (hs x hx').1
    have hbpx : a.perm.symm x = x := hs.perm_symm hx'
    have h3 : (1 : Equiv.Perm (Fin 5)).symm x = x := rfl
    rw [h3, hbx, hbpx] at h2
    have h5 : (allOnes 5).vec ((a.perm * (zOf (emb α h)).perm).symm x) = 1 := rfl
    rw [h5, add_zero, zero_add] at h2
    have h6 : (zOf (emb α h)).vec x + 1 = (zOf (emb α h)).vec x + 0 := by
      rw [add_zero]; exact h2.symm
    exact absurd (add_left_cancel h6) (by decide)

end Ae5Aux

end CFSG.ClassicalInvolution.Q3.AE
