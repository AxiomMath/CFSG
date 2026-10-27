
module


public import Certificates.Certificate320007

public section

namespace CFSG.GH74.QTGen4.Recog.G23

section Native

theorem elts_len : elts.length = 576 := Certificates.certificate320007.1

theorem elts_nodup : elts.Nodup := Certificates.certificate320007.2.1

theorem elts_closed : ∀ s ∈ elts, ∀ g ∈ gensL, mulL s g ∈ elts := Certificates.certificate320007.2.2.1

theorem idL_mem : idL ∈ elts := Certificates.certificate320007.2.2.2

theorem Hc_sub_elts : ∀ σ ∈ Hc, Lst σ ∈ elts := by
  intro σ hσ
  have hmem : σ ∈ Submonoid.closure (Set.range gen ∪ (Set.range gen)⁻¹) := by
    have h : σ ∈ (Subgroup.closure (Set.range gen)).toSubmonoid := hσ
    rwa [Subgroup.closure_toSubmonoid] at h
  have key : ∀ τ : Equiv.Perm (Fin 32), Lst τ ∈ elts → Lst (τ * σ) ∈ elts := by
    refine Submonoid.closure_induction
      (motive := fun x _ => ∀ τ : Equiv.Perm (Fin 32), Lst τ ∈ elts → Lst (τ * x) ∈ elts)
      ?_ ?_ ?_ hmem
    · intro x hx τ hτ
      rcases hx with ⟨k, rfl⟩ | hx'
      · rw [Lst_mul]
        exact elts_closed _ hτ _
          (gen_mem_gensL k)
      · obtain ⟨k, hk⟩ := Set.mem_inv.mp hx'
        have hxk : x = (gen k)⁻¹ := by rw [hk, inv_inv]
        subst hxk
        rw [Lst_mul]
        exact elts_closed _ hτ _
          (inv_gen_mem_gensL k)
    · intro τ hτ
      rw [mul_one]
      exact hτ
    · intro x y _ _ hx hy τ hτ
      rw [← mul_assoc]
      exact hy _ (hx τ hτ)
  have := key 1 (by simpa only [glue_idL_eq] using idL_mem)
  rwa [one_mul] at this

theorem Hc_image : Lst '' (Hc : Set (Equiv.Perm (Fin 32))) = (elts.toFinset : Set (List ℕ)) := by
  ext l
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact List.mem_toFinset.mpr (Hc_sub_elts σ hσ)
  · intro hl
    obtain ⟨σ, hσ, rfl⟩ := elts_sound l (List.mem_toFinset.mp hl)
    exact ⟨σ, hσ, rfl⟩

theorem Hc_card : Nat.card Hc = 576 := by
  show Nat.card (Hc : Set (Equiv.Perm (Fin 32))) = 576
  rw [Nat.card_coe_set_eq, ← Set.ncard_image_of_injective _ Lst_injective, Hc_image,
    Set.ncard_coe_finset, List.toFinset_card_of_nodup elts_nodup, elts_len]

end Native

end CFSG.GH74.QTGen4.Recog.G23
