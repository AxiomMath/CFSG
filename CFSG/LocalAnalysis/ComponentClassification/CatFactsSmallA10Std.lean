module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallA10Out

public section

namespace CFSG.ComponentClassification.CatFactsSmall

namespace A10

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.UnbalancedLayer
open Equiv

variable {H : Type} [Group H] [Finite H] {h : Hyp52 H}

theorem mem_normalizer_of_involution {y g : Wbar h.B}
    (hy : y ∈ centralizer (wbarImage h.B (GSLit.fixedLayer h.J h.B) : Set (Wbar h.B)))
    (hgy : g * y * g⁻¹ ∈ centralizer (wbarImage h.B (GSLit.fixedLayer h.J h.B) : Set (Wbar h.B)))
    (hy2 : y * y = 1) (hy1 : y ≠ 1) :
    g ∈ normalizer (wbarImage h.B (GSLit.fixedLayer h.J h.B) : Set (Wbar h.B)) := by
  have hstdJ := h.isStandard_bar
  set C := centralizer (wbarImage h.B (GSLit.fixedLayer h.J h.B) : Set (Wbar h.B)) with hC
  rw [← hstdJ.2.2.2.1]
  by_contra hgN
  have hodd := hstdJ.2.2.1 g hgN
  have hmem : y ∈ C ⊓ conjugate C g := by
    refine ⟨hy, ?_⟩
    show y ∈ C.map (MulAut.conj g⁻¹).toMonoidHom
    refine ⟨g * y * g⁻¹, hgy, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hord : orderOf (⟨y, hmem⟩ : ↥(C ⊓ conjugate C g)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [sq, hy2]) hy1
  have h2 := orderOf_dvd_natCard (⟨y, hmem⟩ : ↥(C ⊓ conjugate C g))
  rw [hord] at h2
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)

variable (hKa : conjugate h.K h.a = h.K) (eK : OddBar h.K ≃* alternatingGroup (Fin 10))
  (eJ : OddBar h.J ≃* alternatingGroup (Fin 6))

include eJ in
theorem sign_rhoW (w : h.W) : Perm.sign (rhoW h hKa eK w) = 1 := by
  rcases Int.units_eq_one_or (Perm.sign (rhoW h hKa eK w)) with hs | hs
  · exact hs
  · exact (false_of_sign_eq_neg_one hKa eK eJ hs).elim

include eJ in
theorem rhoBar_mem_alt (y : Wbar h.B) : rhoBar hKa eK y ∈ alternatingGroup (Fin 10) := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (oddTwoCore h.W) y
  change rhoBar hKa eK (wbarMk h.B w) ∈ _
  rw [rhoBar_mk, Equiv.Perm.mem_alternatingGroup]
  exact sign_rhoW hKa eK eJ w

theorem exists_lift_alt {π : Perm (Fin 10)} (hπ : π ∈ alternatingGroup (Fin 10)) :
    ∃ k : h.K, rhoW h hKa eK ⟨k, K_le_W h k.2⟩ = π := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (eK.symm ⟨π, hπ⟩)
  exact ⟨k, by rw [rhoW_of_mem_K, hk, MulEquiv.apply_symm_apply]⟩

include eJ in
theorem exists_std_tau :
    ∃ τ : Perm (Fin 10), τ * τ = 1 ∧ τ ≠ 1 ∧ τ ∈ alternatingGroup (Fin 10) ∧
      τ.support.card = 4 ∧
      (∀ l, l ∈ Lsub hKa eK ↔ l ∈ alternatingGroup (Fin 10) ∧ ∀ x ∈ τ.support, l x = x) ∧
      Nat.card (Lsub hKa eK) = 360 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJK := JBbar_le_Kbar hKa
  have hstdJ := h.isStandard_bar
  set Jt := wbarImage h.B (GSLit.fixedLayer h.J h.B) with hJt
  set C := centralizer (Jt : Set (Wbar h.B)) with hC
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 (even_iff_two_dvd.1 hstdJ.2.1)
  have hc2 : (c : Wbar h.B) * c = 1 := by
    have := pow_orderOf_eq_one c
    rw [hc, sq] at this
    exact congrArg Subtype.val this
  have hc1 : (c : Wbar h.B) ≠ 1 := by
    intro h1
    have : c = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hc
    exact absurd hc (by norm_num)
  set τ := rhoBar hKa eK c with hτ
  have hτC : ∀ l ∈ Lsub hKa eK, l * τ = τ * l := by
    rintro _ ⟨j, hj, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 c.2 j hj]
  have hτ2 : τ * τ = 1 := by rw [← map_mul, hc2, map_one]
  have hτ1 : τ ≠ 1 := fun h1 => hc1 (eq_one_of_rhoBar_eq_one hKa eK h1 hc2)
  have hN : ∀ π : Perm (Fin 10), π ∈ alternatingGroup (Fin 10) → π * τ = τ * π →
      π ∈ normalizer ((Lsub hKa eK : Subgroup (Perm (Fin 10))) : Set (Perm (Fin 10))) := by
    intro π hπ hπτ
    obtain ⟨k, hk⟩ := exists_lift_alt hKa eK hπ
    set g := wbarMk h.B ⟨k, K_le_W h k.2⟩ with hg
    have hgπ : rhoBar hKa eK g = π := by rw [hg, rhoBar_mk, hk]
    have hgc : g * c * g⁻¹ ∈ C := by
      refine mem_centralizer_of_rhoBar hKa eK hJK ?_
      rw [map_mul, map_mul, map_inv, hgπ, ← hτ, hπτ, mul_inv_cancel_right]
      rw [mem_centralizer_iff]
      exact hτC
    have hgN := mem_normalizer_of_involution c.2 hgc hc2 hc1
    rw [← hgπ]
    exact le_normalizer_map (rhoBar hKa eK) ⟨g, hgN, rfl⟩
  have h360 : 360 ∣ Nat.card (Lsub hKa eK) := by
    rw [← card_L_core hKa eK eJ]
    exact card_quotient_dvd_card _
  obtain ⟨h4, hL, hcard⟩ := eq_alt_fix_of_normalized hτ2 hτ1 (L_le_alt hKa eK)
    (L_perfect hKa eK) h360 (card_L_core hKa eK eJ) hτC hN
  exact ⟨τ, hτ2, hτ1, rhoBar_mem_alt hKa eK eJ c, h4, hL, hcard⟩

end A10

end CFSG.ComponentClassification.CatFactsSmall
