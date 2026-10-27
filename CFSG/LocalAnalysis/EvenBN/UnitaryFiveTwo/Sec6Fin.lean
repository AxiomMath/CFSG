module

public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec6B

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

section C7


namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem no_conj_t_mem (h : d.Hyp) {Q B : Subgroup G}
    (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hBs : ∀ x ∈ B, x * x = 1)
    (hBcard : Nat.card B = 2 ^ 12) (hBN : ∀ p ∈ Q, ∀ b ∈ B, p * b * p⁻¹ ∈ B) :
    ∀ g : G, g⁻¹ * d.t * g ∉ Q := by
  intro g hg
  have hx2 : (g⁻¹ * d.t * g) * (g⁻¹ * d.t * g) = 1 := by
    calc (g⁻¹ * d.t * g) * (g⁻¹ * d.t * g) = g⁻¹ * (d.t * d.t) * g := by group
      _ = 1 := by rw [h.t_mul_t]; group
  have hcard6 := exists_centralizer_elemAb (n := 6) hBc hBs (by rw [hBcard]) hx2 (hBN _ hg)
  set E : Subgroup G := (B ⊓ centralizer ({g⁻¹ * d.t * g} : Set G)).map
    (MulAut.conj g).toMonoidHom with hE
  have hEH : E ≤ d.H := by
    rintro _ ⟨b, ⟨hbB, hbC⟩, rfl⟩
    have hc : b * (g⁻¹ * d.t * g) = (g⁻¹ * d.t * g) * b := mem_centralizer_singleton_iff.1 hbC
    refine mem_centralizer_singleton_iff.2 ?_
    show (g * b * g⁻¹) * d.t = d.t * (g * b * g⁻¹)
    calc (g * b * g⁻¹) * d.t = g * (b * (g⁻¹ * d.t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * d.t * g) * b) * g⁻¹ := by rw [hc]
      _ = d.t * (g * b * g⁻¹) := by group
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨a, ⟨haB, -⟩, rfl⟩ _ ⟨b, ⟨hbB, -⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [hBc a haB b hbB]
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group
  have hEs : ∀ x ∈ E, x * x = 1 := by
    rintro _ ⟨a, ⟨haB, -⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [hBs a haB]; group
  have hcardE : Nat.card E = Nat.card ↥(B ⊓ centralizer ({g⁻¹ * d.t * g} : Set G)) :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have h5 := h.card_le_of_elemAb hEH hEc hEs
  rw [hcardE] at h5
  have h6 : 2 ^ 6 ≤ 2 ^ 5 := hcard6.trans h5
  norm_num at h6

theorem false_of_sylow (h : d.Hyp) {Q : Subgroup G}
    (hSyl : ∃ S₂ : Sylow 2 G, (S₂ : Subgroup G) = Q ⊔ zpowers d.t) (htQ : d.t ∉ Q)
    (htN : ∀ x ∈ Q, d.t * x * d.t⁻¹ ∈ Q) (hno : ∀ g : G, g⁻¹ * d.t * g ∉ Q) : False := by
  obtain ⟨S₂, hS₂⟩ := hSyl
  have hQS : Q ≤ (S₂ : Subgroup G) := by
    rw [hS₂]
    exact le_sup_left
  have hzN : zpowers d.t ≤ normalizer (Q : Set G) := by
    rw [zpowers_le]
    refine mem_normalizer_fintype fun x hx => ?_
    have := htN x hx
    rwa [h.t_inv] at this ⊢
  have hindex : Q.relIndex (S₂ : Subgroup G) = 2 := by
    have hcard := PGrp.card_sup_mul_card_inf hzN
    have hdvd : Nat.card ↥(zpowers d.t ⊓ Q) ∣ 2 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : zpowers d.t ⊓ Q ≤ zpowers d.t)
      rwa [Nat.card_zpowers, h.t_two] at this
    have hne : Nat.card ↥(zpowers d.t ⊓ Q) ≠ 2 := fun h2 => by
      have heq : zpowers d.t ⊓ Q = zpowers d.t :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h2, Nat.card_zpowers, h.t_two])
      have : d.t ∈ zpowers d.t ⊓ Q := by
        rw [heq]
        exact mem_zpowers d.t
      exact htQ this.2
    have h1 : Nat.card ↥(zpowers d.t ⊓ Q) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
      · exact h1
      · exact absurd h2 hne
    rw [h1, Nat.card_zpowers, h.t_two, mul_one, sup_comm, ← hS₂] at hcard
    have hrel := Subgroup.relIndex_mul_card (H := Q) (K := (S₂ : Subgroup G))
    rw [inf_eq_left.mpr hQS, hcard] at hrel
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hrel
  obtain ⟨N, hNn, hNsq, htN'⟩ :=
    CFSG.Quasithin.thompson_transfer_exists_normal S₂ hQS hindex h.t_two hno
  haveI := h.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hN | hN
  · obtain ⟨a, b, hab⟩ := h.nonab
    have hsq : ∀ x : G, x * x = 1 := fun x => by
      have := hNsq x
      rw [hN, Subgroup.mem_bot, sq] at this
      exact this
    apply hab
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a)
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b)
    have e : a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left (hsq (a * b))
    rw [e, mul_inv_rev, hai, hbi]
  · exact htN' (hN ▸ mem_top _)

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
