module

public import CFSG.GroupTheory.SteinbergCBFTFactorization
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710YBasic

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_sup_of_le {B A C : Subgroup G}
    (hA : B ≤ Subgroup.normalizer (A : Set G)) (hC : B ≤ Subgroup.normalizer (C : Set G)) :
    B ≤ Subgroup.normalizer ((A ⊔ C : Subgroup G) : Set G) := by
  have key : ∀ b ∈ B, ∀ x ∈ A ⊔ C, b * x * b⁻¹ ∈ A ⊔ C := by
    intro b hb x hx
    have hbA := (Subgroup.mem_normalizer_iff.1 (hA hb))
    have hbC := (Subgroup.mem_normalizer_iff.1 (hC hb))
    have : A ⊔ C ≤ (A ⊔ C).comap (MulAut.conj b).toMonoidHom := by
      refine sup_le (fun a ha => ?_) (fun c hc => ?_)
      · exact Subgroup.mem_sup_left ((hbA a).1 ha)
      · exact Subgroup.mem_sup_right ((hbC c).1 hc)
    exact this hx
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key b hb x, fun hx => ?_⟩
  have := key b⁻¹ (inv_mem hb) _ hx
  simpa [mul_assoc] using this

omit [Finite G] in
theorem card_sup_mul_card_inf {T P : Subgroup G} (h : T ≤ Subgroup.normalizer (P : Set G)) :
    Nat.card ↥(T ⊔ P) * Nat.card ↥(T ⊓ P) = Nat.card ↥T * Nat.card ↥P := by
  have h1 := CFSG.GroupTheory.FT63ChII.card_setMul_mul_card_inf T P
  rw [← Subgroup.coe_mul_of_left_le_normalizer_right T P h] at h1
  exact h1

theorem sylow_s {B T I : Subgroup G} (h : Setup710 B T I) :
    IsPGroup 2 ↥(sOf B T I) ∧ ¬ 2 ∣ (sOf B T I).relIndex (pOf B T I) := by
  have hTN : T ≤ Subgroup.normalizer (pOf B T I : Set G) :=
    (T_le_yOf B T I).trans (y_le_normalizer_pOf B T I)
  have hBN : B ≤ Subgroup.normalizer (pOf B T I : Set G) :=
    (B_le_yOf B T I).trans (y_le_normalizer_pOf B T I)
  refine ⟨h.tTwo.of_injective (Subgroup.inclusion (inf_le_left : sOf B T I ≤ T))
      (Subgroup.inclusion_injective _), ?_⟩
  set P := pOf B T I with hP
  have hcard := card_sup_mul_card_inf hTN
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.1 h.tTwo)
  have h3 : ¬ 3 ∣ Nat.card ↥(T ⊔ P) := by
    intro hd
    have : 3 ∣ Nat.card ↥T * Nat.card ↥P :=
      hcard ▸ Dvd.dvd.mul_right hd _
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 this with h3T | h3P
    · rw [hk] at h3T
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3T
      omega
    · exact not_three_dvd_card_pOf B T I h3P
  have hB3 : IsPGroup 3 ↥B := by
    refine IsPGroup.of_card (n := 4) ?_
    simpa using h.card_b
  have hBW : B ≤ Subgroup.normalizer ((T ⊔ P : Subgroup G) : Set G) :=
    le_normalizer_sup_of_le h.bnT hBN
  obtain ⟨Q, hTQ, hQW, hQ2, hBQ, hQrel⟩ :=
    CFSG.GroupTheory.FT63ChII.exists_sylow_ge_normalized (p := 3) (q := 2) (W := T ⊔ P) (A := B)
      (Q₁ := T) hB3 hBW h3 le_sup_left h.tTwo h.bnT
  have hQT : Q = T := h.tMax Q hQ2 hBQ hTQ
  subst hQT
  have hr : Q.relIndex (Q ⊔ P) * Nat.card ↥Q = Nat.card ↥(Q ⊔ P) := by
    have := Subgroup.relIndex_mul_card (H := Q) (K := Q ⊔ P)
    rwa [inf_of_le_left le_sup_left] at this
  have hS : (Q ⊓ P).relIndex P * Nat.card ↥(Q ⊓ P) = Nat.card ↥P := by
    have := Subgroup.relIndex_mul_card (H := Q ⊓ P) (K := P)
    rwa [inf_of_le_left inf_le_right] at this
  have hQpos : 0 < Nat.card ↥Q := Nat.card_pos
  have heq : Q.relIndex (Q ⊔ P) * Nat.card ↥(Q ⊓ P) = Nat.card ↥P := by
    have h4 := hcard
    rw [← hr] at h4
    apply Nat.eq_of_mul_eq_mul_left hQpos
    calc Nat.card ↥Q * (Q.relIndex (Q ⊔ P) * Nat.card ↥(Q ⊓ P))
        = Q.relIndex (Q ⊔ P) * Nat.card ↥Q * Nat.card ↥(Q ⊓ P) := by ring
      _ = _ := h4
  have hSpos : 0 < Nat.card ↥(Q ⊓ P) := Nat.card_pos
  have : (Q ⊓ P).relIndex P = Q.relIndex (Q ⊔ P) :=
    Nat.eq_of_mul_eq_mul_right hSpos (hS.trans heq.symm)
  exact this ▸ hQrel

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710
