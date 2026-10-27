module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10SideSym
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82Set2

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GSThmB.A10Side

namespace Eight2

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem map_conj_eq_of_mem_normalizer {K : Subgroup X} {g : X}
    (hg : g ∈ normalizer (K : Set X)) : K.map (MulAut.conj g).toMonoidHom = K := by
  apply le_antisymm
  · rintro _ ⟨k, hk, rfl⟩
    exact (mem_normalizer_iff.mp hg k).mp hk
  · intro k hk
    refine ⟨g⁻¹ * k * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have h1 := (mem_normalizer_iff.mp (inv_mem hg) k).mp hk
    rwa [inv_inv] at h1

namespace Setting2

variable (s : Setting2 X)

theorem secJ0_le_J : s.h.secJ0 s.y ≤ s.h.J :=
  (GSLit.fixedLayer_le_inf _ _).trans inf_le_left

theorem secJ0_sup : s.h.secJ0 s.y ⊔ (pPrimeCore 2 ↥s.h.J).map s.h.J.subtype = s.h.J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (GSLit.fixedLayer_sup_pPrimeCore (B5a.isQuasisimple_J s.h)
    ((s.h.secB0_le_B s.y).trans (s.h.B_le.trans inf_le_right)) (s.h.isPGroup_secB0 s.y)).1

@[expose] noncomputable def piJ : ↥(s.h.secJ0 s.y) →* ↥s.h.J ⧸ pPrimeCore 2 ↥s.h.J :=
  (QuotientGroup.mk' (pPrimeCore 2 ↥s.h.J)).comp (inclusion s.secJ0_le_J)

@[expose] noncomputable def piSec : ↥(s.h.secJ0 s.y) →* ↥s.sec.J :=
  ((s.h.subQ s.y).comp (inclusion (s.h.secJ0_le_secSub s.y))).codRestrict s.sec.J fun j => by
    rw [s.sec_J]
    exact mem_map_of_mem _ (mem_subgroupOf.mpr j.2)

theorem piSec_surjective : Function.Surjective s.piSec := by
  rintro ⟨x, hx⟩
  have hx' := hx
  rw [s.sec_J] at hx'
  obtain ⟨g, hg, rfl⟩ := hx'
  exact ⟨⟨g, mem_subgroupOf.mp hg⟩, Subtype.ext rfl⟩

theorem exists_quot_equiv : ∃ e : ↥(s.h.secJ0 s.y) ⧸ pPrimeCore 2 ↥(s.h.secJ0 s.y) ≃*
    ↥s.h.J ⧸ pPrimeCore 2 ↥s.h.J, ∀ t : ↥(s.h.secJ0 s.y),
      e (t : ↥(s.h.secJ0 s.y) ⧸ pPrimeCore 2 ↥(s.h.secJ0 s.y)) = s.piJ t := by
  obtain ⟨-, e, he⟩ := restriction_quotient_mulEquiv s.secJ0_le_J s.secJ0_sup
  exact ⟨e, fun t => he t (s.secJ0_le_J t.2)⟩

theorem exists_theta (hA : Nonempty (↥(generalizedFitting (s.h.subQuot s.y)) ≃*
      alternatingGroup (Fin 10))) :
    ∃ Θ : ↥s.h.J ⧸ pPrimeCore 2 ↥s.h.J ≃* ↥s.sec.J, ∀ t, Θ (s.piJ t) = s.piSec t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₁, -⟩ := exists_altSix_equiv s.hp s.hp2 s.hf s.centralizer_eq hA s.sec.orderOf_a
    s.sec.J_le s.sec.isPComponent_J s.J_type
  have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have hsimp : IsSimpleGroup ↥s.sec.J := e₁.isSimpleGroup
  have hcard : Nat.card ↥s.sec.J = 360 := by
    rw [Nat.card_congr e₁.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have hO : pPrimeCore 2 ↥s.sec.J = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 ↥s.sec.J) with h | h
    · exact h
    · exfalso
      have h1 : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥s.sec.J)) := pPrimeCore_coprime_card
      rw [h, card_top, hcard] at h1
      norm_num at h1
  have hJbar : Nat.card (↥s.h.J ⧸ pPrimeCore 2 ↥s.h.J) = 360 := by
    obtain ⟨eJ⟩ := s.sec_J_equiv
    rw [← Nat.card_congr eJ.toEquiv, Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hO).toEquiv,
      Nat.card_congr (QuotientGroup.quotientBot (G := ↥s.sec.J)).toEquiv, hcard]
  obtain ⟨e₀, he₀⟩ := s.exists_quot_equiv
  have hle : pPrimeCore 2 ↥(s.h.secJ0 s.y) ≤ s.piSec.ker := by
    have hn : ((pPrimeCore 2 ↥(s.h.secJ0 s.y)).map s.piSec).Normal :=
      (inferInstance : (pPrimeCore 2 ↥(s.h.secJ0 s.y)).Normal).map _ s.piSec_surjective
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((pPrimeCore 2 ↥(s.h.secJ0 s.y)).map s.piSec) with h | h
    · exact (Subgroup.map_eq_bot_iff _).mp h
    · exfalso
      have h1 := Subgroup.card_map_dvd (H := pPrimeCore 2 ↥(s.h.secJ0 s.y)) s.piSec
      rw [h, card_top, hcard] at h1
      have h2 : Odd (Nat.card (pPrimeCore 2 ↥(s.h.secJ0 s.y))) :=
        Nat.coprime_two_left.mp pPrimeCore_coprime_card
      exact absurd (Odd.of_dvd_nat h2 h1) (by decide)
  set ψ := QuotientGroup.lift (pPrimeCore 2 ↥(s.h.secJ0 s.y)) s.piSec hle with hψ
  have hψsurj : Function.Surjective ψ := by
    intro x
    obtain ⟨t, rfl⟩ := s.piSec_surjective x
    exact ⟨t, rfl⟩
  have hψbij : Function.Bijective ψ := hψsurj.bijective_of_nat_card_le (by
    rw [Nat.card_congr e₀.toEquiv, hJbar, hcard])
  refine ⟨e₀.symm.trans (MulEquiv.ofBijective ψ hψbij), fun t => ?_⟩
  rw [← he₀ t]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.ofBijective_apply]
  rfl

theorem exists_isSymSixType (hA : Nonempty (↥(generalizedFitting (s.h.subQuot s.y)) ≃*
      alternatingGroup (Fin 10))) :
    ∃ e : ↥s.h.J ⧸ pPrimeCore 2 ↥s.h.J ≃* alternatingGroup (Fin 6),
      ∀ (g : X) (hga : g ∈ centralizer ({s.h.a} : Set X)), g ∈ s.h.secG0 s.y →
        IsSymSixType e (Eight.oddBarAction s.h.J ⟨g, s.J_normal hga⟩) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₁, he₁⟩ := exists_altSix_equiv s.hp s.hp2 s.hf s.centralizer_eq hA s.sec.orderOf_a
    s.sec.J_le s.sec.isPComponent_J s.J_type
  obtain ⟨Θ, hΘ⟩ := s.exists_theta hA
  obtain ⟨e₀, he₀⟩ := s.exists_quot_equiv
  refine ⟨Θ.trans e₁, fun g hga hg0 => ?_⟩
  have hgJ : g ∈ normalizer (s.h.J : Set X) := s.J_normal hga
  have haH : s.h.a ∈ s.h.secSub s.y := s.secCond.a_mem_secSub
  have hgH : g ∈ s.h.secSub s.y := s.h.secC0_le_secSub s.y ⟨hga, hg0⟩
  set θg := s.h.subQ s.y ⟨g, hgH⟩ with hθg
  have hga' : g * s.h.a = s.h.a * g := mem_centralizer_singleton_iff.mp hga
  have hha : θg * s.sec.a = s.sec.a * θg := by
    rw [s.sec_a haH, hθg, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hga'
  have hgJ0 : ∀ j ∈ s.h.secJ0 s.y, g * j * g⁻¹ ∈ s.h.secJ0 s.y := by
    have hmap := GSLit.map_fixedLayer (MulAut.conj g) s.h.J (s.h.secB0 s.y)
    rw [map_conj_eq_of_mem_normalizer hgJ, map_conj_eq_of_mem_normalizer hg0] at hmap
    intro j hj
    have hmem : g * j * g⁻¹ ∈
        (GSLit.fixedLayer s.h.J (s.h.secB0 s.y)).map (MulAut.conj g).toMonoidHom := ⟨j, hj, rfl⟩
    rw [hmap] at hmem
    exact hmem
  have hN : θg ∈ normalizer (s.sec.J : Set (s.h.subQuot s.y)) := by
    apply mem_normalizer_of_conj_mem_fin
    intro x hx
    rw [s.sec_J] at hx ⊢
    obtain ⟨k, hk, rfl⟩ := hx
    refine ⟨⟨g, hgH⟩ * k * ⟨g, hgH⟩⁻¹, mem_subgroupOf.mpr (hgJ0 k (mem_subgroupOf.mp hk)), ?_⟩
    rw [map_mul, map_mul, map_inv]
  obtain ⟨σ, hσ⟩ := he₁ ⟨θg, hN⟩ hha
  refine ⟨σ, ?_⟩
  apply MulEquiv.ext
  intro c
  obtain ⟨q, rfl⟩ := (Θ.trans e₁).surjective c
  obtain ⟨u, rfl⟩ := e₀.surjective q
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective u
  rw [he₀ t]
  have h1 : Eight.oddBarAction s.h.J ⟨g, hgJ⟩ (s.piJ t) =
      s.piJ ⟨g * t * g⁻¹, hgJ0 t t.2⟩ := rfl
  have h2 : s.piSec ⟨g * t * g⁻¹, hgJ0 t t.2⟩ =
      s.sec.J.normalizerMonoidHom ⟨θg, hN⟩ (s.piSec t) := by
    apply Subtype.ext
    change s.h.subQ s.y ⟨g * t * g⁻¹, _⟩ = θg * s.h.subQ s.y ⟨t, _⟩ * θg⁻¹
    rw [hθg, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have h3 := congrArg (fun φ : MulAut (alternatingGroup (Fin 6)) => φ (e₁ (s.piSec t))) hσ
  change e₁ (s.sec.J.normalizerMonoidHom ⟨θg, hN⟩ (e₁.symm (e₁ (s.piSec t)))) =
    MulAut.conjNormal σ (e₁ (s.piSec t)) at h3
  rw [MulEquiv.symm_apply_apply] at h3
  change e₁ (Θ (Eight.oddBarAction s.h.J ⟨g, hgJ⟩ ((Θ.trans e₁).symm ((Θ.trans e₁)
    (s.piJ t))))) = MulAut.conjNormal σ (e₁ (Θ (s.piJ t)))
  rw [MulEquiv.symm_apply_apply, h1, hΘ, hΘ, h2, h3]

end Setting2

end Eight2

end CFSG.ComponentClassification.GSThmB
