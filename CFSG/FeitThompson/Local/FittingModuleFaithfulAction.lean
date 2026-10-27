module

public import CFSG.FeitThompson.Local.PrimeCentralizerComplementNoncentral
import CFSG.FeitThompson.Local.FixedOrderElementaryAbelianCover
import CFSG.FeitThompson.Local.FittingMonoNormal
import CFSG.FeitThompson.Local.PrimeCentralizerMinimalFittingAbelian
import CFSG.FeitThompson.Foundations.LiftHallByNormalComplement

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Matrix Pointwise Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

theorem natCard_sup_eq_mul_of_le_normalizer {K T : Subgroup G} (hT : T ≤ normalizer (K : Set G))
    (hdisj : K ⊓ T = ⊥) : Nat.card ↥(K ⊔ T) = Nat.card ↥K * Nat.card ↥T :=
  natCard_eq_mul_of_mul_eq_of_inf_eq_bot
    (Subgroup.coe_mul_of_right_le_normalizer_left K T hT).symm hdisj

variable [Finite G] {p : ℕ} {H R R0 V K U N P : Subgroup G}
  (hc : IsPrimeCentralizerKernelSetup p H R R0 V K U N P)

namespace IsPrimeCentralizerKernelSetup

include hc

theorem sup_K_R0_le_normalizer_K : K ⊔ R0 ≤ normalizer (K : Set G) :=
  sup_le Subgroup.le_normalizer (hc.admissible.le.trans hc.R_le_normalizer_K)

theorem coe_sup_K_R0 : ((K ⊔ R0 : Subgroup G) : Set G) = (K : Set G) * (R0 : Set G) :=
  Subgroup.coe_mul_of_right_le_normalizer_left K R0
    (hc.admissible.le.trans hc.R_le_normalizer_K)

theorem normal_V : V.Normal := by
  rw [hc.V_eq]; exact normal_map_subtype_fittingRaw hc.admissible.normal

theorem sup_K_R0_le_normalizer_V : K ⊔ R0 ≤ normalizer (V : Set G) :=
  have := hc.normal_V
  Subgroup.le_normalizer_of_normal

theorem centralizer_V_inf_H : centralizer (V : Set G) ⊓ H = V := by
  have := Fact.mk hc.prime_p
  rw [hc.V_eq]
  exact centralizer_map_subtype_fittingRaw_inf_eq_of_minimal hc.admissible
    hc.not_hasPLengthLeOne hc.minimal

theorem inf_K_centralizer_V : K ⊓ centralizer (V : Set G) = ⊥ := by
  rw [eq_bot_iff, ← hc.inf_K_V]
  intro x hx
  exact ⟨hx.1, hc.centralizer_V_inf_H ▸ ⟨hx.2, hc.K_le_H hx.1⟩⟩

theorem inf_K_R0 : K ⊓ R0 = ⊥ :=
  eq_bot_iff.2 ((inf_le_inf hc.K_le_H hc.admissible.le).trans hc.admissible.inf_eq_bot.le)

theorem le_centralizer_K : (K ⊔ R0) ⊓ centralizer (V : Set G) ≤ centralizer (K : Set G) := by
  have hCVn : (centralizer (V : Set G)).Normal :=
    have := hc.normal_V
    Subgroup.normal_centralizer
  intro c hcm
  refine mem_centralizer_iff.2 fun k hk => ?_
  have h1 : c * k * c⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.1 (hc.sup_K_R0_le_normalizer_K hcm.1) k).1 hk
  have h2 : k * c⁻¹ * k⁻¹ ∈ centralizer (V : Set G) :=
    hCVn.conj_mem _ ((centralizer (V : Set G)).inv_mem hcm.2) k
  have h3 : ⁅c, k⁆ ∈ K ⊓ centralizer (V : Set G) := by
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact K.mul_mem h1 (K.inv_mem hk)
    · have h4 : ⁅c, k⁆ = c * (k * c⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
      rw [h4]
      exact (centralizer (V : Set G)).mul_mem hcm.2 h2
  rw [hc.inf_K_centralizer_V, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
  exact h3.symm

theorem inf_sup_centralizer_V_eq_bot : (K ⊔ R0) ⊓ centralizer (V : Set G) = ⊥ := by
  set C := (K ⊔ R0) ⊓ centralizer (V : Set G) with hCdef
  by_contra hne
  have hCK : C ≤ centralizer (K : Set G) := hc.le_centralizer_K
  have hCnorm : C ≤ normalizer (K : Set G) := hCK.trans (Subgroup.centralizer_le_normalizer _)
  have hdisjC : K ⊓ C = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf_left K (inf_le_right (a := K ⊔ R0))).trans
      hc.inf_K_centralizer_V.le)
  have hcard1 : Nat.card ↥(K ⊔ C) = Nat.card ↥K * Nat.card ↥C :=
    natCard_sup_eq_mul_of_le_normalizer hCnorm hdisjC
  have hcard2 : Nat.card ↥(K ⊔ R0) = Nat.card ↥K * Nat.card ↥R0 :=
    natCard_sup_eq_mul_of_le_normalizer (hc.admissible.le.trans hc.R_le_normalizer_K) hc.inf_K_R0
  have hle : K ⊔ C ≤ K ⊔ R0 := sup_le le_sup_left inf_le_left
  have hdvd : Nat.card ↥C ∣ Nat.card ↥R0 := by
    have hd := Subgroup.card_dvd_of_le hle
    rw [hcard1, hcard2] at hd
    exact (mul_dvd_mul_iff_left (Nat.card_pos (α := ↥K)).ne').1 hd
  have hCcard : Nat.card ↥C = Nat.card ↥R0 :=
    (hc.admissible.prime_card.eq_one_or_self_of_dvd _ hdvd).resolve_left fun h1 =>
      hne (Subgroup.card_eq_one.1 h1)
  have hsupeq : K ⊔ C = K ⊔ R0 :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hcard1, hcard2, hCcard]))
  have hcop : (Nat.card ↥K).Coprime (Nat.card ↥R0) :=
    (hc.admissible.coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hc.K_le_H)).coprime_dvd_right
      (Subgroup.card_dvd_of_le hc.admissible.le)
  have hR0C : R0 ≤ C := by
    intro x hx
    have hxmem : x ∈ K ⊔ C := hsupeq ▸ Subgroup.mem_sup_right hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left K C hCnorm] at hxmem
    obtain ⟨k, hk, c, hcc, rfl⟩ := hxmem
    have hcomm : Commute k c := mem_centralizer_iff.1 (hCK hcc) k hk
    have hxr : (k * c) ^ Nat.card ↥R0 = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard R0 hx)
    have hkr : k ^ Nat.card ↥R0 = 1 := by
      have h1 : k ^ Nat.card ↥R0 * c ^ Nat.card ↥R0 = 1 := by
        rw [← hcomm.mul_pow]; exact hxr
      have h2 : k ^ Nat.card ↥R0 ∈ C := by
        rw [mul_eq_one_iff_eq_inv.1 h1]
        exact C.inv_mem (C.pow_mem hcc _)
      have h3 : k ^ Nat.card ↥R0 ∈ K ⊓ C := ⟨K.pow_mem hk _, h2⟩
      rw [hdisjC, Subgroup.mem_bot] at h3
      exact h3
    have hkK : k ^ Nat.card ↥K = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard K hk)
    have hone : orderOf k = 1 := by
      have hg := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hkK) (orderOf_dvd_of_pow_eq_one hkr)
      rw [hcop] at hg
      exact Nat.dvd_one.1 hg
    simpa [orderOf_eq_one_iff.1 hone] using hcc
  exact hc.not_le_centralizer_K (hR0C.trans hCK)

def actionV : ↥(K ⊔ R0) →* MulAut ↥V := conjOnNormalized V hc.sup_K_R0_le_normalizer_V

theorem actionV_apply_coe (x : ↥(K ⊔ R0)) (v : ↥V) :
    ((hc.actionV x v : ↥V) : G) = (x : G) * (v : G) * (x : G)⁻¹ :=
  conjOnNormalized_apply_coe _ x v

theorem injective_actionV : Function.Injective hc.actionV := by
  rw [actionV, ← MonoidHom.ker_eq_bot_iff, ker_conjOnNormalized, Subgroup.subgroupOf_eq_bot,
    disjoint_iff, inf_comm]
  exact hc.inf_sup_centralizer_V_eq_bot

theorem exists_mulEquiv_V : ∃ d : ℕ, 1 ≤ d ∧ Nat.card ↥V = p ^ d ∧
    Nonempty (↥V ≃* Multiplicative (Fin d → ZMod p)) := by
  have := Fact.mk hc.prime_p
  obtain ⟨d, hd1, hdcard, ⟨e⟩⟩ :=
    exists_mulEquiv_pi_fittingRaw_of_minimal hc.admissible hc.not_hasPLengthLeOne hc.minimal
      (p := p)
  have hV := hc.V_eq
  subst hV
  exact ⟨d, hd1, Nat.card_congr
      ((fittingRaw ↥H).equivMapOfInjective H.subtype H.subtype_injective).toEquiv.symm |>.trans
      hdcard,
    ⟨(((fittingRaw ↥H).equivMapOfInjective H.subtype H.subtype_injective).symm.trans e).trans
      (MulEquiv.piMultiplicative _).symm⟩⟩

theorem exists_injective_gl_rep : ∃ d : ℕ, 1 ≤ d ∧ Nat.card ↥V = p ^ d ∧
    ∃ (e : ↥V ≃* Multiplicative (Fin d → ZMod p)) (ρ : ↥(K ⊔ R0) →* GL (Fin d) (ZMod p)),
      Function.Injective ρ ∧ ∀ (x : ↥(K ⊔ R0)) (v : ↥V),
        (ρ x : Matrix (Fin d) (Fin d) (ZMod p)) *ᵥ Multiplicative.toAdd (e v)
          = Multiplicative.toAdd (e (hc.actionV x v)) := by
  obtain ⟨d, hd1, hdcard, ⟨e⟩⟩ := hc.exists_mulEquiv_V
  refine ⟨d, hd1, hdcard, e, (mulAutMulEquivGL ↥V e).toMonoidHom.comp hc.actionV,
    (mulAutMulEquivGL ↥V e).injective.comp hc.injective_actionV, fun x v => ?_⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, mulAutMulEquivGL_mulVec]
  simp

end IsPrimeCentralizerKernelSetup

end CFSG.FeitThompson

end
