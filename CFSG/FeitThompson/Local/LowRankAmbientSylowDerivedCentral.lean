module

public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.LowRankSylowCentralProduct
import CFSG.FeitThompson.Foundations.MinimalNormalInFittingCenter
import CFSG.FeitThompson.Local.SolvableDerivedKernelCommutators

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_le_center_of_natCard_eq_pow_three {p : ℕ} (hp : p.Prime) {B : Type*} [Group B]
    (hcard : Nat.card B = p ^ 3) (hZ : Nat.card (center B) = p) :
    _root_.commutator B ≤ center B := by
  have := Fact.mk hp
  have hq : Nat.card (B ⧸ center B) = p ^ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center B)
    rw [hcard, hZ, show p ^ 3 = p ^ 2 * p by ring] at h
    exact Nat.eq_of_mul_eq_mul_right hp.pos h.symm
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.1
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hq)

theorem natCard_center_eq_natCard_inf_centralizer (B : Subgroup G) :
    Nat.card (center ↥B) = Nat.card ↥(B ⊓ centralizer (B : Set G)) := by
  rw [← map_center_subtype_eq_inf_centralizer B,
    Subgroup.card_map_of_injective B.subtype_injective]

theorem commutator_le_inf_centralizer_of_commutator_le_center {B : Subgroup G}
    (h : _root_.commutator ↥B ≤ center ↥B) : ⁅B, B⁆ ≤ B ⊓ centralizer (B : Set G) := by
  rw [← Subgroup.map_subtype_commutator, ← map_center_subtype_eq_inf_centralizer]
  exact Subgroup.map_mono h

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup CFSG.FeitThompson
open scoped commutatorElement

universe u

theorem FTS_low_rank_ambient_sylow_derived_central
    (h₁ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FTS_low_rank_ambient_sylow_derived_central.{u} := by
  intro G _ _ hG p hp hpodd P hrank
  have := Fact.mk hp
  have hfin : Fintype G := Fintype.ofFinite G
  set R : Subgroup G := (P : Subgroup G)
  have hG6 : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  rcases em (IsMulCommutative ↥R) with hab | hab
  ·
    have hbot : ⁅R, R⁆ = ⊥ := by
      rw [← Subgroup.map_subtype_commutator, (_root_.commutator_eq_bot_iff ↥R).2 hab,
        Subgroup.map_bot]
    rw [hbot]
    exact bot_le
  ·
    have hRsyl : CFSG.FeitThompson.Prep06.IsSylowIn p R ⊤ :=
      ⟨le_top, by rw [Subgroup.card_top]; exact P.card_eq_multiplicity⟩
    obtain ⟨B, C, hBR, hCR, hsup, hBcard, hBnab, hBexp, hCne, hCcyc, hCZ, hBC, hBCset, hBCcard⟩ :=
      FPL_low_rank_sylow_central_product h₁ G hG6 p hp hpodd R hRsyl hrank hab
    have hCcent : ∀ c ∈ C, ∀ x ∈ R, Commute c x := fun c hc x hx =>
      (mem_centralizer_iff.1 (hCZ hc).2 x hx).symm
    have hZcard : Nat.card (center ↥B) = p := by
      rw [natCard_center_eq_natCard_inf_centralizer, ← hBC]; exact hBCcard
    have hBcomm : ⁅B, B⁆ ≤ B ⊓ C :=
      hBC ▸ commutator_le_inf_centralizer_of_commutator_le_center
        (commutator_le_center_of_natCard_eq_pow_three hp hBcard hZcard)
    have hBnorm : B ≤ normalizer (C : Set G) := fun b hb =>
      centralizer_le_normalizer _ (mem_centralizer_iff.2 fun c hc =>
        (hCcent c hc b (hBR hb)).eq)
    have hRset : ∀ x ∈ R, ∃ b ∈ B, ∃ c ∈ C, x = b * c := by
      intro x hx
      have hmem : x ∈ ((B ⊔ C : Subgroup G) : Set G) := by rw [hsup]; exact hx
      rw [Subgroup.coe_mul_of_left_le_normalizer_right B C hBnorm] at hmem
      obtain ⟨b, hb, c, hc, rfl⟩ := hmem
      exact ⟨b, hb, c, hc, rfl⟩
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨b₁, hb₁, c₁, hc₁, rfl⟩ := hRset x hx
    obtain ⟨b₂, hb₂, c₂, hc₂, rfl⟩ := hRset y hy
    have hccomm : ⁅c₁, c₂⁆ = 1 :=
      commutatorElement_eq_one_iff_commute.2 (hCcent c₁ hc₁ c₂ (hCR hc₂))
    rw [commutatorElement_mul_mul_of_forall_commute (A := B) (B := C)
        (fun b hb c hc => (hCcent c hc b (hBR hb)).symm) hb₁ hb₂ hc₁ hc₂, hccomm, mul_one]
    have hmem := hBcomm (Subgroup.commutator_mem_commutator hb₁ hb₂)
    exact ⟨hCR hmem.2, (hCZ hmem.2).2⟩

end

end CFSG.FeitThompson.Proofs
