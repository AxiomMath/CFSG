module

public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I142

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

@[expose] def centFix {X : Type*} [Group X] (A : Subgroup (MulAut X)) : Subgroup X :=
  ⨅ (e : MulAut X) (_ : e ∈ A), CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup e

theorem mem_centFix {X : Type*} [Group X] {A : Subgroup (MulAut X)} {x : X} :
    x ∈ centFix A ↔ ∀ e ∈ A, e x = x := by
  simp only [centFix, Subgroup.mem_iInf, CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup]

@[reducible, expose] def LieSemisimpleCentE : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsChevSimple 2 S → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ E : Subgroup (MulAut S),
      IsElemAbelian p E → ∀ P : Subgroup S, P ≤ centFix E → ⁅P, P⁆ = P →
        P ≤ GLALayer (centFix E)

variable {G : Type} [Group G]

@[expose] noncomputable def Ebar (p : ℕ) (K E : Subgroup G) : Subgroup (MulAut (PSimple p K)) :=
  (E.subgroupOf (Subgroup.normalizer (K : Set G))).map (chevAut p K)

theorem chevAut_mk (p : ℕ) (K : Subgroup G) (γ : ↥(Subgroup.normalizer (K : Set G)))
    (x : PQuot p K) :
    chevAut p K γ (QuotientGroup.mk' (Subgroup.center (PQuot p K)) x) =
      QuotientGroup.mk' (Subgroup.center (PQuot p K)) (barAut p K γ x) := by
  obtain ⟨k, rfl⟩ := pQuotHom_surjective p K x
  have h := chevAut_chevQuotHom p K γ k
  rw [barAut_pQuotHom]
  exact h

theorem mem_centFix_mk_iff (p : ℕ) (K E : Subgroup G) (x : PQuot p K) :
    QuotientGroup.mk' (Subgroup.center (PQuot p K)) x ∈ centFix (Ebar p K E) ↔
      ∀ γ ∈ E.subgroupOf (Subgroup.normalizer (K : Set G)),
        QuotientGroup.mk' (Subgroup.center (PQuot p K)) (barAut p K γ x) =
          QuotientGroup.mk' (Subgroup.center (PQuot p K)) x := by
  rw [mem_centFix]
  constructor
  · intro h γ hγ
    have := h (chevAut p K γ) (Subgroup.mem_map_of_mem _ hγ)
    rwa [chevAut_mk] at this
  · intro h e he
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 he
    rw [chevAut_mk]
    exact h γ hγ

theorem coprime_card_glaPPrimeCoreOf [Finite G] (p : ℕ) [hp : Fact p.Prime] (K : Subgroup G) :
    Nat.Coprime p (Nat.card ↥(GLAPPrimeCoreOf p K)) := by
  have h : GLAPPrimeCoreOf p K = (GLAPPrimeCore p ↥K).map K.subtype := rfl
  rw [h, Subgroup.card_map_of_injective K.subtype_injective]
  exact CFSG.pPrimeCore_coprime_card

instance normal_glaPPrimeCoreOf_subgroupOf (p : ℕ) (K : Subgroup G) :
    ((GLAPPrimeCoreOf p K).subgroupOf K).Normal := by
  have : (GLAPPrimeCoreOf p K).subgroupOf K = GLAPPrimeCore p ↥K :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  rw [this]
  infer_instance

end CFSG.LocalAnalysis.GLTheoremA.I142
