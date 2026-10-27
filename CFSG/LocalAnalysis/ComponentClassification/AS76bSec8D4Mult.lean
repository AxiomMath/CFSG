module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4Defs
public import CFSG.LocalAnalysis.SectionRank.TrialityEvenCover
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.D4

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
open CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.SectionRank

section Model

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem map_twistedGroup_eq_d4C
    {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = (2 ^ m) ^ 3)
    (hσq : ∀ c, σ c = c ^ 2 ^ m) :
    (twistedGroup σ.toRingHom).map (adjointGroup d4 K).subtype = d4C K σ := by
  have hq : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  rw [← commutator_twistedFixedGroup_eq_map σ.toRingHom hq hK hσq]
  exact (finite_fixed_root_group_perfect TwistTag.D4 Nat.prime_two hm K hK σ.toRingHom
    hσq).2.2.1

@[expose] noncomputable def twistedGroupEquivD4C
    {m : ℕ} (hm : 1 ≤ m)
    (hK : Nat.card K = (2 ^ m) ^ 3) (hσq : ∀ c, σ c = c ^ 2 ^ m) :
    twistedGroup σ.toRingHom ≃* ↥(d4C K σ) :=
  (Subgroup.equivMapOfInjective (twistedGroup σ.toRingHom) (adjointGroup d4 K).subtype
    Subtype.val_injective).trans (MulEquiv.subgroupCongr (map_twistedGroup_eq_d4C σ hm hK hσq))

end Model

theorem d4CentralExtSplit :
    ∀ (m : ℕ), 1 ≤ m → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ m) ^ 3 →
      ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2 ^ m) →
        ∀ (E : Type) [Group E] [Finite E] (π : E →* ↥(d4C K σ)), Function.Surjective π →
          π.ker ≤ center E → Odd (Nat.card π.ker) → ∃ s : ↥(d4C K σ) →* E, ∀ g, π (s g) = g := by
  intro m hm K _ _ hK σ hσq E _ _ π hπ hker hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := m * 3)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c :=
    sigma_three_of_card (σ := σ.toRingHom) hK hσq
  set eT := twistedGroupEquivD4C σ hm hK hσq
  set ψ : E →* twistedGroup σ.toRingHom := eT.symm.toMonoidHom.comp π with hψdef
  have hψker : ψ.ker = π.ker := ker_mulEquiv_comp π eT.symm
  have hψ : Function.Surjective ψ := eT.symm.surjective.comp hπ
  obtain ⟨s, hs, -, -⟩ := triality_even_central_odd_extension_splitting hσ3 hψ
    (by rw [hψker]; exact hker) (by rw [hψker]; exact hodd)
  exact ⟨s.comp eT.symm.toMonoidHom, fun g => eT.symm.injective (hs (eT.symm g))⟩

theorem center_eq_bot_of_d4
    {m : ℕ} (hm : 1 ≤ m) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ m) ^ 3) (σ : K ≃+* K) (hσq : ∀ c, σ c = c ^ 2 ^ m) {A : Type}
    [Group A] [Finite A] (hA : commutator A = ⊤) (hZ : Odd (Nat.card (center A)))
    (e : A ⧸ center A ≃* ↥(d4C K σ)) : center A = ⊥ := by
  have : Group.IsPerfect A := ⟨hA⟩
  set π : A →* ↥(d4C K σ) := e.toMonoidHom.comp (QuotientGroup.mk' (center A)) with hπdef
  have hπker : π.ker = center A := by
    rw [hπdef, ker_mulEquiv_comp, QuotientGroup.ker_mk']
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨s, hs⟩ := d4CentralExtSplit m hm K hK σ hσq A π hπ hπker.le
    (by rw [hπker]; exact hZ)
  rw [← hπker]
  exact ker_eq_bot_of_section_of_perfect π hπker.le s hs

end CFSG.ComponentClassification.RankTwoExceptional.D4
