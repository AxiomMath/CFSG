module

public import CFSG.LocalAnalysis.SectionRank.TrialityEvenCover
public import CFSG.LieType.HighestRoot.GenModels
public import CFSG.LieType.Chevalley.GraphFixedOddPerfect

public section

namespace CFSG.LieType.Steinberg.CentralExt.TrialityClosed

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits

variable {K : Type} [Field K] {σ : K →+* K}

theorem triality_exists_section_of_coprime [Finite K] (hσ : ∀ c, σ (σ (σ c)) = c) {p : ℕ}
    [Fact p.Prime] [CharP K p] {E : Type*} [Group E] [Finite E] {π : E →* twistedGroup σ}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hC : p.Coprime (Nat.card π.ker)) :
    ∃ s : twistedGroup σ →* E, ∀ g, π (s g) = g := by
  have hC' : ¬ p ∣ Nat.card π.ker := (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hC
  have : Finite (fixedField σ) := Subtype.finite
  refine (existsUnique_section_of_rankOne_lift (p := p) (twistedDatum_isCTGroupDatum σ hσ)
    (twistedDatum_steinbergExtras σ hσ)
    (fun β hβ => HighestRoot.isPGroup_twistedD4_rootGroup σ hσ
      (isRoot_of_mem_twistedDatum_roots σ hβ)) hπ hcen hC' fun i => ?_).exists
  match i with
  | ⟨0, _⟩ =>
    obtain ⟨ρ', hρ', -⟩ := SectionRank.EvenCover.sl2_existsUnique_lift hπ hcen hC' (slLong σ hσ)
    exact exists_lift_of_injective (slLong_injective hσ) (SectionRank.rankOne_long_le_range hσ)
      fun g => DFunLike.congr_fun hρ' g
  | ⟨1, _⟩ =>
    obtain ⟨ρ', hρ', -⟩ := SectionRank.EvenCover.sl2_existsUnique_lift hπ hcen hC' (slShort σ hσ)
    exact exists_lift_of_injective (slShort_injective hσ)
      (SectionRank.rankOne_short_le_range_slShort hσ) fun g => DFunLike.congr_fun hρ' g

theorem map_twistedGroup_eq_graphFixedRootGroup [Finite K] (hK2 : ringChar K ≠ 2) {q : ℕ}
    (hq : 2 ≤ q) (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) :
    (twistedGroup σ).map (adjointGroup d4 K).subtype = graphFixedRootGroup TwistTag.D4 K σ := by
  let σK : K ≃+* K := RingEquiv.ofBijective σ
    ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσK : σK.toRingHom = σ := RingHom.ext fun _ => rfl
  have h1 := (odd_diagram_fixed_root_group_perfect TwistTag.D4 K hK2 σK).2.2
  rw [hσK] at h1
  exact (commutator_twistedFixedGroup_eq_map σ hq hK hσq).symm.trans h1

theorem twistedGroup_center_eq_bot_of_card [Finite K] {q : ℕ} (hq : 2 ≤ q)
    (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) :
    Subgroup.center (twistedGroup σ) = ⊥ := by
  have hσ : ∀ c, σ (σ (σ c)) = c := fun c => by
    have := sigma_three_of_card hK hσq
    exact this c
  by_cases h2 : ringChar K = 2
  · have : CharP K 2 := ringChar.of_eq h2
    exact SectionRank.twistedGroup_center_eq_bot hσ
  · let σK : K ≃+* K := RingEquiv.ofBijective σ
      ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
    have hσK : σK.toRingHom = σ := RingHom.ext fun _ => rfl
    have hZ := exceptional_fixed_center_trivial TwistTag.D4 K σK
    rw [hσK] at hZ
    let e : twistedGroup σ ≃* graphFixedRootGroup TwistTag.D4 K σ :=
      (Subgroup.equivMapOfInjective (twistedGroup σ) (adjointGroup d4 K).subtype
        Subtype.val_injective).trans
        (MulEquiv.subgroupCongr (map_twistedGroup_eq_graphFixedRootGroup h2 hq hK hσq))
    exact SectionRank.center_eq_bot_of_mulEquiv' e.symm hZ

end CFSG.LieType.Steinberg.CentralExt.TrialityClosed
