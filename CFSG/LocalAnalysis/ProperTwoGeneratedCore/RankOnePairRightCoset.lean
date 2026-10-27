module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RankOnePairDoubleTransitive
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometryEmbedding

public section

namespace CFSG.ProperTwoGeneratedCore.RankOnePair

open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G] [Finite G]

theorem rightCoset_odd_degree_rank_one_pair_centralizer_meets_involution_classes
    (H : Subgroup G)
    (hfaithful : ∀ g : G, (∀ omega : rightCosetSpace H, rightCosetTranslate H omega g = omega) →
      g = 1)
    (hdoubly : ∀ a b c d : rightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, rightCosetTranslate H a g = c ∧ rightCosetTranslate H b g = d)
    (hodd : Odd H.index) {α β : rightCosetSpace H} (hαβ : α ≠ β)
    (hrank : CFSG.Open.pRank 2 (rightCosetStabilizer H α ⊓ rightCosetStabilizer H β) = 1)
    {u : G} (huB : u ∈ rightCosetStabilizer H α ⊓ rightCosetStabilizer H β)
    (hu : orderOf u = 2)
    (htransitive : ∀ γ δ : rightCosetSpace H, rightCosetTranslate H γ u = γ →
      rightCosetTranslate H δ u = δ →
      ∃ c ∈ Subgroup.centralizer ({u} : Set G), rightCosetTranslate H γ c = δ)
    (T : Sylow 2 ↥(Subgroup.centralizer ({u} : Set G) ⊓ rightCosetStabilizer H α))
    (v : G) (hv : orderOf v = 2) :
    ∃ g : G, g⁻¹ * v * g ∈ (T : Subgroup _).map
      (Subgroup.centralizer ({u} : Set G) ⊓ rightCosetStabilizer H α).subtype := by
  classical
  let : MulAction G (rightCosetSpace H) :=
    { smul := fun g omega => rightCosetTranslate H omega g⁻¹
      one_smul := fun omega => by
        change rightCosetTranslate H omega 1⁻¹ = omega
        rw [inv_one, rightCosetTranslate_one]
      mul_smul := fun g k omega => by
        change rightCosetTranslate H omega (g * k)⁻¹ =
          rightCosetTranslate H (rightCosetTranslate H omega k⁻¹) g⁻¹
        rw [rightCosetTranslate_mul, mul_inv_rev] }
  have hsmul : ∀ (g : G) (omega : rightCosetSpace H),
      g • omega = rightCosetTranslate H omega g⁻¹ := fun _ _ => rfl
  have hstab : ∀ omega, MulAction.stabilizer G omega = rightCosetStabilizer H omega := by
    intro omega
    ext g
    rw [MulAction.mem_stabilizer_iff, hsmul, mem_rightCosetStabilizer_iff]
    constructor
    · intro h
      have h' := congrArg (fun x => rightCosetTranslate H x g) h
      simp only [rightCosetTranslate_mul, inv_mul_cancel, rightCosetTranslate_one] at h'
      exact h'.symm
    · intro h
      have h' := congrArg (fun x => rightCosetTranslate H x g⁻¹) h
      simp only [rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one] at h'
      exact h'.symm
  have : FaithfulSMul G (rightCosetSpace H) := ⟨fun {g₁ g₂} h => by
    have hfix : ∀ omega : rightCosetSpace H,
        rightCosetTranslate H omega (g₁⁻¹ * g₂) = omega := by
      intro omega
      have h' := h omega
      rw [hsmul, hsmul] at h'
      rw [← rightCosetTranslate_mul, h', rightCosetTranslate_mul, inv_mul_cancel,
        rightCosetTranslate_one]
    exact inv_mul_eq_one.mp (hfaithful _ hfix)⟩
  have : MulAction.IsMultiplyPretransitive G (rightCosetSpace H) 2 := by
    refine MulAction.is_two_pretransitive_iff.mpr fun {a b c d} hab hcd => ?_
    obtain ⟨g, hac, hbd⟩ := hdoubly a b c d hab hcd
    exact ⟨g⁻¹, by rw [hsmul, inv_inv, hac], by rw [hsmul, inv_inv, hbd]⟩
  have hodd' : Odd (Nat.card (rightCosetSpace H)) := by
    rw [Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H)]
    exact hodd
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by
    rw [← pow_two, ← hu, pow_orderOf_eq_one])
  have htransitive' : ∀ γ δ : rightCosetSpace H, u • γ = γ → u • δ = δ →
      ∃ c ∈ Subgroup.centralizer ({u} : Set G), c • γ = δ := by
    intro γ δ hγ hδ
    rw [hsmul, huinv] at hγ hδ
    obtain ⟨c, hc, hcγ⟩ := htransitive γ δ hγ hδ
    exact ⟨c⁻¹, Subgroup.inv_mem _ hc, by rw [hsmul, inv_inv, hcγ]⟩
  obtain ⟨T', hT'⟩ : ∃ T' : Sylow 2 ↥(Subgroup.centralizer ({u} : Set G) ⊓
      MulAction.stabilizer G α), (T' : Subgroup _).map
        (Subgroup.centralizer ({u} : Set G) ⊓ MulAction.stabilizer G α).subtype =
      (T : Subgroup _).map
        (Subgroup.centralizer ({u} : Set G) ⊓ rightCosetStabilizer H α).subtype := by
    rw [hstab α]
    exact ⟨T, rfl⟩
  obtain ⟨g, hg⟩ := odd_degree_rank_one_pair_centralizer_meets_involution_classes hodd' hαβ
    (by rw [hstab, hstab]; exact hrank) (by rw [hstab, hstab]; exact huB) hu htransitive' T'
    v hv
  exact ⟨g, hT' ▸ hg⟩

end CFSG.ProperTwoGeneratedCore.RankOnePair
