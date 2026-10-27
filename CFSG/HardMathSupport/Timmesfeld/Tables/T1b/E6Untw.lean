module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6TorusLower
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6Rank

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open

@[expose] def E6RankLowerUntw : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (n r f : ℕ),
    CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .E6 n r f → 3 ∣ r ^ f - 1 →
      (3 ∣ Nat.card (Subgroup.center L) → 6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L)) ∧
      (9 ∣ r ^ f - 1 → 6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ Subgroup.center L)))

@[expose] def E6RankLowerTw : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (n r f : ℕ),
    CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .twistedE6 n r f → 3 ∣ r ^ f + 1 →
      (3 ∣ Nat.card (Subgroup.center L) → 6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L)) ∧
      (9 ∣ r ^ f + 1 → 6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ Subgroup.center L)))

theorem e6RankLower_of_parts (hU : E6RankLowerUntw) (hT : E6RankLowerTw) : E6RankLower := by
  intro L _ _ _ t n r f hm hpar
  rcases hpar with ⟨rfl, h3⟩ | ⟨rfl, h3⟩
  · obtain ⟨h1, h2⟩ := hU L n r f hm h3
    exact ⟨h1, fun h _ => h2 (h rfl)⟩
  · obtain ⟨h1, h2⟩ := hT L n r f hm h3
    exact ⟨h1, fun _ h => h2 (h rfl)⟩

theorem exists_hom_of_untwistedModel
    {K : Type} [Field K] [Finite K] {L : Type} [Group L]
    (e : (L ⧸ Subgroup.center L) ≃* AdjointQuotient Tag.E6 K) :
    ∃ ψ : (L ⧸ Subgroup.center L) ≃* adjointGroup Tag.E6 K,
      ∀ x : L, ψ (QuotientGroup.mk x) = 1 ↔ x ∈ Subgroup.center L := by
  have hcen := center_adjointGroup_eq_bot (τ := Tag.E6) (K := K)
  let φ : AdjointQuotient Tag.E6 K →* adjointGroup Tag.E6 K :=
    QuotientGroup.lift _ (MonoidHom.id _) (fun x hx => by
      rw [hcen] at hx
      exact (Subgroup.mem_bot.1 hx))
  have hφ : ∀ x : adjointGroup Tag.E6 K, φ (QuotientGroup.mk x) = x := fun x => rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hφ] at hy
    rw [hy]
    exact QuotientGroup.mk_one _
  have hsurj : Function.Surjective φ := fun x => ⟨QuotientGroup.mk x, hφ x⟩
  refine ⟨e.trans (MulEquiv.ofBijective φ ⟨hinj, hsurj⟩), fun x => ?_⟩
  change φ (e (QuotientGroup.mk x)) = 1 ↔ _
  rw [← map_one φ, hinj.eq_iff, ← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff]

theorem e6RankLowerUntw :
    E6RankLowerUntw := by
  intro L _ _ n r f hm h3
  have hU : UntwistedChevalleyModel (L ⧸ Subgroup.center L) .E6 (r ^ f) := by
    rcases hm with ⟨ht, -⟩ | ⟨-, -, ⟨-, hc⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact hc
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨K, _, _, hcard, ⟨e⟩⟩ := hU
  obtain ⟨ψ, hψ⟩ := exists_hom_of_untwistedModel e
  have hK3 : 3 ∣ Nat.card K - 1 := by rw [hcard]; exact h3
  refine ⟨fun hZ => ?_, fun h9 => ?_⟩
  · refine six_le_pRank_of_cover_E6 hK3
      ((ψ : (L ⧸ Subgroup.center L) →* _).comp (QuotientGroup.mk' _)) ?_ ?_ hZ
    · intro y
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (ψ.symm y)
      exact ⟨x, by simp [hx]⟩
    · intro x
      exact hψ x
  · have h9K : 9 ∣ Nat.card K - 1 := by rw [hcard]; exact h9
    obtain ⟨E, hE, hcE⟩ := exists_elemAbelian_E6_torus hK3 h9K
    have hE' := CFSG.SectionRank.isElemAbelian_map hE ψ.symm.toMonoidHom
    have hc' : Nat.card (E.map ψ.symm.toMonoidHom) = 3 ^ 6 := by
      rw [Subgroup.card_map_of_injective ψ.symm.injective, hcE]
    exact CFSG.SectionRank.le_pRank (by norm_num) le_top hE' hc'

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
