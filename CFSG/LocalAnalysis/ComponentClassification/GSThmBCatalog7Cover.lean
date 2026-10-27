module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7CoverInputs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7Rec
public import CFSG.LocalAnalysis.SectionRank.EvenCover.CoverMap
public import CFSG.LieType.Steinberg.CentralExt.SymplecticPerfect
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7Cover

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.SectionRank.EvenCover CFSG.LieType.Steinberg

theorem sp_existsUnique_section_of_coprime
    {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (r : ℕ)
    {E : Type*} [Group E] [Finite E] {π : E →* StatedSp r K} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ center E) (hC : ¬ p ∣ Nat.card π.ker) :
    ∃! σ : StatedSp r K →* E, ∀ g, π (σ g) = g :=
  sp_existsUnique_section_of_sl2_lift r hπ hcen hC fun ρ => by
    obtain ⟨ρ', hρ', -⟩ := sl2_existsUnique_lift hπ hcen hC ρ
    exact ⟨ρ', fun g => congrArg (· g) hρ'⟩

theorem nonempty_mulEquiv_statedSp
    {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] {r : ℕ}
    {L : Type*} [Group L] [Finite L] [Group.IsPerfect L] (hZ : center L ≠ ⊥)
    (hC : ¬ p ∣ Nat.card (center L)) (e : L ⧸ center L ≃* StatedProj (StatedSp r K)) :
    Nonempty (L ≃* StatedSp r K) := by
  obtain ⟨hsurj, hcen, hdvd⟩ := pullbackFst_centralQuotientMap e
  obtain ⟨σ, hσ, -⟩ :=
    sp_existsUnique_section_of_coprime r hsurj hcen fun h => hC (h.trans hdvd)
  obtain ⟨φ, hφs, hφk, hD⟩ := perfect_cover_map_of_section e σ hσ
  have hD2 := card_statedScalars_subgroupOf_statedSp_le_two r K
  have hker : φ.ker = ⊥ := by
    by_contra hne
    have h1 : 1 < Nat.card φ.ker := (one_lt_card_iff_ne_bot _).mpr hne
    have heq : φ.ker = (StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K) :=
      eq_of_le_of_card_ge hφk (by have := card_le_of_le hφk; omega)
    apply hZ
    rw [← hD, ← heq]
    exact (Subgroup.map_eq_bot_iff _).mpr le_rfl
  exact ⟨(MulEquiv.ofBijective φ ⟨(MonoidHom.ker_eq_bot_iff φ).mp hker, hφs⟩).symm⟩

theorem cfSp4CoverInv
    (hPP : Sp4CenterPPartInput) : CFSp4CoverInv := by
  intro G _ _ p f hp hp2 hf Y hY hZ hm t _ _ M hMle hM
  have : Fact p.Prime := ⟨hp⟩
  have hC := hPP Y p f hp hp2 hY hm
  obtain ⟨-, -, K, _, _, hK, ⟨eK⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ := hm
  rotate_left
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have : Group.IsPerfect Y := hY.1
  obtain ⟨eY⟩ := nonempty_mulEquiv_statedSp hZ hC eK
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  exact CatFactsSp4.center_quotient_ne_bot_of_le h2 eY hMle (hMle.trans inf_le_left) hM

end Catalog7Cover

end CFSG.ComponentClassification.GSThmB
