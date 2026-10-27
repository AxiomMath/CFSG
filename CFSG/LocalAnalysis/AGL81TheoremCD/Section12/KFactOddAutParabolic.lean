module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.AGLEmbedding

@[expose] def KFactOddAutParabolicFix : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L →
    IsClassicalTwoOrG2 (L ⧸ Subgroup.center L) →
    ∀ P : Subgroup L, IsParabolicTwo ⊤ P →
    ∀ r : ℕ, r.Prime → 5 ≤ r → ¬ r ∣ Nat.card P →
    ∀ (α : MulAut L) (k : ℕ), orderOf α = r ^ k →
      Subgroup.zpowers α ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner L = ⊥ →
      ∃ y : L, (P.map (MulAut.conj y).toMonoidHom).map α.toMonoidHom =
        P.map (MulAut.conj y).toMonoidHom

@[expose] def KFactOddAutParabolicFixPrime : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L →
    IsClassicalTwoOrG2 (L ⧸ Subgroup.center L) →
    ∀ P : Subgroup L, IsParabolicTwo ⊤ P →
    ∀ r : ℕ, r.Prime → 5 ≤ r → ¬ r ∣ Nat.card P →
    ∀ α : MulAut L, α ^ r = 1 → α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner L →
      ∃ y : L, (P.map (MulAut.conj y).toMonoidHom).map α.toMonoidHom =
        P.map (MulAut.conj y).toMonoidHom

theorem kFactOddAutParabolicFixPrime_of_general (h : KFactOddAutParabolicFix) :
    KFactOddAutParabolicFixPrime := by
  intro L _ _ hL hLY P hP r hr hr5 hrP α hα hαinn
  have hα1 : α ≠ 1 := fun h1 => hαinn (h1 ▸ Subgroup.one_mem _)
  have : Fact r.Prime := ⟨hr⟩
  have hord : orderOf α = r := orderOf_eq_prime hα hα1
  have : Finite (MulAut L) :=
    Finite.of_injective (fun f : MulAut L => (f : L → L)) fun f g hfg => MulEquiv.ext (congrFun hfg)
  refine h L hL hLY P hP r hr hr5 hrP α 1 (by rw [pow_one, hord]) ?_
  rw [eq_bot_iff]
  intro β hβ
  obtain ⟨hβz, hβi⟩ := Subgroup.mem_inf.mp hβ
  rw [Subgroup.mem_bot]
  by_contra hne
  apply hαinn
  have hle : Subgroup.zpowers β ≤ Subgroup.zpowers α := Subgroup.zpowers_le.mpr hβz
  have hβord : orderOf β = r := by
    have hdvd : orderOf β ∣ r := hord ▸ orderOf_dvd_of_mem_zpowers hβz
    rcases (Nat.dvd_prime hr).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hne
    · exact h1
  have heq : Subgroup.zpowers β = Subgroup.zpowers α := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Nat.card_zpowers, Nat.card_zpowers, hord, hβord]
  have hαβ : α ∈ Subgroup.zpowers β := heq ▸ Subgroup.mem_zpowers α
  exact Subgroup.zpowers_le.mpr hβi hαβ

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
