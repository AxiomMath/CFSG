module

public import CFSG.GH74.GLS.TwoThin.Bridge
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65

open Subgroup CFSG
open scoped commutatorElement

theorem exists_odd_cover_of_two_quotients {I Q₁ Q₂ : Type} [Group I] [Finite I] [Group Q₁] [Group Q₂]
    (f₁ : I →* Q₁) (f₂ : I →* Q₂) (h1 : Function.Surjective f₁) (h2 : Function.Surjective f₂)
    (hodd₁ : Odd (Nat.card f₁.ker)) (hodd₂ : Odd (Nat.card f₂.ker))
    (hQ₁ : IsSimpleGroup Q₁) (hQ₁n : ∃ a b : Q₁, a * b ≠ b * a) :
    ∃ g : Q₂ →* Q₁, Function.Surjective g ∧ Odd (Nat.card g.ker) ∧ ∀ i, g (f₂ i) = f₁ i := by
  have : Finite Q₁ := Finite.of_surjective f₁ h1
  have hN : (f₂.ker.map f₁).Normal := Subgroup.Normal.map inferInstance f₁ h1
  have hker : f₂.ker ≤ f₁.ker := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (f₂.ker.map f₁) with hb | ht
    · exact (Subgroup.map_eq_bot_iff _).1 hb
    · exfalso
      have hcard : Nat.card ↥(f₂.ker.map f₁) ∣ Nat.card f₂.ker :=
        Subgroup.card_map_dvd _ _
      have hodd : Odd (Nat.card ↥(f₂.ker.map f₁)) := Odd.of_dvd_nat hodd₂ hcard
      rw [ht, Subgroup.card_top] at hodd
      have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
      obtain ⟨a, b, hab⟩ := hQ₁n
      have : Nontrivial Q₁ := ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
      have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial Q₁
      have hbot : commutator Q₁ = ⊥ :=
        (IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q₁)).resolve_right hlt.ne
      have hmem : ⁅a, b⁆ ∈ commutator Q₁ := by
        rw [_root_.commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hab hmem
  exact CFSG.GH74.GLS.TwoThin.exists_odd_quotient_of_ker_le f₂ h2 f₁ h1 hker hodd₁

theorem quasisimple_quot_of_odd_cover {Q Q₁ : Type} [Group Q] [Finite Q] [Group Q₁]
    (hQ : IsQuasisimple Q) (hQ₁ : IsSimpleGroup Q₁) (hn : ∃ a b : Q₁, a * b ≠ b * a)
    (g : Q →* Q₁) (hg : Function.Surjective g) (hodd : Odd (Nat.card g.ker)) :
    g.ker = center Q ∧ Nonempty (Q ⧸ center Q ≃* Q₁) ∧ Odd (Nat.card (center Q)) := by
  have hc₁ : center Q₁ = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q₁) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hn
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  have hle : g.ker ≤ center Q := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ g.normal_ker with h | h
    · exfalso
      have hone : ∀ x : Q, g x = 1 := fun x => MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top x)
      obtain ⟨a, b, hab⟩ := hn
      obtain ⟨x, rfl⟩ := hg a
      obtain ⟨y, rfl⟩ := hg b
      apply hab
      rw [hone x, hone y]
    · exact h
  have hge : center Q ≤ g.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have : g x ∈ center Q₁ := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y', rfl⟩ := hg y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y']
    rw [hc₁, Subgroup.mem_bot] at this
    exact this
  have heq : g.ker = center Q := le_antisymm hle hge
  refine ⟨heq, ?_, heq ▸ hodd⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq heq.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65
