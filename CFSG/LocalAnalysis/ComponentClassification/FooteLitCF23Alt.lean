module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Base
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdEven
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrStableAlternating

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup Assembly.LowTwoRank Equiv

theorem exists_ne_comm_alt {n : ℕ} (hn : 4 ≤ n) :
    ∃ a b : ↥(alternatingGroup (Fin n)), a * b ≠ b * a := by
  have : Nontrivial ↥(alternatingGroup (Fin n)) :=
    alternatingGroup.nontrivial_of_three_le_card (by simp; omega)
  by_contra h
  push Not at h
  have hc : center ↥(alternatingGroup (Fin n)) = ⊤ :=
    eq_top_iff.mpr fun x _ => mem_center_iff.mpr fun g => h g x
  rw [alternatingGroup.center_eq_bot (by simp; omega)] at hc
  exact bot_ne_top hc

theorem cf23Exception_alt {N J : Type} [Group N] [Group J] {n k : ℕ}
    (φ : N ≃* alternatingGroup (Fin n)) (eJ : J ≃* alternatingGroup (Fin k))
    (hk : k = 5 ∨ k = 6 ∨ k = 7) (hn : n = k + 2 ∨ n = k + 4) :
    CF23Exception N (J ⧸ center J) := by
  let eZ : J ⧸ center J ≃* alternatingGroup (Fin k) :=
    (QuotientGroup.congr _ _ eJ (map_center_eq eJ)).trans
      ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by simp; omega))).trans
        QuotientGroup.quotientBot)
  refine Or.inl ⟨k, hk, ⟨eZ⟩, ?_⟩
  rcases hn with rfl | rfl
  · exact Or.inl ⟨φ⟩
  · exact Or.inr ⟨φ⟩


theorem alt : CF23InnerFusionFor fun Y _ =>
    ∃ n : ℕ, 7 ≤ n ∧ Nonempty (Y ≃* alternatingGroup (Fin n)) := by
  intro G _ _ N hN hC hY α J hα hJN hJα hJ hstd hsmall _ hexc
  obtain ⟨n, hn7, ⟨φ⟩⟩ := hY
  exfalso
  apply hexc
  have := hN
  have hs : IsSimpleGroup ↥N := by
    have : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by simp; omega)
    exact φ.isSimpleGroup
  obtain ⟨a, b, hab⟩ := exists_ne_comm_alt (n := n) (by omega)
  have hnab : ∃ x y : ↥N, x * y ≠ y * x :=
    ⟨φ.symm a, φ.symm b, fun h => hab (by simpa using congrArg φ h)⟩
  have hJc : Assembly.IsComponentOf J (centralizer ({α} : Set G)) :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hJα).2 hJ
  have hsrc : (∃ p f : ℕ, p ≠ 2 ∧ StatedClassicalModel (↥J ⧸ center ↥J) .PSL 2 p f) ∨
      Nonempty (↥J ⧸ center ↥J ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (↥J ⧸ center ↥J) .PSL 3 2 2 := by
    rcases hsmall with ⟨p, f, -, hp2, -, -, hm⟩ | h7
    · exact Or.inl ⟨p, f, hp2, RestrictedStd.statedClassicalModel_of_lieModel_PSL hm⟩
    · exact Or.inr (Or.inl h7)
  obtain ⟨-, hβ⟩ := SymmetricLocal.faithful_alternating_socle_small_standard_source_selector_stated
    hs hnab hC hα hJN hJc
    (UnbalancedCorr.assembly_isStandardSubgroup_of_isStandardSubgroup hstd) hsrc (by omega) φ
  obtain ⟨β, hβinj, -, -, -, hJalt, hxor, -, hp, h7, -⟩ := hβ (by omega)
  have hkn : (Nat.card {x // β α x = x} = 5 ∨ Nat.card {x // β α x = x} = 6 ∨
      Nat.card {x // β α x = x} = 7) ∧ (β.range = ⊤ → n = Nat.card {x // β α x = x} + 2) ∧
      (β.range = alternatingGroup (Fin n) → n = Nat.card {x // β α x = x} + 4) := by
    rcases hsmall with ⟨p, f, -, hp2, -, -, hm⟩ | h7'
    · rcases hp p f hp2 (RestrictedStd.statedClassicalModel_of_lieModel_PSL hm) with
        ⟨hc, -, -, ha, hb⟩ | ⟨hc, -, -, ha, hb⟩
      · exact ⟨Or.inl hc, fun h => by have := ha h; omega, fun h => by have := hb h; omega⟩
      · exact ⟨Or.inr (Or.inl hc), fun h => by have := ha h; omega,
          fun h => by have := hb h; omega⟩
    · obtain ⟨hc, ha, hb⟩ := h7 h7'
      exact ⟨Or.inr (Or.inr hc), fun h => by have := ha h; omega,
        fun h => by have := hb h; omega⟩
  obtain ⟨hk, hn2, hn4⟩ := hkn
  let eFix : {x // β α x = x} ≃ Fin (Nat.card {x // β α x = x}) :=
    Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card).symm
  let eJ : ↥J ≃* alternatingGroup (Fin (Nat.card {x // β α x = x})) :=
    ((J.equivMapOfInjective β hβinj).trans (MulEquiv.subgroupCongr hJalt)).trans
      (((alternatingGroup _).equivMapOfInjective _ Perm.ofSubtype_injective).symm.trans
        (Equiv.altCongrHom eFix))
  refine cf23Exception_alt φ eJ hk ?_
  rcases xor_def.mp hxor with ⟨⟨htop, -⟩, -⟩ | ⟨⟨halt, -⟩, -⟩
  · exact Or.inl (hn2 htop)
  · exact Or.inr (hn4 halt)

end CFSG.ComponentClassification.GSThmB.CF23I
