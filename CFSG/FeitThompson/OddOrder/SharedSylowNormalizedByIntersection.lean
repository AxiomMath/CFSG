module

public import Mathlib.GroupTheory.Nilpotent
import CFSG.FeitThompson.Foundations.NilpotentSylowNormalCharacteristic
import CFSG.FeitThompson.Local.MaximalIntersectionSylowNormalizerControl
import CFSG.FeitThompson.Local.SylowInterNormalSylowOrder

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem natCard_eq_pow_factorization_iff_exists_sylow {M P : Subgroup G} (hPM : P ≤ M) :
    Nat.card P = p ^ (Nat.card M).factorization p ↔
      ∃ S : Sylow p M, (S : Subgroup M).map M.subtype = P :=
  ⟨fun hP => exists_sylow_map_subtype_eq Fact.out hPM hP,
    fun ⟨_, hS⟩ => hS ▸ natCard_map_subtype_sylow M _⟩

theorem eq_of_le_nilpotent_of_natCard_eq_pow_factorization {H : Subgroup G}
    (hHnil : Group.IsNilpotent H) {Q₁ Q₂ : Subgroup G} (h₁ : Q₁ ≤ H)
    (hQ₁ : Nat.card Q₁ = p ^ (Nat.card H).factorization p) (h₂ : Q₂ ≤ H)
    (hQ₂ : Nat.card Q₂ = p ^ (Nat.card H).factorization p) : Q₁ = Q₂ := by
  have := hHnil
  have hc₁ : Nat.card (Q₁.subgroupOf H) = p ^ (Nat.card H).factorization p := by
    rw [Nat.card_congr (subgroupOfEquivOfLe h₁).toEquiv, hQ₁]
  have hc₂ : Nat.card (Q₂.subgroupOf H) = p ^ (Nat.card H).factorization p := by
    rw [Nat.card_congr (subgroupOfEquivOfLe h₂).toEquiv, hQ₂]
  have : (Q₁.subgroupOf H).Normal := normal_of_natCard_eq_pow_factorization hc₁
  obtain ⟨g, hg⟩ := exists_conj_smul_eq hc₁ hc₂
  rw [Subgroup.Normal.conj_smul_eq_self g _] at hg
  have h := subgroupOf_inj.mp hg
  rwa [inf_eq_left.mpr h₁, inf_eq_left.mpr h₂] at h

theorem existsUnique_le_natCard_eq_pow_factorization {H : Subgroup G}
    (hHnil : Group.IsNilpotent H) :
    ∃! Q : Subgroup G, Q ≤ H ∧ Nat.card Q = p ^ (Nat.card H).factorization p := by
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow p H))
  exact ⟨_, ⟨map_subtype_le _, natCard_map_subtype_sylow H T⟩, fun R ⟨hRH, hR⟩ =>
    eq_of_le_nilpotent_of_natCard_eq_pow_factorization hHnil hRH hR
      (map_subtype_le _) (natCard_map_subtype_sylow H T)⟩

theorem le_of_isPGroup_le_nilpotent {H Q P : Subgroup G} (hHnil : Group.IsNilpotent H)
    (hQH : Q ≤ H) (hQ : Nat.card Q = p ^ (Nat.card H).factorization p) (hPH : P ≤ H)
    (hP : IsPGroup p P) : P ≤ Q := by
  have := hHnil
  have hc : Nat.card (Q.subgroupOf H) = p ^ (Nat.card H).factorization p := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hQH).toEquiv, hQ]
  have : (Q.subgroupOf H).Normal := normal_of_natCard_eq_pow_factorization hc
  obtain ⟨g, hg⟩ := exists_le_conj_smul_of_isPGroup hc
    (hP.of_equiv (subgroupOfEquivOfLe hPH).symm)
  rw [Subgroup.Normal.conj_smul_eq_self g _] at hg
  intro x hx
  have hxP : (⟨x, hPH hx⟩ : H) ∈ P.subgroupOf H := hx
  exact hg hxP

theorem map_conj_eq_self_of_mem_normalizer {H Q : Subgroup G} (hHnil : Group.IsNilpotent H)
    (hQH : Q ≤ H) (hQ : Nat.card Q = p ^ (Nat.card H).factorization p)
    {g : G} (hg : g ∈ normalizer (H : Set G)) :
    Q.map (MulAut.conj g : G →* G) = Q := by
  have hmapH : H.map (MulAut.conj g : G →* G) = H := mem_normalizer_iff_map_conj_eq.mp hg
  have hle : Q.map (MulAut.conj g : G →* G) ≤ H := by
    rw [← hmapH]; exact Subgroup.map_mono hQH
  have hcard : Nat.card (Q.map (MulAut.conj g : G →* G)) = p ^ (Nat.card H).factorization p := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hQ]
  exact eq_of_le_nilpotent_of_natCard_eq_pow_factorization hHnil hle hcard hQH hQ

variable {M L H P Q : Subgroup G}

theorem inf_eq_of_le_nilpotent (hHnil : Group.IsNilpotent H)
    (hPM : P ≤ M) (hP : Nat.card P = p ^ (Nat.card M).factorization p) (hPH : P ≤ H)
    (hQH : Q ≤ H) (hQ : Nat.card Q = p ^ (Nat.card H).factorization p) : Q ⊓ M = P := by
  have hPQ : P ≤ Q := le_of_isPGroup_le_nilpotent hHnil hQH hQ hPH (IsPGroup.of_card hP)
  refine (Subgroup.eq_of_le_of_card_ge (le_inf hPQ hPM) ?_).symm
  rw [hP]
  exact natCard_le_pow_factorization_of_isPGroup Fact.out inf_le_right
    ((IsPGroup.of_card hQ).to_inf_left)

theorem inf_le_normalizer_of_le_nilpotent (hHnil : Group.IsNilpotent H) (hHL : H ≤ L)
    (hHnorm : (H.subgroupOf L).Normal)
    (hPM : P ≤ M) (hP : Nat.card P = p ^ (Nat.card M).factorization p) (hPH : P ≤ H)
    (hQH : Q ≤ H) (hQ : Nat.card Q = p ^ (Nat.card H).factorization p) :
    M ⊓ L ≤ normalizer (P : Set G) := by
  have := hHnorm
  have hQM : Q ⊓ M = P := inf_eq_of_le_nilpotent hHnil hPM hP hPH hQH hQ
  intro d hd
  obtain ⟨hdM, hdL⟩ := mem_inf.mp hd
  rw [mem_normalizer_iff_map_conj_eq, ← hQM,
    Subgroup.map_inf _ _ _ (MulAut.conj d).injective,
    map_conj_eq_self_of_mem_normalizer hHnil hQH hQ
      (Subgroup.le_normalizer_of_normal_subgroupOf hHL hdL),
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hdM)]

theorem sylow_inf_eq_and_inf_le_normalizer (hHnil : Group.IsNilpotent H) (hHL : H ≤ L)
    (hHnorm : (H.subgroupOf L).Normal) (S : Sylow p M) (T : Sylow p H)
    (hSH : (S : Subgroup M).map M.subtype ≤ H) :
    (T : Subgroup H).map H.subtype ⊓ M = (S : Subgroup M).map M.subtype ∧
      M ⊓ L ≤ normalizer (((S : Subgroup M).map M.subtype : Subgroup G) : Set G) := by
  have hPM : (S : Subgroup M).map M.subtype ≤ M := map_subtype_le _
  have hP := (natCard_eq_pow_factorization_iff_exists_sylow hPM).mpr ⟨S, rfl⟩
  have hQH : (T : Subgroup H).map H.subtype ≤ H := map_subtype_le _
  have hQ := (natCard_eq_pow_factorization_iff_exists_sylow hQH).mpr ⟨T, rfl⟩
  exact ⟨inf_eq_of_le_nilpotent hHnil hPM hP hSH hQH hQ,
    inf_le_normalizer_of_le_nilpotent hHnil hHL hHnorm hPM hP hSH hQH hQ⟩

end

end CFSG.FeitThompson
