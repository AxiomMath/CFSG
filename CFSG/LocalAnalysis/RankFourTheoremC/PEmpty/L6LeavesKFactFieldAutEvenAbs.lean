module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBasic
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Open Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge.Over
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem isSylowTwoOf_of_isSylowOf {J : Type*} [Group J] [Finite J] {T : Subgroup J}
    (h : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) : IsSylowTwoOf T ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hle, hP, hidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp h
  exact ⟨hle, hP, hidx⟩

theorem padicValNat_le_of_dvd' {r a b : ℕ} (hr : r.Prime) (hb : b ≠ 0) (h : a ∣ b) :
    padicValNat r a ≤ padicValNat r b := by
  haveI : Fact r.Prime := ⟨hr⟩
  have ha : a ≠ 0 := fun h0 => hb (Nat.eq_zero_of_zero_dvd (h0 ▸ h))
  exact (padicValNat_dvd_iff_le hb).mp ((pow_padicValNat_dvd (n := a)).trans h)

theorem pCoreOf_ne_bot_of_charTwo {J : Type*} [Group J] {Y T : Subgroup J} (hchar : CharTwo Y)
    (hTY : T ≤ Y) (hT1 : T ≠ ⊥) : pCoreOf 2 Y ≠ ⊥ := by
  intro h0
  apply hT1
  rw [eq_bot_iff]
  intro x hx
  have hxY : x ∈ Y := hTY hx
  have hxC : x ∈ Subgroup.centralizer (pCoreOf 2 Y : Set J) := by
    rw [h0]
    intro y hy
    have : y = 1 := by simpa using hy
    simp [this]
  have := hchar ⟨hxY, hxC⟩
  rw [h0] at this
  simpa using this

theorem closure_eq_top_of_overgroupPrime {J : Type} [Group J] [Finite J] (α : MulAut J)
    (T : Subgroup J) {r : ℕ} (hr : r.Prime)
    (hloc : ∀ Y : Subgroup J, T ≤ Y → Y ≠ ⊤ →
      padicValNat r (Nat.card Y) < padicValNat r (Nat.card (fixedSubgroup α))) :
    Subgroup.closure ({g : J | α g = g} ∪ (T : Set J)) = ⊤ := by
  by_contra hne
  have hTY : T ≤ Subgroup.closure ({g : J | α g = g} ∪ (T : Set J)) :=
    fun x hx => Subgroup.subset_closure (Or.inr hx)
  have hCY : fixedSubgroup α ≤ Subgroup.closure ({g : J | α g = g} ∪ (T : Set J)) :=
    fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hle := padicValNat_le_of_dvd' hr Nat.card_pos.ne' (Subgroup.card_dvd_of_le hCY)
  have hlt := hloc _ hTY hne
  omega

theorem exists_sylow_fixed_of_factorization_le {J : Type} [Group J] [Finite J] (α : MulAut J)
    (h : (Nat.card J).factorization 2 ≤ (Nat.card (fixedSubgroup α)).factorization 2) :
    ∃ U : Subgroup J, CFSG.ABGLocalTools.IsSylowOf 2 U ⊤ ∧ ∀ g ∈ U, α g = g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 (fixedSubgroup α)))
  set U : Subgroup J := (S : Subgroup (fixedSubgroup α)).map (fixedSubgroup α).subtype with hU
  have hUC : U ≤ fixedSubgroup α := Subgroup.map_subtype_le _
  have hcard : Nat.card U = 2 ^ (Nat.card (fixedSubgroup α)).factorization 2 := by
    rw [hU, Subgroup.card_map_of_injective (fixedSubgroup α).subtype_injective,
      Sylow.card_eq_multiplicity]
  have hdvd : Nat.card U ∣ Nat.card J := Subgroup.card_subgroup_dvd_card U
  have hle : (Nat.card (fixedSubgroup α)).factorization 2 ≤ (Nat.card J).factorization 2 := by
    have h1 : 2 ^ (Nat.card (fixedSubgroup α)).factorization 2 ∣ Nat.card J := hcard ▸ hdvd
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h1
  have heq : (Nat.card (fixedSubgroup α)).factorization 2 = (Nat.card J).factorization 2 :=
    le_antisymm hle h
  refine ⟨U, ?_, fun g hg => hUC hg⟩
  refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
  rw [hcard, heq, Subgroup.card_top]

theorem ne_bot_of_isSylowOf_of_even {J : Type*} [Group J] [Finite J] {T : Subgroup J}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hev : Even (Nat.card J)) : T ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h0
  obtain ⟨-, -, hidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hT
  apply hidx
  rw [Subgroup.relIndex_top_right, h0, Subgroup.index_bot]
  exact even_iff_two_dvd.mp hev

theorem dvd_card_of_mem_inner {J : Type*} [Group J] [Finite J] {α : MulAut J} {p : ℕ}
    (h : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner J) (hα : orderOf α = p) :
    p ∣ Nat.card J := by
  obtain ⟨g, rfl⟩ := h
  have : orderOf (MulAut.conj g) ∣ orderOf g := orderOf_map_dvd _ _
  exact hα ▸ this.trans (orderOf_dvd_natCard g)

theorem mem_inner_of_not_dvd_card_outer {J : Type*} [Group J] [Finite J] {p : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer J))
    {α : MulAut J} (hα : α ^ p = 1) :
    α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner J := by
  have hβ : (QuotientGroup.mk α : CFSG.ComponentClassification.OuterAutomorphisms.Outer J) ^ p =
      1 := by
    rw [← QuotientGroup.mk_pow, hα]
    rfl
  rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hβ) with h1 | h1
  · exact (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 h1)
  · exact absurd (h1 ▸ orderOf_dvd_natCard
      (QuotientGroup.mk α : CFSG.ComponentClassification.OuterAutomorphisms.Outer J)) h

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
