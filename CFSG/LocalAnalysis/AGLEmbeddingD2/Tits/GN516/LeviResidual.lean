module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviQuasi
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParOneNode

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open scoped commutatorElement

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

@[expose] def MinLevi (Y : Type) [Group Y] : Prop :=
  IsSimpleGroup Y → ∀ T Q : Subgroup Y, IsSylowTwoOf T ⊤ → IsMinOverBorel ⊤ T Q → Q ≠ ⊤ →
    LeviAlt ↥(pElementSubgroup 2 Q)

theorem isQuasisimple_of_simple {Y : Type} [Group Y] (hs : IsSimpleGroup Y)
    (hna : ∃ a b : Y, a * b ≠ b * a) : Open.IsQuasisimple Y := by
  obtain ⟨a, b, hab⟩ := hna
  have hcom : commutator Y = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Y) with h | h
    · exfalso
      apply hab
      have : ⁅a, b⁆ ∈ commutator Y := by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    · exact h
  have hZ : Subgroup.center Y = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
    · exact h
    · exfalso
      apply hab
      exact Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b |>.symm
  refine ⟨hcom, ?_⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup

theorem leviAlt_of_simple {Y : Type} [Group Y] [Finite Y] (hs : IsSimpleGroup Y)
    (hna : ∃ a b : Y, a * b ≠ b * a) : LeviAlt Y := by
  right
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : Open.IsQuasisimple (Y ⧸ (⊥ : Subgroup Y)) :=
    isQuasisimple_of_mulEquiv_open QuotientGroup.quotientBot.symm (isQuasisimple_of_simple hs hna)
  exact isQuasisimple_quot_pCore_of_normal_two (⊥ : Subgroup Y) IsPGroup.of_bot hq

theorem leviAlt_pElement_top {Y : Type} [Group Y] [Finite Y] (hs : IsSimpleGroup Y)
    (hna : ∃ a b : Y, a * b ≠ b * a) (hne : pElementSubgroup 2 (⊤ : Subgroup Y) ≠ ⊥) :
    LeviAlt ↥(pElementSubgroup 2 (⊤ : Subgroup Y)) := by
  have := normal_pElementSubgroup_top Y
  have htop : pElementSubgroup 2 (⊤ : Subgroup Y) = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_left hne
  exact leviAlt_of_mulEquiv ((Subgroup.topEquiv.symm).trans (MulEquiv.subgroupCongr htop.symm))
    (leviAlt_of_simple hs hna)

theorem leviAlt_pElement_of_solvable {Y : Type} [Group Y] {Q : Subgroup Y}
    (h : Group.IsSolvable ↥Q) : LeviAlt ↥(pElementSubgroup 2 Q) :=
  Or.inl (Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion (pElementSubgroup_le Q)) (Subgroup.inclusion_injective _))

theorem isSolvable_of_natCard_eq {G : Type*} [Group G] [Finite G] {p q a b : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card G = p ^ a * q ^ b) : Group.IsSolvable G := by
  have := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rwa [← Nat.card_eq_fintype_card])

theorem leviAlt_of_minLevi {W : Type} [Group W] [Finite W] {L S₀ A : Subgroup W}
    (hL : Open.IsQuasisimple ↥L) (hS : IsSylowTwoOf S₀ L) (hA : IsMinOverBorel L S₀ A)
    (h : MinLevi (↥L ⧸ Subgroup.center ↥L)) : LeviAlt ↥(pElementSubgroup 2 A) := by
  refine leviAlt_of_isMinOverBorel_of_quotient hS hA ?_
  have hS' := isSylowTwoOf_top_map_center hS
  have hA' := isMinOverBorel_map_of_isMinOverBorel hS hA
  by_cases htop : (A.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) = ⊤
  · have hs : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.2
    have hna : ∃ a b : ↥L ⧸ Subgroup.center ↥L, a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      have h1 : commutator (↥L ⧸ Subgroup.center ↥L) = ⊥ := by
        rw [eq_bot_iff, commutator_def]
        refine Subgroup.commutator_le.2 fun x _ y _ => ?_
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact hcon x y
      have hp : Group.IsPerfect ↥L := Group.isPerfect_def.2 hL.1
      have h2 : commutator (↥L ⧸ Subgroup.center ↥L) = ⊤ :=
        Group.isPerfect_def.1 (Group.IsPerfect.ofSurjective
          (QuotientGroup.mk'_surjective (Subgroup.center ↥L)))
      obtain ⟨x, hx⟩ := exists_ne (1 : ↥L ⧸ Subgroup.center ↥L)
      have : x ∈ commutator (↥L ⧸ Subgroup.center ↥L) := h2 ▸ Subgroup.mem_top x
      rw [h1, Subgroup.mem_bot] at this
      exact hx this
    have hne : pElementSubgroup 2 (⊤ : Subgroup (↥L ⧸ Subgroup.center ↥L)) ≠ ⊥ := by
      intro hbot
      have hle : ((S₀.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) ≤
          pElementSubgroup 2 (⊤ : Subgroup (↥L ⧸ Subgroup.center ↥L)) :=
        le_pElementSubgroup_of_isPGroup le_top hS'.2.1
      rw [hbot, le_bot_iff] at hle
      have hlt := hA'.2.1
      rw [htop, top_inf_eq, hle] at hlt
      exact absurd (Subgroup.normalizer_eq_top_iff.2 inferInstance) hlt.ne
    rw [htop]
    exact leviAlt_pElement_top hs hna hne
  · exact h hL.2 _ _ hS' hA' htop

end CFSG.AGLEmbeddingD2.Tits.GN516
