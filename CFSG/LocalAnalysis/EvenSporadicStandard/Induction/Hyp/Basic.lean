module

public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FStar
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobBalance

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.EvenSporadicStandard.Solomon78

theorem eq_one_of_perfect_of_comm {G A : Type*} [Group G] [Group A] (hG : Group.IsPerfect G)
    (f : G →* A) (hA : ∀ a b : A, a * b = b * a) (g : G) : f g = 1 := by
  have hperf : Group.IsPerfect ↥f.range :=
    Group.IsPerfect.ofSurjective (f := f.rangeRestrict) f.rangeRestrict_surjective
  have h1 : _root_.commutator ↥f.range = ⊥ := by
    rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a _
    exact mem_centralizer_iff.2 fun b _ => Subtype.ext (hA b a)
  have h2 : _root_.commutator ↥f.range = ⊤ := hperf.commutator_eq_top
  have hx : (⟨f g, g, rfl⟩ : ↥f.range) ∈ (⊤ : Subgroup ↥f.range) := Subgroup.mem_top _
  rw [← h2, h1, Subgroup.mem_bot] at hx
  exact congrArg Subtype.val hx

theorem isMulCommutative_of_card_le_four' {A : Type*} [Group A] [Finite A]
    (h : Nat.card A ≤ 4) : IsMulCommutative A := by
  have hpos : 0 < Nat.card A := Nat.card_pos
  obtain h1 | h2 | h3 | h4 : Nat.card A = 1 ∨ Nat.card A = 2 ∨ Nat.card A = 3 ∨ Nat.card A = 4 :=
    by omega
  · have : Subsingleton A := (Nat.card_eq_one_iff_unique.1 h1).1
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := isCyclic_of_prime_card h2
    infer_instance
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have := isCyclic_of_prime_card h3
    infer_instance
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [h4]; norm_num)

theorem le_of_perfect_of_index_le_two {H : Type} [Group H] [Finite H] {N A : Subgroup H}
    [N.Normal] (hidx : N.index ≤ 2) (hA : Group.IsPerfect ↥A) : A ≤ N := by
  have hcomm : IsMulCommutative (H ⧸ N) :=
    isMulCommutative_of_card_le_four' (by
      have : Nat.card (H ⧸ N) = N.index := rfl
      omega)
  intro a ha
  have := eq_one_of_perfect_of_comm hA ((QuotientGroup.mk' N).comp A.subtype)
    (fun x y => hcomm.is_comm.comm x y) ⟨a, ha⟩
  exact (QuotientGroup.eq_one_iff a).1 this

theorem three_mul_card_le_of_proper {H : Type} [Group H] [Finite H] {N A : Subgroup H}
    (hN : IsSimpleGroup ↥N) (hAN : A ≤ N) (hne : A ≠ N) (hbot : A ≠ ⊥) :
    3 * Nat.card ↥A ≤ Nat.card ↥N := by
  have hAN' : (A.subgroupOf N) ≠ ⊤ := fun h => hne (le_antisymm hAN (subgroupOf_eq_top.1 h))
  have hAb : (A.subgroupOf N) ≠ ⊥ := by
    intro h
    have hdis := Subgroup.subgroupOf_eq_bot.1 h
    rw [disjoint_iff, inf_eq_left.2 hAN] at hdis
    exact hbot hdis
  have hidx : (A.subgroupOf N).index ≠ 1 := fun h => hAN' (Subgroup.index_eq_one.1 h)
  have hidx2 : (A.subgroupOf N).index ≠ 2 := by
    intro h2
    have : (A.subgroupOf N).Normal := Subgroup.normal_of_index_eq_two h2
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (A.subgroupOf N) with h | h
    · exact hAb h
    · exact hAN' h
  have hpos : 0 < (A.subgroupOf N).index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have h3 : 3 ≤ (A.subgroupOf N).index := by omega
  have hcard : (A.subgroupOf N).index * Nat.card ↥(A.subgroupOf N) = Nat.card ↥N :=
    Subgroup.index_mul_card _
  have hA : Nat.card ↥(A.subgroupOf N) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
  rw [hA] at hcard
  calc 3 * Nat.card ↥A ≤ (A.subgroupOf N).index * Nat.card ↥A := Nat.mul_le_mul_right _ h3
    _ = Nat.card ↥N := hcard

theorem isQuasisimple_of_simple_nonabelian {N : Type*} [Group N] (hs : IsSimpleGroup N)
    (hna : ∃ a b : N, a * b ≠ b * a) : CFSG.IsQuasisimple N := by
  have hc : center N = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center N) with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      exact hab (mem_center_iff.1 (h1 ▸ mem_top b) a)
  have hperf : Group.IsPerfect N := by
    rw [Group.isPerfect_def, _root_.commutator_def]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ⁅(⊤ : Subgroup N), (⊤ : Subgroup N)⁆ with
        h1 | h1
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1
      exact hab (mem_centralizer_iff.1 (hcen (mem_top a)) b (mem_top b)).symm
    · exact h1
  let e : (N ⧸ center N) ≃* N :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  refine ⟨hperf, MulEquiv.isSimpleGroup e, ?_⟩
  obtain ⟨a, b, hab⟩ := hna
  refine ⟨QuotientGroup.mk a, QuotientGroup.mk b, fun h => hab ?_⟩
  have h1 := congrArg e h
  have he : ∀ x : N, e (QuotientGroup.mk x) = x := fun x => rfl
  rwa [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, he, he] at h1

theorem fStarSimple_of_normal_simple {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y} [N.Normal]
    (hs : IsSimpleGroup ↥N) (hna : ∃ a b : ↥N, a * b ≠ b * a)
    (hC : centralizer (N : Set Y) ≤ N) : FStarSimple N := by
  have hq : CFSG.IsQuasisimple ↥N := isQuasisimple_of_simple_nonabelian hs hna
  have hcomp : CFSG.IsComponent N := ⟨hq, Subgroup.Normal.isSubnormal ‹_›⟩
  have hF : CFSG.fittingSubgroup Y ≤ N := by
    set F := CFSG.fittingSubgroup Y with hFdef
    have : F.Normal := CFSG.fittingSubgroup_normal
    have : Group.IsNilpotent ↥F := CFSG.fittingSubgroup_nilpotent
    have hFN : F ⊓ N = ⊥ := by
      have : (F.subgroupOf N).Normal := Subgroup.Normal.subgroupOf ‹F.Normal› N
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (F.subgroupOf N) with h | h
      · exact disjoint_iff.1 (Subgroup.subgroupOf_eq_bot.1 h)
      · exfalso
        have hNF : N ≤ F := fun x hx => by
          have hx' : (⟨x, hx⟩ : ↥N) ∈ F.subgroupOf N := h ▸ Subgroup.mem_top _
          exact hx'
        have hsolv : Group.IsSolvable ↥N :=
          Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hNF)
        obtain ⟨a, b, hab⟩ := hna
        exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hsolv) a b)
    have hcomm : ⁅F, N⁆ = ⊥ := le_bot_iff.1 (hFN ▸ Subgroup.commutator_le_inf F N)
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm).trans hC
  have hL : CFSG.layer Y ≤ N := by
    refine sSup_le fun K hK => ?_
    rcases CFSG.LocalCores.distinct_components_commute hK hcomp with h | h
    · exact h.le
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h).trans hC
  exact ⟨le_antisymm (sup_le hF hL) (le_trans (le_sSup hcomp) le_sup_right), hs, hna⟩

theorem catalog_of_kProper_of_surjective {H : Type} [Group H]
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) (K : Subgroup H) (hKtop : K ≠ ⊤)
    (S : Type) [Group S] [IsSimpleGroup S] (hnonab : ∃ a b : S, a * b ≠ b * a) (φ : K →* S)
    (hφ : Function.Surjective φ) : CFSG.Blueprint.Catalog S :=
  CFSG.KCore.KProperNonab.catalogue_of_surjective CFSG.SectionRank.catalog_isoInvariant hK K hKtop
    hnonab φ hφ

theorem kProper_of_section {H Γ : Type} [Group H] [Group Γ]
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) (A : Subgroup H) (ψ : ↥A →* Γ)
    (hψ : Function.Surjective ψ) : CFSG.Assembly.KProper CFSG.Blueprint.Catalog Γ :=
  (CFSG.KCore.KProperNonab.subgroup CFSG.SectionRank.catalog_isoInvariant hK A).of_surjective
    CFSG.SectionRank.catalog_isoInvariant ψ hψ

end CFSG.EvenSporadicStandard.Induction.Hyp
