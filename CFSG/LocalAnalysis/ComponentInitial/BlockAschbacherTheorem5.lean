module

public import CFSG.LocalAnalysis.ComponentInitial.BlockOddCoreSection
public import CFSG.LocalAnalysis.ComponentInitial.BlockFactorContainmentAll
public import CFSG.LocalAnalysis.ComponentInitial.StandardCriterion
public import CFSG.Milestones.CL_LIT_Aschbacher_component_type_theorem_5

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup
open CFSG.Open (aschbacherThm5OddCore aschbacherThm5Core aschbacherThm5Preimage
  aschbacherThm5Centralizes aschbacherThm5IsSemisimple)

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {J : Subgroup G}

omit [IsSimpleGroup G] in
theorem even_card_of_two_le_pRank (hrank : 2 ≤ CFSG.Assembly.pRank 2 J) :
    Even (Nat.card J) := by
  obtain ⟨E, hEJ, -, hcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two J
  have hrank' : 2 ≤ CFSG.Open.pRank 2 J := hrank
  have h2 : 2 ∣ Nat.card E := by
    rw [hcard]
    exact dvd_pow_self 2 (by omega)
  exact even_iff_two_dvd.2 (h2.trans (Subgroup.card_dvd_of_le hEJ))

theorem universal_rank_two_component_no_commuting_conjugate
    (hnab : ∃ a b : G, a * b ≠ b * a) (hq : CFSG.Assembly.IsQuasisimple J)
    (hrank : 2 ≤ CFSG.Assembly.pRank 2 J)
    (hCeven : Even (Nat.card (centralizer (J : Set G)))) (hJ : IsUniversalComponent J) :
    (block J).Subsingleton := by
  by_contra hns
  have hΔ : (block J).Nontrivial := Set.not_subsingleton_iff.1 hns
  have heven : Even (Nat.card J) := even_card_of_two_le_pRank hrank
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  set D := blockGroup J with hD
  set r := Nat.card (block J) with hr
  have hr2 : 2 ≤ r := by
    have := (Set.one_lt_ncard_iff_nontrivial (s := block J)).2 hΔ
    rw [← Nat.card_coe_set_eq] at this
    omega
  let e : Fin r ≃ block J := (Finite.equivFin (block J)).symm
  let Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D) :=
    fun i => blockSection J (e i : Subgroup G)
  have hsemisimple : ∀ i, aschbacherThm5IsSemisimple (Abar i) := fun i =>
    ⟨1, fun _ => Abar i, Nat.one_pos,
      fun _ => ⟨le_rfl, isQuasisimple_blockSection hq hJ heven (e i).2⟩,
      fun l m hlm => absurd (Subsingleton.elim l m) hlm, iSup_const⟩
  have hdistinct : Function.Injective Abar :=
    (blockSection_injective hq hJ heven).comp e.injective
  have hcomm : ∀ i j, i ≠ j → ∀ x ∈ Abar i, ∀ y ∈ Abar j, x * y = y * x :=
    fun i j hij _ hx _ hy => commute_of_mem_blockSection hJ heven (e i).2 (e j).2
      (fun h => hij (e.injective (Subtype.ext h))) hx hy
  have hgen : ⨆ i, Abar i = ⊤ := by
    rw [← iSup_blockSection (J := J)]
    exact e.iSup_comp (g := fun K : block J => blockSection J (K : Subgroup G))
  have hperm : ∀ h ∈ normalizer (D : Set G), ∀ i, ∃ j,
      (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj h).toMonoidHom =
        aschbacherThm5Preimage D (Abar j) := by
    intro h hh i
    obtain ⟨hmem, hmap⟩ := map_conj_preimage_blockSection hq hJ heven hh (e i).2
    refine ⟨e.symm ⟨conjSub h (e i), hmem⟩, ?_⟩
    change _ = aschbacherThm5Preimage D (blockSection J (e (e.symm ⟨_, hmem⟩) : Subgroup G))
    rw [Equiv.apply_symm_apply]
    exact hmap
  have hcoreK : ∀ K ∈ block J, ⁅aschbacherThm5Core D, K⁆ = ⊥ := fun K hK => by
    rw [commutator_comm]
    exact commutator_eq_bot_core_of_mem_block hq hJ heven hK
  have hcoreC := commutator_core_blockGroup_eq_bot hq hJ heven
  have hcentK : ∀ (K : block J) (y : G),
      aschbacherThm5Centralizes (aschbacherThm5Core D)
        (aschbacherThm5Preimage D (blockSection J (K : Subgroup G))) y →
      y ∈ centralizer ((K : Subgroup G) : Set G) := by
    intro K y hy
    have : Group.IsPerfect (K : Subgroup G) := ⟨(isQuasisimple_of_isConjOf hq K.2.1).1⟩
    exact mem_centralizer_of_centralizes_modulo (hcoreK K K.2) hcoreC
      (fun a ha => hy a (le_preimage_blockSection (le_blockGroup K.2) ha))
  have hi : ∀ (i j : Fin r) (t g : G), (∃ k : ℕ, t ^ (2 ^ k) = 1) → t ∉ center G →
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar i)) t →
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar j))
        (g⁻¹ * t * g) →
      g ∈ normalizer (D : Set G) := by
    intro i j t g ht htc hti htj
    have ht1 : t ≠ 1 := fun h => htc (h ▸ one_mem _)
    exact mem_normalizer_blockGroup_of_two_element hJ heven (e i).2 (e j).2 ht ht1
      (hcentK (e i) t hti) (hcentK (e j) _ htj)
  have hii : ∀ (i : Fin r) (g : G) (X : Subgroup G),
      X ≤ (normalizer (D : Set G)).map (MulAut.conj g⁻¹).toMonoidHom →
      (∀ a ∈ aschbacherThm5Preimage D (Abar i), ∃ x ∈ X, ∃ o ∈ aschbacherThm5Core D,
        a = x * o) →
      g ∈ normalizer (D : Set G) := by
    intro i g X hX hcover
    have hKX : (e i : Subgroup G) ≤ X :=
      le_of_forall_eq_mul_mem
        (commutator_self_eq_of_assemblyQuasisimple (isQuasisimple_of_isConjOf hq (e i).2.1))
        (hcoreK _ (e i).2) hcoreC
        (fun a ha => hcover a (le_preimage_blockSection (le_blockGroup (e i).2) ha))
    have hconj : conjSub g (e i : Subgroup G) ≤ normalizer (D : Set G) :=
      calc conjSub g (e i : Subgroup G) ≤ conjSub g X := Subgroup.map_mono hKX
        _ ≤ conjSub g (conjSub g⁻¹ (normalizer (D : Set G))) := Subgroup.map_mono hX
        _ = normalizer (D : Set G) := conjSub_conjSub_inv g _
    exact commuting_block_factor_containment_transporter_all hq heven hJ hΔ (e i).2 hconj
  have hH : normalizer (D : Set G) ≠ ⊤ :=
    (normalizer_blockGroup_lt_top hq hJ heven inferInstance hnab hCeven).1.ne
  rcases CFSG.Milestones.cl_lit_aschbacher_component_type_theorem_5 G D r (by omega) Abar
      hdistinct hsemisimple hcomm hgen hperm hi hii hH with h1 | ⟨-, hrest⟩
  · omega
  · set i0 : Fin r := ⟨0, by omega⟩ with hi0
    have hrank1 := (hrest i0 ⟨1, by omega⟩ (by simp [hi0, Fin.ext_iff])).2.1
    have hle : CFSG.Open.pRank 2 J ≤ CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar i0)) :=
      pRank_le_pRank_preimage_blockSection (e i0).2
    have hrank' : 2 ≤ CFSG.Open.pRank 2 J := hrank
    omega

theorem universal_rank_two_component_eq_of_commutator_eq_bot
    (hnab : ∃ a b : G, a * b ≠ b * a) (hq : CFSG.Assembly.IsQuasisimple J)
    (hrank : 2 ≤ CFSG.Assembly.pRank 2 J)
    (hCeven : Even (Nat.card (centralizer (J : Set G)))) (hJ : IsUniversalComponent J) (g : G)
    (hg : ⁅J, conjSub g J⁆ = ⊥) : conjSub g J = J :=
  universal_rank_two_component_no_commuting_conjugate hnab hq hrank hCeven hJ
    (⟨⟨g, rfl⟩, Or.inr hg⟩ : conjSub g J ∈ block J) mem_block_self

theorem universal_rank_two_component_commutator_ne_bot
    (hnab : ∃ a b : G, a * b ≠ b * a) (hq : CFSG.Assembly.IsQuasisimple J)
    (hrank : 2 ≤ CFSG.Assembly.pRank 2 J)
    (hCeven : Even (Nat.card (centralizer (J : Set G)))) (hJ : IsUniversalComponent J) (g : G) :
    ⁅J, J.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
  intro hg
  have hJg := universal_rank_two_component_eq_of_commutator_eq_bot hnab hq hrank hCeven hJ g hg
  rw [show J.map (MulAut.conj g).toMonoidHom = J from hJg] at hg
  exact not_le_centralizer_self_of_isQuasisimple hq (commutator_eq_bot_iff_le_centralizer.1 hg)

theorem universal_rank_two_component_isStandardSubgroup
    (hnab : ∃ a b : G, a * b ≠ b * a) (hq : CFSG.Assembly.IsQuasisimple J)
    (hrank : 2 ≤ CFSG.Assembly.pRank 2 J)
    (hCeven : Even (Nat.card (centralizer (J : Set G)))) (hJ : IsUniversalComponent J) :
    CFSG.Assembly.ComponentType.IsStandardSubgroup J :=
  (involution_component_standard_criterion hq hCeven
    (universal_rank_two_component_commutator_ne_bot hnab hq hrank hCeven hJ)).2 hJ

end CFSG.LocalAnalysis.ComponentInitial
