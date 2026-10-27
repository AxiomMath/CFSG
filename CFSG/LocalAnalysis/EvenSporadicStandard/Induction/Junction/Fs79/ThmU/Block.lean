module

public import CFSG.LocalAnalysis.ComponentInitial.BlockAschbacherTheorem5
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FStar

public section

namespace CFSG.EvenSporadicStandard.Induction.ThmU

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.EvenSporadicStandard.Induction
open CFSG.Open (aschbacherThm5OddCore aschbacherThm5Core aschbacherThm5Preimage
  aschbacherThm5Centralizes aschbacherThm5IsSemisimple)

variable {H : Type} [Group H] [Finite H] {J : Subgroup H}

theorem normalizer_blockGroup_ne_top_of_fStarSimple {N : Subgroup H} (hN : FStarSimple N)
    (hq : CFSG.Assembly.IsQuasisimple J) (hJ : IsUniversalComponent J)
    (heven : Even (Nat.card J)) (hJN : J ≤ N)
    (hCeven : Even (Nat.card (centralizer (J : Set H)))) :
    normalizer (blockGroup J : Set H) ≠ ⊤ := by
  intro htop
  have hDn : (blockGroup J).Normal := normalizer_eq_top_iff.1 htop
  haveI hNs : IsSimpleGroup ↥N := hN.isSimpleGroup
  haveI hNn : N.Normal := hN.normal
  have hJne : J ≠ ⊥ := by
    intro h
    exact not_le_centralizer_self_of_isQuasisimple hq (by rw [h]; exact bot_le)
  have hDN : blockGroup J ≤ N := by
    refine iSup₂_le fun K hK => ?_
    obtain ⟨g, rfl⟩ := hK.1
    have hconjN : N.map (MulAut.conj g).toMonoidHom = N := by
      simpa using Subgroup.Normal.map_conj_eq (H := N) g
    calc conjSub g J = J.map (MulAut.conj g).toMonoidHom := rfl
      _ ≤ N.map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hJN
      _ = N := hconjN
  have hDsub_ne_bot : (blockGroup J).subgroupOf N ≠ ⊥ := by
    intro h
    have hinf : blockGroup J ⊓ N = ⊥ := disjoint_iff.1 (Subgroup.subgroupOf_eq_bot.1 h)
    have hJle : J ≤ blockGroup J ⊓ N := le_inf (le_blockGroup mem_block_self) hJN
    exact hJne (le_bot_iff.1 (hinf ▸ hJle))
  have hDsubN : ((blockGroup J).subgroupOf N).Normal := hDn.subgroupOf N
  have hDsub_top : (blockGroup J).subgroupOf N = ⊤ := by
    rcases hDsubN.eq_bot_or_eq_top with h | h
    · exact absurd h hDsub_ne_bot
    · exact h
  have hDN_eq : blockGroup J = N := le_antisymm hDN (Subgroup.subgroupOf_eq_top.1 hDsub_top)
  have hJsubN : (J.subgroupOf N).Normal := by
    rw [← hDN_eq]
    exact normal_of_mem_block hJ heven mem_block_self
  have hJsub_ne_bot : J.subgroupOf N ≠ ⊥ := by
    intro h
    have hinf : J ⊓ N = ⊥ := disjoint_iff.1 (Subgroup.subgroupOf_eq_bot.1 h)
    have hJle : J ≤ J ⊓ N := le_inf le_rfl hJN
    exact hJne (le_bot_iff.1 (hinf ▸ hJle))
  have hJsub_top : J.subgroupOf N = ⊤ := by
    rcases hJsubN.eq_bot_or_eq_top with h | h
    · exact absurd h hJsub_ne_bot
    · exact h
  have hJN_eq : J = N := le_antisymm hJN (Subgroup.subgroupOf_eq_top.1 hJsub_top)
  have hcentN_bot : centralizer (N : Set H) = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    have hxN : x ∈ N := hN.centralizer_le hx
    rw [Subgroup.mem_bot]
    have hxZ : (⟨x, hxN⟩ : ↥N) ∈ Subgroup.center ↥N := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hx y y.2)
    have hZbot : Subgroup.center ↥N = ⊥ := by
      rcases (inferInstance : (Subgroup.center ↥N).Normal).eq_bot_or_eq_top with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hN.nonabelian
        refine hab ?_
        have ha : a ∈ Subgroup.center ↥N := h ▸ Subgroup.mem_top a
        exact (Subgroup.mem_center_iff.1 ha b).symm
    have hx1 : (⟨x, hxN⟩ : ↥N) = 1 := by
      rw [← Subgroup.mem_bot, ← hZbot]
      exact hxZ
    simpa using Subtype.ext_iff.1 hx1
  have hcentJ_bot : centralizer (J : Set H) = ⊥ := by rw [hJN_eq]; exact hcentN_bot
  rw [hcentJ_bot, Subgroup.card_bot] at hCeven
  exact Nat.not_even_one hCeven

theorem universal_rank_two_component_no_commuting_conjugate_of_ne_top
    (hq : CFSG.Assembly.IsQuasisimple J) (hrank : 2 ≤ CFSG.Assembly.pRank 2 J)
    (hJ : IsUniversalComponent J) (hH : normalizer (blockGroup J : Set H) ≠ ⊤) :
    (block J).Subsingleton := by
  by_contra hns
  have hΔ : (block J).Nontrivial := Set.not_subsingleton_iff.1 hns
  have heven : Even (Nat.card J) := even_card_of_two_le_pRank hrank
  have : Finite (Subgroup H) :=
    Finite.of_injective (fun K : Subgroup H => (K : Set H)) SetLike.coe_injective
  set D := blockGroup J with hD
  set r := Nat.card (block J) with hr
  have hr2 : 2 ≤ r := by
    have := (Set.one_lt_ncard_iff_nontrivial (s := block J)).2 hΔ
    rw [← Nat.card_coe_set_eq] at this
    omega
  let e : Fin r ≃ block J := (Finite.equivFin (block J)).symm
  let Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D) :=
    fun i => blockSection J (e i : Subgroup H)
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
    exact e.iSup_comp (g := fun K : block J => blockSection J (K : Subgroup H))
  have hperm : ∀ h ∈ normalizer (D : Set H), ∀ i, ∃ j,
      (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj h).toMonoidHom =
        aschbacherThm5Preimage D (Abar j) := by
    intro h hh i
    obtain ⟨hmem, hmap⟩ := map_conj_preimage_blockSection hq hJ heven hh (e i).2
    refine ⟨e.symm ⟨conjSub h (e i), hmem⟩, ?_⟩
    change _ = aschbacherThm5Preimage D (blockSection J (e (e.symm ⟨_, hmem⟩) : Subgroup H))
    rw [Equiv.apply_symm_apply]
    exact hmap
  have hcoreK : ∀ K ∈ block J, ⁅aschbacherThm5Core D, K⁆ = ⊥ := fun K hK => by
    rw [commutator_comm]
    exact commutator_eq_bot_core_of_mem_block hq hJ heven hK
  have hcoreC := commutator_core_blockGroup_eq_bot hq hJ heven
  have hcentK : ∀ (K : block J) (y : H),
      aschbacherThm5Centralizes (aschbacherThm5Core D)
        (aschbacherThm5Preimage D (blockSection J (K : Subgroup H))) y →
      y ∈ centralizer ((K : Subgroup H) : Set H) := by
    intro K y hy
    have : Group.IsPerfect (K : Subgroup H) := ⟨(isQuasisimple_of_isConjOf hq K.2.1).1⟩
    exact mem_centralizer_of_centralizes_modulo (hcoreK K K.2) hcoreC
      (fun a ha => hy a (le_preimage_blockSection (le_blockGroup K.2) ha))
  have hi : ∀ (i j : Fin r) (t g : H), (∃ k : ℕ, t ^ (2 ^ k) = 1) → t ∉ center H →
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar i)) t →
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar j))
        (g⁻¹ * t * g) →
      g ∈ normalizer (D : Set H) := by
    intro i j t g ht htc hti htj
    have ht1 : t ≠ 1 := fun h => htc (h ▸ one_mem _)
    exact mem_normalizer_blockGroup_of_two_element hJ heven (e i).2 (e j).2 ht ht1
      (hcentK (e i) t hti) (hcentK (e j) _ htj)
  have hii : ∀ (i : Fin r) (g : H) (X : Subgroup H),
      X ≤ (normalizer (D : Set H)).map (MulAut.conj g⁻¹).toMonoidHom →
      (∀ a ∈ aschbacherThm5Preimage D (Abar i), ∃ x ∈ X, ∃ o ∈ aschbacherThm5Core D,
        a = x * o) →
      g ∈ normalizer (D : Set H) := by
    intro i g X hX hcover
    have hKX : (e i : Subgroup H) ≤ X :=
      le_of_forall_eq_mul_mem
        (commutator_self_eq_of_assemblyQuasisimple (isQuasisimple_of_isConjOf hq (e i).2.1))
        (hcoreK _ (e i).2) hcoreC
        (fun a ha => hcover a (le_preimage_blockSection (le_blockGroup (e i).2) ha))
    have hconj : conjSub g (e i : Subgroup H) ≤ normalizer (D : Set H) :=
      calc conjSub g (e i : Subgroup H) ≤ conjSub g X := Subgroup.map_mono hKX
        _ ≤ conjSub g (conjSub g⁻¹ (normalizer (D : Set H))) := Subgroup.map_mono hX
        _ = normalizer (D : Set H) := conjSub_conjSub_inv g _
    exact commuting_block_factor_containment_transporter_all hq heven hJ hΔ (e i).2 hconj
  have hH' : normalizer (D : Set H) ≠ ⊤ := by rw [hD]; exact hH
  rcases CFSG.Milestones.cl_lit_aschbacher_component_type_theorem_5 H D r (by omega) Abar
      hdistinct hsemisimple hcomm hgen hperm hi hii hH' with h1 | ⟨-, hrest⟩
  · omega
  · set i0 : Fin r := ⟨0, by omega⟩ with hi0
    have hrank1 := (hrest i0 ⟨1, by omega⟩ (by simp [hi0, Fin.ext_iff])).2.1
    have hle : CFSG.Open.pRank 2 J ≤ CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar i0)) :=
      pRank_le_pRank_preimage_blockSection (e i0).2
    have hrank' : 2 ≤ CFSG.Open.pRank 2 J := hrank
    omega

theorem universal_rank_two_component_eq_of_commutator_eq_bot_of_ne_top
    (hq : CFSG.Assembly.IsQuasisimple J) (hrank : 2 ≤ CFSG.Assembly.pRank 2 J)
    (hJ : IsUniversalComponent J) (hH : normalizer (blockGroup J : Set H) ≠ ⊤) (g : H)
    (hg : ⁅J, conjSub g J⁆ = ⊥) : conjSub g J = J := by
  exact universal_rank_two_component_no_commuting_conjugate_of_ne_top hq hrank hJ hH
    (⟨⟨g, rfl⟩, Or.inr hg⟩ : conjSub g J ∈ block J) mem_block_self

theorem universal_rank_two_component_commutator_ne_bot_of_ne_top
    (hq : CFSG.Assembly.IsQuasisimple J) (hrank : 2 ≤ CFSG.Assembly.pRank 2 J)
    (hJ : IsUniversalComponent J) (hH : normalizer (blockGroup J : Set H) ≠ ⊤) (g : H) :
    ⁅J, J.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
  intro hg
  have hJg := universal_rank_two_component_eq_of_commutator_eq_bot_of_ne_top hq hrank hJ hH g hg
  rw [show J.map (MulAut.conj g).toMonoidHom = J from hJg] at hg
  exact not_le_centralizer_self_of_isQuasisimple hq (commutator_eq_bot_iff_le_centralizer.1 hg)

theorem universal_rank_two_component_isStandardSubgroup_of_ne_top
    (hq : CFSG.Assembly.IsQuasisimple J) (hrank : 2 ≤ CFSG.Assembly.pRank 2 J)
    (hCeven : Even (Nat.card (centralizer (J : Set H)))) (hJ : IsUniversalComponent J)
    (hH : normalizer (blockGroup J : Set H) ≠ ⊤) :
    CFSG.Assembly.ComponentType.IsStandardSubgroup J := by
  exact (involution_component_standard_criterion hq hCeven
    (universal_rank_two_component_commutator_ne_bot_of_ne_top hq hrank hJ hH)).2 hJ

end CFSG.EvenSporadicStandard.Induction.ThmU
