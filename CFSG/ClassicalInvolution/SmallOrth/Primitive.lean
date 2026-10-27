module

public import CFSG.ClassicalGroups.Orthogonal.Lines
public import CFSG.ClassicalInvolution.SmallOrth.Basic

public section

namespace CFSG.ClassicalGroups.Orthogonal.Small

open QuadraticMap
open scoped LinearAlgebra.Projectivization

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_orth_hypPair_of_mem_perp (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q) {y : V}
    (hyP : y ∈ P.perp) (hy0 : y ≠ 0) (hy : Q y = 0) : ∃ P' : HypPair Q, P.Orth P' ∧ P'.e = y := by
  obtain ⟨v, hvP, hv⟩ := (P.polarNondegOn_perp hQ).exists_polar_ne_zero hyP hy0
  obtain ⟨v₁, hv₁P, hyv₁⟩ : ∃ v₁ ∈ P.perp, polar Q y v₁ = 1 :=
    ⟨(polar Q y v)⁻¹ • v, P.perp.smul_mem _ hvP, by
      rw [polar_smul_right_eq, inv_mul_cancel₀ hv]⟩
  refine ⟨HypPair.ofPolarEqOne hy hyv₁, ⟨?_, ?_, ?_, ?_⟩, rfl⟩
  · exact (HypPair.mem_perp.mp hyP).1
  · change polar Q P.e (v₁ - Q v₁ • y) = 0
    rw [polar_sub_right, polar_smul_right_eq, (HypPair.mem_perp.mp hv₁P).1,
      (HypPair.mem_perp.mp hyP).1]
    ring
  · exact (HypPair.mem_perp.mp hyP).2
  · change polar Q P.f (v₁ - Q v₁ • y) = 0
    rw [polar_sub_right, polar_smul_right_eq, (HypPair.mem_perp.mp hv₁P).2,
      (HypPair.mem_perp.mp hyP).2]
    ring

theorem exists_eq_smul_of_polar_eq_zero_of_noOrth (hQ : (polarBilin Q).Nondegenerate)
    (hW1 : ∀ P P' : HypPair Q, ¬ P.Orth P') {e x : V} (he : Q e = 0) (he0 : e ≠ 0) (hx : Q x = 0)
    (hex : polar Q e x = 0) : ∃ c : K, x = c • e := by
  by_contra! hxe
  obtain ⟨P, rfl⟩ := exists_hypPair hQ he he0
  set α := polar Q x P.f with hα
  have hxe' : polar Q x P.e = 0 := by rw [polar_comm, hex]
  have hy' : P.proj x = x - α • P.e := by
    rw [HypPair.proj, hxe', zero_smul, sub_zero]
  have hy'P : x - α • P.e ∈ P.perp := hy' ▸ P.proj_mem_perp x
  have hy'0 : x - α • P.e ≠ 0 := fun h => hxe α (sub_eq_zero.mp h)
  have hy'Q : Q (x - α • P.e) = 0 := by
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, map_smul_eq_sq, P.Q_e,
      polar_neg_right, polar_smul_right_eq, hxe', hx]
    ring
  obtain ⟨P', hP', -⟩ := exists_orth_hypPair_of_mem_perp hQ P hy'P hy'0 hy'Q
  exact hW1 P P' hP'

theorem isPretransitive_singularLines_small (hQ : (polarBilin Q).Nondegenerate)
    (hA : HasAnisoPerp Q) : MulAction.IsPretransitive (elementaryGroup Q) (singularLines Q) := by
  refine ⟨fun p q => ?_⟩
  obtain ⟨v, hv, hQv, rfl⟩ := exists_eq_lineMk p
  obtain ⟨w, hw, hQw, rfl⟩ := exists_eq_lineMk q
  obtain ⟨g, hg, c, hc, hgv⟩ := exists_mem_elementaryGroup_apply_eq_smul hQ hA hQv hQw hv hw
  exact ⟨⟨g, hg⟩, smul_lineMk_of_apply_eq_smul hv hw hQv hQw hgv⟩

variable {B : Set (singularLines Q)}

theorem smul_mem_of_isBlock' (hB : MulAction.IsBlock (elementaryGroup Q) B)
    {p q : singularLines Q} (hp : p ∈ B) (hq : q ∈ B) {g : elementaryGroup Q} (hg : g • p = p) :
    g • q ∈ B := by
  have h := hB.smul_eq_of_mem hp (by rwa [hg])
  rw [← h]
  exact Set.smul_mem_smul_set hq

theorem inv_smul_mem_of_isBlock' (hB : MulAction.IsBlock (elementaryGroup Q) B)
    {p q : singularLines Q} (hp : p ∈ B) (hq : q ∈ B) {g : elementaryGroup Q} (hg : g • p = p) :
    g⁻¹ • q ∈ B :=
  smul_mem_of_isBlock' hB hp hq (by rw [inv_smul_eq_iff, hg])

theorem isPreprimitive_singularLines_of_noOrth (hQ : (polarBilin Q).Nondegenerate)
    (hA : HasAnisoPerp Q) (hW1 : ∀ P P' : HypPair Q, ¬ P.Orth P') (P₀ : HypPair Q) :
    MulAction.IsPreprimitive (elementaryGroup Q) (singularLines Q) := by
  have := isPretransitive_singularLines_small hQ hA
  apply MulAction.IsPreprimitive.of_isTrivialBlock_base (lineMk P₀.e P₀.e_ne_zero P₀.Q_e)
  intro B hα hB
  by_cases hsub : B.Subsingleton
  · exact Or.inl hsub
  right
  obtain ⟨b, hbB, hbα⟩ : ∃ b ∈ B, b ≠ lineMk P₀.e P₀.e_ne_zero P₀.Q_e := by
    by_contra hcon
    push Not at hcon
    exact hsub fun p hp q hq => by rw [hcon p hp, hcon q hq]
  obtain ⟨x, hx0, hx, rfl⟩ := exists_eq_lineMk b
  have hnot : ∀ {y : V} (hy0 : y ≠ 0) (hy : Q y = 0),
      lineMk y hy0 hy ≠ lineMk P₀.e P₀.e_ne_zero P₀.Q_e → polar Q P₀.e y ≠ 0 := by
    intro y hy0 hy hne hpol
    obtain ⟨c, hc⟩ := exists_eq_smul_of_polar_eq_zero_of_noOrth hQ hW1 P₀.Q_e P₀.e_ne_zero hy hpol
    apply hne
    rw [lineMk_eq_lineMk_iff]
    exact ⟨c, hc.symm⟩
  refine Set.eq_univ_of_forall fun q => ?_
  by_cases hq : q = lineMk P₀.e P₀.e_ne_zero P₀.Q_e
  · rw [hq]
    exact hα
  obtain ⟨y, hy0, hy, rfl⟩ := exists_eq_lineMk q
  obtain ⟨k, hk, hke, c, hkx⟩ := exists_fix_apply_eq_smul_of_polar_ne_zero P₀.Q_e hx hy
    (hnot hx0 hx hbα) (hnot hy0 hy hq)
  have hkα : (⟨k, hk⟩ : elementaryGroup Q) • lineMk P₀.e P₀.e_ne_zero P₀.Q_e =
      lineMk P₀.e P₀.e_ne_zero P₀.Q_e :=
    smul_lineMk_of_apply_eq_smul _ _ _ _ (c := 1) (by rw [one_smul]; exact hke)
  have := smul_mem_of_isBlock' hB hα hbB hkα
  rwa [smul_lineMk_of_apply_eq_smul hx0 hy0 hx hy hkx] at this

end CFSG.ClassicalGroups.Orthogonal.Small
