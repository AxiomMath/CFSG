module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.AGLEmbedding

section Abstract

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
private lemma exists_isPGroup_three_map_conj {L : Subgroup X} {t : X} (htL : t ∈ L)
    (ht3 : orderOf t = 3) (htc : t ∉ Subgroup.centralizer (L : Set X)) (c : X) :
    ∃ u ∈ L.map (MulAut.conj c).toMonoidHom, IsPGroup 3 (Subgroup.zpowers u) ∧
      ∃ l ∈ L.map (MulAut.conj c).toMonoidHom, u * l ≠ l * u := by
  have hne : ∃ l ∈ L, l * t ≠ t * l := by
    by_contra h
    push Not at h
    exact htc (Subgroup.mem_centralizer_iff.mpr h)
  obtain ⟨l, hlL, hlt⟩ := hne
  refine ⟨c * t * c⁻¹, ?_, ?_, c * l * c⁻¹, ?_, ?_⟩
  · simpa [MulAut.conj_apply] using
      Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom htL
  · exact IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, ← ht3, pow_one]
      exact MulEquiv.orderOf_eq (MulAut.conj c) t)
  · simpa [MulAut.conj_apply] using
      Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom hlL
  · intro heq
    have h' : t * l = l * t := by
      simpa [mul_assoc] using congrArg (fun z => c⁻¹ * z * c) heq
    exact hlt h'.symm

theorem relIndex_inf_normalizer_le_pRank_three {L : Subgroup X} (hL : IsComponentOf L ⊤)
    (ht : ∃ t ∈ L, orderOf t = 3 ∧ t ∉ Subgroup.centralizer (L : Set X)) (D : Subgroup X) :
    (D ⊓ Subgroup.normalizer (L : Set X)).relIndex D ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  classical
  obtain ⟨t, htL, ht3, htc⟩ := ht
  let _ : MulDistribMulAction (ConjAct X) X := inferInstance
  let _ : MulAction (ConjAct X) (Subgroup X) := Subgroup.pointwiseMulAction
  let _ : MulAction D (Subgroup X) :=
    MulAction.compHom (Subgroup X) (ConjAct.toConjAct.toMonoidHom.comp D.subtype)
  have hsmul : ∀ (g : D) (H : Subgroup X),
      g • H = H.map (MulAut.conj (g : X)).toMonoidHom := by
    intro g H
    rw [MulAction.compHom_smul_def, Subgroup.pointwise_smul_def]
    congr 1
  have hstab : MulAction.stabilizer D L =
      (D ⊓ Subgroup.normalizer (L : Set X)).subgroupOf D := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_normalizer_iff_map_conj_eq, hsmul]
    simp
  have hidx : (D ⊓ Subgroup.normalizer (L : Set X)).relIndex D =
      Nat.card (MulAction.orbit D L) := by
    rw [Subgroup.relIndex, ← hstab, MulAction.index_stabilizer, Nat.card_coe_set_eq]
  rw [hidx]
  let f : MulAction.orbit D L → D := fun i => Classical.choose i.2
  have hf : ∀ i : MulAction.orbit D L, f i • L = i.1 := fun i => Classical.choose_spec i.2
  have hy : ∀ i : MulAction.orbit D L, ∃ u ∈ i.1, IsPGroup 3 (Subgroup.zpowers u) ∧
      ∃ l ∈ i.1, u * l ≠ l * u := by
    intro i
    rw [← hf i, hsmul]
    exact exists_isPGroup_three_map_conj htL ht3 htc (f i)
  choose y hyL hyq l hyl hyZ using hy
  exact le_pRank_of_components Nat.prime_three (fun i : MulAction.orbit D L => i.1)
    (fun i => by
      rw [← hf i, hsmul]
      exact (CFSG.ComponentClassification.LocalComponents.equiv_iff
        (MulAut.conj (f i : X)) L).mpr hL)
    (fun i j h => Subtype.ext h) ⊤ y (fun i => Subgroup.mem_top _) hyL hyq
    (fun i => ⟨l i, hyl i, hyZ i⟩)

theorem le_normalizer_of_isPGroup_of_pRank_three_le_three {L : Subgroup X}
    (hL : IsComponentOf L ⊤)
    (ht : ∃ t ∈ L, orderOf t = 3 ∧ t ∉ Subgroup.centralizer (L : Set X))
    (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3) {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d)
    {D : Subgroup X} (hD : IsPGroup d D) : D ≤ Subgroup.normalizer (L : Set X) := by
  have : Fact d.Prime := ⟨hd⟩
  have hle := relIndex_inf_normalizer_le_pRank_three hL ht D
  obtain ⟨n, hn⟩ := hD.index ((D ⊓ Subgroup.normalizer (L : Set X)).subgroupOf D)
  have hrel : (D ⊓ Subgroup.normalizer (L : Set X)).relIndex D = d ^ n := hn
  have hn0 : n = 0 := by
    by_contra hn0
    have hdn : d ≤ d ^ n := Nat.le_self_pow hn0 d
    omega
  rw [hn0, pow_zero, Subgroup.relIndex_eq_one] at hrel
  exact hrel.trans inf_le_right

end Abstract

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_barM_of_isPGroup {M L : Subgroup G} (hL : IsTwoPrimeComponent M L)
    (hm3 : CFSG.Open.pRank 3 M ≤ 3)
    (ht : ∃ t ∈ barM M L, orderOf t = 3 ∧
      t ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d) {D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hD : IsPGroup d D) :
    D ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have htop : barM M M = ⊤ := by
    rw [barM, Subgroup.subgroupOf_self]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have h3 : CFSG.Open.pRank 3 (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ 3 := by
    rw [← htop]
    exact (pRank_barM_le Nat.prime_three (by norm_num) M M le_rfl).trans hm3
  exact le_normalizer_of_isPGroup_of_pRank_three_le_three hL.component ht h3 hd hd5 hD

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
