module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeExc
public import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExclusionsTwo
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TitsP3NoElemAbelian

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup TauCeti
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section Generic

variable {X : Type} [Group X] [Finite X]

theorem pRank_top_subgroup_le (L : Subgroup X) :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
  CFSG.SectionRank.pRank_top_le_of_injective (by norm_num) L.subtype L.subtype_injective

theorem exists_elemAbelian_27 (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3) :
    ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 27 := by
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup X)
  exact ⟨E, hE, by rw [hcard, h3]; norm_num⟩

theorem centRankAt_of_four_le {d : ValidLieTypeIndex}
    (h4 : ∀ (K : Type) [Group K] [Finite K], (K ≃* (CFSGIndex.lie d).Group) →
      4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K)) : CentRankAt d := by
  intro X _ _ L _ _ _ ⟨e⟩ _ hX x _
  exfalso
  have h1 := h4 ↥L e
  have h2 := pRank_top_subgroup_le L
  omega

theorem centRankAt_of_aut {d : ValidLieTypeIndex}
    (hA : ∀ (K : Type) [Group K] [Finite K], (K ≃* (CFSGIndex.lie d).Group) →
      ∀ E : Subgroup (MulAut K), IsElemAbelian 3 E → Nat.card E ≠ 27) : CentRankAt d := by
  intro X _ _ L hLn _ _ ⟨e⟩ hC hX x _
  exfalso
  have hinj : Function.Injective (MulAut.conjNormal : X →* MulAut ↥L) :=
    conjNormal_injective_of_centralizer_eq_bot L hC
  obtain ⟨E, hE, hE27⟩ := exists_elemAbelian_27 hX
  refine hA ↥L e (E.map (MulAut.conjNormal : X →* MulAut ↥L))
    (CFSG.SectionRank.isElemAbelian_map hE _) ?_
  rw [Subgroup.card_map_of_injective hinj, hE27]

theorem mem_of_not_three_dvd_outer {L : Subgroup X} [L.Normal]
    (hC : centralizer (L : Set X) = ⊥) (hO : ¬ 3 ∣ Nat.card (Outer ↥L)) {g : X}
    (hg : g ^ 3 = 1) : g ∈ L := by
  set φ : MulAut ↥L := MulAut.conjNormal g with hφ
  have hφ3 : φ ^ 3 = 1 := by rw [hφ, ← map_pow, hg, map_one]
  have hq : (QuotientGroup.mk φ : Outer ↥L) = 1 := by
    have h1 : orderOf (QuotientGroup.mk φ : Outer ↥L) ∣ 3 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← QuotientGroup.mk_pow, hφ3, QuotientGroup.mk_one]
    have h2 : orderOf (QuotientGroup.mk φ : Outer ↥L) ∣ Nat.card (Outer ↥L) :=
      orderOf_dvd_natCard _
    have h3 : orderOf (QuotientGroup.mk φ : Outer ↥L) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
      · exact h
      · rw [h] at h2
        exact absurd h2 hO
    exact orderOf_eq_one_iff.1 h3
  obtain ⟨l, hl⟩ : φ ∈ inner ↥L := (QuotientGroup.eq_one_iff φ).1 hq
  have hc : (l : X)⁻¹ * g ∈ centralizer (L : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg (fun α : MulAut ↥L => ((α ⟨y, hy⟩ : ↥L) : X)) hl
    simp only [hφ, MulAut.conjNormal_apply, MulAut.conj_apply] at h1
    change (l : X) * y * (l : X)⁻¹ = g * y * g⁻¹ at h1
    calc y * ((l : X)⁻¹ * g) = (l : X)⁻¹ * ((l : X) * y * (l : X)⁻¹) * g := by group
      _ = (l : X)⁻¹ * (g * y * g⁻¹) * g := by rw [h1]
      _ = (l : X)⁻¹ * g * y := by group
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hc
  rw [← hc]
  exact l.2

theorem centRankAt_of_outer {d : ValidLieTypeIndex}
    (hO : ∀ (K : Type) [Group K] [Finite K], (K ≃* (CFSGIndex.lie d).Group) →
      ¬ 3 ∣ Nat.card (Outer K))
    (hR : ∀ (K : Type) [Group K] [Finite K], (K ≃* (CFSGIndex.lie d).Group) →
      ∀ E : Subgroup K, IsElemAbelian 3 E → Nat.card E ≠ 27) : CentRankAt d := by
  intro X _ _ L hLn _ _ ⟨e⟩ hC hX x _
  exfalso
  obtain ⟨E, hE, hE27⟩ := exists_elemAbelian_27 hX
  have hEL : E ≤ L := fun g hg => mem_of_not_three_dvd_outer hC (hO ↥L e) (hE.2 g hg)
  refine hR ↥L e (E.subgroupOf L) ?_ ?_
  · refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a ha => Subtype.ext (hE.2 _ ha)⟩
    show ((a : ↥L) : X) * ((b : ↥L) : X) = ((b : ↥L) : X) * ((a : ↥L) : X)
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨((a : ↥L) : X), a.2⟩ ⟨((b : ↥L) : X), b.2⟩)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hE27]

end Generic

section ExcBig


theorem centRankAt_excBig {d : ValidLieTypeIndex}
    (hd : CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.I294CrossIsExcBig d.1) :
    CentRankAt d :=
  centRankAt_of_four_le fun _ _ _ e =>
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.four_le_pRank_three_of_isExcBig
      d hd e

end ExcBig

section Suzuki


theorem centRankAt_suzuki (m : ℕ) (hv : (LieTypeIndex.suzuki m).Valid) :
    CentRankAt ⟨.suzuki m, hv⟩ := by
  refine centRankAt_of_aut fun K _ _ e E hE h27 => ?_
  have hdvd := CFSG.RankThree.PartTwo.KFacts.KP7.card_dvd_three_of_pow_three
    (CFSG.HardMathSupport.Cooperstein.Coordinator.suzukiModel_of_lie hv e) hE.2
  rw [h27] at hdvd
  norm_num at hdvd

end Suzuki

section Tits


theorem centRankAt_tits (hv : LieTypeIndex.tits.Valid) : CentRankAt ⟨.tits, hv⟩ := by
  refine centRankAt_of_outer (fun K _ _ e => ?_) (fun K _ _ e E hE h27 => ?_)
  · obtain ⟨f⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv K 2 1
      (CFSG.HardMathSupport.Cooperstein.Coordinator.reeTitsModel_tits_of_lie hv e)
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence f).toEquiv,
      CFSG.Sporadic.Schreier.Tits.card_outer_titsD]
    decide
  · exact CFSG.HardMathSupport.Timmesfeld.CrossChar.no_elemAbelian27_cat_tits hv
      (E := E.map e.toMonoidHom) (CFSG.SectionRank.isElemAbelian_map hE _)
      (by rw [Subgroup.card_map_of_injective e.injective, h27])

end Tits

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
