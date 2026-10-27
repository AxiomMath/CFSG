module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.Descent
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.InnOrthType
public import CFSG.Adapters.LieModelSimple
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs CFSG.RankThree.PartTwo.KFacts

theorem IsCatalogLieIso.of_mulEquiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) {P : TauCeti.LieTypeIndex → Prop}
    (h : IsCatalogLieIso X P) : IsCatalogLieIso Y P := by
  obtain ⟨d, hd, ⟨f⟩⟩ := h
  exact ⟨d, hd, ⟨e.symm.trans f⟩⟩

theorem card_of_isD42Type {K : Type} [Group K]
    (h : IsCatalogLieIso K IsD42Index) : Nat.card K = 174182400 := by
  rw [CFSG.SeitzReduction.OmegaPilot.card_of_lieModel_POmega_two (Or.inl rfl)
    (lieModel_of_isD42 h)]
  decide

theorem isSimpleGroup_of_isD42Type {X : Type} [Group X]
    (h : IsCatalogLieIso X IsD42Index) :
    IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  have hsimple : IsSimpleGroup X :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide)
      (lieModel_of_isD42 h)
  refine ⟨hsimple, ?_⟩
  by_contra hno
  push Not at hno
  let cX : CommGroup X := { ‹Group X› with mul_comm := fun a b => hno a b }
  have hcard := card_of_isD42Type h
  have hp := @IsSimpleGroup.prime_card X cX hsimple
  rw [hcard] at hp
  exact absurd hp (by norm_num)

theorem isD42Type_barOf_of_central {Y P : Type} [Group Y] [Finite Y] [Group P] [Finite P]
    (π : Y →* P) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center Y)
    (α : MulAut Y) (ψ : MulAut P) (hαψ : ∀ y, π (α y) = ψ (π y))
    {J : Subgroup Y} (hJ : GLAPComponent 3 (fixSubgroup α) J)
    (hr : IsCatalogLieIso (barOf 3 J) IsD42Index) :
    ∃ A : Subgroup P, GLAPComponent 3 (fixSubgroup ψ) A ∧
      IsCatalogLieIso (barOf 3 A) IsD42Index := by
  have hA := glaPComponent_map_fixSubgroup π hker α ψ hαψ hπ Nat.prime_three hJ
  refine ⟨J.map π, hA, ?_⟩
  have hAq : CFSG.Open.IsQuasisimple (barOf 3 (J.map π)) :=
    isQuasisimple_barOf_of_glaPComponent Nat.prime_three hA
  let φ : ↥J →* ↥(J.map π) := π.subgroupMap J
  have hφ : Function.Surjective φ := π.subgroupMap_surjective J
  let f₀ : ↥J →* barOf 3 (J.map π) := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(J.map π))).comp φ
  have hk : GLAPPrimeCore 3 ↥J ≤ f₀.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).2 (map_gLAPPrimeCore_le' 3 φ hφ ⟨x, hx, rfl⟩)
  let f : barOf 3 J →* barOf 3 (J.map π) := QuotientGroup.lift _ f₀ hk
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥(J.map π)) y
    obtain ⟨j, rfl⟩ := hφ a
    exact ⟨QuotientGroup.mk j, rfl⟩
  have hsimple : IsSimpleGroup (barOf 3 J) := (isSimpleGroup_of_isD42Type hr).1
  let : IsSimpleGroup (barOf 3 J) := hsimple
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    have hnorm := f.normal_ker
    let : f.ker.Normal := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
    · exact h
    · exfalso
      have hall : ∀ y : barOf 3 (J.map π), y = 1 := by
        intro y
        obtain ⟨x, rfl⟩ := hf y
        have : x ∈ f.ker := by rw [h]; exact Subgroup.mem_top x
        exact this
      have hsub : Subsingleton (barOf 3 (J.map π)) := ⟨fun a b => (hall a).trans (hall b).symm⟩
      have hs2 : Subsingleton (barOf 3 (J.map π) ⧸ Subgroup.center (barOf 3 (J.map π))) :=
        (QuotientGroup.mk'_surjective (Subgroup.center (barOf 3 (J.map π)))).subsingleton
      exact (not_nontrivial_iff_subsingleton.2 hs2) hAq.2.toNontrivial
  exact IsCatalogLieIso.of_mulEquiv (MulEquiv.ofBijective f ⟨hinj, hf⟩) hr

theorem UpD42Pumpup.congr {S P : Type} [Group S] [Finite S] [Group P] [Finite P]
    (e : S ≃* P) {α : MulAut S} (h : UpD42Pumpup S α) :
    UpD42Pumpup P (MulAut.congr e α) := by
  obtain ⟨hα3, hα1, I, hI, hD⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [← map_pow, hα3, map_one]
  · intro h1
    exact hα1 ((MulAut.congr e).injective (h1.trans (map_one _).symm))
  · have hker : e.toMonoidHom.ker ≤ Subgroup.center S := by
      rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective]
      exact bot_le
    exact isD42Type_barOf_of_central e.toMonoidHom e.surjective hker α
      (MulAut.congr e α) (fun y => by simp [MulAut.congr_apply]) hI hD

theorem UpD42Pumpup.descend {Q : Type} [Group Q] [Finite Q] (hq : CFSG.Open.IsQuasisimple Q)
    {β : MulAut Q} (h : UpD42Pumpup Q β) :
    UpD42Pumpup (Q ⧸ Subgroup.center Q) (centerDescend Q β) := by
  obtain ⟨hβ3, hβ1, J, hJ, hJ42⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [← map_pow, hβ3, map_one]
  · intro h1
    exact hβ1 (eq_one_of_centerDescend_eq_one hq h1)
  · have hπ : Function.Surjective (QuotientGroup.mk' (Subgroup.center Q)) :=
      QuotientGroup.mk'_surjective _
    have hker : (QuotientGroup.mk' (Subgroup.center Q)).ker ≤ Subgroup.center Q := by
      rw [QuotientGroup.ker_mk']
    exact isD42Type_barOf_of_central (QuotientGroup.mk' (Subgroup.center Q)) hπ hker β
      (centerDescend Q β) (fun y => rfl) hJ hJ42

end CFSG.HardMathSupport.Dickson.Sec6

end
