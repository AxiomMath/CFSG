module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Sec
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma18iii
public import CFSG.GH74.GLS.Stage2.Local.P34S5Jbar
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK
open scoped commutatorElement

theorem isL2_of_simple_quot {F₀ : Type} [Field F₀] [Finite F₀] (hodd : Odd (Nat.card F₀))
    (h3 : 3 < Nat.card F₀) {S : Type} [Group S] (e : S ≃* GorensteinWalter.PSL2 F₀) {Y : Type}
    [Group Y] [IsSimpleGroup Y] (φ : S →* Y) (hφ : Function.Surjective φ) :
    IVK.IsL2 Y (fun r => Odd r ∧ 5 ≤ r) := by
  have hPSL : IsSimpleGroup (GorensteinWalter.PSL2 F₀) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  have hS : IsSimpleGroup S := e.isSimpleGroup
  have hker : φ.ker = ⊥ := by
    rcases hS.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨y, hy⟩ := exists_ne (1 : Y)
      obtain ⟨s, rfl⟩ := hφ y
      have : s ∈ φ.ker := by rw [h]; trivial
      exact hy (MonoidHom.mem_ker.mp this)
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
  let ψ : S ≃* Y := MulEquiv.ofBijective φ ⟨hinj, hφ⟩
  have h5 : 5 ≤ Nat.card F₀ := by
    obtain ⟨k, hk⟩ := hodd
    omega
  exact ⟨F₀, inferInstance, inferInstance, ⟨hodd, h5⟩, ⟨ψ.symm.trans (e.trans (L2.equivPSL F₀).symm)⟩⟩

theorem odd_card_of_ringChar_eq {F F₀ : Type} [Field F] [Finite F] [Field F₀] [Finite F₀]
    (hF : Odd (Nat.card F)) (h : ringChar F₀ = ringChar F) : Odd (Nat.card F₀) := by
  classical
  let _ : Fintype F := Fintype.ofFinite F
  let _ : Fintype F₀ := Fintype.ofFinite F₀
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  have hp2 : ringChar F ≠ 2 := by
    intro h2
    rw [Nat.card_eq_fintype_card, hn, h2] at hF
    have : Even (2 ^ (n : ℕ)) := (Nat.even_pow).mpr ⟨even_two, n.pos.ne'⟩
    exact (Nat.not_even_iff_odd.mpr hF) this
  have : CharP F₀ (ringChar F) := by rw [← h]; exact ringChar.charP F₀
  obtain ⟨n₀, hp₀, hn₀⟩ := FiniteField.card F₀ (ringChar F)
  rw [Nat.card_eq_fintype_card, hn₀]
  exact Odd.pow ((hp.eq_two_or_odd').resolve_left hp2)

theorem simple_sec_L2 {F : Type} [Field F] [Finite F] (hF : L2Field F)
    {Y : Type} [Group Y] [IsSimpleGroup Y] (hns : ¬ Group.IsSolvable Y) (h : IsSection Y (L2 F)) :
    IVK.IsL2 Y (fun r => Odd r ∧ 5 ≤ r) := by
  obtain ⟨L, φ, hφ⟩ := h
  have hLns : ¬ Group.IsSolvable ↥L := fun hs => hns (Group.isSolvable_of_surjective hφ)
  have h18 := (Proofs2.ivk_1_8 F hF (L2 F) (MulEquiv.refl _)).1 L hLns
  rcases h18 with ⟨F₀, iF₀, fF₀, hchar, hle, hL | hL⟩ | ⟨F₀, iF₀, fF₀, h5, ⟨e⟩⟩
  · obtain ⟨e⟩ := hL
    have hodd := odd_card_of_ringChar_eq hF.1 hchar
    have h3 : 3 < Nat.card F₀ := by
      by_contra hle3
      apply hLns
      have : Group.IsSolvable (GorensteinWalter.PSL2 F₀) :=
        Stage2.Local.P34.psl2_solvable_of_card_le_three (by omega)
      exact Group.isSolvable_of_isSolvable_injective (f := (toPSL e).toMonoidHom) (toPSL e).injective
    exact isL2_of_simple_quot hodd h3 (toPSL e) φ hφ
  · obtain ⟨e⟩ := hL
    have hodd := odd_card_of_ringChar_eq hF.1 hchar
    have h3 : 3 < Nat.card F₀ := by
      by_contra hle3
      apply hLns
      have h1 : 1 < Nat.card F₀ := Finite.one_lt_card
      have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) F₀) :=
        ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable F₀ (by omega)
      have hs : Group.IsSolvable (GorensteinWalter.PGL2 F₀) :=
        Group.isSolvable_of_surjective (f := (Matrix.ProjGenLinGroup.mk :
          Matrix.GeneralLinearGroup (Fin 2) F₀ →* GorensteinWalter.PGL2 F₀))
          Matrix.ProjGenLinGroup.mk_surjective
      exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    obtain ⟨e'⟩ := GorensteinWalter.commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three F₀
      (ABGLocalTools.isOddPrimePower_card_of_odd hodd) h3 e
    have hYcomm := commutator_eq_top_of_simple hns
    let C : Subgroup ↥L := commutator ↥L
    have hmap : C.map φ = commutator Y := by
      have h1 := Subgroup.map_commutator (⊤ : Subgroup ↥L) ⊤ φ
      have h2 : Subgroup.map φ (⊤ : Subgroup ↥L) = ⊤ := by
        rw [← MonoidHom.range_eq_map]; exact MonoidHom.range_eq_top.mpr hφ
      rw [h2] at h1
      exact h1
    have hCsurj : Function.Surjective (φ.comp C.subtype) := by
      intro y
      have hy : y ∈ C.map φ := by rw [hmap, hYcomm]; trivial
      obtain ⟨c, hc, rfl⟩ := hy
      exact ⟨⟨c, hc⟩, rfl⟩
    exact isL2_of_simple_quot hodd h3 e' (φ.comp C.subtype) hCsurj
  · have hodd : Odd (Nat.card F₀) := by rw [h5]; decide
    exact isL2_of_simple_quot hodd (by omega) (toPSL e) φ hφ

theorem isSection_L2_of_SL2 {F : Type} [Field F] [Finite F] {Y : Type} [Group Y] [IsSimpleGroup Y]
    (hns : ¬ Group.IsSolvable Y) (h : IsSection Y (SL2 F)) : IsSection Y (L2 F) := by
  rcases h.dichotomy ((Assembly.LowTwoRank.StatedScalars (Fin 2) F).subgroupOf
      (Assembly.LowTwoRank.StatedSL 2 F)) with h1 | h2
  · exfalso
    apply hns
    refine h1.isSolvable (Group.isSolvable_of_comm ?_)
    intro a b
    have ha : (a : GL (Fin 2) F) ∈ Subgroup.center (GL (Fin 2) F) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact Subgroup.mem_subgroupOf.mp a.2
    have := Subgroup.mem_center_iff.mp ha (b : GL (Fin 2) F)
    exact Subtype.ext (Subtype.ext this.symm)
  · exact h2

theorem simple_sec_of_SL2model {L : Type} [Group L] {r : ℕ}
    (hr : Odd r) (hL : HasSL2Model L (fun q => q = r)) {Y : Type} [Group Y] [IsSimpleGroup Y]
    (hns : ¬ Group.IsSolvable Y) (h : IsSection Y L) : IVK.IsL2 Y (fun q => Odd q ∧ 5 ≤ q) := by
  obtain ⟨F, iF, fF, hrF, ⟨e⟩⟩ := hL
  have hodd : Odd (Nat.card F) := by rw [hrF]; exact hr
  have h1 : IsSection Y (SL2 F) := IsSection.of_equiv e.symm h
  by_cases h3 : 3 < Nat.card F
  · exact simple_sec_L2 ⟨hodd, h3⟩ hns (isSection_L2_of_SL2 hns h1)
  · exfalso
    apply hns
    have hF1 : 1 < Nat.card F := Finite.one_lt_card
    have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) F) :=
      ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable F (by
        obtain ⟨k, hk⟩ := hodd
        omega)
    have : Group.IsSolvable (SL2 F) := inferInstance
    exact h1.isSolvable this

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
