module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PCLie
public import CFSG.LocalAnalysis.ComponentClassification.GS82PCSpor

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem oddLieType_of_alternating_five_or_six {X : Type} [Group X]
    {n : ℕ} (hn : n = 5 ∨ n = 6) (e : X ≃* alternatingGroup (Fin n)) :
    Blueprint.OddLieType X := by
  rcases hn with rfl | rfl
  · have hm := LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_five_of_alternating_five
      X ⟨e⟩
    exact ⟨.PSL, 2, 5, 1, Nat.prime_five, by norm_num, hm.1, Or.inl ⟨by decide, hm⟩⟩
  · have hm := LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_nine_of_alternating_six
      X ⟨e⟩
    exact ⟨.PSL, 2, 3, 2, Nat.prime_three, by norm_num, hm.1, Or.inl ⟨by decide, hm⟩⟩

theorem card_center_eq_two_of_alternating {Q : Type} [Group Q] [Finite Q] (hQ : IsQuasisimple Q)
    (hO : pPrimeCore 2 Q = ⊥) (hZ : center Q ≠ ⊥) {m : ℕ} (hm : 5 ≤ m)
    (e : Q ⧸ center Q ≃* alternatingGroup (Fin m)) : Nat.card (center Q) = 2 := by
  have : Group.IsPerfect Q := hQ.1
  let η : Q →* alternatingGroup (Fin m) := e.toMonoidHom.comp (QuotientGroup.mk' (center Q))
  have hη : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = center Q := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (center Q) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hle :=
    LocalAnalysis.ComponentInitial.alternating_perfect_central_two_kernel_order_at_most_two
      hm η hη hker.le (hker ▸ Sol78.center_isPGroup_two hO)
  rw [hker] at hle
  have hlt := (Subgroup.one_lt_card_iff_ne_bot _).mpr hZ
  omega

theorem typPumpInput_of_leaves (hS : TypPumpLeaf TypLeafSpor)
    (hE : TypPumpLeaf TypLeafEven) : TypPumpInput := by
  intro Y _ _ hK hY hZ β hβ T hTF hT hTZ hTC
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Yb := Y ⧸ pPrimeCore 2 Y with hYb
  have hYq : IsQuasisimple Yb := hY.2
  have hO : pPrimeCore 2 Yb = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have : IsSimpleGroup (Yb ⧸ center Yb) := hYq.2.1
  have hna : ∃ a b : Yb ⧸ center Yb, a * b ≠ b * a := hYq.2.2
  obtain ⟨eS⟩ := GrSLit.nonempty_quotient_center_equiv_fusionZStar Y
  have hcat : Blueprint.Catalog (Yb ⧸ center Yb) :=
    SectionRank.catalog_of_isKGroupCat_of_surjective hK ⊤
      (((QuotientGroup.mk' (center Yb)).comp (QuotientGroup.mk' (pPrimeCore 2 Y))).comp
        (⊤ : Subgroup Y).subtype)
      (((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)).comp
        fun y => ⟨⟨y, mem_top y⟩, rfl⟩)
  have oddS : Blueprint.OddLieType (Yb ⧸ center Yb) → TypC Y := fun ⟨t, n, p, f, hp, hp2, hadm,
      hm⟩ => Or.inl ⟨t, n, p, f, hp, hp2, hadm, Blueprint.LieModel.of_mulEquiv eS hm⟩
  have alt : ∀ m, Nonempty (Yb ⧸ center Yb ≃* alternatingGroup (Fin m)) → TypC Y := by
    rintro m ⟨e⟩
    have hm5 : 5 ≤ m := by
      by_contra hlt
      have hm4 : Nat.card (Fin m) ≤ 4 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fin]
        omega
      have : Group.IsSolvable (alternatingGroup (Fin m)) := alternatingGroup.isSolvable hm4
      have : Group.IsSolvable (Yb ⧸ center Yb) :=
        Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
      obtain ⟨a, b, hab⟩ := hna
      exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr this a b)
    rcases (by omega : m = 5 ∨ m = 6 ∨ 7 ≤ m) with h56 | h56 | h7
    · exact oddS (oddLieType_of_alternating_five_or_six (.inl h56) e)
    · exact oddS (oddLieType_of_alternating_five_or_six (.inr h56) e)
    · exact Or.inr (Or.inl ⟨m, h7, hYq, card_center_eq_two_of_alternating hYq hO hZ hm5 e, ⟨e⟩⟩)
  have leaf : ∀ P : ∀ (X : Type) [Group X], Prop, TypPumpLeaf P → P Yb → False := by
    intro P hP hPY
    obtain ⟨cbar, hc2, hTbF, hTbp, ⟨e⟩⟩ := exists_coreQuotient_fixed_component β hβ hTF hT
    exact hP Yb hYq hO hZ hPY cbar hc2 _ hTbF hTbp (center_ne_bot_of_mulEquiv e hTZ)
      (typC_of_coreEquiv e hTC)
  rcases (Milestones.ct_catalog_nonabelian_type_partition _ hna).mp hcat with
      ⟨m, -, he⟩ | hodd | heven | hspor
  · exact alt m he
  · exact oddS hodd
  · by_cases hodd : Blueprint.OddLieType (Yb ⧸ center Yb)
    · exact oddS hodd
    by_cases halt : ∃ m, Nonempty (Yb ⧸ center Yb ≃* alternatingGroup (Fin m))
    · obtain ⟨m, he⟩ := halt
      exact alt m he
    by_cases hL : GH74.GLS.IsL34Quotient Yb ∧ ¬ IsElementaryAbelian 2 ↥(center Yb)
    · exact Or.inr (Or.inr hL)
    exact (leaf TypLeafEven hE
      ⟨heven, hodd, fun m => ⟨fun e => halt ⟨m, ⟨e⟩⟩⟩, hL⟩).elim
  · exact (leaf TypLeafSpor hS hspor).elim

theorem typPumpInput_holds
    : TypPumpInput :=
  typPumpInput_of_leaves typPumpLeaf_spor_holds typPumpLeaf_even_holds

end CFSG.ComponentClassification.GS82PumpInputs
