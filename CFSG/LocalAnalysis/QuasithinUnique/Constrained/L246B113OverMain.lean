module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverRank2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverSmall
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverA7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverOrders

public section

namespace CFSG.QuasithinUnique.Bridge.Over

open CFSG.Quasithin CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem overgroups_of_native
    (h : AsLieRank2FStar) {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hnat : SQTKCharTwoOrAltNative S)
    (h7 : ¬ Nonempty (S ≃* alternatingGroup (Fin 7))) : Overgroups S := by
  rcases hnat with ⟨n, hn5, hn8, ⟨e⟩⟩ | h5 | h7' | h9 | hu | (⟨f, hf⟩ | ht) | ⟨n, hn, hm⟩
  · have : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact overgroups_alt (Or.inl rfl) e
    · exact overgroups_alt (Or.inr (Or.inl rfl)) e
    · exact absurd ⟨e⟩ h7
    · exact overgroups_alt (Or.inr (Or.inr rfl)) e
  · exact overgroups_model_five h5
  · exact overgroups_model_seven h7'
  · exact overgroups_model_nine h9
  · exact overgroups_psu_three_three hu
  · rcases hf with ⟨hf2, hm⟩ | ⟨hf1, hm⟩ | ⟨hf2, hm⟩ | ⟨hf2, hm⟩ | ⟨hf2, hm⟩ | ⟨hf1, hm⟩ |
      ⟨hodd, hf3, hm⟩ | ⟨hodd, hf3, hm⟩
    · exact overgroups_isPSL_two hm
    · rcases Nat.eq_or_lt_of_le hf1 with rfl | hf2
      · exact overgroups_psl_three_two hm
      · exact h S hS (Or.inl ⟨f, Or.inl ⟨hf2, hm⟩⟩)
    · exact overgroups_isPSU_three hf2 hm
    · exact h S hS (Or.inl ⟨f, Or.inr (Or.inl ⟨hf2, hm⟩)⟩)
    · exact h S hS (Or.inl ⟨f, Or.inr (Or.inr (Or.inl ⟨hf2, hm⟩))⟩)
    · exact h S hS (Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inl ⟨hf1, hm⟩)))⟩)
    · exact h S hS (Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inr ⟨hodd, hf3, hm⟩)))⟩)
    · exact overgroups_isSz hm
  · exact h S hS (Or.inr (Or.inl ht))
  · rcases hn with rfl | rfl
    · exact overgroups_psl_four_two hm
    · exact h S hS (Or.inr (Or.inr hm))

theorem card_alt_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem isAlt_seven_of_lieAltType
    {L : Type} [Group L] [Finite L] (hLA : IsLieAltType L)
    (e : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 7)) : IsAlt 7 L := by
  have hS : Nat.card (L ⧸ Subgroup.center L) = 2520 := by
    rw [Nat.card_congr e.toEquiv, card_alt_seven]
  rcases hLA with hlie | ⟨m, hm⟩ | hhat
  · exfalso
    rcases (hlie.2 : EvenLieType _ ∨ IsPSU 3 3 1 _) with hE | hU
    · exact not_evenLieType_of_card hS hE
    · exact not_psu33_of_card hS hU
  ·
    obtain ⟨e'⟩ : Nonempty (L ≃* alternatingGroup (Fin m)) := hm
    have hcardL : Nat.card L = Nat.card (alternatingGroup (Fin m)) := Nat.card_congr e'.toEquiv
    have hdvd : Nat.card L = Nat.card (L ⧸ Subgroup.center L) * Nat.card (Subgroup.center L) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have hpos : 0 < Nat.card (Subgroup.center L) := Nat.card_pos
    have hge : 2520 ≤ Nat.card L := by
      rw [hdvd, hS]
      exact Nat.le_mul_of_pos_right _ hpos
    have hm5 : 5 ≤ m := by
      by_contra hlt
      have hle : Nat.card (alternatingGroup (Fin m)) ≤ Nat.factorial m := by
        have h1 : Nat.card (alternatingGroup (Fin m)) ≤ Nat.card (Equiv.Perm (Fin m)) :=
          Nat.card_le_card_of_injective _ (alternatingGroup (Fin m)).subtype_injective
        rwa [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin m)), Fintype.card_perm,
          Fintype.card_fin] at h1
      have h2 : Nat.factorial m ≤ Nat.factorial 4 := Nat.factorial_le (by omega)
      have h3 : Nat.factorial 4 = 24 := by decide
      omega
    have hsimple : IsSimpleGroup (alternatingGroup (Fin m)) := Bridge.alt_isSimple hm5
    have hsimpleL : IsSimpleGroup L := e'.isSimpleGroup
    obtain ⟨a, b, hab⟩ := Bridge.alt_exists_noncomm hm5
    have hcomm : ∃ x y : L, x * y ≠ y * x := ⟨e'.symm a, e'.symm b, fun h => hab (by
      apply e'.symm.injective
      rw [map_mul, map_mul, h])⟩
    have hZ : Subgroup.center L = ⊥ :=
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hcomm).2
    have hL2520 : Nat.card L = 2520 := by
      rw [hdvd, hS, hZ, Subgroup.card_bot, mul_one]
    have hA : Nat.card (alternatingGroup (Fin m)) = Nat.factorial m / 2 := by
      have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    have hm7 : m = 7 := by
      rw [hL2520, hA] at hcardL
      have h2 : 2 ∣ Nat.factorial m := Nat.dvd_factorial (by norm_num) (by omega)
      have hfac : Nat.factorial m = 5040 := by omega
      have h6 : 7 ≤ m := by
        by_contra hlt
        have : Nat.factorial m ≤ Nat.factorial 6 := Nat.factorial_le (by omega)
        have h3 : Nat.factorial 6 = 720 := by decide
        omega
      have h8 : m ≤ 7 := by
        by_contra hlt
        have : Nat.factorial 8 ≤ Nat.factorial m := Nat.factorial_le (by omega)
        have h3 : Nat.factorial 8 = 40320 := by decide
        omega
      omega
    subst hm7
    exact ⟨e'⟩
  ·
    exfalso
    obtain ⟨e'⟩ : Nonempty (L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 6)) := hhat.2.2
    have h6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    have h7 := Nat.card_congr e'.toEquiv
    omega

theorem asLieAltOvergroupsList_of
    (h : AsLieRank2FStar) : AsLieAltOvergroupsList := by
  intro Ω _ _ L T X K hLq hodd hLA hnat hT hTX hXL hXne hKX hsub hK hKc
  by_cases h7 : Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 7))
  · obtain ⟨e⟩ := h7
    obtain ⟨eL⟩ := isAlt_seven_of_lieAltType hLA e
    refine ⟨7, ⟨eL⟩, ?_⟩
    rcases A7.concl_of_alt7 eL hT hTX hXL hXne hKX hsub hK with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨h', rfl⟩
  · exact (false_of_overgroups hLq hodd hT hTX hXL hXne hKX hsub hK hKc
      (overgroups_of_native h hLq.2.1 hnat h7)).elim

end CFSG.QuasithinUnique.Bridge.Over
