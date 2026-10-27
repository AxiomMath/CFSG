module

public import CFSG.CharacterTheory.OddOrderBasics.TypeIExtension
public import CFSG.CharacterTheory.OddOrderBasics.ClassAlgebra
public import CFSG.CharacterTheory.OddOrderBasics.Induction

public section

open scoped BigOperators Classical ComplexOrder

namespace CFSG.OddOrderBasics

open Wreathed TwoRankLowerBound.Helpers BlockSectionOrthogonality.Helpers

theorem blocksInnerProduct_eq_conj_swap {K : Type} [Group K] [Fintype K] (f g : K → ℂ) :
    BlocksInnerProduct f g = starRingEnd ℂ (BlocksInnerProduct g f) := by
  unfold BlocksInnerProduct
  rw [map_mul, map_sum, map_inv₀, Complex.conj_natCast]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

theorem abelian_inertia_multiplicity_free_induction {L : Type} [Group L] [Fintype L]
    (H E : Subgroup L) [H.Normal] (hHE : H.IsComplement' E)
    (hcop : (Nat.card H).Coprime (Nat.card E)) (θ : H → ℂ) (hθ : θ ∈ BlocksIrr H)
    (T : Subgroup L) (hTdef : T = E ⊓ characterInertiaSubgroup H θ) (hT : IsMulCommutative T)
    (I : Subgroup L) (hIdef : I = H ⊔ T) :
    ∃ B : Finset (L → ℂ), (∀ χ ∈ B, χ ∈ BlocksIrr L) ∧ B.card = Nat.card T ∧
      inducedFunction H θ = ∑ χ ∈ B, χ ∧ (∀ χ ∈ B, χ 1 = (I.index : ℂ) * θ 1) ∧
      ∀ ξ ∈ BlocksIrr L, BlocksInnerProduct (inducedFunction H θ) ξ = 0 ∨
        BlocksInnerProduct (inducedFunction H θ) ξ = 1 := by
  set J := characterInertiaSubgroup H θ with hJdef
  have hθclass : BlocksIsClassFunction θ := by
    obtain ⟨V, _, _, _, ρ, -, rfl⟩ := hθ
    exact fun g h => Representation.char_conj ρ g h
  have hHJ : H ≤ J := le_characterInertiaSubgroup H hθclass
  have hTJ : T ≤ J := hTdef ▸ inf_le_right
  have hTE : T ≤ E := hTdef ▸ inf_le_left
  have hJ : ∀ x ∈ J, ∃ h ∈ H, ∃ t ∈ T, h * t = x := by
    intro x hx
    obtain ⟨⟨h, e⟩, hhe⟩ := hHE.2 x
    have hhe' : (h : L) * e = x := hhe
    have he : (e : L) ∈ J := by
      have : (h : L)⁻¹ * x ∈ J := J.mul_mem (J.inv_mem (hHJ h.2)) hx
      rwa [← hhe', inv_mul_cancel_left] at this
    exact ⟨h, h.2, e, by rw [hTdef]; exact ⟨e.2, he⟩, hhe'⟩
  have hJI : J = I := by
    rw [hIdef]
    apply le_antisymm
    · intro x hx
      obtain ⟨h, hh, t, ht, rfl⟩ := hJ x hx
      exact Subgroup.mul_mem_sup hh ht
    · exact sup_le hHJ hTJ
  set H' := H.subgroupOf J with hH'def
  set T' := T.subgroupOf J with hT'def
  have hHT' : H'.IsComplement' T' := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxH hxT
      exact Subtype.ext (Subgroup.disjoint_def.mp hHE.disjoint hxH (hTE hxT))
    · ext x
      simp only [Set.mem_mul, Set.mem_univ, iff_true]
      obtain ⟨h, hh, t, ht, hht⟩ := hJ x x.2
      exact ⟨⟨h, hHJ hh⟩, hh, ⟨t, hTJ ht⟩, ht, Subtype.ext hht⟩
  have hT' : IsMulCommutative T' := ⟨⟨fun a b => by
    have h1 := congrArg Subtype.val (hT.is_comm.comm ⟨((a : J) : L), a.2⟩ ⟨((b : J) : L), b.2⟩)
    apply Subtype.ext
    apply Subtype.ext
    exact h1⟩⟩
  have hTcard : Nat.card T' = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTJ).toEquiv
  let θ' : H' → ℂ := fun x => θ ⟨((x : J) : L), x.2⟩
  have hθ' : θ' ∈ BlocksIrr H' := by
    obtain ⟨V, i₁, i₂, i₃, ρ, hirr, hρ⟩ := hθ
    let e : H' ≃* H := Subgroup.subgroupOfEquivOfLe hHJ
    refine ⟨V, i₁, i₂, i₃, ρ.comp e.toMonoidHom,
      LyonsUnitaryFour.isIrreducible_comp_surjective e.toMonoidHom e.surjective ρ hirr, ?_⟩
    funext x
    change ρ.character (e x) = θ' x
    rw [hρ]
    rfl
  have hinv' : ∀ t ∈ T', conjugateNormalCharacter H' θ' t = θ' := by
    intro t _
    funext x
    have h1 := congrFun ((mem_characterInertiaSubgroup_iff H θ (t : L)).mp t.2)
      ⟨((x : J) : L), x.2⟩
    rw [conjugateNormalCharacter_apply] at h1
    rw [conjugateNormalCharacter_apply]
    exact h1
  obtain ⟨d, hdpos, hd, hdvd, -⟩ := irreducible_character_degree_divides_order θ hθ
  have hd' : θ' 1 = d := hd
  have hcop' : d.Coprime (Nat.card T') := by
    rw [hTcard]
    exact Nat.Coprime.coprime_dvd_left hdvd
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hTE) hcop)
  obtain ⟨θe, hθe, hθeres⟩ :=
    coprime_abelian_action_character_extension H' T' hHT' hT' θ' hθ' hinv' hd' hcop'
  obtain ⟨V, _, _, _, ρ, -, hρchar⟩ := hθe
  have hρ : ∀ (x : J) (hx : (x : L) ∈ H), ρ.character x = θ ⟨x, hx⟩ := by
    intro x hx
    rw [hρchar]
    exact hθeres ⟨x, hx⟩
  have hquot : IsMulCommutative (InertiaQuotient H θ) := by
    refine Function.Surjective.isMulCommutative (f := (QuotientGroup.mk' H').comp T'.subtype)
      ?_ hT'
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H' q
    obtain ⟨⟨h, t⟩, hht⟩ := hHT'.2 x
    refine ⟨t, ?_⟩
    change (QuotientGroup.mk' H') (t : J) = QuotientGroup.mk' H' x
    rw [← hht]
    change ((t : J) : J ⧸ H') = (((h : J) * t : J) : J ⧸ H')
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (h : J)).mpr h.2, one_mul]
  obtain ⟨hfam, -, hiff, hresC, -⟩ := abelian_inertia_extension_induction_character_family H hθ ρ hρ
  set Θ := inertiaInducedCharacter H ρ with hΘdef
  have hpair : ∀ σ, BlocksInnerProduct (fun n : H => Θ σ n) θ = 1 := by
    intro σ
    obtain ⟨C₀, hC₀⟩ := exists_leftCoset_reps J
    obtain ⟨-, -, -, hmult⟩ := hresC C₀ hC₀
    obtain ⟨h₀, ⟨hh₀, hq₀⟩, -⟩ := hC₀ (1 : L)
    have hθh₀ : conjugateNormalCharacter H θ h₀ = θ := by
      have h1 := (conjugateNormalCharacter_eq_iff H θ h₀ 1).mpr hq₀
      rwa [conjugateNormalCharacter_one] at h1
    have h2 := hmult σ h₀ hh₀
    rwa [hθh₀] at h2
  have hmult : ∀ ξ ∈ BlocksIrr L, BlocksInnerProduct (inducedFunction H θ) ξ =
      if ∃ σ, ξ = Θ σ then 1 else 0 := by
    intro ξ hξ
    obtain ⟨W, _, _, _, τ, -, hτ⟩ := id hξ
    have hξclass : BlocksIsClassFunction ξ := by
      rw [← hτ]
      exact fun g h => Representation.char_conj τ g h
    obtain ⟨c, hc⟩ := exists_natCast_blocksInnerProduct_restrict τ H hθ
    have hc' : BlocksInnerProduct (fun n : H => ξ n) θ = c := by
      rw [← hτ]
      exact hc
    rw [blocksInnerProduct_inducedFunction_left H θ ξ hξclass, blocksInnerProduct_eq_conj_swap,
      hc', Complex.conj_natCast]
    split_ifs with hσ
    · obtain ⟨σ, rfl⟩ := hσ
      rw [← hc', hpair σ]
    · have hnpos : ¬ (0 < BlocksInnerProduct (fun n : H => ξ n) θ) :=
        fun hpos => hσ ((hiff ξ hξ).mp hpos)
      rw [hc'] at hnpos
      have hc0 : c = 0 := by
        by_contra hc0
        exact hnpos (by exact_mod_cast Nat.pos_of_ne_zero hc0)
      rw [hc0, Nat.cast_zero]
  set B := (irreducibles_finite L).toFinset.filter fun ξ => ∃ σ, ξ = Θ σ with hBdef
  have hirrB : ∀ χ ∈ B, χ ∈ BlocksIrr L := fun χ hχ =>
    (irreducibles_finite L).mem_toFinset.mp (Finset.mem_filter.mp hχ).1
  have hdegB : ∀ χ ∈ B, χ 1 = (J.index : ℂ) * θ 1 := by
    intro χ hχ
    obtain ⟨σ, rfl⟩ := (Finset.mem_filter.mp hχ).2
    exact (hfam σ).2
  have hsum : inducedFunction H θ = ∑ χ ∈ B, χ := by
    have hclass : BlocksIsClassFunction (inducedFunction H θ) := fun g h =>
      inducedFunction_conjugate H θ g h
    refine ((irreducible_character_basis L).2.2.2 _ hclass).trans ?_
    rw [hBdef, Finset.sum_filter]
    refine Finset.sum_congr rfl fun ξ hξ => ?_
    rw [hmult ξ ((irreducibles_finite L).mem_toFinset.mp hξ)]
    split_ifs <;> simp
  have hcard : B.card = Nat.card T := by
    have h1 := congrFun hsum 1
    rw [Finset.sum_apply, (induced_class_function_identities H).2.2.1 θ,
      Finset.sum_congr rfl hdegB, Finset.sum_const, nsmul_eq_mul] at h1
    have hidx : H.index = J.index * Nat.card T := by
      rw [← Subgroup.relIndex_mul_index hHJ, mul_comm, ← hTcard]
      congr 1
      exact hHT'.symm.index_eq_card
    have hθ1 : θ 1 ≠ 0 := by
      rw [hd]
      exact_mod_cast hdpos.ne'
    have hJ0 : (J.index : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
    rw [hidx, Nat.cast_mul] at h1
    have h2 : (Nat.card T : ℂ) * ((J.index : ℂ) * θ 1) =
        (B.card : ℂ) * ((J.index : ℂ) * θ 1) := by
      rw [← h1]
      ring
    exact_mod_cast (mul_right_cancel₀ (mul_ne_zero hJ0 hθ1) h2).symm
  refine ⟨B, hirrB, hcard, hsum, fun χ hχ => by rw [hdegB χ hχ, hJI], fun ξ hξ => ?_⟩
  rw [hmult ξ hξ]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

end CFSG.OddOrderBasics
