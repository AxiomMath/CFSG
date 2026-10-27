module

public import CFSG.LieType.SeitzGeneration.SpBlockPlanes
public import CFSG.LieType.SeitzGeneration.SpHyperAnisoSplit
public import CFSG.LieType.SeitzGeneration.HyperEx
public import CFSG.LieType.SeitzGeneration.SpHyperScope
public import CFSG.RankThree.PartOne.CTP.SeitzLinear
public import CFSG.RankThree.PartOne.CTP.SeitzSpIndex

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock isSupp_longBlock coords mem_coords
  suppGroup suppGroup_mono longBlock_injective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open scoped MatrixGroups

variable {r : ℕ} {K : Type} [Field K]

private theorem natCard_SL_two_field (K : Type) [Field K] [Finite K] :
    Nat.card (SL(2, K)) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  let := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card K ^ 2 - Fintype.card K =
      Fintype.card K * (Fintype.card K - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem spEnd_mul_apply (g h : StatedSp r K) (v : Fin r ⊕ Fin r → K) :
    spEnd (g * h) v = spEnd g (spEnd h v) := by
  simp only [spEnd_apply, Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec]

private theorem spEnd_one_apply_aux (v : Fin r ⊕ Fin r → K) : spEnd (1 : StatedSp r K) v = v := by
  simp [spEnd_apply]

theorem single_mem_planeSub {k j : Fin r} (hkj : k ≠ j) :
    (Pi.single (Sum.inl k) 1 : Fin r ⊕ Fin r → K) ∈ planeSub (K := K) {i | i ≠ j} := by
  intro c hc
  have hcj : planeOf c = j := not_not.1 hc
  refine Pi.single_eq_of_ne (fun h => hkj ?_) _
  rw [h] at hcj
  exact hcj

theorem exists_block_cube (hr : 4 ≤ r) {p : ℕ} (hp : p.Prime) (A : SL(2, K))
    (hA : orderOf A = p) :
    ∃ E : Subgroup (StatedSp r K), IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
      ∀ g ∈ E, spEnd g (Pi.single (Sum.inl ⟨3, by omega⟩) 1) =
        Pi.single (Sum.inl ⟨3, by omega⟩) 1 := by
  let k₀ : Fin r := ⟨0, by omega⟩
  let k₁ : Fin r := ⟨1, by omega⟩
  let k₂ : Fin r := ⟨2, by omega⟩
  let k₃ : Fin r := ⟨3, by omega⟩
  have h01 : k₀ ≠ k₁ := fun h => by simpa [k₀, k₁] using congrArg Fin.val h
  have h02 : k₀ ≠ k₂ := fun h => by simpa [k₀, k₂] using congrArg Fin.val h
  have h12 : k₁ ≠ k₂ := fun h => by simpa [k₁, k₂] using congrArg Fin.val h
  have h30 : k₃ ≠ k₀ := fun h => by simpa [k₃, k₀] using congrArg Fin.val h
  have h31 : k₃ ≠ k₁ := fun h => by simpa [k₃, k₁] using congrArg Fin.val h
  have h32 : k₃ ≠ k₂ := fun h => by simpa [k₃, k₂] using congrArg Fin.val h
  set a : StatedSp r K := longBlock K r k₀ A with ha
  set b : StatedSp r K := longBlock K r k₁ A with hb
  set c : StatedSp r K := longBlock K r k₂ A with hc
  have hA1 : A ≠ 1 := fun h => by
    rw [h, orderOf_one] at hA
    exact hp.one_lt.ne hA
  have hb1 : b ≠ 1 := fun h => hA1 (longBlock_injective k₁ (by rw [map_one]; exact h))
  have hc1 : c ≠ 1 := fun h => hA1 (longBlock_injective k₂ (by rw [map_one]; exact h))
  have hab : Commute a b := commute_longBlock h01 A A
  have hac : Commute a c := commute_longBlock h02 A A
  have hbc : Commute b c := commute_longBlock h12 A A
  have hao : orderOf a = p := by
    rw [ha, orderOf_injective (longBlock K r k₀) (longBlock_injective k₀) A, hA]
  have hbo : orderOf b = p := by
    rw [hb, orderOf_injective (longBlock K r k₁) (longBlock_injective k₁) A, hA]
  have hco : orderOf c = p := by
    rw [hc, orderOf_injective (longBlock K r k₂) (longBlock_injective k₂) A, hA]
  have haS : a ∈ suppGroup (K := K) (coords k₀) := isSupp_longBlock k₀ A
  have hbS : b ∈ suppGroup (K := K) (coords k₁) := isSupp_longBlock k₁ A
  have hcS : c ∈ suppGroup (K := K) (coords k₂) := isSupp_longBlock k₂ A
  have hdisj01 : Disjoint (coords k₀) (coords k₁) := Set.disjoint_left.2 fun x h0 h1 => by
    rcases mem_coords.1 h0 with rfl | rfl <;> rcases mem_coords.1 h1 with h | h <;>
      first | exact h01 (Sum.inl_injective h) | exact h01 (Sum.inr_injective h) | cases h
  have hdisj2 : Disjoint (coords k₀ ∪ coords k₁) (coords k₂) := by
    refine Set.disjoint_union_left.2 ⟨Set.disjoint_left.2 fun x h0 h2 => ?_,
      Set.disjoint_left.2 fun x h1 h2 => ?_⟩
    · rcases mem_coords.1 h0 with rfl | rfl <;> rcases mem_coords.1 h2 with h | h <;>
        first | exact h02 (Sum.inl_injective h) | exact h02 (Sum.inr_injective h) | cases h
    · rcases mem_coords.1 h1 with rfl | rfl <;> rcases mem_coords.1 h2 with h | h <;>
        first | exact h12 (Sum.inl_injective h) | exact h12 (Sum.inr_injective h) | cases h
  have hind : b ∉ Subgroup.zpowers a := by
    intro hmem
    have h0 : b ∈ suppGroup (K := K) (coords k₀) := Subgroup.zpowers_le.2 haS hmem
    exact hb1 (eq_one_of_isSupp_disjoint hdisj01 h0 hbS)
  set F : Subgroup (StatedSp r K) := Subgroup.closure ({a, b} : Set (StatedSp r K)) with hF
  have hFcard : Nat.card F = p ^ 2 := card_closure_pair' hp hab hao hbo hind
  have hFS : F ≤ suppGroup (K := K) (coords k₀ ∪ coords k₁) := by
    rw [hF, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact suppGroup_mono Set.subset_union_left haS
    · exact suppGroup_mono Set.subset_union_right hbS
  have hdisj : Disjoint F (Subgroup.zpowers c) := by
    rw [Subgroup.disjoint_def]
    intro x hxF hxc
    exact eq_one_of_isSupp_disjoint hdisj2 (hFS hxF) (Subgroup.zpowers_le.2 hcS hxc)
  have hFc : F ≤ Subgroup.centralizer {c} := by
    rw [hF, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2 hac.eq
    · exact Subgroup.mem_centralizer_singleton_iff.2 hbc.eq
  have hnorm : Subgroup.zpowers c ≤ Subgroup.normalizer (F : Set (StatedSp r K)) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.1 (hFc hh)
  have hE : Subgroup.closure ({a, b, c} : Set (StatedSp r K)) = F ⊔ Subgroup.zpowers c := by
    rw [hF, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    tauto
  refine ⟨Subgroup.closure {a, b, c}, ?_, ?_, ?_⟩
  · refine isElemAbelian_closure_of_comm ?_ ?_
    · intro x hx y hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        first | exact Commute.refl _ | exact hab | exact hab.symm | exact hac | exact hac.symm |
          exact hbc | exact hbc.symm
    · intro x hx
      rcases hx with rfl | rfl | rfl
      · rw [← hao]
        exact pow_orderOf_eq_one _
      · rw [← hbo]
        exact pow_orderOf_eq_one _
      · rw [← hco]
        exact pow_orderOf_eq_one _
  · rw [hE, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
      hFcard, Nat.card_zpowers, hco]
    ring
  · intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl | rfl
      · exact spEnd_longBlock_of_mem k₀ A (single_mem_planeSub h30)
      · exact spEnd_longBlock_of_mem k₁ A (single_mem_planeSub h31)
      · exact spEnd_longBlock_of_mem k₂ A (single_mem_planeSub h32)
    | one => exact spEnd_one_apply_aux _
    | mul x y _ _ hx hy => rw [spEnd_mul_apply, hy, hx]
    | inv x _ hx =>
      calc spEnd x⁻¹ (Pi.single (Sum.inl k₃) 1) =
          spEnd x⁻¹ (spEnd x (Pi.single (Sum.inl k₃) 1)) := by rw [hx]
        _ = Pi.single (Sum.inl k₃) 1 := by
          rw [← spEnd_mul_apply, inv_mul_cancel, spEnd_one_apply_aux]

theorem seitzHyperLieEx_symplectic_twoThree :
    SeitzHyperLieEx fun d p _ => IsSymplecticIndex d.1 ∧ IsSpTwoThree d p := by
  rintro d p hp hp2 hpd hlist ⟨E₀, -, -, -, hp3, r, q, hq2, hqe, hBC⟩
  subst hp3
  obtain ⟨d, hv⟩ := d
  have hrange := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  rcases hBC with rfl | rfl
  · rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hrange
    have hcard2 : q.card = 2 := by rw [TauCeti.PrimePower.card_def, hq2, hqe]; norm_num
    have hr3 : 3 ≤ r := by
      rcases hrange with ⟨h2, hne⟩
      by_contra h
      exact hne ⟨by omega, hcard2⟩
    have hr5 : 5 ≤ r := by
      by_contra h
      apply hlist
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, q, hq2, hqe, ?_⟩))))
      rcases (by omega : r = 3 ∨ r = 4) with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    let K : Type := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)
    have : Finite K := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hq2 hr3
    have hK2 : Nat.card K = 2 := by
      rw [CFSG.RankThree.PartOne.CTP.card_fixedField_B r q hv, hq2, hqe]
      norm_num
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hSL : 3 ∣ Nat.card (SL(2, K)) := by
      rw [natCard_SL_two_field K, hK2]
      norm_num
    obtain ⟨A, hA⟩ := exists_prime_orderOf_dvd_card' (G := SL(2, K)) 3 hSL
    obtain ⟨Eh, hEh, hEhcard, hfix⟩ := exists_block_cube (r := r) (by omega) Nat.prime_three A hA
    have hinj : Function.Injective (proj r K) := (MonoidHom.ker_eq_bot_iff _).1
      (ker_proj_eq_bot_of_even (by omega) (by rw [hK2]))
    set v : Fin r ⊕ Fin r → K := Pi.single (Sum.inl ⟨3, by omega⟩) 1 with hv3
    set E : Subgroup (Cat ⟨.B r q, hv⟩) := (Eh.map (proj r K)).map e.symm.toMonoidHom with hEdef
    have hEe : E.map e.toMonoidHom = Eh.map (proj r K) := by
      rw [hEdef, Subgroup.map_map]
      have hid : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by
        ext x
        simp
      rw [hid, Subgroup.map_id]
    have hEab : IsElemAbelian 3 E :=
      CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3
        (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hEh _) _
    have hEcard : Nat.card E = 3 ^ 3 := by
      rw [hEdef, Subgroup.card_map_of_injective e.symm.injective,
        Subgroup.card_map_of_injective hinj, hEhcard]
    refine ⟨E, hEab, hEcard, seitzHyperLie_symplecticReducible ⟨.B r q, hv⟩ 3 hp hp2 hpd hlist E
      hEab hEcard ⟨r, K, inferInstance, inferInstance, e, ?_, by omega, K ∙ v, ?_, ?_, ?_⟩⟩
    · refine CFSG.RankThree.PartOne.CTP.natCast_ne_zero_of_not_dvd_card Nat.prime_three ?_
      rw [hK2]
      decide
    · rw [Ne, Submodule.span_singleton_eq_bot]
      intro h0
      have := congrFun h0 (Sum.inl ⟨3, by omega⟩)
      simp [hv3] at this
    · intro x hx y hy
      obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hx
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [LinearMap.map_smul₂, LinearMap.map_smul, spForm_isAlt v, smul_zero, smul_zero]
    · intro g hg w hw
      rw [hEe] at hg
      obtain ⟨gh, hgh, hghg⟩ := hg
      have hgeq : gh = g := hinj hghg
      subst hgeq
      obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hw
      rw [map_smul, hfix gh hgh]
      exact Submodule.smul_mem _ s (Submodule.mem_span_singleton_self v)
  · rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hrange
    exact absurd hq2 hrange.2

end CFSG.LieType.SeitzGeneration
