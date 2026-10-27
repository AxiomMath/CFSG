module

public import CFSG.CharacterTheory.Semidihedral.OddFieldSL2Degree
public import CFSG.CharacterTheory.OddOrderBasics.TypeIInduction
public import CFSG.CharacterTheory.Wreathed.OriginalSylowNormalizerWitness

public section

noncomputable section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.IndexTwoSL2Degree

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.OddFieldSL2Degree
  CFSG.Semidihedral.NormalInductionConstituent CFSG.Section1

theorem blocksInnerProduct_sum_left {G : Type} [Group G] [Fintype G] {ι : Type*} (s : Finset ι)
    (f : ι → G → ℂ) (g : G → ℂ) :
    BlocksInnerProduct (∑ i ∈ s, f i) g = ∑ i ∈ s, BlocksInnerProduct (f i) g := by
  simp only [BlocksInnerProduct, Finset.sum_apply, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem degree_dvd_card_complement {L : Type} [Group L] [Fintype L] (H E : Subgroup L)
    [H.Normal] (hHE : H.IsComplement' E) (hcop : (Nat.card H).Coprime (Nat.card E))
    [IsMulCommutative H] (hE : IsMulCommutative E) {η : L → ℂ} (hη : η ∈ BlocksIrr L) :
    ∃ k : ℕ, η 1 = k ∧ k ∣ Nat.card E := by
  obtain ⟨lam, hlam, hne⟩ : ∃ lam : H → ℂ, lam ∈ BlocksIrr H ∧
      BlocksInnerProduct (inducedFunction H lam) η ≠ 0 := by
    obtain ⟨V, _, _, _, ρ, -, rfl⟩ := id hη
    obtain ⟨-, ⟨m, hm, -⟩, hcoef⟩ :=
      complex_representation_character_decomposition (ρ.comp H.subtype)
    have hm0 : m ≠ 0 := by
      rintro rfl
      apply CFSG.DirectProduct.identity_ne_zero_of_mem hη
      have h1 : Representation.character (ρ.comp H.subtype) 1 = 0 := by
        rw [hm]
        simp
      exact h1
    obtain ⟨lam, hlamm⟩ := Finsupp.support_nonempty_iff.mpr hm0
    refine ⟨lam, lam.2, ?_⟩
    rw [blocksInnerProduct_inducedFunction_left H lam _
      (fun g h => Representation.char_conj ρ g h),
      CFSG.OddOrderBasics.blocksInnerProduct_eq_conj_swap]
    change starRingEnd ℂ (BlocksInnerProduct (Representation.character (ρ.comp H.subtype)) lam) ≠ 0
    rw [← hcoef m hm lam, Complex.conj_natCast]
    exact_mod_cast Finsupp.mem_support_iff.mp hlamm
  set T : Subgroup L := E ⊓ CFSG.Wreathed.characterInertiaSubgroup H lam with hT
  have hTcomm : IsMulCommutative T := ⟨⟨fun a b => by
    have h := congrArg Subtype.val (hE.is_comm.comm ⟨(a : L), a.2.1⟩ ⟨(b : L), b.2.1⟩)
    exact Subtype.ext h⟩⟩
  obtain ⟨B, hBirr, -, hind, hdeg, -⟩ :=
    CFSG.OddOrderBasics.abelian_inertia_multiplicity_free_induction H E hHE hcop lam hlam T hT
      hTcomm (H ⊔ T) rfl
  have hηB : η ∈ B := by
    by_contra hnot
    apply hne
    rw [hind, blocksInnerProduct_sum_left]
    apply Finset.sum_eq_zero
    intro χ hχ
    rw [CFSG.DirectProduct.blocksInnerProduct_of_mem (hBirr χ hχ) hη]
    simp [show χ ≠ η from fun h => hnot (h ▸ hχ)]
  have hlam1 : lam 1 = 1 := isIrreducibleCharacterOnGroup_degree_eq_one_of_commutative
    (isIrreducibleCharacterOnGroup_of_mem_blocksIrr hlam)
  refine ⟨(H ⊔ T).index, by rw [hdeg η hηB, hlam1, mul_one], ?_⟩
  rw [← hHE.symm.index_eq_card]
  exact Subgroup.index_dvd_of_le le_sup_left

theorem index_two_SL2_times_odd_abelian_by_abelian_group_has_no_four_characteristic_degree
    {F : Type} [Field F] [Fintype F] {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) {C : Type} [Group C] [Fintype C] (Y : Subgroup C) [Y.Normal]
    (hY : Y.index = 2) (J N : Subgroup C) (hJN : J ⊔ N = Y) (hdisj : Disjoint J N)
    (hcomm : ∀ j ∈ J, ∀ n ∈ N, j * n = n * j) (eJ : J ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hNodd : Odd (Nat.card N)) (U A : Subgroup C) (hUN : U ≤ N) (hAN : A ≤ N)
    (hUnorm : N ≤ Subgroup.normalizer (U : Set C)) (hUA : Disjoint U A) (hUAN : U ⊔ A = N)
    (hU : IsMulCommutative U) (hA : IsMulCommutative A)
    (hcop : Nat.Coprime (Nat.card U) (Nat.card A)) (hpA : ¬ p ∣ Nat.card A) :
    (∀ η ∈ BlocksIrr N, ∃ k : ℕ, η 1 = k ∧ k ∣ Nat.card A) ∧
    (∀ χ ∈ BlocksIrr C, ∃ θ ∈ BlocksIrr J, ∃ η ∈ BlocksIrr N, ∃ r : ℕ, (r = 1 ∨ r = 2) ∧
      χ 1 = r * θ 1 * η 1) ∧
    ∀ χ ∈ BlocksIrr C, ∀ n : ℕ, χ 1 = n → (4 ∣ n → ¬ p ∣ n) ∧ ¬ 4 * p ∣ n := by
  have : (U.subgroupOf N).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUN).mpr hUnorm
  have hHE : (U.subgroupOf N).IsComplement' (A.subgroupOf N) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxU hxA
      exact Subtype.ext (Subgroup.disjoint_def.mp hUA hxU hxA)
    · rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup hUN hAN, hUAN,
        Subgroup.subgroupOf_self, Subgroup.coe_top]
  have hcardU : Nat.card (U.subgroupOf N) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUN).toEquiv
  have hcardA : Nat.card (A.subgroupOf N) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
  have : IsMulCommutative (U.subgroupOf N) := ⟨⟨fun a b => by
    have h := congrArg Subtype.val (hU.is_comm.comm ⟨((a : N) : C), a.2⟩ ⟨((b : N) : C), b.2⟩)
    exact Subtype.ext (Subtype.ext h)⟩⟩
  have hAcomm : IsMulCommutative (A.subgroupOf N) := ⟨⟨fun a b => by
    have h := congrArg Subtype.val (hA.is_comm.comm ⟨((a : N) : C), a.2⟩ ⟨((b : N) : C), b.2⟩)
    exact Subtype.ext (Subtype.ext h)⟩⟩
  have hpart1 : ∀ η ∈ BlocksIrr N, ∃ k : ℕ, η 1 = k ∧ k ∣ Nat.card A := by
    intro η hη
    obtain ⟨k, hk, hkA⟩ := degree_dvd_card_complement (U.subgroupOf N) (A.subgroupOf N) hHE
      (by rw [hcardU, hcardA]; exact hcop) hAcomm hη
    exact ⟨k, hk, hcardA ▸ hkA⟩
  subst hJN
  have hcomm' : ∀ (x : J) (y : N), Commute (J.subtype x) (N.subtype y) :=
    fun x y => hcomm x x.2 y y.2
  let eY := CFSG.Wreathed.OriginalSylowNormalizerWitness.internalProductEquiv J N hcomm' hdisj
  have hfam := CFSG.DirectProduct.direct_product_irreducible_character_families J N
  have hpart2 : ∀ χ ∈ BlocksIrr C, ∃ θ ∈ BlocksIrr J, ∃ η ∈ BlocksIrr N, ∃ r : ℕ,
      (r = 1 ∨ r = 2) ∧ χ 1 = r * θ 1 * η 1 := by
    intro χ hχ
    obtain ⟨ζ, hζ, -, -, -, hdeg⟩ := index_two_irreducible_restriction (J ⊔ N) hY χ
      (isIrreducibleCharacterOnGroup_of_mem_blocksIrr hχ)
    obtain ⟨⟨θ, η⟩, ⟨hθ, hη⟩, hζeq⟩ := hfam.1.2.2
      (comp_mulEquiv_mem_blocksIrr eY (mem_blocksIrr_of_isIrreducibleCharacterOnGroup hζ))
    have hζ1 : ζ 1 = θ 1 * η 1 := by
      have h1 := congrFun hζeq 1
      simp only [Function.comp_apply, map_one] at h1
      rw [← h1]
      exact hfam.2.1 θ η
    refine ⟨θ, hθ, η, hη, ?_⟩
    rcases hdeg with h | h
    · refine ⟨1, Or.inl rfl, ?_⟩
      change χ 1 = ζ 1 at h
      rw [h, hζ1]
      push_cast
      ring
    · refine ⟨2, Or.inr rfl, ?_⟩
      change χ 1 = 2 * ζ 1 at h
      rw [h, hζ1]
      push_cast
      ring
  refine ⟨hpart1, hpart2, fun χ hχ n hn => ?_⟩
  obtain ⟨θ, hθ, η, hη, r, hr, hχ1⟩ := hpart2 χ hχ
  obtain ⟨t, -, hθt⟩ := CFSG.Wreathed.CentralSL2.blocksIrr_one_eq_natCast hθ
  obtain ⟨k, hηk, hkA⟩ := hpart1 η hη
  have hnrtk : n = r * t * k := by
    have h : ((n : ℕ) : ℂ) = ((r * t * k : ℕ) : ℂ) := by
      rw [← hn, hχ1, hθt, hηk]
      push_cast
      ring
    exact_mod_cast h
  have hkodd : Odd k := hNodd.of_dvd_nat (hkA.trans (Subgroup.card_dvd_of_le hAN))
  have hpk : ¬ p ∣ k := fun h => hpA (h.trans hkA)
  have hpr : ¬ p ∣ r := by
    rcases hr with rfl | rfl
    · exact hp.not_dvd_one
    · intro h
      have h1 := Nat.le_of_dvd two_pos h
      have h2 := hp.two_le
      obtain rfl : p = 2 := by omega
      exact absurd hpodd (by decide)
  obtain ⟨t', ht', -, -, -, h2p⟩ :=
    odd_field_SL2_irreducible_degree_is_not_divisible_by_two_times_characteristic hp hpodd hf
      hcard _ (comp_mulEquiv_mem_blocksIrr eJ.symm hθ)
  have htt' : t' = t := by
    have h : ((t' : ℕ) : ℂ) = (t : ℂ) := by
      rw [← ht', Function.comp_apply, map_one, hθt]
    exact_mod_cast h
  rw [htt'] at h2p
  have key : 4 ∣ n → ¬ p ∣ n := by
    intro h4 hpn
    rw [hnrtk] at h4 hpn
    have hpt : p ∣ t := by
      rcases (Nat.Prime.dvd_mul hp).mp hpn with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
        · exact absurd h' hpr
        · exact h'
      · exact absurd h hpk
    have hc4 : Nat.Coprime 4 k := by
      have h := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hkodd)
      norm_num at h
      exact h
    have h4' : 4 ∣ r * t := hc4.dvd_of_dvd_mul_right h4
    have h2t : 2 ∣ t := by
      rcases hr with rfl | rfl
      · obtain ⟨c, hc⟩ := h4'
        exact ⟨2 * c, by omega⟩
      · obtain ⟨c, hc⟩ := h4'
        exact ⟨c, by omega⟩
    exact h2p (Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.coprime_two_left.mpr hpodd) h2t hpt)
  exact ⟨key, fun h4p => key ((Dvd.intro p rfl).trans h4p) ((Dvd.intro_left 4 rfl).trans h4p)⟩

end CFSG.Semidihedral.IndexTwoSL2Degree
