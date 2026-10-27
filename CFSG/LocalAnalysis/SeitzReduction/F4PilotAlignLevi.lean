module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAlignLeviBruhat
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAmalgam
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotToralCentralizer

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore perfectCore_mono le_perfectCore_of_perfect)
open scoped commutatorElement

local instance f4PilotAlignLeviNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

variable {K : Type} [Field K]

section Char

variable {τ : Tag}

theorem rootChar_single_one (b : Fin τ.rank → Kˣ) (j : Fin τ.rank) :
    rootChar b (Pi.single j 1) = b j := by
  simpa using rootChar_nsmul_single b j 1

theorem rootChar_neg_eq_inv (b : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar b (-v) = (rootChar b v)⁻¹ := by
  rw [← zero_sub, rootChar_sub, rootChar_zero, one_mul]

theorem rootChar_mulSingle_apply (i : Fin τ.rank) (c : Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar (Pi.mulSingle i c) v = c ^ v i := by
  rw [rootChar, Finset.prod_eq_single i (fun j _ hj => by
      rw [Pi.mulSingle_eq_of_ne hj, one_zpow])
    (fun h => absurd (Finset.mem_univ i) h), Pi.mulSingle_eq_same]

end Char

@[expose] def leviTupleSet (A : Subgroup Kˣ) (J : Finset (Fin (Tag.rank .F4))) :
    Set (Fin (Tag.rank .F4) → Kˣ) :=
  {b | (∀ j ∈ J, b j = 1) ∧ ∀ i, b i ∈ A}

variable (K) in
@[expose] noncomputable def leviTorusOf (A : Subgroup Kˣ) (J : Finset (Fin (Tag.rank .F4))) :
    Subgroup (ModGL .F4 K) :=
  (Subgroup.pi Set.univ fun i => if i ∈ J then ⊥ else A).map (rootDiagUnitHom .F4 K)

theorem mem_leviTorusOf {A : Subgroup Kˣ} {J : Finset (Fin (Tag.rank .F4))} {g : ModGL .F4 K} :
    g ∈ leviTorusOf K A J ↔ ∃ b ∈ leviTupleSet A J, rootDiagUnit .F4 b = g := by
  simp only [leviTorusOf, mem_map, mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨b, ⟨fun j hj => ?_, fun i => ?_⟩, rfl⟩
    · have h := hb j
      split_ifs at h
      exact (mem_bot.1 h)
    · have h := hb i
      split_ifs at h with hi
      · rw [mem_bot] at h
        rw [h]
        exact one_mem A
      · exact h
  · rintro ⟨b, ⟨hb1, hbA⟩, rfl⟩
    refine ⟨b, fun i => ?_, rfl⟩
    split_ifs with hi
    · rw [mem_bot]
      exact hb1 i hi
    · exact hbA i

theorem rootDiagUnit_mem_leviTorusOf {A : Subgroup Kˣ} {J : Finset (Fin (Tag.rank .F4))}
    {b : Fin (Tag.rank .F4) → Kˣ} (hb : b ∈ leviTupleSet A J) :
    rootDiagUnit .F4 b ∈ leviTorusOf K A J :=
  mem_leviTorusOf.2 ⟨b, hb, rfl⟩

theorem leviTorusOf_mono {A A' : Subgroup Kˣ} (hA : A ≤ A') {J J' : Finset (Fin (Tag.rank .F4))}
    (hJ : J ⊆ J') : leviTorusOf K A J' ≤ leviTorusOf K A' J := by
  intro g hg
  obtain ⟨b, ⟨hb1, hbA⟩, rfl⟩ := mem_leviTorusOf.1 hg
  exact rootDiagUnit_mem_leviTorusOf ⟨fun j hj => hb1 j (hJ hj), fun i => hA (hbA i)⟩

theorem leviTorusOf_le_adjointGroup
    (A : Subgroup Kˣ) (J : Finset (Fin (Tag.rank .F4))) :
    leviTorusOf K A J ≤ adjointGroup .F4 K := by
  intro g hg
  obtain ⟨b, -, rfl⟩ := mem_leviTorusOf.1 hg
  exact f4RootDiagUnit_mem_adjointGroup b

theorem mulSingle_mem_leviTupleSet {A : Subgroup Kˣ} {J : Finset (Fin (Tag.rank .F4))}
    {i : Fin (Tag.rank .F4)} (hi : i ∉ J) {c : Kˣ} (hc : c ∈ A) :
    Pi.mulSingle i c ∈ leviTupleSet A J := by
  refine ⟨fun j hj => ?_, fun k => ?_⟩
  · have hji : j ≠ i := fun h => hi (h ▸ hj)
    exact Pi.mulSingle_eq_of_ne (M := fun _ => Kˣ) hji c
  by_cases hk : k = i
  · subst hk
    rw [Pi.mulSingle_eq_same]
    exact hc
  · rw [Pi.mulSingle_eq_of_ne hk]
    exact one_mem A

theorem exists_mem_orderOf_eq_natCard {A : Subgroup Kˣ} (hA : 3 ≤ Nat.card A) :
    ∃ c : Kˣ, c ∈ A ∧ orderOf c = Nat.card A := by
  have : Finite A := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := A)
  exact ⟨g, g.2, by rw [Subgroup.orderOf_coe, hg]⟩

theorem leviTorusOf_root_check : ∀ γ ∈ rootFinset .F4, (∀ i : Fin (Tag.rank .F4), |γ i| ≤ 4) ∧
    ∀ m ∈ ([3, 4] : List ℤ), ∀ J : Finset (Fin (Tag.rank .F4)), J.card ≤ 2 →
      (∀ i ∉ J, m ∣ γ i) → ∀ i ∉ J, γ i = 0 := by
  decide +kernel

theorem leviTorusOf_weyl_bound_check : ∀ β ∈ rootFinset .F4, ∀ i j : Fin (Tag.rank .F4),
    iform β β = iform (Pi.single j 1 : Fin (Tag.rank .F4) → ℤ) (Pi.single j 1) →
      |β i - (Pi.single j 1 : Fin (Tag.rank .F4) → ℤ) i| ≤ 4 := by
  decide +kernel

theorem iform_single_F4_values :
    iform (Pi.single 0 1 : Fin (Tag.rank .F4) → ℤ) (Pi.single 1 1) = -2 ∧
    iform (Pi.single 0 1 : Fin (Tag.rank .F4) → ℤ) (Pi.single 2 1) = 0 ∧
    iform (Pi.single 1 1 : Fin (Tag.rank .F4) → ℤ) (Pi.single 2 1) = -2 ∧
    iform (Pi.single 0 1 : Fin (Tag.rank .F4) → ℤ) (Pi.single 3 1) = 0 ∧
    iform (Pi.single 1 1 : Fin (Tag.rank .F4) → ℤ) (Pi.single 3 1) = 0 ∧
    iform (Pi.single 2 1 : Fin (Tag.rank .F4) → ℤ) (Pi.single 3 1) = -1 := by
  decide +kernel

theorem leviTorusOf_weyl_check : ∀ m ∈ ([3, 4] : List ℤ), ∀ J : Finset (Fin (Tag.rank .F4)),
    J.card ≤ 2 →
    ∀ b0 ∈ rootFinset .F4, (∀ i ∉ J, m ∣ b0 i - (Pi.single 0 1 : Fin (Tag.rank .F4) → ℤ) i) →
    ∀ b1 ∈ rootFinset .F4, (∀ i ∉ J, m ∣ b1 i - (Pi.single 1 1 : Fin (Tag.rank .F4) → ℤ) i) →
      iform b0 b1 = -2 →
    ∀ b2 ∈ rootFinset .F4, (∀ i ∉ J, m ∣ b2 i - (Pi.single 2 1 : Fin (Tag.rank .F4) → ℤ) i) →
      iform b0 b2 = 0 → iform b1 b2 = -2 →
    ∀ b3 ∈ rootFinset .F4, (∀ i ∉ J, m ∣ b3 i - (Pi.single 3 1 : Fin (Tag.rank .F4) → ℤ) i) →
      iform b0 b3 = 0 → iform b1 b3 = 0 → iform b2 b3 = -1 →
    ∀ i ∉ J, b0 i = (Pi.single 0 1 : Fin (Tag.rank .F4) → ℤ) i ∧
      b1 i = (Pi.single 1 1 : Fin (Tag.rank .F4) → ℤ) i ∧
      b2 i = (Pi.single 2 1 : Fin (Tag.rank .F4) → ℤ) i ∧
      b3 i = (Pi.single 3 1 : Fin (Tag.rank .F4) → ℤ) i := by
  decide +kernel

theorem coeff_eq_zero_of_mem_toralSetKernel_leviTupleSet
    {A : Subgroup Kˣ} (hA : 3 ≤ Nat.card A) {J : Finset (Fin (Tag.rank .F4))} (hJ : J.card ≤ 2)
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ toralSetKernel (leviTupleSet A J)) :
    ∀ i ∉ J, γ i = 0 := by
  obtain ⟨c, hcA, hc⟩ := exists_mem_orderOf_eq_natCard hA
  have hd : ∀ i ∉ J, ((Nat.card A : ℕ) : ℤ) ∣ γ i := by
    intro i hi
    have h1 := hγ.2 _ (mulSingle_mem_leviTupleSet hi hcA)
    rw [rootChar_mulSingle_apply, ← orderOf_dvd_iff_zpow_eq_one, hc] at h1
    exact h1
  obtain ⟨hb, hcheck⟩ := leviTorusOf_root_check γ (mem_rootFinset.2 hγ.1)
  have hm3 : (3 : ℤ) ≤ ((Nat.card A : ℕ) : ℤ) := by exact_mod_cast hA
  by_cases hm5 : (5 : ℤ) ≤ ((Nat.card A : ℕ) : ℤ)
  · intro i hi
    refine Int.eq_zero_of_abs_lt_dvd (hd i hi) ?_
    have := hb i
    omega
  · have hmem : ((Nat.card A : ℕ) : ℤ) ∈ ([3, 4] : List ℤ) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    exact hcheck _ hmem J hJ hd

theorem smul_apply_eq_of_forall_single {τ : Tag} {w : WeylGroup τ} {i : Fin τ.rank}
    (h : ∀ j, (w • (Pi.single j 1 : Fin τ.rank → ℤ)) i = (Pi.single j 1 : Fin τ.rank → ℤ) i)
    (v : Fin τ.rank → ℤ) : (w • v) i = v i := by
  have hv : v = ∑ j, v j • (Pi.single j 1 : Fin τ.rank → ℤ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have hw : w • v = ∑ j, v j • (w • (Pi.single j 1 : Fin τ.rank → ℤ)) := by
    conv_lhs => rw [hv]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => smul_comm w (v j) _
  rw [hw, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, h]
  conv_rhs => rw [hv, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]

theorem smul_apply_eq_of_mem_rootCharStabilizer_leviTupleSet
    {A : Subgroup Kˣ} (hA : 3 ≤ Nat.card A)
    {J : Finset (Fin (Tag.rank .F4))} (hJ : J.card ≤ 2) {w : WeylGroup .F4}
    (hw : ∀ b ∈ leviTupleSet A J, w ∈ rootCharStabilizer b) :
    ∀ v : Fin (Tag.rank .F4) → ℤ, ∀ i ∉ J, (w • v) i = v i := by
  obtain ⟨c, hcA, hc⟩ := exists_mem_orderOf_eq_natCard hA
  have hd : ∀ i ∉ J, ∀ v : Fin (Tag.rank .F4) → ℤ,
      ((Nat.card A : ℕ) : ℤ) ∣ (w • v) i - v i := by
    intro i hi v
    have h1 : rootChar (Pi.mulSingle i c) (w • v) = rootChar (Pi.mulSingle i c) v :=
      hw _ (mulSingle_mem_leviTupleSet hi hcA) v
    rw [rootChar_mulSingle_apply, rootChar_mulSingle_apply] at h1
    rw [← hc, orderOf_dvd_iff_zpow_eq_one, zpow_sub, h1, mul_inv_cancel]
  have hroot : ∀ j : Fin (Tag.rank .F4), w • (Pi.single j 1 : Fin (Tag.rank .F4) → ℤ) ∈
      rootFinset .F4 := fun j => mem_rootFinset.2 (IsRoot.smul (isRoot_single .F4 j) w)
  have hex : ∀ i ∉ J, ∀ j, (w • (Pi.single j 1 : Fin (Tag.rank .F4) → ℤ)) i =
      (Pi.single j 1 : Fin (Tag.rank .F4) → ℤ) i := by
    have hm3 : (3 : ℤ) ≤ ((Nat.card A : ℕ) : ℤ) := by exact_mod_cast hA
    by_cases hm5 : (5 : ℤ) ≤ ((Nat.card A : ℕ) : ℤ)
    · intro i hi j
      have hb := leviTorusOf_weyl_bound_check _ (hroot j) i j (iform_smul w _ _)
      exact sub_eq_zero.1 (Int.eq_zero_of_abs_lt_dvd (hd i hi _) (by omega))
    · have hmem : ((Nat.card A : ℕ) : ℤ) ∈ ([3, 4] : List ℤ) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        omega
      obtain ⟨g01, g02, g12, g03, g13, g23⟩ := iform_single_F4_values
      have h := leviTorusOf_weyl_check _ hmem J hJ _ (hroot 0) (fun i hi => hd i hi _) _ (hroot 1)
        (fun i hi => hd i hi _) ((iform_smul w _ _).trans g01) _ (hroot 2) (fun i hi => hd i hi _)
        ((iform_smul w _ _).trans g02) ((iform_smul w _ _).trans g12) _ (hroot 3)
        (fun i hi => hd i hi _) ((iform_smul w _ _).trans g03) ((iform_smul w _ _).trans g13)
        ((iform_smul w _ _).trans g23)
      intro i hi j
      obtain ⟨h0, h1, h2, h3⟩ := h i hi
      fin_cases j
      exacts [h0, h1, h2, h3]
  intro v i hi
  exact smul_apply_eq_of_forall_single (hex i hi) v

theorem amalgamRoots_eq_signedSimpleRoots (J : Finset (Fin (Tag.rank .F4))) :
    amalgamRoots J = signedSimpleRoots (J : Set (Fin (Tag.rank .F4))) :=
  rfl

section Perfect


variable {τ : Tag}

theorem rootSubgroup_le_commutator_of_rootChar_ne_one {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    {a : Fin τ.rank → Kˣ} (ha : rootChar a α ≠ 1) {R : Subgroup (ModGL τ K)}
    (hdR : rootDiagUnit τ a ∈ R) (hUR : rootSubgroup τ K α ≤ R) :
    rootSubgroup τ K α ≤ ⁅R, R⁆ := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  have hχ : (rootChar a α : K) - 1 ≠ 0 := fun h =>
    ha (Units.ext (by rw [Units.val_one]; exact sub_eq_zero.1 h))
  have hcomm : ⁅rootDiagUnit τ a, pinnedX τ K α (c / ((rootChar a α : K) - 1))⁆ =
      pinnedX τ K α c := by
    rw [commutatorElement_def, rootDiagUnit_conj_pinnedX a hα, pinnedX_neg, ← pinnedX_add]
    congr 1
    field_simp
    ring
  rw [SetLike.mem_coe, ← hcomm]
  exact Subgroup.commutator_mem_commutator hdR (hUR (Subgroup.subset_closure ⟨_, rfl⟩))

theorem commutator_rootPair_eq {t : Kˣ} (ht : t ^ 2 ≠ 1) (j : Fin τ.rank) :
    ⁅rootSubgroup τ K (Pi.single j 1) ⊔ rootSubgroup τ K (-Pi.single j 1),
        rootSubgroup τ K (Pi.single j 1) ⊔ rootSubgroup τ K (-Pi.single j 1)⁆ =
      rootSubgroup τ K (Pi.single j 1) ⊔ rootSubgroup τ K (-Pi.single j 1) := by
  set a : Fin τ.rank → Kˣ := fun k => t ^ τ.cartan j k
  have hd : rootDiagUnit τ a ∈
      rootSubgroup τ K (Pi.single j 1) ⊔ rootSubgroup τ K (-Pi.single j 1) := by
    rw [← torusElt_eq_rootDiagUnit]
    exact torusElt_mem_rootPair j t
  have haj : rootChar a (Pi.single j 1) = t ^ 2 := by
    rw [rootChar_single_one]
    change t ^ τ.cartan j j = t ^ 2
    rw [Tag.cartan_self]
    rfl
  refine le_antisymm (CFSG.Quasithin.A3.commutator_self_le _) (sup_le ?_ ?_)
  · refine rootSubgroup_le_commutator_of_rootChar_ne_one (isRoot_single τ j) ?_ hd le_sup_left
    rw [haj]
    exact ht
  · refine rootSubgroup_le_commutator_of_rootChar_ne_one (IsRoot.neg (isRoot_single τ j)) ?_ hd
      le_sup_right
    rw [rootChar_neg_eq_inv, haj]
    exact fun h => ht (inv_eq_one.1 h)

theorem commutator_rootSpan_signedSimpleRoots_eq {t : Kˣ} (ht : t ^ 2 ≠ 1)
    (J : Set (Fin τ.rank)) :
    ⁅rootSpan τ K (signedSimpleRoots J), rootSpan τ K (signedSimpleRoots J)⁆ =
      rootSpan τ K (signedSimpleRoots J) := by
  refine le_antisymm (CFSG.Quasithin.A3.commutator_self_le _) (iSup₂_le fun α hα => ?_)
  obtain ⟨j, hj, hαj⟩ := hα
  have hR : rootSubgroup τ K (Pi.single j 1) ⊔ rootSubgroup τ K (-Pi.single j 1) ≤
      rootSpan τ K (signedSimpleRoots J) := by
    refine sup_le ?_ ?_
    · exact le_iSup₂_of_le (f := fun β (_ : β ∈ signedSimpleRoots J) => rootSubgroup τ K β)
        (Pi.single j 1) ⟨j, hj, Or.inl rfl⟩ le_rfl
    · exact le_iSup₂_of_le (f := fun β (_ : β ∈ signedSimpleRoots J) => rootSubgroup τ K β)
        (-Pi.single j 1) ⟨j, hj, Or.inr rfl⟩ le_rfl
  have hα : rootSubgroup τ K α ≤
      rootSubgroup τ K (Pi.single j 1) ⊔ rootSubgroup τ K (-Pi.single j 1) := by
    rcases hαj with rfl | rfl
    exacts [le_sup_left, le_sup_right]
  rw [← commutator_rootPair_eq ht j] at hα
  exact hα.trans (Subgroup.commutator_mono hR hR)

theorem rootSpan_amalgamRoots_le_inf_centralizer_leviTorusOf (A : Subgroup Kˣ)
    (J : Finset (Fin (Tag.rank .F4))) :
    rootSpan .F4 K (amalgamRoots J) ≤
      adjointGroup .F4 K ⊓ centralizer (leviTorusOf K A J : Set (ModGL .F4 K)) := by
  refine le_inf (rootSpan_le_adjointGroup K _) fun x hx => mem_centralizer_iff.2 fun t ht => ?_
  obtain ⟨b, hb, rfl⟩ := mem_leviTorusOf.1 ht
  have hS : amalgamRoots J ⊆ rootCharKernel b := by
    rintro γ ⟨j, hj, rfl | rfl⟩
    · exact ⟨isRoot_single _ j, by rw [rootChar_single_one, hb.1 j hj]⟩
    · exact ⟨IsRoot.neg (isRoot_single _ j), by
        rw [rootChar_neg_eq_inv, rootChar_single_one, hb.1 j hj, inv_one]⟩
  exact (mem_centralizer_singleton_iff.1 (rootSpan_le_centralizer b hS hx)).symm

theorem commutator_rootSpan_amalgamRoots_eq {A : Subgroup Kˣ} (hA : 3 ≤ Nat.card A)
    (J : Finset (Fin (Tag.rank .F4))) :
    ⁅rootSpan .F4 K (amalgamRoots J), rootSpan .F4 K (amalgamRoots J)⁆ =
      rootSpan .F4 K (amalgamRoots J) := by
  obtain ⟨c, -, hc⟩ := exists_mem_orderOf_eq_natCard hA
  exact commutator_rootSpan_signedSimpleRoots_eq
    (ne_one_and_sq_ne_one_of_three_le_orderOf (hc ▸ hA)).2 _

theorem commutator_rootSpan_amalgamRoots_eq_of_four_le [Finite K] (hq : 4 ≤ Nat.card K)
    (J : Finset (Fin (Tag.rank .F4))) :
    ⁅rootSpan .F4 K (amalgamRoots J), rootSpan .F4 K (amalgamRoots J)⁆ =
      rootSpan .F4 K (amalgamRoots J) := by
  obtain ⟨c, hc⟩ := exists_three_le_orderOf hq
  exact commutator_rootSpan_signedSimpleRoots_eq (ne_one_and_sq_ne_one_of_three_le_orderOf hc).2 _

end Perfect

section Main


theorem perfectCore_le_rootSpan_amalgamRoots_of_le {A : Subgroup Kˣ} (hA : 3 ≤ Nat.card A)
    {J : Finset (Fin (Tag.rank .F4))} (hJ : J.card ≤ 2) {H : Subgroup (ModGL .F4 K)}
    (hH : H ≤ adjointGroup .F4 K ⊓ centralizer (leviTorusOf K A J : Set (ModGL .F4 K))) :
    perfectCore H ≤ rootSpan .F4 K (amalgamRoots J) := by
  refine perfectCore_le_rootSpan_of_forall_conj_eq (leviTupleSet A J)
    (J : Set (Fin (Tag.rank .F4)))
    (fun γ hγ _ => coeff_eq_zero_of_mem_toralSetKernel_leviTupleSet hA hJ hγ)
    (fun w hw => smul_apply_eq_of_mem_rootCharStabilizer_leviTupleSet hA hJ hw)
    fun g hg => ⟨(mem_inf.1 (hH hg)).1, fun b hb => ?_⟩
  have h := mem_centralizer_iff.1 (mem_inf.1 (hH hg)).2 _ (rootDiagUnit_mem_leviTorusOf hb)
  rw [h, mul_inv_cancel_right]

theorem perfectCore_inf_centralizer_leviTorusOf (A : Subgroup Kˣ) (hA : 3 ≤ Nat.card A)
    {J : Finset (Fin (Tag.rank .F4))} (hJ : J.card ≤ 2) :
    perfectCore (adjointGroup .F4 K ⊓ centralizer (leviTorusOf K A J : Set (ModGL .F4 K))) =
      rootSpan .F4 K (amalgamRoots J) :=
  le_antisymm (perfectCore_le_rootSpan_amalgamRoots_of_le hA hJ le_rfl)
    (le_perfectCore_of_perfect (rootSpan_amalgamRoots_le_inf_centralizer_leviTorusOf A J)
      (commutator_rootSpan_amalgamRoots_eq hA J))

theorem perfectCore_levi_inf_centralizer_leviTorusOf (A : Subgroup Kˣ) (hA : 3 ≤ Nat.card A)
    {J : Finset (Fin (Tag.rank .F4))} (hJ : J.card ≤ 2) (N : AmalgamNeighbour)
    (hJN : J ⊆ N.nodes) :
    perfectCore ((N.levi K).map (adjointGroup .F4 K).subtype ⊓
        centralizer (leviTorusOf K A J : Set (ModGL .F4 K))) =
      rootSpan .F4 K (amalgamRoots J) := by
  refine le_antisymm (perfectCore_le_rootSpan_amalgamRoots_of_le hA hJ
    (inf_le_inf_right _ (map_subtype_le _))) (le_perfectCore_of_perfect (le_inf ?_
      ((rootSpan_amalgamRoots_le_inf_centralizer_leviTorusOf A J).trans inf_le_right))
    (commutator_rootSpan_amalgamRoots_eq hA J))
  rw [← map_subtype_levi_f4Datum J]
  exact map_mono (levi_le_neighbourLevi hJN)

end Main

end CFSG.SeitzReduction.F4Pilot
