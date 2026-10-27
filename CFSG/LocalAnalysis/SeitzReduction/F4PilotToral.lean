module

public import CFSG.LieType.Chevalley.ToralCentralizerQuotient
public import CFSG.LieType.Chevalley.LangWeylChamberStabilizers
public import CFSG.LieType.Chevalley.RootDiagonalTorusWords
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotRoots

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley RootSpace

local instance f4PilotToralNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

variable {K : Type} [Field K]

@[expose] def rDiag (c : Kˣ) : Fin (Tag.rank .F4) → Kˣ := Pi.mulSingle 0 c

theorem rootChar_rDiag (c : Kˣ) (v : Fin (Tag.rank .F4) → ℤ) :
    rootChar (rDiag c) v = c ^ v 0 := by
  rw [rootChar, Finset.prod_eq_single 0 (fun i _ hi => by
      rw [rDiag, Pi.mulSingle_eq_of_ne hi, one_zpow])
    (fun h => absurd (Finset.mem_univ 0) h), rDiag, Pi.mulSingle_eq_same]

theorem rDiag_eq (c : Kˣ) : rDiag c = ![c, 1, 1, 1] := by
  funext i
  fin_cases i <;> rfl

theorem rDiag_one : rDiag (1 : Kˣ) = 1 := Pi.mulSingle_one 0

theorem rDiag_mul (c d : Kˣ) : rDiag (c * d) = rDiag c * rDiag d := by
  unfold rDiag
  exact Pi.mulSingle_mul _ _ _

@[expose] def f4Vec (a b c d : ℤ) : Fin (Tag.rank .F4) → ℤ := ![a, b, c, d]

theorem eq_zero_of_zpow_eq_one_of_abs_le_two {G : Type*} [Group G] {c : G} (hc1 : c ≠ 1)
    (hc2 : c ^ 2 ≠ 1) {m : ℤ} (hm : |m| ≤ 2) (h : c ^ m = 1) : m = 0 := by
  rw [abs_le] at hm
  rcases (show m = -2 ∨ m = -1 ∨ m = 0 ∨ m = 1 ∨ m = 2 by omega) with rfl | rfl | rfl | rfl | rfl
  · exact absurd (by rw [zpow_neg, inv_eq_one] at h; exact_mod_cast h) hc2
  · exact absurd (by rw [zpow_neg, zpow_one, inv_eq_one] at h; exact h) hc1
  · rfl
  · exact absurd (by rw [zpow_one] at h; exact h) hc1
  · exact absurd (by exact_mod_cast h) hc2

theorem ne_one_and_sq_ne_one_of_three_le_orderOf {G : Type*} [Group G] {c : G}
    (hc : 3 ≤ orderOf c) : c ≠ 1 ∧ c ^ 2 ≠ 1 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, orderOf_one] at hc
    omega
  · have := orderOf_le_of_pow_eq_one (by norm_num) h
    omega

theorem exists_three_le_orderOf [Finite K] (hq : 4 ≤ Nat.card K) : ∃ c : Kˣ, 3 ≤ orderOf c := by
  obtain ⟨c, hc⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  refine ⟨c, ?_⟩
  rw [hc, Nat.card_units]
  omega

theorem exists_sq_eq_of_ringChar_eq_two [Finite K] (hK : ringChar K = 2) (t : Kˣ) :
    ∃ v : Kˣ, v ^ 2 = t := by
  have := Fintype.ofFinite K
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two hK (t : K)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact t.ne_zero (by rw [hs, mul_zero])
  exact ⟨Units.mk0 s hs0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hs, sq])⟩

theorem single_eq_sub_shortRoots :
    (Pi.single 0 1 : Fin (Tag.rank .F4) → ℤ) = f4Vec 1 1 1 0 - f4Vec 0 1 1 0 ∧
    (Pi.single 1 1 : Fin (Tag.rank .F4) → ℤ) = f4Vec 0 1 1 0 - f4Vec 0 0 1 0 ∧
    (Pi.single 2 1 : Fin (Tag.rank .F4) → ℤ) = f4Vec 0 0 1 0 ∧
    (Pi.single 3 1 : Fin (Tag.rank .F4) → ℤ) = f4Vec 0 0 0 1 :=
  ⟨List.ofFn_injective (by decide +kernel), List.ofFn_injective (by decide +kernel),
    List.ofFn_injective (by decide +kernel), List.ofFn_injective (by decide +kernel)⟩

theorem shortRoots_check : ∀ σ ∈ [f4Vec 1 1 1 0, f4Vec 0 1 1 0, f4Vec 0 0 1 0, f4Vec 0 0 0 1],
    σ ∈ rootFinset .F4 ∧ iform σ σ = 2 := by
  decide +kernel

section Kernel


theorem rootCharKernel_rDiag {c : Kˣ} (hc1 : c ≠ 1) (hc2 : c ^ 2 ≠ 1) :
    rootCharKernel (rDiag c) = C3Set := by
  ext γ
  change (IsRoot .F4 γ ∧ rootChar (rDiag c) γ = 1) ↔ γ ∈ C3Set
  rw [rootChar_rDiag, mem_C3Set_iff]
  refine and_congr_right fun hγ => ⟨fun h => ?_, fun h => by rw [h, zpow_zero]⟩
  exact eq_zero_of_zpow_eq_one_of_abs_le_two hc1 hc2 (abs_coeff_zero_le_two hγ) h

theorem C3Set_subset_rootCharKernel (c : Kˣ) : C3Set ⊆ rootCharKernel (rDiag c) := by
  intro γ hγ
  have h := C3Roots_check.1 γ hγ
  exact ⟨mem_rootFinset.1 h.1, by rw [rootChar_rDiag, h.2, zpow_zero]⟩

end Kernel

section Stabilizer


theorem iform_eq_zero_of_mem_C3Set {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ C3Set) :
    iform γ rootR = 0 ∧ iform γ (-rootR) = 0 := by
  have h := (mem_C3Roots_iff_iform.1 hγ).2
  rw [iform_comm] at h
  refine ⟨h, ?_⟩
  rw [show (-rootR : Fin (Tag.rank .F4) → ℤ) = (-1 : ℤ) • rootR by simp, iform_smul_right, h,
    mul_zero]

theorem not_isRoot_nsmul_add_nsmul_of_perp {γ δ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    (hδl : iform δ δ = 4) (h0 : iform γ δ = 0) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ¬IsRoot .F4 (a • γ + b • δ) := by
  intro h
  have h1 := iform_self_eq_two_or_four h
  have hγγ := iform_self_eq_two_or_four hγ
  have e : iform (a • γ + b • δ) (a • γ + b • δ) =
      (a : ℤ) ^ 2 * iform γ γ + (b : ℤ) ^ 2 * iform δ δ := by
    rw [← natCast_zsmul γ a, ← natCast_zsmul δ b]
    simp only [iform_add_left, iform_add_right, iform_smul_left, iform_smul_right, h0,
      iform_comm δ γ]
    ring
  rw [e, hδl] at h1
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  rcases hγγ with h2 | h2 <;> rw [h2] at h1 <;> rcases h1 with h1 | h1 <;> nlinarith

theorem smul_eq_self_of_iform_smul_single {τ : Tag} {w : WeylGroup τ} {l : Fin τ.rank → ℤ}
    (h : ∀ j : Fin τ.rank, iform l (w • Pi.single j 1) = iform l (Pi.single j 1)) :
    w • l = l := by
  set X := w⁻¹ • l - l with hX
  have hXj : ∀ j, iform X (Pi.single j 1) = 0 := by
    intro j
    have h2 : iform l (w • Pi.single j 1) = iform (w⁻¹ • l) (Pi.single j 1) := by
      rw [← iform_smul w⁻¹ l (w • Pi.single j 1), inv_smul_smul]
    rw [hX, iform_sub_left, ← h2, h j, sub_self]
  have hX0 : X = 0 := by
    by_contra hne
    have hpos := iform_self_pos hne
    rw [iform_eq_sum_mul_iform_single X X] at hpos
    simp only [hXj, mul_zero, Finset.sum_const_zero] at hpos
    exact lt_irrefl _ hpos
  have : w⁻¹ • l = l := sub_eq_zero.1 hX0
  calc w • l = w • (w⁻¹ • l) := by rw [this]
    _ = l := smul_inv_smul w _

theorem rootCharStabilizer_rDiag_le {c : Kˣ} (hc1 : c ≠ 1) (hc2 : c ^ 2 ≠ 1) :
    rootCharStabilizerSubgroup (rDiag c) ≤ kernelReflectionGroup (rDiag c) := by
  intro w hw
  have hw' : ∀ v, rootChar (rDiag c) (w • v) = rootChar (rDiag c) v := hw
  have hshort : ∀ σ, IsRoot .F4 σ → iform σ σ = 2 → (w • σ) 0 = σ 0 := by
    intro σ hσ hs
    have h := hw' σ
    rw [rootChar_rDiag, rootChar_rDiag] at h
    have b1 := abs_coeff_zero_le_one_of_short (IsRoot.smul hσ w) (by rw [iform_smul, hs])
    have b2 := abs_coeff_zero_le_one_of_short hσ hs
    have h3 : c ^ ((w • σ) 0 - σ 0) = 1 := by rw [zpow_sub, h, mul_inv_cancel]
    rw [abs_le] at b1 b2
    have := eq_zero_of_zpow_eq_one_of_abs_le_two hc1 hc2 (by rw [abs_le]; omega) h3
    omega
  have hs : ∀ σ ∈ [f4Vec 1 1 1 0, f4Vec 0 1 1 0, f4Vec 0 0 1 0, f4Vec 0 0 0 1],
      (w • σ) 0 = σ 0 := fun σ hσ =>
    hshort σ (mem_rootFinset.1 (shortRoots_check σ hσ).1) (shortRoots_check σ hσ).2
  obtain ⟨e0, e1, e2, e3⟩ := single_eq_sub_shortRoots
  have hj : ∀ j : Fin (Tag.rank .F4), (w • (Pi.single j 1 : Fin (Tag.rank .F4) → ℤ)) 0 =
      (Pi.single j 1 : Fin (Tag.rank .F4) → ℤ) 0 := by
    intro j
    fin_cases j
    · change (w • (Pi.single 0 1 : Fin (Tag.rank .F4) → ℤ)) 0 =
        (Pi.single 0 1 : Fin (Tag.rank .F4) → ℤ) 0
      rw [e0, smul_sub, Pi.sub_apply, Pi.sub_apply, hs _ (by simp), hs _ (by simp)]
    · change (w • (Pi.single 1 1 : Fin (Tag.rank .F4) → ℤ)) 0 =
        (Pi.single 1 1 : Fin (Tag.rank .F4) → ℤ) 0
      rw [e1, smul_sub, Pi.sub_apply, Pi.sub_apply, hs _ (by simp), hs _ (by simp)]
    · change (w • (Pi.single 2 1 : Fin (Tag.rank .F4) → ℤ)) 0 =
        (Pi.single 2 1 : Fin (Tag.rank .F4) → ℤ) 0
      rw [e2, hs _ (by simp)]
    · change (w • (Pi.single 3 1 : Fin (Tag.rank .F4) → ℤ)) 0 =
        (Pi.single 3 1 : Fin (Tag.rank .F4) → ℤ) 0
      rw [e3, hs _ (by simp)]
  have hwr : w • rootR = rootR :=
    smul_eq_self_of_iform_smul_single fun j => by rw [iform_rootR, iform_rootR, hj j]
  have hstab : w ∈ weylStabilizer .F4 (ofLattice rootR) := by
    change weylAct .F4 w (ofLattice rootR) = ofLattice rootR
    rw [weylAct_ofLattice, hwr]
  obtain ⟨cc, hcc, hform⟩ := (exceptional_Lang_Weyl_chamber_point_stabilizers .F4).1
  rw [(exceptional_Lang_Weyl_chamber_point_stabilizers .F4).2.2.2.2.2 (ofLattice rootR)] at hstab
  refine (Subgroup.closure_le _).2 ?_ hstab
  rintro _ ⟨α, hα, hinner, rfl⟩
  have hiform : ((iform α rootR : ℤ) : ℝ) =
      ∑ i, ∑ j, (ofLattice α) i * ((Tag.F4.symmetrizedCartan i j : ℤ) : ℝ) *
        (ofLattice rootR) j := by
    simp only [ofLattice_apply, iform, Int.cast_sum, Int.cast_mul]
  rw [hform, ← hiform] at hinner
  have h0 : iform α rootR = 0 := by
    have : ((iform α rootR : ℤ) : ℝ) = 0 := by
      rcases mul_eq_zero.1 hinner with h | h
      · exact absurd h hcc.ne'
      · exact h
    exact_mod_cast this
  have hker : α ∈ rootCharKernel (rDiag c) := by
    rw [rootCharKernel_rDiag hc1 hc2]
    exact mem_C3Roots_iff_iform.2 ⟨hα, by rw [iform_comm]; exact h0⟩
  obtain ⟨u, j, huj⟩ := isRoot_iff_exists_smul_single.1 hα
  rw [rootReflection_eq_conj huj]
  exact Subgroup.subset_closure ⟨u, j, huj ▸ hker, rfl⟩

end Stabilizer

variable (K) in
@[expose] noncomputable def torusLineR : Subgroup (ModGL .F4 K) :=
  ((rootDiagUnitHom .F4 K).comp (MonoidHom.mulSingle (fun _ : Fin (Tag.rank .F4) => Kˣ) 0)).range

theorem mem_torusLineR {g : ModGL .F4 K} :
    g ∈ torusLineR K ↔ ∃ c : Kˣ, rootDiagUnit .F4 (rDiag c) = g :=
  MonoidHom.mem_range

section Torus


theorem f4RootDiagUnit_mem_torusGroup (b : Fin (Tag.rank .F4) → Kˣ) :
    rootDiagUnit .F4 b ∈ torusGroup .F4 K := by
  obtain ⟨⟨B, hB, -⟩, hdiag⟩ := G2_F4_root_character_diagonals_inner .F4 (Or.inr rfl) K
  exact (hdiag B hB b).2.1

theorem torusLineR_le_torusGroup : torusLineR K ≤ torusGroup .F4 K := by
  rintro _ ⟨c, rfl⟩
  exact f4RootDiagUnit_mem_torusGroup _

theorem rootSubgroup_le_rootSpan_C3Set {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ C3Set) :
    rootSubgroup .F4 K γ ≤ rootSpan .F4 K C3Set :=
  le_iSup₂_of_le (f := fun δ (_ : δ ∈ C3Set) => rootSubgroup .F4 K δ) γ hγ le_rfl

theorem torusElt_mem_rootSpan_C3Set {i : Fin (Tag.rank .F4)} (hi : i ≠ 0) (u : Kˣ) :
    torusElt .F4 K i u ∈ rootSpan .F4 K C3Set := by
  have hpos : (Pi.single i 1 : Fin (Tag.rank .F4) → ℤ) ∈ C3Set :=
    mem_C3Set_iff.2 ⟨isRoot_single _ i, Pi.single_eq_of_ne (Ne.symm hi) _⟩
  have hneg : (-Pi.single i 1 : Fin (Tag.rank .F4) → ℤ) ∈ C3Set :=
    mem_C3Set_iff.2 ⟨IsRoot.neg (isRoot_single _ i), by
      rw [Pi.neg_apply, Pi.single_eq_of_ne (Ne.symm hi), neg_zero]⟩
  have hx : ∀ c : K, xUnit .F4 K i c ∈ rootSpan .F4 K C3Set := fun c =>
    rootSubgroup_le_rootSpan_C3Set hpos (xUnit_mem_rootSubgroup i c)
  have hy : ∀ c : K, yUnit .F4 K i c ∈ rootSpan .F4 K C3Set := fun c =>
    rootSubgroup_le_rootSpan_C3Set hneg (yUnit_mem_rootSubgroup i c)
  have hw : ∀ t : Kˣ, weylElt .F4 K i t ∈ rootSpan .F4 K C3Set := fun t => by
    rw [weylElt_eq_xUnit_mul]
    exact mul_mem (mul_mem (hx _) (hy _)) (hx _)
  have e : torusElt .F4 K i u = weylElt .F4 K i u * (weylElt .F4 K i 1)⁻¹ :=
    eq_mul_inv_of_mul_eq (weylElt_eq_torusElt_mul_weylElt_one i u).symm
  rw [e]
  exact mul_mem (hw u) (inv_mem (hw 1))

theorem torusElt_zero_sq_eq (v : Kˣ) :
    torusElt .F4 K 0 (v ^ 2) = rootDiagUnit .F4 (rDiag v) * torusElt .F4 K 1 (v ^ (-3 : ℤ)) *
      torusElt .F4 K 2 (v ^ (-2 : ℤ)) * torusElt .F4 K 3 (v ^ (-1 : ℤ)) := by
  simp only [torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
  congr 1
  funext j
  simp only [Pi.mul_apply]
  have hr : rDiag v j = v ^ (if j = 0 then (1 : ℤ) else 0) := by
    by_cases hj : j = 0
    · subst hj
      rw [rDiag, Pi.mulSingle_eq_same, ite_eq_left rfl, zpow_one]
    · rw [rDiag, Pi.mulSingle_eq_of_ne hj, ite_eq_right hj, zpow_zero]
  have hexp : ∀ j : Fin (Tag.rank .F4), 2 * Tag.cartan .F4 0 j = (if j = 0 then 1 else 0) +
      -3 * Tag.cartan .F4 1 j + -2 * Tag.cartan .F4 2 j + -1 * Tag.cartan .F4 3 j := by
    decide +kernel
  rw [hr, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_add, ← zpow_add,
    ← zpow_add]
  congr 1
  push_cast
  linear_combination hexp j

theorem torusGroup_le_torusLineR_sup (hsq : ∀ t : Kˣ, ∃ v : Kˣ, v ^ 2 = t) :
    torusGroup .F4 K ≤ torusLineR K ⊔ rootSpan .F4 K C3Set := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, u⟩, rfl⟩
  by_cases hi : i = 0
  · subst hi
    obtain ⟨v, rfl⟩ := hsq u
    change torusElt .F4 K 0 (v ^ 2) ∈ torusLineR K ⊔ rootSpan .F4 K C3Set
    rw [torusElt_zero_sq_eq]
    refine mul_mem (mul_mem (mul_mem (le_sup_left (a := torusLineR K) ⟨v, rfl⟩) ?_) ?_) ?_ <;>
      exact le_sup_right (a := torusLineR K) (torusElt_mem_rootSpan_C3Set (by decide) _)
  · exact le_sup_right (a := torusLineR K) (torusElt_mem_rootSpan_C3Set hi u)

end Torus

section Conj


theorem commute_of_mem_torusLineR_of_mem_rootSpan {x y : ModGL .F4 K} (hx : x ∈ torusLineR K)
    (hy : y ∈ rootSpan .F4 K C3Set) : Commute x y := by
  obtain ⟨c, rfl⟩ := mem_torusLineR.1 hx
  have h := rootSpan_le_centralizer (rDiag c) (C3Set_subset_rootCharKernel c) hy
  exact (Subgroup.mem_centralizer_singleton_iff.1 h).symm

theorem eq_one_of_commute_pinnedX_rootR (hK : ringChar K = 2) {c : Kˣ}
    (h : Commute (rootDiagUnit .F4 (rDiag c)) (pinnedX .F4 K rootR 1)) : c = 1 := by
  have hconj := rootDiagUnit_conj_pinnedX (rDiag c) isRoot_rootR (1 : K)
  rw [rootChar_rDiag, mul_one, h.eq, mul_inv_cancel_right] at hconj
  have h3 := pinnedX_injective .F4 K rootR hconj
  have hr0 : rootR 0 = 2 := rfl
  rw [hr0, Units.val_zpow_eq_zpow_val, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl,
    zpow_natCast] at h3
  have : CharP K 2 := ringChar.eq_iff.1 hK
  have h4 : (c : K) ^ 2 = 1 ^ 2 := by rw [← h3, one_pow]
  exact Units.ext (by rw [Units.val_one]; exact CharTwo.sq_inj.1 h4)

end Conj

section Full


theorem toralCentralizer_rDiag {c : Kˣ} (hc1 : c ≠ 1) (hc2 : c ^ 2 ≠ 1) :
    toralCentralizer .F4 K (rDiag c) = torusGroup .F4 K ⊔ rootSpan .F4 K C3Set := by
  obtain ⟨hMX, -, -, -, φ, hφ, -⟩ :=
    Chevalley_toral_centralizer_root_generated_quotient .F4 K (rDiag c)
  have hM : toralRootGroup .F4 K (rDiag c) = torusGroup .F4 K ⊔ rootSpan .F4 K C3Set := by
    rw [toralRootGroup, rootCharKernel_rDiag hc1 hc2]
  rw [← hM]
  refine le_antisymm (fun x hx => ?_) hMX
  obtain ⟨q, hq⟩ := hφ (QuotientGroup.mk ⟨x, hx⟩)
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
  have hw1 : (QuotientGroup.mk w : rootCharStabilizerSubgroup (rDiag c) ⧸
      (kernelReflectionGroup (rDiag c)).subgroupOf (rootCharStabilizerSubgroup (rDiag c))) = 1 :=
    (QuotientGroup.eq_one_iff w).2
      (Subgroup.mem_subgroupOf.2 (rootCharStabilizer_rDiag_le hc1 hc2 w.2))
  rw [hw1, map_one] at hq
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hq.symm)

theorem commute_of_iform_eq_zero_of_long {γ δ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    (hδ : IsRoot .F4 δ) (hδl : iform δ δ = 4) (h0 : iform γ δ = 0) {x y : ModGL .F4 K}
    (hx : x ∈ rootSubgroup .F4 K γ) (hy : y ∈ rootSubgroup .F4 K δ) : Commute x y := by
  have hne : γ ≠ δ := by
    rintro rfl
    rw [hδl] at h0
    exact absurd h0 (by norm_num)
  have hne' : γ ≠ -δ := by
    rintro rfl
    rw [show (-δ : Fin (Tag.rank .F4) → ℤ) = (-1 : ℤ) • δ by simp, iform_smul_left, hδl] at h0
    exact absurd h0 (by norm_num)
  obtain ⟨-, hmem, -, -, hF⟩ := root_commutator_formula .F4 hγ hδ hne hne'
  have hnil : commPairs .F4 γ δ = [] := List.eq_nil_iff_forall_not_mem.2 fun p hp =>
    not_isRoot_nsmul_add_nsmul_of_perp hγ hδl h0 ((hmem p).1 hp).1 ((hmem p).1 hp).2.1
      ((hmem p).1 hp).2.2
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hy
  have h1 := hF K c d
  rw [hnil, List.map_nil, List.prod_nil, ← pinnedX_neg, ← pinnedX_neg] at h1
  exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)

theorem rootSpan_C3Set_le_centralizer {δ : Fin (Tag.rank .F4) → ℤ} (hδ : IsRoot .F4 δ)
    (hδl : iform δ δ = 4) (hperp : ∀ γ ∈ C3Set, iform γ δ = 0) :
    rootSpan .F4 K C3Set ≤ Subgroup.centralizer (rootSubgroup .F4 K δ : Set (ModGL .F4 K)) := by
  refine iSup₂_le fun γ hγ x hx => Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  exact (commute_of_iform_eq_zero_of_long (mem_C3Set_iff.1 hγ).1 hδ hδl (hperp γ hγ) hx hy).eq.symm

theorem disjoint_torusLineR_rootSpan_C3 (hK : ringChar K = 2) :
    Disjoint (torusLineR K) (rootSpan .F4 K C3Set) := by
  rw [Subgroup.disjoint_def]
  intro g hgT hgD
  obtain ⟨c, rfl⟩ := mem_torusLineR.1 hgT
  have hc := rootSpan_C3Set_le_centralizer isRoot_rootR iform_rootR_rootS_values.1
    (fun γ hγ => (iform_eq_zero_of_mem_C3Set hγ).1) hgD
  have hcomm : Commute (rootDiagUnit .F4 (rDiag c)) (pinnedX .F4 K rootR 1) :=
    (Subgroup.mem_centralizer_iff.1 hc _ (mem_rootSubgroup.2 ⟨1, rfl⟩)).symm
  rw [eq_one_of_commute_pinnedX_rootR hK hcomm, rDiag_one, rootDiagUnit_one]

theorem toralCentralizer_rDiag_eq_sup [Finite K] (hK : ringChar K = 2) {c : Kˣ}
    (hc : 3 ≤ orderOf c) :
    toralCentralizer .F4 K (rDiag c) = torusLineR K ⊔ rootSpan .F4 K C3Set ∧
      Disjoint (torusLineR K) (rootSpan .F4 K C3Set) ∧
      ∀ x ∈ torusLineR K, ∀ y ∈ rootSpan .F4 K C3Set, Commute x y := by
  obtain ⟨hc1, hc2⟩ := ne_one_and_sq_ne_one_of_three_le_orderOf hc
  refine ⟨?_, disjoint_torusLineR_rootSpan_C3 hK,
    fun x hx y hy => commute_of_mem_torusLineR_of_mem_rootSpan hx hy⟩
  rw [toralCentralizer_rDiag hc1 hc2]
  exact le_antisymm
    (sup_le (torusGroup_le_torusLineR_sup (exists_sq_eq_of_ringChar_eq_two hK)) le_sup_right)
    (sup_le (torusLineR_le_torusGroup.trans le_sup_left) le_sup_right)

end Full

end CFSG.SeitzReduction.F4Pilot
