module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotRoots
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotToralCentralizer

public section

namespace CFSG.SeitzReduction.EPilot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley RootSpace

variable {τ : Tag} {K : Type} [Field K]

@[expose] def highDiag (τ : Tag) (c : Kˣ) : Fin τ.rank → Kˣ :=
  Pi.mulSingle (highNode τ) c

theorem rootChar_highDiag (c : Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar (highDiag τ c) v = c ^ v (highNode τ) := by
  rw [rootChar, Finset.prod_eq_single (highNode τ) (fun i _ hi => by
      rw [highDiag, Pi.mulSingle_eq_of_ne hi, one_zpow])
    (fun h => absurd (Finset.mem_univ _) h), highDiag, Pi.mulSingle_eq_same]

theorem highDiag_one : highDiag τ (1 : Kˣ) = 1 := Pi.mulSingle_one _

theorem highDiag_mul (c d : Kˣ) : highDiag τ (c * d) = highDiag τ c * highDiag τ d := by
  unfold highDiag
  exact Pi.mulSingle_mul _ _ _

theorem highDiag_apply (c : Kˣ) (l : Fin τ.rank) :
    highDiag τ c l = c ^ (if l = highNode τ then (1 : ℤ) else 0) := by
  by_cases hl : l = highNode τ
  · subst hl
    rw [highDiag, Pi.mulSingle_eq_same, ite_eq_left rfl, zpow_one]
  · rw [highDiag, Pi.mulSingle_eq_of_ne hl, ite_eq_right hl, zpow_zero]

section Kernel


theorem rootCharKernel_highDiag (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {c : Kˣ} (hc1 : c ≠ 1)
    (hc2 : c ^ 2 ≠ 1) : rootCharKernel (highDiag τ c) = perpRoots τ := by
  ext γ
  change (IsRoot τ γ ∧ rootChar (highDiag τ c) γ = 1) ↔ γ ∈ perpRoots τ
  rw [rootChar_highDiag, mem_perpRoots_iff]
  refine and_congr_right fun hγ => ⟨fun h => ?_, fun h => by rw [h, zpow_zero]⟩
  exact F4Pilot.eq_zero_of_zpow_eq_one_of_abs_le_two hc1 hc2 (abs_coeff_highNode_le_two hτ hγ) h

theorem perpRoots_subset_rootCharKernel (c : Kˣ) : perpRoots τ ⊆ rootCharKernel (highDiag τ c) :=
  fun _ hγ => ⟨hγ.1, by rw [rootChar_highDiag, hγ.2, zpow_zero]⟩

end Kernel

section Stabilizer


theorem rootCharStabilizer_highDiag_le (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {c : Kˣ} (hc1 : c ≠ 1)
    (hc2 : c ^ 2 ≠ 1) :
    rootCharStabilizerSubgroup (highDiag τ c) ≤ kernelReflectionGroup (highDiag τ c) := by
  intro w hw
  have hw' : ∀ v, rootChar (highDiag τ c) (w • v) = rootChar (highDiag τ c) v := hw
  have hcoeff : ∀ v : Fin τ.rank → ℤ, c ^ ((w • v) (highNode τ) - v (highNode τ)) = 1 := by
    intro v
    have h := hw' v
    rw [rootChar_highDiag, rootChar_highDiag] at h
    rw [zpow_sub, h, mul_inv_cancel]
  have hother : ∀ j : Fin τ.rank, j ≠ highNode τ →
      (w • (Pi.single j 1 : Fin τ.rank → ℤ)) (highNode τ) = 0 := by
    intro j hj
    have h1 := hcoeff (Pi.single j 1)
    rw [Pi.single_eq_of_ne (Ne.symm hj), sub_zero] at h1
    exact F4Pilot.eq_zero_of_zpow_eq_one_of_abs_le_two hc1 hc2
      (abs_coeff_highNode_le_two hτ (IsRoot.smul (isRoot_single τ j) w)) h1
  have hnode : (w • (Pi.single (highNode τ) 1 : Fin τ.rank → ℤ)) (highNode τ) = 1 := by
    have hroot := IsRoot.smul (isRoot_single τ (highNode τ)) w
    have hb := abs_le.1 (abs_coeff_highNode_le_two hτ hroot)
    have h1 := hcoeff (Pi.single (highNode τ) 1)
    rw [Pi.single_eq_same] at h1
    by_cases hk : (w • (Pi.single (highNode τ) 1 : Fin τ.rank → ℤ)) (highNode τ) = -2
    · exfalso
      have hneg := eq_neg_highRoot_of_coeff_highNode_eq_neg_two hτ hroot hk
      obtain ⟨i, hi⟩ := exists_iform_single_highNode hτ
      have hij : i ≠ highNode τ := by
        rintro rfl
        rw [iform_self_eq_two hτ (isRoot_single τ _)] at hi
        omega
      have e1 : iform (w • (Pi.single i 1 : Fin τ.rank → ℤ))
          (w • (Pi.single (highNode τ) 1 : Fin τ.rank → ℤ)) = -1 := by
        rw [iform_smul, hi]
      rw [hneg, ← neg_one_smul ℤ (highRoot τ), iform_smul_right, iform_comm, iform_highRoot hτ,
        hother i hij, mul_zero] at e1
      omega
    · have hb' : |(w • (Pi.single (highNode τ) 1 : Fin τ.rank → ℤ)) (highNode τ) - 1| ≤ 2 := by
        rw [abs_le]
        omega
      have := F4Pilot.eq_zero_of_zpow_eq_one_of_abs_le_two hc1 hc2 hb' h1
      omega
  have hall : ∀ j : Fin τ.rank,
      iform (highRoot τ) (w • Pi.single j 1) = iform (highRoot τ) (Pi.single j 1) := by
    intro j
    rw [iform_highRoot hτ, iform_highRoot hτ]
    by_cases hj : j = highNode τ
    · subst hj
      rw [hnode, Pi.single_eq_same]
    · rw [hother j hj, Pi.single_eq_of_ne (Ne.symm hj)]
  have hwθ : w • highRoot τ = highRoot τ := F4Pilot.smul_eq_self_of_iform_smul_single hall
  have hstab : w ∈ weylStabilizer τ (ofLattice (highRoot τ)) := by
    change weylAct τ w (ofLattice (highRoot τ)) = ofLattice (highRoot τ)
    rw [weylAct_ofLattice, hwθ]
  obtain ⟨cc, hcc, hform⟩ := (exceptional_Lang_Weyl_chamber_point_stabilizers τ).1
  rw [(exceptional_Lang_Weyl_chamber_point_stabilizers τ).2.2.2.2.2 (ofLattice (highRoot τ))]
    at hstab
  refine (Subgroup.closure_le _).2 ?_ hstab
  rintro _ ⟨α, hα, hinner, rfl⟩
  have hiform : ((iform α (highRoot τ) : ℤ) : ℝ) =
      ∑ i, ∑ j, (ofLattice α) i * ((τ.symmetrizedCartan i j : ℤ) : ℝ) *
        (ofLattice (highRoot τ)) j := by
    simp only [ofLattice_apply, iform, Int.cast_sum, Int.cast_mul]
  rw [hform, ← hiform] at hinner
  have h0 : iform α (highRoot τ) = 0 := by
    have : ((iform α (highRoot τ) : ℤ) : ℝ) = 0 := by
      rcases mul_eq_zero.1 hinner with h | h
      · exact absurd h hcc.ne'
      · exact h
    exact_mod_cast this
  have hker : α ∈ rootCharKernel (highDiag τ c) := by
    rw [rootCharKernel_highDiag hτ hc1 hc2]
    exact (mem_perpRoots_iff_iform hτ).2 ⟨hα, by rw [iform_comm]; exact h0⟩
  obtain ⟨u, j, huj⟩ := isRoot_iff_exists_smul_single.1 hα
  rw [rootReflection_eq_conj huj]
  exact Subgroup.subset_closure ⟨u, j, huj ▸ hker, rfl⟩

end Stabilizer

variable (τ K) in
@[expose] noncomputable def highTorusLine : Subgroup (ModGL τ K) :=
  ((rootDiagUnitHom τ K).comp
    (MonoidHom.mulSingle (fun _ : Fin τ.rank => Kˣ) (highNode τ))).range

theorem mem_highTorusLine {g : ModGL τ K} :
    g ∈ highTorusLine τ K ↔ ∃ c : Kˣ, rootDiagUnit τ (highDiag τ c) = g :=
  MonoidHom.mem_range

theorem rootDiagUnit_highDiag_mem_highTorusLine (c : Kˣ) :
    rootDiagUnit τ (highDiag τ c) ∈ highTorusLine τ K :=
  mem_highTorusLine.2 ⟨c, rfl⟩

theorem cartanChar_zpow (v : Kˣ) (n : Fin τ.rank → ℤ) :
    cartanChar (fun j => v ^ n j) = fun l => v ^ (∑ j, n j * τ.cartan j l) := by
  funext l
  simp only [cartanChar, ← zpow_mul]
  rw [Finset.prod_zpow_eq_zpow_sum]

theorem sum_neg_highRoot_mul_cartan (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (l : Fin τ.rank) :
    ∑ j, (if j = highNode τ then 0 else -highRoot τ j) * τ.cartan j l =
      2 * τ.cartan (highNode τ) l - if l = highNode τ then 1 else 0 := by
  rcases hτ with rfl | rfl | rfl <;> revert l <;> decide +kernel

section Torus


theorem rootDiagUnit_highDiag_eq_prod (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (v : Kˣ) :
    rootDiagUnit τ (highDiag τ v) =
      ((List.finRange τ.rank).map fun j => torusElt τ K j (v ^ highRoot τ j)).prod := by
  rw [list_prod_torusElt_eq_rootDiagUnit, cartanChar_zpow]
  congr 1
  funext l
  rw [sum_highRoot_mul_cartan hτ l, highDiag_apply]

theorem highTorusLine_le_torusGroup (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    highTorusLine τ K ≤ torusGroup τ K := by
  rintro _ ⟨v, rfl⟩
  change rootDiagUnit τ (highDiag τ v) ∈ torusGroup τ K
  rw [rootDiagUnit_highDiag_eq_prod hτ]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure ⟨(j, _), rfl⟩

theorem rootSubgroup_le_rootSpan_perpRoots {γ : Fin τ.rank → ℤ} (hγ : γ ∈ perpRoots τ) :
    rootSubgroup τ K γ ≤ rootSpan τ K (perpRoots τ) :=
  le_iSup₂_of_le (f := fun δ (_ : δ ∈ perpRoots τ) => rootSubgroup τ K δ) γ hγ le_rfl

theorem torusElt_mem_rootSpan_perpRoots {j : Fin τ.rank} (hj : j ≠ highNode τ) (u : Kˣ) :
    torusElt τ K j u ∈ rootSpan τ K (perpRoots τ) :=
  sup_le (rootSubgroup_le_rootSpan_perpRoots (single_mem_perpRoots hj))
    (rootSubgroup_le_rootSpan_perpRoots (neg_single_mem_perpRoots hj))
    (F4Pilot.torusElt_mem_rootPair j u)

theorem prod_torusElt_mem_rootSpan_perpRoots (v : Kˣ) {m : Fin τ.rank → ℤ}
    (hm : m (highNode τ) = 0) :
    ((List.finRange τ.rank).map fun j => torusElt τ K j (v ^ m j)).prod ∈
      rootSpan τ K (perpRoots τ) := by
  refine list_prod_mem fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  by_cases hj : j = highNode τ
  · subst hj
    rw [hm, zpow_zero, torusElt_eq_rootDiagUnit]
    simp only [one_zpow]
    rw [show (fun _ : Fin τ.rank => (1 : Kˣ)) = 1 from rfl, rootDiagUnit_one]
    exact one_mem _
  · exact torusElt_mem_rootSpan_perpRoots hj _

theorem torusElt_highNode_sq_eq (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (v : Kˣ) :
    torusElt τ K (highNode τ) (v ^ 2) = rootDiagUnit τ (highDiag τ v) *
      ((List.finRange τ.rank).map fun j =>
        torusElt τ K j (v ^ (if j = highNode τ then 0 else -highRoot τ j))).prod := by
  rw [list_prod_torusElt_eq_rootDiagUnit, cartanChar_zpow, torusElt_eq_rootDiagUnit,
    ← rootDiagUnit_mul]
  congr 1
  funext l
  rw [Pi.mul_apply, highDiag_apply, sum_neg_highRoot_mul_cartan hτ l, ← zpow_add,
    ← zpow_natCast, ← zpow_mul]
  congr 1
  push_cast
  ring

theorem torusGroup_le_highTorusLine_sup (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hsq : ∀ t : Kˣ, ∃ v : Kˣ, v ^ 2 = t) :
    torusGroup τ K ≤ highTorusLine τ K ⊔ rootSpan τ K (perpRoots τ) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨j, u⟩, rfl⟩
  by_cases hj : j = highNode τ
  · subst hj
    obtain ⟨v, rfl⟩ := hsq u
    change torusElt τ K (highNode τ) (v ^ 2) ∈ highTorusLine τ K ⊔ rootSpan τ K (perpRoots τ)
    rw [torusElt_highNode_sq_eq hτ]
    exact mul_mem (le_sup_left (a := highTorusLine τ K) (rootDiagUnit_highDiag_mem_highTorusLine v))
      (le_sup_right (a := highTorusLine τ K)
        (prod_torusElt_mem_rootSpan_perpRoots v (by rw [ite_eq_left rfl])))
  · exact le_sup_right (a := highTorusLine τ K) (torusElt_mem_rootSpan_perpRoots hj u)

end Torus

section Conj


theorem not_isRoot_nsmul_add_nsmul_of_iform_eq_zero (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hδ : IsRoot τ δ) (h0 : iform γ δ = 0) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) : ¬IsRoot τ (a • γ + b • δ) := by
  intro h
  have h1 := iform_self_eq_two hτ h
  have e : iform (a • γ + b • δ) (a • γ + b • δ) =
      (a : ℤ) ^ 2 * iform γ γ + (b : ℤ) ^ 2 * iform δ δ := by
    rw [← natCast_zsmul γ a, ← natCast_zsmul δ b]
    simp only [iform_add_left, iform_add_right, iform_smul_left, iform_smul_right, h0,
      iform_comm δ γ]
    ring
  rw [e, iform_self_eq_two hτ hγ, iform_self_eq_two hτ hδ] at h1
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  nlinarith

theorem commute_of_iform_eq_zero (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {γ δ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hδ : IsRoot τ δ) (h0 : iform γ δ = 0) {x y : ModGL τ K}
    (hx : x ∈ rootSubgroup τ K γ) (hy : y ∈ rootSubgroup τ K δ) : Commute x y := by
  have hne : γ ≠ δ := by
    rintro rfl
    rw [iform_self_eq_two hτ hγ] at h0
    exact absurd h0 (by norm_num)
  have hne' : γ ≠ -δ := by
    rintro rfl
    rw [← neg_one_smul ℤ δ, iform_smul_left, iform_self_eq_two hτ hδ] at h0
    exact absurd h0 (by norm_num)
  obtain ⟨-, hmem, -, -, hF⟩ := root_commutator_formula τ hγ hδ hne hne'
  have hnil : commPairs τ γ δ = [] := List.eq_nil_iff_forall_not_mem.2 fun p hp =>
    not_isRoot_nsmul_add_nsmul_of_iform_eq_zero hτ hγ hδ h0 ((hmem p).1 hp).1
      ((hmem p).1 hp).2.1 ((hmem p).1 hp).2.2
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hy
  have h1 := hF K c d
  rw [hnil, List.map_nil, List.prod_nil, ← pinnedX_neg, ← pinnedX_neg] at h1
  exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)

theorem rootSpan_perpRoots_le_centralizer (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) (hperp : ∀ γ ∈ perpRoots τ, iform γ δ = 0) :
    rootSpan τ K (perpRoots τ) ≤
      Subgroup.centralizer (rootSubgroup τ K δ : Set (ModGL τ K)) := by
  refine iSup₂_le fun γ hγ x hx => Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  exact (commute_of_iform_eq_zero hτ hγ.1 hδ (hperp γ hγ) hx hy).eq.symm

theorem rootSpan_perpRoots_le_centralizer_highRootSL2 (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    rootSpan τ K (perpRoots τ) ≤
      Subgroup.centralizer (highRootSL2 τ K : Set (ModGL τ K)) := by
  intro x hx
  rw [highRootSL2, Subgroup.mem_centralizer_iff]
  have hxS : highRootSL2 τ K ≤ Subgroup.centralizer ({x} : Set (ModGL τ K)) := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · have h := rootSpan_perpRoots_le_centralizer hτ (isRoot_highRoot τ)
        (fun γ hγ => (iform_eq_zero_of_mem_perpRoots hτ hγ).1) hx
      exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 h y hy)
    · have h := rootSpan_perpRoots_le_centralizer hτ (IsRoot.neg (isRoot_highRoot τ))
        (fun γ hγ => (iform_eq_zero_of_mem_perpRoots hτ hγ).2) hx
      exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 h y hy)
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.1 (hxS hy)

theorem commute_of_mem_highTorusLine_of_mem_rootSpan {x y : ModGL τ K}
    (hx : x ∈ highTorusLine τ K) (hy : y ∈ rootSpan τ K (perpRoots τ)) : Commute x y := by
  obtain ⟨c, rfl⟩ := mem_highTorusLine.1 hx
  have h := rootSpan_le_centralizer (highDiag τ c) (perpRoots_subset_rootCharKernel c) hy
  exact (Subgroup.mem_centralizer_singleton_iff.1 h).symm

theorem eq_one_of_commute_pinnedX_highRoot (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hK : ringChar K = 2) {c : Kˣ}
    (h : Commute (rootDiagUnit τ (highDiag τ c)) (pinnedX τ K (highRoot τ) 1)) : c = 1 := by
  have hconj := rootDiagUnit_conj_pinnedX (highDiag τ c) (isRoot_highRoot τ) (1 : K)
  rw [rootChar_highDiag, mul_one, h.eq, mul_inv_cancel_right] at hconj
  have h3 := pinnedX_injective τ K (highRoot τ) hconj
  rw [highRoot_highNode hτ, Units.val_zpow_eq_zpow_val, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl,
    zpow_natCast] at h3
  have : CharP K 2 := ringChar.eq_iff.1 hK
  have h4 : (c : K) ^ 2 = 1 ^ 2 := by rw [← h3, one_pow]
  exact Units.ext (by rw [Units.val_one]; exact CharTwo.sq_inj.1 h4)

theorem disjoint_highTorusLine_rootSpan (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hK : ringChar K = 2) : Disjoint (highTorusLine τ K) (rootSpan τ K (perpRoots τ)) := by
  rw [Subgroup.disjoint_def]
  intro g hgT hgD
  obtain ⟨c, rfl⟩ := mem_highTorusLine.1 hgT
  have hc := rootSpan_perpRoots_le_centralizer hτ (isRoot_highRoot τ)
    (fun γ hγ => (iform_eq_zero_of_mem_perpRoots hτ hγ).1) hgD
  have hcomm : Commute (rootDiagUnit τ (highDiag τ c)) (pinnedX τ K (highRoot τ) 1) :=
    (Subgroup.mem_centralizer_iff.1 hc _ (mem_rootSubgroup.2 ⟨1, rfl⟩)).symm
  rw [eq_one_of_commute_pinnedX_highRoot hτ hK hcomm, highDiag_one, rootDiagUnit_one]

end Conj

section Full


theorem toralCentralizer_highDiag (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {c : Kˣ} (hc1 : c ≠ 1)
    (hc2 : c ^ 2 ≠ 1) :
    toralCentralizer τ K (highDiag τ c) = torusGroup τ K ⊔ rootSpan τ K (perpRoots τ) := by
  obtain ⟨hMX, -, -, -, φ, hφ, -⟩ :=
    Chevalley_toral_centralizer_root_generated_quotient τ K (highDiag τ c)
  have hM : toralRootGroup τ K (highDiag τ c) = torusGroup τ K ⊔ rootSpan τ K (perpRoots τ) := by
    rw [toralRootGroup, rootCharKernel_highDiag hτ hc1 hc2]
  rw [← hM]
  refine le_antisymm (fun x hx => ?_) hMX
  obtain ⟨q, hq⟩ := hφ (QuotientGroup.mk ⟨x, hx⟩)
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
  have hw1 : (QuotientGroup.mk w : rootCharStabilizerSubgroup (highDiag τ c) ⧸
      (kernelReflectionGroup (highDiag τ c)).subgroupOf
        (rootCharStabilizerSubgroup (highDiag τ c))) = 1 :=
    (QuotientGroup.eq_one_iff w).2
      (Subgroup.mem_subgroupOf.2 (rootCharStabilizer_highDiag_le hτ hc1 hc2 w.2))
  rw [hw1, map_one] at hq
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hq.symm)

theorem toralCentralizer_highDiag_eq_sup (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [Finite K]
    (hK : ringChar K = 2) {c : Kˣ} (hc : 3 ≤ orderOf c) :
    toralCentralizer τ K (highDiag τ c) = highTorusLine τ K ⊔ rootSpan τ K (perpRoots τ) ∧
      Disjoint (highTorusLine τ K) (rootSpan τ K (perpRoots τ)) ∧
      ∀ x ∈ highTorusLine τ K, ∀ y ∈ rootSpan τ K (perpRoots τ), Commute x y := by
  obtain ⟨hc1, hc2⟩ := F4Pilot.ne_one_and_sq_ne_one_of_three_le_orderOf hc
  refine ⟨?_, disjoint_highTorusLine_rootSpan hτ hK,
    fun x hx y hy => commute_of_mem_highTorusLine_of_mem_rootSpan hx hy⟩
  rw [toralCentralizer_highDiag hτ hc1 hc2]
  exact le_antisymm
    (sup_le (torusGroup_le_highTorusLine_sup hτ (F4Pilot.exists_sq_eq_of_ringChar_eq_two hK))
      le_sup_right)
    (sup_le ((highTorusLine_le_torusGroup hτ).trans le_sup_left) le_sup_right)

end Full

end CFSG.SeitzReduction.EPilot
