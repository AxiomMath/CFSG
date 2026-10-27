module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFldTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3LinCent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcHR2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Layer
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Co13Gen

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction CFSG.SeitzReduction.EPilot
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley (rootSL2_injective_of_field range_rootSL2_of_isRoot)

@[expose] def frameTwoLNodes : (τ : Tag) → Finset (Fin τ.rank)
  | .F4 => ({0, 3} : Finset (Fin 4))
  | .E6 => ({0, 1, 5} : Finset (Fin 6))
  | .E7 => ({0, 5, 6} : Finset (Fin 7))
  | .E8 => ({0, 7} : Finset (Fin 8))
  | _ => ∅

@[expose] def frameTwoLNode : (τ : Tag) → Fin τ.rank
  | .F4 => (1 : Fin 4)
  | .E6 => (3 : Fin 6)
  | .E7 => (3 : Fin 7)
  | .E8 => (3 : Fin 8)
  | .G2 => (0 : Fin 2)
  | .D4 => (0 : Fin 4)

@[expose] def frameTwoSplitCheck (τ : Tag) : Bool :=
  (List.range τ.rootCertificate.roots.length).all fun m =>
    !decide (∀ j ∈ frameTwoNodes τ, τ.rootCertificate.root m j = 0) ||
    decide (∀ j ∈ frameTwoLNodes τ, τ.rootCertificate.root m j = 0) ||
    (List.range τ.rootCertificate.roots.length).all fun m' =>
      !decide (∀ j ∈ frameTwoLNodes τ, τ.rootCertificate.root m' j = 0) ||
      (decide (iform (τ.rootCertificate.root m) (τ.rootCertificate.root m') = 0) &&
        !RootOps.isRootB τ (τ.rootCertificate.root m + τ.rootCertificate.root m') &&
        !RootOps.isRootB τ (τ.rootCertificate.root m - τ.rootCertificate.root m'))

theorem frameTwoSplitCheck_eq_true {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    frameTwoSplitCheck τ = true := by
  rcases hτ with rfl | rfl | rfl | rfl <;> decide +kernel

theorem frameTwoNodes_subset {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    frameTwoNodes τ ⊆ frameTwoLNodes τ := by
  rcases hτ with rfl | rfl | rfl | rfl <;> decide

theorem frameTwoLNode_not_mem {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    frameTwoLNode τ ∉ frameTwoLNodes τ := by
  rcases hτ with rfl | rfl | rfl | rfl <;> decide

private def parF4'' : Fin Tag.F4.rank → Fin Tag.F4.rank := ![2, 2, 2, 2]
private def depF4'' : Fin Tag.F4.rank → ℕ := ![0, 1, 0, 1]
private def parE6'' : Fin Tag.E6.rank → Fin Tag.E6.rank := ![3, 3, 3, 3, 3, 3]
private def depE6'' : Fin Tag.E6.rank → ℕ := ![0, 0, 1, 0, 1, 0]
private def parE7'' : Fin Tag.E7.rank → Fin Tag.E7.rank := ![3, 3, 3, 3, 3, 3, 3]
private def depE7'' : Fin Tag.E7.rank → ℕ := ![0, 1, 1, 0, 1, 0, 0]
private def parE8'' : Fin Tag.E8.rank → Fin Tag.E8.rank := ![2, 3, 3, 3, 3, 4, 5, 7]
private def depE8'' : Fin Tag.E8.rank → ℕ := ![2, 1, 1, 0, 1, 2, 3, 0]


variable {τ : Tag} {K : Type} [Field K]

theorem isQuasisimple_frameTwoL (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hK2 : ringChar K ≠ 2) :
    CFSG.Open.IsQuasisimple ↥(rootSpan τ K (leviRootsOff τ (frameTwoLNodes τ))) := by
  rcases hτ with rfl | rfl | rfl | rfl
  · exact isQuasisimple_rootSpan_leviRootsOff_F4 hK2 _ (i₀ := (2 : Fin Tag.F4.rank))
      (i₁ := (1 : Fin Tag.F4.rank)) (by decide) (by decide) (by decide) parF4'' depF4''
      (by decide)
  · exact isQuasisimple_rootSpan_leviRootsOff_of_odd hK2 (by decide) _
      (i₀ := (3 : Fin Tag.E6.rank)) (i₁ := (2 : Fin Tag.E6.rank)) (by decide) (by decide)
      (by decide) parE6'' depE6'' (by decide)
  · exact isQuasisimple_rootSpan_leviRootsOff_of_odd hK2 (by decide) _
      (i₀ := (3 : Fin Tag.E7.rank)) (i₁ := (2 : Fin Tag.E7.rank)) (by decide) (by decide)
      (by decide) parE7'' depE7'' (by decide)
  · exact isQuasisimple_rootSpan_leviRootsOff_of_odd hK2 (by decide) _
      (i₀ := (3 : Fin Tag.E8.rank)) (i₁ := (2 : Fin Tag.E8.rank)) (by decide) (by decide)
      (by decide) parE8'' depE8'' (by decide)

theorem rootSpan_frameTwo_le_normalizer_L (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    rootSpan τ K (leviRootsOff τ (frameTwoNodes τ)) ≤
      Subgroup.normalizer (rootSpan τ K (leviRootsOff τ (frameTwoLNodes τ)) :
        Set (ModGL τ K)) := by
  have hc := frameTwoSplitCheck_eq_true hτ
  refine iSup₂_le fun β hβ => ?_
  obtain ⟨m, hm, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hβ.1
  simp only [frameTwoSplitCheck, List.all_eq_true, List.mem_range] at hc
  have h1 := hc m hm
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    at h1
  rcases h1 with (h1 | h1) | h1
  · exact absurd hβ.2 h1
  · exact (le_iSup₂_of_le _ ⟨hβ.1, h1⟩ le_rfl : rootSubgroup τ K (τ.rootCertificate.root m) ≤
      rootSpan τ K (leviRootsOff τ (frameTwoLNodes τ))).trans Subgroup.le_normalizer
  · refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    have hle : rootSpan τ K (leviRootsOff τ (frameTwoLNodes τ)) ≤
        Subgroup.centralizer ({x} : Set (ModGL τ K)) := by
      refine iSup₂_le fun δ hδ y hy => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨m', hm', hδm⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hδ.1
      rw [List.all_eq_true] at h1
      have h2 := h1 m' (List.mem_range.2 hm')
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.and_eq_true,
        decide_eq_true_eq] at h2
      rw [← hδm] at hδ hy
      rcases h2 with h2 | ⟨⟨h0, hp⟩, hmi⟩
      · exact absurd hδ.2 h2
      · have hnot : ∀ {v : Fin τ.rank → ℤ}, RootOps.isRootB τ v = false → ¬ IsRoot τ v :=
          fun hv hr => by
            rw [← RootOps.isRootB_iff, hv] at hr
            exact Bool.false_ne_true hr
        have hx' : x ∈ rootRankOneGroup τ K (τ.rootCertificate.root m) := by
          rw [(exceptional_Lang_root_rank_one_torus_transport τ K hβ.1).1]
          exact (le_sup_left : rootSubgroup τ K _ ≤ rootSubgroup τ K _ ⊔ rootSubgroup τ K _) hx
        have hy' : y ∈ rootRankOneGroup τ K (τ.rootCertificate.root m') := by
          rw [(exceptional_Lang_root_rank_one_torus_transport τ K hδ.1).1]
          exact (le_sup_left : rootSubgroup τ K _ ≤ rootSubgroup τ K _ ⊔ rootSubgroup τ K _) hy
        exact (exceptional_Lang_strongly_orthogonal_root_rank_one_commutation τ K hβ.1 hδ.1 h0
          (hnot hp) (hnot hmi) x hx' y hy').symm
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)

theorem glaPLayer_perpJ_inf_frameTwo_ne_bot [Finite K]
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hK2 : ringChar K ≠ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) {A₀ : SL2 K} (hA₀ : orderOf A₀ = p)
    {A₁₂ : Subgroup ↥(adjointGroup τ K)} (hz₀ : frameSL2 τ K (frame0 τ) A₀ ∈ A₁₂)
    (hz₁ : frameSL2 τ K (frame1 hτ) A₀ ∈ A₁₂)
    (hcomm : ∀ a ∈ A₁₂, ∀ l ∈ rootSpan τ K (leviRootsOff τ (frameTwoNodes τ)),
      ((a : ↥(adjointGroup τ K)) : ModGL τ K) * l = l * a) :
    GLAPLayer p ((rootSpan τ K (perpRoots τ)).subgroupOf (adjointGroup τ K) ⊓
      Subgroup.centralizer (A₁₂ : Set ↥(adjointGroup τ K))) ≠ ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite ↥(adjointGroup τ K) := generated_group_finite τ K
  have hd := hrRootData_of hτ
  have hodd : Odd p := hp.odd_of_ne_two hp2
  set X := ↥(adjointGroup τ K)
  have hA₀p : A₀ ^ p = 1 := hA₀ ▸ pow_orderOf_eq_one A₀
  have hA₀1 : A₀ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hA₀
    exact hp.one_lt.ne hA₀
  set L₁₂ := rootSpan τ K (leviRootsOff τ (frameTwoNodes τ)) with hL₁₂
  set L := rootSpan τ K (leviRootsOff τ (frameTwoLNodes τ)) with hL
  set R := rootSpan τ K (leviRootsOff τ (frameTwoNodes τ) ∪
    {highRoot τ, -highRoot τ, frameTwoRoot τ, -frameTwoRoot τ}) with hR
  have hRL : R ≤ Subgroup.normalizer (L₁₂ : Set (ModGL τ K)) :=
    rootSpan_frameTwoKernel_le_normalizer hτ
  have hL₁₂L : L₁₂ ≤ Subgroup.normalizer (L : Set (ModGL τ K)) :=
    rootSpan_frameTwo_le_normalizer_L hτ
  have hL₁₂J : L₁₂ ≤ rootSpan τ K (perpRoots τ) :=
    rootSpan_mono fun β hβ => ⟨hβ.1, hβ.2 _ (highNode_mem_frameTwoNodes hτ)⟩
  have hL₁₂R : L₁₂ ≤ R := rootSpan_mono Set.subset_union_left
  have hLL₁₂ : L ≤ L₁₂ := rootSpan_mono fun β hβ => ⟨hβ.1, fun j hj =>
    hβ.2 j (frameTwoNodes_subset hτ hj)⟩
  have hLX : L ≤ adjointGroup τ K := rootSpan_le_adjointGroup K _
  have hRX : R ≤ adjointGroup τ K := rootSpan_le_adjointGroup K _
  set H : Subgroup X := (rootSpan τ K (perpRoots τ)).subgroupOf (adjointGroup τ K) ⊓
    Subgroup.centralizer (A₁₂ : Set X) with hH
  have hHR : ∀ g ∈ H, ((g : X) : ModGL τ K) ∈ Subgroup.normalizer (R : Set (ModGL τ K)) := by
    intro g hg
    obtain ⟨-, hgc⟩ := Subgroup.mem_inf.1 hg
    have hc₀ := Subgroup.mem_centralizer_iff.1 hgc _ hz₀
    have hc₁ := Subgroup.mem_centralizer_iff.1 hgc _ hz₁
    have hC : ∀ c : (AlgebraicClosure K)ˣ, c ≠ 1 → c ^ 2 ≠ 1 →
        toralCentralizer τ (AlgebraicClosure K) (Pi.mulSingle (highNode τ) c) ≤
          toralCentralizer τ (AlgebraicClosure K) (Pi.mulSingle (highNode τ) (-1)) :=
      fun c hc1 hc2 => toralCentralizer_mulSingle_le hc1 hc2 hd.abs_le hd.highRoot_highNode (-1)
    have hg₀ := centralizer_rootSL2_highRoot_le hτ hp hp2 hpK hA₀p hA₀1 hC
      (Subgroup.mem_inf.2 ⟨g.2, Subgroup.mem_centralizer_singleton_iff.2 (by
        have := congrArg Subtype.val hc₀
        rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_frameSL2_frame0 hτ] at this
        exact this.symm)⟩)
    have hg₁ := centralizer_rootSL2_frameTwo_le hτ hK2 hp hp2 hpK hA₀p hA₀1
      (Subgroup.mem_inf.2 ⟨g.2, Subgroup.mem_centralizer_singleton_iff.2 (by
        have := congrArg Subtype.val hc₁
        rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_frameSL2, frameRoot_frame1 hτ] at this
        exact this.symm)⟩)
    have hN := toralCentralizer_inf_le_normalizer (K := K) _ _ (Subgroup.mem_inf.2 ⟨hg₀, hg₁⟩)
    rwa [rootCharKernel_frameTwo_eq hτ hK2] at hN
  set L' : Subgroup X := L.subgroupOf (adjointGroup τ K) with hL'
  set L₁₂' : Subgroup X := L₁₂.subgroupOf (adjointGroup τ K) with hL₁₂'
  set N' : Subgroup X := R.subgroupOf (adjointGroup τ K) ⊓ H with hN'
  have hL₁₂H : L₁₂' ≤ H := by
    intro x hx
    rw [hL₁₂', Subgroup.mem_subgroupOf] at hx
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 (hL₁₂J hx), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subtype.ext (hcomm a ha _ hx)
  have hsub : IsSubnormal L' H := by
    refine IsSubnormal.step (fun x hx => Subgroup.mem_subgroupOf.2 (hLL₁₂
      (Subgroup.mem_subgroupOf.1 hx))) ⟨fun n hn g => ?_⟩ (IsSubnormal.step
        (fun x hx => Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 (hL₁₂R
          (Subgroup.mem_subgroupOf.1 hx)), hL₁₂H hx⟩) ⟨fun n hn g => ?_⟩
        (IsSubnormal.step inf_le_right ⟨fun n hn g => ?_⟩ (IsSubnormal.refl H)))
    · rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hn ⊢
      exact (Subgroup.mem_normalizer_iff.1 (hL₁₂L (Subgroup.mem_subgroupOf.1 g.2)) _).1 hn
    · rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hn ⊢
      have hgR : (((g : ↥N') : X) : ModGL τ K) ∈ R :=
        Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 g.2).1
      exact (Subgroup.mem_normalizer_iff.1 (hRL hgR) _).1 hn
    · rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨hnR, hnH⟩ := Subgroup.mem_inf.1 hn
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 ?_, mul_mem (mul_mem g.2 hnH)
        (inv_mem g.2)⟩
      exact (Subgroup.mem_normalizer_iff.1 (hHR _ g.2) _).1 (Subgroup.mem_subgroupOf.1 hnR)
  have eL : ↥L' ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLX
  have hq : CFSG.Open.IsQuasisimple ↥L' :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co15.isQuasisimple_of_equiv eL.symm
      (isQuasisimple_frameTwoL hτ hK2)
  set k := frameTwoLNode τ
  have hk := frameTwoLNode_not_mem hτ
  have hek : (Pi.single k 1 : Fin τ.rank → ℤ) ∈ leviRootsOff τ (frameTwoLNodes τ) :=
    ⟨IsRoot.basis k, fun j hj => Pi.single_eq_of_ne (ne_of_mem_of_not_mem hj hk) 1⟩
  have hek' : (-Pi.single k 1 : Fin τ.rank → ℤ) ∈ leviRootsOff τ (frameTwoLNodes τ) :=
    ⟨IsRoot.neg (IsRoot.basis k), fun j hj => by
      rw [Pi.neg_apply, Pi.single_eq_of_ne (ne_of_mem_of_not_mem hj hk) 1, neg_zero]⟩
  set ρk : SL2 K →* X := (rootSL2 τ K (Pi.single k 1)).codRestrict (adjointGroup τ K)
    (exceptional_Lang_root_rank_one_data τ K _).2.2.2.2.1 with hρk
  have hρkL : ∀ B, ρk B ∈ L' := by
    intro B
    rw [hL', Subgroup.mem_subgroupOf]
    have hmem : rootSL2 τ K (Pi.single k 1) B ∈ (rootSL2 τ K (Pi.single k 1)).range := ⟨B, rfl⟩
    rw [range_rootSL2_of_isRoot (IsRoot.basis k)] at hmem
    exact (sup_le (le_iSup₂_of_le _ hek le_rfl) (le_iSup₂_of_le _ hek' le_rfl) :
      rootSubgroup τ K (Pi.single k 1) ⊔ rootSubgroup τ K (-Pi.single k 1) ≤ L) hmem
  have hρkinj : Function.Injective ρk := fun A B h =>
    rootSL2_injective_of_field (τ := τ) (K := K) _ (congrArg Subtype.val h)
  obtain ⟨W, hW⟩ := exists_not_commute_sl2 hp hodd hA₀
  have hzp : ρk A₀ ^ p = 1 := by rw [← map_pow, hA₀p, map_one]
  have hzw : ρk A₀ * ρk W ≠ ρk W * ρk A₀ := by
    intro h
    rw [← map_mul, ← map_mul] at h
    exact hW (hρkinj h)
  exact CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPLayer_ne_bot_of_isSubnormal_quasisimple hp hsub hq
    (CFSG.LocalAnalysis.GLTheoremA.H81.LinA3.dvd_card_quotient_center_of_not_commute hp
      (hρkL A₀) (hρkL W) hzp hzw)

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
