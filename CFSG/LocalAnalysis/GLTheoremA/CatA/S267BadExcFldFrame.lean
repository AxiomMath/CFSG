module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcHRTypes
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcG2Model
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction CFSG.SeitzReduction.EPilot
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley (rootSL2_injective_of_field entrywise_rootSL2_of_field
  range_rootSL2_of_isRoot)

@[expose] def frameSize : Tag → ℕ
  | .F4 => 4
  | .E6 => 4
  | .E7 => 7
  | .E8 => 8
  | _ => 1

@[expose] def frameRoot : (τ : Tag) → Fin (frameSize τ) → Fin τ.rank → ℤ
  | .F4 => ![![2, 3, 4, 2], ![0, 1, 2, 2], ![0, 1, 0, 0], ![0, 1, 2, 0]]
  | .E6 => ![![1, 2, 2, 3, 2, 1], ![1, 0, 1, 1, 1, 1], ![0, 0, 0, 1, 1, 0], ![0, 0, 1, 1, 0, 0]]
  | .E7 => ![![2, 2, 3, 4, 3, 2, 1], ![0, 1, 1, 2, 2, 2, 1], ![0, 0, 0, 0, 1, 0, 0],
      ![0, 0, 0, 0, 0, 0, 1], ![0, 1, 0, 0, 0, 0, 0], ![0, 1, 1, 2, 1, 0, 0],
      ![0, 0, 1, 0, 0, 0, 0]]
  | .E8 => ![![2, 3, 4, 6, 5, 4, 3, 2], ![2, 2, 3, 4, 3, 2, 1, 0], ![0, 1, 1, 2, 1, 1, 0, 0],
      ![0, 1, 0, 1, 1, 0, 0, 0], ![0, 1, 1, 1, 1, 1, 1, 0], ![0, 0, 0, 0, 1, 1, 0, 0],
      ![0, 0, 1, 1, 1, 0, 0, 0], ![0, 0, 0, 1, 1, 1, 1, 0]]
  | .G2 => ![highRoot .G2]
  | .D4 => ![highRoot .D4]

theorem frameSize_pos (τ : Tag) : 0 < frameSize τ := by cases τ <;> decide

@[expose] def frame0 (τ : Tag) : Fin (frameSize τ) := ⟨0, frameSize_pos τ⟩

@[expose] def frame1 {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    Fin (frameSize τ) :=
  ⟨1, by rcases hτ with rfl | rfl | rfl | rfl <;> decide⟩

theorem frame1_ne_frame0 {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    frame1 hτ ≠ frame0 τ := fun h => by
  have := congrArg Fin.val h
  simp [frame1, frame0] at this

theorem frame_check {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    frameRoot τ (frame0 τ) = highRoot τ ∧
    (∀ i, RootOps.isRootB τ (frameRoot τ i) = true) ∧
    (∀ i, i ≠ frame0 τ → frameRoot τ i (highNode τ) = 0) ∧
    ∀ i j, i ≠ j → iform (frameRoot τ i) (frameRoot τ j) = 0 ∧
      RootOps.isRootB τ (frameRoot τ i + frameRoot τ j) = false ∧
      RootOps.isRootB τ (frameRoot τ i - frameRoot τ j) = false := by
  rcases hτ with rfl | rfl | rfl | rfl <;> decide +kernel


variable {τ : Tag}

theorem isRoot_frameRoot (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (i : Fin (frameSize τ)) :
    IsRoot τ (frameRoot τ i) :=
  RootOps.isRootB_iff.1 ((frame_check hτ).2.1 i)

theorem frameRoot_mem_perpRoots (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {i : Fin (frameSize τ)} (hi : i ≠ frame0 τ) : frameRoot τ i ∈ perpRoots τ :=
  ⟨isRoot_frameRoot hτ i, (frame_check hτ).2.2.1 i hi⟩

variable (τ) (K : Type) [Field K]

@[expose] noncomputable def frameSL2 (i : Fin (frameSize τ)) : SL2 K →* ↥(adjointGroup τ K) :=
  (rootSL2 τ K (frameRoot τ i)).codRestrict (adjointGroup τ K)
    (exceptional_Lang_root_rank_one_data τ K (frameRoot τ i)).2.2.2.2.1

variable {τ K}

theorem coe_frameSL2 (i : Fin (frameSize τ)) (A : SL2 K) :
    ((frameSL2 τ K i A : ↥(adjointGroup τ K)) : ModGL τ K) = rootSL2 τ K (frameRoot τ i) A :=
  rfl

theorem frameSL2_injective (i : Fin (frameSize τ)) : Function.Injective (frameSL2 τ K i) :=
  fun A B h => rootSL2_injective_of_field (τ := τ) (K := K) (frameRoot τ i)
    (congrArg Subtype.val h)

theorem coe_frameSL2_frame0 (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (A : SL2 K) :
    ((frameSL2 τ K (frame0 τ) A : ↥(adjointGroup τ K)) : ModGL τ K) =
      rootSL2 τ K (highRoot τ) A := by
  rw [coe_frameSL2, (frame_check hτ).1]

theorem frameSL2_commute (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {i j : Fin (frameSize τ)} (hij : i ≠ j) (A B : SL2 K) :
    frameSL2 τ K i A * frameSL2 τ K j B = frameSL2 τ K j B * frameSL2 τ K i A := by
  have hnot : ∀ {v : Fin τ.rank → ℤ}, RootOps.isRootB τ v = false → ¬ IsRoot τ v :=
    fun hv hr => by
      rw [← RootOps.isRootB_iff, hv] at hr
      exact Bool.false_ne_true hr
  obtain ⟨h0, hp, hm⟩ := (frame_check hτ).2.2.2 i j hij
  exact Subtype.ext (exceptional_Lang_strongly_orthogonal_root_rank_one_commutation τ K
    (isRoot_frameRoot hτ i) (isRoot_frameRoot hτ j) h0 (hnot hp) (hnot hm) _ ⟨A, rfl⟩ _ ⟨B, rfl⟩)

theorem coe_frameSL2_mem_perp (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {i : Fin (frameSize τ)} (hi : i ≠ frame0 τ) (A : SL2 K) :
    ((frameSL2 τ K i A : ↥(adjointGroup τ K)) : ModGL τ K) ∈ rootSpan τ K (perpRoots τ) := by
  have hmem : rootSL2 τ K (frameRoot τ i) A ∈ (rootSL2 τ K (frameRoot τ i)).range := ⟨A, rfl⟩
  rw [range_rootSL2_of_isRoot (isRoot_frameRoot hτ i)] at hmem
  have hγ := frameRoot_mem_perpRoots hτ hi
  exact (sup_le (le_iSup₂_of_le (frameRoot τ i) hγ le_rfl)
    (le_iSup₂_of_le (-frameRoot τ i) (neg_mem_perpRoots hγ) le_rfl) :
      rootSubgroup τ K (frameRoot τ i) ⊔ rootSubgroup τ K (-frameRoot τ i) ≤
        rootSpan τ K (perpRoots τ)) hmem

theorem hrRootData_of (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) : HRRootData τ := by
  rcases hτ with rfl | hE
  · exact hrRootData_F4
  · exact hrRootData_E hE

theorem rootSL2_highRoot_commute_perp (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (A : SL2 K)
    {j : ModGL τ K} (hj : j ∈ rootSpan τ K (perpRoots τ)) :
    rootSL2 τ K (highRoot τ) A * j = j * rootSL2 τ K (highRoot τ) A := by
  have hd := hrRootData_of hτ
  have hmem : rootSL2 τ K (highRoot τ) A ∈ (rootSL2 τ K (highRoot τ)).range := ⟨A, rfl⟩
  rw [range_rootSL2_of_isRoot (isRoot_highRoot τ)] at hmem
  have h1 := rootSubgroup_highRoot_le_centralizer (K := K) (Or.inl rfl) hd.abs_le hd.eq_highRoot
    hd.highRoot_highNode
  have h2 := rootSubgroup_highRoot_le_centralizer (K := K) (Or.inr rfl) hd.abs_le hd.eq_highRoot
    hd.highRoot_highNode
  rw [one_smul] at h1
  rw [neg_one_smul] at h2
  have hc := (sup_le h1 h2) hmem
  exact (Subgroup.mem_centralizer_iff.1 hc j hj).symm

theorem frameSL2_zero_commute_perp (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (A : SL2 K)
    {j : ModGL τ K} (hj : j ∈ rootSpan τ K (perpRoots τ)) :
    ((frameSL2 τ K (frame0 τ) A : ↥(adjointGroup τ K)) : ModGL τ K) * j =
      j * ((frameSL2 τ K (frame0 τ) A : ↥(adjointGroup τ K)) : ModGL τ K) := by
  rw [coe_frameSL2_frame0 hτ]
  exact rootSL2_highRoot_commute_perp hτ A hj

theorem entrywise_frameSL2 (σ : K ≃+* K) (i : Fin (frameSize τ)) (A : SL2 K) :
    entrywiseAdjointAut τ σ (frameSL2 τ K i A) =
      frameSL2 τ K i (Matrix.SpecialLinearGroup.map σ.toRingHom A) := by
  refine Subtype.ext ?_
  rw [coe_entrywiseAdjointAut, coe_frameSL2, coe_frameSL2]
  exact entrywise_rootSL2_of_field σ.toRingHom (frameRoot τ i) A

section Hom

variable {p : ℕ} [NeZero p]

@[expose] def sl2PowHom {A₀ : SL2 K} (hA₀ : A₀ ^ p = 1) : Multiplicative (ZMod p) →* SL2 K where
  toFun s := A₀ ^ (Multiplicative.toAdd s).val
  map_one' := by simp
  map_mul' s t := by
    simp only [toAdd_mul, ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ hA₀).symm

theorem sl2PowHom_apply {A₀ : SL2 K} (hA₀ : A₀ ^ p = 1) (s : Multiplicative (ZMod p)) :
    sl2PowHom hA₀ s = A₀ ^ (Multiplicative.toAdd s).val :=
  rfl

theorem sl2PowHom_injective {A₀ : SL2 K} (hA₀ : orderOf A₀ = p) :
    Function.Injective (sl2PowHom (K := K) (hA₀ ▸ pow_orderOf_eq_one A₀)) := by
  intro s t h
  rw [sl2PowHom_apply, sl2PowHom_apply] at h
  have hs : (Multiplicative.toAdd s).val < orderOf A₀ := by rw [hA₀]; exact ZMod.val_lt _
  have ht : (Multiplicative.toAdd t).val < orderOf A₀ := by rw [hA₀]; exact ZMod.val_lt _
  exact Multiplicative.toAdd.injective (ZMod.val_injective _ (pow_injOn_Iio_orderOf hs ht h))

variable (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {A₀ : SL2 K} (hA₀ : A₀ ^ p = 1)

@[expose] noncomputable def frameFactor (i : Fin (frameSize τ)) :
    Multiplicative (ZMod p) →* ↥(adjointGroup τ K) :=
  (frameSL2 τ K i).comp (sl2PowHom hA₀)

include hτ in
theorem frameFactor_commute :
    Pairwise fun i j => ∀ (x y : Multiplicative (ZMod p)),
      Commute (frameFactor (τ := τ) (K := K) hA₀ i x) (frameFactor (τ := τ) (K := K) hA₀ j y) :=
  fun _ _ hij _ _ => frameSL2_commute hτ hij _ _

@[expose] noncomputable def frameHom :
    (Fin (frameSize τ) → Multiplicative (ZMod p)) →* ↥(adjointGroup τ K) :=
  MonoidHom.noncommPiCoprod (frameFactor hA₀) (frameFactor_commute hτ hA₀)

theorem frameFactor_apply (i : Fin (frameSize τ)) (s : Multiplicative (ZMod p)) :
    frameFactor (τ := τ) (K := K) hA₀ i s = frameSL2 τ K i (sl2PowHom hA₀ s) :=
  MonoidHom.comp_apply _ _ _

theorem frameHom_mulSingle (i : Fin (frameSize τ)) (s : Multiplicative (ZMod p)) :
    frameHom hτ hA₀ (Pi.mulSingle i s) = frameFactor (τ := τ) (K := K) hA₀ i s :=
  MonoidHom.noncommPiCoprod_mulSingle (frameFactor hA₀) i s

theorem range_frameHom :
    (frameHom hτ hA₀).range = ⨆ i, (frameFactor (τ := τ) (K := K) hA₀ i).range :=
  MonoidHom.noncommPiCoprod_range _

end Hom

theorem mem_center_of_commute_uSL_vSL {F : Type} [Field F] {B : SL2 F}
    (hu : B * uSL 1 = uSL 1 * B) (hv : B * vSL 1 = vSL 1 * B) : B ∈ Subgroup.center (SL2 F) := by
  have hu' := congrArg (fun g : SL2 F => (g : Matrix (Fin 2) (Fin 2) F)) hu
  have hv' := congrArg (fun g : SL2 F => (g : Matrix (Fin 2) (Fin 2) F)) hv
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL] at hu' hv'
  have e00 := congrFun (congrFun hu' 0) 1
  have e10 := congrFun (congrFun hu' 1) 1
  have f01 := congrFun (congrFun hv' 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e10 f01
  have hdet := det_SL2 B
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨(B : Matrix (Fin 2) (Fin 2) F) 0 0, ?_, ?_⟩
  · have hc : (B : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination e10
    have hb : (B : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by linear_combination f01
    have had : (B : Matrix (Fin 2) (Fin 2) F) 1 1 = (B : Matrix (Fin 2) (Fin 2) F) 0 0 := by
      linear_combination -e00
    rw [hc, hb, had] at hdet
    simpa [sq] using hdet
  · have hc : (B : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination e10
    have hb : (B : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by linear_combination f01
    have had : (B : Matrix (Fin 2) (Fin 2) F) 1 1 = (B : Matrix (Fin 2) (Fin 2) F) 0 0 := by
      linear_combination -e00
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hc, hb, had]

section Inj

variable {p : ℕ} [NeZero p] (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {A₀ : SL2 K}

theorem eq_one_of_mem_frameFactor_of_commute (hp2 : Odd p) (hA₀ : A₀ ^ p = 1)
    {i : Fin (frameSize τ)} {g : ↥(adjointGroup τ K)} (hg : g ∈ (frameFactor hA₀ i).range)
    (hc : ∀ B : SL2 K, g * frameSL2 τ K i B = frameSL2 τ K i B * g) : g = 1 := by
  obtain ⟨s, rfl⟩ := hg
  change frameSL2 τ K i (sl2PowHom hA₀ s) = 1
  set C := sl2PowHom hA₀ s with hC
  have hCc : C ∈ Subgroup.center (SL2 K) := by
    rw [Subgroup.mem_center_iff]
    intro B
    apply frameSL2_injective i
    rw [map_mul, map_mul]
    exact (hc B).symm
  have hCp : C ^ p = 1 := by
    rw [hC, ← map_pow]
    have : s ^ p = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [this, map_one]
  rw [eq_one_of_mem_center_sl2_of_pow hp2 hCc hCp, map_one]

theorem frameHom_injective (hp2 : Odd p) (hA₀ : orderOf A₀ = p) :
    Function.Injective (frameHom hτ (K := K) (hA₀ ▸ pow_orderOf_eq_one A₀)) := by
  have hA₀' : A₀ ^ p = 1 := hA₀ ▸ pow_orderOf_eq_one A₀
  refine MonoidHom.injective_noncommPiCoprod_of_iSupIndep _ ?_ fun i =>
    (frameSL2_injective i).comp (sl2PowHom_injective hA₀)
  rw [iSupIndep_def]
  intro i
  rw [disjoint_iff, eq_bot_iff]
  intro g hg
  obtain ⟨hgi, hgo⟩ := Subgroup.mem_inf.1 hg
  rw [Subgroup.mem_bot]
  refine eq_one_of_mem_frameFactor_of_commute hp2 hA₀' hgi fun B => ?_
  have hle : (⨆ j, ⨆ (_ : j ≠ i), (frameFactor (τ := τ) (K := K) hA₀' j).range) ≤
      Subgroup.centralizer (Set.range (frameSL2 τ K i)) := by
    refine iSup₂_le fun j hj => ?_
    rintro _ ⟨s, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨B', rfl⟩
    exact frameSL2_commute hτ hj.symm _ _
  exact (Subgroup.mem_centralizer_iff.1 (hle hgo) _ ⟨B, rfl⟩).symm

end Inj

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
