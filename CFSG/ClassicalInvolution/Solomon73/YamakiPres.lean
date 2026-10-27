module

public import CFSG.Certificates.CosetTableColumns
public import CFSG.Open.StatedDefs
public import Certificates.Data.YamakiPres
public import Certificates.Certificate550701
public import Certificates.Certificate550702
import CFSG.Certificates.CosetTablePresented
import Certificates.Kernel.Bounds.Family
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3
import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
import CFSG.Open.StatedAPI
import CFSG.RankThree.PartOne.CTP.SeitzSpClosure
import Mathlib.LinearAlgebra.Matrix.Transvection
public import CFSG.Certificates.CosetTableShort
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.ClassicalInvolution.Solomon73.Yamaki

open CFSG.CosetTable CFSG.Open Matrix

section Words

variable {m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem wordMat_append (M : Fin m → Matrix ι ι (ZMod 2)) (v w : List (Fin m × Bool)) :
    wordMat M (v ++ w) = wordMat M v * wordMat M w := by
  simp only [wordMat, List.map_append, List.prod_append]

theorem wordMat_cons (M : Fin m → Matrix ι ι (ZMod 2)) (l : Fin m × Bool)
    (w : List (Fin m × Bool)) : wordMat M (l :: w) = M l.1 * wordMat M w := by
  simp only [wordMat, List.map_cons, List.prod_cons]

theorem wordMat_reverse_mul (M : Fin m → Matrix ι ι (ZMod 2)) (hM : ∀ i, M i * M i = 1) :
    ∀ w : List (Fin m × Bool), wordMat M w.reverse * wordMat M w = 1
  | [] => by simp [wordMat]
  | l :: w => by
    rw [List.reverse_cons, wordMat_append, wordMat_cons, wordMat_cons]
    simp only [wordMat, List.map_nil, List.prod_nil, Matrix.mul_one]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (M l.1), hM, Matrix.one_mul]
    exact wordMat_reverse_mul M hM w

theorem wordMat_eq_one_of_halfOK (M : Fin m → Matrix ι ι (ZMod 2)) (hM : ∀ i, M i * M i = 1)
    {w : List (Fin m × Bool)} (h : halfOK M w = true) : wordMat M w = 1 := by
  have h' := of_decide_eq_true h
  rw [← List.take_append_drop (w.length / 2) w, wordMat_append, h']
  exact wordMat_reverse_mul M hM _

theorem lift_mk_eq_prod {G : Type*} [Group G] {x : Fin m → G} (hx : ∀ i, x i * x i = 1)
    (w : List (Fin m × Bool)) :
    FreeGroup.lift x (FreeGroup.mk w) = (w.map fun l => x l.1).prod := by
  rw [FreeGroup.lift_mk]
  congr 1
  refine List.map_congr_left fun l _ => ?_
  obtain ⟨i, b⟩ := l
  cases b
  · exact inv_eq_of_mul_eq_one_right (hx i)
  · rfl

theorem closure_eq_bot_or_exists_mulEquiv_of {ws : List (List (Fin m × Bool))} {S : Type*}
    [Group S] [IsSimpleGroup S] (e : PG m ws ≃* S) {G : Type*} [Group G] (x : Fin m → G)
    (hx : ∀ r ∈ ws, FreeGroup.lift x (FreeGroup.mk r) = 1) :
    Subgroup.closure (Set.range x) = ⊥ ∨
      ∃ f : ↥(Subgroup.closure (Set.range x)) ≃* S,
        ∀ i, f ⟨x i, Subgroup.subset_closure ⟨i, rfl⟩⟩ = e (PresentedGroup.of i) := by
  have hrel : ∀ r ∈ {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk},
      FreeGroup.lift x r = 1 := by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact hx w hw
  set φ : PG m ws →* G := PresentedGroup.toGroup hrel
  have hφ : ∀ i, φ (PresentedGroup.of i) = x i := fun i => PresentedGroup.toGroup.of hrel
  have hrange : φ.range = Subgroup.closure (Set.range x) := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      ← Set.range_comp]
    congr 2
    funext i
    exact hφ i
  haveI : IsSimpleGroup (PG m ws) := e.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
  · right
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp h
    refine ⟨(MulEquiv.subgroupCongr hrange.symm).trans
      ((MonoidHom.ofInjective hinj).symm.trans e), fun i => ?_⟩
    simp only [MulEquiv.trans_apply]
    congr 1
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (hφ i).symm
  · left
    rw [← hrange, eq_bot_iff]
    rintro _ ⟨g, rfl⟩
    exact Subgroup.mem_bot.mpr (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top g))

theorem closure_eq_bot_or_nonempty_mulEquiv_of {ws : List (List (Fin m × Bool))} {S : Type*}
    [Group S] [IsSimpleGroup S] (e : PG m ws ≃* S) {G : Type*} [Group G] (x : Fin m → G)
    (hx : ∀ r ∈ ws, FreeGroup.lift x (FreeGroup.mk r) = 1) :
    Subgroup.closure (Set.range x) = ⊥ ∨
      Nonempty (↥(Subgroup.closure (Set.range x)) ≃* S) :=
  (closure_eq_bot_or_exists_mulEquiv_of e x hx).imp_right fun ⟨f, _⟩ => ⟨f⟩

end Words

abbrev YPG : Type := PG 12 yamakiRels

theorem finite_card_YPG :
    Finite YPG ∧ Nat.card YPG ≤ 1451520 :=
  Certificates.certificate550701

theorem spInvolCheck_holds : spInvolCheck () = true :=
  Certificates.certificate550702.1

theorem spSympCheck_holds : spSympCheck () = true :=
  Certificates.certificate550702.2.1

theorem spRelCheck_holds : spRelCheck () = true :=
  Certificates.certificate550702.2.2.1

theorem spTransvCheck_holds : spTransvCheck () = true :=
  Certificates.certificate550702.2.2.2.1

theorem spOrbitCheck_holds : spOrbitCheck () = true :=
  Certificates.certificate550702.2.2.2.2.1

theorem spCoverCheck_holds : spCoverCheck () = true :=
  Certificates.certificate550702.2.2.2.2.2

theorem yamakiMat_mul_self (i : Fin 12) :
    yamakiMat i * yamakiMat i = 1 := by
  have h := spInvolCheck_holds
  simp only [spInvolCheck, List.all_eq_true, decide_eq_true_eq] at h
  exact h i (List.mem_finRange i)

@[expose] def yamakiGL (i : Fin 12) :
    GL (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  ⟨yamakiMat i, yamakiMat i, yamakiMat_mul_self i, yamakiMat_mul_self i⟩

theorem yamakiGL_mem (i : Fin 12) :
    yamakiGL i ∈ StatedSp 3 (ZMod 2) := by
  have h := spSympCheck_holds
  simp only [spSympCheck, List.all_eq_true, decide_eq_true_eq] at h
  exact StatedAPI.mem_statedSp_iff.mpr (h i (List.mem_finRange i))

@[expose] def yamakiSp (i : Fin 12) : StatedSp 3 (ZMod 2) :=
  ⟨yamakiGL i, yamakiGL_mem i⟩

@[simp] theorem coe_yamakiSp (i : Fin 12) :
    (((yamakiSp i : StatedSp 3 (ZMod 2)) : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) = yamakiMat i :=
  rfl

@[expose] def spMat : StatedSp 3 (ZMod 2) →* Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  (Units.coeHom _).comp (StatedSp 3 (ZMod 2)).subtype

theorem spMat_injective : Function.Injective spMat := fun _ _ h => Subtype.ext (Units.ext h)

theorem yamakiSp_mul_self (i : Fin 12) :
    yamakiSp i * yamakiSp i = 1 :=
  spMat_injective (by rw [map_mul, map_one]; exact yamakiMat_mul_self i)

theorem lift_yamakiSp_rel {r : List (Fin 12 × Bool)}
    (hr : r ∈ yamakiRels) : FreeGroup.lift yamakiSp (FreeGroup.mk r) = 1 := by
  apply spMat_injective
  rw [lift_mk_eq_prod yamakiSp_mul_self, map_list_prod, List.map_map, map_one]
  have h := spRelCheck_holds
  simp only [spRelCheck, List.all_eq_true] at h
  exact wordMat_eq_one_of_halfOK yamakiMat yamakiMat_mul_self (h r hr)

theorem lift_yamakiSp_relSet :
    ∀ r ∈ {r : FreeGroup (Fin 12) | r ∈ yamakiRels.map FreeGroup.mk},
      FreeGroup.lift yamakiSp r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
  exact lift_yamakiSp_rel hw

@[expose] noncomputable def yamakiHom :
    YPG →* StatedSp 3 (ZMod 2) :=
  PresentedGroup.toGroup lift_yamakiSp_relSet

theorem yamakiHom_of (i : Fin 12) :
    yamakiHom (PresentedGroup.of i) = yamakiSp i :=
  PresentedGroup.toGroup.of _

open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical in
theorem closure_range_yamakiSp :
    Subgroup.closure (Set.range yamakiSp) = ⊤ := by
  set H := Subgroup.closure (Set.range yamakiSp)
  have hgen : ∀ k, yamakiSp k ∈ H := fun k => Subgroup.subset_closure ⟨k, rfl⟩
  have htr : ∀ y : Fin 3 ⊕ Fin 3 → ZMod 2,
      yamakiMat 7 *ᵥ y = y + (y ⬝ᵥ (fromBlocks 0 1 (-1) 0 *ᵥ vecOf 9)) • vecOf 9 := by
    have h := spTransvCheck_holds
    unfold spTransvCheck at h
    exact of_decide_eq_true h
  have hT1 : spTransvection (vecOf 9) (1 : ZMod 2) = yamakiSp 7 := by
    apply spLin_injective
    refine Units.ext (LinearMap.ext fun y => ?_)
    change spEnd (spTransvection (vecOf 9) 1) y = spEnd (yamakiSp 7) y
    rw [spEnd_spTransvection, spForm_apply, one_mul, spEnd_apply, coe_yamakiSp]
    exact (htr y).symm
  have hT0 : spTransvection (vecOf 9) (0 : ZMod 2) = 1 := by
    apply spLin_injective
    rw [map_one]
    refine Units.ext (LinearMap.ext fun y => ?_)
    change spEnd (spTransvection (vecOf 9) 0) y = y
    rw [spEnd_spTransvection, zero_mul, zero_smul, add_zero]
  have hc9 : TransCenter H (vecOf 9) := by
    intro t
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) t with rfl | rfl
    · rw [hT0]
      exact H.one_mem
    · rw [hT1]
      exact hgen 7
  have hstep : ∀ (k : Fin 12) (p : ℕ), TransCenter H (vecOf p) →
      TransCenter H (yamakiMat k *ᵥ vecOf p) := by
    intro k p hp
    have h := hp.map (hgen k)
    rw [spEnd_apply, coe_yamakiSp] at h
    exact h
  have horbit : ∀ (l : List (ℕ × ℕ × Fin 12)) (seen : List ℕ), orbitOK seen l = true →
      (∀ p ∈ seen, TransCenter H (vecOf p)) → ∀ e ∈ l, TransCenter H (vecOf e.1) := by
    intro l
    induction l with
    | nil => intro _ _ _ e he; simp at he
    | cons e l ih =>
      obtain ⟨c, p, k⟩ := e
      intro seen h hseen
      simp only [orbitOK, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
      obtain ⟨⟨hp, hc⟩, hl⟩ := h
      have hcen : TransCenter H (vecOf c) := hc ▸ hstep k p (hseen p hp)
      have hseen' : ∀ q ∈ c :: seen, TransCenter H (vecOf q) := by
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hcen
        · exact hseen q hq
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hcen
      · exact ih (c :: seen) hl hseen' e he
  have hall := horbit yamakiOrbit [9] spOrbitCheck_holds (fun p hp => by
    rw [List.mem_singleton.mp hp]
    exact hc9)
  have hcov : ∀ v : Fin 3 ⊕ Fin 3 → ZMod 2,
      v = 0 ∨ v = vecOf 9 ∨ ∃ e ∈ yamakiOrbit, vecOf e.1 = v := by
    have h := spCoverCheck_holds
    unfold spCoverCheck at h
    exact of_decide_eq_true h
  apply eq_top_of_transCenter
  intro v
  rcases hcov v with rfl | rfl | ⟨e, he, rfl⟩
  · exact transCenter_zero
  · exact hc9
  · exact hall e he

theorem yamakiHom_surjective :
    Function.Surjective yamakiHom := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_range_yamakiSp, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨PresentedGroup.of i, yamakiHom_of i⟩

theorem card_sp62 : Nat.card (StatedSp 3 (ZMod 2)) = 1451520 := by
  rw [(CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.symplectic_higher_order_and_Sylow
    (K := ZMod 2) 2 2 (Nat.card_zmod 2) (r := 3) (by norm_num)).1]
  decide

theorem yamakiHom_bijective :
    Function.Bijective yamakiHom := by
  have := finite_card_YPG.1
  exact yamakiHom_surjective.bijective_of_nat_card_le (by rw [card_sp62]; exact finite_card_YPG.2)

@[expose] noncomputable def yamakiEquiv :
    YPG ≃* StatedSp 3 (ZMod 2) :=
  MulEquiv.ofBijective yamakiHom yamakiHom_bijective

theorem yamakiEquiv_of
    (i : Fin 12) : yamakiEquiv (PresentedGroup.of i) = yamakiSp i :=
  yamakiHom_of i

theorem isSimpleGroup_sp62 : IsSimpleGroup (StatedSp 3 (ZMod 2)) := by
  have hs : IsSimpleGroup (StatedProj (StatedSp 3 (ZMod 2))) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (ZMod 2) 3 (by norm_num)
      (Or.inr (Or.inr ⟨Nat.card_zmod 2, le_rfl⟩))
  have hbot : (StatedScalars (Fin 3 ⊕ Fin 3) (ZMod 2)).subgroupOf (StatedSp 3 (ZMod 2)) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_subgroupOf] at hg
    obtain ⟨c, hc⟩ := hg
    have h1 : c = 1 := Units.ext ((show ∀ x : ZMod 2, x ≠ 0 → x = 1 by decide) _ c.ne_zero)
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hc, h1, map_one]
    rfl
  exact ((QuotientGroup.quotientMulEquivOfEq hbot).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

theorem closure_eq_bot_or_nonempty_mulEquiv
    {G : Type*} [Group G] (x : Fin 12 → G)
    (hx : ∀ r ∈ yamakiRels, FreeGroup.lift x (FreeGroup.mk r) = 1) :
    Subgroup.closure (Set.range x) = ⊥ ∨
      Nonempty (↥(Subgroup.closure (Set.range x)) ≃* StatedSp 3 (ZMod 2)) :=
  haveI := isSimpleGroup_sp62
  closure_eq_bot_or_nonempty_mulEquiv_of yamakiEquiv x hx

theorem closure_eq_bot_or_exists_mulEquiv
    {G : Type*} [Group G] (x : Fin 12 → G)
    (hx : ∀ r ∈ yamakiRels, FreeGroup.lift x (FreeGroup.mk r) = 1) :
    Subgroup.closure (Set.range x) = ⊥ ∨
      ∃ f : ↥(Subgroup.closure (Set.range x)) ≃* StatedSp 3 (ZMod 2),
        ∀ i, f ⟨x i, Subgroup.subset_closure ⟨i, rfl⟩⟩ = yamakiSp i := by
  haveI := isSimpleGroup_sp62
  simpa only [yamakiEquiv_of] using closure_eq_bot_or_exists_mulEquiv_of yamakiEquiv x hx

end CFSG.ClassicalInvolution.Solomon73.Yamaki
