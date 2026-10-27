module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockCast
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PureEmbed
public import CFSG.Permutation.ProperSupportMaps

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
open CFSG.SeitzReduction.UnitaryPilot CFSG.Permutation.ProperSupportMaps
open CFSG.GH74.Generic.S1.SymBlocksUni
open QuadraticMap

open scoped Matrix

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

def delPerm {m : ℕ} (c : Fin (m + 1)) : Equiv.Perm (Fin (m + 1)) :=
  (Fin.cycleRange c)⁻¹ * finRotate (m + 1)

theorem delPerm_castSucc {m : ℕ} (c : Fin (m + 1)) (j : Fin m) :
    delPerm c (Fin.castSucc j) = c.succAbove j := by
  rw [delPerm]
  change (Fin.cycleRange c).symm (finRotate (m + 1) (Fin.castSucc j)) = c.succAbove j
  have hfr : finRotate (m + 1) (Fin.castSucc j) = Fin.succ j := by
    rw [show (Fin.castSucc j : Fin (m + 1)) =
        ⟨(j : ℕ), j.isLt.trans_le m.le_succ⟩ from rfl,
      finRotate_of_lt (n := m) j.isLt]
    rfl
  rw [hfr]
  exact Fin.cycleRange_symm_succ c j

theorem delPerm_last {m : ℕ} (c : Fin (m + 1)) :
    delPerm c (Fin.last m) = c := by
  rw [delPerm]
  change (Fin.cycleRange c).symm (finRotate (m + 1) (Fin.last m)) = c
  rw [finRotate_last]
  exact Fin.cycleRange_symm_zero c

theorem delPerm_last_eq_one {m : ℕ} : delPerm (Fin.last m) = 1 := by
  rw [delPerm, Fin.cycleRange_last]
  exact inv_mul_cancel _

noncomputable def normDel {m : ℕ} (hm : 2 ≤ m) (c : Fin (m + 1)) :
    normOmega E m →* normOmega E (m + 1) :=
  (MulAut.conj (normPerm E (by omega) (delPerm c))).toMonoidHom.comp
    (normOmegaCast E (Nat.le_succ m))

theorem normDel_injective {m : ℕ} (hm : 2 ≤ m) (c : Fin (m + 1)) :
    Function.Injective (normDel E hm c) := by
  intro a b hab
  have h2 : (MulAut.conj (normPerm E (by omega : 3 ≤ m + 1) (delPerm c)))
      (normOmegaCast E (Nat.le_succ m) a) =
      (MulAut.conj (normPerm E (by omega : 3 ≤ m + 1) (delPerm c)))
      (normOmegaCast E (Nat.le_succ m) b) := by
    simpa only [normDel, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using hab
  exact normOmegaCast_injective E (Nat.le_succ m)
    ((MulAut.conj (normPerm E (by omega : 3 ≤ m + 1) (delPerm c))).injective h2)

theorem normDel_last {m : ℕ} (hm : 2 ≤ m) :
    normDel E hm (Fin.last m) = normOmegaCast E (Nat.le_succ m) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  dsimp only [normDel, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [delPerm_last_eq_one, map_one]
  simp

theorem map_normPureBlock_normDel {m : ℕ} (hm : 2 ≤ m) (c : Fin (m + 1))
    (S : Finset (Fin m)) :
    (normPureBlock E m S).map (normDel E hm c) =
      normPureBlock E (m + 1) (S.map c.succAboveEmb) := by
  classical
  rw [normDel, ← Subgroup.map_map,
    map_normPureBlock_normOmegaCast E (Nat.le_succ m) S,
    map_normPureBlock_normPerm E (by omega : 3 ≤ m + 1) (delPerm c)]
  congr 1
  simp only [Finset.map_eq_image, Finset.image_image]
  apply Finset.image_congr
  intro j _
  change delPerm c (Fin.castLE (Nat.le_succ m) j) = c.succAbove j
  rw [show Fin.castLE (Nat.le_succ m) j = Fin.castSucc j from Fin.ext rfl,
    delPerm_castSucc]

theorem comap_normPureBlock_normDel {m : ℕ} (hm : 2 ≤ m) (c : Fin (m + 1))
    (S : Finset (Fin m)) :
    (normPureBlock E (m + 1) (S.map c.succAboveEmb)).comap (normDel E hm c) =
      normPureBlock E m S := by
  rw [← map_normPureBlock_normDel E hm c S,
    Subgroup.comap_map_eq_self_of_injective (normDel_injective E hm c)]

theorem range_normDel {m : ℕ} (hm : 2 ≤ m) (c : Fin (m + 1)) :
    (normDel E hm c).range = normBlock E (m + 1) (Finset.univ.erase c) := by
  rw [normDel, MonoidHom.range_comp, range_normOmegaCast_succ,
    map_normBlock_normPerm E (by omega : 3 ≤ m + 1) (delPerm c)]
  congr 1
  rw [Finset.image_erase (Equiv.injective (delPerm c)), Finset.image_univ_equiv,
    delPerm_last]

noncomputable def chartLift {G : Type*} [Group G] {m : ℕ} (hm : 2 ≤ m)
    (c : Fin (m + 1)) (κ : normOmega E m →* G) :
    ↥(normDel E hm c).range →* G :=
  κ.comp (MonoidHom.ofInjective (normDel_injective E hm c)).symm.toMonoidHom

noncomputable def liftAt {H G : Type*} [Group H] [Group G] {m : ℕ} (hm : 2 ≤ m)
    (c : Fin (m + 1)) (κ : normOmega E m →* G) (α : H →* normOmega E (m + 1))
    (hα : α.range ≤ (normDel E hm c).range) : H →* G :=
  (chartLift E hm c κ).comp (α.codRestrict _ fun x => hα ⟨x, rfl⟩)

theorem liftAt_apply {H G : Type*} [Group H] [Group G] {m : ℕ} (hm : 2 ≤ m)
    (c : Fin (m + 1)) (κ : normOmega E m →* G) (α : H →* normOmega E (m + 1))
    (hα : α.range ≤ (normDel E hm c).range) {x : H} {y : normOmega E m}
    (h : α x = normDel E hm c y) :
    liftAt E hm c κ α hα x = κ y := by
  let e : normOmega E m ≃* ↥(normDel E hm c).range :=
    MonoidHom.ofInjective (normDel_injective E hm c)
  have hx : (α.codRestrict (normDel E hm c).range (fun x => hα ⟨x, rfl⟩)) x = e y := by
    apply Subtype.ext
    simp only [e, MonoidHom.codRestrict_apply, MonoidHom.ofInjective_apply]
    exact h
  rw [liftAt, chartLift, MonoidHom.comp_apply, MonoidHom.comp_apply, hx]
  change κ (e.symm (e y)) = κ y
  rw [e.symm_apply_apply]

theorem range_liftAt {H G : Type*} [Group H] [Group G] {m : ℕ} (hm : 2 ≤ m)
    (c : Fin (m + 1)) (κ : normOmega E m →* G) (α : H →* normOmega E (m + 1))
    (hα : α.range ≤ (normDel E hm c).range) :
    (liftAt E hm c κ α hα).range =
      (α.range.comap (normDel E hm c)).map κ := by
  let e : normOmega E m ≃* ↥(normDel E hm c).range :=
    MonoidHom.ofInjective (normDel_injective E hm c)
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    let a : ↥(normDel E hm c).range :=
      (α.codRestrict (normDel E hm c).range (fun x => hα ⟨x, rfl⟩)) x
    let y : normOmega E m := e.symm a
    have ha : (a : normOmega E (m + 1)) = α x := by
      dsimp only [a]
      rw [MonoidHom.codRestrict_apply]
    have hy : (a : normOmega E (m + 1)) = normDel E hm c y := by
      dsimp only [y]
      change (a : normOmega E (m + 1)) = (e (e.symm a) : normOmega E (m + 1))
      exact (congrArg Subtype.val (e.apply_symm_apply a)).symm
    have hxy : α x = normDel E hm c y := ha.symm.trans hy
    refine Subgroup.mem_map.mpr ⟨y, ?_, ?_⟩
    · change normDel E hm c y ∈ α.range
      exact ⟨x, hxy⟩
    · exact (liftAt_apply E hm c κ α hα hxy).symm
  · rintro ⟨y, hy, rfl⟩
    change normDel E hm c y ∈ α.range at hy
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
    exact ⟨x, liftAt_apply E hm c κ α hα hx⟩

theorem liftAt_comp {H H' G : Type*} [Group H] [Group H'] [Group G] {m : ℕ} (hm : 2 ≤ m)
    (c : Fin (m + 1)) (κ : normOmega E m →* G) (α : H →* normOmega E (m + 1))
    (hα : α.range ≤ (normDel E hm c).range) (β : H' →* H) :
    (liftAt E hm c κ α hα).comp β =
      liftAt E hm c κ (α.comp β) (fun _ ⟨x, hx⟩ => hα ⟨β x, hx⟩) :=
  MonoidHom.ext fun _ => rfl

theorem liftAt_injective {H G : Type*} [Group H] [Group G] {m : ℕ} (hm : 2 ≤ m)
    (c : Fin (m + 1)) {κ : normOmega E m →* G} (hκ : Function.Injective κ)
    {α : H →* normOmega E (m + 1)} (hα' : Function.Injective α)
    (hα : α.range ≤ (normDel E hm c).range) : Function.Injective (liftAt E hm c κ α hα) := by
  intro x y hxy
  obtain ⟨u, hu⟩ := hα ⟨x, rfl⟩
  obtain ⟨v, hv⟩ := hα ⟨y, rfl⟩
  rw [liftAt_apply E hm c κ α hα hu.symm, liftAt_apply E hm c κ α hα hv.symm] at hxy
  apply hα'
  rw [← hu, ← hv, hκ hxy]

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
