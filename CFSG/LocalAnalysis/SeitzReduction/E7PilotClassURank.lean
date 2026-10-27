module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassUBruhat

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.SeitzReduction.E6Pilot (rootProd RootCommFamily conjCoeff)
open CFSG.LieType.Chevalley.RootOps (isRootB isRootB_iff)
open scoped commutatorElement Pointwise

local instance e7ClassURankNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

@[expose] def uTopRoot : Fin Tag.E7.rank → ℤ := ![1, 2, 2, 3, 2, 1, 0]

@[expose] def uTop : List (Fin Tag.E7.rank → ℤ) :=
  [![1, 2, 2, 3, 2, 1, 1], ![1, 2, 2, 3, 2, 2, 1], ![1, 2, 2, 3, 3, 2, 1], ![1, 2, 2, 4, 3, 2, 1],
    ![1, 2, 3, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1]]

theorem uTop_check :
    uTop.Nodup ∧ (∀ β ∈ uTop, β ∈ uPsi ∧ β 1 = 2) ∧ isRootB .E7 uTopRoot = true ∧
      uLevel uTopRoot = 0 ∧ height uTopRoot = 11 ∧
      (∀ β ∈ uPsi, isRootB .E7 (uTopRoot + β) = true → uTopRoot + β ∈ uTop) ∧
      (∀ ρ ∈ uTop, ρ - uTopRoot ∈ uPsi) ∧ uTop.sum = 3 • uTopRoot + 2 • uOmega := by
  decide +kernel

theorem uTop_root_check : ∀ k < Tag.E7.rootCertificate.roots.length,
    uLevel (Tag.E7.rootCertificate.root k) ≤ 1 ∧
      (uLevel (Tag.E7.rootCertificate.root k) = 1 → Tag.E7.rootCertificate.root k 1 ≤ 2) ∧
      (uLevel (Tag.E7.rootCertificate.root k) = 1 ∧ Tag.E7.rootCertificate.root k 1 = 2 →
        Tag.E7.rootCertificate.root k ∈ uTop) ∧
      (uLevel (Tag.E7.rootCertificate.root k) = 0 →
        height (Tag.E7.rootCertificate.root k) ≤ 11) := by
  decide +kernel


theorem uTop_root_bounds {ρ : Fin Tag.E7.rank → ℤ} (hρ : IsRoot .E7 ρ) :
    uLevel ρ ≤ 1 ∧ (uLevel ρ = 1 → ρ 1 ≤ 2) ∧ (uLevel ρ = 1 ∧ ρ 1 = 2 → ρ ∈ uTop) ∧
      (uLevel ρ = 0 → height ρ ≤ 11) := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hρ
  exact uTop_root_check k hk

theorem mem_uPsi_of_mem_uTop {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ uTop) : β ∈ uPsi :=
  (uTop_check.2.1 β hβ).1

theorem isRoot_uTopRoot : IsRoot .E7 uTopRoot := isRootB_iff.1 uTop_check.2.2.1

theorem uTop_absorbs {α : Fin Tag.E7.rank → ℤ} (hα : IsRoot .E7 α ∧ 0 < height α)
    {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ uTop) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hr : IsRoot .E7 (a • α + b • β)) : a • α + b • β ∈ uTop := by
  have hnn := (IsRoot.height_pos_iff hα.1).1 hα.2
  have hβ1 := (uTop_check.2.1 β hβ).2
  have hβ6 : β 6 = 1 := level_of_mem_uPsi (mem_uPsi_of_mem_uTop hβ)
  obtain ⟨h1, h2, h3, -⟩ := uTop_root_bounds hr
  have key : ∀ j, (a • α + b • β) j = (a : ℤ) * α j + (b : ℤ) * β j := fun j => by
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, nsmul_eq_mul]
  simp only [uLevel, key] at h1 h2
  have hα6 := hnn 6
  have hα1 := hnn 1
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  rw [hβ6] at h1 h2
  rw [hβ1] at h2
  have hα6z : α 6 = 0 := by nlinarith
  have hbz : (b : ℤ) = 1 := by rw [hα6z] at h1; linarith
  have e6 : (a : ℤ) * α 6 + b * 1 = 1 := by rw [hα6z, hbz]; ring
  have hα1z : α 1 = 0 := by
    have := h2 e6
    rw [hbz] at this
    nlinarith
  refine h3 ⟨?_, ?_⟩
  · simp only [uLevel, key, hβ6, hα6z, hbz]
    ring
  · simp only [key, hβ1, hα1z, hbz]
    ring

section RootProd

variable {K : Type} [Field K]


theorem exists_rootProd_eq_of_mem_rootSpan {τ : Tag} {l : List (Fin τ.rank → ℤ)} (hnd : l.Nodup)
    (hl : RootCommFamily τ K l) {g : ModGL τ K} (hg : g ∈ rootSpan τ K {β | β ∈ l}) :
    ∃ d : (Fin τ.rank → ℤ) → K, g = rootProd τ K l d := by
  let S : Subgroup (ModGL τ K) :=
    { carrier := {g | ∃ d : (Fin τ.rank → ℤ) → K, g = rootProd τ K l d}
      mul_mem' := by
        rintro _ _ ⟨d, rfl⟩ ⟨d', rfl⟩
        exact ⟨d + d', (E6Pilot.rootProd_add hl d d').symm⟩
      one_mem' := ⟨0, (E6Pilot.rootProd_zero l).symm⟩
      inv_mem' := by
        rintro _ ⟨d, rfl⟩
        refine ⟨-d, ?_⟩
        rw [inv_eq_iff_mul_eq_one, ← E6Pilot.rootProd_add hl, add_neg_cancel,
          E6Pilot.rootProd_zero] }
  have hle : rootSpan τ K {β | β ∈ l} ≤ S :=
    iSup₂_le fun β hβ => (closure_le _).2 (by
      rintro _ ⟨t, rfl⟩
      exact ⟨Pi.single β t, (E6Pilot.rootProd_single hnd hβ t).symm⟩)
  exact hle hg

end RootProd

section Groups

variable {K : Type} [Field K]


variable (K) in
@[expose] noncomputable def uTopGroup : Subgroup (ModGL .E7 K) := rootSpan .E7 K {β | β ∈ uTop}

theorem uTop_comm : RootCommFamily .E7 K uTop :=
  uPsi_comm.of_sublist fun _ hβ => mem_uPsi_of_mem_uTop hβ

theorem borelGroup_le_normalizer_uTopGroup :
    borelGroup .E7 K ≤ normalizer (uTopGroup K : Set (ModGL .E7 K)) :=
  sup_le (torusGroup_le_normalizer_rootSpan fun _ hβ =>
      isRoot_of_mem_uPsi (mem_uPsi_of_mem_uTop hβ))
    (posUnipotent_le_normalizer_of_absorbs (fun _ hβ => pos_of_mem_uPsi (mem_uPsi_of_mem_uTop hβ))
      fun _ hα _ hβ _ _ ha hb hr => uTop_absorbs hα hβ ha hb hr)

theorem uHeight_add (u v : Fin Tag.E7.rank → ℤ) : height (u + v) = height u + height v := by
  simp only [height, Pi.add_apply, Finset.sum_add_distrib]

@[expose] def uTopInv (β : Fin Tag.E7.rank → ℤ) (c : (Fin Tag.E7.rank → ℤ) → K) : Prop :=
  c β ≠ 0 ∧ ∀ ρ ∈ uPsi, height ρ < height β → c ρ = 0

theorem borelGroup_le_uInvSubgroup_uTopInv [CharP K 2] {β : Fin Tag.E7.rank → ℤ}
    (hβ : β ∈ uPsi) : borelGroup .E7 K ≤ uInvSubgroup K (uTopInv β) := by
  refine sup_le (torusGroup_le_uInvSubgroup fun g hg c hc => ⟨?_, fun ρ hρ hlt => ?_⟩)
    (rootSpan_le_uInvSubgroup fun α hα t => pinnedX_mem_uInvSubgroup (fun t c hc =>
      ⟨_, conj_rootProd_uPsi hα.1 (uLevel_nonneg_of_pos hα) t c, ?_⟩) t)
  · exact mul_ne_zero (torusRootChar_ne_zero (torusGroup_le_diagonalGroup hg) β) hc.1
  · show torusRootChar g ρ * c ρ = 0
    rw [hc.2 ρ hρ hlt, mul_zero]
  · have hfeed : ∀ ρ ∈ uPsi, height ρ ≤ height β → conjCoeff α t uPsi c ρ = c ρ :=
      fun ρ hρ hle => E6Pilot.conjCoeff_apply_of_forall uPsi_nodup t c hρ fun β' hβ' he =>
        hc.2 β' hβ' (by
          have h1 : height ρ = height α + height β' := by rw [← he, uHeight_add]
          have h2 := hα.2
          omega)
    exact ⟨by rw [hfeed β hβ le_rfl]; exact hc.1, fun ρ hρ hlt => by
      rw [hfeed ρ hρ hlt.le]; exact hc.2 ρ hρ hlt⟩

theorem smul_mem_uTop_of_mem_normalizer [CharP K 2] {g : ModGL .E7 K} {w : WeylGroup .E7}
    (hw : g ∈ bruhatCell .E7 K w) (hgN : g ∈ normalizer (uTopGroup K : Set (ModGL .E7 K))) :
    ∀ β ∈ uTop, w • β ∈ uTop := by
  intro β hβ
  have hβΨ := mem_uPsi_of_mem_uTop hβ
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw
  have hinit : uTopInv β (Pi.single β (1 : K)) := ⟨by simp, fun ρ _ hlt => by
    rw [Pi.single_eq_of_ne (by rintro rfl; exact lt_irrefl _ hlt)]⟩
  obtain ⟨⟨c, ec, hc⟩, -⟩ := borelGroup_le_uInvSubgroup_uTopInv hβΨ hb' _ hinit
  rw [E6Pilot.rootProd_single uPsi_nodup hβΨ] at ec
  have hx : pinnedX .E7 K β 1 ∈ uTopGroup K := pinnedX_mem_rootSpan hβ 1
  have hmem : canonicalRep (coxeterSystem .E7) K w * rootProd .E7 K uPsi c *
      (canonicalRep (coxeterSystem .E7) K w)⁻¹ ∈ uTopGroup K := by
    rw [← ec]
    have e : canonicalRep (coxeterSystem .E7) K w * (b' * pinnedX .E7 K β 1 * b'⁻¹) *
        (canonicalRep (coxeterSystem .E7) K w)⁻¹ =
        b⁻¹ * ((b * canonicalRep (coxeterSystem .E7) K w * b') * pinnedX .E7 K β 1 *
          (b * canonicalRep (coxeterSystem .E7) K w * b')⁻¹) * b⁻¹⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 (borelGroup_le_normalizer_uTopGroup (inv_mem hb)) _).1
      ((mem_normalizer_iff.1 hgN _).1 hx)
  obtain ⟨d, hd⟩ := exists_rootProd_eq_of_mem_rootSpan uTop_check.1 uTop_comm hmem
  rw [canonicalRep_mul_rootProd_uPsi] at hd
  have hLnd : (uPsi.map fun β => w • β).Nodup := uPsi_nodup.map (MulAction.injective w)
  have hLr : ∀ ρ ∈ uPsi.map (fun β => w • β), IsRoot .E7 ρ := by
    intro ρ hρ
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hρ
    exact IsRoot.smul (isRoot_of_mem_uPsi hγ) w
  exact (E6Pilot.mem_and_eq_of_rootProd_eq hLnd hLr (uPsi_map_comm w) uTop_check.1
    (fun _ hρ => pos_of_mem_uPsi (mem_uPsi_of_mem_uTop hρ)) uTop_comm hd
    (List.mem_map_of_mem hβΨ) (by simp only [inv_smul_smul]; exact hc.1)).1

theorem smul_uOmega_of_mem_parabolicWeylGroup {w : WeylGroup .E7}
    (hw : w ∈ parabolicWeylGroup .E7 uNodes) : w • uOmega = uOmega := by
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    rw [simple_smul, reflect_uOmega i hi]
  | one => rw [one_smul]
  | mul x y _ _ hx hy => rw [mul_smul, hy, hx]
  | inv x _ hx => rw [inv_smul_eq_iff, hx]

theorem smul_uTopRoot_eq {w : WeylGroup .E7} (hwJ : w ∈ parabolicWeylGroup .E7 uNodes)
    (h : ∀ β ∈ uTop, w • β ∈ uTop) : w • uTopRoot = uTopRoot := by
  have hnd : (uTop.map (w • ·)).Nodup := uTop_check.1.map (MulAction.injective w)
  have hsub : uTop.map (w • ·) ⊆ uTop := fun β hβ => by
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hβ
    exact h γ hγ
  have hperm : (uTop.map (w • ·)).Perm uTop :=
    (List.subperm_of_subset hnd hsub).perm_of_length_le (by rw [List.length_map])
  have hsum : w • uTop.sum = uTop.sum := by rw [List.smul_sum, hperm.sum_eq]
  rw [uTop_check.2.2.2.2.2.2.2, smul_add, smul_comm w (3 : ℕ), smul_comm w (2 : ℕ),
    smul_uOmega_of_mem_parabolicWeylGroup hwJ] at hsum
  have h3 : (3 : ℕ) • (w • uTopRoot) = (3 : ℕ) • uTopRoot := add_right_cancel hsum
  funext j
  have := congrFun h3 j
  simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at this
  omega

theorem mem_normalizer_rootSubgroup_uTopRoot_of_mem_torus_mul {t : ModGL .E7 K}
    (ht : t ∈ (torusGroup .E7 K : Set (ModGL .E7 K)) *
      (parabolicLeviUnipotent .E7 K uNodes : Set (ModGL .E7 K))) :
    t ∈ normalizer (rootSubgroup .E7 K uTopRoot : Set (ModGL .E7 K)) := by
  obtain ⟨h, hh, v, hv, rfl⟩ := ht
  have hspan : rootSpan .E7 K {uTopRoot} = rootSubgroup .E7 K uTopRoot :=
    le_antisymm (iSup₂_le fun α hα => by rw [Set.mem_singleton_iff.1 hα])
      (le_iSup₂_of_le uTopRoot (Set.mem_singleton _) le_rfl)
  refine mul_mem ?_ ?_
  · have hN := torusGroup_le_normalizer_rootSpan (K := K) (S := {uTopRoot})
      (fun _ hα => by rw [Set.mem_singleton_iff.1 hα]; exact isRoot_uTopRoot) hh
    rwa [hspan] at hN
  · have hc : parabolicLeviUnipotent .E7 K uNodes ≤
        centralizer (rootSubgroup .E7 K uTopRoot : Set (ModGL .E7 K)) := by
      refine iSup₂_le fun α hα => (closure_le _).2 ?_
      rintro _ ⟨s, rfl⟩
      obtain ⟨⟨hαr, hα0⟩, -, hαpos⟩ := hα
      have hα6 : α 6 = 0 := hα0 6 (by simp [uNodes])
      have hsub : rootSubgroup .E7 K uTopRoot ≤
          centralizer ({pinnedX .E7 K α s} : Set (ModGL .E7 K)) := by
        refine (closure_le _).2 ?_
        rintro _ ⟨t, rfl⟩
        refine mem_centralizer_singleton_iff.2 (CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv
          isRoot_uTopRoot hαr (fun he => ?_) (fun hr => ?_) t s).eq
        · have h1 : height uTopRoot = -height α := by rw [he, height_neg]
          rw [uTop_check.2.2.2.2.1] at h1
          omega
        · have hb := (uTop_root_bounds hr).2.2.2
          have hlev : uLevel (uTopRoot + α) = 0 := by
            rw [uLevel_add, uTop_check.2.2.2.1]
            simpa [uLevel] using hα6
          have := hb hlev
          rw [uHeight_add, uTop_check.2.2.2.2.1] at this
          omega
      rw [SetLike.mem_coe, mem_centralizer_iff]
      intro y hy
      exact mem_centralizer_singleton_iff.1 (hsub hy)
    rw [mem_normalizer_iff]
    intro y
    have hvc := mem_centralizer_iff.1 (hc hv)
    constructor
    · intro hy
      rw [← hvc y hy, mul_inv_cancel_right]
      exact hy
    · intro hy
      have e : y = v * y * v⁻¹ := by
        have := hvc (v * y * v⁻¹) hy
        calc y = v⁻¹ * (v * y * v⁻¹) * v := by group
          _ = v⁻¹ * (v * (v * y * v⁻¹)) := by rw [mul_assoc, this, ← mul_assoc]
          _ = v * y * v⁻¹ := by group
      rw [e]
      exact hy

theorem mem_normalizer_rootSubgroup_uTopRoot_of_mem_bruhatCell {g : ModGL .E7 K}
    {w : WeylGroup .E7} (hw : g ∈ bruhatCell .E7 K w) (hwJ : w ∈ parabolicWeylGroup .E7 uNodes)
    (hwr : w • uTopRoot = uTopRoot) (hgM : g ∈ parabolicLevi .E7 K uNodes) :
    g ∈ normalizer (rootSubgroup .E7 K uTopRoot : Set (ModGL .E7 K)) := by
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw
  have hnM : canonicalRep (coxeterSystem .E7) K w ∈ parabolicLevi .E7 K uNodes :=
    canonicalRep_mem_parabolicLevi hwJ
  have hnN : canonicalRep (coxeterSystem .E7) K w ∈
      normalizer (rootSubgroup .E7 K uTopRoot : Set (ModGL .E7 K)) := by
    rw [mem_normalizer_iff_map_conj_eq]
    have h := (canonical_weyl_root_transport .E7 K).2.1 w _ isRoot_uTopRoot
    rw [hwr] at h
    exact h
  have hB := borelGroup_eq_mul_parabolic (τ := .E7) (K := K) uNodes
  have hb1 : b ∈ (parabolicRadical .E7 K uNodes : Set (ModGL .E7 K)) *
      ((torusGroup .E7 K : Set (ModGL .E7 K)) *
        (parabolicLeviUnipotent .E7 K uNodes : Set (ModGL .E7 K))) := by
    rw [← hB]
    exact hb
  have hb2 : b' ∈ (parabolicRadical .E7 K uNodes : Set (ModGL .E7 K)) *
      ((torusGroup .E7 K : Set (ModGL .E7 K)) *
        (parabolicLeviUnipotent .E7 K uNodes : Set (ModGL .E7 K))) := by
    rw [← hB]
    exact hb'
  obtain ⟨q₁, hq₁, t₁, ht₁, rfl⟩ := hb1
  obtain ⟨q₂, hq₂, t₂, ht₂, rfl⟩ := hb2
  have htM : ∀ t ∈ (torusGroup .E7 K : Set (ModGL .E7 K)) *
      (parabolicLeviUnipotent .E7 K uNodes : Set (ModGL .E7 K)),
      t ∈ parabolicLevi .E7 K uNodes := by
    rintro _ ⟨h, hh, v, hv, rfl⟩
    exact mul_mem (torusGroup_le_parabolicLevi uNodes hh)
      (parabolicLeviUnipotent_le_parabolicLevi uNodes hv)
  have hMN : parabolicLevi .E7 K uNodes ≤
      normalizer (parabolicRadical .E7 K uNodes : Set (ModGL .E7 K)) :=
    (parabolicLevi_le_parabolicSubgroup uNodes).trans
      (parabolicSubgroup_le_normalizer_parabolicRadical uNodes)
  set n := canonicalRep (coxeterSystem .E7) K w with hn
  have hm : t₁ * n * t₂ ∈ parabolicLevi .E7 K uNodes :=
    mul_mem (mul_mem (htM t₁ ht₁) hnM) (htM t₂ ht₂)
  have hq : q₁ * ((t₁ * n) * q₂ * (t₁ * n)⁻¹) ∈ parabolicRadical .E7 K uNodes :=
    mul_mem hq₁ ((mem_normalizer_iff.1 (hMN (mul_mem (htM t₁ ht₁) hnM)) q₂).1 hq₂)
  have e : q₁ * t₁ * n * (q₂ * t₂) = (q₁ * ((t₁ * n) * q₂ * (t₁ * n)⁻¹)) * (t₁ * n * t₂) := by
    group
  have hqM : q₁ * ((t₁ * n) * q₂ * (t₁ * n)⁻¹) ∈ parabolicLevi .E7 K uNodes := by
    have e' : q₁ * ((t₁ * n) * q₂ * (t₁ * n)⁻¹) =
        (q₁ * t₁ * n * (q₂ * t₂)) * (t₁ * n * t₂)⁻¹ := by
      rw [e]
      group
    rw [e']
    exact mul_mem hgM (inv_mem hm)
  have h1 : q₁ * ((t₁ * n) * q₂ * (t₁ * n)⁻¹) = 1 := by
    have := mem_inf.2 ⟨hq, hqM⟩
    rwa [parabolicRadical_inf_parabolicLevi uNodes, mem_bot] at this
  rw [e, h1, one_mul]
  exact mul_mem (mul_mem (mem_normalizer_rootSubgroup_uTopRoot_of_mem_torus_mul ht₁) hnN)
    (mem_normalizer_rootSubgroup_uTopRoot_of_mem_torus_mul ht₂)

theorem mem_normalizer_rootSubgroup_of_mem_normalizer_uTopGroup [CharP K 2] {g : ModGL .E7 K}
    (hgC : g ∈ adjointGroup .E7 K) (hgM : g ∈ parabolicLevi .E7 K uNodes)
    (hgN : g ∈ normalizer (uTopGroup K : Set (ModGL .E7 K))) :
    g ∈ normalizer (rootSubgroup .E7 K uTopRoot : Set (ModGL .E7 K)) := by
  obtain ⟨w, hw⟩ := CFSG.SeitzReduction.exists_mem_bruhatCell_of_mem_adjointGroup hgC
  have hwJ : w ∈ parabolicWeylGroup .E7 uNodes := by
    have hgP : g ∈ (parabolicSubgroup .E7 K uNodes : Set (ModGL .E7 K)) :=
      parabolicLevi_le_parabolicSubgroup uNodes hgM
    rw [(standard_parabolic_cells .E7 K).1 uNodes] at hgP
    obtain ⟨w', hw'J, hgw'⟩ := Set.mem_iUnion₂.1 hgP
    by_contra hne
    have hne' : w ≠ w' := fun h => hne (h ▸ hw'J)
    exact Set.disjoint_left.1 ((standard_parabolic_cells .E7 K).2.1 w w' hne') hw hgw'
  exact mem_normalizer_rootSubgroup_uTopRoot_of_mem_bruhatCell hw hwJ
    (smul_uTopRoot_eq hwJ (smul_mem_uTop_of_mem_normalizer hw hgN)) hgM

theorem mem_parabolicRadicalRoots_of_mem_uPsi {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ uPsi) :
    β ∈ parabolicRadicalRoots .E7 uNodes :=
  mem_parabolicRadicalRoots_iff.2 ⟨isRoot_of_mem_uPsi hβ, (pos_of_mem_uPsi hβ).2, 6,
    by simp [uNodes], by rw [show β 6 = uLevel β from rfl, level_of_mem_uPsi hβ]; exact one_ne_zero⟩

theorem rootProd_uPsi_mem_uTopGroup {d : (Fin Tag.E7.rank → ℤ) → K}
    (hd : ∀ β ∈ uPsi, β ∉ uTop → d β = 0) : rootProd .E7 K uPsi d ∈ uTopGroup K := by
  refine list_prod_mem fun x hx => ?_
  obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx
  by_cases hβT : β ∈ uTop
  · exact pinnedX_mem_rootSpan hβT _
  · rw [hd β hβ hβT, pinnedX_zero]
    exact one_mem _

theorem commutator_parabolicRadical_rootSubgroup_le [CharP K 2] :
    ⁅parabolicRadical .E7 K uNodes, rootSubgroup .E7 K uTopRoot⁆ ≤ uTopGroup K := by
  rw [commutator_le]
  intro q hq x hx
  have hle : parabolicRadical .E7 K uNodes ≤ rootSpan .E7 K {β | β ∈ uPsi} :=
    iSup₂_le fun α hα => le_iSup₂_of_le (f := fun β (_ : β ∈ {β | β ∈ uPsi}) =>
      rootSubgroup .E7 K β) α (mem_uPsi_of_mem_parabolicRadicalRoots hα) le_rfl
  have hqΨ : q ∈ rootSpan .E7 K {β | β ∈ uPsi} := hle hq
  obtain ⟨c, rfl⟩ := exists_rootProd_eq_of_mem_rootSpan uPsi_nodup uPsi_comm hqΨ
  obtain ⟨t, rfl⟩ := mem_rootSubgroup.1 hx
  have hinv : (rootProd .E7 K uPsi c)⁻¹ = rootProd .E7 K uPsi (-c) := by
    rw [inv_eq_iff_mul_eq_one, ← E6Pilot.rootProd_add uPsi_comm, add_neg_cancel,
      E6Pilot.rootProd_zero]
  have e : ⁅rootProd .E7 K uPsi c, pinnedX .E7 K uTopRoot t⁆ =
      rootProd .E7 K uPsi (c + conjCoeff uTopRoot t uPsi (-c)) := by
    rw [commutatorElement_def, E6Pilot.rootProd_add uPsi_comm,
      ← conj_rootProd_uPsi isRoot_uTopRoot (by rw [uTop_check.2.2.2.1]) t (-c), ← hinv]
    group
  rw [e]
  refine rootProd_uPsi_mem_uTopGroup fun ρ hρ hρT => ?_
  have hfeed : conjCoeff uTopRoot t uPsi (-c) ρ = (-c) ρ :=
    E6Pilot.conjCoeff_apply_of_forall uPsi_nodup t (-c) hρ fun β hβ he => by
      exfalso
      apply hρT
      rw [← he]
      exact uTop_check.2.2.2.2.2.1 β hβ (isRootB_iff.2 (he ▸ isRoot_of_mem_uPsi hρ))
  rw [Pi.add_apply, hfeed, Pi.neg_apply, add_neg_cancel]

theorem uTopGroup_le_commutator_zpowers [CharP K 2] {t : K} (ht : t ≠ 0) :
    uTopGroup K ≤ ⁅parabolicRadical .E7 K uNodes, zpowers (pinnedX .E7 K uTopRoot t)⁆ := by
  refine iSup₂_le fun ρ hρ => (closure_le _).2 ?_
  rintro _ ⟨s, rfl⟩
  have hρ' : ρ ∈ uTop := hρ
  have ha := mem_uPsi_of_mem_uTop hρ'
  have hd := uTop_check.2.2.2.2.2.2.1 ρ hρ'
  have hlev : uLevel (ρ - uTopRoot) = 1 := level_of_mem_uPsi hd
  have hlev0 : uLevel uTopRoot = 0 := uTop_check.2.2.2.1
  have hne : ρ - uTopRoot ≠ uTopRoot := fun h => by rw [h] at hlev; omega
  have hne' : ρ - uTopRoot ≠ -uTopRoot := fun h => by rw [h, uLevel_neg] at hlev; omega
  have hsum : ρ - uTopRoot + uTopRoot = ρ := by abel
  have hc := CFSG.SeitzReduction.commutatorElement_pinnedX_of_oddDerivLaced (R := K)
    CharTwo.two_eq_zero
    (CFSG.SeitzReduction.oddDerivLacedCheck_of_simplyLaced (Or.inr (Or.inr (Or.inl rfl))))
    (isRoot_of_mem_uPsi hd) isRoot_uTopRoot hne hne'
    (by rw [hsum]; exact isRoot_of_mem_uPsi ha) (s / t) t
  rw [hsum, div_mul_cancel₀ s ht] at hc
  rw [SetLike.mem_coe, ← hc]
  exact commutator_mem_commutator
    (pinnedX_mem_rootSpan (mem_parabolicRadicalRoots_of_mem_uPsi hd) _) (mem_zpowers _)

theorem commutator_parabolicRadical_rootSubgroup_uTopRoot [CharP K 2] :
    ⁅parabolicRadical .E7 K uNodes, rootSubgroup .E7 K uTopRoot⁆ = uTopGroup K := by
  refine le_antisymm commutator_parabolicRadical_rootSubgroup_le
    ((uTopGroup_le_commutator_zpowers one_ne_zero).trans (commutator_mono le_rfl ?_))
  rw [zpowers_le]
  exact mem_rootSubgroup.2 ⟨1, rfl⟩

theorem commutator_parabolicRadical_zpowers_eq [CharP K 2] {x : ModGL .E7 K}
    (hx : x ∈ rootSubgroup .E7 K uTopRoot) (hx1 : x ≠ 1) :
    ⁅parabolicRadical .E7 K uNodes, zpowers x⁆ = uTopGroup K := by
  obtain ⟨t, rfl⟩ := mem_rootSubgroup.1 hx
  have ht : t ≠ 0 := by
    rintro rfl
    exact hx1 (pinnedX_zero .E7 K _)
  refine le_antisymm ?_ (uTopGroup_le_commutator_zpowers ht)
  rw [← commutator_parabolicRadical_rootSubgroup_uTopRoot]
  exact commutator_mono le_rfl ((zpowers_le).2 hx)

end Groups

end CFSG.SeitzReduction.E7Pilot
