module

public import CFSG.LieType.SpecialLinear.Block222.Trivial
public import CFSG.LieType.SpecialLinear.Block222.Section

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.SpecialLinear
  CFSG.LieType.RootSystem CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open scoped MatrixGroups

noncomputable section

variable (c : ℕ) (F : Type) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

omit [Finite F] in
private theorem one_sl_diag {n : ℕ} (i : Fin n) :
    ((1 : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i i = 1 := by
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq]

omit [Finite F] in
private theorem one_sl_off {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    ((1 : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0 := by
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne h]

theorem blockEmbed222_mem_U_left {u : SpecialLinearGroup (Fin 2) F}
    (hu : u ∈ (curtisDatum 1 F p).U) :
    blockEmbed222 c F (u, 1, 1) ∈ (curtisDatum (c + 3) F p).U := by
  have hu' := (mem_curtisDatum_U_iff (m := 1) (F := F) (p := p)).mp hu
  exact blockEmbed222_mem_U_of_entries c F p hu'.1 hu'.2 (fun i => one_sl_diag F i)
    (fun i j hji => one_sl_off F (ne_of_gt hji)) (fun i => one_sl_diag F i)
    (fun i j hji => one_sl_off F (ne_of_gt hji))

theorem blockEmbed222_mem_U_right {u : SpecialLinearGroup (Fin 2) F}
    (hu : u ∈ (curtisDatum 1 F p).U) :
    blockEmbed222 c F (1, 1, u) ∈ (curtisDatum (c + 3) F p).U := by
  have hu' := (mem_curtisDatum_U_iff (m := 1) (F := F) (p := p)).mp hu
  exact blockEmbed222_mem_U_of_entries c F p (fun i => one_sl_diag F i)
    (fun i j hji => one_sl_off F (ne_of_gt hji)) (fun i => one_sl_diag F i)
    (fun i j hji => one_sl_off F (ne_of_gt hji)) hu'.1 hu'.2

theorem blockEmbed222_mem_H_left {u : SpecialLinearGroup (Fin 2) F}
    (hu : u ∈ (curtisDatum 1 F p).H) :
    blockEmbed222 c F (u, 1, 1) ∈ (curtisDatum (c + 3) F p).H := by
  have hu' := (mem_curtisDatum_H_iff (m := 1) (F := F) (p := p)).mp hu
  exact blockEmbed222_mem_H_of_entries c F p hu'
    (fun i j hij => one_sl_off F hij) (fun i j hij => one_sl_off F hij)

theorem blockEmbed222_mem_H_right {u : SpecialLinearGroup (Fin 2) F}
    (hu : u ∈ (curtisDatum 1 F p).H) :
    blockEmbed222 c F (1, 1, u) ∈ (curtisDatum (c + 3) F p).H := by
  have hu' := (mem_curtisDatum_H_iff (m := 1) (F := F) (p := p)).mp hu
  exact blockEmbed222_mem_H_of_entries c F p (fun i j hij => one_sl_off F hij)
    (fun i j hij => one_sl_off F hij) hu'

theorem heckeT_comp_left {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (SpecialLinearGroup (Fin (c + 4)) F) V) (s : Fin 1) (v : V) :
    (curtisDatum 1 F p).heckeT ((ρ.comp (blockEmbed222 c F)).comp (leftHom222 c F)) s v =
      (curtisDatum (c + 3) F p).heckeT ρ (⟨0, by omega⟩ : Fin (c + 3)) v :=
  heckeT_comp_of F p (m := 1) (n := c + 3)
    (φ := (blockEmbed222 c F).comp (leftHom222 c F)) (ι := fun _ => ⟨0, by omega⟩)
    (fun s x => by
      rw [Fin.eq_zero s]
      exact blockEmbed222_rankOne_x_left (c := c) (F := F) (p := p) x)
    (fun s => by
      rw [Fin.eq_zero s]
      exact blockEmbed222_n_left (c := c) (F := F) (p := p)) ρ s v

theorem heckeT_comp_right {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (SpecialLinearGroup (Fin (c + 4)) F) V) (s : Fin 1) (v : V) :
    (curtisDatum 1 F p).heckeT ((ρ.comp (blockEmbed222 c F)).comp (rightHom222 c F)) s v =
      (curtisDatum (c + 3) F p).heckeT ρ (⟨c + 2, by omega⟩ : Fin (c + 3)) v :=
  heckeT_comp_of F p (m := 1) (n := c + 3)
    (φ := (blockEmbed222 c F).comp (rightHom222 c F)) (ι := fun _ => ⟨c + 2, by omega⟩)
    (fun s x => by
      rw [Fin.eq_zero s]
      exact blockEmbed222_rankOne_x_right (c := c) (F := F) (p := p) x)
    (fun s => by
      rw [Fin.eq_zero s]
      exact blockEmbed222_n_right (c := c) (F := F) (p := p)) ρ s v

private theorem coverId_datum_heckeT_eq (m : ℕ) {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] (ρ : Representation k (SpecialLinearGroup (Fin (m + 1)) F) V)
    (s : Fin m) (v : V) :
    (coverId m F p).datum.heckeT ρ s v = (curtisDatum m F p).heckeT ρ s v := by
  let : Fintype ↥((coverId m F p).datum.X s) := Fintype.ofFinite _
  let : Fintype ↥((curtisDatum m F p).X s) := Fintype.ofFinite _
  rw [CurtisDatum.heckeT_apply, CurtisDatum.heckeT_apply]
  let e : ↥((coverId m F p).datum.X s) ≃ ↥((curtisDatum m F p).X s) :=
    (coverId m F p).lXEquiv s
  refine Fintype.sum_equiv e _ _ ?_
  intro x
  have hx : ((e x : ↥((curtisDatum m F p).X s)) : SpecialLinearGroup (Fin (m + 1)) F) =
      (x : SpecialLinearGroup (Fin (m + 1)) F) := rfl
  have hn : (coverId m F p).datum.n s = (curtisDatum m F p).n s := by
    change (coverId m F p).nhat s = (curtisDatum m F p).n s
    rw [CentralCoverData.nhat]
    have h := (coverId m F p).map_nhatW ((curtisCoxeterSystem m).simple s)
    simp only [MonoidHom.id_apply] at h
    rw [h, CentralCoverData.nW_simple]
  rw [hx, hn]

omit [Fact (Nat.Prime p)] in
private theorem coe_heckeT_restrictRep (m : ℕ) {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] (ρ : Representation k (SpecialLinearGroup (Fin (m + 1)) F) V)
    (W : Submodule k V) (hW : ∀ g : SpecialLinearGroup (Fin (m + 1)) F, ∀ w ∈ W, ρ g w ∈ W)
    (s : Fin m) (v : W) :
    (((curtisDatum m F p).heckeT (restrictRep ρ W hW) s v : W) : V) =
      (curtisDatum m F p).heckeT ρ s v := by
  let : Fintype ↥((curtisDatum m F p).X s) := Fintype.ofFinite _
  rw [CurtisDatum.heckeT_apply, CurtisDatum.heckeT_apply]
  simp only [Submodule.coe_sum]
  exact Finset.sum_congr rfl fun x _ => rfl

@[expose] noncomputable def factor1Rep {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (SpecialLinearGroup (Fin (c + 4)) F) V) :
    Representation k (SpecialLinearGroup (Fin 2) F) (blockFix222 c F ρ) :=
  (blockRestrict222 c F ρ).comp (leftHom222 c F)

@[expose] noncomputable def factor3Rep {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (SpecialLinearGroup (Fin (c + 4)) F) V) :
    Representation k (SpecialLinearGroup (Fin 2) F) (blockFix222 c F ρ) :=
  (blockRestrict222 c F ρ).comp (rightHom222 c F)

private theorem coe_heckeT_factor1 {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k (SpecialLinearGroup (Fin (c + 4)) F) V} {y : V}
    {χ : SpecialLinearGroup (Fin (c + 4)) F → k} {J : Finset (Fin (c + 3))}
    (ht : IsCoverType (rankOne (c + 3) F p) ρ y χ J) (s : Fin 1) :
    (((coverId 1 F p).datum.heckeT (factor1Rep c F ρ) s
        ⟨y, mem_blockFix222_of_isCoverType c F p ht⟩ : blockFix222 c F ρ) : V) =
      (coverId (c + 3) F p).datum.heckeT ρ (⟨0, by omega⟩ : Fin (c + 3)) y := by
  rw [coverId_datum_heckeT_eq (m := 1) (F := F) (p := p)]
  have hrep : factor1Rep c F ρ =
      restrictRep ((ρ.comp (blockEmbed222 c F)).comp (leftHom222 c F))
        (blockFix222 c F ρ)
        (fun g w hw => blockFix222_stable c F ρ (leftHom222 c F g) w hw) := by
    ext g w
    rfl
  rw [hrep, coe_heckeT_restrictRep]
  rw [heckeT_comp_left c F p]
  rw [← coverId_datum_heckeT_eq (m := c + 3) (F := F) (p := p)]

theorem factor1_isCoverType {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k (SpecialLinearGroup (Fin (c + 4)) F) V} {y : V}
    {χ : SpecialLinearGroup (Fin (c + 4)) F → k} {J : Finset (Fin (c + 3))}
    (ht : IsCoverType (rankOne (c + 3) F p) ρ y χ J) :
    IsCoverType (rankOne 1 F p) (factor1Rep c F ρ)
      ⟨y, mem_blockFix222_of_isCoverType c F p ht⟩
      (fun g : SpecialLinearGroup (Fin 2) F => χ (blockEmbed222 c F (g, 1, 1)))
      (Finset.univ.filter fun _ : Fin 1 => (⟨0, by omega⟩ : Fin (c + 3)) ∈ J) := by
  let hyW := mem_blockFix222_of_isCoverType c F p ht
  unfold IsCoverType
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [CurtisDatum.mem_fixU]
    intro u hu
    apply Subtype.ext
    change ρ (blockEmbed222 c F (u, 1, 1)) y = y
    have hu' : u ∈ (curtisDatum 1 F p).U := by
      rwa [coverId_datum_U 1 F p] at hu
    have huB : blockEmbed222 c F (u, 1, 1) ∈ (curtisDatum (c + 3) F p).U :=
      blockEmbed222_mem_U_left c F p hu'
    have hyU := ht.1
    rw [CurtisDatum.mem_fixU] at hyU
    rw [coverId_datum_U (c + 3) F p] at hyU
    exact hyU _ huB
  · intro h
    exact ht.2.1 (congrArg Subtype.val h)
  · intro h hh
    apply Subtype.ext
    change ρ (blockEmbed222 c F (h, 1, 1)) y = χ (blockEmbed222 c F (h, 1, 1)) • y
    have hh' : h ∈ (curtisDatum 1 F p).H := by
      rwa [Subgroup.comap_id] at hh
    have hhB : blockEmbed222 c F (h, 1, 1) ∈ (curtisDatum (c + 3) F p).H :=
      blockEmbed222_mem_H_left c F p hh'
    have hchar := ht.2.2.1
    rw [Subgroup.comap_id] at hchar
    exact hchar _ hhB
  · intro s
    rw [Fin.eq_zero s]
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    have hcoeeq := coe_heckeT_factor1 c F p ht (0 : Fin 1)
    have hiff : ((coverId 1 F p).datum.heckeT (factor1Rep c F ρ) (0 : Fin 1)
        ⟨y, hyW⟩ = 0) ↔
        ((coverId (c + 3) F p).datum.heckeT ρ (⟨0, by omega⟩ : Fin (c + 3)) y = 0) := by
      constructor
      · intro h
        rw [← hcoeeq, h]
        rfl
      · intro h
        apply Subtype.ext
        rw [hcoeeq, h]
        rfl
    constructor
    · intro hs
      have hbig := (ht.2.2.2 (⟨0, by omega⟩ : Fin (c + 3))).mp hs
      refine ⟨?_, hiff.mpr hbig.2⟩
      intro u
      have h : χ (hdiag (c + 3) F (⟨0, by omega⟩ : Fin (c + 3)) u) = 1 := hbig.1 u
      rw [← blockEmbed222_hdiag_left (c := c) (F := F) u] at h
      exact h
    · intro hs
      apply (ht.2.2.2 (⟨0, by omega⟩ : Fin (c + 3))).mpr
      refine ⟨?_, hiff.mp hs.2⟩
      intro u
      have h : χ (blockEmbed222 c F (hdiag 1 F (0 : Fin 1) u, 1, 1)) = 1 := hs.1 u
      rw [blockEmbed222_hdiag_left (c := c) (F := F) u] at h
      exact h

private theorem coe_heckeT_factor3 {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k (SpecialLinearGroup (Fin (c + 4)) F) V} {y : V}
    {χ : SpecialLinearGroup (Fin (c + 4)) F → k} {J : Finset (Fin (c + 3))}
    (ht : IsCoverType (rankOne (c + 3) F p) ρ y χ J) (s : Fin 1) :
    (((coverId 1 F p).datum.heckeT (factor3Rep c F ρ) s
        ⟨y, mem_blockFix222_of_isCoverType c F p ht⟩ : blockFix222 c F ρ) : V) =
      (coverId (c + 3) F p).datum.heckeT ρ (⟨c + 2, by omega⟩ : Fin (c + 3)) y := by
  rw [coverId_datum_heckeT_eq (m := 1) (F := F) (p := p)]
  have hrep : factor3Rep c F ρ =
      restrictRep ((ρ.comp (blockEmbed222 c F)).comp (rightHom222 c F))
        (blockFix222 c F ρ)
        (fun g w hw => blockFix222_stable c F ρ (rightHom222 c F g) w hw) := by
    ext g w
    rfl
  rw [hrep, coe_heckeT_restrictRep]
  rw [heckeT_comp_right c F p]
  rw [← coverId_datum_heckeT_eq (m := c + 3) (F := F) (p := p)]

theorem factor3_isCoverType {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k (SpecialLinearGroup (Fin (c + 4)) F) V} {y : V}
    {χ : SpecialLinearGroup (Fin (c + 4)) F → k} {J : Finset (Fin (c + 3))}
    (ht : IsCoverType (rankOne (c + 3) F p) ρ y χ J) :
    IsCoverType (rankOne 1 F p) (factor3Rep c F ρ)
      ⟨y, mem_blockFix222_of_isCoverType c F p ht⟩
      (fun g : SpecialLinearGroup (Fin 2) F => χ (blockEmbed222 c F (1, 1, g)))
      (Finset.univ.filter fun _ : Fin 1 => (⟨c + 2, by omega⟩ : Fin (c + 3)) ∈ J) := by
  let hyW := mem_blockFix222_of_isCoverType c F p ht
  unfold IsCoverType
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [CurtisDatum.mem_fixU]
    intro u hu
    apply Subtype.ext
    change ρ (blockEmbed222 c F (1, 1, u)) y = y
    have hu' : u ∈ (curtisDatum 1 F p).U := by
      rwa [coverId_datum_U 1 F p] at hu
    have huB : blockEmbed222 c F (1, 1, u) ∈ (curtisDatum (c + 3) F p).U :=
      blockEmbed222_mem_U_right c F p hu'
    have hyU := ht.1
    rw [CurtisDatum.mem_fixU] at hyU
    rw [coverId_datum_U (c + 3) F p] at hyU
    exact hyU _ huB
  · intro h
    exact ht.2.1 (congrArg Subtype.val h)
  · intro h hh
    apply Subtype.ext
    change ρ (blockEmbed222 c F (1, 1, h)) y = χ (blockEmbed222 c F (1, 1, h)) • y
    have hh' : h ∈ (curtisDatum 1 F p).H := by
      rwa [Subgroup.comap_id] at hh
    have hhB : blockEmbed222 c F (1, 1, h) ∈ (curtisDatum (c + 3) F p).H :=
      blockEmbed222_mem_H_right c F p hh'
    have hchar := ht.2.2.1
    rw [Subgroup.comap_id] at hchar
    exact hchar _ hhB
  · intro s
    rw [Fin.eq_zero s]
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    have hcoeeq := coe_heckeT_factor3 c F p ht (0 : Fin 1)
    have hiff : ((coverId 1 F p).datum.heckeT (factor3Rep c F ρ) (0 : Fin 1)
        ⟨y, hyW⟩ = 0) ↔
        ((coverId (c + 3) F p).datum.heckeT ρ (⟨c + 2, by omega⟩ : Fin (c + 3)) y = 0) := by
      constructor
      · intro h
        rw [← hcoeeq, h]
        rfl
      · intro h
        apply Subtype.ext
        rw [hcoeeq, h]
        rfl
    constructor
    · intro hs
      have hbig := (ht.2.2.2 (⟨c + 2, by omega⟩ : Fin (c + 3))).mp hs
      refine ⟨?_, hiff.mpr hbig.2⟩
      intro u
      have h : χ (hdiag (c + 3) F (⟨c + 2, by omega⟩ : Fin (c + 3)) u) = 1 := hbig.1 u
      rw [← blockEmbed222_hdiag_right (c := c) (F := F) u] at h
      exact h
    · intro hs
      apply (ht.2.2.2 (⟨c + 2, by omega⟩ : Fin (c + 3))).mpr
      refine ⟨?_, hiff.mp hs.2⟩
      intro u
      have h : χ (blockEmbed222 c F (1, 1, hdiag 1 F (0 : Fin 1) u)) = 1 := hs.1 u
      rw [blockEmbed222_hdiag_right (c := c) (F := F) u] at h
      exact h

end

end CFSG.LieType.SpecialLinear
