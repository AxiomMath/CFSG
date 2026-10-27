module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.OctadOnto
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.OctadAbelian

public section

namespace CFSG.EvenSporadicStandard.M24Std.Octad

open Subgroup

variable {G : Type} [Group G]

structure YStructB (L B : Subgroup G) (z : G) (Y : Subgroup G) : Prop where
  B_le : B ≤ Y
  le_lam : Y ≤ egLam B z
  z_not_mem : z ∉ Y
  H_inv : ∀ h ∈ egNL L B, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y
  cover : ∀ w ∈ egLam B z, w ∈ Y ∨ z * w ∈ Y

variable [Finite G] {L B : Subgroup G} {z : G}

theorem exists_YStructB (hs : LocalSetting G L z) (hBL : B ≤ L) (hb : OctadBasics L B)
    (hsp : SplitDataB L B) (hcase : ¬ egM B z ≤ centralizer ({z} : Set G)) :
    ∃ Y : Subgroup G, YStructB L B z Y := by
  have hVΛ := egV_le_egLam hs hBL hb.elem.1 (z := z)
  obtain ⟨Y, hBY, hYW, hzY, hHY, hcov⟩ := hsp z (egLam B z) (hVΛ z_mem_egV) (z_mul_self hs)
    (fun h => z_not_mem_L hs (hBL h)) (fun h hh => z_comm hs (mem_inf.1 hh).2)
    (fun u hu => z_comm hs (hBL hu)) (B_le_egV.trans hVΛ)
    (fun w hw u hu => ((mem_egLam.1 hw).2 u hu).symm)
    (fun w hw => mul_self_mem hs hBL hb hcase hw) (fun h hh w hw => conj_mem_egLam hs hBL hh hw)
    (fun w hw => phiB_mem hs hBL (mem_egLam.1 hw).1)
    (fun u hu => exists_phiB_eq hs hBL hb hcase hu)
    (fun w hw hzw => mem_egV_of_comm hs hBL hb hw hzw.symm)
  exact ⟨Y, hBY, hYW, hzY, hHY, hcov⟩

section Y

variable (hs : LocalSetting G L z) (hBL : B ≤ L) (hb : OctadBasics L B) {Y : Subgroup G}
  (hY : YStructB L B z Y)
include hs hBL hb hY

theorem phiB_eq_one_mem {y : G} (hy : y ∈ Y) (h1 : phiB z y = 1) : y ∈ B := by
  have hyV := mem_egV_of_comm hs hBL hb (hY.le_lam hy) ((phiB_eq_one_iff hs).1 h1)
  obtain ⟨b, hbB, h | h⟩ := (mem_egV_iff hs hBL).1 hyV
  · rw [h]; exact hbB
  · exfalso
    apply hY.z_not_mem
    have e : z = b⁻¹ * y := by rw [h]; group
    rw [e]
    exact mul_mem (inv_mem (hY.B_le hbB)) hy

theorem exists_phiB_eq_Y (hcase : ¬ egM B z ≤ centralizer ({z} : Set G)) {b : G}
    (hbB : b ∈ B) : ∃ y ∈ Y, phiB z y = b := by
  obtain ⟨t, ht, htb⟩ := exists_phiB_eq hs hBL hb hcase hbB
  rcases hY.cover t ht with h | h
  · exact ⟨t, h, htb⟩
  · refine ⟨z * t, h, ?_⟩
    have hzΛ : z ∈ egLam B z := egV_le_egLam hs hBL hb.elem.1 z_mem_egV
    rw [phiB_mul hs hBL hb.elem.1 hzΛ ht, (phiB_eq_one_iff hs).2 rfl, one_mul, htb]

theorem card_Y (hcase : ¬ egM B z ≤ centralizer ({z} : Set G)) : Nat.card Y = 256 := by
  let ψ : Y →* G :=
    { toFun := fun y => phiB z y
      map_one' := (phiB_eq_one_iff hs).2 (by simp)
      map_mul' := fun a b => phiB_mul hs hBL hb.elem.1 (hY.le_lam a.2) (hY.le_lam b.2) }
  have hker : ψ.ker = B.subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact ⟨fun h => phiB_eq_one_mem hs hBL hb hY y.2 h, fun h => phiB_eq_one_of_mem hs hBL h⟩
  have hrange : ψ.range = B := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact phiB_mem hs hBL (mem_egLam.1 (hY.le_lam y.2)).1
    · intro hx
      obtain ⟨y, hy, hyx⟩ := exists_phiB_eq_Y hs hBL hb hY hcase hx
      exact ⟨⟨y, hy⟩, hyx⟩
  have := Subgroup.card_ker_mul_card_range ψ
  rw [hker, hrange, Nat.card_congr (subgroupOfEquivOfLe hY.B_le).toEquiv, hb.card_B] at this
  omega

theorem yFactsB_of (hcase : ¬ egM B z ≤ centralizer ({z} : Set G)) :
    YFactsB L B (phiB z) Y where
  B_le := hY.B_le
  central := fun _ hy u hu => ((mem_egLam.1 (hY.le_lam hy)).2 u hu).symm
  sq_mem := fun _ hy => mul_self_mem hs hBL hb hcase (hY.le_lam hy)
  phi_mem := fun _ hy => phiB_mem hs hBL (mem_egLam.1 (hY.le_lam hy)).1
  phi_mul := fun _ hy _ hy' => phiB_mul hs hBL hb.elem.1 (hY.le_lam hy) (hY.le_lam hy')
  phi_ker := fun _ hy h1 => phiB_eq_one_mem hs hBL hb hY hy h1
  phi_surj := fun _ hu => exists_phiB_eq_Y hs hBL hb hY hcase hu
  phi_conj := fun h hh y hy => ⟨hY.H_inv h hh y hy, phiB_conj hs (mem_inf.1 hh).2 y⟩

end Y

end CFSG.EvenSporadicStandard.M24Std.Octad
