module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47fTable
public import CFSG.LieType.Chevalley.GraphFixedOrbitCollection

public noncomputable section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk47

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

theorem eq_zero_of_sign_mul' {K : Type} [Field K] {e x : K} (he : e = 1 ∨ e = -1)
    (h : e * x = 0) : x = 0 := by
  rcases he with rfl | rfl <;> simpa using h

@[expose] def rootsUVBC : Fin 4 → (Fin Tag.G2.rank → ℤ) := ![![1, 1], ![1, 2], ![1, 3], ![2, 3]]

theorem rootsUVBC_injective : Function.Injective rootsUVBC := by
  unfold rootsUVBC
  decide

@[expose] def posRootList : List (Fin Tag.G2.rank → ℤ) :=
  [![1, 0], ![0, 1], ![1, 1], ![1, 3], ![1, 2], ![2, 3]]

theorem posRootList_nodup : posRootList.Nodup := by decide

theorem posRoots_closed (τ : Tag) :
    ∀ α ∈ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α},
      ∀ β ∈ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α},
      ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
        a • α + b • β ∈ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α} :=
  fun α hα β hβ a b ha hb hr => ⟨hr, by
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    rw [height_nsmul_add_nsmul]
    nlinarith [hα.2, hβ.2]⟩

theorem mem_posRootList_iff {α : Fin Tag.G2.rank → ℤ} :
    α ∈ posRootList ↔ IsRoot .G2 α ∧ 0 < height α := by
  have hfin : (rootFinset .G2).filter (fun β => 0 < height β) = posRootList.toFinset := by
    decide +kernel
  rw [← List.mem_toFinset, ← hfin, Finset.mem_filter, mem_rootFinset]

@[expose] def Xa {K : Type} [Field K]
    (x : K) : ModGL .G2 K := pinnedX .G2 K ![1, 0] x

@[expose] def Xr {K : Type} [Field K]
    (x : K) : ModGL .G2 K := pinnedX .G2 K ![0, 1] x

@[expose] def Xu {K : Type} [Field K]
    (x : K) : ModGL .G2 K := pinnedX .G2 K ![1, 1] x

@[expose] def Xb {K : Type} [Field K]
    (x : K) : ModGL .G2 K := pinnedX .G2 K ![1, 3] x

@[expose] def Xv {K : Type} [Field K]
    (x : K) : ModGL .G2 K := pinnedX .G2 K ![1, 2] x

@[expose] def Xc {K : Type} [Field K]
    (x : K) : ModGL .G2 K := pinnedX .G2 K ![2, 3] x

theorem rootsUVBC_pos (i : Fin 4) :
    IsRoot .G2 (rootsUVBC i) ∧ 0 < height (τ := .G2) (rootsUVBC i) := by
  fin_cases i
  · exact mem_posRootList_iff.1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact mem_posRootList_iff.1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  · exact mem_posRootList_iff.1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))
  · exact mem_posRootList_iff.1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_singleton_self _))))))

section Basic

variable {K : Type} [Field K]

theorem Xa_add (x y : K) : Xa (x + y) = Xa x * Xa y := pinnedX_add .G2 K _ x y
theorem Xr_add (x y : K) : Xr (x + y) = Xr x * Xr y := pinnedX_add .G2 K _ x y
theorem Xu_add (x y : K) : Xu (x + y) = Xu x * Xu y := pinnedX_add .G2 K _ x y
theorem Xb_add (x y : K) : Xb (x + y) = Xb x * Xb y := pinnedX_add .G2 K _ x y
theorem Xv_add (x y : K) : Xv (x + y) = Xv x * Xv y := pinnedX_add .G2 K _ x y
theorem Xc_add (x y : K) : Xc (x + y) = Xc x * Xc y := pinnedX_add .G2 K _ x y

theorem Xa_zero : Xa (0 : K) = 1 := pinnedX_zero .G2 K _
theorem Xr_zero : Xr (0 : K) = 1 := pinnedX_zero .G2 K _
theorem Xu_zero : Xu (0 : K) = 1 := pinnedX_zero .G2 K _
theorem Xb_zero : Xb (0 : K) = 1 := pinnedX_zero .G2 K _
theorem Xv_zero : Xv (0 : K) = 1 := pinnedX_zero .G2 K _
theorem Xc_zero : Xc (0 : K) = 1 := pinnedX_zero .G2 K _

theorem Xv_injective : Function.Injective (Xv (K := K)) := pinnedX_injective .G2 K _
theorem Xc_injective : Function.Injective (Xc (K := K)) := pinnedX_injective .G2 K _

theorem Xa_comm (x y : K) : Commute (Xa x) (Xa y) := by
  show Xa x * Xa y = Xa y * Xa x
  rw [← Xa_add, ← Xa_add, add_comm]
theorem Xu_comm (x y : K) : Commute (Xu x) (Xu y) := by
  show Xu x * Xu y = Xu y * Xu x
  rw [← Xu_add, ← Xu_add, add_comm]
theorem Xb_comm (x y : K) : Commute (Xb x) (Xb y) := by
  show Xb x * Xb y = Xb y * Xb x
  rw [← Xb_add, ← Xb_add, add_comm]
theorem Xv_comm (x y : K) : Commute (Xv x) (Xv y) := by
  show Xv x * Xv y = Xv y * Xv x
  rw [← Xv_add, ← Xv_add, add_comm]
theorem Xc_comm (x y : K) : Commute (Xc x) (Xc y) := by
  show Xc x * Xc y = Xc y * Xc x
  rw [← Xc_add, ← Xc_add, add_comm]

theorem Xv_pow_three (h3 : (3 : K) = 0) (s : K) : Xv s ^ 3 = 1 := by
  rw [pow_succ, pow_two, ← Xv_add, ← Xv_add]
  have : s + s + s = 0 := by
    have h : s + s + s = 3 * s := by ring
    rw [h, h3, zero_mul]
  rw [this, Xv_zero]

theorem Xc_pow_three (h3 : (3 : K) = 0) (s : K) : Xc s ^ 3 = 1 := by
  rw [pow_succ, pow_two, ← Xc_add, ← Xc_add]
  have : s + s + s = 0 := by
    have h : s + s + s = 3 * s := by ring
    rw [h, h3, zero_mul]
  rw [this, Xc_zero]

end Basic

theorem forall_posRootList {P : (Fin Tag.G2.rank → ℤ) → Prop} (h1 : P ![1, 0]) (h2 : P ![0, 1])
    (h3 : P ![1, 1]) (h4 : P ![1, 3]) (h5 : P ![1, 2]) (h6 : P ![2, 3]) :
    ∀ α ∈ posRootList, P α := by
  intro α hα
  rcases List.mem_cons.1 hα with rfl | hα
  · exact h1
  rcases List.mem_cons.1 hα with rfl | hα
  · exact h2
  rcases List.mem_cons.1 hα with rfl | hα
  · exact h3
  rcases List.mem_cons.1 hα with rfl | hα
  · exact h4
  rcases List.mem_cons.1 hα with rfl | hα
  · exact h5
  rcases List.mem_singleton.1 hα with rfl
  exact h6

section Membership

variable {K : Type} [Field K]

theorem pinnedX_mem_posUnipotent {α : Fin Tag.G2.rank → ℤ} (hα : α ∈ posRootList) (x : K) :
    pinnedX .G2 K α x ∈ posUnipotent .G2 K := by
  have hα' := (mem_posRootList_iff).1 hα
  have hle : rootSubgroup .G2 K α ≤ posUnipotent .G2 K := le_iSup₂_of_le α hα' le_rfl
  exact hle (Subgroup.subset_closure ⟨x, rfl⟩)

theorem Xa_mem (x : K) : Xa x ∈ posUnipotent .G2 K :=
  pinnedX_mem_posUnipotent (List.mem_cons_self) x
theorem Xr_mem (x : K) : Xr x ∈ posUnipotent .G2 K :=
  pinnedX_mem_posUnipotent (List.mem_cons_of_mem _ List.mem_cons_self) x
theorem Xu_mem (x : K) : Xu x ∈ posUnipotent .G2 K :=
  pinnedX_mem_posUnipotent (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) x
theorem Xb_mem (x : K) : Xb x ∈ posUnipotent .G2 K :=
  pinnedX_mem_posUnipotent
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))) x
theorem Xv_mem (x : K) : Xv x ∈ posUnipotent .G2 K :=
  pinnedX_mem_posUnipotent
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))) x
theorem Xc_mem (x : K) : Xc x ∈ posUnipotent .G2 K :=
  pinnedX_mem_posUnipotent
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))))) x

theorem commute_of_forall_posRoot {g : ModGL .G2 K}
    (h : ∀ α ∈ posRootList, ∀ y : K, Commute g (pinnedX .G2 K α y)) :
    ∀ u ∈ posUnipotent .G2 K, Commute g u := by
  have hle : posUnipotent .G2 K ≤ Subgroup.centralizer {g} := by
    refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨y, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact ((h α ((mem_posRootList_iff).2 hα) y).symm).eq
  intro u hu
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hu)).symm

theorem mem_Xv_Xc_posUnipotent (s t : K) : Xv s * Xc t ∈ posUnipotent .G2 K :=
  mul_mem (Xv_mem s) (Xc_mem t)

end Membership

section Test

variable {K : Type} [Field K]

theorem ofFn_uvbc (a b c d : K) : (List.ofFn fun i : Fin 4 =>
      pinnedX .G2 K (rootsUVBC i) (![a, b, c, d] i)).prod = Xu a * Xv b * Xb c * Xc d := by
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rfl

end Test

section Main

variable {K : Type} [Field K]

theorem inj4 {p₁ p₂ p₃ p₄ q₁ q₂ q₃ q₄ : K}
    (h : Xu p₁ * Xv p₂ * Xb p₃ * Xc p₄ = Xu q₁ * Xv q₂ * Xb q₃ * Xc q₄) :
    p₁ = q₁ ∧ p₂ = q₂ ∧ p₃ = q₃ ∧ p₄ = q₄ := by
  have hinj := (positive_root_product_injectivity .G2 K (m := 4) rootsUVBC rootsUVBC_injective
    rootsUVBC_pos).2
  have hEq : (List.ofFn fun i : Fin 4 => pinnedX .G2 K (rootsUVBC i) (![p₁, p₂, p₃, p₄] i)).prod =
      (List.ofFn fun i : Fin 4 => pinnedX .G2 K (rootsUVBC i) (![q₁, q₂, q₃, q₄] i)).prod := by
    rw [ofFn_uvbc, ofFn_uvbc]
    exact h
  have h2 := hinj hEq
  exact ⟨congrFun h2 0, congrFun h2 1, congrFun h2 2, congrFun h2 3⟩

theorem comm_au (x y : K) : Commute (Xa x) (Xu y) := (g2_commute_table x y).1
theorem comm_av (x y : K) : Commute (Xa x) (Xv y) := (g2_commute_table x y).2.1
theorem comm_ac (x y : K) : Commute (Xa x) (Xc y) := (g2_commute_table x y).2.2.1
theorem comm_rb (x y : K) : Commute (Xr x) (Xb y) := (g2_commute_table x y).2.2.2.1
theorem comm_rc (x y : K) : Commute (Xr x) (Xc y) := (g2_commute_table x y).2.2.2.2.1
theorem comm_ub (x y : K) : Commute (Xu x) (Xb y) := (g2_commute_table x y).2.2.2.2.2.1
theorem comm_uc (x y : K) : Commute (Xu x) (Xc y) := (g2_commute_table x y).2.2.2.2.2.2.1
theorem comm_vb (x y : K) : Commute (Xv x) (Xb y) := (g2_commute_table x y).2.2.2.2.2.2.2.1
theorem comm_vc (x y : K) : Commute (Xv x) (Xc y) := (g2_commute_table x y).2.2.2.2.2.2.2.2.1
theorem comm_bc (x y : K) : Commute (Xb x) (Xc y) := (g2_commute_table x y).2.2.2.2.2.2.2.2.2
theorem comm_rv (h3 : (3 : K) = 0) (x y : K) : Commute (Xr x) (Xv y) :=
  (g2_commute_three h3 x y).1
theorem comm_uv (h3 : (3 : K) = 0) (x y : K) : Commute (Xu x) (Xv y) :=
  (g2_commute_three h3 x y).2

theorem Xv_central (h3 : (3 : K) = 0) (s : K) : ∀ u ∈ posUnipotent .G2 K, Commute (Xv s) u :=
  commute_of_forall_posRoot (forall_posRootList
    (P := fun α => ∀ y : K, Commute (Xv s) (pinnedX .G2 K α y))
    (fun y => (comm_av y s).symm) (fun y => (comm_rv h3 y s).symm)
    (fun y => (comm_uv h3 y s).symm) (fun y => comm_vb s y) (fun y => Xv_comm s y)
    (fun y => comm_vc s y))

theorem Xc_central (s : K) : ∀ u ∈ posUnipotent .G2 K, Commute (Xc s) u :=
  commute_of_forall_posRoot (forall_posRootList
    (P := fun α => ∀ y : K, Commute (Xc s) (pinnedX .G2 K α y))
    (fun y => (comm_ac y s).symm) (fun y => (comm_rc y s).symm)
    (fun y => (comm_uc y s).symm) (fun y => (comm_bc y s).symm)
    (fun y => (comm_vc y s).symm) (fun y => Xc_comm s y))

theorem rel_ab : ∃ e : K, (e = 1 ∨ e = -1) ∧ ∀ x y : K, ⁅Xa x, Xb y⁆ = Xc (e * (x * y)) := g2_rel_ab

theorem rel_ar : ∃ e₁ e₂ e₃ e₄ : K, (e₁ = 1 ∨ e₁ = -1) ∧ (e₂ = 1 ∨ e₂ = -1) ∧
    (e₃ = 1 ∨ e₃ = -1) ∧ (e₄ = 1 ∨ e₄ = -1) ∧ ∀ x y : K, ⁅Xa x, Xr y⁆ =
      Xu (e₁ * (x * y)) * Xv (e₂ * (x * y ^ 2)) * Xb (e₃ * (x * y ^ 3)) *
        Xc (e₄ * (x ^ 2 * y ^ 3)) := g2_rel_ar

theorem rel_ru (h3 : (3 : K) = 0) :
    ∃ e : K, (e = 1 ∨ e = -1) ∧ ∀ x y : K, ⁅Xr x, Xu y⁆ = Xv (e * (x * y)) := g2_rel_ru h3

theorem eq_Xv_Xc_of_central (h3 : (3 : K) = 0) {z : ModGL .G2 K} (hzU : z ∈ posUnipotent .G2 K)
    (hz : ∀ h ∈ posUnipotent .G2 K, h * z = z * h) : ∃ s t : K, z = Xv s * Xc t := by
  obtain ⟨c, hc⟩ := exists_list_prod_pinnedX_eq K
    (S := {α : Fin Tag.G2.rank → ℤ | IsRoot .G2 α ∧ 0 < height α}) (fun α hα => hα)
    (posRoots_closed .G2) posRootList_nodup (fun α => mem_posRootList_iff) hzU
  have h6 : (List.map (fun α => pinnedX .G2 K α (c α)) posRootList).prod =
      Xa (c ![1, 0]) * (Xr (c ![0, 1]) * (Xu (c ![1, 1]) * (Xb (c ![1, 3]) *
        (Xv (c ![1, 2]) * (Xc (c ![2, 3]) * 1))))) := rfl
  rw [hc, mul_one] at h6
  obtain ⟨ca, cr, cu, cb, cv, cc, hz'⟩ : ∃ ca cr cu cb cv cc : K,
      z = Xa ca * (Xr cr * (Xu cu * (Xb cb * (Xv cv * Xc cc)))) :=
    ⟨_, _, _, _, _, _, h6⟩
  clear h6 hc c
  subst hz'
  have hζ : ∀ h ∈ posUnipotent .G2 K, Commute (Xv cv * Xc cc) h := fun h hh =>
    (Xv_central h3 cv h hh).mul_left (Xc_central cc h hh)
  have hA : ∀ h ∈ posUnipotent .G2 K,
      h * (Xa ca * (Xr cr * (Xu cu * Xb cb))) = (Xa ca * (Xr cr * (Xu cu * Xb cb))) * h := by
    intro h hh
    have h1 := hz h hh
    have h2 := (hζ h hh).eq
    refine mul_right_cancel (b := Xv cv * Xc cc) ?_
    calc h * (Xa ca * (Xr cr * (Xu cu * Xb cb))) * (Xv cv * Xc cc)
        = h * (Xa ca * (Xr cr * (Xu cu * (Xb cb * (Xv cv * Xc cc))))) := by
          simp only [mul_assoc]
      _ = Xa ca * (Xr cr * (Xu cu * (Xb cb * (Xv cv * Xc cc)))) * h := h1
      _ = (Xa ca * (Xr cr * (Xu cu * Xb cb))) * ((Xv cv * Xc cc) * h) := by
          simp only [mul_assoc]
      _ = (Xa ca * (Xr cr * (Xu cu * Xb cb))) * (h * (Xv cv * Xc cc)) := by rw [h2]
      _ = (Xa ca * (Xr cr * (Xu cu * Xb cb)) * h) * (Xv cv * Xc cc) := by
          simp only [mul_assoc]
  have hW1 : Commute (Xr cr * (Xu cu * Xb cb)) (Xb (1 : K)) :=
    (comm_rb cr 1).mul_left ((comm_ub cu 1).mul_left (Xb_comm cb 1))
  have hc1 : Xb (1 : K) * Xa ca = Xa ca * Xb (1 : K) := by
    refine mul_right_cancel (b := Xr cr * (Xu cu * Xb cb)) ?_
    calc Xb (1 : K) * Xa ca * (Xr cr * (Xu cu * Xb cb))
        = Xb (1 : K) * (Xa ca * (Xr cr * (Xu cu * Xb cb))) := by simp only [mul_assoc]
      _ = (Xa ca * (Xr cr * (Xu cu * Xb cb))) * Xb (1 : K) := hA (Xb (1 : K)) (Xb_mem 1)
      _ = Xa ca * ((Xr cr * (Xu cu * Xb cb)) * Xb (1 : K)) := by simp only [mul_assoc]
      _ = Xa ca * (Xb (1 : K) * (Xr cr * (Xu cu * Xb cb))) := by rw [hW1.eq]
      _ = Xa ca * Xb (1 : K) * (Xr cr * (Xu cu * Xb cb)) := by simp only [mul_assoc]
  have hca : ca = 0 := by
    obtain ⟨e, he, hab⟩ := rel_ab (K := K)
    have h1 : ⁅Xa ca, Xb (1 : K)⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hc1.symm
    rw [hab] at h1
    have h2 : Xc (e * (ca * 1)) = Xc 0 := by rw [h1, Xc_zero]
    have h4 := Xc_injective h2
    exact eq_zero_of_sign_mul' he (by simpa using h4)
  subst hca
  simp only [Xa_zero, one_mul] at hA ⊢
  obtain ⟨e₁, e₂, e₃, e₄, he₁, he₂, he₃, he₄, har⟩ := rel_ar (K := K)
  obtain ⟨e', he', hab⟩ := rel_ab (K := K)
  have key : ∀ g h : ModGL .G2 K, g * h = ⁅g, h⁆ * (h * g) := fun g h => by
    simp only [commutatorElement_def]
    group
  obtain ⟨Q, hQdef⟩ : ∃ Q : ModGL .G2 K, Q = Xu (e₁ * (1 * cr)) * Xv (e₂ * (1 * cr ^ 2)) *
      Xb (e₃ * (1 * cr ^ 3)) * Xc (e₄ * (1 ^ 2 * cr ^ 3)) := ⟨_, rfl⟩
  obtain ⟨Xcb, hXcb⟩ : ∃ Y : ModGL .G2 K, Y = Xc (e' * (1 * cb)) := ⟨_, rfl⟩
  have hQ : Xa (1 : K) * Xr cr = Q * (Xr cr * Xa (1 : K)) := by
    rw [key (Xa (1 : K)) (Xr cr), har 1 cr, hQdef]
  have hB : Xa (1 : K) * Xb cb = Xcb * (Xb cb * Xa (1 : K)) := by
    rw [key (Xa (1 : K)) (Xb cb), hab 1 cb, hXcb]
  have hau : Xa (1 : K) * Xu cu = Xu cu * Xa (1 : K) := (comm_au 1 cu).eq
  have hcr : Xr cr * Xcb = Xcb * Xr cr := by rw [hXcb]; exact (comm_rc cr _).eq
  have hcu : Xu cu * Xcb = Xcb * Xu cu := by rw [hXcb]; exact (comm_uc cu _).eq
  have hmain : Q * Xcb = 1 := by
    have hcent := hA (Xa (1 : K)) (Xa_mem 1)
    refine mul_right_cancel (b := Xr cr * (Xu cu * (Xb cb * Xa (1 : K)))) ?_
    calc Q * Xcb * (Xr cr * (Xu cu * (Xb cb * Xa (1 : K))))
        = Q * ((Xcb * Xr cr) * (Xu cu * (Xb cb * Xa (1 : K)))) := by simp only [mul_assoc]
      _ = Q * ((Xr cr * Xcb) * (Xu cu * (Xb cb * Xa (1 : K)))) := by rw [hcr]
      _ = Q * (Xr cr * ((Xcb * Xu cu) * (Xb cb * Xa (1 : K)))) := by simp only [mul_assoc]
      _ = Q * (Xr cr * ((Xu cu * Xcb) * (Xb cb * Xa (1 : K)))) := by rw [hcu]
      _ = Q * (Xr cr * (Xu cu * (Xcb * (Xb cb * Xa (1 : K))))) := by simp only [mul_assoc]
      _ = Q * (Xr cr * (Xu cu * (Xa (1 : K) * Xb cb))) := by rw [hB]
      _ = Q * (Xr cr * ((Xu cu * Xa (1 : K)) * Xb cb)) := by simp only [mul_assoc]
      _ = Q * (Xr cr * ((Xa (1 : K) * Xu cu) * Xb cb)) := by rw [hau]
      _ = (Q * (Xr cr * Xa (1 : K))) * (Xu cu * Xb cb) := by simp only [mul_assoc]
      _ = (Xa (1 : K) * Xr cr) * (Xu cu * Xb cb) := by rw [hQ]
      _ = Xa (1 : K) * (Xr cr * (Xu cu * Xb cb)) := by simp only [mul_assoc]
      _ = (Xr cr * (Xu cu * Xb cb)) * Xa (1 : K) := hcent
      _ = 1 * (Xr cr * (Xu cu * (Xb cb * Xa (1 : K)))) := by simp only [mul_assoc, one_mul]
  have hone : Xu (0 : K) * Xv 0 * Xb 0 * Xc 0 = 1 := by
    rw [Xu_zero, Xv_zero, Xb_zero, Xc_zero]
    simp
  have hexp : Xu (e₁ * (1 * cr)) * Xv (e₂ * (1 * cr ^ 2)) * Xb (e₃ * (1 * cr ^ 3)) *
      Xc (e₄ * (1 ^ 2 * cr ^ 3) + e' * (1 * cb)) = Xu 0 * Xv 0 * Xb 0 * Xc 0 := by
    rw [hone, Xc_add, ← mul_assoc]
    rw [hQdef, hXcb] at hmain
    exact hmain
  obtain ⟨hp1, -, -, hp4⟩ := inj4 hexp
  have hcr0 : cr = 0 := eq_zero_of_sign_mul' he₁ (by simpa using hp1)
  subst hcr0
  have hcb0 : cb = 0 := by
    have h5 : e' * cb = 0 := by simpa using hp4
    exact eq_zero_of_sign_mul' he' h5
  subst hcb0
  simp only [Xr_zero, Xb_zero, one_mul, mul_one] at hA
  have hc3 : Xr (1 : K) * Xu cu = Xu cu * Xr (1 : K) := hA (Xr (1 : K)) (Xr_mem 1)
  have hcu0 : cu = 0 := by
    obtain ⟨e, he, hru⟩ := rel_ru (K := K) h3
    have h1 : ⁅Xr (1 : K), Xu cu⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hc3
    rw [hru] at h1
    have h2 : Xv (e * (1 * cu)) = Xv 0 := by rw [h1, Xv_zero]
    have h4 := Xv_injective h2
    exact eq_zero_of_sign_mul' he (by simpa using h4)
  subst hcu0
  refine ⟨cv, cc, ?_⟩
  simp only [Xr_zero, Xu_zero, Xb_zero, one_mul]

theorem mem_center_iff (h3 : (3 : K) = 0) (z : ↥(posUnipotent .G2 K)) :
    z ∈ Subgroup.center ↥(posUnipotent .G2 K) ↔ ∃ s t : K, (z : ModGL .G2 K) = Xv s * Xc t := by
  constructor
  · intro hz
    refine eq_Xv_Xc_of_central h3 z.2 fun h hh => ?_
    have := Subgroup.mem_center_iff.1 hz ⟨h, hh⟩
    exact congrArg Subtype.val this
  · rintro ⟨s, t, hst⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : ModGL .G2 K) * z = z * g
    rw [hst]
    exact ((Xv_central h3 s g g.2).mul_left (Xc_central t g g.2)).eq.symm

theorem inj_vc {s t s' t' : K} (h : Xv s * Xc t = Xv s' * Xc t') : s = s' ∧ t = t' := by
  have h' : Xu (0 : K) * Xv s * Xb 0 * Xc t = Xu 0 * Xv s' * Xb 0 * Xc t' := by
    rw [Xu_zero, Xb_zero, one_mul, mul_one, one_mul, mul_one, h]
  obtain ⟨-, h2, -, h4⟩ := inj4 h'
  exact ⟨h2, h4⟩

@[expose] def centerParam (h3 : (3 : K) = 0) (p : K × K) :
    ↥(Subgroup.center ↥(posUnipotent .G2 K)) :=
  ⟨⟨Xv p.1 * Xc p.2, mem_Xv_Xc_posUnipotent p.1 p.2⟩, (mem_center_iff h3 _).2 ⟨p.1, p.2, rfl⟩⟩

theorem coe_centerParam (h3 : (3 : K) = 0) (p : K × K) :
    (((centerParam h3 p : ↥(Subgroup.center ↥(posUnipotent .G2 K))) :
      ↥(posUnipotent .G2 K)) : ModGL .G2 K) = Xv p.1 * Xc p.2 := rfl

theorem centerParam_bijective (h3 : (3 : K) = 0) : Function.Bijective (centerParam h3) := by
  constructor
  · intro p q h
    have h0 := congrArg (fun z : ↥(Subgroup.center ↥(posUnipotent .G2 K)) =>
      ((z : ↥(posUnipotent .G2 K)) : ModGL .G2 K)) h
    simp only [coe_centerParam] at h0
    obtain ⟨h2, h3'⟩ := inj_vc h0
    exact Prod.ext h2 h3'
  · intro z
    obtain ⟨s, t, hst⟩ := (mem_center_iff h3 z.1).1 z.2
    exact ⟨(s, t), Subtype.ext (Subtype.ext hst.symm)⟩

theorem card_center (h3 : (3 : K) = 0) :
    Nat.card ↥(Subgroup.center ↥(posUnipotent .G2 K)) = Nat.card K ^ 2 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (centerParam_bijective h3)), Nat.card_prod, sq]

theorem pow_three_center (h3 : (3 : K) = 0) (z : ↥(posUnipotent .G2 K))
    (hz : z ∈ Subgroup.center ↥(posUnipotent .G2 K)) : z ^ 3 = 1 := by
  obtain ⟨s, t, hst⟩ := (mem_center_iff h3 z).1 hz
  apply Subtype.ext
  show (z : ModGL .G2 K) ^ 3 = 1
  rw [hst, (comm_vc s t).mul_pow, Xv_pow_three h3, Xc_pow_three h3, mul_one]

end Main

end CFSG.GH74.GLS.IVK.Proofs2.Ivk47
