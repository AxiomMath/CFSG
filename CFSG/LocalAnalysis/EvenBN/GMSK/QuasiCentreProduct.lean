module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup

theorem qcProd_unique {G : Type*} [Group G] {W Y : Subgroup G} (hdisj : W ⊓ Y = ⊥)
    {w w' y y' : G} (hw : w ∈ W) (hw' : w' ∈ W) (hy : y ∈ Y) (hy' : y' ∈ Y)
    (h : w * y = w' * y') : w = w' ∧ y = y' := by
  have h1 : w'⁻¹ * w = y' * y⁻¹ := by
    calc w'⁻¹ * w = w'⁻¹ * (w * y) * y⁻¹ := by group
      _ = w'⁻¹ * (w' * y') * y⁻¹ := by rw [h]
      _ = y' * y⁻¹ := by group
  have hmem : w'⁻¹ * w ∈ W ⊓ Y :=
    ⟨W.mul_mem (W.inv_mem hw') hw, h1 ▸ Y.mul_mem hy' (Y.inv_mem hy)⟩
  rw [hdisj, mem_bot, inv_mul_eq_one] at hmem
  subst hmem
  exact ⟨rfl, mul_left_cancel h⟩

theorem quasisimple_le_of_product {G : Type*} [Group G] {W Y J : Subgroup G} {a : G}
    (hWY : ∀ w ∈ W, ∀ y ∈ Y, w * y = y * w) (hdisj : W ⊓ Y = ⊥)
    (haW : ∀ w ∈ W, a * w * a⁻¹ ∈ W) (haY : ∀ y ∈ Y, a * y * a⁻¹ ∈ Y)
    (hJq : CFSG.IsQuasisimple ↥J) (hJa : J ≤ centralizer ({a} : Set G))
    (hJWY : ∀ j ∈ J, ∃ w ∈ W, ∃ y ∈ Y, j = w * y)
    (hJn : ∀ c ∈ centralizer ({a} : Set G), ∀ j ∈ J, c * j * c⁻¹ ∈ J)
    (hJW : ¬ J ≤ centralizer (W : Set G)) : J ≤ W := by
  classical
  haveI hperf : Group.IsPerfect ↥J := hJq.1
  have hdec : ∀ j : ↥J, ∃ w ∈ W, ∃ y ∈ Y, (j : G) = w * y := fun j => hJWY j j.2
  choose wf hwf yf hyf hjwy using hdec
  have hya : ∀ j : ↥J, a * yf j * a⁻¹ = yf j := by
    intro j
    have hj : a * (j : G) * a⁻¹ = j := by
      have h := mem_centralizer_singleton_iff.mp (hJa j.2)
      rw [← h]
      group
    refine (qcProd_unique hdisj (haW _ (hwf j)) (hwf j) (haY _ (hyf j)) (hyf j) ?_).2
    calc a * wf j * a⁻¹ * (a * yf j * a⁻¹) = a * (wf j * yf j) * a⁻¹ := by group
      _ = a * (j : G) * a⁻¹ := by rw [← hjwy j]
      _ = j := hj
      _ = wf j * yf j := hjwy j
  have hmuly : ∀ j j' : ↥J, yf (j * j') = yf j * yf j' := by
    intro j j'
    refine (qcProd_unique hdisj (hwf (j * j')) (W.mul_mem (hwf j) (hwf j')) (hyf (j * j'))
      (Y.mul_mem (hyf j) (hyf j')) ?_).2
    have hcomm : wf j' * yf j = yf j * wf j' := hWY _ (hwf j') _ (hyf j)
    calc wf (j * j') * yf (j * j') = ((j * j' : ↥J) : G) := (hjwy (j * j')).symm
      _ = (wf j * yf j) * (wf j' * yf j') := by
          rw [Subgroup.coe_mul, hjwy j, hjwy j']
      _ = wf j * (yf j * wf j') * yf j' := by group
      _ = wf j * (wf j' * yf j) * yf j' := by rw [hcomm]
      _ = (wf j * wf j') * (yf j * yf j') := by group
  have hNnormal : (Y.subgroupOf J).Normal := by
    constructor
    intro n hn g
    rw [mem_subgroupOf] at hn ⊢
    have hz : wf g * (yf g * (n : G) * (yf g)⁻¹) = (yf g * (n : G) * (yf g)⁻¹) * wf g :=
      hWY _ (hwf g) _ (Y.mul_mem (Y.mul_mem (hyf g) hn) (Y.inv_mem (hyf g)))
    have heq : ((g * n * g⁻¹ : ↥J) : G) = yf g * (n : G) * (yf g)⁻¹ := by
      calc ((g * n * g⁻¹ : ↥J) : G) = (g : G) * n * (g : G)⁻¹ := rfl
        _ = (wf g * yf g) * n * (wf g * yf g)⁻¹ := by rw [← hjwy g]
        _ = (wf g * (yf g * n * (yf g)⁻¹)) * (wf g)⁻¹ := by group
        _ = ((yf g * n * (yf g)⁻¹) * wf g) * (wf g)⁻¹ := by rw [hz]
        _ = yf g * n * (yf g)⁻¹ := by group
    rw [heq]
    exact Y.mul_mem (Y.mul_mem (hyf g) hn) (Y.inv_mem (hyf g))
  have hNcentral : Y.subgroupOf J ≤ center ↥J := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hJq hNnormal with htop | hle
    · exfalso
      apply hJW
      intro j hj
      have hjY : j ∈ Y := by
        have hmem : (⟨j, hj⟩ : ↥J) ∈ Y.subgroupOf J := by rw [htop]; exact mem_top _
        exact mem_subgroupOf.mp hmem
      rw [mem_centralizer_iff]
      intro w hw
      exact hWY w hw j hjY
    · exact hle
  have hconj : ∀ y₀ ∈ Y ⊓ centralizer ({a} : Set G), ∀ j : ↥J, y₀ * (j : G) * y₀⁻¹ = j := by
    intro y₀ hy₀
    obtain ⟨hy₀Y, hy₀a⟩ := hy₀
    let σ : ↥J →* ↥J :=
      { toFun := fun j => ⟨y₀ * j * y₀⁻¹, hJn y₀ hy₀a j j.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
    have hdisp : ∀ j : ↥J, j⁻¹ * σ j ∈ center ↥J := by
      intro j
      apply hNcentral
      rw [mem_subgroupOf]
      have hc : wf j * y₀ = y₀ * wf j := hWY _ (hwf j) _ hy₀Y
      have heq : ((j⁻¹ * σ j : ↥J) : G) = (yf j)⁻¹ * (y₀ * yf j * y₀⁻¹) := by
        calc ((j⁻¹ * σ j : ↥J) : G) = (j : G)⁻¹ * (y₀ * j * y₀⁻¹) := rfl
          _ = (wf j * yf j)⁻¹ * (y₀ * (wf j * yf j) * y₀⁻¹) := by rw [← hjwy j]
          _ = (yf j)⁻¹ * (wf j)⁻¹ * ((y₀ * wf j) * yf j * y₀⁻¹) := by group
          _ = (yf j)⁻¹ * (wf j)⁻¹ * ((wf j * y₀) * yf j * y₀⁻¹) := by rw [← hc]
          _ = (yf j)⁻¹ * (y₀ * yf j * y₀⁻¹) := by group
      rw [heq]
      exact Y.mul_mem (Y.inv_mem (hyf j)) (Y.mul_mem (Y.mul_mem hy₀Y (hyf j)) (Y.inv_mem hy₀Y))
    have hσid :=
      CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement σ hdisp
    intro j
    exact congrArg Subtype.val (DFunLike.congr_fun hσid j)
  have hyC : ∀ j : ↥J, yf j ∈ Y ⊓ centralizer ({a} : Set G) := fun j =>
    ⟨hyf j, mem_centralizer_singleton_iff.mpr (by
      have h := hya j
      calc yf j * a = (a * yf j * a⁻¹) * a := by rw [h]
        _ = a * yf j := by group)⟩
  have hyZ : ∀ j : ↥J, (⟨yf j, hyC j⟩ : ↥(Y ⊓ centralizer ({a} : Set G))) ∈
      center ↥(Y ⊓ centralizer ({a} : Set G)) := by
    intro j
    rw [mem_center_iff]
    intro c
    apply Subtype.ext
    show (c : G) * yf j = yf j * (c : G)
    have hcj := hconj (c : G) c.2 j
    have hc : wf j * (c : G) = (c : G) * wf j := hWY _ (hwf j) _ c.2.1
    rw [hjwy j] at hcj
    have h2 : (c : G) * yf j * (c : G)⁻¹ = yf j := by
      have h3 : wf j * ((c : G) * yf j * (c : G)⁻¹) = wf j * yf j := by
        calc wf j * ((c : G) * yf j * (c : G)⁻¹)
            = (wf j * (c : G)) * yf j * (c : G)⁻¹ := by group
          _ = ((c : G) * wf j) * yf j * (c : G)⁻¹ := by rw [hc]
          _ = (c : G) * (wf j * yf j) * (c : G)⁻¹ := by group
          _ = wf j * yf j := hcj
      exact mul_left_cancel h3
    calc (c : G) * yf j = ((c : G) * yf j * (c : G)⁻¹) * c := by group
      _ = yf j * c := by rw [h2]
  let ψ : ↥J →* ↥(center ↥(Y ⊓ centralizer ({a} : Set G))) :=
    MonoidHom.mk' (fun j => ⟨⟨yf j, hyC j⟩, hyZ j⟩)
      (fun j j' => Subtype.ext (Subtype.ext (hmuly j j')))
  have hψ : ψ = 1 :=
    CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_one_of_commutative ψ
  intro j hj
  have hy1 : yf ⟨j, hj⟩ = 1 := by
    have h := congrArg (fun f : ↥J →* ↥(center ↥(Y ⊓ centralizer ({a} : Set G))) =>
      (((f ⟨j, hj⟩ : ↥(center ↥(Y ⊓ centralizer ({a} : Set G)))) :
        ↥(Y ⊓ centralizer ({a} : Set G))) : G)) hψ
    exact h
  have h3 : j = wf ⟨j, hj⟩ := by
    have := hjwy ⟨j, hj⟩
    rw [hy1, mul_one] at this
    exact this
  rw [h3]
  exact hwf _

end CFSG.LocalAnalysis.EvenBN.GMSK
