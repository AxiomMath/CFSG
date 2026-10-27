module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22WylCalc
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22WylRel

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement

namespace Perp22Wyl

namespace WylFrame

section Members

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {W : Subgroup Y} {z : Y}
  (F : WylFrame Ω W z) (c : Q3CL.Thompson.Ctx Ω W)
  (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)

include F c hc

theorem g_cases {i : Fin 4} {g : Y} (hg : g ∈ (F.ρ i).K ⊓ W ∧ orderOf g = 4) :
    g * (F.a i)⁻¹ = 1 ∨ g * (F.a i)⁻¹ = z := by
  have hgsq : g * g = z := T7A.sq_eq_of_orderOf_four (F.hz i) hg.1.1 hg.2
  have hu : g * (F.a i)⁻¹ ∈ (F.ρ i).K :=
    (F.ρ i).K.mul_mem hg.1.1 ((F.ρ i).K.inv_mem (F.a_mem_K i))
  have hcomm : (F.a i)⁻¹ * g = g * (F.a i)⁻¹ :=
    (hc g hg.1.2 (F.a i)⁻¹ (W.inv_mem (F.a_mem_W i))).symm
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right F.z_sq
  have hu2 : (g * (F.a i)⁻¹) * (g * (F.a i)⁻¹) = 1 := by
    calc (g * (F.a i)⁻¹) * (g * (F.a i)⁻¹) = g * ((F.a i)⁻¹ * g) * (F.a i)⁻¹ := by group
      _ = g * (g * (F.a i)⁻¹) * (F.a i)⁻¹ := by rw [hcomm]
      _ = (g * g) * (F.a i * F.a i)⁻¹ := by group
      _ = z * z⁻¹ := by rw [hgsq, F.a_sq i]
      _ = 1 := by rw [hzi]; exact F.z_sq
  exact (F.hz i).unique _ hu hu2

theorem prod_cases {g : Fin 4 → Y} (hg : ∀ i, g i ∈ (F.ρ i).K ⊓ W ∧ orderOf (g i) = 4) :
    g 0 * g 1 * g 2 * g 3 = F.t' ∨ g 0 * g 1 * g 2 * g 3 = F.t' * z := by
  let _ : CommGroup ↥W :=
    { (inferInstance : Group ↥W) with mul_comm := fun x y => Subtype.ext (hc x x.2 y y.2) }
  let g' : Fin 4 → ↥W := fun i => ⟨g i, (hg i).1.2⟩
  let a' : Fin 4 → ↥W := fun i => ⟨F.a i, F.a_mem_W i⟩
  have h1 : ∏ i, (g' i * (a' i)⁻¹) = (∏ i, g' i) * (∏ i, a' i)⁻¹ := by
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have h2 : ∏ i, g' i = (∏ i, (g' i * (a' i)⁻¹)) * ∏ i, a' i := by
    rw [h1, inv_mul_cancel_right]
  simp only [Fin.prod_univ_four] at h2
  have h3 := congrArg Subtype.val h2
  have key : g 0 * g 1 * g 2 * g 3 = ((g 0 * (F.a 0)⁻¹) * (g 1 * (F.a 1)⁻¹) * (g 2 * (F.a 2)⁻¹) *
      (g 3 * (F.a 3)⁻¹)) * (F.a 0 * F.a 1 * F.a 2 * F.a 3) := by
    simpa [g', a'] using h3
  have hmul : ∀ x y : Y, (x = 1 ∨ x = z) → (y = 1 ∨ y = z) → (x * y = 1 ∨ x * y = z) := by
    intro x y hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · left; rw [hx, hy, one_mul]
    · right; rw [hx, hy, one_mul]
    · right; rw [hx, hy, mul_one]
    · left; rw [hx, hy]; exact F.z_sq
  have hd := hmul _ _ (hmul _ _ (hmul _ _ (F.g_cases c hc (hg 0)) (F.g_cases c hc (hg 1)))
    (F.g_cases c hc (hg 2))) (F.g_cases c hc (hg 3))
  rw [key, ← F.hrel]
  rcases hd with hd | hd
  · left; rw [hd, one_mul]
  · right; rw [hd]; exact F.zt' c hc

theorem mem_E_of_isUniqueInvolution (hclC : Q3CL.ClassicalClause Ω) (hnc : ¬ DbarConnected Ω W)
    (ρ' : Rep Ω W) {w : Y} (hw : IsUniqueInvolution ρ'.K w) :
    w = z ∨ w = F.t' ∨ w = F.t' * z := by
  by_cases hK : ∃ i, ρ'.K = (F.ρ i).K
  · obtain ⟨i, hi⟩ := hK
    have h' : IsUniqueInvolution ρ'.K z := by rw [hi]; exact F.hz i
    exact Or.inl (hw.eq h')
  · push Not at hK
    obtain ⟨w₀, g, hw₀, hg, hrel⟩ :=
      c.exists_relation_far hclC hnc F.ρ F.hne F.hadj F.hclos ρ' hK
    have hww : w = w₀ := hw.eq hw₀
    rw [hww, hrel]
    rcases F.prod_cases c hc hg with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

theorem mgrp_le (hclC : Q3CL.ClassicalClause Ω) (hnc : ¬ DbarConnected Ω W) {H : Subgroup Y}
    (hz : Subgroup.centralizer ({z} : Set Y) ≤ H)
    (ht : Subgroup.centralizer ({F.t'} : Set Y) ≤ H)
    (htz : Subgroup.centralizer ({F.t' * z} : Set Y) ≤ H) : MGrp Ω W ≤ H := by
  refine iSup₂_le fun R hR => ?_
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR.1
  obtain ⟨ρ', hρ'K, hρ'R⟩ := Q3T8.Asc77.T7D.exists_rep c.hΩ c.hW hJ hRJ hR
  obtain ⟨w, hw⟩ := Sec6Gen.exists_uniqueInvolution c.hΩ hJ
  have hwρ : IsUniqueInvolution ρ'.K w := by rw [hρ'K]; exact hw
  have hRC : R ≤ Subgroup.centralizer ({w} : Set Y) := hRJ.1.trans (isUniqueInvolution_le_centralizer hw)
  rcases F.mem_E_of_isUniqueInvolution c hc hclC hnc ρ' hwρ with h | h | h
  · rw [h] at hRC; exact hRC.trans hz
  · rw [h] at hRC; exact hRC.trans ht
  · rw [h] at hRC; exact hRC.trans htz

end Members

section Trans


variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {W : Subgroup Y}
  (c : Q3CL.Thompson.Ctx Ω W)

include c

theorem braid_conj (hclC : Q3CL.ClassicalClause Ω) {ρ₁ τ' : Rep Ω W}
    (hnc : ρ₁.img * τ'.img ≠ τ'.img * ρ₁.img) :
    conjSub (ρ₁.r * τ'.r * ρ₁.r⁻¹) ρ₁.K = τ'.K := by
  have hn : ρ₁.r * τ'.r * ρ₁.r⁻¹ ∈ Subgroup.normalizer (W : Set Y) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ ρ₁.r_mem_normalizer τ'.r_mem_normalizer)
      (Subgroup.inv_mem _ ρ₁.r_mem_normalizer)
  exact c.K_eq_of_img_eq (Q3T8.Asc77.T7D.conjRep c.hΩ hn ρ₁) τ' (c.conjRep_braid hclC ρ₁ τ' hnc hn)

variable {z : Y} (F : WylFrame Ω W z)

include F

theorem exists_conj_rep (hclC : Q3CL.ClassicalClause Ω) (τ : Rep Ω W) :
    ∃ m ∈ MGrp Ω W, conjSub m (F.ρ 0).K = τ.K := by
  have hMr : ∀ ρ' : Rep Ω W, ρ'.r ∈ MGrp Ω W := fun ρ' => le_MGrp_of_mem_D ρ'.hR ρ'.hr
  have farcase : ∀ τ' : Rep Ω W, (∀ i, τ'.K ≠ (F.ρ i).K) →
      ∃ m ∈ MGrp Ω W, conjSub m (F.ρ 0).K = τ'.K := by
    intro τ' hf
    refine ⟨(F.ρ 0).r * τ'.r * (F.ρ 0).r⁻¹,
      (MGrp Ω W).mul_mem ((MGrp Ω W).mul_mem (hMr _) (hMr _)) ((MGrp Ω W).inv_mem (hMr _)),
      braid_conj c hclC ?_⟩
    intro hcomm
    obtain ⟨j, hj⟩ := F.hclos τ' 0 (Or.inr (c.omega_of_comm (F.ρ 0) τ' (hf 0).symm hcomm))
    exact hf j hj
  by_cases hfr : ∀ i, τ.K ≠ (F.ρ i).K
  · exact farcase τ hfr
  · push Not at hfr
    obtain ⟨j, hj⟩ := hfr
    obtain ⟨m₀, hm₀M, hm₀⟩ := farcase F.σ F.hfar
    have hbr := braid_conj c hclC (ρ₁ := F.ρ j) (τ' := F.σ) (fun hcomm =>
      F.hnot₁ c j (c.omega_of_comm (F.ρ j) F.σ (F.hfar j).symm hcomm))
    have hn : (F.ρ j).r * F.σ.r * (F.ρ j).r⁻¹ ∈ MGrp Ω W :=
      (MGrp Ω W).mul_mem ((MGrp Ω W).mul_mem (hMr _) (hMr _)) ((MGrp Ω W).inv_mem (hMr _))
    refine ⟨((F.ρ j).r * F.σ.r * (F.ρ j).r⁻¹)⁻¹ * m₀, (MGrp Ω W).mul_mem ((MGrp Ω W).inv_mem hn) hm₀M, ?_⟩
    rw [conjSub_mul, hm₀, ← hbr, conjSub_inv_conjSub, hj]

end Trans

end WylFrame

end Perp22Wyl

end CFSG.CGT.PushingUpLit.SolKNA.R4
