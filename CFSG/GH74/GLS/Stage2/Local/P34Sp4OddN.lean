module

public import CFSG.GH74.GLS.Stage2.Local.P34Sp4Def
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TypeOne
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TwoComp

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag CFSG.ComponentClassification.CatFactsSp4

section Model

variable {F : Type} [Field F]

theorem sq_mem_X0 {d : StatedProj (StatedSp 2 F)} (hd : d ∈ centralizer {u1 F}) :
    d * d ∈ X0 F := by
  obtain ⟨g, rfl⟩ := proj_surjective d
  have hd' : proj 2 F g * u1 F = u1 F * proj 2 F g := mem_centralizer_singleton_iff.mp hd
  have hp : proj 2 F (g * T1 F) = proj 2 F (T1 F * g) := by
    rw [map_mul, map_mul]
    exact hd'
  refine ⟨g * g, ?_, by rw [map_mul]⟩
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
  apply sp_ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  have key := eq_or_eq_neg_of_proj_eq hp
  simp only [Subgroup.coe_mul, Units.val_mul] at key
  generalize ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = G at key ⊢
  generalize ((T1 F : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = T
    at key ⊢
  rcases key with h | h
  · calc G * G * T = G * (G * T) := by rw [Matrix.mul_assoc]
      _ = G * (T * G) := by rw [h]
      _ = (G * T) * G := by rw [Matrix.mul_assoc]
      _ = (T * G) * G := by rw [h]
      _ = T * (G * G) := by rw [Matrix.mul_assoc]
  · have hGT : G * T = -(T * G) := by rw [h, neg_neg]
    calc G * G * T = G * (G * T) := by rw [Matrix.mul_assoc]
      _ = G * (-(T * G)) := by rw [hGT]
      _ = -((G * T) * G) := by rw [Matrix.mul_neg, Matrix.mul_assoc]
      _ = -((-(T * G)) * G) := by rw [hGT]
      _ = (T * G) * G := by rw [Matrix.neg_mul, neg_neg]
      _ = T * (G * G) := by rw [Matrix.mul_assoc]

variable [Finite F]

theorem inf_eq_bot_of_pPrimeCore {R E : Subgroup (StatedProj (StatedSp 2 F))}
    (hnorm : ∀ d ∈ centralizer {u1 F}, ∀ r ∈ R, d * r * d⁻¹ ∈ R)
    (hodd' : ∀ r ∈ R, Odd (orderOf r)) (hE : E ≤ centralizer {u1 F}) (hcore : pPrimeCore 2 ↥E = ⊥) :
    R ⊓ E = ⊥ := by
  have hN : ((R ⊓ E).subgroupOf E).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨?_, E.mul_mem (E.mul_mem g.2 n.2) (E.inv_mem g.2)⟩
    exact hnorm g (hE g.2) n hn.1⟩
  have h1 := eq_bot_of_odd_normal_of_oddCore hcore (N := (R ⊓ E).subgroupOf E) (fun n hn => by
    rw [← Subgroup.orderOf_coe]
    exact hodd' _ (Subgroup.mem_subgroupOf.mp hn).1)
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx.2⟩ : ↥E) ∈ (R ⊓ E).subgroupOf E := Subgroup.mem_subgroupOf.mpr hx
  rw [h1, Subgroup.mem_bot] at this
  exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)

theorem oddNormal_u1_trivial (hodd : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F)
    {R : Subgroup (StatedProj (StatedSp 2 F))} (hRD : R ≤ centralizer {u1 F})
    (hnorm : ∀ d ∈ centralizer {u1 F}, ∀ r ∈ R, d * r * d⁻¹ ∈ R)
    (hodd' : ∀ r ∈ R, Odd (orderOf r)) : R = ⊥ := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hE1 : R ⊓ E1 F = ⊥ :=
    inf_eq_bot_of_pPrimeCore hnorm hodd' ((E1_le_X0 h2).trans X0_le_centralizer) (pPrimeCore_E1 h2 h4)
  have hE2 : R ⊓ E2 F = ⊥ :=
    inf_eq_bot_of_pPrimeCore hnorm hodd' ((E2_le_X0 h2).trans X0_le_centralizer) (pPrimeCore_E2 h2 h4)
  have hX0 : ∀ m ∈ R, m ∈ X0 F → m = 1 := by
    intro m hmR hmX
    have hc : ∀ y ∈ E2 F, m * y = y * m := by
      intro y hy
      have hyD : y ∈ centralizer {u1 F} := (E2_le_X0 h2).trans X0_le_centralizer hy
      have h1 : y * m⁻¹ * y⁻¹ ∈ R := hnorm y hyD m⁻¹ (R.inv_mem hmR)
      have h2' : m * y * m⁻¹ ∈ E2 F := conj_mem_E2 h2 hmX hy
      have h3 : m * (y * m⁻¹ * y⁻¹) ∈ R ⊓ E2 F := by
        refine ⟨R.mul_mem hmR h1, ?_⟩
        have : m * (y * m⁻¹ * y⁻¹) = (m * y * m⁻¹) * y⁻¹ := by group
        rw [this]
        exact (E2 F).mul_mem h2' ((E2 F).inv_mem hy)
      rw [hE2, Subgroup.mem_bot] at h3
      have h4' : m * y * m⁻¹ = y := by
        have : (m * y * m⁻¹) * y⁻¹ = 1 := by
          have e : m * (y * m⁻¹ * y⁻¹) = (m * y * m⁻¹) * y⁻¹ := by group
          rw [← e]; exact h3
        exact mul_inv_eq_one.mp this
      calc m * y = (m * y * m⁻¹) * m := by group
        _ = y * m := by rw [h4']
    have hm1 : m ∈ E1 F := mem_E1_of_commute_E2 h2 hmX hc
    have : m ∈ R ⊓ E1 F := ⟨hmR, hm1⟩
    rw [hE1, Subgroup.mem_bot] at this
    exact this
  rw [eq_bot_iff]
  intro r hr
  have hrsq : r * r ∈ R := R.mul_mem hr hr
  have hrX : r * r ∈ X0 F := sq_mem_X0 (hRD hr)
  have hsq : r * r = 1 := hX0 _ hrsq hrX
  have hdvd : orderOf r ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exact (Subgroup.mem_bot).mpr (orderOf_eq_one_iff.mp h1)
  · exact absurd (h1 ▸ hodd' r hr) (by decide)

end Model

end CFSG.GH74.GLS.Stage2.Local.P34
