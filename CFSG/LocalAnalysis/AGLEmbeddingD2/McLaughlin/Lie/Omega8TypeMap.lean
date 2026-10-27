module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.Omega8NativeIso
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.D4Types

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.Lie

open CFSG.EvenSmallLie.OmegaEight CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits

@[expose] def rho4 : Equiv.Perm (Fin 4) := ⟨![2, 1, 3, 0], ![3, 1, 0, 2], by decide, by decide⟩

@[expose] def tau4 : Equiv.Perm (Fin 4) := Equiv.swap 2 3

theorem rhoPerm_two_mul (k : Fin 4) : rhoPerm.getD (2 * k) 0 = 2 * (rho4 k : ℕ) ∧
    rhoPerm.getD (2 * k + 1) 0 = 2 * (rho4 k : ℕ) + 1 := by
  fin_cases k <;> decide

theorem tauPerm_two_mul (k : Fin 4) : tauPerm.getD (2 * k) 0 = 2 * (tau4 k : ℕ) ∧
    tauPerm.getD (2 * k + 1) 0 = 2 * (tau4 k : ℕ) + 1 := by
  fin_cases k <;> decide

@[expose] def PosUnipotentSimple : Prop :=
  posUnipotent (plusDatum 4 F2 three_le_four) =
    ⨆ i : Fin 4, (plusDatum 4 F2 three_le_four).rootGroup (Pi.single i 1)


theorem isTypeMap_autSpin (hU : PosUnipotentSimple) {a : Equiv.Perm (Fin 360)} (ha : a ∈ autT)
    (σ : Equiv.Perm (Fin 4))
    (hσ : ∀ k : Fin 4, a * gen (2 * k) * a⁻¹ = gen (2 * (σ k : ℕ)) ∧
      a * gen (2 * k + 1) * a⁻¹ = gen (2 * (σ k : ℕ) + 1)) :
    IsTypeMap (autSpin ⟨a, ha⟩) σ := by
  set β := autSpin ⟨a, ha⟩ with hβ
  have hpos : ∀ k : Fin 4,
      ((plusDatum 4 F2 three_le_four).rootGroup (Pi.single k 1)).map β.toMonoidHom =
        (plusDatum 4 F2 three_le_four).rootGroup (Pi.single (σ k) 1) := by
    intro k
    rw [rootGroup_single_eq_zpowers card_F2, rootGroup_single_eq_zpowers card_F2,
      MonoidHom.map_zpowers]
    congr 1
    exact autSpin_xRoot ha (by have := k.isLt; omega) (by have := (σ k).isLt; omega) (hσ k).1
  have hneg : ∀ k : Fin 4,
      ((plusDatum 4 F2 three_le_four).rootGroup (-Pi.single k 1)).map β.toMonoidHom =
        (plusDatum 4 F2 three_le_four).rootGroup (-Pi.single (σ k) 1) := by
    intro k
    rw [rootGroup_neg_single_eq_zpowers card_F2, rootGroup_neg_single_eq_zpowers card_F2,
      MonoidHom.map_zpowers]
    congr 1
    exact autSpin_xRoot ha (by have := k.isLt; omega) (by have := (σ k).isLt; omega) (hσ k).2
  have hL : ∀ k : Fin 4,
      (rankOne (plusDatum 4 F2 three_le_four).rootGroup k).map β.toMonoidHom =
        rankOne (plusDatum 4 F2 three_le_four).rootGroup (σ k) := by
    intro k
    show ((plusDatum 4 F2 three_le_four).rootGroup (Pi.single k 1) ⊔
      (plusDatum 4 F2 three_le_four).rootGroup (-Pi.single k 1)).map β.toMonoidHom =
      (plusDatum 4 F2 three_le_four).rootGroup (Pi.single (σ k) 1) ⊔
      (plusDatum 4 F2 three_le_four).rootGroup (-Pi.single (σ k) 1)
    rw [Subgroup.map_sup, hpos, hneg]
  have hB : (borel4 F2).map β.toMonoidHom = borel4 F2 := by
    rw [borel4_eq_posUnipotent card_F2, hU, Subgroup.map_iSup]
    simp_rw [hpos]
    exact Equiv.iSup_comp (g := fun k : Fin 4 =>
      (plusDatum 4 F2 three_le_four).rootGroup (Pi.single k 1)) σ
  intro J
  refine ⟨1, ?_⟩
  rw [MulAut.conj.map_one, map_one_mulAut, par, par, Subgroup.map_sup, hB, Subgroup.map_iSup]
  congr 1
  simp_rw [Subgroup.map_iSup, hL]
  exact iSup_image.symm

theorem isTypeMap_rho (hU : PosUnipotentSimple) :
    IsTypeMap (autSpin ⟨gen 8, gen_mem_autT (by norm_num)⟩) rho4 :=
  isTypeMap_autSpin hU _ rho4 fun k => by
    have hk : 2 * (k : ℕ) < 8 := by have := k.isLt; omega
    have hk' : 2 * (k : ℕ) + 1 < 8 := by have := k.isLt; omega
    rw [conj_gen_rho hk, conj_gen_rho hk', (rhoPerm_two_mul k).1, (rhoPerm_two_mul k).2]
    exact ⟨rfl, rfl⟩

theorem isTypeMap_tau (hU : PosUnipotentSimple) :
    IsTypeMap (autSpin ⟨gen 9, gen_mem_autT (by norm_num)⟩) tau4 :=
  isTypeMap_autSpin hU _ tau4 fun k => by
    have hk : 2 * (k : ℕ) < 8 := by have := k.isLt; omega
    have hk' : 2 * (k : ℕ) + 1 < 8 := by have := k.isLt; omega
    rw [conj_gen_tau hk, conj_gen_tau hk', (tauPerm_two_mul k).1, (tauPerm_two_mul k).2]
    exact ⟨rfl, rfl⟩

theorem exists_isTypeMap (hU : PosUnipotentSimple) (β : MulAut (spinGroup (quadPlus 4 F2))) :
    ∃ σ : Equiv.Perm (Fin 4), σ 1 = 1 ∧ IsTypeMap β σ := by
  suffices h : ∀ x ∈ Subgroup.closure {g | ∃ i < 10, gen i = g}, ∀ hx : x ∈ autT,
      ∃ σ : Equiv.Perm (Fin 4), σ 1 = 1 ∧ IsTypeMap (autSpin ⟨x, hx⟩) σ by
    obtain ⟨⟨a, ha⟩, rfl⟩ := autSpin_bijective.2 β
    exact h a (by rw [← autT_eq]; exact ha) ha
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    intro hxA
    by_cases h8 : i < 8
    · refine ⟨1, rfl, ?_⟩
      have e : (⟨gen i, hxA⟩ : autT) = ⟨gen i, omegaT_le_autT (gen_mem_omegaT h8)⟩ := rfl
      rw [e, autSpin_omegaT (gen_mem_omegaT h8)]
      exact isTypeMap_conj _
    · interval_cases i
      · exact ⟨rho4, by decide, isTypeMap_rho hU⟩
      · exact ⟨tau4, by decide, isTypeMap_tau hU⟩
  | one =>
    intro h1
    refine ⟨1, rfl, ?_⟩
    have e : (⟨1, h1⟩ : autT) = 1 := rfl
    rw [e, map_one]
    exact isTypeMap_one
  | mul x y hx hy ihx ihy =>
    intro hxy
    have hxA : x ∈ autT := by rw [autT_eq]; exact hx
    have hyA : y ∈ autT := by rw [autT_eq]; exact hy
    obtain ⟨σ, hσ1, hσ⟩ := ihx hxA
    obtain ⟨τ, hτ1, hτ⟩ := ihy hyA
    refine ⟨σ * τ, by rw [Equiv.Perm.mul_apply, hτ1, hσ1], ?_⟩
    have e : (⟨x * y, hxy⟩ : autT) = ⟨x, hxA⟩ * ⟨y, hyA⟩ := rfl
    rw [e, map_mul]
    exact hσ.mul hτ
  | inv x hx ihx =>
    intro hxi
    have hxA : x ∈ autT := by rw [autT_eq]; exact hx
    obtain ⟨σ, hσ1, hσ⟩ := ihx hxA
    refine ⟨σ⁻¹, by rw [Equiv.Perm.inv_eq_iff_eq, hσ1], ?_⟩
    have e : (⟨x⁻¹, hxi⟩ : autT) = (⟨x, hxA⟩ : autT)⁻¹ := rfl
    rw [e, map_inv]
    exact hσ.inv

end CFSG.AGLEmbeddingD2.McLaughlin.Lie
