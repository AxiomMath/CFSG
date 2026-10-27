module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage4.T2SL2A
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2

section Aux

variable {F : Type} [Field F]

theorem t2Bo_conj_sl2U_entries (g : SL2 F) (c : F) :
    ((g * sl2U c * g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0 =
        1 - c * (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 ∧
      ((g * sl2U c * g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 1 =
        c * (g : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 ∧
      ((g * sl2U c * g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 =
        -(c * (g : Matrix (Fin 2) (Fin 2) F) 1 0 ^ 2) ∧
      ((g * sl2U c * g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 1 =
        1 + c * (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 := by
  have hdet := t2A_det g
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination hdet
  · ring
  · ring
  · linear_combination hdet

theorem t2Bo_sl2D_conj_entries (t : Fˣ) (x : SL2 F) :
    ((sl2D t * x * (sl2D t)⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0 =
        (x : Matrix (Fin 2) (Fin 2) F) 0 0 ∧
      ((sl2D t * x * (sl2D t)⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 1 =
        (t : F) ^ 2 * (x : Matrix (Fin 2) (Fin 2) F) 0 1 := by
  rw [t2A_sl2D_inv]
  refine ⟨?_, ?_⟩ <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] <;> simp
  · field_simp
  · ring

theorem t2Bo_exists_sq_ne_one [Finite F] (h5 : 5 ≤ Nat.card F) : ∃ a : Fˣ, (a : F) ^ 2 ≠ 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hcard : 5 ≤ Fintype.card F := by rwa [← Nat.card_eq_fintype_card]
  have hlt : ({0, 1, -1} : Finset F).card < (Finset.univ : Finset F).card := by
    calc ({0, 1, -1} : Finset F).card ≤ 3 := Finset.card_le_three
      _ < Fintype.card F := by omega
      _ = (Finset.univ : Finset F).card := Finset.card_univ.symm
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
  obtain ⟨ha0, ha1, ha2⟩ := ha
  refine ⟨Units.mk0 a ha0, fun h => ?_⟩
  have h' : (a - 1) * (a + 1) = 0 := by
    simp only [Units.val_mk0] at h
    linear_combination h
  rcases mul_eq_zero.1 h' with h'' | h''
  · exact ha1 (sub_eq_zero.1 h'')
  · exact ha2 (eq_neg_of_add_eq_zero_left h'')

end Aux

theorem t2C_sylow_torus {F : Type} [Field F] [Finite F] (h5 : 5 ≤ Nat.card F)
    (Y : Subgroup (SL2 F)) (hY : Nat.card ↥Y = Nat.card F)
    (hn : ∀ d ∈ T2.tSub F, ∀ y ∈ Y, d * y * d⁻¹ ∈ Y) :
    Y = T2.uSub F ∨ Y = T2.lSub F := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hq⟩ := FiniteField.card F (ringChar F)
  have hcard : Nat.card F = ringChar F ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hq]
  obtain ⟨g, hg⟩ := CFSG.SL2MinimalFaithful.exists_conj_unipotent_mem hp hcard hY
  have hg' : ∀ t : F, g * sl2U t * g⁻¹ ∈ Y := hg
  have hsurj : ∀ y ∈ Y, ∃ c : F, y = g * sl2U c * g⁻¹ := by
    let f : F → Y := fun c => ⟨g * sl2U c * g⁻¹, hg' c⟩
    have hinj : Function.Injective f := by
      intro c c' h
      have h1 := congrArg Subtype.val h
      simp only [f] at h1
      exact sl2U_injective (mul_left_cancel (mul_right_cancel h1))
    have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le (by rw [hY])
    intro y hy
    obtain ⟨c, hc⟩ := hbij.2 ⟨y, hy⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  obtain ⟨a, ha⟩ := t2Bo_exists_sq_ne_one h5
  obtain ⟨c, hc⟩ := hsurj _ (hn (sl2D a) (sl2D_mem_tSub a) _ (hg' 1))
  obtain ⟨e00, e01, -, -⟩ := t2Bo_conj_sl2U_entries g c
  obtain ⟨f00, f01, -, -⟩ := t2Bo_conj_sl2U_entries g 1
  obtain ⟨k00, k01⟩ := t2Bo_sl2D_conj_entries a (g * sl2U 1 * g⁻¹)
  have hc00 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 0 0) hc
  have hc01 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 0 1) hc
  rw [k00, f00, e00] at hc00
  rw [k01, f01, e01] at hc01
  have hprod : (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    by_contra hne
    have hc1 : c = 1 := by
      have h : (c - 1) * ((g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 0) = 0 := by
        linear_combination hc00
      exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_right hne)
    have hg0 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul hne
    rw [hc1] at hc01
    apply ha
    have h : ((a : F) ^ 2 - 1) * (g : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 = 0 := by
      linear_combination hc01
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_right (pow_ne_zero 2 hg0))
  rcases mul_eq_zero.1 hprod with h00 | h10
  · right
    refine Subgroup.eq_of_le_of_card_ge (fun y hy => ?_) (by rw [card_lSub, hY])
    obtain ⟨c, rfl⟩ := hsurj y hy
    obtain ⟨e00, e01, -, e11⟩ := t2Bo_conj_sl2U_entries g c
    exact ⟨by rw [e00, h00]; ring, by rw [e11, h00]; ring, by rw [e01, h00]; ring⟩
  · left
    refine Subgroup.eq_of_le_of_card_ge (fun y hy => ?_) (by rw [card_uSub, hY])
    obtain ⟨c, rfl⟩ := hsurj y hy
    obtain ⟨e00, -, e10, e11⟩ := t2Bo_conj_sl2U_entries g c
    exact ⟨by rw [e00, h10]; ring, by rw [e11, h10]; ring, by rw [e10, h10]; ring⟩

end CFSG.GH74.GLS.Stage4.Rest
