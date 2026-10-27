module

public import CFSG.GF2Type.Smith1979.W4AsE11Five
public import CFSG.LargeExtraspecial.S111SIIso

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4As

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.Open Subgroup Module

variable {G : Type} [Group G] [Finite G] {S : Setting G}

section Iso
open CFSG.LargeExtraspecial.S11 Module
variable {g : G}

theorem IsoCfg.three_le_finrank_w4 {t y : S.O} (C : IsoCfg S t y) (hy : Hyp S g)
    (hirr : ¬ S.IsReducible) (h4 : 4 ≤ S.width) (ht : t ∈ S.Lbar g) :
    3 ≤ finrank (ZMod 2) (Vt S g t) := by
  have haQ := hy.hyp4.conj_mem
  have ha0 := cl_conj_z_ne_zero S haQ hy.hyp4.conj_ne
  have htop := span_translates_eq_top hirr (s := (Vt S g t : Set S.Qt)) (cl_a_mem_Vt ht) ha0
  set fy : S.Qt →ₗ[ZMod 2] S.Qt :=
    (((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) with hfy
  set fy' : S.Qt →ₗ[ZMod 2] S.Qt :=
    (((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) with hfy'
  have hle : Submodule.span (ZMod 2) {w | ∃ x ∈ S.Mbar, ∃ u ∈ (Vt S g t : Set S.Qt),
      w = ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u} ≤
      Vt S g t ⊔ (Vt S g t).map fy ⊔ (Vt S g t).map fy' := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, v, hv, rfl⟩
    obtain ⟨u, hu, hut⟩ := C.dec x hx
    have hcv := apply_mem_Vt' haQ (mul_mem (inv_mem (C.u_mem hu)) hx) hut hv
    have e1 : ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
        ((u : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((u⁻¹ * x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
      rw [← O_mul_apply, mul_inv_cancel_left]
    rw [e1]
    rcases hu with rfl | rfl | rfl
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (by simpa using hcv))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨_, hcv, rfl⟩)
    · exact Submodule.mem_sup_right ⟨_, hcv, rfl⟩
  have h1 := Submodule.finrank_mono hle
  rw [htop, finrank_top, S.finrank_Qt_eq_two_mul_width] at h1
  have h2 := Submodule.finrank_add_le_finrank_add_finrank
    (Vt S g t ⊔ (Vt S g t).map fy) ((Vt S g t).map fy')
  have h3 := Submodule.finrank_add_le_finrank_add_finrank (Vt S g t) ((Vt S g t).map fy)
  have h4 := Submodule.finrank_map_le fy (Vt S g t)
  have h5 := Submodule.finrank_map_le fy' (Vt S g t)
  omega

end Iso

section IsoW4
open CFSG.LargeExtraspecial.S11 Module QuadraticMap
variable {g : G}

theorem isoCfg_of_isolated_w4 (hy : Hyp S g) (hw : S.width = 4) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1)
    (hiso : ∀ x ∈ S.Mbar, (x * t * x⁻¹) * t = t * (x * t * x⁻¹) → x * t * x⁻¹ = t) :
    ∃ y : S.O, IsoCfg S t y := by
  have haQ := hy.hyp4.conj_mem
  have htM : t ∈ S.Mbar := S.Lbar_le_Mbar g ht
  have ht2 : t * t = 1 := S4.mul_self_of_mem_Lbar S haQ ht
  have := Fintype.ofFinite S.Mbar
  have ht'1 : (⟨t, htM⟩ : S.Mbar) ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have ht'2 : (⟨t, htM⟩ : S.Mbar) * ⟨t, htM⟩ = 1 := Subtype.ext ht2
  obtain ⟨N, hN, hodd, hcomm⟩ := CFSG.ZStar.glauberman_zStar S.Mbar ⟨t, htM⟩ ht'1 ht'2
    fun x hx => Subtype.ext (hiso x x.2 (congrArg Subtype.val hx))
  have hN3 : Nat.card N ∣ 3 := (Subgroup.card_dvd_of_le (S5.le_timmesfeldOddCore hN hodd)).trans
    (card_oddCore_dvd_three_w4 hy hw)
  have hcomm' : ∀ x : S.Mbar, x * ⟨t, htM⟩ * x⁻¹ * (⟨t, htM⟩ : S.Mbar)⁻¹ ∈ N := hcomm
  have hnc : ¬ ∀ x : S.Mbar, x * ⟨t, htM⟩ * x⁻¹ = ⟨t, htM⟩ := fun h =>
    not_central_of_mem_Mbar htM ht2 ht1 fun x hx => congrArg Subtype.val (h ⟨x, hx⟩)
  have hcard : Nat.card N = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hN3 with h | h
    · exfalso
      apply hnc
      intro x
      have h1 := hcomm' x
      rw [Subgroup.card_eq_one.mp h, mem_bot] at h1
      exact mul_inv_eq_one.mp h1
    · exact h
  obtain ⟨y, hS⟩ := exists_inv_of_card_three hN hcard ht'2 hcomm' hnc
  refine ⟨(y : S.O), htM, y.2, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨u, hu, hut⟩ := hS.exists_mem_cent ⟨x, hx⟩
    refine ⟨(u : S.O), ?_, congrArg Subtype.val hut⟩
    rcases hu with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rcases hS.commute_or_commute ⟨x, hx⟩ with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)

theorem IsoCfg.rbar_ne_w4 {t y : S.O} (C : IsoCfg S t y) (hy : Hyp S g) (hirr : ¬ S.IsReducible)
    (h4 : 4 ≤ S.width) (ht : t ∈ S.Lbar g) : Rbar S g t ≠ S.Lbar g := by
  classical
  intro hR
  have haQ := hy.hyp4.conj_mem
  set a := S.cl (g * S.z * g⁻¹) with ha
  have ha0 : a ≠ 0 := cl_conj_z_ne_zero S haQ hy.hyp4.conj_ne
  have hVle := Vt_le_span_of_Rbar_eq hy.hyp4 hy.cons hR
  have hfix : ∀ x ∈ S.Mbar, x * t = t * x → ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a = a := by
    intro x hx hxt
    have h1 : ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a ∈ (ZMod 2) ∙ a :=
      hVle (apply_mem_Vt' haQ hx hxt (cl_a_mem_Vt ht))
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp h1
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases r with rfl | rfl
    · exfalso
      rw [zero_smul] at hr
      exact ha0 (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).injective (by rw [← hr, map_zero]))
    · rw [one_smul] at hr
      exact hr.symm
  have htop := span_translates_eq_top hirr (Set.mem_singleton a) ha0
  set T : Finset S.Qt := {a, ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a,
    ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a} with hT
  have hle : Submodule.span (ZMod 2) {w | ∃ x ∈ S.Mbar, ∃ u ∈ ({a} : Set S.Qt),
      w = ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u} ≤ Submodule.span (ZMod 2) (T : Set S.Qt) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, _, rfl, rfl⟩
    obtain ⟨u, hu, hut⟩ := C.dec x hx
    have hc : u⁻¹ * x ∈ S.Mbar := mul_mem (inv_mem (C.u_mem hu)) hx
    have hxa : ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a = ((u : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a := by
      have h1 := hfix _ hc hut
      rw [O_mul_apply] at h1
      calc ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a
          = ((u * (u⁻¹ * x) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a := by rw [mul_inv_cancel_left]
        _ = ((u : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a := by rw [O_mul_apply, O_mul_apply, h1]
    rw [hxa]
    apply Submodule.subset_span
    rcases hu with rfl | rfl | rfl <;> simp [hT]
  have h1 := Submodule.finrank_mono hle
  rw [htop, finrank_top, S.finrank_Qt_eq_two_mul_width] at h1
  have h2 : finrank (ZMod 2) (Submodule.span (ZMod 2) (T : Set S.Qt)) ≤ T.card :=
    finrank_span_finset_le_card (R := ZMod 2) T
  have h3 : T.card ≤ 3 := Finset.card_le_three
  omega

theorem IsoCfg.false_of_linCase_w4 {t y : S.O} (C : IsoCfg S t y) (hy : Hyp S g)
    (hirr : ¬ S.IsReducible) (h4 : 4 ≤ S.width) (ht : t ∈ S.Lbar g) (hL : LinCase S g ht) :
    False := by
  have haQ := hy.hyp4.conj_mem
  have ha0 := cl_conj_z_ne_zero S haQ hy.hyp4.conj_ne
  have h3 : 3 ≤ finrank (ZMod 2) (Vt S g t) := by
    exact IsoCfg.three_le_finrank_w4 C hy hirr h4 ht
  have haV := cl_a_mem_Vt ht
  apply ha0
  refine S.q_nondegenerate.1 _ fun x => ?_
  rw [polarBilin_apply_apply]
  obtain ⟨v₁, h₁, v₂, h₂, v₃, h₃, rfl⟩ := C.exists_decomp hy hirr ht x
  rw [polar_add_right, polar_add_right,
    C.polar_eq_zero hy h3 ht hL (Or.inr (Or.inl rfl)) haV h₂,
    C.polar_eq_zero hy h3 ht hL (Or.inr (Or.inr rfl)) haV h₃]
  have h1 := C.polar_eq_zero hy h3 ht hL (Or.inl rfl) haV h₁
  simp only [OneMemClass.coe_one, LinearEquiv.coe_one, id_eq] at h1
  rw [h1, add_zero, add_zero]

theorem false_of_isolated_w4 (hy : Hyp S g) (hirr : ¬ S.IsReducible) (hw : S.width = 4)
    {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hiso : ∀ x ∈ S.Mbar, (x * t * x⁻¹) * t = t * (x * t * x⁻¹) → x * t * x⁻¹ = t) :
    False := by
  obtain ⟨y, C⟩ := isoCfg_of_isolated_w4 hy hw ht ht1 hiso
  rcases hy.lin ht ht1 with hR | hL
  · exact IsoCfg.rbar_ne_w4 C hy hirr (by omega) ht hR
  · exact IsoCfg.false_of_linCase_w4 C hy hirr (by omega) ht hL

end IsoW4

end CFSG.GF2Type.Smith1979.W4As
