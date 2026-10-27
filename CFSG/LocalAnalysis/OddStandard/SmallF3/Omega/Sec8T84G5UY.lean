module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3AS
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84GTab
import CFSG.ClassicalInvolution.Balance.Basic
import CFSG.GroupTheory.CommutingProductFixedSubgroup
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Prod
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3AB
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3AG
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3AQ
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3BM
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G5Lift

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

section Helpers

variable {G : Type} [Group G]

private lemma sec8t84g5u_unique {A B : Subgroup G} (hAB : A ⊓ B = ⊥) {a a' b b' : G}
    (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B) (h : a * b = a' * b') :
    a = a' ∧ b = b' := by
  have hmem : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have h1 : a'⁻¹ * a = 1 := by
    have hmem' : a'⁻¹ * a ∈ A ⊓ B :=
      Subgroup.mem_inf.mpr ⟨A.mul_mem (A.inv_mem ha') ha, by
        rw [hmem]
        exact B.mul_mem hb' (B.inv_mem hb)⟩
    rw [hAB] at hmem'
    exact Subgroup.mem_bot.mp hmem'
  have h2 : b' * b⁻¹ = 1 := by rw [← hmem]; exact h1
  exact ⟨(inv_mul_eq_one.mp h1).symm, (mul_inv_eq_one.mp h2).symm⟩

private lemma sec8t84g5u_mem_sup {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  obtain ⟨a, ha, b, hb, hab⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hc hx
  exact ⟨a, ha, b, hb, hab.symm⟩

private lemma sec8t84g5u_fix {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB : A ⊓ B = ⊥) {y : G}
    (hyA : ∀ a ∈ A, y * a * y⁻¹ ∈ A) (hyB : ∀ b ∈ B, y * b * y⁻¹ ∈ B)
    (hA1 : ∀ a ∈ A, y * a = a * y → a = 1)
    (hB1 : ∀ b ∈ B, y * b = b * y → b = 1) :
    ∀ u ∈ A ⊔ B, y * u = u * y → u = 1 := by
  intro u hu hyu
  obtain ⟨a, ha, b, hb, rfl⟩ := sec8t84g5u_mem_sup hc hu
  have hconj : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
  have h_eq : (y * a * y⁻¹) * (y * b * y⁻¹) = a * b := by
    rw [← hconj]
    calc y * (a * b) * y⁻¹ = ((a * b) * y) * y⁻¹ := by rw [hyu]
      _ = a * b := by group
  have huniq := sec8t84g5u_unique hAB (hyA a ha) ha (hyB b hb) hb h_eq
  have hya : y * a = a * y := by
    calc y * a = (y * a * y⁻¹) * y := by group
      _ = a * y := by rw [huniq.1]
  have hyb : y * b = b * y := by
    calc y * b = (y * b * y⁻¹) * y := by group
      _ = b * y := by rw [huniq.2]
  rw [hA1 a ha hya, hB1 b hb hyb, one_mul]

private lemma sec8t84g5u_conj_conj {t : G} (ht : t * t = 1) (A : Subgroup G) :
    (A.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = A := by
  rw [Subgroup.map_map]
  have hcomp : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    rw [inv_eq_of_mul_eq_one_right ht]
    calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
      _ = x := by simp [ht]
  rw [hcomp, Subgroup.map_id]

end Helpers

theorem sec8t84g_U_y (hP : Sec8T84FactP) (hS4 : Sec8T84FactS4) {G : Type} [Group G]
    [Finite G] {t : G} {L : Subgroup G} {E Y1 Y2 T T1 T2 V1 V2 F1 F2 : Subgroup G}
    (h : Sec8T84GSet G t E Y1 Y2 T T1 T2 V1 V2 F1 F2) {γ : G} (hγ2 : γ * γ = 1)
    (htγ : t * γ = γ * t)
    (hE1 : E.map (MulAut.conj γ).toMonoidHom = F1 ⊔ F2)
    (hE0 : (F1 ⊔ F2).map (MulAut.conj γ).toMonoidHom = E)
    (hU1 : (V1 ⊔ F1).map (MulAut.conj γ).toMonoidHom = V1 ⊔ F1)
    (hU2 : (V2 ⊔ F2).map (MulAut.conj γ).toMonoidHom = V2 ⊔ F2)
    (hC1 : IsElemAb2 ((V1 ⊔ F1) ⊓ centralizer ({γ} : Set G)) 2)
    (hC2 : IsElemAb2 ((V2 ⊔ F2) ⊓ centralizer ({γ} : Set G)) 2)
    (hJ0 : (E ⊔ (F1 ⊔ F2)) ⊓ centralizer ({t} : Set G) ≤ L) :
    ∃ (U : Subgroup G) (y : G), IsElemAb2 U 4 ∧ U ≤ centralizer ({γ} : Set G) ∧
      t ∈ normalizer (U : Set G) ∧ U ⊓ centralizer ({t} : Set G) ≤ L ∧
      Odd (orderOf y) ∧ y ∈ centralizer ({γ} : Set G) ∧ y ∈ normalizer (U : Set G) ∧
      ∀ u ∈ U, y * u = u * y → u = 1 := by
  let U1 : Subgroup G := V1 ⊔ F1
  have hU1def : U1 = V1 ⊔ F1 := rfl
  let U2 : Subgroup G := V2 ⊔ F2
  have hU2def : U2 = V2 ⊔ F2 := rfl
  let C1 : Subgroup G := U1 ⊓ centralizer ({γ} : Set G)
  have hC1def : C1 = U1 ⊓ centralizer ({γ} : Set G) := rfl
  let C2 : Subgroup G := U2 ⊓ centralizer ({γ} : Set G)
  have hC2def : C2 = U2 ⊓ centralizer ({γ} : Set G) := rfl
  let W : Subgroup G := E ⊔ (F1 ⊔ F2)
  have hWdef : W = E ⊔ (F1 ⊔ F2) := rfl
  let Q : Subgroup G := sec8t84g_Q E (F1 ⊔ F2)
  have hQdef : Q = sec8t84g_Q E (F1 ⊔ F2) := rfl
  let O : Subgroup G := oddCoreIn Q
  have hOdef : O = oddCoreIn Q := rfl
  have hU1leT1 : U1 ≤ T1 := by
    rw [hU1def]
    exact sup_le h.D.mod1.V_le h.D.mod1.F_le
  have hU2leT2 : U2 ≤ T2 := by
    rw [hU2def]
    exact sup_le (sec8t84g3a_V2_le_T2 h.D) (sec8t84g3a_F2_le_T2 h.D)
  have hcomm : ∀ a ∈ U1, ∀ b ∈ U2, a * b = b * a :=
    fun a ha b hb => h.D.comm a (hU1leT1 ha) b (hU2leT2 hb)
  have hUinf : U1 ⊓ U2 = ⊥ := by
    rw [hU1def, hU2def]
    exact sec8t84g3a_U_inf h.D
  have hUWeq : W = U1 ⊔ U2 := by
    rw [hWdef, hU1def, hU2def]
    exact sec8t84g3a_W_eq h.D
  have hC1le : C1 ≤ U1 := by rw [hC1def]; exact inf_le_left
  have hC2le : C2 ≤ U2 := by rw [hC2def]; exact inf_le_left
  have hC1cent : C1 ≤ centralizer ({γ} : Set G) := by
    rw [hC1def]; exact inf_le_right
  have hC2cent : C2 ≤ centralizer ({γ} : Set G) := by
    rw [hC2def]; exact inf_le_right
  have hC1' : IsElemAb2 C1 2 := hC1
  have hC2' : IsElemAb2 C2 2 := hC2
  have hcommC : ∀ a ∈ C1, ∀ b ∈ C2, a * b = b * a :=
    fun a ha b hb => hcomm a (hC1le ha) b (hC2le hb)
  have hinfC : C1 ⊓ C2 = ⊥ :=
    bot_unique ((inf_le_inf hC1le hC2le).trans (le_of_eq hUinf))
  have hC12 : IsElemAb2 (C1 ⊔ C2) 4 := by
    refine ⟨?_, ?_⟩
    · exact hC1'.1.sup_of_commute hC2'.1 hcommC
    · rw [sec124_card_sup hcommC hinfC, hC1'.2, hC2'.2]
      norm_num
  have hUcent : (C1 ⊔ C2) ≤ centralizer ({γ} : Set G) := sup_le hC1cent hC2cent
  have hU1map : U1.map (MulAut.conj t).toMonoidHom = U2 := by
    rw [hU1def, hU2def, Subgroup.map_sup, h.D.V2_eq, h.D.F2_eq]
  have hU2map : U2.map (MulAut.conj t).toMonoidHom = U1 := by
    rw [← hU1map]
    exact sec8t84g5u_conj_conj h.D.t_sq U1
  have htC : t ∈ centralizer ({γ} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact htγ
  have hCcentmap : (centralizer ({γ} : Set G)).map (MulAut.conj t).toMonoidHom =
      centralizer ({γ} : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer htC)
  have hC1map : C1.map (MulAut.conj t).toMonoidHom = C2 := by
    rw [hC1def, hC2def, Subgroup.map_inf _ _ _ (MulAut.conj t).injective, hU1map, hCcentmap]
  have hC2map : C2.map (MulAut.conj t).toMonoidHom = C1 := by
    rw [hC2def, hC1def, Subgroup.map_inf _ _ _ (MulAut.conj t).injective, hU2map, hCcentmap]
  have ht_norm : t ∈ normalizer ((C1 ⊔ C2 : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe (MulAut.conj t),
      Subgroup.map_sup, hC1map, hC2map, sup_comm]
  have hU1W : U1 ≤ W := by rw [hUWeq]; exact le_sup_left
  have hU2W : U2 ≤ W := by rw [hUWeq]; exact le_sup_right
  have hUCW : C1 ⊔ C2 ≤ W := by
    rw [hUWeq]
    exact sup_le (hC1le.trans le_sup_left) (hC2le.trans le_sup_right)
  have hUCJ : (C1 ⊔ C2) ⊓ centralizer ({t} : Set G) ≤ L :=
    (inf_le_inf_right _ hUCW).trans hJ0
  obtain ⟨m, hmQ, hm3, hγm, hm1, hm2, hf1, hf2⟩ :=
    sec8t84g_exists_m hP hS4 h hγ2 hE1 hE0 hU1 hU2 hC1 hC2
  have hOodd : Odd (Nat.card O) :=
    CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn Q
  have hmO : m ∈ Subgroup.normalizer (O : Set G) :=
    CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn Q hmQ
  have hγO : γ ∈ Subgroup.normalizer (O : Set G) := (sec8t84g3a_gamma_Q hE1 hE0).2.1
  obtain ⟨y, -, hmy, hγy, hyOdd⟩ := sec8t84g5_lift hOodd hmO hγO hγ2 hm3 hγm
  have hOcent : O ≤ centralizer (W : Set G) := sec8t84g3a_O_cent h
  have hOW : ∀ o ∈ O, ∀ w ∈ W, w * o = o * w := by
    intro o ho w hw
    exact (Subgroup.mem_centralizer_iff.mp (hOcent ho)) w hw
  have hyw : ∀ w ∈ W, y * w * y⁻¹ = m * w * m⁻¹ := by
    intro w hw
    have hcomm_ow : w * (m⁻¹ * y) = (m⁻¹ * y) * w := hOW (m⁻¹ * y) hmy w hw
    calc y * w * y⁻¹ = (m * (m⁻¹ * y)) * w * (m * (m⁻¹ * y))⁻¹ := by group
      _ = m * ((m⁻¹ * y) * w * (m⁻¹ * y)⁻¹) * m⁻¹ := by group
      _ = m * w * m⁻¹ := by
          rw [← hcomm_ow]
          group
  have hyw_iff : ∀ w ∈ W, (y * w = w * y ↔ m * w = w * m) := by
    intro w hw
    constructor
    · intro h
      have h1 : m * w * m⁻¹ = w := by rw [← hyw w hw, h]; group
      calc m * w = (m * w * m⁻¹) * m := by group
        _ = w * m := by rw [h1]
    · intro h
      have h2 : y * w * y⁻¹ = w := by rw [hyw w hw, h]; group
      calc y * w = (y * w * y⁻¹) * y := by group
        _ = w * y := by rw [h2]
  have hyU1 : y ∈ Subgroup.normalizer (U1 : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro x hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨u, hu, rfl⟩ := hx
      change y * u * y⁻¹ ∈ U1
      rw [hyw u (hU1W hu)]
      exact (Subgroup.mem_normalizer_iff.mp hm1 u).mp hu
    · rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]
  have hyU2 : y ∈ Subgroup.normalizer (U2 : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro x hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨u, hu, rfl⟩ := hx
      change y * u * y⁻¹ ∈ U2
      rw [hyw u (hU2W hu)]
      exact (Subgroup.mem_normalizer_iff.mp hm2 u).mp hu
    · rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]
  have hyC : y ∈ centralizer ({γ} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * γ = (γ * y * γ⁻¹) * γ := by rw [hγy]
      _ = γ * y := by group
  have hyC1 : y ∈ Subgroup.normalizer (C1 : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.mpr ⟨hyU1, Subgroup.le_normalizer hyC⟩)
  have hyC2 : y ∈ Subgroup.normalizer (C2 : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.mpr ⟨hyU2, Subgroup.le_normalizer hyC⟩)
  have hyUU : y ∈ Subgroup.normalizer ((C1 ⊔ C2 : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp hyC1),
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp hyC2)]
  have hfix : ∀ u ∈ (C1 ⊔ C2 : Subgroup G), y * u = u * y → u = 1 :=
    sec8t84g5u_fix hcommC hinfC
      (fun a ha => (Subgroup.mem_normalizer_iff.mp hyC1 a).mp ha)
      (fun b hb => (Subgroup.mem_normalizer_iff.mp hyC2 b).mp hb)
      (fun a ha hya => hf1 a (hC1le ha) ((hyw_iff a (hU1W (hC1le ha))).mp hya))
      (fun b hb hyb => hf2 b (hC2le hb) ((hyw_iff b (hU2W (hC2le hb))).mp hyb))
  have hOdd_y : Odd (orderOf y) := by
    obtain ⟨k, hk⟩ := hyOdd
    rw [hk]
    exact Odd.pow (by decide : Odd 3)
  exact ⟨C1 ⊔ C2, y, hC12, hUcent, ht_norm, hUCJ, hOdd_y, hyC, hyUU, hfix⟩

end CFSG.OddStandard.SmallF3.Omega
