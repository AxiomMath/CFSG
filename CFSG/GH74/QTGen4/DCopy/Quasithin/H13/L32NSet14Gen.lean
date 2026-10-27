module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NSet14Act
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneLemma4
public import CFSG.Quasithin.Background.F8G2

public section

namespace CFSG.Quasithin.H13.L32NSet14

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace Setting_F4

variable [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V] (S : Setting_F4 G T L V V₂)
include S

theorem gen_F4 : conjClosure V₂ (L₁Of L (fsuV1 T V)) = V := by
  obtain ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩ := S.exists_basis_F4
  obtain ⟨x, hxL, -, hxa, -⟩ := S.exists_x_F4 hz hz1 ha haV hb hbV
  have hV₂W : V₂ ≤ conjClosure V₂ (L₁Of L (fsuV1 T V)) := fun v hv =>
    subset_closure ⟨1, one_mem _, v, hv, by group⟩
  have hWV : conjClosure V₂ (L₁Of L (fsuV1 T V)) ≤ V := (closure_le _).mpr (by
    rintro _ ⟨h, hh, v, hv, rfl⟩
    exact (mem_normalizer_iff.mp (S.LV_F4 (Setting.L1_le hh).1) v).mp (S.hV2.2.1 hv))
  have hbW : b ∈ conjClosure V₂ (L₁Of L (fsuV1 T V)) := subset_closure ⟨x, hxL, a, ha, hxa⟩
  have h1 := Subgroup.card_dvd_of_le hV₂W
  have h2 := Subgroup.card_dvd_of_le hWV
  rw [S.hV2.2.2.2] at h1
  rw [S.card_V_F4] at h2
  have hne : Nat.card (conjClosure V₂ (L₁Of L (fsuV1 T V))) ≠ 4 := fun h => hbV (by
    rw [Subgroup.eq_of_le_of_card_ge hV₂W (by rw [h, S.hV2.2.2.2])]
    exact hbW)
  have h8 : Nat.card (conjClosure V₂ (L₁Of L (fsuV1 T V))) = 8 := by
    have hpos : 0 < Nat.card (conjClosure V₂ (L₁Of L (fsuV1 T V))) := Nat.card_pos
    have hle : Nat.card (conjClosure V₂ (L₁Of L (fsuV1 T V))) ≤ 8 :=
      Nat.le_of_dvd (by norm_num) h2
    obtain ⟨c, hc⟩ := h1
    rw [hc] at hle hpos hne ⊢
    have hc2 : c ≤ 2 := by omega
    have hc0 : 0 < c := by omega
    interval_cases c <;> omega
  exact Subgroup.eq_of_le_of_card_ge hWV (by rw [S.card_V_F4, h8])

theorem exists_L2_F4 {z w b : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) (hw : w ∈ V₂)
    (hwV : w ∉ fsuV1 T V) (hb : b ∈ V) (hbV : b ∉ V₂) : ∃ l ∈ L₁Of L V₂, l * z * l⁻¹ = w := by
  have hzV₂ := S.hV2.1 hz
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz).1
  have hwV' : w ∈ V := S.hV2.2.1 hw
  obtain ⟨l, hlL, hl3, -, hlz, hlw⟩ := S.exists_rot_F4 hb hzV hwV' hz1
    (fun h => hwV (h ▸ one_mem _)) (fun h => hbV (h ▸ hzV₂)) (fun h => hbV (h ▸ hw))
    (fun h => hwV (h ▸ hz)) (fun h => hbV (by
      have := mul_mem hw (inv_mem hzV₂)
      rwa [h, mul_inv_cancel_right] at this))
  have hlN : l ∈ normalizer (V₂ : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun v hv => ?_
    rcases S.mem_V2_F4 hw hwV hv with h | h
    · rcases S.eq_of_mem_V1_F4 hz hz1 h with rfl | rfl
      · rw [mul_one, mul_inv_cancel]
        exact one_mem _
      · rw [hlz]
        exact hw
    · rcases S.eq_of_mem_V1_F4 hz hz1 h with h' | h'
      · rw [eq_inv_of_mul_eq_one_right h',
          show l * w⁻¹ * l⁻¹ = (l * w * l⁻¹)⁻¹ by group, hlw]
        exact inv_mem (mul_mem hzV₂ hw)
      · rw [show v = w⁻¹ * z by rw [← h']; group,
          show l * (w⁻¹ * z) * l⁻¹ = (l * w * l⁻¹)⁻¹ * (l * z * l⁻¹) by group, hlw, hlz]
        exact mul_mem (inv_mem (mul_mem hzV₂ hw)) hw
  exact ⟨l, subset_closure ⟨⟨hlL, hlN⟩, 3, by decide, hl3⟩, hlz⟩

theorem genL_F4 : L ≤ A6.g1 T V ⊔ L₁Of L V₂ := by
  obtain ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩ := S.exists_basis_F4
  have hzV₂ := S.hV2.1 hz
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz).1
  have haV' : a ∈ V := S.hV2.2.1 ha
  have key : ∀ w ∈ V, w ≠ 1 → ∃ h ∈ A6.g1 T V ⊔ L₁Of L V₂, h * z * h⁻¹ = w := by
    intro w hw hw1
    by_cases hw2 : w ∈ V₂
    · by_cases hw1' : w ∈ fsuV1 T V
      · rcases S.eq_of_mem_V1_F4 hz hz1 hw1' with rfl | rfl
        · exact absurd rfl hw1
        · exact ⟨1, one_mem _, by group⟩
      · obtain ⟨l, hl, hlz⟩ := S.exists_L2_F4 hz hz1 hw2 hw1' hb hbV
        exact ⟨l, mem_sup_right hl, hlz⟩
    · obtain ⟨l₂, hl₂, hl₂z⟩ := S.exists_L2_F4 hz hz1 ha haV hb hbV
      obtain ⟨n, -, -, hnz, hna, -⟩ := S.exists_rot_F4 hzV haV' hw
        (fun h => haV (h ▸ one_mem _)) hw1 (fun h => haV (h ▸ hz)) (fun h => hw2 (h ▸ hzV₂))
        (fun h => hw2 (h ▸ ha)) (fun h => hw2 (h ▸ mul_mem hzV₂ ha))
      refine ⟨n * l₂, mul_mem (mem_sup_left (S.mem_g1_F4 hz hz1 hnz)) (mem_sup_right hl₂), ?_⟩
      calc n * l₂ * z * (n * l₂)⁻¹ = n * (l₂ * z * l₂⁻¹) * n⁻¹ := by group
        _ = w := by rw [hl₂z, hna]
  intro l hl
  have hw : l * z * l⁻¹ ∈ V := (mem_normalizer_iff.mp (S.LV_F4 hl) z).mp hzV
  have hw1 : l * z * l⁻¹ ≠ 1 := fun h => hz1 (by
    calc z = l⁻¹ * (l * z * l⁻¹) * l := by group
      _ = 1 := by rw [h]; group)
  obtain ⟨h, hh, hhz⟩ := key _ hw hw1
  have hfix : (h⁻¹ * l) * z * (h⁻¹ * l)⁻¹ = z := by
    calc (h⁻¹ * l) * z * (h⁻¹ * l)⁻¹ = h⁻¹ * (l * z * l⁻¹) * h := by group
      _ = h⁻¹ * (h * z * h⁻¹) * h := by rw [hhz]
      _ = z := by group
  have := mul_mem hh (mem_sup_left (S.mem_g1_F4 hz hz1 hfix) : h⁻¹ * l ∈ A6.g1 T V ⊔ L₁Of L V₂)
  rwa [mul_inv_cancel_left] at this

theorem T_Lp_F4 : T ≤ normalizer (L₁Of L (fsuV1 T V) : Set G) := by
  rw [← lOne_eq_L₁Of]
  exact le_normalizer_lOne S.TL_F4 S.T_V1_F4

theorem irred_F4 : IsIrredOnSection (L₁Of L (fsuV1 T V) ⊔ T) V (fsuV1 T V) := by
  rw [← lOne_eq_L₁Of]
  exact irred_lOne_F4 S.h1222 S.h1281_F4 S.hV1_F4

theorem clv_F4 : L ⊓ centralizer (V : Set G) ≤ A6.o2Z L := by
  rw [S.cent_eq_F4]
  unfold pCoreOf A6.o2Z
  refine Subgroup.map_mono fun g hg => ?_
  rw [Subgroup.mem_comap, QuotientGroup.mk'_apply,
    (QuotientGroup.eq_one_iff g).mpr (by exact hg)]
  exact Subgroup.one_mem _

theorem not_isHatA6_F4 : ¬ A6.IsHatA6 L := by
  rintro ⟨-, h3, ⟨e⟩⟩
  obtain ⟨e'⟩ := nonempty_equiv_SL32_of_lieModel S.hlin
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
  rw [Nat.card_congr e'.toEquiv, HSType.card_SL_three_two, h3, Nat.card_congr e.toEquiv,
    nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at h2
  norm_num [Nat.factorial] at h2

end Setting_F4

end CFSG.Quasithin.H13.L32NSet14
