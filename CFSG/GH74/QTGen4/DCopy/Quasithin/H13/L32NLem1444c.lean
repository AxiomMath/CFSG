module

public import CFSG.Quasithin.H13.L32NLem1444c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1444a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1444b

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits

open L1444 in

theorem lemma1444Seven_of_inputs_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hRest : Lemma14323Rest_F4) : Lemma1444Seven_F4 := by
  intro G _ _ T L V h hext h32 hG2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h13322 := stmt13_3_2_two_of_stmt13_3_2_F4 h1332
  have hV := stmtL32NModule_of_inputs_F4 h1332 h1334
  have hTS := h.isSylowTwoOf_l32nH_F4 hV
  have hHKT : l32nH T V = oTwoUpper (l32nH T V) ⊔ T :=
    (C1Pack12.oTwoUpper_sup_eq_of_sylow hTS).symm
  obtain ⟨V₂, hV₂⟩ := h.exists_plane_F4 hV
  obtain ⟨_, S⟩ := L14332.exists_setting_F4 h1332 h1334 h1222 h hV₂
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := S.TL_F4
  refine ⟨hHKT, le_antisymm ?_ (sup_le Subgroup.le_normalizer hTL)⟩
  have hQT : pCoreOf 2 (l32nH T V) ≤ T := pCoreOf_two_le_of_isSylowTwoOf hTS
  have hKH : oTwoUpper (l32nH T V) ≤ l32nH T V := oTwoUpper_le _

  have hVO := lemma1444Four_of_inputs_F4 h1332 h1334 h1222 h12213 G T L V h hext h32 hG2
  have hMV : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) := by
    rw [hVO]
    exact normalizer_le_normalizer_pCoreOf 2 L

  obtain ⟨z, a, b, hz, hz1, haV₂, haV₁, hb, hbV₂⟩ := S.exists_basis_F4
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz).1
  have hzV₂ : z ∈ V₂ := S.hV2.1 hz
  have ha : a ∈ V := S.hV2.2.1 haV₂
  obtain ⟨y, hyL, hy3, hyz, hya, -⟩ := S.exists_rot_F4 hzV ha hb
    (fun h => haV₁ (h ▸ one_mem _)) (fun h => hbV₂ (h ▸ one_mem _))
    (fun h => haV₁ (h ▸ hz)) (fun h => hbV₂ (h ▸ hzV₂)) (fun h => hbV₂ (h ▸ haV₂))
    (fun h => hbV₂ (h ▸ mul_mem hzV₂ haV₂))
  have hy1 : y ≠ 1 := by
    rintro rfl
    apply hbV₂
    rw [← hya]
    simpa using haV₂
  have hyH : y ∈ l32nH T V := S.mem_g1_F4 hz hz1 hyz
  have hyK : y ∈ oTwoUpper (l32nH T V) :=
    mem_oTwoUpper_of_odd hyH (Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hy3))

  have h1283 := lemma12_8_3_F4 h12213 G T L V 3 (h.hyp1281One_F4 h13322 hV)
  have hHM : ¬ l32nH T V ≤ Subgroup.normalizer (L : Set G) :=
    h1283.2.2.2 _ (h.isTSub_fsuV1_F4 hV)
  have htrans : ∀ w ∈ V, w ≠ 1 → ∃ l ∈ L, l * z * l⁻¹ = w := by
    intro w hw hw1
    have hw2 : orderOf w = 2 := orderOf_eq_prime (S.sq_V_F4 hw) hw1
    obtain ⟨l, hl, hlc⟩ := h1283.2.1 1 (fsuV1 T V) (Subgroup.zpowers w) inf_le_left
      (Subgroup.zpowers_le.mpr hw) (by rw [S.card_V1_F4]; norm_num)
      (by rw [Nat.card_zpowers, hw2]; norm_num)
    have hwc : w ∈ CFSG.conjugate (fsuV1 T V) l := hlc ▸ Subgroup.mem_zpowers w
    obtain ⟨x, hx, hxw⟩ := Subgroup.mem_map.mp hwc
    rcases S.eq_of_mem_V1_F4 hz hz1 hx with hx1 | hxz
    · rw [hx1, map_one] at hxw
      exact absurd hxw.symm hw1
    · refine ⟨l⁻¹, inv_mem hl, ?_⟩
      rw [hxz] at hxw
      simpa using hxw

  obtain ⟨-, hK9⟩ :=
    lemma1444One_of_inputs_F4 h1332 h1334 h1222 h12213 h37 h38 h39 hRest G T L V h hext h32 hG2
  set A := imageOTwoQuot (l32nH T V) (oTwoUpper (l32nH T V) ⊓ Subgroup.normalizer (L : Set G))
    with hA
  have hAK : A ≤ imageOTwoQuot (l32nH T V) (oTwoUpper (l32nH T V)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx).1, rfl⟩
  have hAne : A ≠ imageOTwoQuot (l32nH T V) (oTwoUpper (l32nH T V)) := by
    intro hAeq
    apply hHM
    rw [hHKT]
    refine sup_le (fun k hk => ?_) hTL
    have hk' : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(l32nH T V)) ⟨k, hKH hk⟩ :
        OTwoQuot (l32nH T V)) ∈ A := by
      rw [hAeq]
      exact ⟨⟨k, hKH hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    obtain ⟨⟨x, hxH⟩, hx, hxk⟩ := hk'
    have hxM : x ∈ Subgroup.normalizer (L : Set G) := (Subgroup.mem_subgroupOf.mp hx).2
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxk
    have hq : x⁻¹ * k ∈ T := hQT ⟨_, hxk, rfl⟩
    have e : k = x * (x⁻¹ * k) := by group
    rw [e]
    exact mul_mem hxM (hTL hq)
  have hyA : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(l32nH T V)) ⟨y, hyH⟩ :
      OTwoQuot (l32nH T V)) ∈ A :=
    ⟨⟨y, hyH⟩, Subgroup.mem_subgroupOf.mpr ⟨hyK, Subgroup.le_normalizer hyL⟩, rfl⟩
  have hy1' : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(l32nH T V)) ⟨y, hyH⟩ :
      OTwoQuot (l32nH T V)) ≠ 1 := by
    intro h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact hy1 (eq_one_of_mem_pCoreOf ⟨_, h1, rfl⟩ hy3)
  have hy3' : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(l32nH T V)) ⟨y, hyH⟩ :
      OTwoQuot (l32nH T V)) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨y, hyH⟩ : ↥(l32nH T V)) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [this, map_one]
  have hAy := eq_zpowers_of_card_nine hAK hK9 hAne hyA hy1' hy3'

  intro m hm
  have hw : m * z * m⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hMV hm) z).mp hzV
  have hw1 : m * z * m⁻¹ ≠ 1 := fun h => hz1 (by
    calc z = m⁻¹ * (m * z * m⁻¹) * m := by group
      _ = 1 := by rw [h]; group)
  obtain ⟨l, hl, hlz⟩ := htrans _ hw hw1
  have hlm : l⁻¹ * m ∈ l32nH T V := S.mem_g1_F4 hz hz1 (by
    calc l⁻¹ * m * z * (l⁻¹ * m)⁻¹ = l⁻¹ * (m * z * m⁻¹) * l := by group
      _ = z := by rw [← hlz]; group)
  have hlmM : l⁻¹ * m ∈ Subgroup.normalizer (L : Set G) :=
    mul_mem (Subgroup.le_normalizer (inv_mem hl)) hm
  have hTK : T ≤ Subgroup.normalizer (oTwoUpper (l32nH T V) : Set G) :=
    hTS.1.trans (le_normalizer_oTwoUpper _)
  have hmem : l⁻¹ * m ∈ ((oTwoUpper (l32nH T V) ⊔ T : Subgroup G) : Set G) := by
    rw [SetLike.mem_coe, ← hHKT]
    exact hlm
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTK] at hmem
  obtain ⟨k, hk, t, ht, hkt⟩ := hmem
  have hkt' : k * t = l⁻¹ * m := hkt
  have hkM : k ∈ Subgroup.normalizer (L : Set G) := by
    have e : k = (l⁻¹ * m) * t⁻¹ := by rw [← hkt']; group
    rw [e]
    exact mul_mem hlmM (inv_mem (hTL ht))
  have hkA : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(l32nH T V)) ⟨k, hKH hk⟩ :
      OTwoQuot (l32nH T V)) ∈ A :=
    ⟨⟨k, hKH hk⟩, Subgroup.mem_subgroupOf.mpr ⟨hk, hkM⟩, rfl⟩
  rw [hAy, Subgroup.mem_zpowers_iff] at hkA
  obtain ⟨n, hn⟩ := hkA
  rw [← map_zpow, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hn
  have hq : (y ^ n)⁻¹ * k ∈ T := hQT ⟨_, hn, by simp⟩
  have hm' : m = l * y ^ n * (((y ^ n)⁻¹ * k) * t) := by
    calc m = l * (l⁻¹ * m) := by group
      _ = l * (k * t) := by rw [hkt']
      _ = l * y ^ n * (((y ^ n)⁻¹ * k) * t) := by group
  rw [hm']
  exact mul_mem (Subgroup.mem_sup_left (mul_mem hl (zpow_mem hyL n)))
    (Subgroup.mem_sup_right (mul_mem hq ht))

end CFSG.Quasithin.H13
