module

public import CFSG.Quasithin.H13.L32NLem14331b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14328e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14332a

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14328

open L14331

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]

namespace Ctx_F4

variable {g z b l : G} (C : Ctx_F4 G T L V V₂ g z b l) (D : HatModelU (fsuU T V))
include C

theorem exists_x_F4 : ∃ x ∈ L, x ^ 3 = 1 ∧ x * z * x⁻¹ = z ∧ x * (g⁻¹ * z * g) * x⁻¹ = z * b := by
  have haV₂ := C.a_mem_F4
  have haV₁ := C.a_nmem_F4
  have haV := C.a_V_F4
  generalize g⁻¹ * z * g = a at haV₂ haV₁ haV ⊢
  have hzb : z * b ∈ V := V.mul_mem C.z_V_F4 C.b_mem
  have hzz := C.mul_self_V_F4 C.z_V_F4
  have hbz : b = z * (z * b) := by rw [← mul_assoc, hzz, one_mul]
  obtain ⟨x, hxL, hx3, hxz, hxa, -⟩ := C.S.exists_rot_F4 C.z_V_F4 haV hzb
    (fun h => haV₁ (h ▸ one_mem _))
    (fun h => C.b_nmem (by rw [hbz, h, mul_one]; exact C.z_V₂_F4)) (fun h => haV₁ (h ▸ C.z_mem))
    (fun h => C.b_nmem (by rw [hbz, h, hzz]; exact one_mem _))
    (fun h => C.b_nmem (by rw [hbz, ← h]; exact V₂.mul_mem C.z_V₂_F4 haV₂))
    (fun h => C.b_nmem (by
      rw [hbz, h, ← mul_assoc, hzz, one_mul]
      exact haV₂))
  exact ⟨x, hxL, hx3, hxz, hxa⟩

theorem eq_one_of_conj_F4 (h14325 : Lemma14325One_F4) (h1222 : Stmt12_2_2_F4) {e x : G}
    (he : e ∈ centerOf (i128 T L V (fsuV1 T V))) (hxN : x ∈ Subgroup.normalizer (V : Set G))
    (hxa : x * (g⁻¹ * z * g) * x⁻¹ = z * b) (hxe : x * e * x⁻¹ = e) : e = 1 := by
  rw [C.zI_za_F4] at he
  have h1 : e ∈ zv V (z * b) := by
    have hc := conjugate_zv (v := z * b) hxN
    have e1 : x⁻¹ * (z * b) * x = g⁻¹ * z * g := by
      rw [← hxa]
      group
    rw [e1] at hc
    have h2 : e ∈ CFSG.conjugate (zv V (z * b)) x := by
      rw [hc]
      exact he.2
    rw [mem_conj_iff, hxe] at h2
    exact h2
  have hmem : e ∈ centerOf (fsuU T V) ⊓ CFSG.conjugate (centerOf (fsuU T V)) g ⊓
      CFSG.conjugate (centerOf (fsuU T V)) l := by
    rw [C.conj_zU_F4 (C.P_le_F4 C.gP), C.conj_zU_F4 (C.L_le_F4 C.l_mem), C.l_inv_z_F4, C.zU_eq_F4]
    exact ⟨he, h1⟩
  rw [C.zU_inf_eq_bot_F4 h14325 h1222] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem comm_zU_F4 (h14325 : Lemma14325One_F4) (h1222 : Stmt12_2_2_F4) (h12813 : Lemma12_8_13_F4) {a w : G}
    (ha : a ∈ CFSG.conjugate (centerOf (fsuU T V)) g ⊓ CFSG.conjugate (centerOf (fsuU T V)) l)
    (hw : w ∈ centerOf (fsuU T V)) : a * w = w * a := by
  have hwV : w ∈ Subgroup.centralizer (V : Set G) := Subgroup.centralizer_le Ctx.V_le_U hw.2
  have hgN : w ∈ Subgroup.normalizer (CFSG.conjugate (centerOf (fsuU T V)) g : Set G) := by
    rw [C.conj_zU_F4 (C.P_le_F4 C.gP)]
    exact centralizer_le_normalizer_zv C.a_V_F4 hwV
  have hlN : w ∈ Subgroup.normalizer (CFSG.conjugate (centerOf (fsuU T V)) l : Set G) := by
    rw [C.conj_zU_F4 (C.L_le_F4 C.l_mem), C.l_inv_z_F4]
    exact centralizer_le_normalizer_zv (V.mul_mem C.z_V_F4 C.b_mem) hwV
  have haH : a ∈ l32nH T V := L14332.conj_zU_le_F4 h12813 C.setting C.gP C.gN ha.1
  have haZ := L14332.normalizer_le_normalizer_centerOf _ (L14332.l32nH_le_normalizer_fsuU T V haH)
  set c := a * w * a⁻¹ * w⁻¹ with hc
  have hcZ : c ∈ centerOf (fsuU T V) :=
    (centerOf (fsuU T V)).mul_mem ((Subgroup.mem_normalizer_iff.mp haZ w).mp hw)
      ((centerOf (fsuU T V)).inv_mem hw)
  have e1 : c = a * (w * a⁻¹ * w⁻¹) := by rw [hc]; group
  have hcg : c ∈ CFSG.conjugate (centerOf (fsuU T V)) g := by
    rw [e1]
    exact Subgroup.mul_mem _ ha.1 ((Subgroup.mem_normalizer_iff.mp hgN _).mp
      (Subgroup.inv_mem _ ha.1))
  have hcl : c ∈ CFSG.conjugate (centerOf (fsuU T V)) l := by
    rw [e1]
    exact Subgroup.mul_mem _ ha.2 ((Subgroup.mem_normalizer_iff.mp hlN _).mp
      (Subgroup.inv_mem _ ha.2))
  have hmem : c ∈ centerOf (fsuU T V) ⊓ CFSG.conjugate (centerOf (fsuU T V)) g ⊓
      CFSG.conjugate (centerOf (fsuU T V)) l := ⟨⟨hcZ, hcg⟩, hcl⟩
  rw [C.zU_inf_eq_bot_F4 h14325 h1222, Subgroup.mem_bot] at hmem
  calc a * w = a * w * a⁻¹ * w⁻¹ * (w * a) := by group
    _ = w * a := by rw [← hc, hmem, one_mul]

theorem not_three_dvd_inf_F4
    (hQ : centralizerMod (fsuV1 T V) (l32nH T V) (fsuU T V) = pCoreOf 2 (l32nH T V))
    {K : Subgroup G} (hKZ : K ≤ Subgroup.centralizer (centerOf (fsuU T V) : Set G)) :
    ¬ 3 ∣ Nat.card ↥(K ⊓ l32nCHat T V) := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3
  set c : G := (y : G) with hcy
  have hcK : c ∈ K := (Subgroup.mem_inf.mp y.2).1
  have hcE : c ∈ l32nCHat T V := (Subgroup.mem_inf.mp y.2).2
  have hc3 : orderOf c = 3 := by rw [hcy, Subgroup.orderOf_coe]; exact hy
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hU2 : IsPGroup 2 ↥(fsuU T V) := C.S.hH.sylow.1.to_le C.U_T

  have hcU : ∀ u ∈ fsuU T V, c * u * c⁻¹ = u := by
    intro u hu
    set d := c * u * c⁻¹ * u⁻¹ with hd
    have hdZ : d ∈ centerOf (fsuU T V) := hcE.2.2 u hu
    have hcd : c * d * c⁻¹ = d := by
      rw [← Subgroup.mem_centralizer_iff.mp (hKZ hcK) d hdZ, mul_inv_cancel_right]
    have hcu : c * u * c⁻¹ = d * u := by rw [hd]; group
    have h3 := L14332.pow_conj_eq hcd hcu 3
    rw [hc3', one_mul, inv_one, mul_one] at h3
    have hd3 : d ^ 3 = 1 := by
      have : u * u⁻¹ = d ^ 3 * u * u⁻¹ := by rw [← h3]
      simpa using this.symm
    obtain ⟨k, hk⟩ := hU2 ⟨d, hdZ.1⟩
    have hd2 : d ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hd1 : d = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3))
      (orderOf_dvd_of_pow_eq_one hd2) (orderOf_dvd_of_pow_eq_one hd3))
    rw [hcu, hd1, one_mul]

  have hcQ : c ∈ pCoreOf 2 (l32nH T V) := by
    rw [← hQ]
    refine ⟨hcE.1, hcE.1, fun u hu => ?_⟩
    rw [hcU u hu, mul_inv_cancel]
    exact one_mem _
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (l32nH T V) ⟨c, hcQ⟩
  have hc2 : c ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hc1 : c = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3))
    (orderOf_dvd_of_pow_eq_one hc2) (orderOf_dvd_of_pow_eq_one hc3'))
  rw [hc1, orderOf_one] at hc3
  exact absurd hc3 (by norm_num)

end Ctx_F4

end L14328

end CFSG.Quasithin.H13
