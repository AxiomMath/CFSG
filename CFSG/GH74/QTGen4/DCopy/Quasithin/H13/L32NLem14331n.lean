module

public import CFSG.Quasithin.H13.L32NLem14331n
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14331h

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

namespace L14328

open L14331

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]

namespace Ctx_F4
open CFSG.Quasithin.H13.L14328.Ctx_F4

variable {g z b l : G} (C : Ctx_F4 G T L V V₂ g z b l) (D : HatModelU (fsuU T V)) {e : G}
include C

theorem fix_z_F4 {x : G} (hx : x ∈ l32nH T V) : x * z * x⁻¹ = z := by
  have h1 := (Subgroup.mem_normalizer_iff.mp hx z).mp C.z_mem
  rcases C.S.eq_of_mem_V1_F4 C.z_mem C.z_ne h1 with h2 | h2
  · exfalso
    apply C.z_ne
    calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
      _ = 1 := by rw [h2]; group
  · exact h2

theorem caseI_norm_mem_F4 (Xc : CaseI_F4 T L V g D e)
    (hidx : 3 * Nat.card ↥(iKP T L V l e) ≤ 21 * Nat.card ↥(kT T V l e))
    {y : G} (hyK : y ∈ kA T V (l⁻¹ * e * l)) (hy3 : y ^ 3 = 1)
    (hya : y * (g⁻¹ * z * g) * y⁻¹ ≠ g⁻¹ * z * g) :
    ∀ v ∈ V₂, v * (y * v * y⁻¹) * (y * y * v * (y * y)⁻¹) ∈ fsuV1 T V := by
  set a := g⁻¹ * z * g with ha
  set I := iKP T L V l e with hI
  have hzz : z * z = 1 := C.mul_self_V_F4 C.z_V_F4
  have haa : a * a = 1 := C.mul_self_V_F4 C.a_V_F4
  have hza : z * a = a * z := C.mul_comm_V_F4 C.z_V_F4 C.a_V_F4
  have hyH := C.caseI_K_H_F4 D Xc hyK
  have hyz := C.fix_z_F4 hyH
  have ha1 : a ≠ 1 := by
    intro h
    apply C.a_nmem_F4
    show a ∈ fsuV1 T V
    rw [h]
    exact one_mem _
  have haz : a ≠ z := by
    intro h
    apply C.a_nmem_F4
    show a ∈ fsuV1 T V
    rw [h]
    exact C.z_mem
  have hy3' : y * y * y = 1 := by rw [← pow_three']; exact hy3
  set a₁ := y * a * y⁻¹ with ha₁
  set a₂ := y * y * a * (y * y)⁻¹ with ha₂
  have hc1 : y * a₁ * y⁻¹ = a₂ := by rw [ha₁, ha₂]; group
  have hcz : ∀ u : G, y * (z * u) * y⁻¹ = z * (y * u * y⁻¹) := fun u => by
    calc y * (z * u) * y⁻¹ = (y * z * y⁻¹) * (y * u * y⁻¹) := by group
      _ = z * (y * u * y⁻¹) := by rw [hyz]
  have hconj_sq : ∀ {x u : G}, u * u = 1 → (x * u * x⁻¹) * (x * u * x⁻¹) = 1 := fun {x u} h => by
    calc (x * u * x⁻¹) * (x * u * x⁻¹) = x * (u * u) * x⁻¹ := by group
      _ = 1 := by rw [h]; group
  have ha₁₁ : a₁ * a₁ = 1 := hconj_sq haa
  have ha₂₂ : a₂ * a₂ = 1 := hconj_sq haa
  have hza₁ : z * a₁ = a₁ * z := by
    calc z * a₁ = y * (z * a) * y⁻¹ := by rw [hcz]
      _ = y * (a * z) * y⁻¹ := by rw [hza]
      _ = a₁ * (y * z * y⁻¹) := by rw [ha₁]; group
      _ = a₁ * z := by rw [hyz]
  have hza₂ : z * a₂ = a₂ * z := by
    calc z * a₂ = y * (z * a₁) * y⁻¹ := by rw [hcz, hc1]
      _ = y * (a₁ * z) * y⁻¹ := by rw [hza₁]
      _ = a₂ * (y * z * y⁻¹) := by rw [← hc1]; group
      _ = a₂ * z := by rw [hyz]

  have F2 : a₁ ≠ z * a := by
    intro h
    have h2 : a₂ = a := by rw [← hc1, h, hcz, ← ha₁, h, ← mul_assoc, hzz, one_mul]
    apply hya
    calc y * a * y⁻¹ = y * a₂ * y⁻¹ := by rw [h2]
      _ = (y * y * y) * a * (y * y * y)⁻¹ := by rw [ha₂]; group
      _ = a := by rw [hy3']; group
  have ha₁1 : a₁ ≠ 1 := fun h => ha1 (by
    calc a = y⁻¹ * a₁ * y := by rw [ha₁]; group
      _ = 1 := by rw [h]; group)
  have ha₁z : a₁ ≠ z := fun h => haz (by
    calc a = y⁻¹ * a₁ * y := by rw [ha₁]; group
      _ = y⁻¹ * (y * z * y⁻¹) * y := by rw [h, hyz]
      _ = z := by group)

  have hgI : g ∈ I := (le_sup_right : p128 T L V ≤ I) C.gP
  have hyI : y ∈ I := (le_sup_left.trans le_sup_left : kA T V (l⁻¹ * e * l) ≤ I) hyK
  obtain ⟨k, hkP, hkz, hka, -⟩ := L128P.exists_rotation_mem_F4 Xc.h1222 C.setting.hyp C.setting.v1
    C.setting.v2 C.setting.le C.z_mem C.z_ne C.a_mem_F4 C.a_nmem_F4
  have hkz' : k * z * k⁻¹ = a := hkz
  have hka' : k * a * k⁻¹ = z * a := hka
  have hkI : k ∈ I := (le_sup_right : p128 T L V ≤ I) (oTwoUpper_le _ hkP)

  set O : Set G := {w | ∃ x ∈ I, x * z * x⁻¹ = w} with hO
  have hmemO : ∀ x ∈ I, x * z * x⁻¹ ∈ O := fun x hx => ⟨x, hx, rfl⟩
  have hOinv : ∀ x ∈ I, ∀ w ∈ O, x * w * x⁻¹ ∈ O := by
    rintro x hx _ ⟨x', hx', rfl⟩
    exact ⟨x * x', I.mul_mem hx hx', by group⟩

  have hzI : z ∈ I := (le_sup_right.trans le_sup_left : T ≤ I) (C.U_T (CFSG.Quasithin.H13.L14328.Ctx.V_le_U C.z_V_F4))
  have hOcard : O.ncard ≤ 7 := by
    have hOeq : O = Subtype.val '' _root_.conjugatesOf (⟨z, hzI⟩ : ↥I) := by
      ext w
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨⟨x, hx⟩ * ⟨z, hzI⟩ * (⟨x, hx⟩)⁻¹, isConj_iff.mpr ⟨⟨x, hx⟩, rfl⟩, rfl⟩
      · rintro ⟨w', hw', rfl⟩
        obtain ⟨c, rfl⟩ := isConj_iff.mp hw'
        exact ⟨c, c.2, rfl⟩
    rw [hOeq, Set.ncard_image_of_injective _ Subtype.val_injective,
      ← Subgroup.index_centralizer_eq_ncard]
    have hle : (kT T V l e).subgroupOf I ≤ Subgroup.centralizer {(⟨z, hzI⟩ : ↥I)} := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have h1 := C.fix_z_F4 ((sup_le (C.caseI_K_H_F4 D Xc) C.setting.v1.2.2)
        (Subgroup.mem_subgroupOf.mp hx))
      simp only [Subgroup.coe_mul]
      calc (x : G) * z = (x : G) * z * (x : G)⁻¹ * x := by group
        _ = z * x := by rw [h1]
    have hdvd := Subgroup.index_dvd_of_le hle
    have hidx' : ((kT T V l e).subgroupOf I).index ≤ 7 := by
      have h1 := ((kT T V l e).subgroupOf I).card_mul_index
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : kT T V l e ≤ I)).toEquiv]
        at h1
      have hpos : 0 < Nat.card ↥(kT T V l e) := Nat.card_pos
      rw [← h1] at hidx
      by_contra hcon
      push Not at hcon
      have : 3 * (Nat.card ↥(kT T V l e) * 8) ≤ 3 * (Nat.card ↥(kT T V l e) *
          ((kT T V l e).subgroupOf I).index) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hcon)
      nlinarith
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hdvd).trans hidx'

  set S : Set G := {z, a, z * a, a₁, z * a₁, a₂, z * a₂} with hS
  have hS7 : S.ncard = 7 := fano_ncard hy3 hyz hzz C.z_ne ha1 haz hya
  have hza_mem : z * a ∈ O := by
    refine ⟨k * k, I.mul_mem hkI hkI, ?_⟩
    calc k * k * z * (k * k)⁻¹ = k * (k * z * k⁻¹) * k⁻¹ := by group
      _ = z * a := by rw [hkz', hka']
  have ha_mem : a ∈ O := ⟨g⁻¹, I.inv_mem hgI, by rw [inv_inv]⟩
  have hSO : S ⊆ O := by
    intro w hw
    simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨1, I.one_mem, by group⟩
    · exact ha_mem
    · exact hza_mem
    · exact hOinv y hyI _ ha_mem
    · rw [← hcz]
      exact hOinv y hyI _ hza_mem
    · rw [← hc1]
      exact hOinv y hyI _ (hOinv y hyI _ ha_mem)
    · rw [← hc1, ← hcz]
      refine hOinv y hyI _ ?_
      rw [ha₁, ← hcz]
      exact hOinv y hyI _ hza_mem
  have hSeq : S = O := Set.eq_of_subset_of_ncard_le hSO (by rw [hS7]; exact hOcard)

  have ha₁S : a₁ ∈ S := by
    simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  have hka1 : k⁻¹ * a₁ * k ∈ S := by
    have := hOinv k⁻¹ (I.inv_mem hkI) a₁ (hSO ha₁S)
    rw [inv_inv] at this
    rwa [hSeq]
  have hzp : ∀ p ∈ S, p ≠ z → p ≠ a → p ≠ z * a → z * p ∈ S := by
    intro p hp hpz hpa hpza
    simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hpz
    · exact absurd rfl hpa
    · exact absurd rfl hpza
    · right; right; right; right; left; rfl
    · right; right; right; left; rw [← mul_assoc, hzz, one_mul]
    · right; right; right; right; right; right; rfl
    · right; right; right; right; right; left; rw [← mul_assoc, hzz, one_mul]
  have haa₁ : a * a₁ ∈ S := by
    set p := k⁻¹ * a₁ * k with hp
    have hkp : k * p * k⁻¹ = a₁ := by rw [hp]; group
    have hpz : p ≠ z := fun h => hya (by
      rw [← hkp, h, hkz'])
    have hpa : p ≠ a := fun h => F2 (by rw [← hkp, h, hka'])
    have hpza : p ≠ z * a := fun h => ha₁z (by
      rw [← hkp, h, show k * (z * a) * k⁻¹ = (k * z * k⁻¹) * (k * a * k⁻¹) by group, hkz', hka',
        ← mul_assoc, ← hza, mul_assoc, haa, mul_one])
    have h1 := hzp p hka1 hpz hpa hpza
    rw [hSeq] at h1 ⊢
    have h2 := hOinv k hkI _ h1
    rwa [show k * (z * p) * k⁻¹ = (k * z * k⁻¹) * (k * p * k⁻¹) by group, hkz', hkp] at h2

  have hNa : a * a₁ * a₂ ∈ fsuV1 T V := by
    simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at haa₁
    rcases haa₁ with h | h | h | h | h | h | h
    · exfalso
      apply F2
      calc a₁ = a * (a * a₁) := by rw [← mul_assoc, haa, one_mul]
        _ = z * a := by rw [h, hza]
    · exact absurd (by calc a₁ = a⁻¹ * (a * a₁) := by group
        _ = 1 := by rw [h, inv_mul_cancel]) ha₁1
    · exfalso
      apply ha₁z
      calc a₁ = a * (a * a₁) := by rw [← mul_assoc, haa, one_mul]
        _ = z := by rw [h, ← mul_assoc, ← hza, mul_assoc, haa, mul_one]
    · exact absurd (by calc a = a * a₁ * a₁⁻¹ := by group
        _ = 1 := by rw [h, mul_inv_cancel]) ha1
    · exact absurd (by calc a = a * a₁ * a₁⁻¹ := by group
        _ = z := by rw [h, mul_inv_cancel_right]) haz
    · rw [h, ha₂₂]
      exact one_mem _
    · rw [h, mul_assoc, ha₂₂, mul_one]
      exact C.z_mem

  intro v hv
  by_cases hv1 : v = 1
  · rw [hv1]
    simp only [mul_one, mul_inv_cancel]
    exact one_mem _
  rcases C.V2_cases_F4 hv hv1 with h | h | h <;> rw [h]
  · rw [hyz, show y * y * z * (y * y)⁻¹ = y * (y * z * y⁻¹) * y⁻¹ by group, hyz, hyz, hzz,
      one_mul]
    exact C.z_mem
  · exact hNa
  · rw [hcz, show y * y * (z * a) * (y * y)⁻¹ = y * (y * (z * a) * y⁻¹) * y⁻¹ by group, hcz,
      hcz, ← ha₁, hc1]
    have hmove : ∀ {x w : G}, z * x = x * z → x * (z * w) = z * (x * w) := fun h => by
      rw [← mul_assoc, ← h, mul_assoc]
    have hzaa : z * (a * a₁) = (a * a₁) * z := by
      rw [← mul_assoc, hza, mul_assoc, hza₁, ← mul_assoc]
    have e1 : z * a * (z * a₁) * (z * a₂) = (z * z * z) * (a * a₁ * a₂) := by
      calc z * a * (z * a₁) * (z * a₂) = z * (a * (z * a₁)) * (z * a₂) := by group
        _ = z * (z * (a * a₁)) * (z * a₂) := by rw [hmove hza]
        _ = z * z * ((a * a₁) * (z * a₂)) := by group
        _ = z * z * (z * (a * a₁ * a₂)) := by rw [hmove hzaa]
        _ = (z * z * z) * (a * a₁ * a₂) := by group
    rw [e1, hzz, one_mul]
    exact Subgroup.mul_mem _ C.z_mem hNa

theorem caseI_false_F4 (Xc : CaseI_F4 T L V g D e)
    (hidx : 3 * Nat.card ↥(iKP T L V l e) ≤ 21 * Nat.card ↥(kT T V l e)) : False := by
  obtain ⟨y, hyK, hy3, -, hconj, -, hya⟩ := C.caseI_exists_y_F4 D Xc
  have hyH := C.caseI_K_H_F4 D Xc hyK
  have hNorm := C.caseI_norm_mem_F4 D Xc hidx hyK hy3 hya
  have hTH : T ≤ l32nH T V := C.setting.v1.2.2
  have hUH : fsuU T V ≤ l32nH T V := C.U_T.trans hTH
  have hcen : ∀ h ∈ l32nH T V, ∀ c ∈ fsuV1 T V, h * c * h⁻¹ = c := by
    intro h hh c hc
    rcases C.S.eq_of_mem_V1_F4 C.z_mem C.z_ne hc with h1 | h1
    · rw [h1]
      group
    · rw [h1]
      exact C.fix_z_F4 hh
  have hU2 : IsPGroup 2 ↥(fsuU T V) := C.S.hH.sylow.1.to_le C.U_T
  have hΦ : frattiniOf (fsuU T V) ≤ fsuV1 T V :=
    (display12_8_frattini_F4 Xc.h1222 Xc.h12213 G T L V 3 (fsuV1 T V) V₂ C.setting).le
  obtain ⟨hsq, hcomm⟩ := L14332.sq_mem_and_comm_mem hU2 hΦ
  have hx : ∀ h ∈ l32nH T V, ∃ k ∈ l32nH T V,
      (∀ u ∈ fsuU T V, k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V) ∧
      (h⁻¹ * y * h = k * y ∨ h⁻¹ * y * h = k * y⁻¹) := by
    intro h hh
    obtain ⟨k, hk, hk'⟩ := hconj h hh
    exact ⟨k, hk.1, hk.2.2, hk'⟩
  obtain ⟨w, hwZ, hwV₁⟩ := IsConcreteLE.exists_of_lt C.lt
  have hwU : w ∈ fsuU T V := (Subgroup.mem_inf.mp hwZ).1
  have hwx : y * w * y⁻¹ * w⁻¹ ∈ fsuV1 T V := by
    have hc : w * y = y * w :=
      Subgroup.mem_centralizer_iff.mp (C.caseI_K_Z_F4 D Xc hyK) w hwZ
    rw [← hc, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  exact hwV₁ (L14332.mem_of_norm hUH (L14332.l32nH_le_normalizer_fsuU T V) hcen
    (fun u hu v hv => by simpa [commutatorElement_def] using hcomm u hu v hv)
    (lemma12_8_8_six_F4 Xc.h1222 C.setting).symm hyH hy3 hx hNorm hwU hwx (hsq w hwU))

end Ctx_F4

end L14328

end CFSG.Quasithin.H13
