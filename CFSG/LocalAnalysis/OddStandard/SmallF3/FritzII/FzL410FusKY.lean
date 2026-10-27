module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410FusKZ
public import CFSG.GroupTheory.InvolutionPair
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.CtxData

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

namespace Fz410Set

variable {G : Type} [Group G] [Finite G] {t : G} {L S T : Subgroup G}
  {x₁ x₂ lam rho tau s : G} {Z E W Q R P : Subgroup G}

theorem fz410x_fz410_fusk_normalizes_Z (D : Fz410Set t L S T x₁ x₂ lam rho tau s Z E W Q R P)
    {e k : G} (he : e ∈ E) (hk : k * t * k⁻¹ = e * (t * s))
    (hkS : ∀ x ∈ fz410CR R (e * (t * s)), k⁻¹ * x * k ∈ S) :
    ∀ z : G, k * z * k⁻¹ ∈ Z ↔ z ∈ Z := by
  let i : G := e * (t * s)
  have hkt : k * t * k⁻¹ = i := hk
  have hfus : Fz410Fus R Z i := D.facts.fus_ets e he
  let C : Subgroup G := fz410CR R i
  have hCcard : Nat.card C = 64 := hfus.card_C
  have hCR : C ≤ R := inf_le_left
  have hCkay : ∀ x ∈ C, k⁻¹ * x * k ∈ S := hkS
  let φ : G ≃* G := MulAut.conj k⁻¹
  let Ckay : Subgroup G := C.map φ.toMonoidHom
  let Zkay : Subgroup G := Z.map φ.toMonoidHom
  have hCkayS : Ckay ≤ S := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, hconj⟩ := hy
    rw [← hconj]
    have hconj' : (MulAut.conj k⁻¹).toMonoidHom x = k⁻¹ * x * k := by simp [MulAut.conj_apply]
    rw [hconj']
    exact hCkay x hx
  have hCkaycard : Nat.card Ckay = 64 := by
    rw [Subgroup.card_map_of_injective φ.injective, hCcard]
  obtain ⟨x, hxC, y, hyC, hx2ne, hy2ne, hxy2⟩ := hfus.sq_pair
  have hx2Z : x ^ 2 ∈ Z := D.facts.sqZ x (hCR hxC)
  have hy2Z : y ^ 2 ∈ Z := D.facts.sqZ y (hCR hyC)
  have hx2sq : (x ^ 2) ^ 2 = 1 := D.str.Z_sq (x ^ 2) hx2Z
  have hy2sq : (y ^ 2) ^ 2 = 1 := D.str.Z_sq (y ^ 2) hy2Z
  have hx2sq' : x ^ 2 * x ^ 2 = 1 := by rwa [pow_two] at hx2sq
  have hy2sq' : y ^ 2 * y ^ 2 = 1 := by rwa [pow_two] at hy2sq
  have hcommZ : x ^ 2 * y ^ 2 = y ^ 2 * x ^ 2 :=
    D.str.W_comm (x ^ 2) (D.str.EW (D.str.ZE hx2Z)) (y ^ 2) (D.str.EW (D.str.ZE hy2Z))
  let a : G := k⁻¹ * x ^ 2 * k
  let b : G := k⁻¹ * y ^ 2 * k
  have hx2C : x ^ 2 ∈ C := by rw [pow_two]; exact C.mul_mem hxC hxC
  have hy2C : y ^ 2 ∈ C := by rw [pow_two]; exact C.mul_mem hyC hyC
  have haZkay : a ∈ Zkay := by
    refine Subgroup.mem_map.mpr ⟨x ^ 2, hx2Z, ?_⟩
    change (MulAut.conj k⁻¹).toMonoidHom (x ^ 2) = k⁻¹ * x ^ 2 * k
    rw [fz410x_fz410_fusk_conj_apply]
  have hbZkay : b ∈ Zkay := by
    refine Subgroup.mem_map.mpr ⟨y ^ 2, hy2Z, ?_⟩
    change (MulAut.conj k⁻¹).toMonoidHom (y ^ 2) = k⁻¹ * y ^ 2 * k
    rw [fz410x_fz410_fusk_conj_apply]
  have haCkay : a ∈ Ckay := by
    refine Subgroup.mem_map.mpr ⟨x ^ 2, hx2C, ?_⟩
    change (MulAut.conj k⁻¹).toMonoidHom (x ^ 2) = k⁻¹ * x ^ 2 * k
    rw [fz410x_fz410_fusk_conj_apply]
  have hbCkay : b ∈ Ckay := by
    refine Subgroup.mem_map.mpr ⟨y ^ 2, hy2C, ?_⟩
    change (MulAut.conj k⁻¹).toMonoidHom (y ^ 2) = k⁻¹ * y ^ 2 * k
    rw [fz410x_fz410_fusk_conj_apply]
  have haS : a ∈ S := hCkayS haCkay
  have hbS : b ∈ S := hCkayS hbCkay
  have ha2 : a ^ 2 = 1 := by
    show (k⁻¹ * x ^ 2 * k) ^ 2 = 1
    rw [fz410x_fz410_fusk_conj_pow, hx2sq]
    group
  have hb2 : b ^ 2 = 1 := by
    show (k⁻¹ * y ^ 2 * k) ^ 2 = 1
    rw [fz410x_fz410_fusk_conj_pow, hy2sq]
    group
  have ha2' : a * a = 1 := by rw [← pow_two]; exact ha2
  have hb2' : b * b = 1 := by rw [← pow_two]; exact hb2
  have ha1 : a ≠ 1 := by
    intro h
    apply hx2ne
    have h' : k * a * k⁻¹ = k * 1 * k⁻¹ := by rw [h]
    have h'' : k * a * k⁻¹ = x ^ 2 := by simp only [a]; group
    rw [h'', mul_one, mul_inv_cancel] at h'
    exact h'
  have hb1 : b ≠ 1 := by
    intro h
    apply hy2ne
    have h' : k * b * k⁻¹ = k * 1 * k⁻¹ := by rw [h]
    have h'' : k * b * k⁻¹ = y ^ 2 := by simp only [b]; group
    rw [h'', mul_one, mul_inv_cancel] at h'
    exact h'
  have hab : a ≠ b := by
    intro h
    apply hxy2
    have h' : k * a * k⁻¹ = k * b * k⁻¹ := by rw [h]
    have ha' : k * a * k⁻¹ = x ^ 2 := by simp only [a]; group
    have hb' : k * b * k⁻¹ = y ^ 2 := by simp only [b]; group
    rw [ha', hb'] at h'
    exact h'
  have habcomm : a * b = b * a := by
    simp only [a, b]
    calc (k⁻¹ * x ^ 2 * k) * (k⁻¹ * y ^ 2 * k) = k⁻¹ * (x ^ 2 * y ^ 2) * k := by group
      _ = k⁻¹ * (y ^ 2 * x ^ 2) * k := by rw [hcommZ]
      _ = (k⁻¹ * y ^ 2 * k) * (k⁻¹ * x ^ 2 * k) := by group
  have hCkay_le_CS : Ckay ≤ fz410CS T t a b := by
    intro z hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨w, hw, hconj⟩ := hz
    rw [← hconj]
    have hconj' : (MulAut.conj k⁻¹).toMonoidHom w = k⁻¹ * w * k := by simp [MulAut.conj_apply]
    rw [hconj']
    have hwR : w ∈ R := hw.1
    have hwz : w * x ^ 2 = x ^ 2 * w := by
      have h := D.str.R_Z w hwR (x ^ 2) hx2Z
      calc w * x ^ 2 = (w * x ^ 2 * w⁻¹) * w := by group
        _ = x ^ 2 * w := by rw [h]
    have hwy : w * y ^ 2 = y ^ 2 * w := by
      have h := D.str.R_Z w hwR (y ^ 2) hy2Z
      calc w * y ^ 2 = (w * y ^ 2 * w⁻¹) * w := by group
        _ = y ^ 2 * w := by rw [h]
    have hST : k⁻¹ * w * k ∈ T ⊓ centralizer ({t} : Set G) :=
      (fz410x_fz410_fusk_S_eq_T_inf D) ▸ hCkay w hw
    refine ⟨⟨hST, ?_⟩, ?_⟩
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      rw [hu]
      calc (k⁻¹ * x ^ 2 * k) * (k⁻¹ * w * k) = k⁻¹ * (x ^ 2 * w) * k := by group
        _ = k⁻¹ * (w * x ^ 2) * k := by rw [← hwz]
        _ = (k⁻¹ * w * k) * (k⁻¹ * x ^ 2 * k) := by group
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      rw [hu]
      calc (k⁻¹ * y ^ 2 * k) * (k⁻¹ * w * k) = k⁻¹ * (y ^ 2 * w) * k := by group
        _ = k⁻¹ * (w * y ^ 2) * k := by rw [← hwy]
        _ = (k⁻¹ * w * k) * (k⁻¹ * y ^ 2 * k) := by group
  have hCS_le_S : fz410CS T t a b ≤ S := by
    intro z hz
    rw [fz410x_fz410_fusk_S_eq_T_inf D]
    exact ⟨hz.1.1.1, hz.1.1.2⟩
  have hS128 : Nat.card S = 128 := by rw [fz410x_fz410_fusk_S_eq_T_inf D, D.facts.card_S]
  have hnotS : fz410CS T t a b ≠ S := by
    intro hEq
    have ht2' : t * t = 1 := by rw [← pow_two]; exact D.str.t_sq
    have hz2' : (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 := D.ctx.wreath.sq_x₁x₂_mul_self
    have hzZ : (x₁ * x₂) ^ 2 ∈ Z := by
      rw [D.hZ]; exact Subgroup.subset_closure (by simp)
    have htz' : t * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * t :=
      D.str.W_comm t D.str.t_mem ((x₁ * x₂) ^ 2) (D.str.EW (D.str.ZE hzZ))
    have ht1 : t ≠ 1 := by
      intro h
      have := D.ctx.hyp.ord_t
      rw [h, orderOf_one] at this
      norm_num at this
    have hz1 : (x₁ * x₂) ^ 2 ≠ 1 := D.ctx.wreath.sq_x₁x₂_ne_one
    have ht_ne_z : t ≠ (x₁ * x₂) ^ 2 := by
      intro h
      apply D.str.t_notin_E
      rw [h]
      exact D.str.ZE hzZ
    have ha_cs : a ∈ fz410CS T t a b := by
      refine ⟨⟨(fz410x_fz410_fusk_S_eq_T_inf D) ▸ haS, ?_⟩, ?_⟩
      · refine Subgroup.mem_centralizer_iff.mpr ?_
        intro u hu
        rw [Set.mem_singleton_iff] at hu
        rw [hu]
      · refine Subgroup.mem_centralizer_iff.mpr ?_
        intro u hu
        rw [Set.mem_singleton_iff] at hu
        rw [hu]
        exact habcomm.symm
    have hb_cs : b ∈ fz410CS T t a b := by
      refine ⟨⟨(fz410x_fz410_fusk_S_eq_T_inf D) ▸ hbS, ?_⟩, ?_⟩
      · refine Subgroup.mem_centralizer_iff.mpr ?_
        intro u hu
        rw [Set.mem_singleton_iff] at hu
        rw [hu]
        exact habcomm
      · refine Subgroup.mem_centralizer_iff.mpr ?_
        intro u hu
        rw [Set.mem_singleton_iff] at hu
        rw [hu]
    have haS' : a ∈ S := hEq ▸ ha_cs
    have hbS' : b ∈ S := hEq ▸ hb_cs
    have hS_le_Ca : S ≤ Subgroup.centralizer ({a} : Set G) := by
      rw [← hEq]; exact inf_le_left.trans inf_le_right
    have hS_le_Cb : S ≤ Subgroup.centralizer ({b} : Set G) := by
      rw [← hEq]; exact inf_le_right
    have haCS : a ∈ Subgroup.centralizer (S : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact (Subgroup.mem_centralizer_iff.mp (hS_le_Ca hu) a (Set.mem_singleton a)).symm
    have hbCS : b ∈ Subgroup.centralizer (S : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact (Subgroup.mem_centralizer_iff.mp (hS_le_Cb hu) b (Set.mem_singleton b)).symm
    have ha_cl : a ∈ closure ({t, (x₁ * x₂) ^ 2} : Set G) :=
      D.ctx.center_omega a ⟨haS', haCS⟩ ha2
    have hb_cl : b ∈ closure ({t, (x₁ * x₂) ^ 2} : Set G) :=
      D.ctx.center_omega b ⟨hbS', hbCS⟩ hb2
    have hcard_ab : Nat.card (closure ({a, b} : Set G)) = 4 :=
      CFSG.GroupTheory.card_closure_pair_eq_four ha2' hb2' habcomm ha1 hb1 hab
    have hcard_tz : Nat.card (closure ({t, (x₁ * x₂) ^ 2} : Set G)) = 4 :=
      CFSG.GroupTheory.card_closure_pair_eq_four ht2' hz2' htz' ht1 hz1 ht_ne_z
    have hle_ab : closure ({a, b} : Set G) ≤ closure ({t, (x₁ * x₂) ^ 2} : Set G) := by
      rw [Subgroup.closure_le]
      intro u hu
      rcases hu with rfl | rfl
      · exact ha_cl
      · exact hb_cl
    have heq_ab : closure ({a, b} : Set G) = closure ({t, (x₁ * x₂) ^ 2} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hle_ab (by rw [hcard_tz, hcard_ab])
    have hcl_ab_le_Zkay : closure ({a, b} : Set G) ≤ Zkay :=
      (Subgroup.closure_le (K := Zkay)).mpr (by rintro u (rfl | rfl); exact haZkay; exact hbZkay)
    have ht_Zkay : t ∈ Zkay :=
      hcl_ab_le_Zkay (heq_ab.symm ▸ Subgroup.subset_closure (by simp))
    have hiZ : i ∈ Z := by
      rw [Subgroup.mem_map] at ht_Zkay
      obtain ⟨w, hwZ, hwz⟩ := ht_Zkay
      have hzt : k * t * k⁻¹ = w := by
        rw [← hwz]
        have hφ : φ.toMonoidHom w = k⁻¹ * w * k := by
          change (MulAut.conj k⁻¹).toMonoidHom w = k⁻¹ * w * k
          rw [fz410x_fz410_fusk_conj_apply]
        rw [hφ]
        group
      rw [← hkt, hzt]
      exact hwZ
    have htsP : t * s ∈ P := by
      have heP : e ∈ P := D.pf.EP he
      have hiP : i ∈ P := D.Z_le_P hiZ
      have hmem : e⁻¹ * i ∈ P := P.mul_mem (P.inv_mem heP) hiP
      rwa [show e⁻¹ * i = t * s by simp only [i]; group] at hmem
    exact D.ts_notin_P htsP
  have hCS_eq_Ckay : fz410CS T t a b = Ckay := by
    by_cases hcard : Nat.card (fz410CS T t a b) = 64
    · exact (Subgroup.eq_of_le_of_card_ge hCkay_le_CS (by rw [hcard, hCkaycard])).symm
    · exfalso
      have hCkayS_rel : Ckay.relIndex S = 2 := by
        have h := Subgroup.relIndex_mul_card (H := Ckay) (K := S)
        rw [inf_eq_left.mpr hCkayS, hCkaycard, hS128] at h
        omega
      have hcardCS_le : Nat.card (fz410CS T t a b) ≤ 128 := by
        rw [← hS128]; exact Subgroup.card_le_of_le hCS_le_S
      have hcardCS_ge : 64 ≤ Nat.card (fz410CS T t a b) := by
        rw [← hCkaycard]; exact Subgroup.card_le_of_le hCkay_le_CS
      have hrel_card := Subgroup.relIndex_mul_card (H := Ckay) (K := fz410CS T t a b)
      rw [inf_eq_left.mpr hCkay_le_CS, hCkaycard] at hrel_card
      have hrel_le : Ckay.relIndex (fz410CS T t a b) ≤ 2 := by omega
      have hrel_ge : 1 ≤ Ckay.relIndex (fz410CS T t a b) := by omega
      have hcases : Ckay.relIndex (fz410CS T t a b) = 1 ∨
          Ckay.relIndex (fz410CS T t a b) = 2 := by omega
      rcases hcases with h1 | h2
      · have hle : fz410CS T t a b ≤ Ckay := Subgroup.relIndex_eq_one.mp h1
        have hEq : fz410CS T t a b = Ckay := le_antisymm hle hCkay_le_CS
        exact hcard (by rw [hEq, hCkaycard])
      · have hrelS : (fz410CS T t a b).relIndex S = 1 := by
          have := Subgroup.relIndex_mul_relIndex (H := Ckay) (K := fz410CS T t a b) (L := S)
            hCkay_le_CS hCS_le_S
          rw [h2] at this
          omega
        exact hnotS (le_antisymm hCS_le_S (Subgroup.relIndex_eq_one.mp hrelS))
  have hexp : ∀ x ∈ fz410CS T t a b, x ^ 4 = 1 := by
    intro x hx
    rw [hCS_eq_Ckay, Subgroup.mem_map] at hx
    obtain ⟨w, hw, hconj⟩ := hx
    rw [← hconj]
    have hconj' : (MulAut.conj k⁻¹).toMonoidHom w = k⁻¹ * w * k := by simp [MulAut.conj_apply]
    rw [hconj']
    have hwR : w ∈ R := hw.1
    have hw2Z : w ^ 2 ∈ Z := D.facts.sqZ w hwR
    have hw4 : w ^ 4 = 1 := by
      have h := D.str.Z_sq (w ^ 2) hw2Z
      rwa [show (w ^ 2) ^ 2 = w ^ 4 by rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]] at h
    rw [fz410x_fz410_fusk_conj_pow, hw4]
    group
  have hZCS_eq : fz410ZCS T t a b = (fz410ZCR R i).map φ.toMonoidHom := by
    have hC_eq : fz410CR R i = C := rfl
    unfold fz410ZCS fz410ZCR
    rw [hCS_eq_Ckay, hC_eq]
    show C.map φ.toMonoidHom ⊓
        Subgroup.centralizer ((C.map φ.toMonoidHom : Subgroup G) : Set G) =
      (C ⊓ Subgroup.centralizer (C : Set G)).map φ.toMonoidHom
    rw [← fz410x_fz410_fusk_map_centralizer φ C,
      ← Subgroup.map_inf C (Subgroup.centralizer (C : Set G)) φ.toMonoidHom φ.injective]
  have hcardZCS : Nat.card (fz410ZCS T t a b) = 8 := by
    rw [hZCS_eq, Subgroup.card_map_of_injective φ.injective, hfus.card_ZC]
  have hCS_le_R : fz410CS T t a b ≤ R :=
    D.facts.slem a ((fz410x_fz410_fusk_S_eq_T_inf D) ▸ haS)
      b ((fz410x_fz410_fusk_S_eq_T_inf D) ▸ hbS) ha2 hb2 ha1 hb1 hab
      habcomm (by rw [hCS_eq_Ckay, hCkaycard]) hexp hcardZCS
  have ha_Z : a ∈ Z := by
    have hxk : k⁻¹ * x * k ∈ Ckay := by
      refine Subgroup.mem_map.mpr ⟨x, hxC, ?_⟩
      change (MulAut.conj k⁻¹).toMonoidHom x = k⁻¹ * x * k
      rw [fz410x_fz410_fusk_conj_apply]
    have hxkR : k⁻¹ * x * k ∈ R := hCS_le_R (hCS_eq_Ckay.symm ▸ hxk)
    have h := D.facts.sqZ (k⁻¹ * x * k) hxkR
    have hsq : (k⁻¹ * x * k) ^ 2 = a := by
      have h' := fz410x_fz410_fusk_conj_pow k x 2
      rw [h']
    rwa [hsq] at h
  have hb_Z : b ∈ Z := by
    have hyk : k⁻¹ * y * k ∈ Ckay := by
      refine Subgroup.mem_map.mpr ⟨y, hyC, ?_⟩
      change (MulAut.conj k⁻¹).toMonoidHom y = k⁻¹ * y * k
      rw [fz410x_fz410_fusk_conj_apply]
    have hykR : k⁻¹ * y * k ∈ R := hCS_le_R (hCS_eq_Ckay.symm ▸ hyk)
    have h := D.facts.sqZ (k⁻¹ * y * k) hykR
    have hsq : (k⁻¹ * y * k) ^ 2 = b := by
      have h' := fz410x_fz410_fusk_conj_pow k y 2
      rw [h']
    rwa [hsq] at h
  have hZ_eq : Z = closure ({x ^ 2, y ^ 2} : Set G) := by
    have hle : closure ({x ^ 2, y ^ 2} : Set G) ≤ Z :=
      (Subgroup.closure_le (K := Z)).mpr (by rintro u (rfl | rfl); exact hx2Z; exact hy2Z)
    have hcard_cl : Nat.card (closure ({x ^ 2, y ^ 2} : Set G)) = 4 :=
      CFSG.GroupTheory.card_closure_pair_eq_four hx2sq' hy2sq' hcommZ hx2ne hy2ne hxy2
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [D.str.card_Z, hcard_cl])).symm
  have hZkay_le_Z : Zkay ≤ Z := by
    rw [hZ_eq]
    intro z hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨w, hw, hconj⟩ := hz
    rw [← hconj]
    have hsub : (MulAut.conj k⁻¹).toMonoidHom '' ({x ^ 2, y ^ 2} : Set G) ⊆
        closure ({x ^ 2, y ^ 2} : Set G) := by
      rintro _ ⟨u, (rfl | rfl), rfl⟩
      · simpa [MulAut.conj_apply] using (hZ_eq ▸ ha_Z)
      · simpa [MulAut.conj_apply] using (hZ_eq ▸ hb_Z)
    have hmem : (MulAut.conj k⁻¹).toMonoidHom w ∈
        Subgroup.closure ((MulAut.conj k⁻¹).toMonoidHom '' ({x ^ 2, y ^ 2} : Set G)) := by
      rw [← MonoidHom.map_closure]
      exact Subgroup.mem_map_of_mem _ (hZ_eq ▸ hw)
    exact (Subgroup.closure_le (K := closure ({x ^ 2, y ^ 2} : Set G))).mpr hsub hmem
  exact fz410x_fz410_fusk_normalizes_of_le hZkay_le_Z

end Fz410Set

end CFSG.OddStandard.SmallF3.FritzII
