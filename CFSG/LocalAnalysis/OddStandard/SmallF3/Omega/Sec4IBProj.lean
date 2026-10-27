module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBSpin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] def sec4IOnes : Fin 7 → ZMod 2 := fun _ => 1

private lemma sec4I_sum_ones : (∑ i : Fin 7, sec4IOnes i) = 1 := by
  decide

private lemma sec4I_add_self_eq_zero (v : Fin 7 → ZMod 2) : v + v = 0 := by
  funext i
  exact (by decide : ∀ x : ZMod 2, x + x = 0) (v i)

theorem sec4I_isEvenVec_zero : IsEvenVec (0 : Fin 7 → ZMod 2) := by
  simp [IsEvenVec]

theorem sec4I_isEvenVec_add {v w : Fin 7 → ZMod 2} (hv : IsEvenVec v) (hw : IsEvenVec w) :
    IsEvenVec (v + w) := by
  rw [IsEvenVec] at hv hw ⊢
  simp only [Pi.add_apply, Finset.sum_add_distrib, hv, hw, add_zero]

theorem sec4I_isEvenVec_permVec (σ : Equiv.Perm (Fin 7)) {v : Fin 7 → ZMod 2}
    (hv : IsEvenVec v) : IsEvenVec (permVec σ v) := by
  unfold IsEvenVec at hv ⊢
  simp only [permVec, Function.comp_apply, Equiv.sum_comp σ.symm v]
  exact hv

theorem sec4I_not_isEvenVec_ones : ¬ IsEvenVec sec4IOnes := by
  intro h
  rw [IsEvenVec, sec4I_sum_ones] at h
  exact one_ne_zero h

theorem sec4I_not_isEvenVec_add_ones {v : Fin 7 → ZMod 2} (hv : IsEvenVec v) :
    ¬ IsEvenVec (v + sec4IOnes) := by
  intro h
  rw [IsEvenVec] at hv h
  simp only [Pi.add_apply, Finset.sum_add_distrib, sec4I_sum_ones, hv, zero_add] at h
  exact one_ne_zero h

theorem sec4I_isEvenVec_add_ones {v : Fin 7 → ZMod 2} (hv : ¬ IsEvenVec v) :
    IsEvenVec (v + sec4IOnes) := by
  rw [IsEvenVec] at hv ⊢
  simp only [Pi.add_apply, Finset.sum_add_distrib, sec4I_sum_ones]
  exact (by decide : ∀ x : ZMod 2, x ≠ 0 → x + 1 = 0) _ hv

private noncomputable def sec4I_evenVecEquiv :
    {v : Fin 7 → ZMod 2 // IsEvenVec v} ≃ (Fin 6 → ZMod 2) where
  toFun v := fun i : Fin 6 => v.1 i.castSucc
  invFun u := ⟨Fin.snoc u (∑ i : Fin 6, u i), by
    rw [IsEvenVec, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    exact (by decide : ∀ x : ZMod 2, x + x = 0) _⟩
  left_inv v := by
    apply Subtype.ext
    change Fin.snoc (fun i : Fin 6 => v.1 i.castSucc)
      (∑ i : Fin 6, v.1 i.castSucc) = v.1
    have hlast : (∑ i : Fin 6, v.1 i.castSucc) = v.1 (Fin.last 6) := by
      have hv := v.2
      rw [IsEvenVec, Fin.sum_univ_castSucc] at hv
      have hxx : v.1 (Fin.last 6) + v.1 (Fin.last 6) = 0 :=
        (by decide : ∀ x : ZMod 2, x + x = 0) _
      calc (∑ i : Fin 6, v.1 i.castSucc) = (∑ i : Fin 6, v.1 i.castSucc) + 0 :=
            (add_zero _).symm
        _ = (∑ i : Fin 6, v.1 i.castSucc) + (v.1 (Fin.last 6) + v.1 (Fin.last 6)) := by
              simp only [hxx, add_zero]
        _ = ((∑ i : Fin 6, v.1 i.castSucc) + v.1 (Fin.last 6)) + v.1 (Fin.last 6) := by
              abel
        _ = 0 + v.1 (Fin.last 6) := by rw [hv]
        _ = v.1 (Fin.last 6) := zero_add _
    rw [hlast]
    exact Fin.snoc_init_self v.1
  right_inv u := by
    funext i
    change Fin.snoc (α := fun _ : Fin 7 => ZMod 2) u (∑ i : Fin 6, u i)
      (Fin.castSucc i) = u i
    rw [Fin.snoc_castSucc]

theorem sec4I_card_isEvenVec : Nat.card {v : Fin 7 → ZMod 2 // IsEvenVec v} = 2 ^ 6 := by
  rw [Nat.card_congr sec4I_evenVecEquiv, Nat.card_eq_fintype_card]
  simp [Fintype.card_fun]

theorem sec4I_vecWeight_cases {v : Fin 7 → ZMod 2} (hv : IsEvenVec v) (h0 : v ≠ 0) :
    vecWeight v = 2 ∨ vecWeight v = 4 ∨ vecWeight v = 6 := by
  have hle : vecWeight v ≤ 7 := by
    unfold vecWeight
    calc (Finset.univ.filter fun i => v i ≠ 0).card
        ≤ (Finset.univ : Finset (Fin 7)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = 7 := by simp
  have heven : Even (vecWeight v) := (sec4I_isEvenVec_iff_even_vecWeight v).mp hv
  have hpos : 0 < vecWeight v := by
    unfold vecWeight
    have hex : ∃ i, v i ≠ 0 := by
      by_contra hcon
      rw [not_exists] at hcon
      exact h0 (funext fun i => not_not.mp (hcon i))
    obtain ⟨i, hi⟩ := hex
    exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨k, hk⟩ := heven
  have hkpos : 0 < k := by omega
  have hkup : k ≤ 3 := by omega
  interval_cases k
  · left; omega
  · right; left; omega
  · right; right; omega

private lemma sec4I_sum_single (i : Fin 7) :
    (∑ j : Fin 7, Pi.single i (1 : ZMod 2) j) = 1 := by
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem sec4I_perm_eq_one_of_fix (σ : Equiv.Perm (Fin 7))
    (h : ∀ v : Fin 7 → ZMod 2, IsEvenVec v → permVec σ v = v) : σ = 1 := by
  apply Equiv.ext
  intro i
  change σ i = i
  by_contra hne
  obtain ⟨k, hki, hkσ⟩ := Fin.exists_ne_and_ne_of_two_lt i (σ i) (by decide : 2 < 7)
  let w : Fin 7 → ZMod 2 := Pi.single i 1 + Pi.single k 1
  have hw : IsEvenVec w := by
    dsimp only [w]
    rw [IsEvenVec]
    simp only [Pi.add_apply, Finset.sum_add_distrib, sec4I_sum_single i, sec4I_sum_single k]
    exact (by decide : (1 : ZMod 2) + 1 = 0)
  have hfix := h w hw
  have hval : w (σ i) = 1 := by
    have h1 : w i = w (σ i) := by
      have hfix' := congrFun hfix (σ i)
      simpa only [permVec, Function.comp_apply, Equiv.symm_apply_apply] using hfix'
    have hwi : w i = 1 := by
      dsimp only [w]
      rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hki.symm, add_zero]
    rw [hwi] at h1
    exact h1.symm
  have hzero : w (σ i) = 0 := by
    dsimp only [w]
    rw [Pi.add_apply, Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hkσ.symm, add_zero]
  rw [hval] at hzero
  exact one_ne_zero hzero

theorem sec4IT_ones (fr : Sec4IFrame Q) : sec4IT fr sec4IOnes = piOrth Q := by
  apply sec4I_ogroup_ext fr
  intro i
  rw [sec4IT_apply_basis, coe_piOrth_apply]
  rw [show sec4IOnes i = 1 from rfl, show sec4ISgn (1 : ZMod 2) = -1 from by decide]
  simp

@[expose] noncomputable def sec4IPsi (fr : Sec4IFrame Q) (v : Fin 7 → ZMod 2) : ProjOrth Q :=
  toProj Q (sec4IT fr v)

theorem sec4IPsi_zero (fr : Sec4IFrame Q) : sec4IPsi fr 0 = 1 := by
  unfold sec4IPsi
  rw [sec4IT_zero, map_one]

theorem sec4IPsi_add (fr : Sec4IFrame Q) (v w : Fin 7 → ZMod 2) :
    sec4IPsi fr (v + w) = sec4IPsi fr v * sec4IPsi fr w := by
  unfold sec4IPsi
  rw [sec4IT_add, map_mul]

theorem sec4IPsi_mul_self (fr : Sec4IFrame Q) (v : Fin 7 → ZMod 2) :
    sec4IPsi fr v * sec4IPsi fr v = 1 := by
  unfold sec4IPsi
  rw [← map_mul, sec4IT_mul_self, map_one]

theorem sec4IPsi_comm (fr : Sec4IFrame Q) (v w : Fin 7 → ZMod 2) :
    sec4IPsi fr v * sec4IPsi fr w = sec4IPsi fr w * sec4IPsi fr v := by
  rw [← sec4IPsi_add fr v w, ← sec4IPsi_add fr w v, add_comm]

theorem sec4IPsi_add_ones (fr : Sec4IFrame Q) (v : Fin 7 → ZMod 2) :
    sec4IPsi fr (v + sec4IOnes) = sec4IPsi fr v := by
  unfold sec4IPsi
  rw [sec4IT_add, sec4IT_ones, map_mul, toProj_piOrth, mul_one]

theorem sec4IPsi_eq_iff (fr : Sec4IFrame Q) (v w : Fin 7 → ZMod 2) :
    sec4IPsi fr v = sec4IPsi fr w ↔ v = w ∨ v = w + sec4IOnes := by
  have hTV : (sec4IT fr v)⁻¹ = sec4IT fr v := by
    rw [inv_eq_iff_mul_eq_one]
    exact sec4IT_mul_self fr v
  have key : sec4IPsi fr v = sec4IPsi fr w ↔
      sec4IT fr (v + w) = 1 ∨ sec4IT fr (v + w) = piOrth Q := by
    unfold sec4IPsi
    change QuotientGroup.mk (sec4IT fr v) = QuotientGroup.mk (sec4IT fr w) ↔
      sec4IT fr (v + w) = 1 ∨ sec4IT fr (v + w) = piOrth Q
    rw [QuotientGroup.eq, mem_piGroup_iff, hTV, ← sec4IT_add]
  rw [key]
  constructor
  · rintro (h | h)
    · left
      have hT : sec4IT fr (v + w) = sec4IT fr 0 := by rw [sec4IT_zero, h]
      have hvw : v + w = 0 := (sec4IMono_injective fr hT).2
      calc v = v + 0 := (add_zero v).symm
        _ = v + (w + w) := by rw [sec4I_add_self_eq_zero w]
        _ = (v + w) + w := by abel
        _ = 0 + w := by rw [hvw]
        _ = w := zero_add w
    · right
      have hT : sec4IT fr (v + w) = sec4IT fr sec4IOnes := by rw [sec4IT_ones, h]
      have hvw : v + w = sec4IOnes := (sec4IMono_injective fr hT).2
      calc v = v + 0 := (add_zero v).symm
        _ = v + (w + w) := by rw [sec4I_add_self_eq_zero w]
        _ = (v + w) + w := by abel
        _ = sec4IOnes + w := by rw [hvw]
        _ = w + sec4IOnes := add_comm _ _
  · rintro (rfl | h)
    · left
      rw [sec4I_add_self_eq_zero, sec4IT_zero]
    · right
      have hvw : (w + sec4IOnes) + w = sec4IOnes := by
        calc (w + sec4IOnes) + w = sec4IOnes + (w + w) := by abel
          _ = sec4IOnes + 0 := by rw [sec4I_add_self_eq_zero w]
          _ = sec4IOnes := add_zero _
      rw [h, hvw, sec4IT_ones]

theorem sec4IPsi_injOn (fr : Sec4IFrame Q) {v w : Fin 7 → ZMod 2} (hv : IsEvenVec v)
    (hw : IsEvenVec w) (h : sec4IPsi fr v = sec4IPsi fr w) : v = w := by
  rcases (sec4IPsi_eq_iff fr v w).mp h with rfl | hvw
  · rfl
  · rw [hvw] at hv
    exact absurd hv (sec4I_not_isEvenVec_add_ones hw)

theorem sec4IPsi_ne_one (fr : Sec4IFrame Q) {v : Fin 7 → ZMod 2} (hv : IsEvenVec v)
    (h0 : v ≠ 0) : sec4IPsi fr v ≠ 1 := by
  intro h
  have h1 : sec4IPsi fr v = sec4IPsi fr 0 := by rw [sec4IPsi_zero, h]
  rcases (sec4IPsi_eq_iff fr v 0).mp h1 with h2 | h2
  · exact h0 h2
  · rw [h2, zero_add] at hv
    exact sec4I_not_isEvenVec_ones hv

@[expose] noncomputable def sec4IB0 (fr : Sec4IFrame Q) : Subgroup (ProjOrth Q) where
  carrier := {x | ∃ v, IsEvenVec v ∧ sec4IPsi fr v = x}
  mul_mem' := by
    rintro x y ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨v + w, sec4I_isEvenVec_add hv hw, sec4IPsi_add fr v w⟩
  one_mem' := ⟨0, sec4I_isEvenVec_zero, sec4IPsi_zero fr⟩
  inv_mem' := by
    rintro x ⟨v, hv, rfl⟩
    refine ⟨v, hv, ?_⟩
    exact (inv_eq_of_mul_eq_one_right (sec4IPsi_mul_self fr v)).symm

theorem mem_sec4IB0_iff (fr : Sec4IFrame Q) {x : ProjOrth Q} :
    x ∈ sec4IB0 fr ↔ ∃ v, IsEvenVec v ∧ sec4IPsi fr v = x :=
  Iff.rfl

theorem sec4IPsi_mem_sec4IB0 (fr : Sec4IFrame Q) {v : Fin 7 → ZMod 2} (hv : IsEvenVec v) :
    sec4IPsi fr v ∈ sec4IB0 fr :=
  ⟨v, hv, rfl⟩

theorem sec4IB0_card (fr : Sec4IFrame Q) : Nat.card (sec4IB0 fr) = 2 ^ 6 := by
  let f : {v : Fin 7 → ZMod 2 // IsEvenVec v} → sec4IB0 fr :=
    fun v => ⟨sec4IPsi fr v.1, sec4IPsi_mem_sec4IB0 fr v.2⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact sec4IPsi_injOn fr a.2 b.2 (congrArg Subtype.val hab)
  have hf_surj : Function.Surjective f := by
    intro x
    obtain ⟨v, hv, hx⟩ := (mem_sec4IB0_iff fr).mp x.2
    refine ⟨⟨v, hv⟩, ?_⟩
    apply Subtype.ext
    exact hx
  calc Nat.card (sec4IB0 fr) = Nat.card {v : Fin 7 → ZMod 2 // IsEvenVec v} :=
        (Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)).symm
    _ = 2 ^ 6 := sec4I_card_isEvenVec

theorem sec4IB0_isElemAbelian (fr : Sec4IFrame Q) :
    CFSG.Open.IsElemAbelian 2 (sec4IB0 fr) := by
  constructor
  · refine IsMulCommutative.of_comm fun a b => ?_
    obtain ⟨v, hv, ha⟩ := (mem_sec4IB0_iff fr).mp a.2
    obtain ⟨w, hw, hb⟩ := (mem_sec4IB0_iff fr).mp b.2
    apply Subtype.ext
    change (a : ProjOrth Q) * b = b * a
    rw [← ha, ← hb]
    exact sec4IPsi_comm fr v w
  · intro x hx
    obtain ⟨v, hv, ha⟩ := (mem_sec4IB0_iff fr).mp hx
    rw [← ha, pow_two]
    exact sec4IPsi_mul_self fr v

theorem sec4IB0_le_omegaProj (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q) :
    sec4IB0 fr ≤ omegaProj hQ := by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := (mem_sec4IB0_iff fr).mp hx
  rw [mem_omegaProj_iff]
  exact ⟨sec4IT fr v,
    (sec4IMono_mem_omegaGroup_iff hQ fr 1 v).mpr ⟨Equiv.Perm.sign_one, hv⟩, rfl⟩

end CFSG.OddStandard.SmallF3.Omega
