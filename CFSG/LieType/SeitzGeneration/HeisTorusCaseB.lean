module

public import CFSG.LieType.SeitzGeneration.HeisTorusIsolate
public import CFSG.LieType.SeitzGeneration.HeisTorusIdent

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix

variable {F : Type*} [Field F] {p : ℕ}

theorem caseB_shift_mul_apply (M : Matrix (Fin p) (Fin p) F) (a b : Fin p) :
    (heisShiftMat F p * M) a b = M (finRotate p a) b := by
  simp [Matrix.mul_apply, heisShiftMat_entry]

theorem caseB_mul_shift_apply (M : Matrix (Fin p) (Fin p) F) (a b : Fin p) :
    (M * heisShiftMat F p) a (finRotate p b) = M a b := by
  simp [Matrix.mul_apply, heisShiftMat_entry]

theorem caseB_sparse_apply (a c : Fin p) :
    (1 + heisShiftMat F p + heisShiftMat F p ^ 2 : Matrix (Fin p) (Fin p) F) a c =
      (if a = c then 1 else 0) + (if finRotate p a = c then 1 else 0) +
        (if finRotate p (finRotate p a) = c then 1 else 0) := by
  rw [sq, Matrix.add_apply, Matrix.add_apply, Matrix.one_apply, caseB_shift_mul_apply,
    heisShiftMat_entry, heisShiftMat_entry]

theorem caseB_rot_succ [NeZero p] {a b : Fin p} (hb : (b : ℕ) = (a : ℕ) + 1) :
    finRotate p a = b := by
  apply Fin.ext
  rw [finRotate_val_mod, hb]
  exact Nat.mod_eq_of_lt (hb ▸ b.isLt)

theorem caseB_rot_last [NeZero p] {a : Fin p} (ha : (a : ℕ) + 1 = p) : finRotate p a = 0 := by
  apply Fin.ext
  rw [finRotate_val_mod, ha, Nat.mod_self, Fin.val_zero]

theorem caseB_indices [NeZero p] (hp : 7 ≤ p) :
    ∃ z₁ z₂ m₁ m₂ m₃ : Fin p, finRotate p 0 = z₁ ∧ finRotate p z₁ = z₂ ∧ finRotate p m₃ = m₂ ∧
      finRotate p m₂ = m₁ ∧ finRotate p m₁ = 0 ∧ z₁ ≠ 0 ∧ z₂ ≠ 0 ∧ m₁ ≠ 0 ∧
      z₂ ∉ ({m₂, m₁, 0, z₁} : Finset (Fin p)) ∧ m₃ ∉ ({m₂, m₁, 0, z₁} : Finset (Fin p)) ∧
      z₂ ≠ m₃ := by
  refine ⟨⟨1, by omega⟩, ⟨2, by omega⟩, ⟨p - 1, by omega⟩, ⟨p - 2, by omega⟩, ⟨p - 3, by omega⟩,
    caseB_rot_succ (by simp), caseB_rot_succ rfl, caseB_rot_succ (by simp; omega),
    caseB_rot_succ (by simp; omega), caseB_rot_last (by simp; omega), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Fin.ext_iff] <;> omega

theorem caseB_sparse_zero_of_not_mem [NeZero p] {z₁ m₁ m₂ : Fin p} (hz₁ : finRotate p 0 = z₁)
    (hm₂ : finRotate p m₂ = m₁) (hm₁ : finRotate p m₁ = 0) {a : Fin p}
    (ha : a ∉ ({m₂, m₁, 0, z₁} : Finset (Fin p))) :
    (1 + heisShiftMat F p + heisShiftMat F p ^ 2 : Matrix (Fin p) (Fin p) F) a 0 = 0 ∧
      (1 + heisShiftMat F p + heisShiftMat F p ^ 2 : Matrix (Fin p) (Fin p) F) a z₁ = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
  obtain ⟨ha2, ha1, ha0, haz⟩ := ha
  have hρ : Function.Injective (finRotate p) := (finRotate p).injective
  have e1 : finRotate p a ≠ 0 := fun h => ha1 (hρ (h.trans hm₁.symm))
  have e2 : finRotate p (finRotate p a) ≠ 0 :=
    fun h => ha2 (hρ ((hρ (h.trans hm₁.symm)).trans hm₂.symm))
  have e3 : finRotate p a ≠ z₁ := fun h => ha0 (hρ (h.trans hz₁.symm))
  have e4 : finRotate p (finRotate p a) ≠ z₁ :=
    fun h => ha1 (hρ ((hρ (h.trans hz₁.symm)).trans hm₁.symm))
  refine ⟨?_, ?_⟩
  · rw [caseB_sparse_apply, if_neg ha0, if_neg e1, if_neg e2]
    simp
  · rw [caseB_sparse_apply, if_neg haz, if_neg e3, if_neg e4]
    simp

theorem caseB_torus_mem {K : Subgroup (SpecialLinearGroup (Fin p) F)} (hK : ContainsDiagTorus K)
    {l : F} (hl : l ≠ 0) {x m : Fin p} (hxm : x ≠ m) :
    ∃ g ∈ K, (g : Matrix (Fin p) (Fin p) F) =
      diagonal (fun i => (if i = x then l else 1) * (if i = m then l⁻¹ else 1)) := by
  have hdet : (diagonal fun i : Fin p =>
      (if i = x then l else 1) * (if i = m then l⁻¹ else 1)).det = 1 := by
    rw [Matrix.det_diagonal, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
    simp [hl]
  exact ⟨⟨_, hdet⟩, hK _ ⟨_, rfl⟩, rfl⟩

theorem caseB_inv_comm {δ E : Matrix (Fin p) (Fin p) F}
    (hδ : δ = 1 + heisShiftMat F p + heisShiftMat F p ^ 2) (hδE : δ * E = 1) (hEδ : E * δ = 1) :
    E * heisShiftMat F p = heisShiftMat F p * E := by
  have hc : δ * heisShiftMat F p = heisShiftMat F p * δ := by
    rw [hδ]
    noncomm_ring
  calc E * heisShiftMat F p = E * heisShiftMat F p * (δ * E) := by rw [hδE, mul_one]
    _ = E * (heisShiftMat F p * δ) * E := by noncomm_ring
    _ = E * (δ * heisShiftMat F p) * E := by rw [hc]
    _ = (E * δ) * heisShiftMat F p * E := by noncomm_ring
    _ = heisShiftMat F p * E := by rw [hEδ, one_mul]

theorem caseB_inv_periodic {E : Matrix (Fin p) (Fin p) F}
    (hcomm : E * heisShiftMat F p = heisShiftMat F p * E) (a b : Fin p) :
    E (finRotate p a) (finRotate p b) = E a b := by
  have h := congrFun (congrFun hcomm a) (finRotate p b)
  rw [caseB_mul_shift_apply, caseB_shift_mul_apply] at h
  exact h.symm

theorem caseB_inv_rec {E : Matrix (Fin p) (Fin p) F}
    (h : (1 + heisShiftMat F p + heisShiftMat F p ^ 2) * E = 1) (a b : Fin p) :
    E a b + E (finRotate p a) b + E (finRotate p (finRotate p a)) b =
      if a = b then 1 else 0 := by
  have h' := congrFun (congrFun h a) b
  rw [add_mul, add_mul, one_mul, sq, mul_assoc, Matrix.add_apply, Matrix.add_apply,
    caseB_shift_mul_apply, caseB_shift_mul_apply, caseB_shift_mul_apply, Matrix.one_apply] at h'
  exact h'

theorem caseB_inv_not_vanish [NeZero p] {E : Matrix (Fin p) (Fin p) F}
    (hper : ∀ a b, E (finRotate p a) (finRotate p b) = E a b)
    (hrec : ∀ a b, E a b + E (finRotate p a) b + E (finRotate p (finRotate p a)) b =
      if a = b then 1 else 0)
    {z₁ z₂ m₁ m₂ m₃ : Fin p} (hz₁ : finRotate p 0 = z₁) (hz₂ : finRotate p z₁ = z₂)
    (hm₃ : finRotate p m₃ = m₂) (hm₂ : finRotate p m₂ = m₁) (hm₁ : finRotate p m₁ = 0)
    (hz₂0 : z₂ ≠ 0) (hm₁0 : m₁ ≠ 0)
    (h1 : E 0 z₂ = 0) (h2 : E z₁ z₂ = 0) (h3 : E 0 m₃ = 0) : False := by
  have e11 : E z₁ z₁ = E 0 0 := by
    have := hper 0 0
    rwa [hz₁] at this
  have e22 : E z₂ z₂ = E z₁ z₁ := by
    have := hper z₁ z₁
    rwa [hz₂] at this
  have e10 : E z₁ 0 = E 0 m₁ := by
    have := hper 0 m₁
    rwa [hz₁, hm₁] at this
  have e20 : E z₂ 0 = E z₁ m₁ := by
    have := hper z₁ m₁
    rwa [hz₂, hm₁] at this
  have e2m : E z₂ m₁ = E z₁ m₂ := by
    have := hper z₁ m₂
    rwa [hz₂, hm₂] at this
  have e1m' : E z₁ m₂ = E 0 m₃ := by
    have := hper 0 m₃
    rwa [hz₁, hm₃] at this
  have r0 := hrec 0 0
  have r2 := hrec 0 z₂
  have r3 := hrec 0 m₁
  rw [hz₁, hz₂, if_pos rfl] at r0
  rw [hz₁, hz₂, if_neg (Ne.symm hz₂0)] at r2
  rw [hz₁, hz₂, if_neg (Ne.symm hm₁0)] at r3
  have : (1 : F) = 0 := by
    linear_combination (-1 : F) * r0 + r3 + r2 + e10 + e20 - e22 - e11 - e2m - e1m' - h3 - h1 - h2
  exact one_ne_zero this

theorem caseB_range [NeZero p] {δ E s : Matrix (Fin p) (Fin p) F}
    (hδ : δ = 1 + heisShiftMat F p + heisShiftMat F p ^ 2) (hδE : δ * E = 1)
    {t : Fin p → F} (hs : s = diagonal t) {z₁ m₁ m₂ : Fin p} (hz₁ : finRotate p 0 = z₁)
    (hm₂ : finRotate p m₂ = m₁) (hm₁ : finRotate p m₁ = 0)
    (ht : ∀ c, c ≠ 0 → c ≠ z₁ → t c = 1) {a : Fin p}
    (ha : a ∉ ({m₂, m₁, 0, z₁} : Finset (Fin p))) (b : Fin p) :
    (δ * s * E - 1) a b = 0 := by
  obtain ⟨h0, h1⟩ := caseB_sparse_zero_of_not_mem (F := F) hz₁ hm₂ hm₁ ha
  rw [← hδ] at h0 h1
  have hrw : δ * s * E - 1 = (δ * s - δ) * E := by rw [sub_mul, hδE]
  rw [hrw, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  have hc : (δ * s - δ) a c = 0 := by
    rw [Matrix.sub_apply, hs, Matrix.mul_diagonal]
    by_cases hc0 : c = 0
    · rw [hc0, h0]
      ring
    · by_cases hcz : c = z₁
      · rw [hcz, h1]
        ring
      · rw [ht c hc0 hcz]
        ring
  rw [hc, zero_mul]

theorem caseB_col_zero {δ E s : Matrix (Fin p) (Fin p) F} (hEδ : E * δ = 1) {t : Fin p → F}
    (hs : s = diagonal t) {j : Fin p} (hj : (δ * s * E - 1) *ᵥ Pi.single j 1 = 0) (c : Fin p) :
    (t c - 1) * E c j = 0 := by
  have h1 : E * (δ * s * E - 1) = s * E - E := by
    calc E * (δ * s * E - 1) = (E * δ) * s * E - E := by noncomm_ring
      _ = s * E - E := by rw [hEδ, one_mul]
  have h2 : (E * (δ * s * E - 1)) c j = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun a _ => ?_
    have h3 : (δ * s * E - 1) a j = 0 := by
      have := congrFun hj a
      simpa using this
    rw [h3, mul_zero]
  rw [h1, hs, Matrix.sub_apply, Matrix.diagonal_mul] at h2
  linear_combination h2

theorem exists_range_mem_caseB [Fact p.Prime] (hp : 7 ≤ p) [CharP F 2] {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) {K : Subgroup (SpecialLinearGroup (Fin p) F)}
    (hT : ContainsDiagTorus K) (hTw : ContainsFourierTorus ζ K) :
    ∃ x ∈ K, ∃ I : Finset (Fin p),
      (∀ a b, a ∉ I → ((x : Matrix (Fin p) (Fin p) F) - 1) a b = 0) ∧ 2 ≤ Iᶜ.card ∧
      ∃ j ∉ I, ((x : Matrix (Fin p) (Fin p) F) - 1) *ᵥ Pi.single j 1 ≠ 0 := by
  haveI : NeZero p := ⟨by omega⟩
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  obtain ⟨z₁, z₂, m₁, m₂, m₃, hz₁, hz₂, hm₃, hm₂, hm₁, hz₁0, hz₂0, hm₁0, hz₂I, hm₃I, hz₂m₃⟩ :=
    caseB_indices (p := p) hp
  have hp3 : ¬ 3 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out : p.Prime)).mp h
    omega
  have hdet : (1 + heisShiftMat F p + heisShiftMat F p ^ 2 : Matrix (Fin p) (Fin p) F).det = 1 := by
    rw [det_sparse (by omega) hp3 hζ]
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    calc (3 : F) = 2 + 1 := by norm_num
      _ = 1 := by rw [h2, zero_add]
  obtain ⟨dl, hdl⟩ : ∃ dl : SpecialLinearGroup (Fin p) F,
      (dl : Matrix (Fin p) (Fin p) F) = 1 + heisShiftMat F p + heisShiftMat F p ^ 2 :=
    ⟨⟨_, hdet⟩, rfl⟩
  have hdlK : dl ∈ K := hTw dl ⟨fun j : Fin p => 1 + ζ ^ (j : ℕ) + ζ ^ (2 * (j : ℕ)), by
    rw [hdl]
    exact sparse_mul_heisFourierMat hζ.pow_eq_one⟩
  obtain ⟨sl, hslK, hsl⟩ := caseB_torus_mem hT hζ0 (x := 0) (m := z₁) (Ne.symm hz₁0)
  obtain ⟨t, ht_def⟩ : ∃ t : Fin p → F,
      t = fun i => (if i = 0 then ζ else 1) * (if i = z₁ then ζ⁻¹ else 1) := ⟨_, rfl⟩
  have hsl' : (sl : Matrix (Fin p) (Fin p) F) = diagonal t := by rw [hsl, ht_def]
  have ht1 : ∀ c, c ≠ 0 → c ≠ z₁ → t c = 1 := fun c hc0 hcz => by simp [ht_def, hc0, hcz]
  have ht0 : t 0 = ζ := by simp [ht_def, Ne.symm hz₁0]
  have htz : t z₁ = ζ⁻¹ := by simp [ht_def, hz₁0]
  have hδE : (dl : Matrix (Fin p) (Fin p) F) *
      ((dl⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hEδ : ((dl⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) * dl = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hxmat : ((dl * sl * dl⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      (dl : Matrix (Fin p) (Fin p) F) * sl *
        ((dl⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  generalize ((dl⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) = E at hδE hEδ hxmat
  have hcomm := caseB_inv_comm hdl hδE hEδ
  have hper := caseB_inv_periodic hcomm
  have hrec := caseB_inv_rec (E := E) (by rw [← hdl]; exact hδE)
  refine ⟨dl * sl * dl⁻¹, K.mul_mem (K.mul_mem hdlK hslK) (K.inv_mem hdlK),
    {m₂, m₁, 0, z₁}, ?_, ?_, ?_⟩
  · intro a b ha
    rw [hxmat]
    exact caseB_range hdl hδE hsl' hz₁ hm₂ hm₁ ht1 ha b
  · have hsub : ({z₂, m₃} : Finset (Fin p)) ⊆ ({m₂, m₁, 0, z₁} : Finset (Fin p))ᶜ := by
      intro i hi
      rw [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact Finset.mem_compl.mpr hz₂I
      · exact Finset.mem_compl.mpr hm₃I
    calc 2 = ({z₂, m₃} : Finset (Fin p)).card := (Finset.card_pair hz₂m₃).symm
      _ ≤ _ := Finset.card_le_card hsub
  · by_contra hcon
    push Not at hcon
    have hcol : ∀ j, ((dl : Matrix (Fin p) (Fin p) F) * (sl : Matrix (Fin p) (Fin p) F) * E - 1) *ᵥ
        Pi.single j 1 = 0 → E 0 j = 0 ∧ E z₁ j = 0 := by
      intro j hj
      have a0 := caseB_col_zero hEδ hsl' hj 0
      have a1 := caseB_col_zero hEδ hsl' hj z₁
      rw [ht0] at a0
      rw [htz] at a1
      exact ⟨(mul_eq_zero.mp a0).resolve_left (sub_ne_zero.mpr hζ1),
        (mul_eq_zero.mp a1).resolve_left (sub_ne_zero.mpr fun h => hζ1 (inv_eq_one.mp h))⟩
    obtain ⟨h1, h2⟩ := hcol z₂ (by rw [← hxmat]; exact hcon z₂ hz₂I)
    obtain ⟨h3, -⟩ := hcol m₃ (by rw [← hxmat]; exact hcon m₃ hm₃I)
    exact caseB_inv_not_vanish hper hrec hz₁ hz₂ hm₃ hm₂ hm₁ hz₂0 hm₁0 h1 h2 h3

theorem caseB_isolate_of_range (hp : 5 ≤ p) {l : F} (hl0 : l ≠ 0) (hl1 : l ≠ 1)
    {K : Subgroup (SpecialLinearGroup (Fin p) F)} (hT : ContainsDiagTorus K)
    {x : SpecialLinearGroup (Fin p) F} (hxK : x ∈ K) {I : Finset (Fin p)}
    (hY : ∀ a b, a ∉ I → ((x : Matrix (Fin p) (Fin p) F) - 1) a b = 0) {j j' : Fin p}
    (hjI : j ∉ I) (hj'I : j' ∉ I) (hjj' : j ≠ j')
    (hjne : ((x : Matrix (Fin p) (Fin p) F) - 1) *ᵥ Pi.single j 1 ≠ 0) :
    ∃ a b : Fin p, a ≠ b ∧ ∃ c : F, c ≠ 0 ∧
      ∃ g ∈ K, (g : Matrix (Fin p) (Fin p) F) = 1 + Matrix.single a b c := by
  obtain ⟨zl, hzlK, hzl⟩ := caseB_torus_mem hT hl0 hjj'
  obtain ⟨z, hz⟩ : ∃ z : Fin p → F,
      z = fun i => (if i = j then l else 1) * (if i = j' then l⁻¹ else 1) := ⟨_, rfl⟩
  have hzl' : (zl : Matrix (Fin p) (Fin p) F) = diagonal z := by rw [hzl, hz]
  have hz0 : ∀ i, z i ≠ 0 := by
    intro i
    simp only [hz]
    split_ifs <;> simp [hl0]
  have hzI : ∀ i ∈ I, z i = 1 := by
    intro i hi
    have h1 : i ≠ j := fun h => hjI (h ▸ hi)
    have h2 : i ≠ j' := fun h => hj'I (h ▸ hi)
    simp [hz, h1, h2]
  have hzj : z j = l := by simp [hz, hjj']
  have hxdet : (x : Matrix (Fin p) (Fin p) F).det = 1 := Matrix.SpecialLinearGroup.det_coe x
  have hxinv : ((x⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      (x : Matrix (Fin p) (Fin p) F)⁻¹ :=
    isolate_coe_inv_eq_of_mul_eq_one x
      (Matrix.mul_nonsing_inv _ (by rw [hxdet]; exact isUnit_one))
  have hzdet : (diagonal z).det = 1 := by
    rw [← hzl']
    exact Matrix.SpecialLinearGroup.det_coe zl
  have hzinv : ((zl⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      (diagonal z)⁻¹ :=
    isolate_coe_inv_eq_of_mul_eq_one zl
      (by rw [hzl']; exact Matrix.mul_nonsing_inv _ (by rw [hzdet]; exact isUnit_one))
  have hcomm := diag_comm_of_range hY (by rw [add_sub_cancel, hxdet]; exact isUnit_one) hz0 hzI
  rw [add_sub_cancel] at hcomm
  have hgK : zl * x * zl⁻¹ * x⁻¹ ∈ K :=
    K.mul_mem (K.mul_mem (K.mul_mem hzlK hxK) (K.inv_mem hzlK)) (K.inv_mem hxK)
  have hgmat : ((zl * x * zl⁻¹ * x⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      1 + ((x : Matrix (Fin p) (Fin p) F) - 1) * ((diagonal z)⁻¹ - 1) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, hzl', hzinv, hxinv]
    exact hcomm
  have hMentry : ∀ a b, (((x : Matrix (Fin p) (Fin p) F) - 1) * ((diagonal z)⁻¹ - 1)) a b =
      ((x : Matrix (Fin p) (Fin p) F) - 1) a b * ((z b)⁻¹ - 1) := by
    intro a b
    rw [inv_diagonal_of_ne_zero hz0, mul_sub, mul_one, Matrix.sub_apply, Matrix.mul_diagonal]
    ring
  have hMsupp : RootSuppIn I (((x : Matrix (Fin p) (Fin p) F) - 1) * ((diagonal z)⁻¹ - 1)) := by
    intro a b hab
    rw [hMentry] at hab
    refine ⟨?_, ?_⟩
    · by_contra ha
      exact hab (by rw [hY a b ha, zero_mul])
    · intro hb
      exact hab (by rw [hzI b hb, inv_one, sub_self, mul_zero])
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, ((x : Matrix (Fin p) (Fin p) F) - 1) a₀ j ≠ 0 := by
    by_contra h
    push Not at h
    apply hjne
    ext a
    simpa using h a
  have hab : (((x : Matrix (Fin p) (Fin p) F) - 1) * ((diagonal z)⁻¹ - 1)) a₀ j ≠ 0 := by
    rw [hMentry, hzj]
    exact mul_ne_zero ha₀ (sub_ne_zero.mpr fun h => hl1 (inv_eq_one.mp h))
  obtain ⟨c, hc, g', hg'K, hg'⟩ :=
    exists_single_mem_of_suppIn hp hl0 hl1 hT hMsupp hab ⟨_, hgK, hgmat⟩
  exact ⟨a₀, j, fun h => (hMsupp a₀ j hab).2 (h ▸ (hMsupp a₀ j hab).1), c, hc, g', hg'K, hg'⟩

theorem exists_single_mem_caseB [Fact p.Prime] (hp : 7 ≤ p) [CharP F 2] {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) {K : Subgroup (SpecialLinearGroup (Fin p) F)}
    (hT : ContainsDiagTorus K) (hTw : ContainsFourierTorus ζ K) :
    ∃ a b : Fin p, a ≠ b ∧ ∃ c : F, c ≠ 0 ∧
      ∃ g ∈ K, (g : Matrix (Fin p) (Fin p) F) = 1 + Matrix.single a b c := by
  obtain ⟨x, hxK, I, hY, hcard, j, hjI, hjne⟩ := exists_range_mem_caseB hp hζ hT hTw
  obtain ⟨j', hj'I, hj'j⟩ := Finset.exists_mem_ne (lt_of_lt_of_le one_lt_two hcard) j
  exact caseB_isolate_of_range (by omega) (hζ.ne_zero (by omega)) (hζ.ne_one (by omega)) hT hxK
    hY hjI (Finset.mem_compl.mp hj'I) (Ne.symm hj'j) hjne

end CFSG.LieType.SeitzGeneration
