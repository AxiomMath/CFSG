module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.Involutions
public import CFSG.LocalAnalysis.EvenBN.U4.Model.Perfect

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement Pointwise

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section FieldFixed

@[expose] def miyamotoCu : Subgroup (GL (Fin 4) K) :=
  (Units.map (h.bar.mapMatrix : Matrix (Fin 4) (Fin 4) K →+* Matrix (Fin 4) (Fin 4) K).toMonoidHom
    ).eqLocus (MonoidHom.id _)

theorem mem_miyamotoCu {g : GL (Fin 4) K} :
    g ∈ miyamotoCu h ↔ (g : Matrix (Fin 4) (Fin 4) K).map h.bar = g :=
  Units.ext_iff

theorem miyamotoXGL_mem_Cu {a b c d : K} : miyamotoXGL h a b c d ∈ miyamotoCu h ↔
    h.bar a = a ∧ h.bar b = b ∧ h.bar c = c ∧ h.bar d = d := by
  rw [mem_miyamotoCu, coe_miyamotoXGL]
  constructor
  · intro e
    exact ⟨by simpa [miyamotoX] using congrFun (congrFun e 1) 0,
      by simpa [miyamotoX] using congrFun (congrFun e 2) 1,
      by simpa [miyamotoX] using congrFun (congrFun e 2) 0,
      by simpa [miyamotoX] using congrFun (congrFun e 3) 0⟩
  · rintro ⟨ha, hb, hc, hd⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [miyamotoX, ha, hb, hc, hd]

theorem miyamotoN1Hom_mem_N1_inf_Cu {m : SpecialLinearGroup (Fin 2) K}
    (hm : ∀ i j, h.bar ((m : Matrix (Fin 2) (Fin 2) K) i j) = (m : Matrix (Fin 2) (Fin 2) K) i j) :
    miyamotoN1Hom h m ∈ miyamotoN1 h ⊓ miyamotoCu h := by
  refine ⟨⟨m, rfl⟩, (mem_miyamotoCu h).2 ?_⟩
  rw [coe_miyamotoN1Hom]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [miyamotoN1Mat, hm]

theorem miyamotoN1_inf_Cu : miyamotoN1 h ⊓ miyamotoCu h = miyamotoN1F h := by
  ext n
  rw [mem_inf, mem_miyamotoCu, mem_miyamotoN1F_iff]

theorem miyamotoN1F_le_N1 : miyamotoN1F h ≤ miyamotoN1 h := by
  rintro _ ⟨mF, rfl⟩
  exact ⟨_, rfl⟩

theorem miyamotoN1Cu_le_normalizer [CharP K 2] : miyamotoN1 h ⊓ miyamotoCu h ≤
    normalizer ((miyamotoA1 h ⊓ miyamotoCu h : Subgroup (GL (Fin 4) K)) : Set (GL (Fin 4) K)) := by
  intro n hn'
  obtain ⟨hn, hnC⟩ := mem_inf.1 hn'
  have hA := miyamotoN1_le_normalizer_A1 h hn
  refine mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
    exact mem_inf.2 ⟨(mem_normalizer_iff.1 hA x).1 hx1, mul_mem (mul_mem hnC hx2) (inv_mem hnC)⟩
  · obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
    refine mem_inf.2 ⟨(mem_normalizer_iff.1 hA x).2 hx1, ?_⟩
    have e : x = n⁻¹ * (n * x * n⁻¹) * n := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hnC) hx2) hnC

end FieldFixed

section Centralizer

variable [CharP K 2]

omit [CharP K 2] in
theorem shapeOne_of_commute_miyamotoZ2 {g : GL (Fin 4) K}
    (hc : g * miyamotoXGL h 0 0 1 0 = miyamotoXGL h 0 0 1 0 * g) :
    (g : Matrix (Fin 4) (Fin 4) K) 0 2 = 0 ∧ (g : Matrix (Fin 4) (Fin 4) K) 0 3 = 0 ∧
      (g : Matrix (Fin 4) (Fin 4) K) 1 2 = 0 ∧ (g : Matrix (Fin 4) (Fin 4) K) 1 3 = 0 := by
  have ent : ∀ i j, ((g : Matrix (Fin 4) (Fin 4) K) * miyamotoX h 0 0 1 0) i j =
      (miyamotoX h 0 0 1 0 * (g : Matrix (Fin 4) (Fin 4) K)) i j := fun i j => by
    rw [← coe_miyamotoXGL, ← Units.val_mul, ← Units.val_mul, hc]
  have q00 := ent 0 0
  have q01 := ent 0 1
  have q10 := ent 1 0
  have q11 := ent 1 1
  simp [miyamotoX, Matrix.mul_apply, Fin.sum_univ_four] at q00 q01 q10 q11
  exact ⟨q00, q01, q10, q11⟩

theorem mul_comm_of_mem_miyamotoA1 {x y : GL (Fin 4) K} (hx : x ∈ miyamotoA1 h)
    (hy : y ∈ miyamotoA1 h) : x * y = y * x := by
  obtain ⟨b, c, d, hb, -, rfl⟩ := (mem_A1 h).1 hx
  obtain ⟨b', c', d', hb', -, rfl⟩ := (mem_A1 h).1 hy
  rw [miyamotoXGL_mul_A1 h hb, miyamotoXGL_mul_A1 h hb', add_comm b, add_comm c, add_comm d]

theorem centralizer_miyamotoZ2 :
    gramSU h (miyamotoJ4 K) ⊓ centralizer ({LocalAnalysis.miyamotoZ2 K} : Set (GL (Fin 4) K)) =
      miyamotoA1 h ⊔ miyamotoN1F h := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hzA : miyamotoXGL h 0 0 1 0 ∈ miyamotoA1 h :=
    (miyamotoXGL_mem_A1 h).2 ⟨rfl, map_zero _, map_zero _⟩
  apply le_antisymm
  · intro g hg'
    obtain ⟨hg, hc⟩ := mem_inf.1 hg'
    rw [miyamotoZ2_eq h, mem_centralizer_singleton_iff] at hc
    obtain ⟨h02, h03, h12, h13⟩ := shapeOne_of_commute_miyamotoZ2 h hc
    obtain ⟨a, ha, i, hi, n, hn, rfl⟩ := exists_mul_of_shapeOne h hg h02 h03 h12 h13
    obtain ⟨t, ht, rfl⟩ := (mem_miyamotoI1 h).1 hi
    have haz := mul_comm_of_mem_miyamotoA1 h ha hzA
    have hk : miyamotoIHom h (t, t) * n * miyamotoXGL h 0 0 1 0 =
        miyamotoXGL h 0 0 1 0 * (miyamotoIHom h (t, t) * n) := by
      refine mul_left_cancel (a := a) ?_
      calc a * (miyamotoIHom h (t, t) * n * miyamotoXGL h 0 0 1 0)
          = a * miyamotoIHom h (t, t) * n * miyamotoXGL h 0 0 1 0 := by group
        _ = miyamotoXGL h 0 0 1 0 * (a * miyamotoIHom h (t, t) * n) := hc
        _ = miyamotoXGL h 0 0 1 0 * a * (miyamotoIHom h (t, t) * n) := by group
        _ = a * miyamotoXGL h 0 0 1 0 * (miyamotoIHom h (t, t) * n) := by rw [haz]
        _ = a * (miyamotoXGL h 0 0 1 0 * (miyamotoIHom h (t, t) * n)) := by group
    have hconj : (miyamotoIHom h (t, t) * n)⁻¹ * miyamotoXGL h 0 0 1 0 *
        (miyamotoIHom h (t, t) * n) = miyamotoXGL h 0 0 1 0 := by
      rw [mul_assoc, ← hk]
      group
    have hD : (miyamotoIHom h (t, t))⁻¹ * miyamotoXGL h 0 0 1 0 * miyamotoIHom h (t, t) ∈
        miyamotoA1 h := miyamotoIHom_conj_mem_unipotent h _ hzA
    have hQ := congrArg (miyamotoQA1 h) hconj
    rw [show (miyamotoIHom h (t, t) * n)⁻¹ * miyamotoXGL h 0 0 1 0 * (miyamotoIHom h (t, t) * n) =
        n⁻¹ * ((miyamotoIHom h (t, t))⁻¹ * miyamotoXGL h 0 0 1 0 * miyamotoIHom h (t, t)) * n by
          group, miyamotoQA1_conj_N1 h hn hD, miyamotoQA1_conj_I1 h ht hzA,
      miyamotoQA1_miyamotoXGL] at hQ
    simp only [map_one, mul_one, mul_zero, add_zero] at hQ
    have ht1 : t = 1 := by
      have h4 : ((t : K) - 1) ^ 4 = 0 := by
        linear_combination hQ + (-2 * (t : K) ^ 3 + 3 * (t : K) ^ 2 - 2 * (t : K) + 1) * h2
      exact Units.ext (sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h4))
    have hD1 : miyamotoIHom h (t, t) = 1 := by
      rw [ht1]
      exact map_one (miyamotoIHom h)
    rw [hD1, one_mul] at hk
    rw [hD1, mul_one]
    have hn' : n ∈ miyamotoN1F h := by
      rw [← miyamotoN1_inf_centralizer_z2 h, miyamotoZ2_eq h]
      exact ⟨hn, mem_centralizer_singleton_iff.2 hk⟩
    exact mul_mem (mem_sup_left ha) (mem_sup_right hn')
  · refine sup_le (le_inf (miyamotoUnipotent_le_SU h true false) fun x hx => ?_) fun n hn => ?_
    · rw [miyamotoZ2_eq h, mem_centralizer_singleton_iff]
      exact mul_comm_of_mem_miyamotoA1 h hx hzA
    · rw [← miyamotoN1_inf_centralizer_z2 h] at hn
      exact ⟨miyamotoN1_le_gramSU h hn.1, hn.2⟩

theorem exists_of_mem_centralizer_miyamotoZ2 {g : GL (Fin 4) K}
    (hg : g ∈ gramSU h (miyamotoJ4 K) ⊓
      centralizer ({LocalAnalysis.miyamotoZ2 K} : Set (GL (Fin 4) K))) :
    ∃ b c d : K, h.bar b = b ∧ h.bar d = d ∧ ∃ m : SpecialLinearGroup (Fin 2) K,
      (∀ i j, h.bar ((m : Matrix (Fin 2) (Fin 2) K) i j) = (m : Matrix (Fin 2) (Fin 2) K) i j) ∧
        g = miyamotoXGL h 0 b c d * miyamotoN1Hom h m := by
  rw [centralizer_miyamotoZ2 h, ← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _
    ((miyamotoN1F_le_N1 h).trans (miyamotoN1_le_normalizer_A1 h))] at hg
  obtain ⟨a, ha, n, ⟨mF, rfl⟩, rfl⟩ := hg
  obtain ⟨b, c, d, hb, hd, rfl⟩ := (mem_A1 h).1 ha
  exact ⟨b, c, d, hb, hd, SpecialLinearGroup.map (h.fixedField.subtype : h.fixedField →+* K) mF,
    fun i j => (mF i j).2, rfl⟩

end Centralizer

section Beta

variable [CharP K 2]

@[expose] def miyamotoBetaZ2 (g : GL (Fin 4) K) : K :=
  (g : Matrix (Fin 4) (Fin 4) K) 2 0 * (g : Matrix (Fin 4) (Fin 4) K) 1 1 +
    (g : Matrix (Fin 4) (Fin 4) K) 2 1 * (g : Matrix (Fin 4) (Fin 4) K) 1 0

omit [CharP K 2] in
theorem miyamotoBetaZ2_one : miyamotoBetaZ2 (1 : GL (Fin 4) K) = 0 := by
  simp [miyamotoBetaZ2]

theorem miyamotoBetaZ2_mul_N1 (m : SpecialLinearGroup (Fin 2) K) (b c d : K) :
    miyamotoBetaZ2 (miyamotoXGL h 0 b c d * miyamotoN1Hom h m) = c := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hdet := m.2
  rw [Matrix.det_fin_two] at hdet
  simp only [miyamotoBetaZ2, Units.val_mul, coe_miyamotoXGL, coe_miyamotoN1Hom]
  simp [miyamotoN1Mat, miyamotoX, Matrix.mul_apply, Fin.sum_univ_four]
  linear_combination c * hdet + (c * (m : Matrix (Fin 2) (Fin 2) K) 0 1 *
    (m : Matrix (Fin 2) (Fin 2) K) 1 0 + b * (m : Matrix (Fin 2) (Fin 2) K) 1 0 *
      (m : Matrix (Fin 2) (Fin 2) K) 1 1) * h2

theorem miyamotoBetaZ2_mul_sub_mem {g g' : GL (Fin 4) K}
    (hg : g ∈ gramSU h (miyamotoJ4 K) ⊓
      centralizer ({LocalAnalysis.miyamotoZ2 K} : Set (GL (Fin 4) K)))
    (hg' : g' ∈ gramSU h (miyamotoJ4 K) ⊓
      centralizer ({LocalAnalysis.miyamotoZ2 K} : Set (GL (Fin 4) K))) :
    miyamotoBetaZ2 (g * g') - miyamotoBetaZ2 g - miyamotoBetaZ2 g' ∈ h.fixedField := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hbb := h.bar_bar
  obtain ⟨b, c, d, hb, hd, m, hm, rfl⟩ := exists_of_mem_centralizer_miyamotoZ2 h hg
  obtain ⟨b', c', d', hb', hd', m', -, rfl⟩ := exists_of_mem_centralizer_miyamotoZ2 h hg'
  have e : miyamotoXGL h 0 b c d * miyamotoN1Hom h m *
      (miyamotoXGL h 0 b' c' d' * miyamotoN1Hom h m') =
      miyamotoXGL h 0 b c d * ((miyamotoN1Hom h m⁻¹)⁻¹ * miyamotoXGL h 0 b' c' d' *
        miyamotoN1Hom h m⁻¹) * miyamotoN1Hom h (m * m') := by
    rw [map_inv, inv_inv, map_mul]
    group
  rw [e, miyamotoN1Hom_conj_A1 h _ hb' hd', miyamotoXGL_mul_A1 h hb, miyamotoBetaZ2_mul_N1,
    miyamotoBetaZ2_mul_N1, miyamotoBetaZ2_mul_N1, h.mem_fixedField]
  have hdet := m.2
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, map_add, map_sub, map_mul, map_neg, hm, hbb, hb', hd']
  linear_combination (h.bar c' - c') * hdet + (h.bar c' - c') * (m : Matrix (Fin 2) (Fin 2) K) 0 1 *
    (m : Matrix (Fin 2) (Fin 2) K) 1 0 * h2

theorem mem_of_miyamotoBetaZ2_mem {g : GL (Fin 4) K}
    (hg : g ∈ gramSU h (miyamotoJ4 K) ⊓
      centralizer ({LocalAnalysis.miyamotoZ2 K} : Set (GL (Fin 4) K)))
    (hβ : miyamotoBetaZ2 g ∈ h.fixedField) :
    g ∈ (miyamotoA1 h ⊓ miyamotoCu h) ⊔ (miyamotoN1 h ⊓ miyamotoCu h) := by
  obtain ⟨b, c, d, hb, hd, m, hm, rfl⟩ := exists_of_mem_centralizer_miyamotoZ2 h hg
  rw [miyamotoBetaZ2_mul_N1, h.mem_fixedField] at hβ
  exact mul_mem (mem_sup_left ⟨(miyamotoXGL_mem_A1 h).2 ⟨rfl, hb, hd⟩,
    (miyamotoXGL_mem_Cu h).2 ⟨map_zero _, hb, hβ, hd⟩⟩)
    (mem_sup_right (miyamotoN1Hom_mem_N1_inf_Cu h hm))

end Beta

section Derived

variable [CharP K 2]

theorem miyamotoA1Cu_sup_N1Cu_le_commutator (hf : 2 ≤ f) {H : Subgroup (GL (Fin 4) K)}
    (hA : miyamotoA1 h ⊓ miyamotoCu h ≤ H) (hN : miyamotoN1 h ⊓ miyamotoCu h ≤ H) :
    (miyamotoA1 h ⊓ miyamotoCu h) ⊔ (miyamotoN1 h ⊓ miyamotoCu h) ≤ ⁅H, H⁆ := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨t, htF, ht⟩ := exists_fixed_unit_sq_ne_one h hf
  have hx : ∀ {b c d : K}, h.bar b = b → h.bar c = c → h.bar d = d →
      miyamotoXGL h 0 b c d ∈ H := fun hb hc hd =>
    hA ⟨(miyamotoXGL_mem_A1 h).2 ⟨rfl, hb, hd⟩, (miyamotoXGL_mem_Cu h).2 ⟨map_zero _, hb, hc, hd⟩⟩
  have hcomm : ∀ {b c d : K} {n : GL (Fin 4) K}, h.bar b = b → h.bar c = c → h.bar d = d →
      n ∈ H → miyamotoXGL h 0 b c d * (n⁻¹ * miyamotoXGL h 0 b c d * n) ∈ ⁅H, H⁆ := by
    intro b c d n hb hc hd hn
    have hinv : (miyamotoXGL h 0 b c d)⁻¹ = miyamotoXGL h 0 b c d :=
      inv_eq_of_mul_eq_one_right (miyamotoXGL_A1_mul_self h hb)
    have e : miyamotoXGL h 0 b c d * (n⁻¹ * miyamotoXGL h 0 b c d * n) =
        ⁅(miyamotoXGL h 0 b c d)⁻¹, n⁻¹⁆ := by
      rw [commutatorElement_def, inv_inv, inv_inv, hinv]
      group
    rw [e]
    exact commutator_mem_commutator (inv_mem (hx hb hc hd)) (inv_mem hn)
  have hm1 : ∀ i j, h.bar (((diagSL2 t : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) i j) = ((diagSL2 t : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [coe_diagSL2, htF]
  have hn1 : miyamotoN1Hom h (diagSL2 t) ∈ H := hN (miyamotoN1Hom_mem_N1_inf_Cu h hm1)
  have ht0 : (t : K) ≠ 0 := t.ne_zero
  have hs1 : 1 + ((t : K) ^ 2)⁻¹ ≠ 0 := by
    intro e
    apply ht
    have : ((t : K) ^ 2)⁻¹ = 1 := by linear_combination e - h2
    exact inv_eq_one.1 this
  have hs2 : 1 + (t : K) ^ 2 ≠ 0 := by
    intro e
    exact ht (by linear_combination e - h2)
  have step1 : ∀ {b d : K}, h.bar b = b → h.bar d = d → miyamotoXGL h 0 b 0 d ∈ ⁅H, H⁆ := by
    intro b d hb hd
    obtain ⟨u, hu⟩ : ∃ u : K, u = (1 + ((t : K) ^ 2)⁻¹)⁻¹ * b := ⟨_, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v : K, v = (1 + (t : K) ^ 2)⁻¹ * d := ⟨_, rfl⟩
    have hu' : u * (1 + ((t : K) ^ 2)⁻¹) = b := by
      rw [hu, mul_comm, ← mul_assoc, mul_inv_cancel₀ hs1, one_mul]
    have hv' : v * (1 + (t : K) ^ 2) = d := by
      rw [hv, mul_comm, ← mul_assoc, mul_inv_cancel₀ hs2, one_mul]
    have huF : h.bar u = u := by
      rw [hu]
      simp [htF, hb]
    have hvF : h.bar v = v := by
      rw [hv]
      simp [htF, hd]
    have key := hcomm huF (map_zero _) hvF hn1
    rw [miyamotoN1Hom_conj_A1 h _ huF hvF, miyamotoXGL_mul_A1 h huF] at key
    simp only [coe_diagSL2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, map_zero, map_inv₀,
      htF] at key
    convert key using 2
    · rw [← hu']
      ring
    · ring
    · rw [← hv']
      ring
  have hm2 : ∀ i j, h.bar (((upperSL2 (1 : K) : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) i j) = ((upperSL2 (1 : K) : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [coe_upperSL2]
  have hn2 : miyamotoN1Hom h (upperSL2 1) ∈ H := hN (miyamotoN1Hom_mem_N1_inf_Cu h hm2)
  have step2 : ∀ {c : K}, h.bar c = c → miyamotoXGL h 0 c c 0 ∈ ⁅H, H⁆ := by
    intro c hc
    have key := hcomm (map_zero _) (map_zero _) hc hn2
    rw [miyamotoN1Hom_conj_A1 h _ (map_zero _) hc, miyamotoXGL_mul_A1 h (map_zero _)] at key
    convert key using 2
    · simp [coe_upperSL2]
      linear_combination c * h2
    · simp [coe_upperSL2]
      linear_combination c * h2
    · simp [coe_upperSL2]
      linear_combination -c * h2
  refine sup_le (fun x hx => ?_) ?_
  · obtain ⟨hxA, hxC⟩ := hx
    obtain ⟨b, c, d, hb, hd, rfl⟩ := (mem_A1 h).1 hxA
    have hc := ((miyamotoXGL_mem_Cu h).1 hxC).2.2.1
    have hbc : h.bar (b + c) = b + c := by rw [map_add, hb, hc]
    have e : miyamotoXGL h 0 b c d = miyamotoXGL h 0 (b + c) 0 d * miyamotoXGL h 0 c c 0 := by
      rw [miyamotoXGL_mul_A1 h hbc, miyamotoXGL_inj]
      exact ⟨rfl, by linear_combination -c * h2, by ring, by ring⟩
    rw [e]
    exact mul_mem (step1 hbc hd) (step2 hc)
  · have hNF : miyamotoN1F h ≤ H := by
      rw [← miyamotoN1_inf_Cu h]
      exact hN
    have ht0' : (⟨(t : K), htF⟩ : h.fixedField) ≠ 0 := fun e => t.ne_zero (congrArg Subtype.val e)
    have ht' : ((Units.mk0 _ ht0' : h.fixedFieldˣ) : h.fixedField) ^ 2 ≠ 1 := fun e =>
      ht (by simpa using congrArg Subtype.val e)
    rw [miyamotoN1_inf_Cu h]
    rintro _ ⟨m, rfl⟩
    exact commutator_mono hNF hNF (mem_commutator_range_of_SL2 _ ht' m)

theorem commutator_miyamotoA1Cu_sup_N1Cu (hf : 2 ≤ f) :
    ⁅(miyamotoA1 h ⊓ miyamotoCu h) ⊔ (miyamotoN1 h ⊓ miyamotoCu h),
      (miyamotoA1 h ⊓ miyamotoCu h) ⊔ (miyamotoN1 h ⊓ miyamotoCu h)⁆ =
      (miyamotoA1 h ⊓ miyamotoCu h) ⊔ (miyamotoN1 h ⊓ miyamotoCu h) :=
  le_antisymm (commutator_le_self _)
    (miyamotoA1Cu_sup_N1Cu_le_commutator h hf le_sup_left le_sup_right)

theorem commutator_centralizer_miyamotoZ2 (hf : 2 ≤ f) :
    ⁅gramSU h (miyamotoJ4 K) ⊓ centralizer ({LocalAnalysis.miyamotoZ2 K} : Set (GL (Fin 4) K)),
      gramSU h (miyamotoJ4 K) ⊓ centralizer ({LocalAnalysis.miyamotoZ2 K} : Set (GL (Fin 4) K))⁆ =
      (miyamotoA1 h ⊓ miyamotoCu h) ⊔ (miyamotoN1 h ⊓ miyamotoCu h) := by
  refine le_antisymm (commutator_le.2 fun g hg g' hg' => ?_)
    (miyamotoA1Cu_sup_N1Cu_le_commutator h hf ?_ ?_)
  · have hc : ⁅g, g'⁆ ∈ gramSU h (miyamotoJ4 K) ⊓
        centralizer ({LocalAnalysis.miyamotoZ2 K} : Set (GL (Fin 4) K)) := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hg hg') (inv_mem hg)) (inv_mem hg')
    refine mem_of_miyamotoBetaZ2_mem h hc ?_
    have e1 := miyamotoBetaZ2_mul_sub_mem h (mul_mem (mul_mem hg hg') (inv_mem hg)) (inv_mem hg')
    have e2 := miyamotoBetaZ2_mul_sub_mem h (mul_mem hg hg') (inv_mem hg)
    have e3 := miyamotoBetaZ2_mul_sub_mem h hg hg'
    have e4 := miyamotoBetaZ2_mul_sub_mem h hg (inv_mem hg)
    have e5 := miyamotoBetaZ2_mul_sub_mem h hg' (inv_mem hg')
    rw [mul_inv_cancel, miyamotoBetaZ2_one] at e4 e5
    have key : miyamotoBetaZ2 ⁅g, g'⁆ =
        (miyamotoBetaZ2 (g * g' * g⁻¹ * g'⁻¹) - miyamotoBetaZ2 (g * g' * g⁻¹) -
          miyamotoBetaZ2 g'⁻¹) +
        (miyamotoBetaZ2 (g * g' * g⁻¹) - miyamotoBetaZ2 (g * g') - miyamotoBetaZ2 g⁻¹) +
        (miyamotoBetaZ2 (g * g') - miyamotoBetaZ2 g - miyamotoBetaZ2 g') -
        (0 - miyamotoBetaZ2 g - miyamotoBetaZ2 g⁻¹) -
        (0 - miyamotoBetaZ2 g' - miyamotoBetaZ2 g'⁻¹) := by
      rw [commutatorElement_def]
      ring
    rw [key]
    exact sub_mem (sub_mem (add_mem (add_mem e1 e2) e3) e4) e5
  · rw [centralizer_miyamotoZ2 h]
    exact inf_le_left.trans le_sup_left
  · rw [miyamotoN1_inf_Cu h, centralizer_miyamotoZ2 h]
    exact le_sup_right

end Derived

section Pull

variable {G : Type} [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K))

theorem miyamotoPull_inf_centralizer_singleton {x : GL (Fin 4) K}
    (hx : x ∈ gramSU h (miyamotoJ4 K)) :
    miyamotoPull h L η (gramSU h (miyamotoJ4 K) ⊓ centralizer ({x} : Set (GL (Fin 4) K))) =
      L ⊓ centralizer ({((η.symm ⟨x, hx⟩ : L) : G)} : Set G) := by
  ext y
  rw [mem_inf, mem_miyamotoPull, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨g, ⟨-, hgC⟩, rfl⟩
    refine ⟨(η.symm g).2, ?_⟩
    have e : g * ⟨x, hx⟩ = ⟨x, hx⟩ * g := Subtype.ext (mem_centralizer_singleton_iff.1 hgC)
    rw [← L.coe_mul, ← L.coe_mul, ← map_mul, ← map_mul, e]
  · rintro ⟨hyL, hyC⟩
    refine ⟨η ⟨y, hyL⟩, ⟨(η ⟨y, hyL⟩).2, mem_centralizer_singleton_iff.2 ?_⟩, by
      rw [MulEquiv.symm_apply_apply]⟩
    have e : (⟨y, hyL⟩ : L) * η.symm ⟨x, hx⟩ = η.symm ⟨x, hx⟩ * ⟨y, hyL⟩ := Subtype.ext hyC
    have e' := congrArg η e
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at e'
    exact congrArg Subtype.val e'

variable [CharP K 2]

theorem commutator_centralizer_miyamotoZ2G (hf : 2 ≤ f) :
    ⁅L ⊓ centralizer ({miyamotoZ2G h L η} : Set G),
        L ⊓ centralizer ({miyamotoZ2G h L η} : Set G)⁆ =
        miyamotoPull h L η ((miyamotoA1 h ⊓ miyamotoCu h) ⊔ (miyamotoN1 h ⊓ miyamotoCu h)) ∧
      ⁅miyamotoPull h L η ((miyamotoA1 h ⊓ miyamotoCu h) ⊔ (miyamotoN1 h ⊓ miyamotoCu h)),
        miyamotoPull h L η ((miyamotoA1 h ⊓ miyamotoCu h) ⊔ (miyamotoN1 h ⊓ miyamotoCu h))⁆ =
        miyamotoPull h L η ((miyamotoA1 h ⊓ miyamotoCu h) ⊔ (miyamotoN1 h ⊓ miyamotoCu h)) := by
  have hX : (miyamotoA1 h ⊓ miyamotoCu h) ⊔ (miyamotoN1 h ⊓ miyamotoCu h) ≤
      gramSU h (miyamotoJ4 K) := sup_le (inf_le_left.trans (miyamotoUnipotent_le_SU h true false))
    (inf_le_left.trans (miyamotoN1_le_gramSU h))
  have e := miyamotoPull_inf_centralizer_singleton h L η (miyamotoZ2_mem_gramSU h)
  refine ⟨?_, ?_⟩
  · unfold miyamotoZ2G
    rw [← e, ← miyamotoPull_commutator h L η inf_le_left inf_le_left,
      commutator_centralizer_miyamotoZ2 h hf]
  · rw [← miyamotoPull_commutator h L η hX hX, commutator_miyamotoA1Cu_sup_N1Cu h hf]

end Pull

end CFSG.LocalAnalysis.EvenBN.U4
