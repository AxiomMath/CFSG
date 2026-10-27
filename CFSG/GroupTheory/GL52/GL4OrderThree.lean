module

public import CFSG.GroupTheory.GL52.OrderThreeCover
import CFSG.GroupTheory.ElementaryAbelianTransport

public noncomputable section

namespace CFSG.GroupTheory.GL52

open Matrix

abbrev M4 : Type := Matrix (Fin 4) (Fin 4) (ZMod 2)

abbrev G42 : Type := GL (Fin 4) (ZMod 2)

@[expose] def mk4 (A B : M4) (h : A * B = 1) : G42 :=
  ⟨A, B, h, mul_eq_one_comm.1 h⟩

@[simp] theorem coe_mk4 (A B : M4) (h : A * B = 1) : ((mk4 A B h : G42) : M4) = A :=
  rfl

@[simp] theorem coe_mk4_inv (A B : M4) (h : A * B = 1) :
    (((mk4 A B h)⁻¹ : G42) : M4) = B :=
  rfl

theorem card_G42 : Nat.card G42 = 2 ^ 6 * 3 ^ 2 * 5 * 7 := by
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_four]
  norm_num

@[expose] def gl4EmbM (A : M4) : M5 :=
  !![A 0 0, A 0 1, A 0 2, A 0 3, 0; A 1 0, A 1 1, A 1 2, A 1 3, 0;
    A 2 0, A 2 1, A 2 2, A 2 3, 0; A 3 0, A 3 1, A 3 2, A 3 3, 0; 0, 0, 0, 0, 1]

theorem gl4EmbM_mul (A B : M4) : gl4EmbM A * gl4EmbM B = gl4EmbM (A * B) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gl4EmbM, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_four]

theorem gl4EmbM_one : gl4EmbM 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] def gl4Emb : G42 →* G52 where
  toFun A := mk5 (gl4EmbM A) (gl4EmbM ((A⁻¹ : G42) : M4)) (by
    rw [gl4EmbM_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, gl4EmbM_one])
  map_one' := Units.ext (by rw [coe_mk5, Units.val_one, Units.val_one, gl4EmbM_one])
  map_mul' A B := Units.ext (by
    rw [coe_mk5, Units.val_mul, Units.val_mul, coe_mk5, coe_mk5, gl4EmbM_mul])

@[expose] def gl4Blk (g : M5) : M4 :=
  !![g 0 0, g 0 1, g 0 2, g 0 3; g 1 0, g 1 1, g 1 2, g 1 3; g 2 0, g 2 1, g 2 2, g 2 3;
    g 3 0, g 3 1, g 3 2, g 3 3]

theorem gl4Blk_emb (A : M4) : gl4Blk (gl4EmbM A) = A := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem gl4EmbM_injective : Function.Injective gl4EmbM := fun A B h => by
  rw [← gl4Blk_emb A, h, gl4Blk_emb]

theorem gl4Emb_injective : Function.Injective gl4Emb := fun _ _ h =>
  Units.ext (gl4EmbM_injective (congrArg (fun g : G52 => (g : M5)) h))

abbrev gl4Shape (g : M5) : Prop :=
  g *ᵥ Pi.single 4 1 = Pi.single 4 1 ∧ Pi.single 4 1 ᵥ* g = Pi.single 4 1

theorem gl4EmbM_blk {g : M5} (hg : gl4Shape g) : gl4EmbM (gl4Blk g) = g := by
  obtain ⟨h1, h2⟩ := hg
  have c : ∀ i, g i 4 = (Pi.single 4 1 : V5) i := fun i => by
    have := congrFun h1 i
    rwa [mulVec_single_one, col_apply] at this
  have r : ∀ j, g 4 j = (Pi.single 4 1 : V5) j := fun j => by
    have := congrFun h2 j
    rwa [single_one_vecMul, row_apply] at this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gl4EmbM, gl4Blk, c, r, Pi.single_apply]

theorem gl4Shape_inv {g : G52} (hg : gl4Shape (g : M5)) : gl4Shape ((g⁻¹ : G52) : M5) := by
  obtain ⟨h1, h2⟩ := hg
  constructor
  · conv_lhs => rw [← h1]
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  · conv_lhs => rw [← h2]
    rw [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]

theorem mem_range_gl4Emb {g : G52} (hg : gl4Shape (g : M5)) : g ∈ gl4Emb.range := by
  have hBB : gl4Blk (g : M5) * gl4Blk ((g⁻¹ : G52) : M5) = 1 := by
    apply gl4EmbM_injective
    rw [← gl4EmbM_mul, gl4EmbM_blk hg, gl4EmbM_blk (gl4Shape_inv hg), ← Units.val_mul,
      mul_inv_cancel, Units.val_one, gl4EmbM_one]
  exact ⟨⟨_, _, hBB, mul_eq_one_comm.1 hBB⟩, Units.ext (gl4EmbM_blk hg)⟩

theorem gl4_card_comap {H : Subgroup G52} (h : H ≤ gl4Emb.range) :
    Nat.card (H.comap gl4Emb) = Nat.card H := by
  rw [← Subgroup.card_map_of_injective gl4Emb_injective, Subgroup.map_comap_eq_self h]

theorem gl4_comap_equiv {H : Subgroup G52} (h : H ≤ gl4Emb.range) :
    Nonempty (H.comap gl4Emb ≃* H) :=
  ⟨(Subgroup.equivMapOfInjective _ gl4Emb gl4Emb_injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self h))⟩

theorem gl4_comap_centralizer (a : G42) :
    (Subgroup.centralizer ({gl4Emb a} : Set G52)).comap gl4Emb = Subgroup.centralizer {a} := by
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  exact gl4Emb_injective.eq_iff

@[expose] def gl4AM : M4 :=
  !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def gl4BM : M4 :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1]

theorem gl4_facts : gl4AM * gl4AM ^ 2 = 1 ∧ gl4BM * gl4BM ^ 2 = 1 ∧
    gl4EmbM gl4AM = ord3T2M ∧ gl4EmbM gl4BM = syl3TbM ∧ ord3T2M * syl3TbM = ord3T4M := by
  decide +kernel

@[expose] def gl4A : G42 :=
  mk4 gl4AM (gl4AM ^ 2) gl4_facts.1

@[expose] def gl4B : G42 :=
  mk4 gl4BM (gl4BM ^ 2) gl4_facts.2.1

@[expose] def gl4Al : G42 :=
  gl4A * gl4B

theorem gl4Emb_A : gl4Emb gl4A = ord3T2 :=
  Units.ext gl4_facts.2.2.1

theorem gl4Emb_B : gl4Emb gl4B = syl3Tb :=
  Units.ext gl4_facts.2.2.2.1

theorem gl4Emb_Al : gl4Emb gl4Al = ord3T4 := by
  rw [gl4Al, map_mul, gl4Emb_A, gl4Emb_B]
  exact Units.ext gl4_facts.2.2.2.2

theorem orderOf_gl4A : orderOf gl4A = 3 := by
  rw [← orderOf_injective gl4Emb gl4Emb_injective, gl4Emb_A, orderOf_ord3T2]

theorem orderOf_gl4Al : orderOf gl4Al = 3 := by
  rw [← orderOf_injective gl4Emb gl4Emb_injective, gl4Emb_Al, orderOf_ord3T4]

@[expose] def gl4P : Subgroup G42 :=
  syl3R.comap gl4Emb

theorem gl4_R_le_range : syl3R ≤ gl4Emb.range := by
  rw [syl3R]
  exact sup_le (Subgroup.zpowers_le.mpr ⟨gl4A, gl4Emb_A⟩)
    (Subgroup.zpowers_le.mpr ⟨gl4B, gl4Emb_B⟩)

theorem gl4_card_P : Nat.card gl4P = 9 := by
  rw [gl4P, gl4_card_comap gl4_R_le_range, syl3_card_R]

theorem gl4_mem_P {y : G42} (hy : y ∈ gl4P) : ∃ i < 3, ∃ j < 3, y = gl4A ^ i * gl4B ^ j := by
  obtain ⟨i, hi, j, hj, h⟩ := syl3_mem_R (Subgroup.mem_comap.mp hy)
  refine ⟨i, hi, j, hj, gl4Emb_injective ?_⟩
  rw [h, map_mul, map_pow, map_pow, gl4Emb_A, gl4Emb_B]

theorem gl4_P_isElementaryAbelian : IsElementaryAbelian 3 gl4P where
  is_comm := ⟨fun x y => Subtype.ext (gl4Emb_injective (by
    show gl4Emb ((x : G42) * y) = gl4Emb ((y : G42) * x)
    rw [map_mul, map_mul]
    exact syl3_R_comm _ x.2 _ y.2))⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (gl4Emb_injective (by
      show gl4Emb ((x : G42) ^ 3) = gl4Emb 1
      rw [map_pow, map_one]
      exact syl3_R_cube _ x.2))

theorem gl4_card_sylow (P : Sylow 3 G42) : Nat.card P = 9 := by
  have := card_sylow_of_card_eq_pow_mul (p := 3) (k := 2) (m := 2 ^ 6 * 5 * 7)
    (by rw [card_G42]; ring) (by norm_num) P
  rw [this]
  norm_num

set_option maxRecDepth 100000 in
theorem gl4_syl3DM_shape : ∀ x : DihedralGroup 4,
    syl3DM x *ᵥ Pi.single 4 1 = Pi.single 4 1 ∧ Pi.single 4 1 ᵥ* syl3DM x = Pi.single 4 1 := by
  decide +kernel

theorem gl4_N_le_range : Subgroup.normalizer (syl3R : Set G52) ≤ gl4Emb.range := by
  rw [← syl3_normalizer_eq]
  refine sup_le gl4_R_le_range ?_
  rintro _ ⟨x, rfl⟩
  exact mem_range_gl4Emb (gl4_syl3DM_shape x)

theorem gl4_card_normalizer_P : Nat.card (Subgroup.normalizer (gl4P : Set G42)) = 72 := by
  rw [gl4P, ← Subgroup.comap_normalizer_eq_of_le_range gl4_R_le_range,
    gl4_card_comap gl4_N_le_range, syl3_card_normalizer]

theorem gl4_syl3_structure (R : Sylow 3 G42) :
    Nat.card R = 9 ∧ IsElementaryAbelian 3 (R : Subgroup G42) ∧
    Nat.card (Subgroup.normalizer ((R : Subgroup G42) : Set G42)) = 72 := by
  obtain ⟨Q, hQ⟩ := exists_sylow_eq_of_card_pow (p := 3) (k := 2) (H := gl4P)
    (by rw [gl4_card_P]; norm_num) (fun P => by rw [gl4_card_sylow P]; norm_num)
  obtain ⟨c, hc⟩ := exists_eq_map_conj_sylow Q R
  rw [hQ] at hc
  refine ⟨gl4_card_sylow R, ?_, ?_⟩
  · rw [hc]
    exact gl4_P_isElementaryAbelian.subgroup_map _
  · rw [hc, normalizer_map_conj, Subgroup.card_map_of_injective (MulAut.conj c).injective,
      gl4_card_normalizer_P]

@[expose] def gl4S1M : M4 :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def gl4S2M : M4 :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

@[expose] def gl4SSM : M4 :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

@[expose] def gl4WM : M4 :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

@[expose] def gl4CM (i j : ℕ) : M4 :=
  if i = 0 then (if j = 2 then gl4S2M * gl4WM else if j = 1 then gl4WM else 1)
  else if i = 2 then (if j = 2 then gl4SSM else gl4S1M)
  else (if j = 2 then gl4S2M else 1)

@[expose] def gl4CMi (i j : ℕ) : M4 :=
  if i = 0 then (if j = 2 then gl4WM * gl4S2M else if j = 1 then gl4WM else 1)
  else if i = 2 then (if j = 2 then gl4SSM else gl4S1M)
  else (if j = 2 then gl4S2M else 1)

theorem gl4_conj_facts : ∀ i j : Fin 3, gl4CM i j * gl4CMi i j = 1 ∧
    ((i : ℕ) ≠ 0 → (j : ℕ) ≠ 0 →
      gl4CM i j * (gl4AM * gl4BM) * gl4CMi i j = gl4AM ^ (i : ℕ) * gl4BM ^ (j : ℕ)) ∧
    ((i : ℕ) = 0 ∨ (j : ℕ) = 0 → (i : ℕ) ≠ 0 ∨ (j : ℕ) ≠ 0 →
      gl4CM i j * gl4AM * gl4CMi i j = gl4AM ^ (i : ℕ) * gl4BM ^ (j : ℕ)) := by
  decide +kernel

theorem gl4_conj_P {i j : ℕ} (hi : i < 3) (hj : j < 3) (hij : i ≠ 0 ∨ j ≠ 0) :
    IsConj gl4A (gl4A ^ i * gl4B ^ j) ∨ IsConj gl4Al (gl4A ^ i * gl4B ^ j) := by
  obtain ⟨h1, h2, h3⟩ := gl4_conj_facts ⟨i, hi⟩ ⟨j, hj⟩
  have key : ∀ t : G42, gl4CM i j * (t : M4) * gl4CMi i j = gl4AM ^ i * gl4BM ^ j →
      IsConj t (gl4A ^ i * gl4B ^ j) := fun t ht =>
    isConj_iff.mpr ⟨mk4 (gl4CM i j) (gl4CMi i j) h1, Units.ext (by
      simp only [Units.val_mul, coe_mk4, coe_mk4_inv, Units.val_pow_eq_pow_val]
      rw [ht]
      rfl)⟩
  by_cases h : i = 0 ∨ j = 0
  · exact Or.inl (key gl4A (h3 h hij))
  · rw [not_or] at h
    exact Or.inr (key gl4Al (h2 h.1 h.2))

theorem gl4_ord3_classify {x : G42} (hx : orderOf x = 3) : IsConj gl4A x ∨ IsConj gl4Al x := by
  have hp : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨R, hR⟩ := hp.exists_le_sylow
  obtain ⟨Q, hQ⟩ := exists_sylow_eq_of_card_pow (p := 3) (k := 2) (H := gl4P)
    (by rw [gl4_card_P]; norm_num) (fun P => by rw [gl4_card_sylow P]; norm_num)
  obtain ⟨c, hc⟩ := exists_eq_map_conj_sylow Q R
  rw [hQ] at hc
  have hxR : x ∈ (R : Subgroup G42) := hR (Subgroup.mem_zpowers x)
  rw [hc] at hxR
  obtain ⟨y, hy, rfl⟩ := hxR
  obtain ⟨i, hi, j, hj, rfl⟩ := gl4_mem_P hy
  have hij : i ≠ 0 ∨ j ≠ 0 := by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [pow_zero, pow_zero, mul_one, map_one, orderOf_one] at hx
        exact absurd hx (by norm_num)
      · exact Or.inr hj0.ne'
    · exact Or.inl hi0.ne'
  have hconj : IsConj (gl4A ^ i * gl4B ^ j)
      ((MulAut.conj c).toMonoidHom (gl4A ^ i * gl4B ^ j)) :=
    isConj_iff.mpr ⟨c, rfl⟩
  rcases gl4_conj_P hi hj hij with h | h
  · exact Or.inl (h.trans hconj)
  · exact Or.inr (h.trans hconj)

theorem gl4_not_isConj_Al_A : ¬ IsConj gl4Al gl4A := fun h => by
  have := gl4Emb.map_isConj h
  rw [gl4Emb_Al, gl4Emb_A] at this
  exact ord3_not_isConj_T4_T2 this

theorem gl4_isConj_A_of {y : G42} (h : IsConj ord3T2 (gl4Emb y)) : IsConj gl4A y := by
  have hy : orderOf y = 3 := by
    obtain ⟨c, hc⟩ := isConj_iff.mp h
    rw [← orderOf_injective gl4Emb gl4Emb_injective, ← hc, ← MulAut.conj_apply,
      MulEquiv.orderOf_eq, orderOf_ord3T2]
  rcases gl4_ord3_classify hy with h' | h'
  · exact h'
  · have := gl4Emb.map_isConj h'
    rw [gl4Emb_Al] at this
    exact absurd (this.trans h.symm) ord3_not_isConj_T4_T2

theorem gl4_isConj_Al_of {y : G42} (h : IsConj ord3T4 (gl4Emb y)) : IsConj gl4Al y := by
  have hy : orderOf y = 3 := by
    obtain ⟨c, hc⟩ := isConj_iff.mp h
    rw [← orderOf_injective gl4Emb gl4Emb_injective, ← hc, ← MulAut.conj_apply,
      MulEquiv.orderOf_eq, orderOf_ord3T4]
  rcases gl4_ord3_classify hy with h' | h'
  · have := gl4Emb.map_isConj h'
    rw [gl4Emb_A] at this
    exact absurd (h.trans this.symm) ord3_not_isConj_T4_T2
  · exact h'

@[expose] def gl4K4 : Subgroup G42 :=
  ord3K4.comap gl4Emb

theorem gl4Shape_PhiM (A : Matrix (Fin 2) (Fin 2) F4) : gl4Shape (ord3PhiM A) := by
  constructor
  · rw [mulVec_single_one]
    ext i
    fin_cases i <;> simp [ord3PhiM]
  · rw [single_one_vecMul]
    ext j
    fin_cases j <;> simp [ord3PhiM]

theorem gl4_K4_le_range : ord3K4 ≤ gl4Emb.range := by
  rintro _ ⟨S, rfl⟩
  exact mem_range_gl4Emb (gl4Shape_PhiM _)

theorem gl4_K4_equiv : Nonempty (gl4K4 ≃* Matrix.SpecialLinearGroup (Fin 2) F4) := by
  obtain ⟨e4⟩ := ord3_K4_equiv
  obtain ⟨e⟩ := gl4_comap_equiv gl4_K4_le_range
  exact ⟨e.trans e4⟩

theorem gl4_centralizer_Al :
    IsInnerDirectProduct (Subgroup.zpowers gl4Al) gl4K4 (Subgroup.centralizer {gl4Al}) := by
  obtain ⟨hsup, hinf, hcomm⟩ := ord3_centralizer_T4
  have hz : (Subgroup.zpowers ord3T4).comap gl4Emb = Subgroup.zpowers gl4Al := by
    rw [← gl4Emb_Al, ← MonoidHom.map_zpowers gl4Emb gl4Al,
      Subgroup.comap_map_eq_self_of_injective gl4Emb_injective]
  have hzr : Subgroup.zpowers ord3T4 ≤ gl4Emb.range :=
    Subgroup.zpowers_le.mpr ⟨gl4Al, gl4Emb_Al⟩
  refine ⟨?_, ?_, fun a ha b hb => gl4Emb_injective ?_⟩
  · rw [← hz, gl4K4, Subgroup.comap_sup_eq_of_le_range gl4Emb hzr gl4_K4_le_range, hsup,
      ← gl4Emb_Al, gl4_comap_centralizer]
  · rw [← hz, gl4K4, ← Subgroup.comap_inf, hinf, MonoidHom.comap_bot,
      (MonoidHom.ker_eq_bot_iff _).mpr gl4Emb_injective]
  · rw [← hz] at ha
    rw [map_mul, map_mul]
    exact hcomm _ (Subgroup.mem_comap.mp ha) _ (Subgroup.mem_comap.mp hb)

theorem gl4_exists_Al_mem_K4 : ∃ y ∈ gl4K4, IsConj gl4Al y := by
  obtain ⟨y, hyK, -, hy⟩ := ord3_exists_T4_mem_K4
  obtain ⟨y', rfl⟩ := gl4_K4_le_range hyK
  exact ⟨y', hyK, gl4_isConj_Al_of hy⟩

@[expose] def gl4G0M : M5 :=
  !![1, 0, 0, 0, 1; 0, 1, 0, 0, 1; 0, 0, 1, 0, 1; 0, 0, 0, 1, 1; 1, 1, 1, 1, 1]

@[expose] def gl4G0iM : M5 :=
  !![0, 1, 1, 1, 1; 1, 0, 1, 1, 1; 1, 1, 0, 1, 1; 1, 1, 1, 0, 1; 1, 1, 1, 1, 1]

theorem gl4_G0_facts : gl4G0M * gl4G0iM = 1 ∧ gl4G0iM *ᵥ Pi.single 4 1 = 1 ∧
    Pi.single 4 1 ᵥ* gl4G0M = 1 ∧ gl4G0M *ᵥ 1 = Pi.single 4 1 ∧
    (1 : V5) ᵥ* gl4G0iM = Pi.single 4 1 := by
  decide +kernel

@[expose] def gl4G0 : G52 :=
  mk5 gl4G0M gl4G0iM gl4_G0_facts.1

theorem gl4Shape_conj_G0 {P : M5} (h1 : P *ᵥ 1 = 1) (h2 : (1 : V5) ᵥ* P = 1) :
    gl4Shape (gl4G0M * P * gl4G0iM) := by
  obtain ⟨-, f1, f2, f3, f4⟩ := gl4_G0_facts
  constructor
  · rw [← mulVec_mulVec, f1, ← mulVec_mulVec, h1, f3]
  · rw [← vecMul_vecMul, ← vecMul_vecMul, f2, h2, f4]

theorem gl4_permMatrix_mulVec (σ : Equiv.Perm (Fin 5)) :
    σ.permMatrix (ZMod 2) *ᵥ (1 : V5) = 1 := by
  rw [Matrix.permMatrix_mulVec]
  rfl

theorem gl4_vecMul_permMatrix (σ : Equiv.Perm (Fin 5)) :
    (1 : V5) ᵥ* σ.permMatrix (ZMod 2) = 1 := by
  rw [Matrix.vecMul_permMatrix]
  rfl

theorem gl4_K5_le_range : ord3K5.map (MulAut.conj gl4G0).toMonoidHom ≤ gl4Emb.range := by
  rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
  refine mem_range_gl4Emb ?_
  have e : (((MulAut.conj gl4G0).toMonoidHom (ord3P1Hom A) : G52) : M5) =
      gl4G0M * (ord3P1Perm A)⁻¹.permMatrix (ZMod 2) * gl4G0iM :=
    rfl
  rw [e]
  exact gl4Shape_conj_G0 (gl4_permMatrix_mulVec _) (gl4_vecMul_permMatrix _)

@[expose] def gl4K5 : Subgroup G42 :=
  (ord3K5.map (MulAut.conj gl4G0).toMonoidHom).comap gl4Emb

theorem gl4_K5_equiv : Nonempty (gl4K5 ≃* Matrix.SpecialLinearGroup (Fin 2) F4) := by
  obtain ⟨e5⟩ := ord3_K5_equiv
  obtain ⟨e⟩ := gl4_comap_equiv gl4_K5_le_range
  exact ⟨e.trans (((MulAut.conj gl4G0).subgroupMap ord3K5).symm.trans e5)⟩

theorem gl4_exists_A_mem_K5 : ∃ y ∈ gl4K5, IsConj gl4A y := by
  obtain ⟨y, hyK, -, hy⟩ := ord3_exists_T2_mem_K5
  have hm : (MulAut.conj gl4G0).toMonoidHom y ∈ ord3K5.map (MulAut.conj gl4G0).toMonoidHom :=
    ⟨y, hyK, rfl⟩
  obtain ⟨y', hy'⟩ := gl4_K5_le_range hm
  refine ⟨y', by rw [gl4K5, Subgroup.mem_comap, hy']; exact hm, gl4_isConj_A_of ?_⟩
  rw [hy']
  exact hy.trans (isConj_iff.mpr ⟨gl4G0, rfl⟩)

end CFSG.GroupTheory.GL52
