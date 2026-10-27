module

public import CFSG.GH74.SmallRanks.Basic
public import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

namespace L34Rank

theorem isPGroup_two_closure_pair {H : Type*} [Group H] {a b : H} (ha : a * a = 1) (hb : b * b = 1)
    (hab : (a * b) ^ 4 = 1) : IsPGroup 2 (Subgroup.closure ({a, b} : Set H)) := by
  set r : H := a * b with hr
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hri : r⁻¹ = r ^ 3 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hab)
  have hr3 : r ^ 3 = b * a := by rw [← hri, hr, mul_inv_rev, hai, hbi]
  have har : a * r = r ^ 3 * a := by
    rw [hr3, hr, ← mul_assoc, ha, one_mul, mul_assoc, ha, mul_one]
  have hapow : ∀ j : ℕ, a * r ^ j = r ^ (3 * j) * a := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, ← mul_assoc, ih, mul_assoc, har, ← mul_assoc, ← pow_add,
        show 3 * (j + 1) = 3 * j + 3 by ring]
  have hrinv : ∀ i : ℕ, (r ^ i)⁻¹ = r ^ (3 * i) := by
    intro i
    rw [← inv_pow, hri, ← pow_mul]
  let T : Subgroup H :=
    { carrier := {g | ∃ i : ℕ, g = r ^ i ∨ g = r ^ i * a}
      one_mem' := ⟨0, Or.inl (by simp)⟩
      mul_mem' := by
        rintro g h ⟨i, hi | hi⟩ ⟨j, hj | hj⟩
        · exact ⟨i + j, Or.inl (by rw [hi, hj, pow_add])⟩
        · exact ⟨i + j, Or.inr (by rw [hi, hj, pow_add, mul_assoc])⟩
        · refine ⟨i + 3 * j, Or.inr ?_⟩
          calc g * h = r ^ i * (a * r ^ j) := by rw [hi, hj]; simp only [mul_assoc]
            _ = r ^ i * (r ^ (3 * j) * a) := by rw [hapow]
            _ = r ^ (i + 3 * j) * a := by rw [pow_add]; simp only [mul_assoc]
        · refine ⟨i + 3 * j, Or.inl ?_⟩
          calc g * h = r ^ i * (a * r ^ j) * a := by rw [hi, hj]; simp only [mul_assoc]
            _ = r ^ i * (r ^ (3 * j) * a) * a := by rw [hapow]
            _ = r ^ (i + 3 * j) * (a * a) := by rw [pow_add]; simp only [mul_assoc]
            _ = r ^ (i + 3 * j) := by rw [ha, mul_one]
      inv_mem' := by
        rintro g ⟨i, hi | hi⟩
        · exact ⟨3 * i, Or.inl (by rw [hi, hrinv])⟩
        · exact ⟨3 * (3 * i), Or.inr (by rw [hi, mul_inv_rev, hai, hrinv, hapow])⟩ }
  have hsub : ({a, b} : Set H) ⊆ (T : Set H) := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · exact ⟨0, Or.inr (by rw [hg]; simp)⟩
    · exact ⟨3, Or.inr (by rw [hg, hr3, mul_assoc, ha, mul_one])⟩
  have hg4 : ∀ g ∈ T, g ^ 4 = 1 := by
    rintro g ⟨i, hi | hi⟩
    · rw [hi, ← pow_mul, mul_comm, pow_mul, hab, one_pow]
    · have h2 : g * g = 1 := by
        calc g * g = r ^ i * (a * r ^ i) * a := by rw [hi]; simp only [mul_assoc]
          _ = r ^ i * (r ^ (3 * i) * a) * a := by rw [hapow]
          _ = r ^ (i + 3 * i) * (a * a) := by rw [pow_add]; simp only [mul_assoc]
          _ = 1 := by
            rw [ha, mul_one, show i + 3 * i = 4 * i by ring, pow_mul, hab, one_pow]
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, h2, mul_one]
  have hclos : Subgroup.closure ({a, b} : Set H) ≤ T := (Subgroup.closure_le T).2 hsub
  intro g
  refine ⟨2, Subtype.ext ?_⟩
  have h4 := hg4 g.1 (hclos g.2)
  simpa using h4

theorem card_lt_two_pow_of_abelian {Q : Type*} [Group Q] [Finite Q] {a b : Q}
    (hD : IsPGroup 2 (Subgroup.closure ({a, b} : Set Q))) (hab : a * b ≠ b * a)
    {E : Subgroup Q} (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE2 : IsPGroup 2 E) :
    Nat.card E < 2 ^ (Nat.card Q).factorization 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hEP⟩ := hE2.exists_le_sylow
  obtain ⟨P', hDP'⟩ := hD.exists_le_sylow
  have hP : Nat.card P = 2 ^ (Nat.card Q).factorization 2 := P.card_eq_multiplicity
  by_contra hlt
  push Not at hlt
  have hle : Nat.card (P : Subgroup Q) ≤ Nat.card E := hP ▸ hlt
  have hEeq : E = P := Subgroup.eq_of_le_of_card_ge hEP hle
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q P P'
  have hmem : ∀ u ∈ (P' : Subgroup Q), ∃ s ∈ (P : Subgroup Q), u = g * s * g⁻¹ := by
    intro u hu
    rw [← hg, Sylow.coe_subgroup_smul] at hu
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_smul_pointwise_iff_exists _ _ _ |>.1 hu
    exact ⟨s, hs, by simp [MulAut.conj_apply]⟩
  have ha : a ∈ (P' : Subgroup Q) := hDP' (Subgroup.subset_closure (by simp))
  have hb : b ∈ (P' : Subgroup Q) := hDP' (Subgroup.subset_closure (by simp))
  obtain ⟨s, hs, hsa⟩ := hmem a ha
  obtain ⟨t, ht, htb⟩ := hmem b hb
  apply hab
  have hst := hEc s (hEeq ▸ hs) t (hEeq ▸ ht)
  rw [hsa, htb]
  calc g * s * g⁻¹ * (g * t * g⁻¹) = g * (s * t) * g⁻¹ := by group
    _ = g * (t * s) * g⁻¹ := by rw [hst]
    _ = g * t * g⁻¹ * (g * s * g⁻¹) := by group

section Matrices

open Matrix

variable {F : Type*} [Field F]

private def xM : Matrix (Fin 3) (Fin 3) F := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

private def yM : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 0, 1, 1; 0, 0, 1]

private def zM : Matrix (Fin 3) (Fin 3) F := !![1, 0, 1; 0, 1, 0; 0, 0, 1]

private theorem xM_mul_xM (h : (1 : F) + 1 = 0) : (xM * xM : Matrix (Fin 3) (Fin 3) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xM, Matrix.mul_apply, Fin.sum_univ_three, h]

private theorem yM_mul_yM (h : (1 : F) + 1 = 0) : (yM * yM : Matrix (Fin 3) (Fin 3) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [yM, Matrix.mul_apply, Fin.sum_univ_three, h]

private theorem zM_mul_zM (h : (1 : F) + 1 = 0) : (zM * zM : Matrix (Fin 3) (Fin 3) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zM, Matrix.mul_apply, Fin.sum_univ_three, h]

private theorem xyM_sq (h : (1 : F) + 1 = 0) :
    ((xM * yM) * (xM * yM) : Matrix (Fin 3) (Fin 3) F) = zM := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xM, yM, zM, Matrix.mul_apply, Fin.sum_univ_three, h]

private theorem yxM_sq (h : (1 : F) + 1 = 0) :
    ((yM * xM) * (yM * xM) : Matrix (Fin 3) (Fin 3) F) = zM := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xM, yM, zM, Matrix.mul_apply, Fin.sum_univ_three, h]

end Matrices

section SL

open Matrix Matrix.SpecialLinearGroup

variable {F : Type*} [Field F]

private theorem det_xM : (xM : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [xM, Matrix.det_fin_three]

private theorem det_yM : (yM : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [yM, Matrix.det_fin_three]

private theorem det_zM : (zM : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [zM, Matrix.det_fin_three]

private def xS : SpecialLinearGroup (Fin 3) F := ⟨xM, det_xM⟩

private def yS : SpecialLinearGroup (Fin 3) F := ⟨yM, det_yM⟩

private def zS : SpecialLinearGroup (Fin 3) F := ⟨zM, det_zM⟩

private theorem xS_mul_xS (h : (1 : F) + 1 = 0) :
    xS * xS = (1 : SpecialLinearGroup (Fin 3) F) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  exact xM_mul_xM h

private theorem yS_mul_yS (h : (1 : F) + 1 = 0) :
    yS * yS = (1 : SpecialLinearGroup (Fin 3) F) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  exact yM_mul_yM h

private theorem zS_mul_zS (h : (1 : F) + 1 = 0) :
    zS * zS = (1 : SpecialLinearGroup (Fin 3) F) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  exact zM_mul_zM h

private theorem xyS_sq (h : (1 : F) + 1 = 0) :
    (xS * yS) * (xS * yS) = (zS : SpecialLinearGroup (Fin 3) F) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  exact xyM_sq h

private theorem yxS_sq (h : (1 : F) + 1 = 0) :
    (yS * xS) * (yS * xS) = (zS : SpecialLinearGroup (Fin 3) F) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  exact yxM_sq h

private theorem xyS_pow_four (h : (1 : F) + 1 = 0) :
    (xS * yS) ^ 4 = (1 : SpecialLinearGroup (Fin 3) F) := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, xyS_sq h, zS_mul_zS h]

private theorem zS_not_mem_center :
    (zS : SpecialLinearGroup (Fin 3) F) ∉ Subgroup.center (SpecialLinearGroup (Fin 3) F) := by
  intro h
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 h
  have := congrFun (congrFun hr 0) 2
  simp [zS, zM] at this

private theorem eq_one_of_sq_eq_one_of_mem_center {z : SpecialLinearGroup (Fin 3) F}
    (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F)) (h2 : z ^ 2 = 1) : z = 1 := by
  obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  have h2' : ((z : Matrix (Fin 3) (Fin 3) F)) ^ 2 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, h2, Matrix.SpecialLinearGroup.coe_one]
  rw [← hr, ← map_pow] at h2'
  have hr2 : r ^ 2 = 1 := by
    have := congrFun (congrFun h2' 0) 0
    simpa [Matrix.scalar_apply] using this
  have hr1 : r = 1 := by
    have hr3' : r ^ 3 = 1 := by simpa using hr3
    calc r = r * r ^ 2 := by rw [hr2, mul_one]
      _ = r ^ 3 := by ring
      _ = 1 := hr3'
  apply Subtype.ext
  rw [← hr, hr1]
  simp

private theorem odd_card_center_sl3 [Finite F] :
    Odd (Nat.card (Subgroup.center (SpecialLinearGroup (Fin 3) F))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have h2 : 2 ∣ Nat.card (Subgroup.center (SpecialLinearGroup (Fin 3) F)) :=
    even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have h1 : z = 1 := by
    apply Subtype.ext
    exact eq_one_of_sq_eq_one_of_mem_center z.2 (by simpa using congrArg Subtype.val hz2)
  rw [h1, orderOf_one] at hz
  exact absurd hz (by norm_num)

private theorem card_sl3_four [Finite F] (hF : Nat.card F = 4) :
    Nat.card (SpecialLinearGroup (Fin 3) F) = 60480 := by
  haveI := Fintype.ofFinite F
  have hq : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card]; exact hF
  rw [Matrix.card_SL_field, hq, Fin.prod_univ_three]
  norm_num

end SL

theorem card_le_thirtyTwo_of_isElemAbelian_psl3 {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) (E : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F))
    (hE : IsElemAbelian 2 E) : Nat.card E ≤ 32 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h11 : (1 : F) + 1 = 0 := by
    haveI := Fintype.ofFinite F
    have h4 : ((Fintype.card F : ℕ) : F) = 0 := Nat.cast_card_eq_zero F
    have hq : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card]; exact hF
    rw [hq] at h4
    have h22 : (2 : F) * 2 = 0 := by
      have : ((4 : ℕ) : F) = (2 : F) * 2 := by norm_num
      rw [← this]; exact h4
    rw [one_add_one_eq_two]
    exact mul_self_eq_zero.1 h22
  set S := Matrix.SpecialLinearGroup (Fin 3) F with hSdef
  have hS : Nat.card S = 60480 := card_sl3_four hF
  have hZ : Odd (Nat.card (Subgroup.center S)) := odd_card_center_sl3
  have hcard : Nat.card S = Nat.card (S ⧸ Subgroup.center S) * Nat.card (Subgroup.center S) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hQ6 : (Nat.card (S ⧸ Subgroup.center S)).factorization 2 = 6 := by
    have hQ0 : Nat.card (S ⧸ Subgroup.center S) ≠ 0 := Nat.card_pos.ne'
    have hZ0 : Nat.card (Subgroup.center S) ≠ 0 := Nat.card_pos.ne'
    have h1 := congrArg (fun n => n.factorization 2) hcard
    simp only [Nat.factorization_mul hQ0 hZ0, Finsupp.add_apply] at h1
    have hZ2 : (Nat.card (Subgroup.center S)).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by
        intro hd
        exact (Nat.not_even_iff_odd.2 hZ) (even_iff_two_dvd.2 hd))
    have h60 : (60480 : ℕ).factorization 2 = 6 := by
      rw [show (60480 : ℕ) = 2 ^ 6 * 945 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
      simp
    rw [hS, h60, hZ2] at h1
    omega
  have hxx : (QuotientGroup.mk xS : S ⧸ Subgroup.center S) * QuotientGroup.mk xS = 1 := by
    rw [← QuotientGroup.mk_mul, xS_mul_xS h11]; rfl
  have hyy : (QuotientGroup.mk yS : S ⧸ Subgroup.center S) * QuotientGroup.mk yS = 1 := by
    rw [← QuotientGroup.mk_mul, yS_mul_yS h11]; rfl
  have hxy4 : ((QuotientGroup.mk xS : S ⧸ Subgroup.center S) * QuotientGroup.mk yS) ^ 4 = 1 := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, xyS_pow_four h11]; rfl
  have hne : (QuotientGroup.mk xS : S ⧸ Subgroup.center S) * QuotientGroup.mk yS ≠
      QuotientGroup.mk yS * QuotientGroup.mk xS := by
    intro h
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h
    have hinv : (xS * yS : S)⁻¹ = yS * xS := by
      apply inv_eq_of_mul_eq_one_right
      calc xS * yS * (yS * xS) = xS * (yS * yS) * xS := by simp only [mul_assoc]
        _ = 1 := by rw [yS_mul_yS h11, mul_one, xS_mul_xS h11]
    rw [hinv, yxS_sq h11] at h
    exact zS_not_mem_center h
  have hD := isPGroup_two_closure_pair hxx hyy hxy4
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hE2 : IsPGroup 2 E := CFSG.GH74.SmallRanks.isPGroup_two_of_isElemAbelian hE
  have hlt := card_lt_two_pow_of_abelian hD hne hEc hE2
  rw [hQ6] at hlt
  obtain ⟨k, hk⟩ := hE2.exists_card_eq
  rw [hk] at hlt ⊢
  have hk6 : k < 6 := by
    by_contra h
    push Not at h
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h
    omega
  calc 2 ^ k ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 32 := by norm_num

end L34Rank

theorem twoRank_lt_six_of_odd_center_quotient {J : Type} [Group J] [Finite J]
    (hZ : Odd (Nat.card (Subgroup.center J)))
    (hS : ∀ F : Subgroup (J ⧸ Subgroup.center J), IsElemAbelian 2 F → Nat.card F ≤ 32) :
    twoRank J < 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr : twoRank J ≤ 5 := by
    show CFSG.Open.pRank 2 (⊤ : Subgroup J) ≤ 5
    refine CFSG.SectionRank.pRank_le Nat.one_lt_two (k := 5) (fun E _ hE => ?_)
    have hP : IsPGroup 2 E := CFSG.GH74.SmallRanks.isPGroup_two_of_isElemAbelian hE
    obtain ⟨kE, hkE⟩ := hP.exists_card_eq
    set φ : E →* J ⧸ Subgroup.center J :=
      (QuotientGroup.mk' (Subgroup.center J)).comp E.subtype with hφ
    have hcard := Subgroup.card_ker_mul_card_range φ
    have hF : Nat.card φ.range ≤ 32 := by
      apply hS
      have hEE : IsElemAbelian 2 (⊤ : Subgroup E) := by
        refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y _ => ?_⟩
        · exact Subtype.ext (hE.1.is_comm.comm a.1 b.1)
        · exact Subtype.ext (by simpa using hE.2 _ y.2)
      rw [MonoidHom.range_eq_map]
      exact CFSG.SectionRank.isElemAbelian_map hEE φ
    have hK1 : Nat.card φ.ker = 1 := by
      have hd : Nat.card φ.ker ∣ 2 ^ kE := by
        rw [← hkE]
        exact Subgroup.card_subgroup_dvd_card φ.ker
      have hKz : φ.ker.map E.subtype ≤ Subgroup.center J := by
        intro x hx
        obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hx
        have hk1 : (QuotientGroup.mk (k : J) : J ⧸ Subgroup.center J) = 1 := by
          have := MonoidHom.mem_ker.1 hk
          exact this
        exact QuotientGroup.eq_one_iff _ |>.1 hk1
      have hmap : Nat.card (φ.ker.map E.subtype) = Nat.card φ.ker :=
        Subgroup.card_map_of_injective E.subtype_injective
      have hdz : Nat.card φ.ker ∣ Nat.card (Subgroup.center J) := by
        rw [← hmap]
        exact Subgroup.card_dvd_of_le hKz
      have hcop : Nat.Coprime (2 ^ kE) (Nat.card (Subgroup.center J)) :=
        Nat.Coprime.pow_left kE (Nat.coprime_two_left.2 hZ)
      exact (Nat.Coprime.coprime_dvd_left hd hcop).eq_one_of_dvd hdz
    have hE32 : Nat.card E ≤ 2 ^ 5 := by
      rw [← hcard, hK1, one_mul]
      exact hF
    exact hE32
  exact lt_of_le_of_lt hr (by norm_num)

theorem twoRank_lt_six_of_A_two_four {J : Type} [Group J] [Finite J]
    (hZ : Odd (Nat.card (Subgroup.center J))) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A 2 q).Valid) (hq : q.card = 4)
    (e : J ⧸ Subgroup.center J ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A 2 q, hv⟩) :
    twoRank J < 6 := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  let φ : J ⧸ Subgroup.center J ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField q.p q.exponent) :=
    e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)
  have hF : Nat.card (GaloisField q.p q.exponent) = 4 := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', ← TauCeti.PrimePower.card_def, hq]
  refine twoRank_lt_six_of_odd_center_quotient hZ (fun F hF' => ?_)
  have h1 := L34Rank.card_le_thirtyTwo_of_isElemAbelian_psl3 hF (F.map φ.toMonoidHom)
    (CFSG.SectionRank.isElemAbelian_map hF' φ.toMonoidHom)
  have h2 : Nat.card (F.map φ.toMonoidHom) = Nat.card F :=
    Subgroup.card_map_of_injective φ.injective
  omega

end CFSG.LocalAnalysis.GLTheoremA

end
