module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Defs
public import CFSG.RankThree.PGroups.MaximalNormalElementaryCentralizer
public import CFSG.Sporadic.Schreier.RuElemAut
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open scoped Pointwise

namespace Input319

def Nexp (k : ℕ) : ℕ := ∑ i : Fin k, (i : ℕ)

theorem Nexp_mul_two (k : ℕ) : Nexp k * 2 = k * (k - 1) := by
  unfold Nexp
  rw [Fin.sum_univ_eq_sum_range (fun i => i) k, Finset.sum_range_id_mul_two]

theorem lower_aux {p : ℕ} (hp3 : 3 ≤ p) :
    ∀ m : ℕ, 2 ≤ m → (m + 1) * (m + 2) < 2 * p ^ m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => nlinarith
  | succ m hm ih =>
    rw [pow_succ]
    nlinarith [Nat.mul_le_mul_left (p ^ m) hp3]

theorem upper_aux {p : ℕ} (hp3 : 3 ≤ p) :
    ∀ m : ℕ, 2 ≤ m → (m + 1) * (m + 4) ≤ 2 * p ^ m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => nlinarith
  | succ m hm ih =>
    rw [pow_succ]
    nlinarith [Nat.mul_le_mul_left (p ^ m) hp3]

theorem arith_lower {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : 2 ≤ r)
    (hnot : ¬ (p = 3 ∧ r = 2)) : r + Nexp r < p ^ (r - 1) := by
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  have hN := Nexp_mul_two (m + 1)
  simp only [Nat.add_sub_cancel] at hN ⊢
  rcases Nat.lt_or_ge m 2 with hm | hm
  · have hm1 : m = 1 := by omega
    subst hm1
    have hp5 : 5 ≤ p := by
      have hp3' : p ≠ 3 := fun h => hnot ⟨h, rfl⟩
      have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
      omega
    have hN' : Nexp 2 = 1 := by unfold Nexp; simp [Fin.sum_univ_two]
    have : Nexp (1 + 1) = 1 := hN'
    simp only [pow_one] at *
    omega
  · have hl := lower_aux h3 m hm
    have key : 2 * (m + 1 + Nexp (m + 1)) < 2 * p ^ m := by
      nlinarith [hN, hl]
    omega

theorem arith_upper {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : 2 ≤ r)
    (hnot : ¬ (p = 3 ∧ r = 2)) : r + Nexp (r + 1) ≤ p ^ (r - 1) := by
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  have hN := Nexp_mul_two (m + 1 + 1)
  simp only [Nat.add_sub_cancel] at hN ⊢
  rcases Nat.lt_or_ge m 2 with hm | hm
  · have hm1 : m = 1 := by omega
    subst hm1
    have hp5 : 5 ≤ p := by
      have hp3' : p ≠ 3 := fun h => hnot ⟨h, rfl⟩
      have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
      omega
    have hN' : Nexp 3 = 3 := by unfold Nexp; simp [Fin.sum_univ_succ]
    simp only [pow_one]
    omega
  · have hu := upper_aux h3 m hm
    have key : 2 * (m + 1 + Nexp (m + 1 + 1)) ≤ 2 * p ^ m := by
      nlinarith [hN, hu]
    omega


theorem gl_card_factor (p k : ℕ) [hp : Fact p.Prime] :
    ∃ M : ℕ, Nat.card (Matrix.GeneralLinearGroup (Fin k) (ZMod p)) = p ^ Nexp k * M ∧ ¬ p ∣ M := by
  refine ⟨∏ i : Fin k, (p ^ (k - (i : ℕ)) - 1), ?_, ?_⟩
  · rw [Matrix.card_GL_field, ZMod.card]
    unfold Nexp
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    have hi : (i : ℕ) ≤ k := by have := i.2; omega
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_of_le hi]
  · intro h
    obtain ⟨i, _, hi⟩ := (Prime.dvd_finset_prod_iff hp.out.prime _).1 h
    have hik : (i : ℕ) < k := i.2
    have h1 : p ∣ p ^ (k - (i : ℕ)) := dvd_pow_self p (by omega)
    have h2 : p ∣ p ^ (k - (i : ℕ)) - (p ^ (k - (i : ℕ)) - 1) := Nat.dvd_sub h1 hi
    have h3 : p ^ (k - (i : ℕ)) - (p ^ (k - (i : ℕ)) - 1) = 1 := by
      have := Nat.one_le_pow (k - (i : ℕ)) p hp.out.pos
      omega
    rw [h3] at h2
    exact hp.out.one_lt.ne' (Nat.dvd_one.1 h2)

theorem gl_pSub_card_le (p k : ℕ) [hp : Fact p.Prime]
    {Q : Subgroup (Matrix.GeneralLinearGroup (Fin k) (ZMod p))} (hQ : IsPGroup p Q) :
    Nat.card Q ≤ p ^ Nexp k := by
  obtain ⟨M, hM, hpM⟩ := gl_card_factor p k
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hQ
  have hidx := Subgroup.index_mul_card (H := Q)
  rw [hM, hj] at hidx
  have hdvd : p ^ j ∣ p ^ Nexp k * M := ⟨Q.index, by rw [← hidx, mul_comm]⟩
  have hcop : Nat.Coprime (p ^ j) M :=
    Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpM)
  have h2 : p ^ j ∣ p ^ Nexp k := hcop.dvd_of_dvd_mul_right hdvd
  have hj' : j ≤ Nexp k := (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).1 h2
  rw [hj]
  exact Nat.pow_le_pow_right hp.out.pos hj'

def IsUT {p k : ℕ} (M : Matrix (Fin k) (Fin k) (ZMod p)) : Prop :=
  (∀ i j : Fin k, j < i → M i j = 0) ∧ ∀ i : Fin k, M i i = 1

theorem isUT_one {p k : ℕ} : IsUT (1 : Matrix (Fin k) (Fin k) (ZMod p)) :=
  ⟨fun i j h => Matrix.one_apply_ne h.ne', fun i => by simp⟩

theorem isUT_mul {p k : ℕ} {M N : Matrix (Fin k) (Fin k) (ZMod p)} (hM : IsUT M) (hN : IsUT N) :
    IsUT (M * N) := by
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hjl : j < l
    · rw [hN.1 l j hjl, mul_zero]
    · have hli : l < i := lt_of_le_of_lt (not_lt.1 hjl) hji
      rw [hM.1 i l hli, zero_mul]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hM.2 i, hN.2 i, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hM.1 i l h, zero_mul]
      · rw [hN.1 l i h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h

theorem isUT_isUnit_det {p k : ℕ} {M : Matrix (Fin k) (Fin k) (ZMod p)} (hM : IsUT M) :
    IsUnit M.det := by
  rw [Matrix.det_of_upperTriangular (by intro i j h; exact hM.1 i j h)]
  simp [hM.2]

def unitriSub (p k : ℕ) [Fact p.Prime] :
    Subgroup (Matrix.GeneralLinearGroup (Fin k) (ZMod p)) where
  carrier := {g | IsUT (g : Matrix (Fin k) (Fin k) (ZMod p))}
  mul_mem' := fun {g h} hg hh => by
    show IsUT ((g : Matrix (Fin k) (Fin k) (ZMod p)) * (h : Matrix (Fin k) (Fin k) (ZMod p)))
    exact isUT_mul hg hh
  one_mem' := by
    show IsUT ((1 : Matrix.GeneralLinearGroup (Fin k) (ZMod p)) : Matrix (Fin k) (Fin k) (ZMod p))
    simpa using (isUT_one : IsUT (1 : Matrix (Fin k) (Fin k) (ZMod p)))
  inv_mem' := fun {g} hg => by
    have hpow : ∀ n : ℕ, IsUT ((g ^ n : Matrix.GeneralLinearGroup (Fin k) (ZMod p)) :
        Matrix (Fin k) (Fin k) (ZMod p)) := by
      intro n
      induction n with
      | zero => simpa using (isUT_one : IsUT (1 : Matrix (Fin k) (Fin k) (ZMod p)))
      | succ n ih =>
        rw [pow_succ, Units.val_mul]
        exact isUT_mul ih hg
    have hinv : g⁻¹ = g ^ (orderOf g - 1) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos g),
        pow_orderOf_eq_one]
    show IsUT ((g⁻¹ : Matrix.GeneralLinearGroup (Fin k) (ZMod p)) :
        Matrix (Fin k) (Fin k) (ZMod p))
    rw [hinv]
    exact hpow _

abbrev PairsLT (k : ℕ) : Type := {ij : Fin k × Fin k // ij.1 < ij.2}

theorem card_pairsLT (k : ℕ) : Nat.card (PairsLT k) = Nexp k := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    Fintype.sum_prod_type]
  have hinner : ∀ a : Fin k, (∑ b : Fin k, if a < b then 1 else 0) = k - 1 - (a : ℕ) := by
    intro a
    rw [Finset.sum_boole]
    have hset : (Finset.univ.filter (fun b : Fin k => a < b)) = Finset.Ioi a := by
      ext b; simp
    rw [hset, Fin.card_Ioi, Nat.cast_id]
  simp only [hinner]
  unfold Nexp
  rw [Fin.sum_univ_eq_sum_range (fun i => k - 1 - i) k, Fin.sum_univ_eq_sum_range (fun i => i) k]
  exact Finset.sum_range_reflect (fun i => i) k

theorem card_unitriSub (p k : ℕ) [hp : Fact p.Prime] :
    Nat.card (unitriSub p k) = p ^ Nexp k := by
  classical
  let f : unitriSub p k → (PairsLT k → ZMod p) := fun g t =>
    ((g : Matrix.GeneralLinearGroup (Fin k) (ZMod p)) : Matrix (Fin k) (Fin k) (ZMod p))
      t.1.1 t.1.2
  have hf : Function.Bijective f := by
    constructor
    · intro g h hgh
      apply Subtype.ext
      apply Units.ext
      ext i j
      have hg : IsUT ((g : Matrix.GeneralLinearGroup (Fin k) (ZMod p)) :
          Matrix (Fin k) (Fin k) (ZMod p)) := g.2
      have hh : IsUT ((h : Matrix.GeneralLinearGroup (Fin k) (ZMod p)) :
          Matrix (Fin k) (Fin k) (ZMod p)) := h.2
      rcases lt_trichotomy i j with hij | hij | hij
      · exact congrFun hgh ⟨(i, j), hij⟩
      · subst hij
        rw [hg.2 i, hh.2 i]
      · rw [hg.1 i j hij, hh.1 i j hij]
    · intro φ
      let M : Matrix (Fin k) (Fin k) (ZMod p) := fun i j =>
        if hij : i < j then φ ⟨(i, j), hij⟩ else if i = j then 1 else 0
      have hM : IsUT M := by
        refine ⟨fun i j hji => ?_, fun i => ?_⟩
        · simp only [M]
          rw [dif_neg (not_lt.2 hji.le), if_neg hji.ne']
        · simp [M]
      refine ⟨⟨Matrix.GeneralLinearGroup.mk'' M (isUT_isUnit_det hM), hM⟩, ?_⟩
      funext t
      show M t.1.1 t.1.2 = φ t
      simp only [M, dif_pos t.2]
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_fun, Nat.card_zmod, card_pairsLT]


theorem elem_isUT {p k : ℕ} {i j : Fin k} (hij : i < j) :
    IsUT (1 + Matrix.single i j (1 : ZMod p)) := by
  refine ⟨fun a b hba => ?_, fun a => ?_⟩
  · rw [Matrix.add_apply, Matrix.one_apply_ne hba.ne', zero_add, Matrix.single_apply, if_neg]
    rintro ⟨h1, h2⟩
    rw [← h1, ← h2] at hba
    exact lt_asymm hij hba
  · rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply, if_neg, add_zero]
    rintro ⟨h1, h2⟩
    rw [← h1] at h2
    exact hij.ne h2.symm

theorem unitriSub_nonabelian (p k : ℕ) [hp : Fact p.Prime] (hk : 3 ≤ k) :
    ∃ a ∈ unitriSub p k, ∃ b ∈ unitriSub p k, a * b ≠ b * a := by
  let i0 : Fin k := ⟨0, by omega⟩
  let i1 : Fin k := ⟨1, by omega⟩
  let i2 : Fin k := ⟨2, by omega⟩
  have h01 : i0 < i1 := by simp [i0, i1, Fin.lt_def]
  have h12 : i1 < i2 := by simp [i1, i2, Fin.lt_def]
  let a : Matrix.GeneralLinearGroup (Fin k) (ZMod p) :=
    Matrix.GeneralLinearGroup.mk'' _ (isUT_isUnit_det (elem_isUT (p := p) h01))
  let b : Matrix.GeneralLinearGroup (Fin k) (ZMod p) :=
    Matrix.GeneralLinearGroup.mk'' _ (isUT_isUnit_det (elem_isUT (p := p) h12))
  have ha : a ∈ unitriSub p k := elem_isUT (p := p) h01
  have hb : b ∈ unitriSub p k := elem_isUT (p := p) h12
  refine ⟨a, ha, b, hb, ?_⟩
  intro hab
  have hmat : (1 + Matrix.single i0 i1 (1 : ZMod p)) * (1 + Matrix.single i1 i2 (1 : ZMod p)) =
      (1 + Matrix.single i1 i2 (1 : ZMod p)) * (1 + Matrix.single i0 i1 (1 : ZMod p)) :=
    congrArg Units.val hab
  have e1 : (1 + Matrix.single i0 i1 (1 : ZMod p)) * (1 + Matrix.single i1 i2 (1 : ZMod p)) =
      1 + Matrix.single i1 i2 (1 : ZMod p) + Matrix.single i0 i1 (1 : ZMod p) +
        Matrix.single i0 i2 (1 : ZMod p) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one,
      Matrix.single_mul_single_same, mul_one]
    abel
  have e2 : (1 + Matrix.single i1 i2 (1 : ZMod p)) * (1 + Matrix.single i0 i1 (1 : ZMod p)) =
      1 + Matrix.single i1 i2 (1 : ZMod p) + Matrix.single i0 i1 (1 : ZMod p) := by
    have h20 : i2 ≠ i0 := by
      intro h
      have := congrArg Fin.val h
      simp [i0, i2] at this
    have hz : Matrix.single i1 i2 (1 : ZMod p) * Matrix.single i0 i1 (1 : ZMod p) = 0 :=
      Matrix.single_mul_single_of_ne _ i1 i2 i0 h20 _
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, hz, add_zero]
  rw [e1, e2] at hmat
  have hent := congrFun (congrFun hmat i0) i2
  have hne : i0 ≠ i2 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i2] at this
  simp [Matrix.add_apply, Matrix.single_apply, hne, hne.symm] at hent

theorem gl_elemAb_card_le (p k : ℕ) [hp : Fact p.Prime] (hk : 3 ≤ k)
    {Q : Subgroup (Matrix.GeneralLinearGroup (Fin k) (ZMod p))} (hQ : IsElemAbelian p Q) :
    Nat.card Q ≤ p ^ (Nexp k - 1) := by
  classical
  haveI : Finite (Sylow p (Matrix.GeneralLinearGroup (Fin k) (ZMod p))) :=
    Finite.of_injective (fun P : Sylow p (Matrix.GeneralLinearGroup (Fin k) (ZMod p)) =>
      (P : Set (Matrix.GeneralLinearGroup (Fin k) (ZMod p))))
      (fun _ _ h => SetLike.coe_injective h)
  have hQp : IsPGroup p Q := CFSG.Open.IsElemAbelian.isPGroup hQ
  have hle := gl_pSub_card_le p k hQp
  obtain ⟨M, hM, hpM⟩ := gl_card_factor p k
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hQp
  have hjN : j ≤ Nexp k := by
    rw [hj] at hle
    exact (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hle
  rcases Nat.lt_or_ge j (Nexp k) with hlt | hge
  · rw [hj]
    exact Nat.pow_le_pow_right hp.out.pos (by omega)
  · exfalso
    have hjN' : j = Nexp k := le_antisymm hjN hge
    have hidx : Q.index = M := by
      have h := Subgroup.index_mul_card (H := Q)
      rw [hM, hj, hjN'] at h
      apply Nat.eq_of_mul_eq_mul_right (pow_pos hp.out.pos (Nexp k))
      rw [h, mul_comm]
    have hUcard : Nat.card (unitriSub p k) = p ^ Nexp k := card_unitriSub p k
    have hUidx : (unitriSub p k).index = M := by
      have h := Subgroup.index_mul_card (H := unitriSub p k)
      rw [hM, hUcard] at h
      apply Nat.eq_of_mul_eq_mul_right (pow_pos hp.out.pos (Nexp k))
      rw [h, mul_comm]
    have hQi : ¬ p ∣ Q.index := by rw [hidx]; exact hpM
    have hUi : ¬ p ∣ (unitriSub p k).index := by rw [hUidx]; exact hpM
    have hU : IsPGroup p (unitriSub p k) := IsPGroup.of_card hUcard
    let Qs := hQp.toSylow hQi
    let Us := hU.toSylow hUi
    have htrans : MulAction.IsPretransitive (Matrix.GeneralLinearGroup (Fin k) (ZMod p))
        (Sylow p (Matrix.GeneralLinearGroup (Fin k) (ZMod p))) := inferInstance
    obtain ⟨g, hg⟩ := htrans.exists_smul_eq Qs Us
    have hset : (Us : Set (Matrix.GeneralLinearGroup (Fin k) (ZMod p))) =
        MulAut.conj g • (Qs : Set (Matrix.GeneralLinearGroup (Fin k) (ZMod p))) := by
      rw [← hg, Sylow.coe_smul]
    have hsub : ∀ u ∈ unitriSub p k, ∃ x ∈ Q, g * x * g⁻¹ = u := by
      intro u hu
      have hu' : u ∈ MulAut.conj g • (Qs : Set (Matrix.GeneralLinearGroup (Fin k) (ZMod p))) := by
        rw [← hset]
        exact hu
      obtain ⟨x, hx, hxu⟩ := hu'
      exact ⟨x, hx, by simpa [MulAut.conj_apply] using hxu⟩
    obtain ⟨a, ha, b, hb, hab⟩ := unitriSub_nonabelian p k hk
    obtain ⟨x, hx, rfl⟩ := hsub a ha
    obtain ⟨y, hy, rfl⟩ := hsub b hb
    apply hab
    have hxy : x * y = y * x := by
      haveI : IsMulCommutative Q := hQ.1
      have := congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : Q) ⟨y, hy⟩)
      simpa using this
    calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
      _ = g * (y * x) * g⁻¹ := by rw [hxy]
      _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group


section Transport

variable {G : Type*} [Group G]

def conjAct (A E : Subgroup G) (hnorm : ∀ a ∈ A, ∀ e ∈ E, a * e * a⁻¹ ∈ E) : A →* MulAut E where
  toFun a :=
    { toFun := fun e => ⟨(a : G) * e * (a : G)⁻¹, hnorm a a.2 e e.2⟩
      invFun := fun e => ⟨(a : G)⁻¹ * e * (a : G), by
        have h := hnorm (a⁻¹ : A) (A.inv_mem a.2) e e.2
        simpa [mul_assoc] using h⟩
      left_inv := fun e => Subtype.ext (by simp [mul_assoc])
      right_inv := fun e => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun e f => Subtype.ext (by simp [mul_assoc]) }
  map_one' := MulEquiv.ext fun e => Subtype.ext (by simp)
  map_mul' := fun a b => MulEquiv.ext fun e => Subtype.ext (by simp [mul_assoc])

variable [Finite G]

theorem transport {p k : ℕ} [hp : Fact p.Prime] {A E : Subgroup G}
    (hA : IsElemAbelian p A) (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ k)
    (hnorm : ∀ a ∈ A, ∀ e ∈ E, a * e * a⁻¹ ∈ E) :
    ∃ ψ : A →* Matrix.GeneralLinearGroup (Fin k) (ZMod p),
      (∀ a : A, ψ a = 1 ↔ ∀ e ∈ E, (a : G) * e = e * (a : G)) ∧
      IsElemAbelian p ψ.range ∧
      Nat.card A = Nat.card ψ.ker * Nat.card ψ.range := by
  classical
  haveI : IsMulCommutative E := hE.1
  have hcomm : ∀ a b : E, a * b = b * a := fun a b => mul_comm' a b
  have hpow : ∀ a : E, a ^ p = 1 := fun a => Subtype.ext (by simpa using hE.2 a a.2)
  obtain ⟨φ⟩ :=
    CFSG.Sporadic.RuSchreier.ru_nonempty_mulEquiv_of_elementary (p := p) hcomm hpow hEc
  let c : A →* Matrix.GeneralLinearGroup (Fin k) (ZMod p) :=
    (CFSG.Sporadic.RuSchreier.ruMulAutEquivGL (p := p) k).toMonoidHom.comp
      ((MulAut.congr φ).toMonoidHom.comp (conjAct A E hnorm))
  have hcA : ∀ a : A, conjAct A E hnorm a = 1 ↔ ∀ e ∈ E, (a : G) * e = e * (a : G) := by
    intro a
    constructor
    · intro h e he
      have h' := congrArg (fun f : MulAut E => ((f ⟨e, he⟩ : E) : G)) h
      simp only [MulAut.one_apply] at h'
      change (a : G) * e * (a : G)⁻¹ = e at h'
      rw [mul_inv_eq_iff_eq_mul] at h'
      exact h'
    · intro h
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      have hx := h x.1 x.2
      change (a : G) * x.1 * (a : G)⁻¹ = x.1
      rw [mul_inv_eq_iff_eq_mul, hx]
  have hc : ∀ a : A, c a = 1 ↔ ∀ e ∈ E, (a : G) * e = e * (a : G) := by
    intro a
    rw [← hcA a]
    change (CFSG.Sporadic.RuSchreier.ruMulAutEquivGL (p := p) k)
        ((MulAut.congr φ) (conjAct A E hnorm a)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff]
  refine ⟨c, hc, ?_, ?_⟩
  · haveI : IsMulCommutative A := hA.1
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, ha⟩ := x.2
      obtain ⟨b, hb⟩ := y.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm' a b]
    · obtain ⟨a, ha⟩ := hx
      have hapow : a ^ p = 1 := Subtype.ext (by simpa using hA.2 a a.2)
      rw [← ha, ← map_pow, hapow, map_one]
  · have h1 := Subgroup.card_mul_index c.ker
    have h2 : c.ker.index = Nat.card c.range := by
      rw [Subgroup.index]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivRange c).toEquiv
    rw [← h1, h2]

end Transport


def NormIn {G : Type} [Group G] (R B : Subgroup G) : Prop := ∀ g ∈ R, ∀ x ∈ B, g * x * g⁻¹ ∈ B

section RLevel

variable {G : Type} [Group G] [Finite G]

theorem exists_max_normal_ea (R : Subgroup G) (p : ℕ) :
    ∃ E0 : Subgroup G, E0 ≤ R ∧ NormIn R E0 ∧ IsElemAbelian p E0 ∧
      ∀ B : Subgroup G, B ≤ R → NormIn R B → IsElemAbelian p B → Nat.card B ≤ Nat.card E0 := by
  classical
  let S : Set (Subgroup G) := {B | B ≤ R ∧ NormIn R B ∧ IsElemAbelian p B}
  have hS : S.Nonempty := ⟨⊥, bot_le, fun g _ x hx => by
      rw [Subgroup.mem_bot.1 hx]; simp, isElemAbelian_bot p⟩
  obtain ⟨E0, hE0S, hmax⟩ := Set.exists_max_image S (fun B : Subgroup G => Nat.card B) (Set.toFinite S) hS
  exact ⟨E0, hE0S.1, hE0S.2.1, hE0S.2.2, fun B hBR hBn hBa => hmax B ⟨hBR, hBn, hBa⟩⟩

theorem star_of_maxNormal {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (R : Subgroup G)
    (hR : IsPGroup p R) (E0 : Subgroup G) (hE0R : E0 ≤ R) (hnorm : NormIn R E0)
    (hE0 : IsElemAbelian p E0)
    (hmax : ∀ B : Subgroup G, B ≤ R → NormIn R B → IsElemAbelian p B → Nat.card B ≤ Nat.card E0) :
    ∀ a ∈ R, a ^ p = 1 → (∀ e ∈ E0, a * e = e * a) → a ∈ E0 := by
  classical
  let E' : Subgroup R := E0.subgroupOf R
  haveI hEn : E'.Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hnorm g.1 g.2 x.1 hx⟩
  have hE'el : CFSG.IsElementaryAbelian p E' :=
    CFSG.Open.IsElemAbelian.isElementaryAbelian (CFSG.Open.IsElemAbelian.subgroupOf hE0 R)
  have hmax' : ∀ B : Subgroup R, B.Normal → CFSG.IsElementaryAbelian p B → E' ≤ B → B = E' := by
    intro B hBn hBel hle
    have hBa : IsElemAbelian p B := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.2 hBel
    let B' : Subgroup G := B.map R.subtype
    have hB'R : B' ≤ R := Subgroup.map_subtype_le B
    have hB'n : NormIn R B' := by
      intro g hg x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      refine Subgroup.mem_map.2 ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, hBn.conj_mem y hy _, ?_⟩
      simp
    have hB'a : IsElemAbelian p B' := CFSG.Open.IsElemAbelian.map hBa R.subtype
    have hE0B' : E0 ≤ B' := by
      intro x hx
      have hxR : x ∈ R := hE0R hx
      have hmemE' : (⟨x, hxR⟩ : R) ∈ E' := Subgroup.mem_subgroupOf.2 hx
      exact Subgroup.mem_map.2 ⟨⟨x, hxR⟩, hle hmemE', rfl⟩
    have hcard := hmax B' hB'R hB'n hB'a
    have heq : E0 = B' := Subgroup.eq_of_le_of_card_ge hE0B' hcard
    apply le_antisymm ?_ hle
    intro y hy
    have hyB' : (y : G) ∈ B' := Subgroup.mem_map.2 ⟨y, hy, rfl⟩
    rw [← heq] at hyB'
    exact Subgroup.mem_subgroupOf.2 hyB'
  have hx := (CFSG.RankThree.PGroups.maximal_normal_elementary_centralizer_torsion hp.out hp2 hR
    hE'el hmax').2
  intro a ha hap hcomm
  have hxmem : (⟨a, ha⟩ : R) ∈ Subgroup.centralizer (E' : Set R) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hh' : (h : G) ∈ E0 := Subgroup.mem_subgroupOf.1 hh
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact (hcomm h hh').symm
  have hxp : (⟨a, ha⟩ : R) ^ p = 1 := Subtype.ext (by simpa using hap)
  exact Subgroup.mem_subgroupOf.1 (hx ⟨a, ha⟩ hxmem hxp)

theorem exists_normal_rank {p : ℕ} [hp : Fact p.Prime] (R : Subgroup G) (hR : IsPGroup p R)
    (E0 : Subgroup G) (hE0R : E0 ≤ R) (hnorm : NormIn R E0) (hE0 : IsElemAbelian p E0)
    {n k : ℕ} (hn : Nat.card E0 = p ^ n) (hk : k ≤ n) :
    ∃ E : Subgroup G, E ≤ R ∧ NormIn R E ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k := by
  classical
  haveI : Fact (IsPGroup p R) := ⟨hR⟩
  let N : Subgroup R := E0.subgroupOf R
  haveI hN : N.Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hnorm g.1 g.2 x.1 hx⟩
  have hNc : Nat.card N = p ^ n := by
    rw [← hn]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE0R).toEquiv
  obtain ⟨K, hKn, hKN, hKc⟩ := CFSG.exists_normal_subgroup_card_pow_of_normal N hN hNc k hk
  refine ⟨K.map R.subtype, Subgroup.map_subtype_le K, ?_, ?_, ?_⟩
  · intro g hg x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_map.2 ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, hKn.conj_mem y hy _, ?_⟩
    simp
  · have hle : K.map R.subtype ≤ E0 := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      exact Subgroup.mem_subgroupOf.1 (hKN hy)
    exact CFSG.Open.IsElemAbelian.mono hE0 hle
  · rw [Subgroup.card_map_of_injective (f := R.subtype) (K := K) Subtype.val_injective]
    exact hKc

theorem Nexp_succ_pos {r : ℕ} (hr : 2 ≤ r) : 1 ≤ Nexp (r + 1) := by
  have h := Nexp_mul_two (r + 1)
  have h' : (r + 1) * (r + 1 - 1) = (r + 1) * r := by simp
  rw [h'] at h
  nlinarith

theorem Nexp_mono {n r : ℕ} (h : n ≤ r) : Nexp n ≤ Nexp r := by
  have h1 := Nexp_mul_two n
  have h2 := Nexp_mul_two r
  have h3 : n * (n - 1) ≤ r * (r - 1) := Nat.mul_le_mul h (by omega)
  linarith

theorem rank_ge_of_normal {p r : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (R : Subgroup G)
    (hR : IsPGroup p R) (hr : 2 ≤ r) (hnot : ¬ (p = 3 ∧ r = 2)) {A : Subgroup G}
    (hA : IsEkIn p (p ^ (r - 1)) R A) (E0 : Subgroup G) (hE0R : E0 ≤ R) (hnorm : NormIn R E0)
    (hE0 : IsElemAbelian p E0)
    (hmax : ∀ B : Subgroup G, B ≤ R → NormIn R B → IsElemAbelian p B → Nat.card B ≤ Nat.card E0)
    {n : ℕ} (hn : Nat.card E0 = p ^ n) : r + 1 ≤ n := by
  by_contra hlt
  obtain ⟨hAR, hAa, hAc⟩ := hA
  have hnormA : ∀ a ∈ A, ∀ e ∈ E0, a * e * a⁻¹ ∈ E0 := fun a ha e he => hnorm a (hAR ha) e he
  obtain ⟨ψ, hψ, hψr, hψc⟩ := transport hAa hE0 hn hnormA
  have hker : Nat.card ψ.ker ≤ p ^ n := by
    have hsub : ψ.ker.map A.subtype ≤ E0 := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      have hyc : ∀ e ∈ E0, (y : G) * e = e * (y : G) := (hψ y).1 (MonoidHom.mem_ker.1 hy)
      exact star_of_maxNormal hp2 R hR E0 hE0R hnorm hE0 hmax (y : G) (hAR y.2) (hAa.2 _ y.2) hyc
    rw [← Subgroup.card_map_of_injective (f := A.subtype) (K := ψ.ker) Subtype.val_injective,
      ← hn]
    exact Subgroup.card_le_of_le hsub
  have hrange : Nat.card ψ.range ≤ p ^ Nexp n :=
    gl_pSub_card_le p n (CFSG.Open.IsElemAbelian.isPGroup hψr)
  have hbig : p ^ (p ^ (r - 1)) ≤ p ^ (n + Nexp n) := by
    rw [← hAc, hψc, pow_add]
    exact Nat.mul_le_mul hker hrange
  have hexp : p ^ (r - 1) ≤ n + Nexp n :=
    (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hbig
  have hlow := arith_lower hp.out hp2 hr hnot
  have hmono := Nexp_mono (show n ≤ r by omega)
  omega

theorem link_to_normal {p r : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (R : Subgroup G)
    (hr : 2 ≤ r) (hnot : ¬ (p = 3 ∧ r = 2)) {E : Subgroup G}
    (hE : IsEkIn p (r + 1) R E) (hEn : NormIn R E) {A : Subgroup G}
    (hA : IsEkIn p (p ^ (r - 1)) R A) :
    ∃ U : Subgroup G, IsEkIn p (r + 1) R U ∧ U ≤ A ∧ ∀ u ∈ U, ∀ e ∈ E, u * e = e * u := by
  obtain ⟨hAR, hAa, hAc⟩ := hA
  obtain ⟨ψ, hψ, hψr, hψc⟩ :=
    transport hAa hE.2.1 hE.2.2 (fun a ha e he => hEn a (hAR ha) e he)
  have hrange := gl_elemAb_card_le p (r + 1) (by omega) hψr
  have hpos : 0 < p ^ (Nexp (r + 1) - 1) := pow_pos hp.out.pos _
  have hup := arith_upper hp.out hp2 hr hnot
  have hN1 := Nexp_succ_pos hr
  have hexp : r + 1 + (Nexp (r + 1) - 1) ≤ p ^ (r - 1) := by
    have : r + 1 + (Nexp (r + 1) - 1) = r + Nexp (r + 1) := by omega
    rw [this]
    exact hup
  have hkerc : p ^ (r + 1) ≤ Nat.card ψ.ker := by
    have hbig : p ^ (r + 1) * p ^ (Nexp (r + 1) - 1) ≤
        Nat.card ψ.ker * p ^ (Nexp (r + 1) - 1) := by
      calc p ^ (r + 1) * p ^ (Nexp (r + 1) - 1) = p ^ (r + 1 + (Nexp (r + 1) - 1)) :=
            (pow_add _ _ _).symm
        _ ≤ p ^ (p ^ (r - 1)) := Nat.pow_le_pow_right hp.out.pos hexp
        _ = Nat.card A := hAc.symm
        _ = Nat.card ψ.ker * Nat.card ψ.range := hψc
        _ ≤ Nat.card ψ.ker * p ^ (Nexp (r + 1) - 1) := Nat.mul_le_mul_left _ hrange
    exact Nat.le_of_mul_le_mul_right hbig hpos
  obtain ⟨K, hK, hKc⟩ :=
    Sylow.exists_subgroup_le_card_pow_prime_of_le_card hp.out
      (CFSG.Open.IsElemAbelian.isPGroup hAa) hkerc
  have hUA : K.map A.subtype ≤ A := Subgroup.map_subtype_le K
  refine ⟨K.map A.subtype, ⟨hUA.trans hAR, CFSG.Open.IsElemAbelian.mono hAa hUA, ?_⟩, hUA, ?_⟩
  · rw [Subgroup.card_map_of_injective (f := A.subtype) (K := K) Subtype.val_injective]
    exact hKc
  · rintro u hu e he
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hu
    have hxk : ψ x = 1 := MonoidHom.mem_ker.1 (hK hx)
    exact (hψ x).1 hxk e he

end RLevel

end Input319

open Input319 in
theorem input31_9_holds : Input31_9 := by
  intro G _ _ p r hp hp2 hr hnot R hR A B hA hB
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E0, hE0R, hE0n, hE0a, hE0max⟩ := exists_max_normal_ea R p
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (CFSG.Open.IsElemAbelian.isPGroup hE0a)
  have hkn := rank_ge_of_normal hp2 R hR hr hnot hA E0 hE0R hE0n hE0a hE0max hn
  obtain ⟨E, hER, hEn, hEa, hEc⟩ :=
    exists_normal_rank R hR E0 hE0R hE0n hE0a hn (k := r + 1) hkn
  have hE : IsEkIn p (r + 1) R E := ⟨hER, hEa, hEc⟩
  obtain ⟨U, hU, hUA, hUE⟩ := link_to_normal hp2 R hr hnot hE hEn hA
  obtain ⟨V, hV, hVB, hVE⟩ := link_to_normal hp2 R hr hnot hE hEn hB
  have hsize : ∀ X : Subgroup G, IsEkIn p (p ^ (r - 1)) R X → p ^ (r + 1) ≤ Nat.card X := by
    intro X hX
    rw [hX.2.2]
    apply Nat.pow_le_pow_right hp.pos
    have hup := arith_upper hp hp2 hr hnot
    have hN1 := Nexp_succ_pos hr
    omega
  have hAU : A ≤ Subgroup.centralizer (U : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    haveI : IsMulCommutative A := hA.2.1.1
    have := mul_comm' (⟨u, hUA hu⟩ : A) ⟨a, ha⟩
    exact congrArg Subtype.val this
  have hUC : U ≤ Subgroup.centralizer (E : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (hUE u hu e he).symm
  have hEC : E ≤ Subgroup.centralizer (V : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact hVE v hv e he
  have hVC : V ≤ Subgroup.centralizer (B : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    haveI : IsMulCommutative B := hB.2.1.1
    have := mul_comm' (⟨b, hb⟩ : B) ⟨v, hVB hv⟩
    exact congrArg Subtype.val this
  refine ⟨hA.1, hA.2.1, hsize A hA, hB.1, hB.2.1, hsize B hB, Or.inr ⟨U, V, hU, hV, hAU, ?_, hVC⟩⟩
  exact (Relation.ReflTransGen.single ⟨hU, hE, hUC⟩).tail ⟨hE, hV, hEC⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
