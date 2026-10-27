module

public import CFSG.GH74.QTGen4.Recog.G23.P7.OpenLeaves
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Borel

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable

variable {G : Type} [Group G]

private lemma card_vec3 : Nat.card (Fin 3 → ZMod 3) = 27 := by
  simp [Nat.card_fun, ZMod.card]

private lemma fixed_eq_zero_of_order13 (g : GL (Fin 3) (ZMod 3)) (hg : orderOf g = 13)
    (u : Fin 3 → ZMod 3) (hu : Matrix.mulVec (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) u = u) :
    u = 0 := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  set N : Matrix (Fin 3) (Fin 3) (ZMod 3) := (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) with hN
  let F : AddSubgroup (Fin 3 → ZMod 3) :=
    { carrier := {v | Matrix.mulVec N v = v}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [Matrix.mulVec_add, ha, hb]
      zero_mem' := by simp
      neg_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [Matrix.mulVec_neg, ha] }
  have hdiv : Nat.card F ∣ 27 := by
    have := AddSubgroup.card_addSubgroup_dvd_card F
    rwa [card_vec3] at this
  have hG : IsPGroup 13 (Subgroup.zpowers g) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hg, pow_one])
  have hfixset : ∀ v : Fin 3 → ZMod 3,
      v ∈ MulAction.fixedPoints (Subgroup.zpowers g) (Fin 3 → ZMod 3) ↔
        Matrix.mulVec N v = v := by
    intro v
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro h
      exact h ⟨g, Subgroup.mem_zpowers g⟩
    · intro h m
      have hle : Subgroup.zpowers g ≤ MulAction.stabilizer (GL (Fin 3) (ZMod 3)) v := by
        rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
        exact h
      exact MulAction.mem_stabilizer_iff.mp (hle m.2)
  have hFeq : MulAction.fixedPoints (Subgroup.zpowers g) (Fin 3 → ZMod 3) =
      (F : Set (Fin 3 → ZMod 3)) := by
    ext v
    exact hfixset v
  have hcong := IsPGroup.card_modEq_card_fixedPoints hG (Fin 3 → ZMod 3)
  rw [card_vec3, hFeq] at hcong
  have hmod : 27 % 13 = Nat.card F % 13 := hcong
  have hle : Nat.card F ≤ 27 := Nat.le_of_dvd (by norm_num) hdiv
  have key : ∀ c < 28, c ∣ 27 → 27 % 13 = c % 13 → c = 1 ∨ c = 27 := by decide
  rcases key (Nat.card F) (by omega) hdiv hmod with h1 | h27
  · obtain ⟨hsub, _⟩ := Nat.card_eq_one_iff_unique.mp h1
    have h0 : (0 : Fin 3 → ZMod 3) ∈ F := zero_mem F
    have := hsub.elim ⟨u, hu⟩ ⟨0, h0⟩
    exact congrArg Subtype.val this
  · exfalso
    have htop : F = ⊤ := AddSubgroup.eq_top_of_card_eq F (by rw [h27, card_vec3])
    have hall : ∀ v : Fin 3 → ZMod 3, Matrix.mulVec N v = v := by
      intro v
      have hv : v ∈ F := by
        rw [htop]
        exact AddSubgroup.mem_top v
      exact hv
    have hN1 : N = 1 := by
      ext i j
      have hj := congrFun (hall (Pi.single j 1)) i
      rw [Matrix.mulVec_single_one] at hj
      simpa [Matrix.col, Pi.single_apply, Matrix.one_apply] using hj
    have hg1 : g = 1 := Units.ext hN1
    rw [hg1, orderOf_one] at hg
    exact absurd hg (by norm_num)

private def sgnZ (b : Bool) : ZMod 3 := if b then -1 else 1

private lemma sgnZ_ne_zero (b : Bool) : sgnZ b ≠ 0 := by
  cases b <;> decide

private lemma sgnZ_mul_self (b : Bool) : sgnZ b * sgnZ b = 1 := by
  cases b <;> decide

private lemma singer_transitive (g : GL (Fin 3) (ZMod 3)) (hg : orderOf g = 13)
    (u v : Fin 3 → ZMod 3) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ k : ℕ, ∃ c : ZMod 3, c ≠ 0 ∧
      Matrix.mulVec ((g ^ k : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) u = c • v := by
  set N : Matrix (Fin 3) (Fin 3) (ZMod 3) := (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) with hN
  have hpow : ∀ k : ℕ, ((g ^ k : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = N ^ k :=
    fun k => Units.val_pow_eq_pow_val g k
  have hN13 : N ^ 13 = 1 := by
    have h := pow_orderOf_eq_one g
    rw [hg] at h
    have h' := congrArg Units.val h
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h'
    exact h'
  have hback : ∀ k : ℕ, k ≤ 13 → ∀ w : Fin 3 → ZMod 3,
      Matrix.mulVec (N ^ (13 - k)) (Matrix.mulVec (N ^ k) w) = w := by
    intro k hk w
    rw [Matrix.mulVec_mulVec, ← pow_add, Nat.sub_add_cancel hk, hN13, Matrix.one_mulVec]
  have hpowfix : ∀ m : ℕ, 0 < m → m < 13 → Matrix.mulVec (N ^ m) u = u → False := by
    intro m hm0 hm13 hmu
    have tab : ∀ m < 13, 0 < m → ∃ m' < 13, m * m' % 13 = 1 := by decide
    obtain ⟨m', -, hm'⟩ := tab m hm13 hm0
    have hNm : N ^ (m * m') = N := by
      have h1 : m * m' = 13 * (m * m' / 13) + 1 := by
        have := Nat.div_add_mod (m * m') 13
        omega
      rw [h1, pow_add, pow_mul, hN13, one_pow, one_mul, pow_one]
    have hiter : ∀ j : ℕ, Matrix.mulVec ((N ^ m) ^ j) u = u := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hmu, ih]
    have hNu : Matrix.mulVec N u = u := by
      calc Matrix.mulVec N u = Matrix.mulVec (N ^ (m * m')) u := by rw [hNm]
        _ = Matrix.mulVec ((N ^ m) ^ m') u := by rw [pow_mul]
        _ = u := hiter m'
    exact hu (fixed_eq_zero_of_order13 g hg u hNu)
  have hdistinct : ∀ k j : ℕ, k < 13 → j < 13 → k < j →
      Matrix.mulVec (N ^ k) u ≠ Matrix.mulVec (N ^ j) u := by
    intro k j hk hj hkj heq
    have h1 : Matrix.mulVec (N ^ (13 - k + j)) u = u := by
      have := congrArg (Matrix.mulVec (N ^ (13 - k))) heq
      rw [hback k hk.le u, Matrix.mulVec_mulVec, ← pow_add] at this
      exact this.symm
    have h3 : N ^ (13 - k + j) = N ^ (j - k) := by
      have : 13 - k + j = (j - k) + 13 := by omega
      rw [this, pow_add, hN13, mul_one]
    exact hpowfix (j - k) (by omega) (by omega) (by rw [← h3]; exact h1)
  have hneg : ∀ k j : ℕ, k < 13 → j < 13 →
      Matrix.mulVec (N ^ k) u ≠ -Matrix.mulVec (N ^ j) u := by
    intro k j hk hj heq
    have h1 : Matrix.mulVec (N ^ (13 - j + k)) u = -u := by
      have := congrArg (Matrix.mulVec (N ^ (13 - j))) heq
      rw [Matrix.mulVec_neg, hback j hj.le u, Matrix.mulVec_mulVec, ← pow_add] at this
      exact this
    have hiter : ∀ i : ℕ, Matrix.mulVec ((N ^ (13 - j + k)) ^ i) u = (-1 : ZMod 3) ^ i • u := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_neg, ih]
        simp only [pow_succ, mul_smul, neg_one_smul, smul_neg]
    have h13 : Matrix.mulVec ((N ^ (13 - j + k)) ^ 13) u = u := by
      rw [← pow_mul, mul_comm, pow_mul, hN13, one_pow, Matrix.one_mulVec]
    have hneg1 : (-1 : ZMod 3) ^ 13 • u = -u := by
      rw [show (-1 : ZMod 3) ^ 13 = -1 by decide, neg_one_smul]
    have hu2 : u = -u := by
      have := hiter 13
      rw [h13, hneg1] at this
      exact this
    have hz : ∀ x : ZMod 3, x = -x → x = 0 := by decide
    exact hu (funext fun i => hz (u i) (congrFun hu2 i))
  have hnz : ∀ k : ℕ, k < 13 → Matrix.mulVec (N ^ k) u ≠ 0 := by
    intro k hk h0
    apply hu
    have := hback k hk.le u
    rw [h0, Matrix.mulVec_zero] at this
    exact this.symm
  have hsame : ∀ k k' : ℕ, k < 13 → k' < 13 →
      Matrix.mulVec (N ^ k) u = Matrix.mulVec (N ^ k') u → k = k' := by
    intro k k' hk hk' heq
    rcases lt_trichotomy k k' with h | h | h
    · exact absurd heq (hdistinct k k' hk hk' h)
    · exact h
    · exact absurd heq.symm (hdistinct k' k hk' hk h)
  let f : Fin 13 × Bool → {w : Fin 3 → ZMod 3 // w ≠ 0} := fun p =>
    ⟨sgnZ p.2 • Matrix.mulVec (N ^ (p.1 : ℕ)) u, smul_ne_zero (sgnZ_ne_zero p.2) (hnz p.1 p.1.isLt)⟩
  have hinj : Function.Injective f := by
    rintro ⟨k, b⟩ ⟨k', b'⟩ h
    have h' : sgnZ b • Matrix.mulVec (N ^ (k : ℕ)) u = sgnZ b' • Matrix.mulVec (N ^ (k' : ℕ)) u :=
      congrArg Subtype.val h
    cases b <;> cases b'
    · rw [show sgnZ false = 1 from rfl, one_smul, one_smul] at h'
      obtain rfl : k = k' := Fin.ext (hsame _ _ k.isLt k'.isLt h')
      rfl
    · rw [show sgnZ false = 1 from rfl, show sgnZ true = -1 from rfl, one_smul, neg_one_smul] at h'
      exact absurd h' (hneg k k' k.isLt k'.isLt)
    · rw [show sgnZ false = 1 from rfl, show sgnZ true = -1 from rfl, one_smul, neg_one_smul] at h'
      exact absurd h'.symm (hneg k' k k'.isLt k.isLt)
    · rw [show sgnZ true = -1 from rfl, neg_one_smul, neg_one_smul, neg_inj] at h'
      obtain rfl : k = k' := Fin.ext (hsame _ _ k.isLt k'.isLt h')
      rfl
  have hcardf : Fintype.card (Fin 13 × Bool) = Fintype.card {w : Fin 3 → ZMod 3 // w ≠ 0} := by
    decide
  have hsurj : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcardf⟩).2
  obtain ⟨⟨k, b⟩, hkb⟩ := hsurj ⟨v, hv⟩
  have hkb' : sgnZ b • Matrix.mulVec (N ^ (k : ℕ)) u = v := congrArg Subtype.val hkb
  refine ⟨(k : ℕ), sgnZ b, sgnZ_ne_zero b, ?_⟩
  rw [hpow, ← hkb', smul_smul, sgnZ_mul_self, one_smul]

private def blk (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  !![M.det, 0, 0; 0, M 0 0, M 0 1; 0, M 1 0, M 1 1]

private lemma blk_mul (M N : Matrix (Fin 2) (Fin 2) (ZMod 3)) :
    blk (M * N) = blk M * blk N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk, Matrix.mul_apply, Fin.sum_univ_three, Matrix.det_mul, Matrix.det_fin_two] <;> ring

private lemma blk_one : blk 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk, Matrix.one_apply]

private def blkHom : Matrix (Fin 2) (Fin 2) (ZMod 3) →* Matrix (Fin 3) (Fin 3) (ZMod 3) where
  toFun := blk
  map_one' := blk_one
  map_mul' := blk_mul

private def blkGL : GL (Fin 2) (ZMod 3) →* GL (Fin 3) (ZMod 3) := Units.map blkHom

private lemma blkGL_val (h : GL (Fin 2) (ZMod 3)) :
    ((blkGL h : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
      blk (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) := rfl

private lemma blk_injective : Function.Injective blk := by
  intro M N h
  have h11 := congrFun (congrFun h 1) 1
  have h12 := congrFun (congrFun h 1) 2
  have h21 := congrFun (congrFun h 2) 1
  have h22 := congrFun (congrFun h 2) 2
  ext i j
  fin_cases i <;> fin_cases j
  · exact h11
  · exact h12
  · exact h21
  · exact h22

private lemma blkGL_injective : Function.Injective blkGL := by
  intro x y hxy
  apply Units.ext
  apply blk_injective
  have := congrArg Units.val hxy
  rw [← blkGL_val, ← blkGL_val]
  exact this

private lemma blkGL_mem (h : GL (Fin 2) (ZMod 3)) : blkGL h ∈ Y0Set := by
  simp only [Y0Set, Set.mem_setOf_eq, blkGL_val]
  simp [blk, Matrix.det_fin_two]

private noncomputable def gM (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) (hM : M.det ≠ 0) : GL (Fin 3) (ZMod 3) :=
  blkGL (Matrix.GeneralLinearGroup.mk'' M (isUnit_iff_ne_zero.mpr hM))

private lemma gM_mem (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) (hM : M.det ≠ 0) :
    gM M hM ∈ Y0Set :=
  blkGL_mem _

private lemma blk_mulVec (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) (w : Fin 3 → ZMod 3) :
    Matrix.mulVec (blk M) w =
      ![M.det * w 0, M 0 0 * w 1 + M 0 1 * w 2, M 1 0 * w 1 + M 1 1 * w 2] := by
  funext i
  fin_cases i <;> simp [blk, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private def tM00 (p0 p1 q0 q1 d : ZMod 3) : ZMod 3 :=
  (p0 ^ 2 + p1 ^ 2) * p0 * q0 + (q0 ^ 2 + q1 ^ 2) * d * q1 * p1

private def tM01 (p0 p1 q0 q1 d : ZMod 3) : ZMod 3 :=
  (p0 ^ 2 + p1 ^ 2) * p1 * q0 - (q0 ^ 2 + q1 ^ 2) * d * q1 * p0

private def tM10 (p0 p1 q0 q1 d : ZMod 3) : ZMod 3 :=
  (p0 ^ 2 + p1 ^ 2) * p0 * q1 - (q0 ^ 2 + q1 ^ 2) * d * q0 * p1

private def tM11 (p0 p1 q0 q1 d : ZMod 3) : ZMod 3 :=
  (p0 ^ 2 + p1 ^ 2) * p1 * q1 + (q0 ^ 2 + q1 ^ 2) * d * q0 * p0

private lemma tM_spec : ∀ p0 p1 q0 q1 d : ZMod 3, (p0 ≠ 0 ∨ p1 ≠ 0) → (q0 ≠ 0 ∨ q1 ≠ 0) →
    d ≠ 0 →
    tM00 p0 p1 q0 q1 d * tM11 p0 p1 q0 q1 d - tM01 p0 p1 q0 q1 d * tM10 p0 p1 q0 q1 d = d ∧
    tM00 p0 p1 q0 q1 d * p0 + tM01 p0 p1 q0 q1 d * p1 = q0 ∧
    tM10 p0 p1 q0 q1 d * p0 + tM11 p0 p1 q0 q1 d * p1 = q1 := by
  decide

private lemma exists_gl2 (p q : Fin 2 → ZMod 3) (hp : p ≠ 0) (hq : q ≠ 0) (d : ZMod 3)
    (hd : d ≠ 0) : ∃ M : Matrix (Fin 2) (Fin 2) (ZMod 3), M.det = d ∧ Matrix.mulVec M p = q := by
  have hp' : p 0 ≠ 0 ∨ p 1 ≠ 0 := by
    by_contra h
    simp only [not_or, ne_eq, not_not] at h
    exact hp (funext fun i => by fin_cases i <;> simp [h.1, h.2])
  have hq' : q 0 ≠ 0 ∨ q 1 ≠ 0 := by
    by_contra h
    simp only [not_or, ne_eq, not_not] at h
    exact hq (funext fun i => by fin_cases i <;> simp [h.1, h.2])
  obtain ⟨h1, h2, h3⟩ := tM_spec (p 0) (p 1) (q 0) (q 1) d hp' hq' hd
  refine ⟨!![tM00 (p 0) (p 1) (q 0) (q 1) d, tM01 (p 0) (p 1) (q 0) (q 1) d;
      tM10 (p 0) (p 1) (q 0) (q 1) d, tM11 (p 0) (p 1) (q 0) (q 1) d], ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    exact h1
  · funext i
    fin_cases i
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h2
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h3

private lemma mulVec_two (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) (p q : Fin 2 → ZMod 3)
    (h : Matrix.mulVec M p = q) :
    M 0 0 * p 0 + M 0 1 * p 1 = q 0 ∧ M 1 0 * p 0 + M 1 1 * p 1 = q 1 := by
  constructor
  · have := congrFun h 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  · have := congrFun h 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this

private noncomputable def mkYel (Y : Subgroup (GL (Fin 3) (ZMod 3))) (hY : ∀ g ∈ Y0Set, g ∈ Y)
    (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) (hM : M.det ≠ 0) : Y :=
  ⟨gM M hM, hY _ (gM_mem M hM)⟩

private lemma mkYel_smul (Y : Subgroup (GL (Fin 3) (ZMod 3))) (hY : ∀ g ∈ Y0Set, g ∈ Y)
    (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) (hM : M.det ≠ 0) (w : Fin 3 → ZMod 3) :
    (mkYel Y hY M hM) • w = Matrix.mulVec (blk M) w := rfl

private lemma mkYel_eq (Y : Subgroup (GL (Fin 3) (ZMod 3))) (hY : ∀ g ∈ Y0Set, g ∈ Y)
    (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) (hM : M.det ≠ 0) (w w' : Fin 3 → ZMod 3)
    (h0 : M.det * w 0 = w' 0) (h1 : M 0 0 * w 1 + M 0 1 * w 2 = w' 1)
    (h2 : M 1 0 * w 1 + M 1 1 * w 2 = w' 2) :
    (mkYel Y hY M hM) • w = w' := by
  rw [mkYel_smul, blk_mulVec]
  funext i
  fin_cases i
  · simpa using h0
  · simpa using h1
  · simpa using h2

private abbrev e0 : Fin 3 → ZMod 3 := ![1, 0, 0]

private lemma e0_ne_zero : e0 ≠ 0 := by decide

private lemma overgroup_part (Y : Subgroup (GL (Fin 3) (ZMod 3)))
    (hY : ∀ g ∈ Y0Set, g ∈ Y) (h13 : ¬ 13 ∣ Nat.card Y)
    (hmove : ∃ g ∈ Y, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 1 0 ≠ 0 ∨
      (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 2 0 ≠ 0) :
    (∀ g ∈ Y, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 1 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 2 = 0) ∧ 432 ∣ Nat.card Y := by
  set O : Set (Fin 3 → ZMod 3) := MulAction.orbit (↥Y) e0
  have hmemO : ∀ w, w ∈ O ↔ ∃ g : Y, g • e0 = w := fun w => MulAction.mem_orbit_iff
  have hinv : ∀ (g : Y) (w : Fin 3 → ZMod 3), w ∈ O → g • w ∈ O := by
    intro g w hw
    obtain ⟨h, rfl⟩ := (hmemO w).mp hw
    exact (hmemO _).mpr ⟨g * h, mul_smul g h e0⟩
  have hsmul_ne : ∀ (g : Y) (w : Fin 3 → ZMod 3), w ≠ 0 → g • w ≠ 0 := by
    intro g w hw hgw
    apply hw
    calc w = g⁻¹ • g • w := (inv_smul_smul g w).symm
      _ = g⁻¹ • (0 : Fin 3 → ZMod 3) := by rw [hgw]
      _ = 0 := smul_zero _
  have hO_ne : ∀ w ∈ O, w ≠ 0 := by
    intro w hw
    obtain ⟨g, hg⟩ := (hmemO w).mp hw
    rw [← hg]
    exact hsmul_ne g e0 e0_ne_zero
  have hnegE : -e0 ∈ O := by
    have hM : (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod 3)).det ≠ 0 := by
      rw [Matrix.det_fin_two_of]
      decide
    refine (hmemO _).mpr ⟨mkYel Y hY _ hM, ?_⟩
    rw [mkYel_smul, blk_mulVec]
    funext i
    fin_cases i <;> simp [e0, Matrix.det_fin_two_of]
  have hC0 : ∀ w : Fin 3 → ZMod 3, w 0 ≠ 0 → w 1 = 0 → w 2 = 0 → w ∈ O := by
    intro w h0 h1 h2
    have key : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1 := by decide
    rcases key (w 0) h0 with hx | hx
    · have hw : w = e0 := by
        funext i
        fin_cases i <;> simp [e0, hx, h1, h2]
      rw [hw]
      exact MulAction.mem_orbit_self e0
    · have hw : w = -e0 := by
        funext i
        fin_cases i <;> simp [e0, hx, h1, h2]
      rw [hw]
      exact hnegE
  have hCP : ∀ w w' : Fin 3 → ZMod 3, w 0 = 0 → w ≠ 0 → w' 0 = 0 → w' ≠ 0 →
      ∃ g : Y, g • w = w' := by
    intro w w' hw0 hw hw'0 hw'
    have hp : (![w 1, w 2] : Fin 2 → ZMod 3) ≠ 0 := by
      intro h
      apply hw
      have h1 : w 1 = 0 := by simpa using congrFun h 0
      have h2 : w 2 = 0 := by simpa using congrFun h 1
      funext i
      fin_cases i <;> simp [hw0, h1, h2]
    have hq : (![w' 1, w' 2] : Fin 2 → ZMod 3) ≠ 0 := by
      intro h
      apply hw'
      have h1 : w' 1 = 0 := by simpa using congrFun h 0
      have h2 : w' 2 = 0 := by simpa using congrFun h 1
      funext i
      fin_cases i <;> simp [hw'0, h1, h2]
    obtain ⟨M, hdet, hMv⟩ := exists_gl2 _ _ hp hq 1 one_ne_zero
    have hM : M.det ≠ 0 := by
      rw [hdet]
      exact one_ne_zero
    obtain ⟨hM0, hM1⟩ := mulVec_two M _ _ hMv
    refine ⟨mkYel Y hY M hM, mkYel_eq Y hY M hM w w' ?_ ?_ ?_⟩
    · rw [hdet, hw0, hw'0]
      ring
    · simpa using hM0
    · simpa using hM1
  have hCA : ∀ w w' : Fin 3 → ZMod 3, w 0 ≠ 0 → w' 0 ≠ 0 → (w 1 ≠ 0 ∨ w 2 ≠ 0) →
      (w' 1 ≠ 0 ∨ w' 2 ≠ 0) → ∃ g : Y, g • w = w' := by
    intro w w' hw0 hw'0 hw12 hw'12
    have hp : (![w 1, w 2] : Fin 2 → ZMod 3) ≠ 0 := by
      intro h
      rcases hw12 with h1 | h2
      · exact h1 (by simpa using congrFun h 0)
      · exact h2 (by simpa using congrFun h 1)
    have hq : (![w' 1, w' 2] : Fin 2 → ZMod 3) ≠ 0 := by
      intro h
      rcases hw'12 with h1 | h2
      · exact h1 (by simpa using congrFun h 0)
      · exact h2 (by simpa using congrFun h 1)
    have hd : w 0 * w' 0 ≠ 0 := mul_ne_zero hw0 hw'0
    obtain ⟨M, hdet, hMv⟩ := exists_gl2 _ _ hp hq (w 0 * w' 0) hd
    have hM : M.det ≠ 0 := by
      rw [hdet]
      exact hd
    obtain ⟨hM0, hM1⟩ := mulVec_two M _ _ hMv
    have hsq : ∀ x : ZMod 3, x ≠ 0 → x * x = 1 := by decide
    refine ⟨mkYel Y hY M hM, mkYel_eq Y hY M hM w w' ?_ ?_ ?_⟩
    · rw [hdet]
      calc w 0 * w' 0 * w 0 = (w 0 * w 0) * w' 0 := by ring
        _ = w' 0 := by rw [hsq _ hw0, one_mul]
    · simpa using hM0
    · simpa using hM1
  have hC_all_of : (∃ w ∈ O, w 0 = 0) → ∀ w : Fin 3 → ZMod 3, w 0 = 0 → w ≠ 0 → w ∈ O := by
    rintro ⟨w₀, hw₀O, hw₀0⟩ w hw0 hw
    obtain ⟨g, hg⟩ := hCP w₀ w hw₀0 (hO_ne w₀ hw₀O) hw0 hw
    rw [← hg]
    exact hinv g w₀ hw₀O
  have hCA_all_of : (∃ w ∈ O, w 0 ≠ 0 ∧ (w 1 ≠ 0 ∨ w 2 ≠ 0)) →
      ∀ w : Fin 3 → ZMod 3, w 0 ≠ 0 → (w 1 ≠ 0 ∨ w 2 ≠ 0) → w ∈ O := by
    rintro ⟨w₀, hw₀O, hw₀0, hw₀12⟩ w hw0 hw12
    obtain ⟨g, hg⟩ := hCA w₀ w hw₀0 hw0 hw₀12 hw12
    rw [← hg]
    exact hinv g w₀ hw₀O
  have hcount : O.ncard * Nat.card (MulAction.stabilizer (↥Y) e0) = Nat.card Y := by
    have h1 := Subgroup.index_mul_card (MulAction.stabilizer (↥Y) e0)
    rw [MulAction.index_stabilizer] at h1
    exact h1
  have h5 : ¬ 5 ∣ Nat.card Y := by
    intro h
    have h' := Subgroup.card_subgroup_dvd_card Y
    have hGL3 : Nat.card (GL (Fin 3) (ZMod 3)) = 11232 := by
      rw [Matrix.card_GL_field]
      simp [Fin.prod_univ_three, ZMod.card]
    rw [hGL3] at h'
    have h'' : 5 ∣ 11232 := h.trans h'
    norm_num at h''
  have hUO : O = {w : Fin 3 → ZMod 3 | w 0 ≠ 0} := by
    by_cases hC : ∃ w ∈ O, w 0 = 0
    · by_cases hCA' : ∃ w ∈ O, w 0 ≠ 0 ∧ (w 1 ≠ 0 ∨ w 2 ≠ 0)
      ·
        exfalso
        have hT : O = {w : Fin 3 → ZMod 3 | w ≠ 0} := by
          apply Set.Subset.antisymm
          · intro w hw
            exact hO_ne w hw
          · intro w hw
            by_cases h0 : w 0 = 0
            · exact hC_all_of hC w h0 hw
            · by_cases h12 : w 1 ≠ 0 ∨ w 2 ≠ 0
              · exact hCA_all_of hCA' w h0 h12
              · simp only [not_or, ne_eq, not_not] at h12
                exact hC0 w h0 h12.1 h12.2
        have hc : O.ncard = 26 := by
          rw [hT]
          have : {w : Fin 3 → ZMod 3 | w ≠ 0} =
              ↑(Finset.univ.filter (fun w : Fin 3 → ZMod 3 => w ≠ 0)) := by
            ext w
            simp
          rw [this, Set.ncard_coe_finset]
          decide
        apply h13
        rw [← hcount, hc]
        exact Dvd.dvd.mul_right (by norm_num) _
      ·
        exfalso
        have hT : O = {w : Fin 3 → ZMod 3 | w ≠ 0 ∧ (w 0 = 0 ∨ (w 1 = 0 ∧ w 2 = 0))} := by
          apply Set.Subset.antisymm
          · intro w hw
            refine ⟨hO_ne w hw, ?_⟩
            by_cases h0 : w 0 = 0
            · exact Or.inl h0
            · by_cases h12 : w 1 ≠ 0 ∨ w 2 ≠ 0
              · exact absurd ⟨w, hw, h0, h12⟩ hCA'
              · simp only [not_or, ne_eq, not_not] at h12
                exact Or.inr h12
          · rintro w ⟨hw, hw0 | ⟨h1, h2⟩⟩
            · exact hC_all_of hC w hw0 hw
            · have h0 : w 0 ≠ 0 := by
                intro h0
                exact hw (funext fun i => by fin_cases i <;> simp [h0, h1, h2])
              exact hC0 w h0 h1 h2
        have hc : O.ncard = 10 := by
          rw [hT]
          have : {w : Fin 3 → ZMod 3 | w ≠ 0 ∧ (w 0 = 0 ∨ (w 1 = 0 ∧ w 2 = 0))} =
              ↑(Finset.univ.filter (fun w : Fin 3 → ZMod 3 => w ≠ 0 ∧ (w 0 = 0 ∨ (w 1 = 0 ∧ w 2 = 0)))) := by
            ext w
            simp
          rw [this, Set.ncard_coe_finset]
          decide
        apply h5
        rw [← hcount, hc]
        exact Dvd.dvd.mul_right (by norm_num) _
    ·
      have hCA' : ∃ w ∈ O, w 0 ≠ 0 ∧ (w 1 ≠ 0 ∨ w 2 ≠ 0) := by
        obtain ⟨g₀, hg₀, hg₀e⟩ := hmove
        have hmem : (⟨g₀, hg₀⟩ : Y) • e0 ∈ O := (hmemO _).mpr ⟨⟨g₀, hg₀⟩, rfl⟩
        have hw1 : ((⟨g₀, hg₀⟩ : Y) • e0) 1 = (g₀ : Matrix (Fin 3) (Fin 3) (ZMod 3)) 1 0 := by
          show Matrix.mulVec (g₀ : Matrix (Fin 3) (Fin 3) (ZMod 3)) e0 1 = _
          simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, e0]
        have hw2 : ((⟨g₀, hg₀⟩ : Y) • e0) 2 = (g₀ : Matrix (Fin 3) (Fin 3) (ZMod 3)) 2 0 := by
          show Matrix.mulVec (g₀ : Matrix (Fin 3) (Fin 3) (ZMod 3)) e0 2 = _
          simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, e0]
        have hw0 : ((⟨g₀, hg₀⟩ : Y) • e0) 0 ≠ 0 := by
          intro h0
          exact hC ⟨_, hmem, h0⟩
        refine ⟨_, hmem, hw0, ?_⟩
        rw [hw1, hw2]
        exact hg₀e
      ext w
      constructor
      · intro hw
        show w 0 ≠ 0
        intro h0
        exact hC ⟨w, hw, h0⟩
      · intro hw
        by_cases h12 : w 1 ≠ 0 ∨ w 2 ≠ 0
        · exact hCA_all_of hCA' w hw h12
        · simp only [not_or, ne_eq, not_not] at h12
          exact hC0 w hw h12.1 h12.2
  have hU18 : ({w : Fin 3 → ZMod 3 | w 0 ≠ 0} : Set (Fin 3 → ZMod 3)).ncard = 18 := by
    have : {w : Fin 3 → ZMod 3 | w 0 ≠ 0} =
        ↑(Finset.univ.filter (fun w : Fin 3 → ZMod 3 => w 0 ≠ 0)) := by
      ext w
      simp
    rw [this, Set.ncard_coe_finset]
    decide
  have hcardO : O.ncard = 18 := by rw [hUO, hU18]
  have hU_in : ∀ w : Fin 3 → ZMod 3, w 0 ≠ 0 → w ∈ O := fun w hw => by
    rw [hUO]
    exact hw
  have hU_out : ∀ w ∈ O, w 0 ≠ 0 := fun w hw => by
    rw [hUO] at hw
    exact hw
  have hcount18 : 18 * Nat.card (MulAction.stabilizer (↥Y) e0) = Nat.card Y := by
    rw [← hcardO]
    exact hcount
  have h3 : 3 ∣ Nat.card (MulAction.stabilizer (↥Y) e0) := by
    have hMu : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod 3)).det ≠ 0 := by
      rw [Matrix.det_fin_two_of]
      decide
    have hMu3 : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod 3)) ^ 3 = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_fin_two] <;> decide
    have hblk3 : blk (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod 3)) ^ 3 = 1 := by
      show blkHom _ ^ 3 = 1
      rw [← map_pow, hMu3, map_one]
    set y : Y := mkYel Y hY _ hMu with hy
    have hyfix : y • e0 = e0 := by
      rw [hy, mkYel_smul, blk_mulVec]
      funext i
      fin_cases i <;> simp [e0, Matrix.det_fin_two_of]
    have hyS : y ∈ MulAction.stabilizer (↥Y) e0 := MulAction.mem_stabilizer_iff.mpr hyfix
    have hypow : ((y : GL (Fin 3) (ZMod 3)))  ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact hblk3
    have hyne : ((y : GL (Fin 3) (ZMod 3))) ≠ 1 := by
      intro h
      have hb : blk (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 1 :=
        congrArg Units.val h
      have h12 := congrFun (congrFun hb 1) 2
      simp [blk, Matrix.one_apply] at h12
    have hxord : orderOf (⟨y, hyS⟩ : MulAction.stabilizer (↥Y) e0) = 3 := by
      rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe, orderOf_eq_prime hypow hyne]
    have hdvd := orderOf_dvd_natCard (⟨y, hyS⟩ : MulAction.stabilizer (↥Y) e0)
    rwa [hxord] at hdvd
  have hrange : (blkGL : GL (Fin 2) (ZMod 3) →* GL (Fin 3) (ZMod 3)).range ≤ Y := by
    intro x hx
    obtain ⟨h, rfl⟩ := MonoidHom.mem_range.mp hx
    exact hY _ (blkGL_mem h)
  have hr48 : Nat.card (blkGL : GL (Fin 2) (ZMod 3) →* GL (Fin 3) (ZMod 3)).range = 48 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective blkGL_injective).toEquiv]
    rw [Matrix.card_GL_field]
    simp [Fin.prod_univ_two, ZMod.card]
  have h48 : 48 ∣ Nat.card Y := by
    rw [← hr48]
    exact Subgroup.card_dvd_of_le hrange
  refine ⟨?_, ?_⟩
  ·
    intro g hg
    have aux : ∀ (y : Y) (w : Fin 3 → ZMod 3), w 0 = 0 → (y • w) 0 = 0 := by
      intro y w hw
      by_contra hne
      obtain ⟨z, hz⟩ := (hmemO _).mp (hU_in _ hne)
      have hwO : w ∈ O := (hmemO w).mpr ⟨y⁻¹ * z, by rw [mul_smul, hz, inv_smul_smul]⟩
      exact hU_out w hwO hw
    have h01 : Matrix.mulVec (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) ![0, 1, 0] 0 = 0 :=
      aux ⟨g, hg⟩ ![0, 1, 0] (by simp)
    have h02 : Matrix.mulVec (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) ![0, 0, 1] 0 = 0 :=
      aux ⟨g, hg⟩ ![0, 0, 1] (by simp)
    constructor
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h01
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h02
  ·
    omega

theorem leafGL3Facts : LeafGL3Facts :=
  ⟨fun g hg u v hu hv => singer_transitive g hg u v hu hv,
    fun Y hY h13 hmove => overgroup_part Y hY h13 hmove⟩

end CFSG.GH74.QTGen4.Recog.G23.P7
