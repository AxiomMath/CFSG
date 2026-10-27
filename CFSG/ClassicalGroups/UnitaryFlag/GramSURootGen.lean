module

public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryTransvectionGeneration

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LocalAnalysis.ComponentInitial

theorem gramSU_one_eq_SUid {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (n : ℕ) :
    gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = SUid h.barEquiv n := by
  have hmap : (⇑h.barEquiv : K → K) = ⇑h.bar := rfl
  ext g
  rw [mem_gramSU, mem_SUid]
  constructor
  · rintro ⟨hiso, hdet⟩
    refine ⟨hdet, ?_⟩
    rw [conjTr, hmap]
    simpa using hiso
  · rintro ⟨hdet, hiso⟩
    refine ⟨?_, hdet⟩
    rw [conjTr, hmap] at hiso
    simpa using hiso

theorem tvMat_pow_ringChar {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    {n : ℕ} {a : Fin n → K} {c : K} (ha : herm h.barEquiv a a = 0) :
    tvMat h.barEquiv a c ^ ringChar K = 1 := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    exact Subsingleton.elim _ _
  · haveI : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
    haveI : Fact ℓ.Prime := ⟨h.prime⟩
    haveI : CharP K ℓ := h.charP
    have hchar : ringChar K = ℓ := ringChar.eq K ℓ
    have hdot : (fun i => h.barEquiv (a i)) ⬝ᵥ a = 0 := by
      simpa [herm, dotProduct] using ha
    have hN2 : (c • vecMulVec a (fun i => h.barEquiv (a i))) ^ 2 = 0 := by
      rw [pow_two, Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec, hdot]
      simp
    have hNpow : (c • vecMulVec a (fun i => h.barEquiv (a i))) ^ ℓ = 0 :=
      pow_eq_zero_of_le (a := c • vecMulVec a (fun i => h.barEquiv (a i)))
        h.prime.two_le hN2
    have hpow : (1 + c • vecMulVec a (fun i => h.barEquiv (a i))) ^ ℓ = 1 := by
      rw [add_pow_char_of_commute (R := Matrix (Fin n) (Fin n) K) (p := ℓ)
        (x := (1 : Matrix (Fin n) (Fin n) K))
        (y := c • vecMulVec a (fun i => h.barEquiv (a i))) (Commute.one_left _), hNpow]
      simp
    rw [tvMat, hchar]
    exact hpow

theorem tv_pow_ringChar {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    {n : ℕ} {t : SUid h.barEquiv n} (ht : t ∈ tvSet h.barEquiv n) :
    t ^ ringChar K = 1 := by
  obtain ⟨a, c, ha, hc, htv⟩ := ht
  have hm : t = mkSU h.barEquiv (tvMat h.barEquiv a c) (tvMat_det ha c)
      (tvMat_isometry h.isUnitaryInvolution_barEquiv.invol ha hc) := by
    apply ext_smul
    intro v
    rw [mkSU_smul, tvMat_mulVec]
    exact htv v
  rw [hm]
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, Units.val_pow_eq_pow_val, Units.val_one]
  change (tvMat h.barEquiv a c) ^ ringChar K = 1
  exact tvMat_pow_ringChar h ha

theorem closure_pow_ringChar_SUid {ℓ f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) {n : ℕ} (hn : 2 ≤ n) (hnq : (n, ℓ ^ f) ≠ (3, 2)) :
    Subgroup.closure {g : SUid h.barEquiv n | g ^ ringChar K = 1} = ⊤ := by
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  have h3 : n = 3 → ∃ s : K, s ≠ 0 ∧ h.barEquiv s * s ≠ 1 := by
    intro hn3
    have hpq : ℓ ≤ ℓ ^ f := Nat.le_self_pow (by have := h.one_le; omega) ℓ
    have hq2 : ℓ ^ f ≠ 2 := fun hq => hnq (by rw [hn3, hq])
    have hq2' : 2 < ℓ ^ f :=
      lt_of_le_of_ne (le_trans h.prime.two_le hpq) (Ne.symm hq2)
    obtain ⟨s, hs0, hs⟩ := CFSG.LinearGroups.exists_ne_zero_norm_ne_one h hq2'
    exact ⟨s, hs0, by rwa [UnitaryFieldData.barEquiv_apply, mul_comm]⟩
  have hT := T_eq_top h.isUnitaryInvolution_barEquiv hn h3
  rw [eq_top_iff, ← hT, T]
  exact Subgroup.closure_mono fun t ht => tv_pow_ringChar h ht

theorem subsingleton_gramSU_one_of_le_one {ℓ f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) {n : ℕ} (hn : n ≤ 1) :
    Subsingleton (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    haveI : Subsingleton (Matrix (Fin 0) (Fin 0) K) :=
      ⟨fun _ _ => Matrix.ext fun i _ => Fin.elim0 i⟩
    haveI : Subsingleton (GL (Fin 0) K) :=
      ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
    constructor
    intro g g'
    exact Subtype.ext (Subsingleton.elim _ _)
  · have hn1 : n = 1 := by omega
    subst hn1
    constructor
    intro g g'
    have hg : (((g : GL (Fin 1) K)) : Matrix (Fin 1) (Fin 1) K) = 1 := by
      ext i j
      fin_cases i
      fin_cases j
      have hdet : (((g : GL (Fin 1) K)) : Matrix (Fin 1) (Fin 1) K).det = 1 :=
        (mem_gramSU.mp g.2).2
      simpa [Matrix.det_fin_one] using hdet
    have hg' : (((g' : GL (Fin 1) K)) : Matrix (Fin 1) (Fin 1) K) = 1 := by
      ext i j
      fin_cases i
      fin_cases j
      have hdet : (((g' : GL (Fin 1) K)) : Matrix (Fin 1) (Fin 1) K).det = 1 :=
        (mem_gramSU.mp g'.2).2
      simpa [Matrix.det_fin_one] using hdet
    exact Subtype.ext (Units.ext (hg.trans hg'.symm))

theorem closure_pow_ringChar_gramSU_of_ne {ℓ f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) {n : ℕ} (hn : (n, ℓ ^ f) ≠ (3, 2)) :
    Subgroup.closure {g : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) |
      g ^ ringChar K = 1} = ⊤ := by
  classical
  by_cases hn2 : 2 ≤ n
  · let S : Set (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
      {g | g ^ ringChar K = 1}
    let e : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≃*
        SUid h.barEquiv n := MulEquiv.subgroupCongr (gramSU_one_eq_SUid h n)
    have hSU := closure_pow_ringChar_SUid h hn2 hn
    have himage : e.toMonoidHom '' S = {g : SUid h.barEquiv n | g ^ ringChar K = 1} := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        change e.toMonoidHom y ^ ringChar K = 1
        rw [← map_pow, hy, map_one]
      · intro hx
        refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
        apply e.injective
        rw [map_pow, MulEquiv.apply_symm_apply, map_one]
        exact hx
    have hmap : Subgroup.map e.toMonoidHom (Subgroup.closure S) = ⊤ := by
      rw [MonoidHom.map_closure, himage, hSU]
    change Subgroup.closure S = ⊤
    rw [eq_top_iff]
    intro g _
    have hg : e g ∈ Subgroup.map e.toMonoidHom (Subgroup.closure S) := by
      rw [hmap]
      exact Subgroup.mem_top _
    rwa [Subgroup.mem_map_equiv] at hg
  · haveI : Subsingleton (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
      subsingleton_gramSU_one_of_le_one h (by omega)
    rw [eq_top_iff]
    intro g _
    rw [Subsingleton.elim g 1]
    exact Subgroup.one_mem _

end CFSG.ClassicalGroups.UnitaryFlag
