module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUc

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace DiagU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks StabU ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
  CFSG.LinearGroups
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem comm_mk_of_fix {A : GL (Fin 4) K} {α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    (hα : IsCU h A α) {g : unitarySU p f K 4} (hαg : α (thU p f K g) = thU p f K g) :
    toProjU h 4 g * QuotientGroup.mk (toSesqU h hα.1) =
      QuotientGroup.mk (toSesqU h hα.1) * toProjU h 4 g := by
  have h1 := hα.apply h g
  rw [hαg] at h1
  have h2 := congrArg (projSUToProjU h 4 (by norm_num)) h1
  change toProjU h 4 g = toProjU h 4 ⟨_, conj_mem_SU h hα.1 g⟩ at h2
  have e : toProjU h 4 ⟨_, conj_mem_SU h hα.1 g⟩ =
      (QuotientGroup.mk (toSesqU h hα.1) : sesqProjUnitary h (stdHermForm h 4)) *
        toProjU h 4 g * (QuotientGroup.mk (toSesqU h hα.1))⁻¹ := by
    change (QuotientGroup.mk (toSesq h 4 ⟨_, conj_mem_SU h hα.1 g⟩) :
      sesqProjUnitary h (stdHermForm h 4)) = _
    rw [toSesq_conj h hα.1 g _ rfl, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv]
    rfl
  rw [e] at h2
  calc toProjU h 4 g * QuotientGroup.mk (toSesqU h hα.1) =
      ((QuotientGroup.mk (toSesqU h hα.1) : sesqProjUnitary h (stdHermForm h 4)) *
        toProjU h 4 g * (QuotientGroup.mk (toSesqU h hα.1))⁻¹) *
          QuotientGroup.mk (toSesqU h hα.1) := by rw [← h2]
    _ = QuotientGroup.mk (toSesqU h hα.1) * toProjU h 4 g := by group

theorem exists_hyp_of_diag (hp2 : p ≠ 2) {A : GL (Fin 4) K}
    {α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))} (hα : IsCU h A α) (hα1 : α ≠ 1)
    (hα2 : α ^ 2 = 1) {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) (hsq : s ∣ (p ^ f) ^ 2 + 1)
    {y : StatedProj (StatedSU 4 (p ^ f) K)} (hy : orderOf y = s) (hαy : α y = y) :
    ∃ (l : K) (P : GL (Fin 4) K), h.bar l * l = -1 ∧
      uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG ∧
      (A : Matrix (Fin 4) (Fin 4) K) * P = P * X1 l := by
  classical
  have := Fact.mk hs
  have : Finite K := h.finite
  have : CharP K p := h.charP
  set B := stdHermForm h 4 with hB
  set Asq := toSesqU h hα.1 with hAsq
  have hA2 := orderOf_mk_toSesqU h hp2 hα hα1 hα2
  have hfin : Module.finrank K (Fin 4 → K) = 4 := Module.finrank_fin_fun K
  obtain ⟨l, hl0, hAA, hN, hP, hM, hcompl, hsplit, hpair, -, hnorm, hidx, -, -, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp2 (by omega)
      (stdHermForm_isSymm h 4) (stdHermForm_separatingLeft h 4) (A := Asq) hA2
  obtain ⟨g, rfl⟩ := thU_surjective y
  have hg : orderOf (toProjU h 4 g) = s := by
    have e : toProjU h 4 g = projSUToProjU h 4 (by norm_num) (thU p f K g) := rfl
    rw [e, orderOf_injective _ (projSUToProjU_injective h 4 (by norm_num)), hy]
  have hcomm := comm_mk_of_fix h hα hαy
  have hdimP : 1 ≤ Module.finrank K (eigenPlus l (unitaryOp Asq)) := by
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact hP
  have hdimM : 1 ≤ Module.finrank K (eigenMinus l (unitaryOp Asq)) := by
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact hM
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  rw [hfin] at hsum
  rcases hN with hN1 | hN1
  ·
    exfalso
    obtain ⟨-, hsepP, hsepM, e₁, -⟩ := hsplit hN1
    have : Finite (LinearMap.GeneralLinearGroup K (Fin 4 → K)) := finite_generalLinearGroup'
    set ybar := toProjU h 4 g with hybar
    have hyC : ybar ∈ Subgroup.centralizer
        {(QuotientGroup.mk' (sesqNormOneScalars h B)) Asq} :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    have hyodd : Odd (orderOf (⟨ybar, hyC⟩ : Subgroup.centralizer
        {(QuotientGroup.mk' (sesqNormOneScalars h B)) Asq})) := by
      rw [← Subgroup.orderOf_coe]
      change Odd (orderOf ybar)
      rw [hybar, hg]
      exact hs.odd_of_ne_two hs2
    have := hnorm
    have hmem := mem_of_index_le_two hidx hyodd
    rw [Subgroup.mem_subgroupOf] at hmem
    obtain ⟨x, hxC, hxy⟩ := hmem
    have hxs : x ^ s ∈ sesqNormOneScalars h B := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      change (QuotientGroup.mk' _ x) ^ s = 1
      rw [hxy]
      change ybar ^ s = 1
      rw [← hg]
      exact pow_orderOf_eq_one _
    have hZexp : ∀ z ∈ sesqNormOneScalars h B, z ^ (p ^ f + 1) = 1 := by
      rintro z ⟨c, hc, hzc⟩
      apply Subtype.ext
      apply Units.ext
      change ((z : LinearMap.GeneralLinearGroup K (Fin 4 → K)) : Module.End K (Fin 4 → K)) ^
        (p ^ f + 1) = 1
      rw [hzc, smul_pow, one_pow]
      have : c ^ (p ^ f + 1) = 1 := by
        rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply] at hc
        rw [pow_succ']
        exact hc
      rw [this, one_smul]
    obtain ⟨m, hm1, hm2⟩ := exists_pow_eq_one_mul_inv_mem hs
      (not_dvd_add_one_of_dvd_sq_add_one hs hs2 hsq) hZexp hxs
    set u := e₁ ⟨x ^ m, Subgroup.pow_mem _ hxC m⟩ with hu
    have hu1 : u ^ s = 1 := by
      rw [hu, ← map_pow]
      have : (⟨x ^ m, Subgroup.pow_mem _ hxC m⟩ : Subgroup.centralizer {Asq}) ^ s = 1 :=
        Subtype.ext hm1
      rw [this, map_one]
    have : Finite (LinearMap.GeneralLinearGroup K (eigenPlus l (unitaryOp Asq))) :=
      finite_generalLinearGroup'
    have : Finite (LinearMap.GeneralLinearGroup K (eigenMinus l (unitaryOp Asq))) :=
      finite_generalLinearGroup'
    have hP1 : u.1 = 1 := by
      apply eq_one_of_pow_eq_one_of_not_dvd hs
        (not_dvd_card_sesqUnitaryGroup h ((stdHermForm_isSymm h 4).domRestrict _) hsepP rfl
          hdimP (by omega) hs hs2 hsq)
      rw [← Prod.pow_fst, hu1]
      rfl
    have hM1 : u.2 = 1 := by
      apply eq_one_of_pow_eq_one_of_not_dvd hs
        (not_dvd_card_sesqUnitaryGroup h ((stdHermForm_isSymm h 4).domRestrict _) hsepM rfl
          hdimM (by omega) hs hs2 hsq)
      rw [← Prod.pow_snd, hu1]
      rfl
    have hxm : x ^ m = 1 := by
      have : (⟨x ^ m, Subgroup.pow_mem _ hxC m⟩ : Subgroup.centralizer {Asq}) = 1 :=
        e₁.injective (by rw [map_one, ← hu]; exact Prod.ext hP1 hM1)
      exact congrArg Subtype.val this
    rw [hxm, one_mul] at hm2
    have hx1 : (QuotientGroup.mk' (sesqNormOneScalars h B)) x = 1 :=
      (QuotientGroup.eq_one_iff x).2 (by simpa using inv_mem hm2)
    rw [hxy] at hx1
    have hy1 : ybar = 1 := hx1
    rw [hy1, orderOf_one] at hg
    exact hs.one_lt.ne' hg.symm
  ·
    obtain ⟨hisoP, hisoM, -, h2d, -, hpairM, -⟩ := hpair hN1
    rw [hfin] at h2d
    have hdP : Module.finrank K (eigenPlus l (unitaryOp Asq)) = 2 := by omega
    have hdM : Module.finrank K (eigenMinus l (unitaryOp Asq)) = 2 := by omega
    set M := (A : Matrix (Fin 4) (Fin 4) K) with hMdef
    have hAv : ∀ v, unitaryOp Asq v = M *ᵥ v := fun v => rfl
    have heig1 : ∀ v ∈ eigenPlus l (unitaryOp Asq), M *ᵥ v = l • v := fun v hv => by
      rw [← hAv]; exact apply_eq_of_mem_eigenPlus hl0 hv
    have heig2 : ∀ w ∈ eigenMinus l (unitaryOp Asq), M *ᵥ w = -l • w := fun w hw => by
      rw [← hAv]; exact apply_eq_of_mem_eigenMinus hl0 hw
    obtain ⟨e, g', he, hg', hdual⟩ := exists_dual_pair h _ _ hdP hdM hpairM
    set col : Fin 4 → Fin 4 → K := ![e 0, e 1, g' 0, g' 1] with hcol
    set Q : Matrix (Fin 4) (Fin 4) K := Matrix.of fun i j => col j i with hQ
    have hQcol : ∀ j, (fun k => Q k j) = col j := fun j => rfl
    have hQQ : uStar h Q * Q = stdG := by
      ext a b
      rw [uStar_mul_apply, hQcol, hQcol]
      have hge : ∀ a b, stdHermForm h 4 (g' a) (e b) = if a = b then 1 else 0 := by
        intro a b
        rw [← (stdHermForm_isSymm h 4).eq, hdual]
        by_cases hab : b = a
        · subst hab; simp
        · simp [hab, Ne.symm hab]
      have hee : ∀ a b, stdHermForm h 4 (e a) (e b) = 0 := fun a b => hisoP _ (he a) _ (he b)
      have hgg : ∀ a b, stdHermForm h 4 (g' a) (g' b) = 0 := fun a b =>
        hisoM _ (hg' a) _ (hg' b)
      fin_cases a <;> fin_cases b <;> simp [hcol, stdG, hdual, hge, hee, hgg]
    have hMQ : M * Q = Q * X1 l := by
      rw [X1_eq_stdDl]
      ext i j
      rw [Matrix.mul_apply, Matrix.mul_apply]
      change (M *ᵥ col j) i = _
      fin_cases j <;> simp [hcol, stdDl, hQ, heig1 _ (he _), heig2 _ (hg' _),
        Matrix.diagonal_apply, mul_comm]
    have hdet : Q.det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hQQ
      have hs' : (stdG : Matrix (Fin 4) (Fin 4) K).det = 1 := det_stdG
      rw [det_mul, h0, mul_zero, hs'] at this
      exact zero_ne_one this
    refine ⟨l, GeneralLinearGroup.mkOfDetNeZero Q hdet, ?_, ?_, ?_⟩
    · rw [UnitaryFieldData.norm] at hN1
      rw [mul_comm]
      exact hN1
    · rw [GeneralLinearGroup.val_mkOfDetNeZero]
      exact hQQ
    · rw [GeneralLinearGroup.val_mkOfDetNeZero]
      exact hMQ

end DiagU

end CFSG.ComponentClassification.CatFactsL4U4
