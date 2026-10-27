module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4U4Order
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherInvolutionCentralizer
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Proj

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LinearGroups CFSG.Assembly.LowTwoRank

theorem exists_pow_eq_one_mul_inv_mem {G : Type*} [Group G] {Z : Subgroup G} {N s : ℕ}
    (hs : s.Prime) (hsN : ¬ s ∣ N) (hZ : ∀ z ∈ Z, z ^ N = 1) {x : G} (hx : x ^ s ∈ Z) :
    ∃ m : ℕ, (x ^ m) ^ s = 1 ∧ x ^ m * x⁻¹ ∈ Z := by
  set m := N ^ (s - 1) with hm
  have hs1 : 1 ≤ s - 1 := by have := hs.two_le; omega
  have hfermat : m % s = 1 := by
    have hcop : Nat.Coprime s N := (Nat.Prime.coprime_iff_not_dvd hs).2 hsN
    have h1 := Nat.ModEq.pow_totient hcop.symm
    rw [Nat.totient_prime hs] at h1
    unfold Nat.ModEq at h1
    rwa [Nat.mod_eq_of_lt hs.one_lt] at h1
  refine ⟨m, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hm, show s - 1 = (s - 1 - 1) + 1 by omega, pow_succ',
      pow_mul, hZ _ hx, one_pow]
  · have hm1 : m = s * (m / s) + 1 := by
      have := Nat.div_add_mod m s
      omega
    rw [hm1, pow_succ, mul_assoc, mul_inv_cancel, mul_one, pow_mul]
    exact Subgroup.pow_mem _ hx _

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem toSesq_scalar_val {n : ℕ} (A : ClassicalGroups.UnitaryFlag.unitarySU p f K n) (c : Kˣ)
    (hA : (A : GL (Fin n) K) = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    (((toSesq h n A : sesqUnitaryGroup (stdHermForm h n)) :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) =
      (c : K) • (1 : Module.End K (Fin n → K)) := by
  refine LinearMap.ext fun v => ?_
  rw [toSesq_apply, hA, Matrix.GeneralLinearGroup.coe_scalar, LinearMap.smul_apply,
    Module.End.one_apply, Matrix.scalar_apply]
  funext i
  rw [Matrix.mulVec_diagonal]
  simp

theorem toSesq_mem_normOne_of_scalar {n : ℕ} (hn : 1 ≤ n)
    (A : ClassicalGroups.UnitaryFlag.unitarySU p f K n)
    (hA : (A : GL (Fin n) K) ∈ StatedScalars (Fin n) K) :
    toSesq h n A ∈ sesqNormOneScalars h (stdHermForm h n) := by
  obtain ⟨c, hc⟩ := hA
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ StatedSU n (p ^ f) K := hc ▸ A.2
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  obtain ⟨-, hc2⟩ := (scalar_mem_statedSU_iff h.prime hK hn c).1 hmem
  refine ⟨c, ?_, toSesq_scalar_val h A c hc.symm⟩
  rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, ← pow_succ']
  have := congrArg Units.val hc2
  simpa using this

theorem mem_statedScalars_of_toSesq_mem {n : ℕ}
    (A : ClassicalGroups.UnitaryFlag.unitarySU p f K n)
    (hA : toSesq h n A ∈ sesqNormOneScalars h (stdHermForm h n)) :
    (A : GL (Fin n) K) ∈ StatedScalars (Fin n) K := by
  obtain ⟨c, hc, hAc⟩ := hA
  have hc0 : c ≠ 0 := ne_zero_of_norm_eq_one h hc
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Matrix.GeneralLinearGroup.toLin.injective
  apply Units.ext
  refine LinearMap.ext fun v => ?_
  have h1 := congrArg (fun g : Module.End K (Fin n → K) => g v) hAc
  simp only [LinearMap.smul_apply, Module.End.one_apply] at h1
  have h2 : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec v = c • v := by
    rw [← toSesq_apply]
    exact h1
  rw [Matrix.GeneralLinearGroup.coe_toLin, Matrix.GeneralLinearGroup.coe_toLin,
    Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, h2, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply]
  funext i
  rw [Matrix.mulVec_diagonal]
  simp

theorem det_eq_of_isCompl_smul {R V : Type*} [Field R] [AddCommGroup V] [Module R V]
    [FiniteDimensional R V] {T : Module.End R V} {W₁ W₂ : Submodule R V} (hc : IsCompl W₁ W₂)
    {a b : R} (h₁ : ∀ v ∈ W₁, T v = a • v) (h₂ : ∀ v ∈ W₂, T v = b • v) :
    LinearMap.det T = a ^ Module.finrank R W₁ * b ^ Module.finrank R W₂ := by
  set e := Submodule.prodEquivOfIsCompl W₁ W₂ hc with he
  set P : Module.End R (W₁ × W₂) :=
    LinearMap.prodMap (a • LinearMap.id) (b • LinearMap.id) with hP
  have hT : T = (e : (W₁ × W₂) →ₗ[R] V) ∘ₗ P ∘ₗ (e.symm : V →ₗ[R] (W₁ × W₂)) := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨⟨x, y⟩, rfl⟩ := e.surjective v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, hP, LinearMap.prodMap_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, LinearMap.id_apply, LinearMap.id_apply, he,
      Submodule.coe_prodEquivOfIsCompl', Submodule.coe_prodEquivOfIsCompl', map_add,
      h₁ x x.2, h₂ y y.2]
    rfl
  rw [hT, LinearMap.det_conj, hP, LinearMap.det_prodMap, LinearMap.det_smul, LinearMap.det_smul,
    LinearMap.det_id, LinearMap.det_id, mul_one, mul_one]

omit [Field K] in
theorem finite_generalLinearGroup' {R W : Type*} [Field R] [Finite R] [AddCommGroup W]
    [Module R W] [FiniteDimensional R W] : Finite (LinearMap.GeneralLinearGroup R W) := by
  have : Finite W := Module.finite_of_finite R
  exact Finite.of_injective
    (fun g : LinearMap.GeneralLinearGroup R W => ((g : W →ₗ[R] W) : W → W))
    fun _ _ hgg => Units.ext (LinearMap.ext (congrFun hgg))

@[expose] noncomputable def toProjU (n : ℕ) :
    ClassicalGroups.UnitaryFlag.unitarySU p f K n →* sesqProjUnitary h (stdHermForm h n) :=
  (QuotientGroup.mk' (sesqNormOneScalars h (stdHermForm h n))).comp (toSesq h n)

@[expose] noncomputable def projSUToProjU (n : ℕ) (hn : 1 ≤ n) :
    StatedProj (StatedSU n (p ^ f) K) →* sesqProjUnitary h (stdHermForm h n) :=
  QuotientGroup.lift _ (toProjU h n) (by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [MonoidHom.mem_ker, toProjU, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact toSesq_mem_normOne_of_scalar h hn x hx)

theorem projSUToProjU_mk (n : ℕ) (hn : 1 ≤ n) (x : StatedSU n (p ^ f) K) :
    projSUToProjU h n hn (QuotientGroup.mk x) = QuotientGroup.mk (toSesq h n x) := rfl

theorem projSUToProjU_injective (n : ℕ) (hn : 1 ≤ n) :
    Function.Injective (projSUToProjU h n hn) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MonoidHom.mem_ker, projSUToProjU_mk, QuotientGroup.eq_one_iff] at hx
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact mem_statedScalars_of_toSesq_mem h A hx

theorem not_dvd_add_one_of_dvd_sq_add_one {q s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2)
    (hsq : s ∣ q ^ 2 + 1) : ¬ s ∣ q + 1 := by
  intro h1
  apply not_int_dvd_pow_sub_neg_one_pow (i := 1) hs hs2 hsq le_rfl (by norm_num)
  have : ((q + 1 : ℕ) : ℤ) = (q : ℤ) ^ 1 - (-1) ^ 1 := by push_cast; ring
  rw [← this]
  exact Int.natCast_dvd_natCast.2 h1

theorem unitary_four_core (hp2 : p ≠ 2) (A g : ClassicalGroups.UnitaryFlag.unitarySU p f K 4)
    (hA2 : orderOf (toProjU h 4 A) = 2) {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2)
    (hsq : s ∣ (p ^ f) ^ 2 + 1) (hg : orderOf (toProjU h 4 g) = s)
    (hcomm : toProjU h 4 g * toProjU h 4 A = toProjU h 4 A * toProjU h 4 g) :
    ∃ l : K, l ≠ 0 ∧ unitaryOp (toSesq h 4 A) * unitaryOp (toSesq h 4 A) = (l ^ 2) • 1 ∧
      h.norm l = -1 ∧ l ^ 2 = -1 ∧ (p ^ f) % 4 = 1 ∧
      Module.finrank K (eigenPlus l (unitaryOp (toSesq h 4 A))) = 2 ∧
      Module.finrank K (eigenMinus l (unitaryOp (toSesq h 4 A))) = 2 ∧
      ∃ e : Subgroup.centralizer {toSesq h 4 A} ≃*
          LinearMap.GeneralLinearGroup K (eigenPlus l (unitaryOp (toSesq h 4 A))),
        ∀ x : Subgroup.centralizer {toSesq h 4 A},
          (eigenPlus l (unitaryOp (toSesq h 4 A))).subtype ∘ₗ
              ((e x : LinearMap.GeneralLinearGroup K _) : Module.End K _) =
            unitaryOp (x : sesqUnitaryGroup (stdHermForm h 4)) ∘ₗ
              (eigenPlus l (unitaryOp (toSesq h 4 A))).subtype := by
  classical
  have := Fact.mk hs
  have : Finite K := h.finite
  have : CharP K p := h.charP
  set B := stdHermForm h 4 with hB
  set Asq := toSesq h 4 A with hAsq
  have hfin : Module.finrank K (Fin 4 → K) = 4 := Module.finrank_fin_fun K
  obtain ⟨l, hl0, hAA, hN, hP, hM, hcompl, hsplit, hpair, -, hnorm, hidx, -, -, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp2 (by omega)
      (stdHermForm_isSymm h 4) (stdHermForm_separatingLeft h 4) (A := Asq) hA2
  have hdimP : 1 ≤ Module.finrank K (eigenPlus l (unitaryOp Asq)) := by
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact hP
  have hdimM : 1 ≤ Module.finrank K (eigenMinus l (unitaryOp Asq)) := by
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact hM
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  rw [hfin] at hsum
  have hcharK : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
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
    obtain ⟨-, -, hdeq, h2d, -, -, eC, heC, -, -⟩ := hpair hN1
    have hdP : Module.finrank K (eigenPlus l (unitaryOp Asq)) = 2 := by omega
    have hdM : Module.finrank K (eigenMinus l (unitaryOp Asq)) = 2 := by omega
    have hdet : LinearMap.det (unitaryOp Asq) = l ^ 2 * (-l) ^ 2 := by
      rw [show l ^ 2 * (-l) ^ 2 = l ^ Module.finrank K (eigenPlus l (unitaryOp Asq)) *
        (-l) ^ Module.finrank K (eigenMinus l (unitaryOp Asq)) by rw [hdP, hdM]]
      refine det_eq_of_isCompl_smul hcompl (fun v hv => ?_) (fun v hv => ?_)
      · have hv' : (invSMulOp l (unitaryOp Asq) - 1) v = 0 := hv
        rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, invSMulOp,
          LinearMap.smul_apply] at hv'
        conv_rhs => rw [← hv']
        rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
      · have hv' : (invSMulOp l (unitaryOp Asq) + 1) v = 0 := hv
        rw [LinearMap.add_apply, Module.End.one_apply, add_eq_zero_iff_eq_neg, invSMulOp,
          LinearMap.smul_apply] at hv'
        have : unitaryOp Asq v = l • (l⁻¹ • unitaryOp Asq v) := by
          rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
        rw [this, hv', smul_neg, neg_smul]
    have hdet1 : LinearMap.det (unitaryOp Asq) = 1 := by
      have h1 : unitaryOp Asq = Matrix.toLin' ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
        refine LinearMap.ext fun v => ?_
        rw [Matrix.toLin'_apply]
        exact toSesq_apply h 4 A v
      rw [h1, LinearMap.det_toLin']
      exact ((ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).1 A.2).1
    have hl4 : l ^ 4 = 1 := by
      rw [hdet1] at hdet
      rw [show l ^ 4 = l ^ 2 * (-l) ^ 2 by ring]
      exact hdet.symm
    have hNl : l ^ (p ^ f + 1) = -1 := by
      rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply] at hN1
      rw [pow_succ']
      exact hN1
    have hqodd : Odd (p ^ f) := (h.prime.odd_of_ne_two hp2).pow
    have hq1 : (p ^ f) % 4 = 1 := by
      rcases Nat.odd_iff.1 hqodd with hq
      by_contra hne
      have h3 : (p ^ f) % 4 = 3 := by omega
      obtain ⟨t, ht⟩ : ∃ t, p ^ f + 1 = 4 * t := ⟨(p ^ f + 1) / 4, by omega⟩
      rw [ht, pow_mul, hl4, one_pow] at hNl
      have hc2 := neg_one_eq_one_iff.1 hNl.symm
      rw [ringChar.eq K p] at hc2
      exact hp2 hc2
    refine ⟨l, hl0, hAA, hN1, ?_, hq1, hdP, hdM, eC, heC⟩
    obtain ⟨t, ht⟩ : ∃ t, p ^ f + 1 = 4 * t + 2 := ⟨(p ^ f + 1) / 4, by omega⟩
    rw [ht, pow_add, pow_mul, hl4, one_pow, one_mul] at hNl
    exact hNl

end CFSG.ComponentClassification.CatFactsL4U4
