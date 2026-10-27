module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreA
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2

public section

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.GorensteinWalter
open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

theorem trace_zero_of_nil {K : Type*} [Field K] {N : Matrix (Fin 2) (Fin 2) K} (hN : IsNilpotent N) :
    N.trace = 0 := by
  have h1 : IsNilpotent (Matrix.toLin' N) := hN.map (Matrix.toLinAlgEquiv' (R := K) (n := Fin 2)).toRingEquiv.toRingHom
  have := (LinearMap.isNilpotent_trace_of_isNilpotent h1).eq_zero
  rwa [LinearMap.trace_eq_matrix_trace K (Pi.basisFun K (Fin 2)), LinearMap.toMatrix_eq_toMatrix',
    LinearMap.toMatrix'_toLin'] at this

theorem det_zero_of_nil {K : Type*} [Field K] {N : Matrix (Fin 2) (Fin 2) K} (hN : IsNilpotent N) :
    N.det = 0 := by
  obtain ⟨k, hk⟩ := hN
  have : IsNilpotent N.det := ⟨k, by rw [← Matrix.det_pow, hk]; simp⟩
  exact this.eq_zero

theorem fin_two_commute_nilpotent {K : Type*} [Field K] (h2 : (2:K) ≠ 0) {N B : Matrix (Fin 2) (Fin 2) K}
    (hN : IsNilpotent N) (hN0 : N ≠ 0) (hc : B * N = N * B) :
    ∃ x y : K, B = x • (1 : Matrix (Fin 2) (Fin 2) K) + y • N := by
  have htr := trace_zero_of_nil hN
  have hdet := det_zero_of_nil hN
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two] at htr
  have hd : N 1 1 = - N 0 0 := by linear_combination htr
  have hn : N 0 0 * N 0 0 + N 0 1 * N 1 0 = 0 := by rw [hd] at hdet; linear_combination -hdet
  have c00 := congrFun (congrFun hc 0) 0
  have c01 := congrFun (congrFun hc 0) 1
  have c10 := congrFun (congrFun hc 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at c00 c01 c10
  rw [hd] at c01 c10
  have key : ∃ y : K, y * N 0 1 = B 0 1 ∧ y * N 1 0 = B 1 0 ∧
      2 * (y * N 0 0) = B 0 0 - B 1 1 := by
    by_cases hb : N 0 1 = 0
    · have ha : N 0 0 = 0 := by
        rw [hb] at hn; simpa using hn
      have hc0 : N 1 0 ≠ 0 := by
        intro hc0
        apply hN0
        ext i j
        fin_cases i <;> fin_cases j <;> simp_all
      refine ⟨B 1 0 / N 1 0, ?_, ?_, ?_⟩
      · rw [hb, mul_zero]
        rw [hb, ha] at c00
        have : B 0 1 * N 1 0 = 0 := by linear_combination c00
        exact ((mul_eq_zero.1 this).resolve_right hc0).symm
      · field_simp
      · rw [ha, mul_zero, mul_zero]
        rw [ha] at c10
        have : N 1 0 * (B 0 0 - B 1 1) = 0 := by linear_combination -c10
        exact ((mul_eq_zero.1 this).resolve_left hc0).symm
    · refine ⟨B 0 1 / N 0 1, ?_, ?_, ?_⟩
      · field_simp
      · field_simp; linear_combination c00
      · field_simp; linear_combination -c01
  obtain ⟨y, hy1, hy2, hy3⟩ := key
  refine ⟨(B 0 0 + B 1 1) / 2, y, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simp; field_simp; linear_combination -hy3
  · simpa using hy1.symm
  · simpa using hy2.symm
  · simp [hd]; field_simp; linear_combination hy3

theorem psl2_matrix_core {K : Type*} [Field K] (h2 : (2:K) ≠ 0)
    {N B Bi : Matrix (Fin 2) (Fin 2) K} (hN : IsNilpotent N) (hN0 : N ≠ 0)
    (hB : B * Bi = 1) (hB' : Bi * B = 1) (σ : K ≃+* K)
    (h : ∀ t : K, ∃ u : K, u • (B * (1 + σ t • N.map σ) * Bi) = 1 + t • N) :
    σ = 1 ∧ ∃ x y : K, B = x • (1 : Matrix (Fin 2) (Fin 2) K) + y • N := by
  have hσN : IsNilpotent (N.map σ) := by
    have := hN.map (σ.toRingHom.mapMatrix)
    simpa using this
  have hM : IsNilpotent (B * N.map σ * Bi) := isNilpotent_conj hB hB' hσN
  have hu : ∀ t : K, σ t • (B * N.map σ * Bi) = t • N := by
    intro t
    obtain ⟨u, hu⟩ := h t
    have e1 : B * (1 + σ t • N.map σ) * Bi = 1 + σ t • (B * N.map σ * Bi) := by
      rw [mul_add, add_mul, mul_one, hB, Matrix.mul_smul, Matrix.smul_mul]
    rw [e1] at hu
    have := eq_one_of_smul_one_add_nilpotent (hM.smul (σ t)) (hN.smul t) hu
    rw [this, one_smul] at hu
    exact add_left_cancel hu
  have h1 : B * N.map σ * Bi = N := by simpa using hu 1
  have hσ : σ = 1 := by
    refine RingEquiv.ext fun t => ?_
    have := hu t
    rw [h1, ← sub_eq_zero, ← sub_smul] at this
    have h3 := (smul_eq_zero.1 this).resolve_right hN0
    exact sub_eq_zero.1 h3
  refine ⟨hσ, ?_⟩
  have hmap : N.map σ = N := by
    ext i j; simp [hσ]
  rw [hmap] at h1
  apply fin_two_commute_nilpotent h2 hN hN0
  calc B * N = (B * N * Bi) * B := by rw [mul_assoc, mul_assoc, hB', mul_one] 
    _ = N * B := by rw [h1]

theorem uniq_psl2 {K : Type} [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (hKc : 3 < Nat.card K) {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    {N : Matrix (Fin 2) (Fin 2) K} (hN : IsNilpotent N) (hN0 : N ≠ 0)
    (α : MulAut (PSL2 K)) (hcop : (orderOf α).Coprime p)
    (hfix : ∀ (s : SpecialLinearGroup (Fin 2) K) (t : K),
      (s : Matrix (Fin 2) (Fin 2) K) = 1 + t • N → α (QuotientGroup.mk s) = QuotientGroup.mk s) :
    α = 1 := by
  classical
  obtain ⟨ℓ, f, hℓ, -, hf, hKcard⟩ := id hK
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨y, hy⟩ := pGammaL2ToMulAutPSL2_surjective K hKcard hK hKc α
  obtain ⟨B, hB⟩ := ProjGenLinGroup.mk_surjective y.left
  have hα : ∀ x, α x = pgl2InnerAutPSL2 K hK hKc y.left (psl2FieldAut K y.right x) := by
    intro x
    have hdec := SemidirectProduct.inl_left_mul_inr_right y
    have : α = pGammaL2ToMulAutPSL2 K hK hKc (SemidirectProduct.inl y.left * SemidirectProduct.inr y.right) := by
      rw [hdec, hy]
    rw [this, map_mul, pGammaL2ToMulAutPSL2_inl, pGammaL2ToMulAutPSL2_inr]
    rfl
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    have := (CharP.cast_eq_zero_iff K p 2).1 this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 this)
  have hmat : ∀ t : K, ∃ u : K, u • ((B : Matrix (Fin 2) (Fin 2) K) *
      (1 + y.right t • N.map y.right) * ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) =
        1 + t • N := by
    intro t
    have h1 := hfix (uniSL (p := p) N hN t) t rfl
    have h3 := congrArg (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)) h1
    have hk : ∀ g : GL (Fin 2) K, pgl2RingEquiv y.right (ProjGenLinGroup.mk g) =
        ProjGenLinGroup.mk (GeneralLinearGroup.map y.right.toRingHom g) :=
      fun g => pgl2RingEquiv_mk y.right g
    rw [hα, toPGL_pgl2InnerAutPSL2_apply, ← hB] at h3
    rw [psl2FieldAut_toPGL, ProjectiveSpecialLinearGroup.toPGL_mk,
      pgl2FieldAut_apply, hk, ← map_inv, ← map_mul, ← map_mul,
      ProjGenLinGroup.mk_eq_mk_iff] at h3
    obtain ⟨u, hu⟩ := h3
    have hu' := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) hu
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at hu'
    refine ⟨(u : K), ?_⟩
    have hs : ((scalar (Fin 2)) (u : K) : Matrix (Fin 2) (Fin 2) K) = (u : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
    rw [hs, Matrix.mul_smul, ← Matrix.smul_mul] at hu'
    have e1 : ∀ g : GL (Fin 2) K, ((GeneralLinearGroup.map y.right.toRingHom g : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = (g : Matrix (Fin 2) (Fin 2) K).map y.right := by
      intro g; ext i j; rfl
    have e2 : ((1 + t • N : Matrix (Fin 2) (Fin 2) K)).map y.right =
        1 + y.right t • N.map y.right := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [e1, SpecialLinearGroup.coe_GL_coe_matrix, mul_one, coe_uniSL,
      e2] at hu'
    exact hu'
  obtain ⟨hσ, x, z, hBxz⟩ := psl2_matrix_core h2 hN hN0 (Units.mul_inv B) (Units.inv_mul B) y.right hmat
  obtain ⟨e, he⟩ := add_smul_one_pow_prime_pow (p := p) (hN.smul z) x
  have hBpow : B ^ p ^ e ∈ Subgroup.center (GL (Fin 2) K) := by
    rw [GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
    refine ⟨x ^ p ^ e, ?_⟩
    rw [Units.val_pow_eq_pow_val, hBxz, he, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
  have hgpow : y.left ^ p ^ e = 1 := by
    rw [← hB, ← map_pow, ProjGenLinGroup.mk_eq_one]
    exact hBpow
  have hαin : α = pgl2InnerAutPSL2 K hK hKc y.left := by
    ext1 x
    rw [hα, hσ, map_one]
    rfl
  have hord : α ^ p ^ e = 1 := by
    rw [hαin, ← map_pow, hgpow, map_one]
  have hdvd : orderOf α ∣ p ^ e := orderOf_dvd_of_pow_eq_one hord
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right e hcop) hdvd)

theorem defCharInnerCoreFreeFamA_one :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      ∀ idx : TauCeti.ValidLieTypeIndex, (∃ q, idx.1 = .A 1 q) →
        Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
        ∀ p : ℕ, p.Prime → p ≠ 2 → idx.1.characteristic = p →
          ∀ x ∈ innerAut S, orderOf x = p → ∀ H : Subgroup (MulAut S), innerAut S ≤ H →
            GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) = ⊥ := by
  intro S _ _ hS hnab idx hidx hSL p hp hp2 hch x hx hxo H hH
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hpq : p = q.p := by simpa using hch.symm
  subst hpq
  have hlin : CFSG.AGLEmbedding.IsLinTwoIndex q.p q.exponent ⟨.A 1 q, hv⟩ := ⟨q, rfl, rfl, rfl⟩
  obtain ⟨e0⟩ := hSL
  obtain ⟨e1⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hlin
  let e : S ≃* PSL2 (GaloisField q.p q.exponent) := e0.trans e1
  let ι : PSL2 (GaloisField q.p q.exponent) ≃* projectiveSL 2 (GaloisField q.p q.exponent) :=
    LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 _
  let E : S ≃* projectiveSL 2 (GaloisField q.p q.exponent) := e.trans ι
  have hKq : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  have hodd : IsOddPrimePower (Nat.card (GaloisField q.p q.exponent)) :=
    ⟨q.p, q.exponent, q.prime_p, q.prime_p.odd_of_ne_two hp2, q.exponent_pos, hKq⟩
  have h4 : 4 ≤ q.p ^ q.exponent := by
    have := hv
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff] at this
    simpa [TauCeti.PrimePower.card_def] using this.1.2 rfl
  have hKc : 3 < Nat.card (GaloisField q.p q.exponent) := by rw [hKq]; omega
  have hZ : Subgroup.center S = ⊥ := center_eq_bot_of_simple hS hnab
  obtain ⟨g, rfl⟩ := hx
  have hord : orderOf g = q.p := by
    rw [← orderOf_injective (MulAut.conj : S →* MulAut S) (conj_injective_of_center_eq_bot hZ) g]
    exact hxo
  have hord0 : orderOf (E g) = q.p := by rw [MulEquiv.orderOf_eq E g]; exact hord
  obtain ⟨N, hN, hN0, hg0⟩ := exists_nilpotent_of_orderOf_eq (p := q.p) (E g) hord0
  refine gLAPPrimeCoreOf_eq_bot_of_framework hZ hp g ∅
    {q' | E q' ∈ modelT 2 (GaloisField q.p q.exponent) N} ?_ ?_ ?_ ?_ ?_ H hH _ rfl
  · intro q' hq'
    rcases hq' with hq' | hq'
    · exact hq'.elim
    apply E.injective
    rw [map_mul, map_mul, hg0]
    exact model_h1 hN (E q') (Or.inr hq')
  · intro s q' hs hq'
    apply E.injective
    rw [map_mul, map_mul]
    refine model_hT hN (E s) (E q') ?_ hq'
    rw [← hg0, ← map_mul, ← map_mul, hs]
  · intro s q' _ hq'
    exact hq'.elim
  · intro q' hq'
    exact hq'.elim
  · intro α hα hfix
    have hcop : (orderOf (MulAut.congr e α)).Coprime q.p := by
      rw [MulEquiv.orderOf_eq (MulAut.congr e) α]; exact hα
    have h1 : MulAut.congr e α = 1 := by
      refine uniq_psl2 (p := q.p) hodd hKc hp2 hN hN0 _ hcop ?_
      intro s t hs
      have hmem : E.symm (proj 2 (GaloisField q.p q.exponent) s) ∈
          (∅ : Set S) ∪ {q' | E q' ∈ modelT 2 (GaloisField q.p q.exponent) N} :=
        Or.inr (by
          show E (E.symm _) ∈ modelT 2 (GaloisField q.p q.exponent) N
          rw [MulEquiv.apply_symm_apply]
          exact ⟨s, t, hs, rfl⟩)
      have h2 := hfix _ hmem
      have h3 : e.symm (QuotientGroup.mk s) = E.symm (proj 2 (GaloisField q.p q.exponent) s) := by
        apply E.injective
        rw [MulEquiv.apply_symm_apply]
        show ι (e (e.symm (QuotientGroup.mk s))) = _
        rw [MulEquiv.apply_symm_apply]
        rfl
      change e (α (e.symm (QuotientGroup.mk s))) = QuotientGroup.mk s
      rw [h3, h2]
      show e (E.symm (proj 2 (GaloisField q.p q.exponent) s)) = _
      rw [← h3, MulEquiv.apply_symm_apply]
    exact (MulAut.congr e).injective (by rw [h1, map_one])

end CFSG.HardMathSupport.Timmesfeld.DefChar
