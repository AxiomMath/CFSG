module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLieClRankFourSL4

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.LocalAnalysis.RankThreeUC.S15
open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.ComponentClassification.OddSelector (conjAut_mem_inner exists_conjAut_of_mem_inner
  eq_of_conjAut_eq_normalForm fieldAut_conj_conjAut)
open CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL (mem_semilinearAutGroup_of_odd)

namespace LieClAut

variable {K : Type} [Field K] {m : ℕ}

theorem conjAut_mul_fieldAut_pow (B : GL (Fin m) K) (σ : K ≃+* K) (k : ℕ) :
    ∃ B' : GL (Fin m) K,
      (conjAut m K B * fieldAut m K σ) ^ k = conjAut m K B' * fieldAut m K (σ ^ k) := by
  induction k with
  | zero => exact ⟨1, by simp⟩
  | succ k ih =>
    obtain ⟨B', hB'⟩ := ih
    refine ⟨B' * GeneralLinearGroup.map ((σ ^ k : K ≃+* K) : K →+* K) B, ?_⟩
    have hc := fieldAut_conj_conjAut (m := m) (σ ^ k) B
    rw [pow_succ, hB', pow_succ σ k, map_mul (fieldAut m K), map_mul (conjAut m K), ← hc]
    group

theorem exists_rankFour_psl_diag {X A : Type} [Group X] [Finite X] [Finite K]
    [CommGroup A] [Finite A] (hm : 3 ≤ m) (h3 : ¬ 3 ∣ Nat.card Kˣ)
    (e : X ≃* projectiveSL m K) (hc : center X = ⊥)
    {H : Subgroup (MulAut X)} (hinn : (MulAut.conj : X →* MulAut X).range ≤ H) {α : MulAut X}
    (hαH : α ∈ H) (hα : ∃ k : ℕ, α ^ 3 ^ k = 1)
    (hαn : α ∉ (MulAut.conj : X →* MulAut X).range) (δ : Kˣ →* GL (Fin m) K)
    (hδdet : ∀ a, GeneralLinearGroup.det (δ a) = a)
    (hδmap : ∀ (σ : K ≃+* K) (a : Kˣ), ∃ b, GeneralLinearGroup.map (σ : K →+* K) (δ a) = δ b)
    (f : A →* SpecialLinearGroup (Fin m) K)
    (hf : Function.Injective ((proj m K).comp f)) (hA3 : ∀ a : A, a ^ 3 = 1)
    (hA : Nat.card A = 27)
    (hfix : ∀ τ : K ≃+* K, τ ^ 3 = 1 → ∀ a, SpecialLinearGroup.map τ.toRingHom (f a) = f a)
    (hδf : ∀ a x, δ a * SpecialLinearGroup.toGL (f x) = SpecialLinearGroup.toGL (f x) * δ a) :
    ∃ F : Subgroup (MulAut X), F ≤ H ∧ IsElemAbelian 3 F ∧ Nat.card F = 81 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := projectiveSL m K
  set Ψ : MulAut X ≃* MulAut P := MulAut.congr e with hΨ
  have hΨconj : ∀ x : X, Ψ (MulAut.conj x) = MulAut.conj (e x) := fun x => by
    ext p
    simp [hΨ]
  have hΨinv : ∀ p : P, Ψ.symm (MulAut.conj p) = MulAut.conj (e.symm p) := fun p => by
    rw [MulEquiv.symm_apply_eq, hΨconj, e.apply_symm_apply]
  have hinnΨ : ∀ β, β ∈ (MulAut.conj : X →* MulAut X).range → Ψ β ∈ inner P := by
    rintro _ ⟨x, rfl⟩
    exact ⟨e x, (hΨconj x).symm⟩
  have hinnΨ' : ∀ γ, γ ∈ inner P → Ψ.symm γ ∈ (MulAut.conj : X →* MulAut X).range := by
    rintro _ ⟨p, rfl⟩
    exact ⟨e.symm p, (hΨinv p).symm⟩
  have hpowδ : ∀ (a : Kˣ) (τ : K ≃+* K) (k : ℕ), ∃ b : Kˣ,
      (conjAut m K (δ a) * fieldAut m K τ) ^ k = conjAut m K (δ b) * fieldAut m K (τ ^ k) := by
    intro a τ k
    induction k with
    | zero => exact ⟨1, by simp⟩
    | succ k ih =>
      obtain ⟨b, hb⟩ := ih
      obtain ⟨b', hb'⟩ := hδmap (τ ^ k) a
      refine ⟨b * b', ?_⟩
      have hc := fieldAut_conj_conjAut (m := m) (τ ^ k) (δ a)
      rw [hb'] at hc
      rw [pow_succ, hb, pow_succ τ k, map_mul (fieldAut m K), map_mul δ, map_mul (conjAut m K),
        ← hc]
      group
  obtain ⟨k, hk⟩ := hα
  have hodd : Odd (orderOf (Ψ α)) := by
    rw [MulEquiv.orderOf_eq]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hk)
    rw [hj]
    exact Odd.pow (by decide)
  obtain ⟨B, φ, hBφ⟩ := mem_semilinearAutGroup_iff.1 (mem_semilinearAutGroup_of_odd hm hodd)
  have hΨk : (Ψ α) ^ 3 ^ k = 1 := by rw [← map_pow, hk, map_one]
  obtain ⟨Bk, hBk⟩ := conjAut_mul_fieldAut_pow B φ (3 ^ k)
  have hφk : φ ^ 3 ^ k = 1 :=
    (eq_one_of_conjAut_mul_fieldAut_eq_one hm Bk _ (by rw [← hBk, ← hBφ, hΨk])).1
  have hr : (Nat.card Kˣ).Coprime (3 ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm
  have hφ1 : φ ≠ 1 := by
    rintro rfl
    apply hαn
    rw [map_one, mul_one] at hBφ
    have h1 : conjAut m K (B ^ 3 ^ k) = 1 := by rw [map_pow, ← hBφ, hΨk]
    obtain ⟨c, hc⟩ :=
      (CFSG.ComponentClassification.UnbalancedCatalog.conjAut_eq_one_iff hm _).1 h1
    have hu : ((powCoprime hr).symm c) ^ 3 ^ k = c := by
      rw [← powCoprime_apply hr]
      exact (powCoprime hr).apply_symm_apply c
    have hsc : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin m) c) = c ^ m :=
      Units.ext (by simp [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_scalar,
        scalar_apply, det_diagonal])
    have hdet : GeneralLinearGroup.det B = ((powCoprime hr).symm c) ^ m := by
      apply (powCoprime hr).injective
      rw [powCoprime_apply, powCoprime_apply, ← map_pow, ← hc, hsc, ← pow_mul, mul_comm,
        pow_mul, hu]
    have h2 : Ψ α ∈ inner P := by rw [hBφ]; exact conjAut_mem_inner hdet
    simpa using hinnΨ' _ h2
  obtain ⟨j, hjk, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hφk)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hφ1 (orderOf_eq_one_iff.1 (by rw [hjo, pow_zero]))
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = φ ^ 3 ^ (j - 1) := ⟨_, rfl⟩
  have hτ3 : τ ^ 3 = 1 := by
    rw [hτ, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hj0), ← hjo,
      pow_orderOf_eq_one]
  have hτ1 : τ ≠ 1 := by
    intro h
    have h1 := orderOf_dvd_of_pow_eq_one (h ▸ hτ).symm
    rw [hjo] at h1
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).1 h1
    omega
  obtain ⟨B', hB'⟩ := conjAut_mul_fieldAut_pow B φ (3 ^ (j - 1))
  rw [← hτ, ← hBφ] at hB'
  obtain ⟨a, ha⟩ : ∃ a, a = GeneralLinearGroup.det B' := ⟨_, rfl⟩
  have hY : GeneralLinearGroup.det (B'⁻¹ * δ a) = 1 ^ m := by
    rw [one_pow, map_mul, map_inv, hδdet, ha, inv_mul_cancel]
  obtain ⟨ψ, hψdef⟩ : ∃ ψ, ψ = conjAut m K (δ a) * fieldAut m K τ := ⟨_, rfl⟩
  have hψ : ψ = (Ψ α) ^ 3 ^ (j - 1) *
      ((fieldAut m K τ)⁻¹ * conjAut m K (B'⁻¹ * δ a) * fieldAut m K τ) := by
    rw [hψdef, hB']
    simp only [map_mul, map_inv]
    group
  haveI := inner_normal P
  have hψH : Ψ.symm ψ ∈ H := by
    rw [hψ, map_mul, map_pow, Ψ.symm_apply_apply]
    refine H.mul_mem (H.pow_mem hαH _) (hinn (hinnΨ' _ ?_))
    have h := (inner_normal P).conj_mem _ (conjAut_mem_inner hY) (fieldAut m K τ)⁻¹
    rwa [inv_inv] at h
  obtain ⟨b3, hb3⟩ := hpowδ a τ 3
  rw [hτ3, map_one, mul_one, ← hψdef] at hb3
  obtain ⟨br, hbr⟩ := hpowδ a τ (Nat.card Kˣ)
  rw [← hψdef] at hbr
  have hβ3 : ((Ψ.symm ψ) ^ Nat.card Kˣ) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, ← map_pow, hb3, ← map_pow, ← map_pow, ← map_pow,
      pow_card_eq_one', map_one, map_one, map_one]
  have hβn : (Ψ.symm ψ) ^ Nat.card Kˣ ∉ (MulAut.conj : X →* MulAut X).range := fun h => by
    have h1 := hinnΨ _ h
    rw [map_pow, Ψ.apply_symm_apply, hbr] at h1
    obtain ⟨Z, hZ⟩ := exists_conjAut_of_mem_inner h1
    have h2 := (eq_of_conjAut_eq_normalForm hm (Nat.zero_le 1) (X := SpecialLinearGroup.toGL Z)
      (B := δ br) (τ := τ ^ Nat.card Kˣ) (by rw [pow_zero, mul_one, ← hZ])).1
    apply h3
    rw [← orderOf_eq_prime hτ3 hτ1]
    exact orderOf_dvd_of_pow_eq_one h2
  have hψfix : ∀ x, ψ (proj m K (f x)) = proj m K (f x) := fun x => by
    rw [hψdef, MulAut.mul_apply, fieldAut_proj, hfix τ hτ3, conjAut_proj]
    congr 1
    refine Subtype.ext ?_
    rw [coe_slConjugation]
    have h1 : δ a * SpecialLinearGroup.toGL (f x) * (δ a)⁻¹ = SpecialLinearGroup.toGL (f x) := by
      rw [hδf, mul_inv_cancel_right]
    have h2 := congrArg (fun g : GL (Fin m) K => (g : Matrix (Fin m) (Fin m) K)) h1
    simpa using h2
  have hpowfix : ∀ (γ : MulAut X) (y : X), γ y = y → ∀ n : ℕ, (γ ^ n) y = y := by
    intro γ y hy n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, MulAut.mul_apply, hy, ih]
  refine exists_rankFour_of_fixed hc hinn (H.pow_mem hψH _) hβ3 hβn
    (e.symm.toMonoidHom.comp ((proj m K).comp f)) (e.symm.injective.comp hf) hA3 hA
    fun x => hpowfix _ _ ?_ _
  simp only [hΨ, MulAut.congr_symm_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, MulEquiv.trans_apply]
  rw [hψfix]

end LieClAut

namespace SpE27

variable {K : Type} [Field K]

def e7 : Fin 1 ⊕ Fin 6 ≃ Fin 7 := finSumFinEquiv

@[expose] def blk (c : K) (M : Matrix (Fin 6) (Fin 6) K) : Matrix (Fin 7) (Fin 7) K :=
  (fromBlocks (diagonal fun _ => c) 0 0 M).submatrix e7.symm e7.symm

theorem blk_mul (c d : K) (M N : Matrix (Fin 6) (Fin 6) K) :
    blk c M * blk d N = blk (c * d) (M * N) := by
  rw [blk, blk, blk, submatrix_mul_equiv, fromBlocks_multiply]
  simp [diagonal_mul_diagonal]

theorem blk_one : blk (1 : K) 1 = 1 := by
  rw [blk, show (diagonal fun _ => (1 : K) : Matrix (Fin 1) (Fin 1) K) = 1 from rfl,
    fromBlocks_one, submatrix_one_equiv]

theorem det_blk (c : K) (M : Matrix (Fin 6) (Fin 6) K) : (blk c M).det = c * M.det := by
  rw [blk, det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_diagonal, Fin.prod_univ_one]

theorem blk_map (σ : K ≃+* K) (c : K) (M : Matrix (Fin 6) (Fin 6) K) :
    (blk c M).map σ = blk (σ c) (M.map σ) := by
  rw [blk, blk, ← submatrix_map, fromBlocks_map, diagonal_map (map_zero σ)]
  simp

theorem blk_apply_inr (c : K) (M : Matrix (Fin 6) (Fin 6) K) (i j : Fin 6) :
    blk c M (e7 (Sum.inr i)) (e7 (Sum.inr j)) = M i j := by
  simp [blk]

@[expose] noncomputable def delta7 : Kˣ →* GL (Fin 7) K where
  toFun a := ⟨blk (a : K) 1, blk (a⁻¹ : Kˣ) 1, by
    rw [blk_mul, Units.mul_inv, Matrix.one_mul, blk_one], by
    rw [blk_mul, Units.inv_mul, Matrix.one_mul, blk_one]⟩
  map_one' := Units.ext (by simp [blk_one])
  map_mul' a b := Units.ext (by
    change blk ((a * b : Kˣ) : K) 1 = blk (a : K) 1 * blk (b : K) 1
    rw [blk_mul, Units.val_mul, Matrix.one_mul])

theorem coe_delta7 (a : Kˣ) : ((delta7 a : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) =
    blk (a : K) 1 := rfl

theorem det_delta7 (a : Kˣ) : GeneralLinearGroup.det (delta7 a) = a :=
  Units.ext (by rw [GeneralLinearGroup.val_det_apply, coe_delta7, det_blk, det_one, mul_one])

theorem map_delta7 (σ : K ≃+* K) (a : Kˣ) :
    ∃ b, GeneralLinearGroup.map (σ : K →+* K) (delta7 a) = delta7 b :=
  ⟨Units.map (σ : K →+* K).toMonoidHom a, Units.ext (by
    rw [coe_delta7]
    change (blk (a : K) 1).map σ = _
    rw [blk_map, Matrix.map_one _ (map_zero σ) (map_one σ)]
    rfl)⟩

variable [CharP K 2]

@[expose] def m6 (v : Fin 3 → ZMod 3) : Matrix (Fin 6) (Fin 6) K :=
  (spE v).submatrix e6.symm e6.symm

@[expose] noncomputable def slE7 : Multiplicative (Fin 3 → ZMod 3) →* SpecialLinearGroup (Fin 7) K
    where
  toFun v := ⟨blk 1 (m6 v.toAdd), by rw [det_blk, one_mul, m6, det_submatrix_equiv_self, spE_det]⟩
  map_one' := Subtype.ext (by
    change blk 1 (m6 (0 : Fin 3 → ZMod 3)) = 1
    rw [m6, spE_zero, submatrix_one_equiv, blk_one])
  map_mul' v w := Subtype.ext (by
    change blk 1 (m6 (v.toAdd + w.toAdd)) = blk 1 (m6 v.toAdd) * blk 1 (m6 w.toAdd)
    rw [blk_mul, one_mul, m6, m6, m6, submatrix_mul_equiv, spE_mul])

theorem coe_slE7 (v : Multiplicative (Fin 3 → ZMod 3)) :
    ((slE7 v : SpecialLinearGroup (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) = blk 1 (m6 v.toAdd) :=
  rfl

theorem projSlE7_injective : Function.Injective ((proj 7 K).comp (slE7 (K := K))) := by
  refine (injective_iff_map_eq_one _).2 fun v hv => ?_
  obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 hv)
  have h0 : ∀ i, (cb (v.toAdd i) : K) = 0 := fun i => by
    have hne : e7 (Sum.inr (e6 (Sum.inl i))) ≠ e7 (Sum.inr (e6 (Sum.inr i))) := fun h =>
      Sum.inl_ne_inr (e6.injective (Sum.inr_injective (e7.injective h)))
    have h := congrArg (fun M : Matrix (Fin 7) (Fin 7) K =>
      M (e7 (Sum.inr (e6 (Sum.inl i)))) (e7 (Sum.inr (e6 (Sum.inr i))))) hc
    simp only [coe_slE7, blk_apply_inr, scalar_apply, diagonal_apply_ne _ hne] at h
    rw [← h]
    simp [m6, spE]
  exact Multiplicative.toAdd.injective (funext fun i => cb_eq_zero (h0 i))

theorem map_slE7 (τ : K ≃+* K) (v : Multiplicative (Fin 3 → ZMod 3)) :
    SpecialLinearGroup.map τ.toRingHom (slE7 v) = slE7 v := by
  refine Subtype.ext ?_
  change (blk 1 (m6 v.toAdd)).map τ = blk 1 (m6 v.toAdd)
  rw [blk_map, map_one, m6, ← submatrix_map, spE_map]

theorem delta7_comm (a : Kˣ) (v : Multiplicative (Fin 3 → ZMod 3)) :
    delta7 a * SpecialLinearGroup.toGL (slE7 v) = SpecialLinearGroup.toGL (slE7 v) * delta7 a :=
  Units.ext (by
    change blk (a : K) 1 * blk 1 (m6 v.toAdd) = blk 1 (m6 v.toAdd) * blk (a : K) 1
    rw [blk_mul, blk_mul, mul_one, Matrix.one_mul, one_mul, Matrix.mul_one])

end SpE27

@[expose] def KFactOuterThreeRankFourRestSL7 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (d : TauCeti.ValidLieTypeIndex), IsRankTwoPlus d.1 →
    RankThreeList d.1 → (∀ q : TauCeti.PrimePower, d.1 ≠ .B 3 q) →
    (∀ q : TauCeti.PrimePower, d.1 ≠ .A 5 q) → (∀ q : TauCeti.PrimePower, d.1 ≠ .A 3 q) →
    (∀ q : TauCeti.PrimePower, d.1 ≠ .A 6 q) → LieClAut.FieldExponentThree d.1 →
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group) → Subgroup.center X = ⊥ →
    ∀ H : Subgroup (MulAut X),
    (MulAut.conj : X →* MulAut X).range ≤ H →
    (∃ α ∈ H, (∃ k : ℕ, α ^ 3 ^ k = 1) ∧ α ∉ (MulAut.conj : X →* MulAut X).range) →
    ∃ F : Subgroup (MulAut X), F ≤ H ∧ IsElemAbelian 3 F ∧ Nat.card F = 81

theorem kFactOuterThreeRankFourRestSL4_of_sl7 (h : KFactOuterThreeRankFourRestSL7) :
    KFactOuterThreeRankFourRestSL4 := by
  classical
  intro X _ _ d hd hl hB hA5 hA3 h3 he hc H hinn hα
  by_cases hA : ∀ q : TauCeti.PrimePower, d.1 ≠ .A 6 q
  · exact h X d hd hl hB hA5 hA3 hA h3 he hc H hinn hα
  push Not at hA
  obtain ⟨q, hq⟩ := hA
  obtain ⟨d, hv⟩ := d
  simp only at hq
  subst hq
  obtain ⟨e⟩ := he
  have hp : q.p = 2 := hd.1
  have hodd : Odd q.exponent := hl
  obtain ⟨_, K, _, _, hK, ⟨e'⟩⟩ := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
  rw [hp] at hK
  haveI := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have h3K : ¬ 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
    have h3 : 2 ^ q.exponent % 3 = 2 := by
      obtain ⟨k, hk⟩ := hodd
      rw [hk, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    omega
  let b : projectiveSL 7 K ≃* StatedProj (StatedSL 7 K) :=
    (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 7 K)).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 7 K)
  obtain ⟨α, hαH, hαk, hαn⟩ := hα
  exact LieClAut.exists_rankFour_psl_diag (m := 7) (by norm_num) h3K (e'.trans b.symm) hc hinn
    hαH hαk hαn SpE27.delta7 SpE27.det_delta7 SpE27.map_delta7 SpE27.slE7
    SpE27.projSlE7_injective SpE27.pow_three_eq_one SpE27.card_e27
    (fun τ _ a => SpE27.map_slE7 τ a) SpE27.delta7_comm

theorem kFactTenElevenOneLieAutRes_of_rankFourSL7
    (hK : KFactOuterThreeRankFourRestSL7) (h2 : KFactTenElevenOneLieAutFieldTwo) :
    KFactTenElevenOneLieAutRes :=
  kFactTenElevenOneLieAutRes_of_rankFourSL4 (kFactOuterThreeRankFourRestSL4_of_sl7 hK) h2

end CFSG.LocalAnalysis.RankThreeTheoremC
