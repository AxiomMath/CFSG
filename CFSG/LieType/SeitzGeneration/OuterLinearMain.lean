module

public import CFSG.LieType.SeitzGeneration.OuterLinearLift
public import CFSG.LieType.SeitzGeneration.OuterLinearTight
public import CFSG.LieType.SeitzGeneration.OuterRank2
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.LieType.SeitzGeneration.OuterLinearPlane
public import CFSG.LieType.SeitzGeneration.OuterModel

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartOne.KCLinComm

section Plane

variable {P : Type*} [Group P] {p : ℕ}

theorem exists_inner_fixed {E : Subgroup (MulAut P)} (hE : IsElemAbelian p E)
    (hinj : Function.Injective (MulAut.conj : P →* MulAut P))
    (hne : E ⊓ (MulAut.conj : P →* MulAut P).range ≠ ⊥) {f : MulAut P} (hf : f ∈ E) :
    ∃ g : P, g ≠ 1 ∧ g ^ p = 1 ∧ MulAut.conj g ∈ E ∧ f g = g := by
  obtain ⟨⟨c, hc⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨hcE, g, rfl⟩ := hc
  have hg1 : g ≠ 1 := fun h => hc1 (Subtype.ext (by simp [h]))
  have hgp : g ^ p = 1 := hinj (by rw [map_pow, hE.2 _ hcE, map_one])
  have hcomm : f * MulAut.conj g = MulAut.conj g * f :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨f, hf⟩ ⟨MulAut.conj g, hcE⟩)
  refine ⟨g, hg1, hgp, hcE, hinj ?_⟩
  rw [← mulAut_mul_conj_mul_inv, hcomm, mul_inv_cancel_right]

theorem congr_inv_apply (h φ : MulAut P) : MulAut.congr h⁻¹ φ = h⁻¹ * φ * h := rfl

end Plane

section Pair

variable {n : ℕ} {K : Type} [Field K]

theorem slEq_of_coe_eq {R : Type*} [CommRing R] {A B : SpecialLinearGroup (Fin n) R}
    (h : (A : Matrix (Fin n) (Fin n) R) = B) : A = B :=
  Matrix.SpecialLinearGroup.ext A B fun i => congrFun (congrFun h i)

theorem exists_matrix_over_subfield {k : Subfield K} {σ : K ≃+* K}
    (hk : ∀ x, x ∈ k ↔ σ x = x) {M : Matrix (Fin n) (Fin n) K} (hM : M.map σ = M) :
    ∃ G : Matrix (Fin n) (Fin n) k, G.map k.subtype = M := by
  refine ⟨Matrix.of fun i j => ⟨M i j, (hk _).mpr (by simpa using congrFun (congrFun hM i) j)⟩, ?_⟩
  ext i j
  rfl

theorem exists_fixed_pair_of_noEigen [Finite K] {k : Subfield K} {σ : K ≃+* K}
    (hk : ∀ x, x ∈ k ↔ σ x = x) {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0) (hnp : p ≤ n)
    {Ĝ : Matrix (Fin n) (Fin n) K} (hĜσ : Ĝ.map σ = Ĝ) (hĜp : Ĝ ^ p = 1)
    (hev : ∀ (w : Fin n → K) (lam : K), (∀ i, w i ∈ k) → lam ∈ k → Ĝ *ᵥ w = lam • w → w = 0) :
    ∃ α β : projectiveSL n K, Commute α β ∧ α ^ p = 1 ∧ β ^ p = 1 ∧
      (∀ i j : ℤ, α ^ i * β ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j) ∧
      fieldAut n K σ α = α ∧ fieldAut n K σ β = β := by
  classical
  have hn0 : 0 < n := lt_of_lt_of_le hp.pos hnp
  obtain ⟨G, hGK⟩ := exists_matrix_over_subfield hk hĜσ
  have hmapG : k.subtype.mapMatrix G = Ĝ := hGK
  have hGp : G ^ p = 1 := by
    apply Matrix.map_injective k.subtype.injective
    show k.subtype.mapMatrix (G ^ p) = k.subtype.mapMatrix 1
    rw [map_pow, map_one, hmapG, hĜp]
  have hB : ∀ (v : Fin n → k) (lam : k), G *ᵥ v = lam • v → v = 0 := by
    intro v lam hv
    have hw : (fun i => (v i : K)) = 0 := by
      refine hev (fun i => (v i : K)) lam (fun i => (v i).2) lam.2 ?_
      funext i
      have h1 := RingHom.map_mulVec k.subtype G v i
      have h2 : (Ĝ *ᵥ fun i => (v i : K)) i = k.subtype ((G *ᵥ v) i) := by
        rw [h1, ← hGK]
        rfl
      rw [h2, hv]
      simp
    funext i
    exact Subtype.ext (congrFun hw i)
  have hpk : (p : k) ≠ 0 := fun h => hpK (by simpa using congrArg k.subtype h)
  obtain ⟨A, B, hAp, hBp, hAB, hdA, hdB, hind⟩ := exists_split_pair_matrix hp hpk G hGp hB hnp
  obtain ⟨Asl, hAsl⟩ : ∃ S : SpecialLinearGroup (Fin n) k, (S : Matrix (Fin n) (Fin n) k) = A :=
    ⟨⟨A, hdA⟩, rfl⟩
  obtain ⟨Bsl, hBsl⟩ : ∃ S : SpecialLinearGroup (Fin n) k, (S : Matrix (Fin n) (Fin n) k) = B :=
    ⟨⟨B, hdB⟩, rfl⟩
  let X : SpecialLinearGroup (Fin n) k →* SpecialLinearGroup (Fin n) K :=
    Matrix.SpecialLinearGroup.map k.subtype
  have hAslp : Asl ^ p = 1 := slEq_of_coe_eq (by
    rw [Matrix.SpecialLinearGroup.coe_pow, hAsl, hAp, Matrix.SpecialLinearGroup.coe_one])
  have hBslp : Bsl ^ p = 1 := slEq_of_coe_eq (by
    rw [Matrix.SpecialLinearGroup.coe_pow, hBsl, hBp, Matrix.SpecialLinearGroup.coe_one])
  have hcomm : Commute Asl Bsl := slEq_of_coe_eq (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hAsl, hBsl, hAB])
  have hfix : ∀ S : SpecialLinearGroup (Fin n) k, fieldAut n K σ (proj n K (X S)) =
      proj n K (X S) := by
    intro S
    rw [fieldAut_proj]
    congr 1
    apply Subtype.ext
    ext i j
    simp [X, Matrix.SpecialLinearGroup.map_apply_coe, (hk _).mp (S i j).2]
  refine ⟨proj n K (X Asl), proj n K (X Bsl), (hcomm.map X).map (proj n K), ?_, ?_, ?_,
    hfix Asl, hfix Bsl⟩
  · rw [← map_pow, ← map_pow, hAslp, map_one, map_one]
  · rw [← map_pow, ← map_pow, hBslp, map_one, map_one]
  · intro i j hij
    have hαp : proj n K (X Asl) ^ p = 1 := by
      rw [← map_pow, ← map_pow, hAslp, map_one, map_one]
    have hβp : proj n K (X Bsl) ^ p = 1 := by
      rw [← map_pow, ← map_pow, hBslp, map_one, map_one]
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    set i₀ := (i % (p : ℤ)).toNat with hi₀
    set j₀ := (j % (p : ℤ)).toNat with hj₀
    have hi₀' : (i₀ : ℤ) = i % (p : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ hp0)
    have hj₀' : (j₀ : ℤ) = j % (p : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ hp0)
    have hi₀p : i₀ < p := by
      have := Int.emod_lt_of_pos i (by exact_mod_cast hp.pos : (0 : ℤ) < p)
      omega
    have hj₀p : j₀ < p := by
      have := Int.emod_lt_of_pos j (by exact_mod_cast hp.pos : (0 : ℤ) < p)
      omega
    rw [zpow_eq_zpow_emod' i hαp, zpow_eq_zpow_emod' j hβp, ← hi₀', ← hj₀', zpow_natCast,
      zpow_natCast] at hij
    have hmem : X (Asl ^ i₀ * Bsl ^ j₀) ∈ scalars n K := by
      rw [← proj_eq_one_iff]
      simpa [map_mul, map_pow] using hij
    obtain ⟨c, -, hc⟩ := hmem
    set M : Matrix (Fin n) (Fin n) k := A ^ i₀ * B ^ j₀ with hM
    have hXc : M.map k.subtype = scalar (Fin n) (c : K) := by
      have hcoe : ((Asl ^ i₀ * Bsl ^ j₀ : SpecialLinearGroup (Fin n) k) :
          Matrix (Fin n) (Fin n) k) = M := by
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow,
          Matrix.SpecialLinearGroup.coe_pow, hAsl, hBsl]
      rw [← hc, Matrix.SpecialLinearGroup.map_apply_coe, hcoe]
      rfl
    have hscal : ∃ c₀ : k, A ^ i₀ * B ^ j₀ = c₀ • (1 : Matrix (Fin n) (Fin n) k) := by
      refine ⟨M ⟨0, hn0⟩ ⟨0, hn0⟩, ?_⟩
      rw [← hM]
      ext a b
      have h1 := congrFun (congrFun hXc a) b
      have h00 := congrFun (congrFun hXc ⟨0, hn0⟩) ⟨0, hn0⟩
      simp only [Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply] at h1 h00
      by_cases hab : a = b
      · subst hab
        have : M a a = M ⟨0, hn0⟩ ⟨0, hn0⟩ := k.subtype.injective (by
          simp only [ite_true] at h1 h00
          exact h1.trans h00.symm)
        simp [this]
      · simp only [hab, ite_false] at h1
        have : M a b = 0 := k.subtype.injective (by simpa using h1)
        simp [this, hab]
    obtain ⟨hi0, hj0⟩ := hind i₀ j₀ hi₀p hj₀p hscal
    refine ⟨Int.dvd_of_emod_eq_zero ?_, Int.dvd_of_emod_eq_zero ?_⟩
    · rw [← hi₀', hi0]
      rfl
    · rw [← hj₀', hj0]
      rfl

end Pair

section Normalized

variable {n : ℕ} {K : Type} [Field K]

theorem exists_fixed_vector_lift {k : Subfield K} {σ : K ≃+* K} (hk : ∀ x, x ∈ k ↔ σ x = x)
    {p : ℕ} {Ĝ : GL (Fin n) K} (hĜσ : (Ĝ : Matrix (Fin n) (Fin n) K).map σ = Ĝ)
    (hĜp : (Ĝ : Matrix (Fin n) (Fin n) K) ^ p = 1) {w : Fin n → K} (hw0 : w ≠ 0) {lam : K}
    (hlam : lam ∈ k) (hw : (Ĝ : Matrix (Fin n) (Fin n) K) *ᵥ w = lam • w) :
    ∃ Ĝ' : GL (Fin n) K, conjAut n K Ĝ' = conjAut n K Ĝ ∧
      (Ĝ' : Matrix (Fin n) (Fin n) K).map σ = Ĝ' ∧ (Ĝ' : Matrix (Fin n) (Fin n) K) ^ p = 1 ∧
      (Ĝ' : Matrix (Fin n) (Fin n) K) *ᵥ w = w := by
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    apply hw0
    have h1 := congrArg (fun v => ((Ĝ⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) hw
    simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using h1
  have hlamp : lam ^ p = 1 := by
    have h1 : ∀ m : ℕ, ((Ĝ : Matrix (Fin n) (Fin n) K) ^ m) *ᵥ w = lam ^ m • w := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hw, smul_smul, pow_succ]
    have h2 := h1 p
    rw [hĜp, Matrix.one_mulVec] at h2
    have h3 : (lam ^ p - 1) • w = 0 := by rw [sub_smul, ← h2, one_smul, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hw0
  have hlamσ : σ lam = lam := (hk _).mp hlam
  have hcoe : ((GeneralLinearGroup.scalar (Fin n) (Units.mk0 lam⁻¹ (inv_ne_zero hlam0)) * Ĝ :
      GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = lam⁻¹ • (Ĝ : Matrix (Fin n) (Fin n) K) := by
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.smul_eq_diagonal_mul]
    rfl
  refine ⟨GeneralLinearGroup.scalar (Fin n) (Units.mk0 lam⁻¹ (inv_ne_zero hlam0)) * Ĝ, ?_, ?_, ?_,
    ?_⟩
  · rw [map_mul, conjAut_scalar, one_mul]
  · rw [hcoe]
    ext i j
    have hij : σ ((Ĝ : Matrix (Fin n) (Fin n) K) i j) = (Ĝ : Matrix (Fin n) (Fin n) K) i j := by
      simpa [Matrix.map_apply] using congrFun (congrFun hĜσ i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hij, map_inv₀, hlamσ]
  · rw [hcoe, smul_pow, hĜp, inv_pow, hlamp, inv_one, one_smul]
  · rw [hcoe, Matrix.smul_mulVec, hw, smul_smul, inv_mul_cancel₀ hlam0, one_smul]

theorem planeGen_of_normalized [Finite K] (hpair : SubfieldPairSLLt) {k : Subfield K} {ℓ e : ℕ}
    {σ : K ≃+* K} (hk : ∀ x, x ∈ k ↔ σ x = x) {p : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (he : 1 ≤ e)
    (hK' : Nat.card K = ℓ ^ e) (hσ : orderOf σ = p) (hK : Nat.card K = Nat.card k ^ p)
    (hpK : (p : K) ≠ 0) (hn : 3 ≤ n) (hpow : ¬ p ∣ n ∨ ¬ p ∣ Nat.card k - 1)
    {E : Subgroup (MulAut (projectiveSL n K))} (hs : NarrowScope p E)
    (hσE : fieldAut n K σ ∈ E) (hσout : ∀ x, fieldAut n K σ ≠ MulAut.conj x)
    {g : projectiveSL n K} (hg1 : g ≠ 1) (hgp : g ^ p = 1) (hgE : MulAut.conj g ∈ E)
    (hgσ : fieldAut n K σ g = g) : PlaneGen E := by
  classical
  have hinj := CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (k := K) hn
  obtain ⟨Ĝ₀, hĜ₀, hĜ₀σ⟩ := exists_rational_lift hp hℓ he hK' σ hσ (by omega) hgσ
  obtain ⟨Ĝ, hĜ, hĜσ, hĜp⟩ := exists_normalized_lift hp σ hk hn hpow hgp hĜ₀ hĜ₀σ
  by_cases hev : ∃ (w : Fin n → K) (lam : K), (∀ i, w i ∈ k) ∧ w ≠ 0 ∧ lam ∈ k ∧
      (Ĝ : Matrix (Fin n) (Fin n) K) *ᵥ w = lam • w
  · obtain ⟨w, lam, hwk, hw0, hlam, hw⟩ := hev
    obtain ⟨Ĝ', hĜ', hĜ'σ, hĜ'p, hĜ'w⟩ := exists_fixed_vector_lift hk hĜσ hĜp hw0 hlam hw
    have hĜ'1 : (Ĝ' : Matrix (Fin n) (Fin n) K) ≠ 1 := by
      intro h1
      apply hg1
      apply hinj
      rw [map_one, ← hĜ, ← hĜ', show Ĝ' = 1 from Units.ext h1, map_one]
    exact planeGen_of_eigenvector σ hk hp hℓ he hK' hσ hK hpK hn hσE hσout hgE (hĜ'.trans hĜ)
      hĜ'σ hĜ'p hĜ'1 hwk hw0 hĜ'w
  · push Not at hev
    have hev' : ∀ (w : Fin n → K) (lam : K), (∀ i, w i ∈ k) → lam ∈ k →
        (Ĝ : Matrix (Fin n) (Fin n) K) *ᵥ w = lam • w → w = 0 :=
      fun w lam hwk hlam h => by_contra fun hw0 => hev w lam hwk hw0 hlam h
    by_cases hnp : n < p
    · refine planeGen_of_pair hpair σ hk hp hℓ he hK' hσ hK hn hnp hσE hσout hgE hĜ hĜσ hĜp ?_
      intro c hc
      have hi₀ : 0 < n := by omega
      set i₀ : Fin n := ⟨0, hi₀⟩ with hi₀def
      have hck : c ∈ k := by
        have h1 := congrFun (congrFun hĜσ i₀) i₀
        have h2 : (Ĝ : Matrix (Fin n) (Fin n) K) i₀ i₀ = c := by simp [hc]
        rw [Matrix.map_apply, h2] at h1
        exact (hk _).mpr h1
      have hwk : ∀ i, (Pi.single i₀ (1 : K) : Fin n → K) i ∈ k := by
        intro i
        by_cases h : i = i₀
        · subst h
          simp [k.one_mem]
        · simp [h, k.zero_mem]
      have h0 := hev' (Pi.single i₀ 1) c hwk hck (by
        rw [hc, Matrix.smul_mulVec, Matrix.one_mulVec])
      have := congrFun h0 i₀
      simp at this
    · exfalso
      obtain ⟨α, β, hcomm, hα, hβ, hind, hfα, hfβ⟩ :=
        exists_fixed_pair_of_noEigen hk hp hpK (not_lt.mp hnp) hĜσ hĜp hev'
      have hσp : σ ^ p = 1 := by
        rw [← hσ]
        exact pow_orderOf_eq_one σ
      exact NarrowScope.false_of_fixed_pair hp hinj hs hσE (by rw [← map_pow, hσp, map_one])
        hσout hcomm hα hβ hind hfα hfβ

end Normalized

section Main

variable {n : ℕ} {K : Type} [Field K] [Finite K]

open CFSG.RankThree.PartOne (innSL)
open CFSG.RankThree.PartOne.KCLinPlane
  (inner_of_mem_linearAut_of_pow_eq_one card_inf_inner_eq_prime)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem planeGen_projectiveSL_outer (hpair : SubfieldPairSLLt) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpℓ : p ≠ ℓ) (hcop : Nat.Coprime p (Nat.gcd n (Nat.card K - 1)))
    {E : Subgroup (MulAut (projectiveSL n K))} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hout : ¬ E ≤ innSL n K) (hs : NarrowScope p E) : PlaneGen E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hinj := CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (k := K) hn
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have hpK : (p : K) ≠ 0 := fun h =>
    hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp ((CharP.cast_eq_zero_iff K ℓ p).mp h)).symm
  have hpA : ∀ a ∈ E, a ^ p = 1 := hE.2
  have hAE : E ≤ (semilinPsi n K).range := fun α hα => by
    rw [range_semilinPsi]
    exact CFSG.RankThree.PartOne.KCLinCommOdd.mem_semilinearAutGroup_of_pow_eq_one hn hp2 hp
      (j := 1) (by simpa using hpA α hα)
  have hcyc : IsCyclic (K ≃+* K) := by
    obtain ⟨σ, -, -, htop, -⟩ := finite_field_automorphism_fixed_field_cardinality hℓ hf hK
    exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ, htop⟩
  have : IsElementaryAbelian p E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).mpr hE
  have hAcap := card_inf_inner_eq_prime hn hp hcop hcyc hAE hc hout
  have hne0 : E ⊓ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hAcap
    exact hp.one_lt.ne hAcap
  obtain ⟨a0, ha0E, ha0H⟩ := IsConcreteLE.not_le_iff_exists.mp hout
  have ha0p : orderOf a0 = p :=
    orderOf_eq_prime (hpA a0 ha0E) (fun h => ha0H (h ▸ one_mem _))
  have ha0D : a0 ∉ linearAutGroup n K := fun hD =>
    ha0H (inner_of_mem_linearAut_of_pow_eq_one hn hcop hD (hpA a0 ha0E))
  have ha0S : a0 ∈ semilinearAutGroup n K := by
    rw [← range_semilinPsi]
    exact hAE ha0E
  obtain ⟨-, -, -, -, -, -, -, hdesc⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent hℓ hf hn hK
  obtain ⟨hpf, σ, hσ, ⟨h, -, hha⟩, hkcard⟩ := hdesc p hp hpℓ a0 ha0S ha0D ha0p
  set k : Subfield K := semilinearFixedSubfield σ with hkdef
  have hk : ∀ x, x ∈ k ↔ σ x = x := fun x => Iff.rfl
  have hKk : Nat.card K = Nat.card k ^ p := by
    rw [hK, hkcard, ← pow_mul, Nat.div_mul_cancel hpf]
  have hpow : ¬ p ∣ n ∨ ¬ p ∣ Nat.card k - 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    refine (Nat.Prime.coprime_iff_not_dvd hp).mp hcop (Nat.dvd_gcd h1 ?_)
    rw [hKk]
    exact h2.trans (by simpa using Nat.sub_dvd_pow_sub_pow (Nat.card k) 1 p)
  have hcongr : ∀ φ : MulAut (projectiveSL n K), MulAut.congr h⁻¹ φ = h⁻¹ * φ * h :=
    fun φ => congr_inv_apply h φ
  obtain ⟨g, hg1, hgp, hgE, ha0g⟩ := exists_inner_fixed hE hinj hne0 ha0E
  have hfa : MulAut.congr h⁻¹ a0 = fieldAut n K σ := by
    rw [hcongr, hha]
    group
  have hσE : fieldAut n K σ ∈ E.map (MulAut.congr h⁻¹).toMonoidHom := ⟨a0, ha0E, hfa⟩
  have hσout : ∀ x, fieldAut n K σ ≠ MulAut.conj x := by
    intro x hx
    refine ha0H ⟨h x, ?_⟩
    rw [← mulAut_mul_conj_mul_inv, ← hx, ← hha]
  have hg'1 : h⁻¹ g ≠ 1 := by
    intro h1
    apply hg1
    have h2 : h (h⁻¹ g) = g := by simp
    rw [← h2, h1, map_one]
  have hg'p : (h⁻¹ g) ^ p = 1 := by rw [← map_pow, hgp, map_one]
  have hg'E : MulAut.conj (h⁻¹ g) ∈ E.map (MulAut.congr h⁻¹).toMonoidHom :=
    ⟨MulAut.conj g, hgE, by
      show MulAut.congr h⁻¹ (MulAut.conj g) = _
      rw [hcongr]
      simpa using mulAut_mul_conj_mul_inv h⁻¹ g⟩
  have hσg' : fieldAut n K σ (h⁻¹ g) = h⁻¹ g := by
    rw [← hfa, hcongr]
    simp [MulAut.mul_apply, ha0g]
  exact planeGen_of_outer_model h⁻¹ (planeGen_of_normalized hpair hk hp hℓ hf hK hσ hKk hpK hn hpow
    (hs.map_congr h⁻¹) hσE hσout hg'1 hg'p hg'E hσg')

end Main

end CFSG.LieType.SeitzGeneration
