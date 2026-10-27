module

public import CFSG.HardMathSupport.GuralnickMalle.Prop310
public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import CFSG.HardMathSupport.GuralnickMalle.FGeneral
public import CFSG.HardMathSupport.GuralnickMalle.Prop24General
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

open CFSG.Open CFSG.HardMathSupport.GuralnickMalle Module
open CFSG.LieType.Universal.Unitary (conjTr conjTr_add conjTr_sub conjTr_one SUid mem_SUid
  SUid_eq_statedSU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)

theorem conjTr_zero {K : Type} [Field K] {n : ℕ} (σ : K ≃+* K) :
    conjTr σ (0 : Matrix (Fin n) (Fin n) K) = 0 := by
  ext i j
  simp [conjTr]

theorem conjTr_smul {K : Type} [Field K] {n : ℕ} (σ : K ≃+* K) (c : K)
    (A : Matrix (Fin n) (Fin n) K) : conjTr σ (c • A) = σ c • conjTr σ A := by
  ext i j
  simp [conjTr, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem conjTr_sum_smul {K : Type} [Field K] {n : ℕ} (σ : K ≃+* K) {ι : Type} (s : Finset ι)
    (z : ι → K) (M : ι → Matrix (Fin n) (Fin n) K) (hM : ∀ i, conjTr σ (M i) = M i) :
    conjTr σ (∑ i ∈ s, z i • M i) = ∑ i ∈ s, σ (z i) • M i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [conjTr_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert (f := fun i => z i • M i) ha,
        Finset.sum_insert (f := fun i => σ (z i) • M i) ha, conjTr_add, conjTr_smul, hM a, ih]

@[expose] def unipotentMat {K : Type} [Field K] {n : ℕ} (a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  (a : Matrix (Fin n) (Fin n) K) - 1

@[expose] def unipotentMatAlgebra {K : Type} [Field K] {n : ℕ} (A : Subgroup (GL (Fin n) K)) :
    Submodule K (Matrix (Fin n) (Fin n) K) :=
  Submodule.span K (unipotentMat '' (A : Set (GL (Fin n) K)))

theorem unipotentMat_injective {K : Type} [Field K] {n : ℕ} :
    Function.Injective (unipotentMat (K := K) (n := n)) := by
  intro a b h
  refine Units.ext ?_
  have h' : (a : Matrix (Fin n) (Fin n) K) - 1 = (b : Matrix (Fin n) (Fin n) K) - 1 := by
    simpa only [unipotentMat] using h
  have := congrArg (fun M : Matrix (Fin n) (Fin n) K => M + 1) h'
  simpa using this

theorem conjTr_unipotentMat {K : Type} [Field K] {n : ℕ} (σ : K ≃+* K) {a : GL (Fin n) K}
    (huni : conjTr σ (a : Matrix (Fin n) (Fin n) K) * (a : Matrix (Fin n) (Fin n) K) = 1)
    (hsq : a * a = 1) :
    conjTr σ (unipotentMat a) = unipotentMat a := by
  have hmat_inv : (a : Matrix (Fin n) (Fin n) K) * ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 := by
    simpa using congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) (mul_inv_cancel a)
  have hga : (a⁻¹ : GL (Fin n) K) = a := by
    calc a⁻¹ = a⁻¹ * 1 := (mul_one _).symm
      _ = a⁻¹ * (a * a) := by rw [hsq]
      _ = (a⁻¹ * a) * a := by rw [mul_assoc]
      _ = a := by rw [inv_mul_cancel, one_mul]
  have hsa : conjTr σ (a : Matrix (Fin n) (Fin n) K) = (a : Matrix (Fin n) (Fin n) K) := by
    have h1 : conjTr σ (a : Matrix (Fin n) (Fin n) K) =
        ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      calc conjTr σ (a : Matrix (Fin n) (Fin n) K)
          = conjTr σ (a : Matrix (Fin n) (Fin n) K) *
              ((a : Matrix (Fin n) (Fin n) K) * ((a⁻¹ : GL (Fin n) K) : Matrix _ _ K)) := by
            rw [hmat_inv, mul_one]
        _ = (conjTr σ (a : Matrix (Fin n) (Fin n) K) * (a : Matrix (Fin n) (Fin n) K)) *
              ((a⁻¹ : GL (Fin n) K) : Matrix _ _ K) := by rw [mul_assoc]
        _ = ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [huni, one_mul]
    rw [h1, hga]
  rw [unipotentMat, conjTr_sub, conjTr_one, hsa]

theorem card_selfadjoint_le_pow_finrank {K : Type} [Field K] [Finite K] {n : ℕ} (σ : K ≃+* K)
    (q : ℕ) (hfix : Nat.card {c : K // σ c = c} ≤ q)
    {D : Submodule K (Matrix (Fin n) (Fin n) K)} {ι : Type} [Fintype ι] (b : Basis ι K D)
    (hb : ∀ i, conjTr σ ((b i : D) : Matrix (Fin n) (Fin n) K) = ((b i : D) : Matrix _ _ K)) :
    Nat.card {x : D // conjTr σ ((x : D) : Matrix (Fin n) (Fin n) K) =
      ((x : D) : Matrix (Fin n) (Fin n) K)} ≤ q ^ finrank K D := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hstar : ∀ z : ι → K,
      conjTr σ (↑(∑ i, z i • b i) : Matrix (Fin n) (Fin n) K) = ↑(∑ i, σ (z i) • b i) := by
    intro z
    have h1 : (↑(∑ i, z i • b i) : Matrix (Fin n) (Fin n) K) =
        ∑ i, z i • ((b i : D) : Matrix (Fin n) (Fin n) K) := by simp
    have h2 : (↑(∑ i, σ (z i) • b i) : Matrix (Fin n) (Fin n) K) =
        ∑ i, σ (z i) • ((b i : D) : Matrix (Fin n) (Fin n) K) := by simp
    rw [h1, h2]
    exact conjTr_sum_smul σ Finset.univ z
      (fun i => ((b i : D) : Matrix (Fin n) (Fin n) K)) fun i => hb i
  have hcoord : ∀ x : D,
      conjTr σ ((x : D) : Matrix (Fin n) (Fin n) K) = ((x : D) : Matrix _ _ K) →
        ∀ i, σ (b.equivFun x i) = b.equivFun x i := by
    intro x hx i
    have hx' : ((x : D) : Matrix (Fin n) (Fin n) K) = ↑(∑ i, b.equivFun x i • b i) := by
      rw [b.sum_equivFun x]
    have heq : (↑(∑ i, σ (b.equivFun x i) • b i) : Matrix (Fin n) (Fin n) K) =
        ↑(∑ i, b.equivFun x i • b i) := by
      rw [← hstar, ← hx', hx]
    have heqD : ∑ i, σ (b.equivFun x i) • b i = ∑ i, b.equivFun x i • b i := Subtype.ext heq
    have hzero : ∑ i, (σ (b.equivFun x i) - b.equivFun x i) • b i = 0 := by
      have h1 : ∀ i, (σ (b.equivFun x i) - b.equivFun x i) • b i =
          σ (b.equivFun x i) • b i - b.equivFun x i • b i :=
        fun i => sub_smul (σ (b.equivFun x i)) (b.equivFun x i) (b i)
      rw [Finset.sum_congr rfl fun i _ => h1 i,
        Finset.sum_sub_distrib (s := Finset.univ)
          (fun i => σ (b.equivFun x i) • b i) (fun i => b.equivFun x i • b i),
        heqD, sub_self]
    exact sub_eq_zero.mp
      ((Fintype.linearIndependent_iff.mp b.linearIndependent)
        (fun i => σ (b.equivFun x i) - b.equivFun x i) hzero i)
  have hinj : Function.Injective
      (fun x : {x : D // conjTr σ ((x : D) : Matrix (Fin n) (Fin n) K) =
          ((x : D) : Matrix _ _ K)} =>
        (⟨b.equivFun (x : D), hcoord (x : D) x.2⟩ : {z : ι → K // ∀ i, σ (z i) = z i})) := by
    intro x y hxy
    have h1 : b.equivFun (x : D) = b.equivFun (y : D) :=
      congrArg (fun z : {z : ι → K // ∀ i, σ (z i) = z i} => (z : ι → K)) hxy
    exact Subtype.ext (b.equivFun.injective h1)
  have hpos : 0 < Nat.card {c : K // σ c = c} := by
    haveI : Nonempty {c : K // σ c = c} := ⟨⟨0, map_zero σ⟩⟩
    exact Nat.card_pos
  calc Nat.card {x : D // conjTr σ ((x : D) : Matrix (Fin n) (Fin n) K) =
        ((x : D) : Matrix _ _ K)}
      ≤ Nat.card {z : ι → K // ∀ i, σ (z i) = z i} :=
        Nat.card_le_card_of_injective _ hinj
    _ = Nat.card {c : K // σ c = c} ^ Fintype.card ι := by
        rw [Nat.card_congr (Equiv.subtypePiEquivPi (p := fun (_ : ι) (c : K) => σ c = c))]
        rw [Nat.card_pi, Finset.prod_const, Finset.card_univ]
    _ ≤ q ^ Fintype.card ι := Nat.pow_le_pow_left hfix (Fintype.card ι)
    _ = q ^ finrank K D := by rw [← finrank_eq_card_basis b]

theorem card_selfadjoint_le_pow_finrank_of_span {K : Type} [Field K] [Finite K] {n : ℕ}
    (σ : K ≃+* K) (q : ℕ) (hfix : Nat.card {c : K // σ c = c} ≤ q)
    {D : Submodule K (Matrix (Fin n) (Fin n) K)} {S : Set (Matrix (Fin n) (Fin n) K)}
    (hS : ∀ x ∈ S, conjTr σ x = x) (hspan : Submodule.span K S = D) :
    Nat.card {x : D // conjTr σ ((x : D) : Matrix (Fin n) (Fin n) K) =
      ((x : D) : Matrix (Fin n) (Fin n) K)} ≤ q ^ finrank K D := by
  classical
  obtain ⟨t, ht_sub, ht_card, ht_span, ht_li⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn (K := K) (M := Matrix (Fin n) (Fin n) K) (s := S)
  have ht_li' : LinearIndependent K (fun i : t => (i : Matrix (Fin n) (Fin n) K)) := ht_li
  let v : t → D := fun i => ⟨(i : Matrix (Fin n) (Fin n) K), by
    rw [← hspan, ← ht_span]
    exact Submodule.subset_span i.2⟩
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff] at ht_li' ⊢
    intro z hz
    exact ht_li' z (by
      have h := congrArg (fun y : D => (y : Matrix (Fin n) (Fin n) K)) hz
      simpa [v] using h)
  have hcard : Fintype.card t = finrank K D := by
    rw [Fintype.card_coe, ht_card, hspan]
  have htop : Submodule.span K (Set.range v) = ⊤ :=
    LinearIndependent.span_eq_top_of_card_eq_finrank' hli hcard
  let b : Basis t K D := Basis.mk hli (by rw [htop])
  refine card_selfadjoint_le_pow_finrank σ q hfix b fun i => ?_
  have hbi : ((b i : D) : Matrix (Fin n) (Fin n) K) = (i : Matrix (Fin n) (Fin n) K) := by
    rw [Basis.mk_apply]
  rw [hbi]
  exact hS _ (ht_sub i.2)

theorem card_fixed_le_pow {K : Type} [Field K] [Finite K] {q : ℕ} (hq : 2 ≤ q) (σ : K ≃+* K)
    (hσq : ∀ c : K, σ c = c ↔ c ^ q = c) :
    Nat.card {c : K // σ c = c} ≤ q := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  let Z : Finset K := Finset.univ.filter fun c => σ c = c
  have hZ : Nat.card {c : K // σ c = c} = Z.card :=
    Nat.subtype_card Z fun x => by simp [Z]
  rw [hZ]
  set p : Polynomial K := Polynomial.X ^ q - Polynomial.X with hp
  have hlt : (Polynomial.X : Polynomial K).natDegree < (Polynomial.X ^ q : Polynomial K).natDegree := by
    rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]
    omega
  have hdeg : p.natDegree = q := by
    rw [hp, Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_X_pow]
  have hp0 : p ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hdeg
    omega
  have hsub : Z.val ⊆ p.roots := by
    intro c hc
    rw [Polynomial.mem_roots hp0, Polynomial.IsRoot.def]
    have hcZ : σ c = c := by
      have : c ∈ Z := Finset.mem_val.mp hc
      simpa [Z] using this
    have hcq : c ^ q = c := (hσq c).mp hcZ
    simp [hp, hcq]
  exact (Polynomial.card_le_degree_of_subset_roots hsub).trans (by rw [hdeg])

theorem toLinAlgEquiv'_unipotentMat {K : Type} [Field K] {n : ℕ} (a : GL (Fin n) K) :
    Matrix.toLinAlgEquiv' (R := K) (n := Fin n) (unipotentMat a) = unipotentEnd a := by
  have hz : ∀ z : Fin n → K,
      (glNaturalRep n K a : Module.End K (Fin n → K)) z =
        (a : Matrix (Fin n) (Fin n) K).mulVec z := by
    intro z
    simpa [glNaturalRep, Matrix.mulVecLin_apply] using Matrix.GeneralLinearGroup.toLin_apply a z
  refine LinearMap.ext fun z => ?_
  simp only [Matrix.toLinAlgEquiv'_apply, unipotentMat, unipotentEnd, LinearMap.sub_apply,
    Matrix.sub_mulVec, Matrix.one_mulVec, End.one_apply, hz z]

theorem finrank_unipotentMatAlgebra {K : Type} [Field K] {n : ℕ}
    (A : Subgroup (GL (Fin n) K)) :
    finrank K (unipotentMatAlgebra A) = finrank K (unipotentAlgebra A) := by
  let e : Matrix (Fin n) (Fin n) K ≃ₗ[K] Module.End K (Fin n → K) :=
    (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).toLinearEquiv
  have hmap : Submodule.map e.toLinearMap (unipotentMatAlgebra A) = unipotentAlgebra A := by
    rw [unipotentMatAlgebra, unipotentAlgebra, Submodule.map_span, Set.image_image]
    rw [show (fun a => e.toLinearMap (unipotentMat a)) = unipotentEnd from
      funext fun a => toLinAlgEquiv'_unipotentMat a]
  rw [← hmap]
  exact (LinearEquiv.finrank_map_eq e (unipotentMatAlgebra A)).symm

theorem card_le_pow_finrank_unipotentAlgebra_of_le_statedSU {K : Type} [Field K] [Finite K]
    {m f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) {A : Subgroup (GL (Fin m) K)}
    (hAS : A ≤ StatedSU m (2 ^ f) K) (hA : IsElemAbelian 2 A) :
    Nat.card A ≤ (2 ^ f) ^ finrank K (unipotentAlgebra A) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow (r := 2) (n := f * 2) Nat.prime_two
      (by rw [hK, pow_mul])
  have huni : ∀ a ∈ A,
      conjTr (unitaryInvolution K 2 f) ((a : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *
        ((a : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = 1 := by
    intro a ha
    have hSU : (a : GL (Fin m) K) ∈ SUid (unitaryInvolution K 2 f) m := by
      rw [SUid_eq_statedSU hK m]
      exact hAS ha
    exact (mem_SUid.mp hSU).2
  have hsq : ∀ a ∈ A, a * a = 1 := by
    intro a ha
    simpa [pow_two] using hA.2 (a : GL (Fin m) K) ha
  have hfix : ∀ a ∈ A,
      conjTr (unitaryInvolution K 2 f) (unipotentMat a) = unipotentMat a :=
    fun a ha => conjTr_unipotentMat (unitaryInvolution K 2 f) (huni a ha) (hsq a ha)
  have hfixcard : Nat.card {c : K // unitaryInvolution K 2 f c = c} ≤ 2 ^ f := by
    refine card_fixed_le_pow (q := 2 ^ f) ?_ (unitaryInvolution K 2 f) fun c => ?_
    · rcases Nat.eq_zero_or_pos f with hf | hf
      · exfalso
        rw [hf] at hK
        simp only [pow_zero, one_pow] at hK
        have := Finite.one_lt_card (α := K)
        omega
      · calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    · simp only [unitaryInvolution_apply]
  have hcount := card_selfadjoint_le_pow_finrank_of_span (K := K)
    (unitaryInvolution K 2 f) (2 ^ f) hfixcard
    (D := unipotentMatAlgebra A) (S := unipotentMat '' (A : Set (GL (Fin m) K)))
    (fun x hx => by
      obtain ⟨a, ha, rfl⟩ := hx
      exact hfix a ha)
    rfl
  have hcardA : Nat.card A ≤
      Nat.card {x : unipotentMatAlgebra A // conjTr (unitaryInvolution K 2 f)
        ((x : unipotentMatAlgebra A) : Matrix (Fin m) (Fin m) K) =
        ((x : unipotentMatAlgebra A) : Matrix (Fin m) (Fin m) K)} := by
    refine Nat.card_le_card_of_injective (fun a : A => ?_) ?_
    · exact ⟨⟨unipotentMat (a : GL (Fin m) K),
        Submodule.subset_span ⟨(a : GL (Fin m) K), a.2, rfl⟩⟩,
        hfix (a : GL (Fin m) K) a.2⟩
    · intro a b hab
      have h1 : unipotentMat (a : GL (Fin m) K) = unipotentMat (b : GL (Fin m) K) := by
        simpa using congrArg
          (fun y : {x : unipotentMatAlgebra A // conjTr (unitaryInvolution K 2 f)
            ((x : unipotentMatAlgebra A) : Matrix (Fin m) (Fin m) K) =
            ((x : unipotentMatAlgebra A) : Matrix (Fin m) (Fin m) K)} =>
            ((y.1 : unipotentMatAlgebra A) : Matrix (Fin m) (Fin m) K)) hab
      exact Subtype.ext (unipotentMat_injective h1)
  calc Nat.card A ≤
        Nat.card {x : unipotentMatAlgebra A // conjTr (unitaryInvolution K 2 f)
          ((x : unipotentMatAlgebra A) : Matrix (Fin m) (Fin m) K) =
          ((x : unipotentMatAlgebra A) : Matrix (Fin m) (Fin m) K)} := hcardA
    _ ≤ (2 ^ f) ^ finrank K (unipotentMatAlgebra A) := hcount
    _ = (2 ^ f) ^ finrank K (unipotentAlgebra A) := by rw [finrank_unipotentMatAlgebra]

theorem card_le_pow_fix_mul_of_le_statedSU {K : Type} [Field K] [Finite K]
    {m f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) {A : Subgroup (GL (Fin m) K)}
    (hAS : A ≤ StatedSU m (2 ^ f) K) (hA : IsElemAbelian 2 A) :
    Nat.card A ≤ (2 ^ f) ^ (finrank K (fixSubGen (glNaturalRep m K) A) *
      (m - finrank K (fixSubGen (glNaturalRep m K) A))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow (r := 2) (n := f * 2) Nat.prime_two
      (by rw [hK, pow_mul])
  have h1 := card_le_pow_finrank_unipotentAlgebra_of_le_statedSU hK hAS hA
  have h2 := finrank_unipotentAlgebra_le (K := K) (p := 2) Nat.prime_two hA
  exact h1.trans (Nat.pow_le_pow_right (by positivity) h2)

end CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
