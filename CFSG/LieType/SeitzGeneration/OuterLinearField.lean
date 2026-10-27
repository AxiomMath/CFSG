module

public import CFSG.LieType.SeitzGeneration.SubfieldPairSLF2
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.LieType.SeitzGeneration.OuterModel

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.RankThree.PartOne.CTP CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)
open CFSG.RankThree.Classical2
  (twistedProd twistedProd_succ twistedProd_zero exists_isUnit_det_fixed)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

section Descent

variable {n : ℕ} {K : Type} [Field K]

theorem twistedProd_smul_of_fixed (σ : K ≃+* K) {A : Matrix (Fin n) (Fin n) K}
    (hA : A.map σ = A) (μ : K) (j : ℕ) :
    twistedProd (⇑σ) (μ • A) j = (∏ i ∈ Finset.range j, (σ ^ i) μ) • A ^ j := by
  induction j with
  | zero => simp [twistedProd_zero]
  | succ j ih =>
    change twistedProd (⇑(σ : K →+* K)) (μ • A) (j + 1) = _
    rw [twistedProd_succ (σ : K →+* K) (μ • A) j]
    change (μ • A) * (twistedProd (⇑σ) (μ • A) j).map σ = _
    have hAj : (A ^ j).map σ = A ^ j := by
      have := Matrix.map_pow A (σ : K →+* K) j
      rw [show (⇑(σ : K →+* K) : K → K) = ⇑σ from rfl, hA] at this
      exact this
    rw [ih, Matrix.map_smul' _ _ _ (fun a b => map_mul σ a b), hAj,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Finset.prod_range_succ', pow_succ']
    congr 1
    rw [mul_comm]
    congr 1
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [pow_succ']
    rfl

theorem exists_fixed_matrix_smul [Finite K] {ℓ e p : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime)
    (he : 1 ≤ e) (hK : Nat.card K = ℓ ^ e) (σ : K ≃+* K) (hσ : orderOf σ = p)
    {A : Matrix (Fin n) (Fin n) K} (hA : A.map σ = A) {c μ : K} (hAp : A ^ p = c • 1)
    (hμ : (∏ i ∈ Finset.range p, (σ ^ i) μ) * c = 1) :
    ∃ M : Matrix (Fin n) (Fin n) K, IsUnit M.det ∧ (μ • A) * M.map σ = M := by
  have hc0 : c ≠ 0 := right_ne_zero_of_mul_eq_one hμ
  have hN0 : (∏ i ∈ Finset.range p, (σ ^ i) μ) ≠ 0 := left_ne_zero_of_mul_eq_one hμ
  have hμ0 : μ ≠ 0 := by
    intro h
    apply hN0
    exact Finset.prod_eq_zero (Finset.mem_range.mpr hp.pos) (by simp [h])
  have hdetA : A.det ≠ 0 := by
    intro h
    have h1 : A.det ^ p = c ^ n := by
      rw [← Matrix.det_pow, hAp, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    rw [h, zero_pow hp.ne_zero] at h1
    exact hc0 (pow_eq_zero_iff'.mp h1.symm).1
  have hdet : IsUnit (μ • A).det := by
    rw [Matrix.det_smul, Fintype.card_fin]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hμ0) hdetA)
  refine exists_isUnit_det_fixed hℓ he hK σ hσ (μ • A) hdet fun v => ?_
  have h1 : twistedProd (⇑σ) (μ • A) p = 1 := by
    rw [twistedProd_smul_of_fixed σ hA, hAp, smul_smul, hμ, one_smul]
  have h2 : (⇑σ)^[p] ∘ v = v := funext fun i => iterate_eq_id_of_orderOf σ hσ (v i)
  rw [h1, h2, Matrix.one_mulVec]

end Descent

section Pair

variable {n : ℕ} {K : Type} [Field K]

theorem slSub_le_comap_planeClosure_gl {k : Subfield K} (σ : K ≃+* K)
    (hk : ∀ x, x ∈ k ↔ σ x = x) {E : Subgroup (MulAut (projectiveSL n K))}
    (hσE : fieldAut n K σ ∈ E) (hσout : ∀ B : GL (Fin n) K, fieldAut n K σ ≠ conjAut n K B)
    {G : GL (Fin n) K} (hGE : conjAut n K G ∈ E) (M : GL (Fin n) K)
    (hGM : (G : Matrix (Fin n) (Fin n) K) * (M : Matrix (Fin n) (Fin n) K).map σ = M) :
    slSub n k ≤ (planeClosure E).comap (proj n K) ∧
      ∀ B ∈ slSub n k, slConjugation n K M B ∈ (planeClosure E).comap (proj n K) := by
  set α : MulAut (projectiveSL n K) := conjAut n K G * fieldAut n K σ with hα
  have hαE : α ∈ E := E.mul_mem hGE hσE
  have hf1 : fieldAut n K σ ≠ 1 := fun h => hσout 1 (by rw [h, map_one])
  have hα1 : α ≠ 1 := by
    intro h
    apply hσout G⁻¹
    have h1 : fieldAut n K σ = (conjAut n K G)⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h1, map_inv]
  have hfixB : ∀ B ∈ slSub n k, fieldAut n K σ (proj n K B) = proj n K B := by
    intro B hB
    rw [fieldAut_proj]
    congr 1
    apply Subtype.ext
    ext i j
    simp [SpecialLinearGroup.map_apply_coe, (hk _).mp ((mem_slSub.mp hB) i j)]
  have hGM' : G * GeneralLinearGroup.map (σ : K →+* K) M = M := Units.ext (by simpa using hGM)
  refine ⟨fun B hB => mem_planeClosure_of_fixed hσE hf1 (hfixB B hB), fun B hB => ?_⟩
  show proj n K (slConjugation n K M B) ∈ planeClosure E
  refine mem_planeClosure_of_fixed hαE hα1 ?_
  rw [← conjAut_proj]
  calc α (conjAut n K M (proj n K B))
      = conjAut n K G (fieldAut n K σ (conjAut n K M (proj n K B))) := rfl
    _ = conjAut n K G (conjAut n K (GeneralLinearGroup.map (σ : K →+* K) M)
          (proj n K B)) := by rw [fieldAut_conjAut_apply, hfixB B hB]
    _ = conjAut n K (G * GeneralLinearGroup.map (σ : K →+* K) M) (proj n K B) := by
        rw [map_mul]; rfl
    _ = conjAut n K M (proj n K B) := by rw [hGM']

theorem slConjugation_map_ne_of_unit {k : Subfield K} (σ : K ≃+* K)
    (hk : ∀ x, x ∈ k ↔ σ x = x) (G : GL (Fin n) K)
    (hG : ∀ c : K, (G : Matrix (Fin n) (Fin n) K) ≠ c • 1) (M : GL (Fin n) K)
    (hGM : (G : Matrix (Fin n) (Fin n) K) * (M : Matrix (Fin n) (Fin n) K).map σ = M) :
    (slSub n k).map (slConjugation n K M).toMonoidHom ≠ slSub n k := by
  intro heq
  set N : Matrix (Fin n) (Fin n) K := ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hN
  set g : Matrix (Fin n) (Fin n) K := (G : Matrix (Fin n) (Fin n) K) with hg
  set gi : Matrix (Fin n) (Fin n) K := ((G⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hgi
  have hgig : gi * g = 1 := by
    rw [hg, hgi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hggi : g * gi = 1 := by
    rw [hg, hgi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hσN : N.map σ = N * g := map_inv_eq_mul_of_fixed hGM
  have hσM : (M : Matrix (Fin n) (Fin n) K).map σ = gi * M := by
    calc (M : Matrix (Fin n) (Fin n) K).map σ
        = (gi * g) * (M : Matrix (Fin n) (Fin n) K).map σ := by rw [hgig, Matrix.one_mul]
      _ = gi * (g * (M : Matrix (Fin n) (Fin n) K).map σ) := by rw [Matrix.mul_assoc]
      _ = gi * M := by rw [hGM]
  have hcomm : ∀ X ∈ slSub n k, g * (X : Matrix (Fin n) (Fin n) K) = X * g := by
    intro X hX
    have hX' : X ∈ (slSub n k).map (slConjugation n K M).toMonoidHom := by rw [heq]; exact hX
    obtain ⟨B, hB, rfl⟩ := hX'
    have hBσ : (B : Matrix (Fin n) (Fin n) K).map σ = B := by
      ext i j
      exact (hk _).mp ((mem_slSub.mp hB) i j)
    have hXσ : ((slConjugation n K M B : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K).map σ = slConjugation n K M B := by
      ext i j
      exact (hk _).mp ((mem_slSub.mp (by rw [← heq]; exact ⟨B, hB, rfl⟩ : slConjugation n K M B ∈
        slSub n k)) i j)
    have hXM : ((slConjugation n K M B : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = M * B * N := slConjugation_matrix n K M B
    have h1 : (M * (B : Matrix (Fin n) (Fin n) K) * N).map σ = gi * (M * B * N) * g := by
      rw [Matrix.map_mul, Matrix.map_mul, hσM, hBσ, hσN]
      simp only [Matrix.mul_assoc]
    change g * ((slConjugation n K M B : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = ((slConjugation n K M B : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) * g
    rw [hXM] at hXσ ⊢
    rw [h1] at hXσ
    calc g * (M * B * N) = g * (gi * (M * B * N) * g) := by rw [hXσ]
      _ = (g * gi) * (M * B * N) * g := by simp only [Matrix.mul_assoc]
      _ = (M * B * N) * g := by rw [hggi, Matrix.one_mul]
  have hsingle : Pairwise fun i j : Fin n => Commute (Matrix.single i j (1 : K)) g := by
    intro i j hij
    have h1 := hcomm _ (transvection_mem_slSub hij k.one_mem)
    rw [SpecialLinearGroup.transvection_coe, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul] at h1
    exact (add_left_cancel h1).symm
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single hsingle
  apply hG c
  rw [← hc]
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply]

theorem planeGen_of_unit_pair {k : Subfield K} (σ : K ≃+* K) (hk : ∀ x, x ∈ k ↔ σ x = x)
    (hpair : ∀ M : GL (Fin n) K,
      (slSub n k).map (slConjugation n K M).toMonoidHom ≠ slSub n k →
        Subgroup.closure ((slSub n k : Set (SpecialLinearGroup (Fin n) K)) ∪
          ((slSub n k).map (slConjugation n K M).toMonoidHom :
            Set (SpecialLinearGroup (Fin n) K))) = ⊤)
    {E : Subgroup (MulAut (projectiveSL n K))} (hσE : fieldAut n K σ ∈ E)
    (hσout : ∀ B : GL (Fin n) K, fieldAut n K σ ≠ conjAut n K B)
    {G : GL (Fin n) K} (hGE : conjAut n K G ∈ E)
    (hG : ∀ c : K, (G : Matrix (Fin n) (Fin n) K) ≠ c • 1) {M : GL (Fin n) K}
    (hGM : (G : Matrix (Fin n) (Fin n) K) * (M : Matrix (Fin n) (Fin n) K).map σ = M) :
    PlaneGen E := by
  obtain ⟨hkH, hMH⟩ := slSub_le_comap_planeClosure_gl σ hk hσE hσout hGE M hGM
  have hclos := hpair M (slConjugation_map_ne_of_unit σ hk G hG M hGM)
  refine planeGen_of_comap_eq_top (eq_top_iff.mpr ?_)
  rw [← hclos, Subgroup.closure_le]
  rintro x (hx | ⟨B, hB, rfl⟩)
  · exact hkH hx
  · exact hMH B hB

theorem pairSL_closure [Finite K] {k : Subfield K} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = Nat.card k ^ p) (hn : 3 ≤ n)
    (M : GL (Fin n) K) (hne : (slSub n k).map (slConjugation n K M).toMonoidHom ≠ slSub n k) :
    Subgroup.closure ((slSub n k : Set (SpecialLinearGroup (Fin n) K)) ∪
      ((slSub n k).map (slConjugation n K M).toMonoidHom :
        Set (SpecialLinearGroup (Fin n) K))) = ⊤ := by
  have h2 : 2 ≤ Nat.card k := Finite.one_lt_card
  rcases (by omega : Nat.card k = 2 ∨ 3 ≤ Nat.card k) with hk2 | hk3
  · exact subfieldPairSLF2_holds K k p hp hp2 hK hk2 n hn M hne
  · exact subfieldPairSL_odd hp hp2 hK hk3 hn M hne

end Pair

section Normal

variable {n : ℕ} {K : Type} [Field K]

theorem mem_zpowers_of_pow_eq_one_of_isCyclic {G : Type*} [Group G] [Finite G] [IsCyclic G]
    {p : ℕ} (hp : p.Prime) {σ τ : G} (hσ : orderOf σ = p) (hτ : τ ^ p = 1) :
    τ ∈ Subgroup.zpowers σ := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set S : Finset G := Finset.univ.filter fun a => a ^ p = 1 with hS
  have hcardS : S.card ≤ p := IsCyclic.card_pow_eq_one_le (α := G) hp.pos
  set Z : Finset G := (Subgroup.zpowers σ : Set G).toFinset with hZ
  have hZS : Z ⊆ S := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (by simpa [hZ] using ha)
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, ← hσ,
      pow_orderOf_eq_one, _root_.one_zpow]
  have hZcard : Z.card = p := by
    have h1 : Nat.card (Subgroup.zpowers σ) = p := by rw [Nat.card_zpowers, hσ]
    rw [hZ, Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact h1
  have hZeq : Z = S := Finset.eq_of_subset_of_card_le hZS (by rw [hZcard]; exact hcardS)
  have hτS : τ ∈ S := by simp [hS, hτ]
  rw [← hZeq] at hτS
  simpa [hZ] using hτS

theorem scalarGL_coe_eq_smul (c : Kˣ) :
    ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (c : K) • 1 := by
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul,
    Matrix.mul_one]

theorem ne_zero_of_gl_coe_eq_smul (hn : 0 < n) {G : GL (Fin n) K} {a : K}
    (h : (G : Matrix (Fin n) (Fin n) K) = a • 1) : a ≠ 0 := by
  rintro rfl
  have h1 : ((G⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * G = 1 := Units.inv_mul G
  rw [h, zero_smul, Matrix.mul_zero] at h1
  exact zero_ne_one (congrFun (congrFun h1 ⟨0, hn⟩) ⟨0, hn⟩)

theorem exists_scalarGL_of_gl_coe_eq_smul (hn : 0 < n) {G : GL (Fin n) K} {a : K}
    (h : (G : Matrix (Fin n) (Fin n) K) = a • 1) :
    ∃ u : Kˣ, GeneralLinearGroup.scalar (Fin n) u = G :=
  ⟨Units.mk0 a (ne_zero_of_gl_coe_eq_smul hn h), Units.ext (by rw [scalarGL_coe_eq_smul, h]; rfl)⟩

end Normal

section NormalForm

variable {n : ℕ} {K : Type} [Field K]

theorem exists_field_normal_form [Finite K] {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hn : 3 ≤ n) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    {E : Subgroup (MulAut (projectiveSL n K))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) (hout : ¬ E ≤ linearAutGroup n K) :
    ∃ (h : MulAut (projectiveSL n K)) (σ : K ≃+* K) (x : GL (Fin n) K) (c : K),
      orderOf σ = p ∧ Nat.card K = Nat.card (semilinearFixedSubfield σ) ^ p ∧
      (∀ B : GL (Fin n) K, fieldAut n K σ ≠ conjAut n K B) ∧
      fieldAut n K σ ∈ E.map (MulAut.congr h⁻¹).toMonoidHom ∧
      conjAut n K x ∈ E.map (MulAut.congr h⁻¹).toMonoidHom ∧
      (x : Matrix (Fin n) (Fin n) K).map σ = x ∧
      (∀ a : K, (x : Matrix (Fin n) (Fin n) K) ≠ a • 1) ∧
      (x : Matrix (Fin n) (Fin n) K) ^ p = c • 1 ∧ σ c = c := by
  classical
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have : Fact p.Prime := ⟨hp⟩
  have hpA : ∀ a ∈ E, a ^ p = 1 := hE.2
  have hES : ∀ a ∈ E, a ∈ semilinearAutGroup n K := fun a ha =>
    CFSG.RankThree.PartOne.KCLinCommOdd.mem_semilinearAutGroup_of_pow_eq_one hn hp2 hp (j := 1)
      (by simpa using hpA a ha)
  obtain ⟨a0, ha0E, ha0D⟩ : ∃ a0 ∈ E, a0 ∉ linearAutGroup n K := by
    by_contra hcon
    push Not at hcon
    exact hout hcon
  have ha0p : orderOf a0 = p := orderOf_eq_prime (hpA a0 ha0E) (fun h => ha0D (h ▸ one_mem _))
  obtain ⟨-, hinj, -, hDF, -, -, -, hdesc⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent hℓ hf hn hK
  obtain ⟨hpf, σ, hσ, ⟨h, hhD, hha⟩, hkcard⟩ := hdesc p hp hpℓ a0 (hES a0 ha0E) ha0D ha0p
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact hp.one_lt.ne hσ
  have hσout : ∀ B : GL (Fin n) K, fieldAut n K σ ≠ conjAut n K B := by
    intro B hB
    have hmem : fieldAut n K σ ∈ linearAutGroup n K ⊓ (fieldAut n K).range :=
      ⟨hB ▸ conjAut_mem_linearAutGroup B, σ, rfl⟩
    rw [hDF, Subgroup.mem_bot] at hmem
    exact hσ1 (hinj (hmem.trans (map_one _).symm))
  have hKk : Nat.card K = Nat.card (semilinearFixedSubfield σ) ^ p := by
    rw [hK, hkcard, ← pow_mul, Nat.div_mul_cancel hpf]
  set E' := E.map (MulAut.congr h⁻¹).toMonoidHom with hE'def
  have hcongr : ∀ φ : MulAut (projectiveSL n K), MulAut.congr h⁻¹ φ = h⁻¹ * φ * h :=
    fun φ => rfl
  have hfa : MulAut.congr h⁻¹ a0 = fieldAut n K σ := by
    rw [hcongr, hha]
    group
  have hσE : fieldAut n K σ ∈ E' := ⟨a0, ha0E, hfa⟩
  have hE' : IsElemAbelian p E' := isElemAbelian_map_congr h⁻¹ hE
  have hc' : Nat.card E' = p ^ 2 := (card_map_congr h⁻¹ E).trans hc
  have hσord : orderOf (fieldAut n K σ) = p := by
    rw [orderOf_injective (fieldAut n K) hinj σ]
    exact hσ
  obtain ⟨x₀, hx₀E, hx₀⟩ : ∃ x₀ ∈ E', x₀ ∉ Subgroup.zpowers (fieldAut n K σ) := by
    by_contra hcon
    push Not at hcon
    have hle : E' ≤ Subgroup.zpowers (fieldAut n K σ) := hcon
    have hfin : Finite (Subgroup.zpowers (fieldAut n K σ)) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hσord]; exact hp.ne_zero)
    have h1 := Subgroup.card_le_of_le hle
    rw [hc', Nat.card_zpowers, hσord] at h1
    nlinarith [hp.two_le]
  have hx₀S : x₀ ∈ semilinearAutGroup n K := by
    obtain ⟨e, heE, rfl⟩ := hx₀E
    have hhS : h ∈ semilinearAutGroup n K := linearAutGroup_le_semilinearAutGroup hhD
    exact (semilinearAutGroup n K).mul_mem ((semilinearAutGroup n K).mul_mem
      ((semilinearAutGroup n K).inv_mem hhS) (hES e heE)) hhS
  obtain ⟨A, τ, hx₀A⟩ := mem_semilinearAutGroup_iff.mp hx₀S
  have hτp : τ ^ p = 1 := by
    have h1 : x₀ ^ p = 1 := hE'.2 x₀ hx₀E
    rw [hx₀A, CFSG.RankThree.LinearDescent.conjAut_mul_fieldAut_pow] at h1
    exact (eq_one_of_conjAut_mul_fieldAut_eq_one hn _ _ h1).1
  obtain ⟨F₀, -, -, htop, hcardAut, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality hℓ hf hK
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨F₀, htop⟩
  have hfinAut : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have hτ : τ ∈ Subgroup.zpowers σ := mem_zpowers_of_pow_eq_one_of_isCyclic hp hσ hτp
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hτ
  have hxA : conjAut n K A ∈ E' := by
    have h1 : (fieldAut n K σ) ^ j ∈ E' := zpow_mem hσE j
    have h2 : x₀ * ((fieldAut n K σ) ^ j)⁻¹ ∈ E' := E'.mul_mem hx₀E (E'.inv_mem h1)
    have h3 : x₀ * ((fieldAut n K σ) ^ j)⁻¹ = conjAut n K A := by
      rw [hx₀A, ← hj, map_zpow]
      group
    rwa [h3] at h2
  have hA1 : conjAut n K A ≠ 1 := by
    intro h1
    apply hx₀
    rw [hx₀A, h1, one_mul, ← hj, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ _
  have hcomm : fieldAut n K σ * conjAut n K A = conjAut n K A * fieldAut n K σ :=
    congrArg Subtype.val (hE'.1.is_comm.comm ⟨_, hσE⟩ ⟨_, hxA⟩)
  have hσA : conjAut n K (GeneralLinearGroup.map (σ : K →+* K) A) = conjAut n K A := by
    rw [← (standard_automorphism_transport (K := K) (n := n)).2.2.1 σ A, hcomm,
      mul_inv_cancel_right]
  obtain ⟨u, hu⟩ : ∃ u : Kˣ, GeneralLinearGroup.scalar (Fin n) u =
      GeneralLinearGroup.map (σ : K →+* K) A * A⁻¹ :=
    (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff hn _).mp
      (by rw [map_mul, map_inv, hσA, mul_inv_cancel])
  have hAσ : (A : Matrix (Fin n) (Fin n) K).map σ = (u : K) • (A : Matrix (Fin n) (Fin n) K) := by
    have h1 : GeneralLinearGroup.map (σ : K →+* K) A = GeneralLinearGroup.scalar (Fin n) u * A := by
      rw [hu, inv_mul_cancel_right]
    have h2 := congrArg (fun B : GL (Fin n) K => (B : Matrix (Fin n) (Fin n) K)) h1
    simp only [Units.val_mul, scalarGL_coe_eq_smul] at h2
    ext i j
    have h3 := congrFun (congrFun h2 i) j
    simpa [GeneralLinearGroup.map_apply, Matrix.smul_apply] using h3
  have hn0 : 0 < n := by omega
  have hA0 : (A : Matrix (Fin n) (Fin n) K) ≠ 0 := by
    intro h0
    have h1 : ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A = 1 := Units.inv_mul A
    rw [h0, Matrix.mul_zero] at h1
    exact zero_ne_one (congrFun (congrFun h1 ⟨0, hn0⟩) ⟨0, hn0⟩)
  obtain ⟨c', hc'0, hc'σ⟩ := exists_rational_smul hp hℓ hf hK σ hσ hA0 hAσ
  set x : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) (Units.mk0 c' hc'0) * A with hxdef
  have hxcoe : (x : Matrix (Fin n) (Fin n) K) = c' • (A : Matrix (Fin n) (Fin n) K) := by
    rw [hxdef, Units.val_mul, scalarGL_coe_eq_smul, Matrix.smul_mul, Matrix.one_mul]
    rfl
  have hconj : conjAut n K x = conjAut n K A := by
    rw [hxdef, map_mul, conjAut_scalar, one_mul]
  have hxE : conjAut n K x ∈ E' := hconj ▸ hxA
  have hxσ : (x : Matrix (Fin n) (Fin n) K).map σ = x := by
    rw [hxcoe]
    exact hc'σ
  have hxns : ∀ a : K, (x : Matrix (Fin n) (Fin n) K) ≠ a • 1 := by
    intro a ha
    obtain ⟨v, hv⟩ := exists_scalarGL_of_gl_coe_eq_smul hn0 ha
    apply hA1
    rw [← hconj, ← hv, conjAut_scalar]
  have hxp1 : conjAut n K (x ^ p) = 1 := by
    rw [map_pow, hconj]
    exact hE'.2 _ hxA
  obtain ⟨d, hd⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff hn _).mp hxp1
  have hxpd : (x : Matrix (Fin n) (Fin n) K) ^ p = (d : K) • 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hd, scalarGL_coe_eq_smul]
  have hdσ : σ (d : K) = d := by
    have h1 : ((x : Matrix (Fin n) (Fin n) K) ^ p).map σ = (x : Matrix (Fin n) (Fin n) K) ^ p := by
      have := Matrix.map_pow (x : Matrix (Fin n) (Fin n) K) (σ : K →+* K) p
      rw [show (⇑(σ : K →+* K) : K → K) = ⇑σ from rfl, hxσ] at this
      exact this
    rw [hxpd] at h1
    have h2 := congrFun (congrFun h1 ⟨0, hn0⟩) ⟨0, hn0⟩
    simpa [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply] using h2
  exact ⟨h, σ, x, d, hσ, hKk, hσout, hσE, hxE, hxσ, hxns, hxpd, hdσ⟩

end NormalForm

section Main

variable {n : ℕ} {K : Type} [Field K]

theorem planeGen_of_field_outer [Finite K] {ℓ f p : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hn : 3 ≤ n) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) {E : Subgroup (MulAut (projectiveSL n K))}
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2) (hout : ¬ E ≤ linearAutGroup n K) :
    PlaneGen E := by
  classical
  obtain ⟨h, σ, x, c, hσ, hKk, hσout, hσE, hxE, hxσ, hxns, hxp, hcσ⟩ :=
    exists_field_normal_form hℓ hf hn hK hp hp2 hpℓ hE hc hout
  set k : Subfield K := semilinearFixedSubfield σ with hkdef
  have hk : ∀ y, y ∈ k ↔ σ y = y := fun y => Iff.rfl
  have hn0 : 0 < n := by omega
  have hc0 : c ≠ 0 :=
    ne_zero_of_gl_coe_eq_smul hn0 (G := x ^ p) (a := c) (by
      rw [Units.val_pow_eq_pow_val]
      exact hxp)
  obtain ⟨μ, hμ⟩ := CFSG.ABGLocalTools.exists_prod_pow_eq σ (c := c⁻¹) (by rw [map_inv₀, hcσ])
  rw [hσ] at hμ
  have hμ0 : μ ≠ 0 := by
    intro h0
    have h1 : ∏ i ∈ Finset.range p, (σ ^ i) μ = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.mpr hp.pos) (by simp [h0])
    rw [hμ] at h1
    exact inv_ne_zero hc0 h1
  obtain ⟨M₀, hdet, hM₀⟩ := exists_fixed_matrix_smul hp hℓ hf hK σ hσ hxσ hxp
    (by rw [hμ]; exact inv_mul_cancel₀ hc0)
  let M : GL (Fin n) K := Matrix.nonsingInvUnit M₀ hdet
  let G : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) (Units.mk0 μ hμ0) * x
  have hGcoe : (G : Matrix (Fin n) (Fin n) K) = μ • (x : Matrix (Fin n) (Fin n) K) := by
    rw [Units.val_mul, scalarGL_coe_eq_smul, Matrix.smul_mul, Matrix.one_mul]
    rfl
  have hGE : conjAut n K G ∈ E.map (MulAut.congr h⁻¹).toMonoidHom := by
    rw [map_mul, conjAut_scalar, one_mul]
    exact hxE
  have hGns : ∀ a : K, (G : Matrix (Fin n) (Fin n) K) ≠ a • 1 := by
    intro a ha
    apply hxns (μ⁻¹ * a)
    rw [hGcoe] at ha
    have h1 := congrArg (fun Z => μ⁻¹ • Z) ha
    simpa [smul_smul, hμ0] using h1
  have hGM : (G : Matrix (Fin n) (Fin n) K) * (M : Matrix (Fin n) (Fin n) K).map σ = M := by
    rw [hGcoe]
    exact hM₀
  have hpl : PlaneGen (E.map (MulAut.congr h⁻¹).toMonoidHom) :=
    planeGen_of_unit_pair σ hk (fun M' hne => pairSL_closure hp hp2 hKk hn M' hne) hσE hσout hGE
      hGns hGM
  exact planeGen_of_outer_model h⁻¹ hpl

end Main

end CFSG.LieType.SeitzGeneration
