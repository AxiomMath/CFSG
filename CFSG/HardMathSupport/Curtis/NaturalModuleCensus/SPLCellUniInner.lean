module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellUniOuter
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellUniCorner
public import CFSG.HardMathSupport.Curtis.Coordinator.SPLCellFam

public section

open Matrix Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.UnitaryDescent (twistedNorm twistedNorm_succ' twistedNorm_succ twistedNorm_mem)

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellUni

open CFSG.HardMathSupport.Curtis.Coordinator CFSG.HardMathSupport.Curtis.Coordinator.SPLCell

open scoped IsMulCommutative

section GammaHat

variable {ℓ f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

@[expose] noncomputable def gammaHatU (M : primeFormUnitary h (idGram K n)) (σ : K ≃+* K) :
    MulAut (primeFormUnitary h (idGram K n)) :=
  MulAut.conj M * primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := n)) σ

theorem coe_gammaHatU (M e : primeFormUnitary h (idGram K n)) (σ : K ≃+* K) :
    ((gammaHatU h M σ e : primeFormUnitary h (idGram K n)) : GL (Fin n) K) =
      (M : GL (Fin n) K) * glAut σ (e : GL (Fin n) K) * (M : GL (Fin n) K)⁻¹ := rfl

theorem fieldU_mul_conj (σ : K ≃+* K) (A : primeFormUnitary h (idGram K n)) :
    primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := n)) σ * MulAut.conj A *
        (primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := n)) σ)⁻¹ =
      MulAut.conj (primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := n)) σ A) := by
  ext e
  simp [MulAut.conj_apply]

noncomputable def twistedNormU (σ : K ≃+* K) (A : primeFormUnitary h (idGram K n)) (m : ℕ) :
    primeFormUnitary h (idGram K n) :=
  ⟨twistedNorm σ (A : GL (Fin n) K) m, twistedNorm_mem h σ A.2 m⟩

theorem gammaHatU_pow (M : primeFormUnitary h (idGram K n)) (σ : K ≃+* K) (m : ℕ) :
    gammaHatU h M σ ^ m = MulAut.conj (twistedNormU h σ M m) *
      primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := n)) (σ ^ m) := by
  induction m with
  | zero =>
    have h1 : twistedNormU h σ M 0 = 1 := Subtype.ext rfl
    simp [h1]
  | succ m ih =>
    have hN : twistedNormU h σ M (m + 1) = M *
        primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := n)) σ (twistedNormU h σ M m) :=
      Subtype.ext (twistedNorm_succ' σ (M : GL (Fin n) K) m)
    rw [pow_succ', ih, gammaHatU, hN, map_mul, pow_succ', map_mul]
    have key := fieldU_mul_conj h σ (twistedNormU h σ M m)
    calc MulAut.conj M * primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := n)) σ *
          (MulAut.conj (twistedNormU h σ M m) *
            primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := n)) (σ ^ m))
        = MulAut.conj M * (primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := n)) σ *
            MulAut.conj (twistedNormU h σ M m) *
              (primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := n)) σ)⁻¹) *
            (primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := n)) σ *
              primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := n)) (σ ^ m)) := by group
      _ = _ := by rw [key]

theorem gammaHatU_pow_eq_one (M : primeFormUnitary h (idGram K n)) (σ : K ≃+* K) {m : ℕ}
    (hσ : σ ^ m = 1) {c : Kˣ}
    (hc : twistedNorm σ (M : GL (Fin n) K) m = GeneralLinearGroup.scalar (Fin n) c) :
    gammaHatU h M σ ^ m = 1 := by
  rw [gammaHatU_pow, hσ, map_one, mul_one]
  refine MulEquiv.ext fun e => ?_
  simp only [MulAut.conj_apply, MulAut.one_apply]
  apply Subtype.ext
  change (twistedNorm σ (M : GL (Fin n) K) m) * (e : GL (Fin n) K) *
    (twistedNorm σ (M : GL (Fin n) K) m)⁻¹ = e
  rw [hc, CFSG.RankThree.UnitaryDescent.scalar_mul_comm, mul_inv_cancel_right]

end GammaHat

section Kernel

variable {ℓ f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

theorem conjHom_eq_one_iff (hn : 3 ≤ n) (A : primeFormUnitary h (idGram K n)) :
    primeFormConjHom h (idGram K n) A = 1 ↔
      ∃ c : Kˣ, h.norm (c : K) = 1 ∧
        (A : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c := by
  have key := primeFormPsi_eq_one_iff h (isPrimeFormGram_idGram (K := K) (n := n)) hn ⟨A, 1⟩
  rw [primeFormPsi_apply, map_one, mul_one] at key
  rw [key]
  exact ⟨fun ⟨_, c, hc, hA⟩ => ⟨c, hc, hA⟩, fun ⟨c, hc, hA⟩ => ⟨rfl, c, hc, hA⟩⟩

theorem conjHom_ker_central (hn : 3 ≤ n) (A : primeFormUnitary h (idGram K n))
    (hA : primeFormConjHom h (idGram K n) A = 1) (g : primeFormUnitary h (idGram K n)) :
    g * A = A * g := by
  obtain ⟨c, -, hc⟩ := (conjHom_eq_one_iff h hn A).1 hA
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
  exact (CFSG.RankThree.UnitaryDescent.scalar_mul_comm c (g : GL (Fin n) K)).symm

theorem conjHom_ker_le_center (hn : 3 ≤ n) :
    (primeFormConjHom h (idGram K n)).ker ≤ Subgroup.center (primeFormUnitary h (idGram K n)) := by
  intro A hA
  rw [Subgroup.mem_center_iff]
  intro g
  exact conjHom_ker_central h hn A (MonoidHom.mem_ker.1 hA) g

theorem isCyclic_conjHom_ker [Finite K] (hn : 3 ≤ n) :
    IsCyclic (primeFormConjHom h (idGram K n)).ker := by
  let R : Subgroup (GL (Fin n) K) :=
    (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range
  have hR : IsCyclic R :=
    isCyclic_of_surjective (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  let φ : ↥(primeFormConjHom h (idGram K n)).ker →* R :=
    ((primeFormUnitary h (idGram K n)).subtype.comp
      (primeFormConjHom h (idGram K n)).ker.subtype).codRestrict R (fun A => by
        obtain ⟨c, -, hc⟩ := (conjHom_eq_one_iff h hn A.1).1 (MonoidHom.mem_ker.1 A.2)
        exact ⟨c, hc.symm⟩)
  exact isCyclic_of_injective φ (fun a b hab => Subtype.ext (Subtype.ext (congrArg
    (fun t : R => (t : GL (Fin n) K)) hab)))

end Kernel

section Step3

variable {ℓ f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

@[reducible] noncomputable def cU (n : ℕ) :
    primeFormUnitary h (idGram K n) →* MulAut (primeFormP h (idGram K n)) :=
  primeFormConjHom h (idGram K n)

@[reducible] noncomputable def fU (n : ℕ) :
    (K ≃+* K) →* MulAut (primeFormP h (idGram K n)) :=
  primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := n))

theorem aut_mul_conj_mul_inv {S : Type*} [Group S] (ζ : MulAut S) (x : S) :
    ζ * MulAut.conj x * ζ⁻¹ = MulAut.conj (ζ x) := by
  ext y
  simp [MulAut.conj_apply]

theorem conjHom_gammaHatU (M e : primeFormUnitary h (idGram K n)) (σ : K ≃+* K) :
    cU h n (gammaHatU h M σ e) = MulAut.conj (cU h n M * fU h n σ) (cU h n e) := by
  have key := primeFormField_conj_eq h (isPrimeFormGram_idGram (K := K) (n := n)) σ e
  have h1 : gammaHatU h M σ e =
      M * primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := n)) σ e * M⁻¹ := rfl
  rw [h1, map_mul, map_mul, map_inv, ← key, MulAut.conj_apply]
  group

theorem map_conj_data [Finite K] (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) {p : ℕ}
    (Ē : Subgroup (primeFormP h (idGram K n))) (hEc : IsMulCommutative Ē)
    (hEp : ∀ x ∈ Ē, x ^ p = 1) (hcard : Nat.card Ē = p ^ 4)
    (γ : MulAut (primeFormP h (idGram K n))) (hγE : ∀ x ∈ Ē, γ x ∈ Ē)
    (hnt : ∃ x ∈ Ē, γ x ≠ x) :
    IsMulCommutative (Ē.map (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n)))) ∧
    (∀ x ∈ Ē.map (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))), x ^ p = 1) ∧
    Nat.card (Ē.map (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n)))) = p ^ 4 ∧
    (∀ x ∈ Ē.map (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))),
      ∃ e : primeFormUnitary h (idGram K n), cU h n e = x) ∧
    (∀ x ∈ Ē.map (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))),
      MulAut.conj γ x ∈ Ē.map (MulAut.conj : primeFormP h (idGram K n) →*
        MulAut (primeFormP h (idGram K n)))) ∧
    (∃ x ∈ Ē.map (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))), MulAut.conj γ x ≠ x) := by
  classical
  have hinj := CFSG.RankThree.PartOne.KCUnitaryRegular.conj_injective_primeFormP h
    (isPrimeFormGram_idGram (K := K) (n := n)) hn hne
  let Ē' : Subgroup (MulAut (primeFormP h (idGram K n))) :=
    Ē.map (MulAut.conj : primeFormP h (idGram K n) →* MulAut (primeFormP h (idGram K n)))
  have hcard' : Nat.card Ē' = p ^ 4 := (Subgroup.card_map_of_injective hinj).trans hcard
  have hEc' : IsMulCommutative Ē' := by
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨a0, ha0, ha⟩ := a.2
    obtain ⟨b0, hb0, hb⟩ := b.2
    apply Subtype.ext
    change (a : MulAut (primeFormP h (idGram K n))) * b = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hEc.is_comm.comm (⟨a0, ha0⟩ : ↥Ē) ⟨b0, hb0⟩)
  have hEp' : ∀ x ∈ Ē', x ^ p = 1 := by
    rintro _ ⟨a0, ha0, rfl⟩
    rw [← map_pow, hEp a0 ha0, map_one]
  have hπE : ∀ x ∈ Ē', ∃ e : primeFormUnitary h (idGram K n), cU h n e = x := by
    rintro _ ⟨a0, ha0, rfl⟩
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective a0
    exact ⟨⟨s, s.2.1⟩, primeFormConjHom_eq_conj h (idGram K n) s⟩
  have hγE' : ∀ x ∈ Ē', MulAut.conj γ x ∈ Ē' := by
    rintro _ ⟨a0, ha0, rfl⟩
    refine ⟨γ a0, hγE a0 ha0, ?_⟩
    rw [MulAut.conj_apply]
    exact (aut_mul_conj_mul_inv γ a0).symm
  have hnt' : ∃ x ∈ Ē', MulAut.conj γ x ≠ x := by
    obtain ⟨a0, ha0, hne'⟩ := hnt
    refine ⟨MulAut.conj a0, ⟨a0, ha0, rfl⟩, fun h' => hne' (hinj ?_)⟩
    rw [MulAut.conj_apply, aut_mul_conj_mul_inv] at h'
    exact h'
  exact ⟨hEc', hEp', hcard', hπE, hγE', hnt'⟩

theorem uni_step3 [Finite K] (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) {p r k : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hrp : ¬ r ∣ p - 1) (hr2 : ¬ r ∣ p ^ 2 - 1)
    (hr3 : ¬ r ∣ p ^ 3 - 1) (hrne : r ≠ p)
    (Ē : Subgroup (primeFormP h (idGram K n))) (hEc : IsMulCommutative Ē)
    (hEp : ∀ x ∈ Ē, x ^ p = 1) (hcard : Nat.card Ē = p ^ 4)
    (y B : primeFormUnitary h (idGram K n)) (σ : K ≃+* K)
    (hζp : cU h n y ^ p = 1) (hζE : ∀ x ∈ Ē, cU h n y x = x)
    (hγ : (cU h n B * fU h n σ) ^ r ^ k = 1)
    (hγE : ∀ x ∈ Ē, (cU h n B * fU h n σ) x ∈ Ē)
    (hcomm : (cU h n B * fU h n σ) * cU h n y = cU h n y * (cU h n B * fU h n σ))
    (hnt : ∃ x ∈ Ē, (cU h n B * fU h n σ) x ≠ x) :
    ∀ e : primeFormUnitary h (idGram K n),
      cU h n e ∈ Ē.map (MulAut.conj : primeFormP h (idGram K n) →*
        MulAut (primeFormP h (idGram K n))) → y * e = e * y := by
  classical
  set γ : MulAut (primeFormP h (idGram K n)) := cU h n B * fU h n σ with hγdef
  obtain ⟨hEc', hEp', hcard', hπE, hγE', hnt'⟩ := map_conj_data h hn hne Ē hEc hEp hcard γ hγE hnt
  have hπE' : ∀ e : primeFormUnitary h (idGram K n),
      cU h n e ∈ Ē.map (MulAut.conj : primeFormP h (idGram K n) →*
        MulAut (primeFormP h (idGram K n))) →
      ∃ a0 ∈ Ē, cU h n e = MulAut.conj a0 :=
    fun e he => by
      obtain ⟨a0, ha0, h'⟩ := he
      exact ⟨a0, ha0, h'.symm⟩
  have hγ' : ∀ e, cU h n (gammaHatU h B σ e) = MulAut.conj γ (cU h n e) :=
    fun e => conjHom_gammaHatU h B e σ
  have hγ'' : MulAut.conj γ ^ r ^ k = 1 := by rw [← map_pow, hγ, map_one]
  have hy : y ^ p ∈ Subgroup.center (primeFormUnitary h (idGram K n)) := by
    apply conjHom_ker_le_center h hn
    rw [MonoidHom.mem_ker, map_pow]
    exact hζp
  have hyE : ∀ e : primeFormUnitary h (idGram K n),
      cU h n e ∈ Ē.map (MulAut.conj : primeFormP h (idGram K n) →*
        MulAut (primeFormP h (idGram K n))) →
      cU h n (y * e * y⁻¹) = cU h n e := by
    intro e he
    obtain ⟨a0, ha0, h'⟩ := hπE' e he
    rw [map_mul, map_mul, map_inv, h', aut_mul_conj_mul_inv, hζE a0 ha0]
  have hγy : gammaHatU h B σ y * y⁻¹ ∈ Subgroup.center (primeFormUnitary h (idGram K n)) := by
    apply conjHom_ker_le_center h hn
    rw [MonoidHom.mem_ker, map_mul, map_inv, hγ', mul_inv_eq_one, MulAut.conj_apply,
      mul_inv_eq_iff_eq_mul]
    exact hcomm
  exact central_of_gamma_commutes hp hr hrp hr2 hr3 hrne (cU h n) (conjHom_ker_le_center h hn)
    (isCyclic_conjHom_ker h hn) _ hEc' hEp' hcard' hπE y hy hyE (MulAut.conj γ)
    (gammaHatU h B σ) hγ' hγ'' hγE' hnt' hγy

end Step3

section Cases

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem scalar_injective_fin {n : ℕ} {K : Type} [Field K] (hn : 0 < n) :
    Function.Injective (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K) := by
  intro a b h
  apply Units.ext
  have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩) h
  simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this

theorem not_elemAbelian_of_le_cyclic {A : Type*} [Group A] {p : ℕ} (hp : p.Prime)
    (R E : Subgroup A) [Finite R] [IsCyclic R] (hER : E ≤ R) (hEp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 4) : False := by
  classical
  have : Fintype R := Fintype.ofFinite R
  have hle : Nat.card E ≤ Nat.card {a : R // a ^ p = 1} := by
    refine Nat.card_le_card_of_injective
      (fun a : E => (⟨⟨a.1, hER a.2⟩, Subtype.ext (hEp a.1 a.2)⟩ : {a : R // a ^ p = 1})) ?_
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun t : {a : R // a ^ p = 1} => ((t.1 : R) : A)) hab
  have h2 : Nat.card {a : R // a ^ p = 1} ≤ p := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsCyclic.card_pow_eq_one_le hp.pos
  rw [hcard] at hle
  have : p ^ 1 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  rw [pow_one] at this
  omega

theorem exists_mul_eq_of_pow_scalar_irreducible (hn : 1 ≤ n) {p : ℕ} (hp : p.Prime) {c : Kˣ}
    (hc : ∀ b : K, b ^ p ≠ (c : K)) (y : primeFormUnitary h (idGram K n))
    (hyp : (y : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) c) : ∃ m, p * m = n := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hX : ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) = Matrix.toLin' ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (Matrix.toLin'_apply' _).symm
  have hmin : minpoly K ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) = X ^ p - C (c : K) := by
    rw [hX]
    exact SPLCell.Uni.minpoly_eq_of_pow_scalar_irreducible hp hc hyp
  have hirr : Irreducible (X ^ p - C (c : K)) := X_pow_sub_C_irreducible_of_prime hp hc
  have hmem : (X ^ p - C (c : K)) ∈ primaryFactors ((toLinU h n y :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) :=
    mem_primaryFactors.mpr ⟨hirr, monic_X_pow_sub_C _ hp.ne_zero, by rw [hmin]⟩
  obtain ⟨-, hdim⟩ := SPLCell.Uni.natDegree_mul_mult_eq hmin hirr ⟨_, hmem⟩
  rw [natDegree_X_pow_sub_C, Module.finrank_fin_fun] at hdim
  exact ⟨_, hdim⟩

theorem uni_caseII_false [Finite K] (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (MulAut (primeFormP h (idGram K n)))) (hEp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 4) (y : primeFormUnitary h (idGram K n)) (c : Kˣ)
    (hyp : (y : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) c)
    (hnp : ∀ b : K, b ^ p ≠ (c : K))
    (hsolv : Group.IsSolvable ↥(autFix (cU h n y)))
    (hC : ∀ x ∈ E, ∃ e : primeFormUnitary h (idGram K n), cU h n e = x ∧ y * e = e * y) :
    False := by
  by_cases h2p : 2 * p ≤ n
  · exact SPLCell.Uni.not_isSolvable_autFix_of_scalar_pow_irreducible hp hp2 hp2 hnp hyp h2p hsolv
  · push Not at h2p
    obtain ⟨m, hm⟩ := exists_mul_eq_of_pow_scalar_irreducible h (by omega) hp hnp y hyp
    have hnp' : n = p := by
      rcases m with _ | _ | m
      · omega
      · omega
      · nlinarith [hp.two_le]
    have hcyc := SPLCell.Uni.isCyclic_centralizer_unitary_of_scalar_pow_irreducible (h := h) hp hp2
      hnp hyp hnp'
    let φ : Subgroup.centralizer ({y} : Set (primeFormUnitary h (idGram K n))) →*
        MulAut (primeFormP h (idGram K n)) :=
      (cU h n).comp (Subgroup.centralizer ({y} : Set (primeFormUnitary h (idGram K n)))).subtype
    have : IsCyclic φ.range :=
      isCyclic_of_surjective φ.rangeRestrict (MonoidHom.rangeRestrict_surjective _)
    refine not_elemAbelian_of_le_cyclic hp φ.range E ?_ hEp hcard
    intro x hx
    obtain ⟨e, rfl, hye⟩ := hC x hx
    exact ⟨⟨e, Subgroup.mem_centralizer_singleton_iff.2 hye.symm⟩, rfl⟩

end Cases

section CaseI

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

@[expose] noncomputable def uRep (n : ℕ) :
    primeFormUnitary h (idGram K n) →* ((Fin n → K) ≃ₗ[K] (Fin n → K)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n → K)).toMonoidHom.comp (toLinU h n)

theorem uRep_apply (e : primeFormUnitary h (idGram K n)) (v : Fin n → K) :
    uRep h n e v = ((e : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v := rfl

theorem uRep_injective : Function.Injective (uRep h n) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n → K)).injective.comp toLinU_injective

theorem semiMap_gammaHatU (M e : primeFormUnitary h (idGram K n)) (σ : K ≃+* K) (v : Fin n → K) :
    semiMap (M : GL (Fin n) K) σ (uRep h n e v) =
      uRep h n (gammaHatU h M σ e) (semiMap (M : GL (Fin n) K) σ v) := by
  rw [uRep_apply, uRep_apply, semiMap_mulVec, coe_gammaHatU, Units.val_mul, Units.val_mul,
    coe_glAut]

theorem uni_caseI_false [Finite K] (hn : 3 ≤ n) {p r k : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime) (hr5 : 5 ≤ r) (hrp : ¬ r ∣ p - 1)
    (hr2 : ¬ r ∣ p ^ 2 - 1) (hr3 : ¬ r ∣ p ^ 3 - 1) (hrne : r ≠ p)
    (E : Subgroup (MulAut (primeFormP h (idGram K n)))) (hEc : IsMulCommutative E)
    (hEp : ∀ x ∈ E, x ^ p = 1) (hcard : Nat.card E = p ^ 4)
    (hπE : ∀ x ∈ E, ∃ e : primeFormUnitary h (idGram K n), cU h n e = x)
    (y B : primeFormUnitary h (idGram K n)) (σ : K ≃+* K) (hyp : y ^ p = 1)
    (hsolv : Group.IsSolvable ↥(autFix (cU h n y)))
    (hC : ∀ e : primeFormUnitary h (idGram K n), cU h n e ∈ E → y * e = e * y)
    (hγ : (cU h n B * fU h n σ) ^ r ^ k = 1)
    (hγE : ∀ x ∈ E, MulAut.conj (cU h n B * fU h n σ) x ∈ E)
    (hnt : ∃ x ∈ E, MulAut.conj (cU h n B * fU h n σ) x ≠ x)
    (hcomm : (cU h n B * fU h n σ) * cU h n y = cU h n y * (cU h n B * fU h n σ)) : False := by
  classical
  have hn0 : 0 < n := by omega
  have : CharP K 2 := h.charP
  have hK : Nat.card K = 2 ^ (2 * f) := h.card
  have : Finite K := inferInstance
  have hpK : (p : K) ≠ 0 := SPLCell.Uni.cast_ne_zero_of_ne_char h hp hp2
  obtain ⟨hσ, T', -, hT'⟩ := pow_eq_one_conj_mul_field h hn B σ (r ^ k) hγ
  have hγ'k : gammaHatU h B σ ^ r ^ k = 1 := gammaHatU_pow_eq_one h B σ hσ hT'
  have hγy_ker : gammaHatU h B σ y * y⁻¹ ∈ (cU h n).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, conjHom_gammaHatU, mul_inv_eq_one,
      MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
    exact hcomm
  set c0 := gammaHatU h B σ y * y⁻¹ with hc0
  have hc0y : gammaHatU h B σ y = c0 * y := by rw [hc0, inv_mul_cancel_right]
  have hcy : c0 * y = y * c0 :=
    (conjHom_ker_central h hn c0 (MonoidHom.mem_ker.1 hγy_ker) y).symm
  obtain ⟨d, -, hd⟩ := (conjHom_eq_one_iff h hn c0).1 (MonoidHom.mem_ker.1 hγy_ker)
  have hc01 : c0 = 1 := by
    refine eq_one_of_gamma_smul hp hr hrne (gammaHatU h B σ) hγ'k y c0 hyp hcy hc0y ?_
    intro hcp
    have hdp : d ^ p = 1 := by
      apply scalar_injective_fin hn0 (K := K)
      rw [map_pow, ← hd, ← Subgroup.coe_pow, hcp, map_one]
      rfl
    have hfix : σ (d : K) = d :=
      fieldAut_apply_eq_of_pow_eq_one hp hp2 hr hrp hK σ hσ
        (by rw [← Units.val_pow_eq_pow_val, hdp, Units.val_one])
    apply Subtype.ext
    rw [coe_gammaHatU, hd, CFSG.RankThree.UnitaryDescent.glAut_scalar,
      show Units.map (σ : K →* K) d = d from Units.ext hfix,
      ← CFSG.RankThree.UnitaryDescent.scalar_mul_comm d (B : GL (Fin n) K), mul_inv_cancel_right]
  have hγy' : gammaHatU h B σ y = y := by rw [hc0y, hc01, one_mul]
  have hyp1 : (y : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) 1 := by
    rw [map_one, ← Subgroup.coe_pow, hyp]
    rfl
  have hx := SPLCell.Uni.squarefree_minpoly_toLinU_of_pow_scalar y hpK hyp1
  have hab : ∀ e e' : primeFormUnitary h (idGram K n), cU h n e ∈ E → cU h n e' ∈ E →
      e * e' = e' * e := by
    by_cases hq4 : 4 ≤ 2 ^ f
    · intro e e' he he'
      rcases SPLCell.Uni.autFix_not_isSolvable_or_centralizer_commute hq4 hx with h1 | h1
      · exact absurd hsolv h1
      · exact h1 e (Subgroup.mem_centralizer_singleton_iff.2 (hC e he).symm) e'
          (Subgroup.mem_centralizer_singleton_iff.2 (hC e' he').symm)
    · intro e e' he he'
      have hf : f = 1 := by
        have h1 := h.one_le
        by_contra hne1
        have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      by_contra hne'
      exact corner_false h hf hn hp hp2 hr hrp hr2 hr3 hrne E hEc hEp hcard
        (MulAut.conj (cU h n B * fU h n σ)) (by rw [← map_pow, hγ, map_one]) hγE hnt
        (gammaHatU h B σ) (fun e => conjHom_gammaHatU h B e σ) hπE y hyp hC hsolv
        (fun hall => hne' (hall e e' he he'))
  have hz : ∀ e : primeFormUnitary h (idGram K n), cU h n e ∈ E →
      Commute ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K))
        ((uRep h n e : (Fin n → K) ≃ₗ[K] (Fin n → K)) : Module.End K (Fin n → K)) := by
    intro e he
    refine LinearMap.ext fun v => ?_
    have h1 := congrArg (fun g : primeFormUnitary h (idGram K n) =>
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) (hC e he)
    simp only [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec] at h1
    exact h1
  have hzp : ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) ^ p = 1 := by
    have h1 : (toLinU h n y) ^ p = 1 := by rw [← map_pow, hyp, map_one]
    have h2 := congrArg (fun u : LinearMap.GeneralLinearGroup K (Fin n → K) =>
      (u : Module.End K (Fin n → K))) h1
    simpa [Units.val_pow_eq_pow_val] using h2
  have hfz : ∀ v, semiMap (B : GL (Fin n) K) σ (((toLinU h n y :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) v) =
      ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))
        (semiMap (B : GL (Fin n) K) σ v) := by
    intro v
    have := semiMap_gammaHatU h B y σ v
    rw [hγy'] at this
    exact this
  obtain ⟨hh, hmem, -, h5⟩ := exists_Omega_big_factor (K := K) (V := Fin n → K)
    (H := primeFormUnitary h (idGram K n)) (S := MulAut (primeFormP h (idGram K n)))
    (f := 2 * f) (p := p) (r := r) (k := k) hK hp hp2 hr hr5 hrp hr2 hr3 hrne (cU h n)
    (conjHom_ker_le_center h hn) (isCyclic_conjHom_ker h hn) E hEc hEp hcard hπE hab (uRep h n)
    (uRep_injective h) _ hzp hz (MulAut.conj (cU h n B * fU h n σ)) (gammaHatU h B σ)
    (fun e => conjHom_gammaHatU h B e σ) (by rw [← map_pow, hγ, map_one]) hγ'k hγE hnt σ hσ
    (semiMap (B : GL (Fin n) K) σ) (semiMap_bijective _ _) (fun e v => semiMap_gammaHatU h B e σ v)
    hfz
  exact SPLCell.Uni.not_isSolvable_autFix_of_mult_four hx ⟨hh, hmem⟩ (le_trans (by norm_num) h5) hsolv

end CaseI

section Final

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem uni_inner_false (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ 2 ^ f = 2)) {p r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime) (hr1 : r ∣ p ^ 2 + 1) (hr2 : ¬ r ∣ p ^ 2 - 1)
    (Ē : Subgroup (primeFormP h (idGram K n))) (ζ γ : MulAut (primeFormP h (idGram K n)))
    (hE : CFSG.Open.IsElemAbelian p Ē) (hcard : Nat.card Ē = p ^ 4) (hζp : ζ ^ p = 1)
    (hζE : ∀ x ∈ Ē, ζ x = x) (hsolv : Group.IsSolvable ↥(autFix ζ))
    (hγ : ∃ k : ℕ, γ ^ r ^ k = 1) (hγE : ∀ x ∈ Ē, γ x ∈ Ē) (hcomm : γ * ζ = ζ * γ)
    (hnt : ∃ x ∈ Ē, γ x ≠ x) : False := by
  classical
  have : Finite K := h.finite
  obtain ⟨hr5, hrp⟩ := prime_facts hp hp2 hr hr1 hr2
  obtain ⟨-, hr3, hrne⟩ := prime_facts' hp hr hr1 hr2
  have hD := zeta_mem_primeFormD h hn hne hp hp2 hr hr1 hr2 Ē ζ γ hE hcard hζp hζE hsolv hγ hγE
    hcomm hnt
  obtain ⟨y, hy⟩ := hD
  obtain ⟨B, σ, hγeq, -⟩ := exists_conj_mul_field h hn hne γ
  obtain ⟨k, hk⟩ := hγ
  subst hy
  subst hγeq
  have hstep := uni_step3 h hn hne hp hr hrp hr2 hr3 hrne Ē hE.1 hE.2 hcard y B σ hζp hζE hk hγE
    hcomm hnt
  obtain ⟨hEc', hEp', hcard', hπE, hγE', hnt'⟩ :=
    map_conj_data h hn hne Ē hE.1 hE.2 hcard _ hγE hnt
  obtain ⟨c, hcn, hyc⟩ := (conjHom_eq_one_iff h hn (y ^ p)).1 (by rw [map_pow]; exact hζp)
  have hyc' : (y : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) c := by
    rw [← Subgroup.coe_pow]
    exact hyc
  by_cases hpow : ∃ b : K, b ^ p = (c : K)
  ·
    obtain ⟨μ, hμ⟩ := hpow
    have hln : (c : K) ^ (2 ^ f + 1) = 1 := by
      have := (pow_succ_eq_one_iff_norm h c).2 hcn
      rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
    obtain ⟨ν, hν, hνn⟩ := exists_unitary_pth_root (K := K) (q := 2 ^ f) (p := p)
      (Nat.even_pow.mpr ⟨even_two, by have := h.one_le; omega⟩) hp.pos
      (by rw [h.card, ← pow_mul, mul_comm]) hln ⟨μ, hμ⟩
    have hν0 : ν ≠ 0 := by
      intro h0
      rw [h0, zero_pow hp.ne_zero] at hν
      exact c.ne_zero hν.symm
    let ν' : Kˣ := Units.mk0 ν hν0
    have hν'n : ν' ^ (2 ^ f + 1) = 1 := Units.ext (by simpa [ν'] using hνn)
    have hν'p : ν' ^ p = c := Units.ext (by simpa [ν'] using hν)
    have hsn : (ν'⁻¹) ^ (2 ^ f + 1) = 1 := by rw [inv_pow, hν'n, inv_one]
    let s : primeFormUnitary h (idGram K n) :=
      ⟨GeneralLinearGroup.scalar (Fin n) ν'⁻¹,
        scalar_mem_primeFormUnitary_one h ((pow_succ_eq_one_iff_norm h ν'⁻¹).1 hsn)⟩
    have hs1 : cU h n s = 1 :=
      (conjHom_eq_one_iff h hn s).2 ⟨ν'⁻¹, (pow_succ_eq_one_iff_norm h ν'⁻¹).1 hsn, rfl⟩
    have hy'p : (y * s) ^ p = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one]
      have hcm : Commute (y : GL (Fin n) K) (GeneralLinearGroup.scalar (Fin n) ν'⁻¹) :=
        (CFSG.RankThree.UnitaryDescent.scalar_mul_comm ν'⁻¹ (y : GL (Fin n) K)).symm
      rw [hcm.mul_pow, hyc', ← map_pow, ← map_mul, ← hν'p, inv_pow, mul_inv_cancel, map_one]
    have hcUy' : cU h n (y * s) = cU h n y := by rw [map_mul, hs1, mul_one]
    have hC'' : ∀ e : primeFormUnitary h (idGram K n), cU h n e ∈ Ē.map
        (MulAut.conj : primeFormP h (idGram K n) →* MulAut (primeFormP h (idGram K n))) →
        (y * s) * e = e * (y * s) := by
      intro e he
      have h1 := conjHom_ker_central h hn s hs1 e
      rw [mul_assoc, ← h1, ← mul_assoc, hstep e he, mul_assoc]
    exact uni_caseI_false h hn hp hp2 hr hr5 hrp hr2 hr3 hrne _ hEc' hEp' hcard' hπE (y * s) B σ
      hy'p (by rw [hcUy']; exact hsolv) hC'' hk hγE' hnt' (by rw [hcUy']; exact hcomm)
  · exact uni_caseII_false h hn hp hp2 _ hEp' hcard' y c hyc' (fun b hb => hpow ⟨b, hb⟩) hsolv
      (fun x hx => by
        obtain ⟨e, he⟩ := hπE x hx
        exact ⟨e, he, hstep e (he ▸ hx)⟩)

end Final

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellUni
