module

public import CFSG.LieType.SeitzGeneration.ClassicalOuterLeaves
public import CFSG.LieType.SeitzGeneration.OuterSUField
public import CFSG.LieType.SeitzGeneration.UnitaryHeisTensor

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.Open CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel

@[expose] def DiagLiftsCommute {ℓ f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (E : Subgroup (MulAut (primeFormP h (idGram K n)))) : Prop :=
  ∀ A B : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) A ∈ E →
    primeFormConjHom h (idGram K n) B ∈ E → A * B = B * A

@[expose] def UnitaryOuterEightPlanes : Prop :=
  ∀ (K : Type) [Field K] (h : UnitaryFieldData 2 3 K)
    (E : Subgroup (MulAut (primeFormP h (idGram K 3)))), IsElemAbelian 3 E → Nat.card E = 3 ^ 2 →
      ¬ E ≤ primeFormD h (idGram K 3) → PlaneGen E

@[expose] def UnitaryOuterNonabOn (D : ℕ → Prop) : Prop :=
  ∀ (ℓ f n p : ℕ) (K : Type) [Field K] (h : UnitaryFieldData ℓ f K), D p → 4 ≤ n → p.Prime →
    p ≠ 2 → p ∣ ℓ ^ f + 1 → p ∣ n →
    ∀ E : Subgroup (MulAut (primeFormP h (idGram K n))), IsElemAbelian p E →
      Nat.card E = p ^ 2 → E ≤ primeFormD h (idGram K n) → ¬ E ≤ innU h n →
        ¬ DiagLiftsCommute h E → PlaneGen E

@[expose] def UnitaryOuterHeisThree : Prop := UnitaryOuterNonabOn (· = 3)

@[expose] def UnitaryOuterHeisFive : Prop := UnitaryOuterNonabOn (5 ≤ ·)

@[expose] def UnitaryOuterAbFive : Prop :=
  ∀ (ℓ f n p : ℕ) (K : Type) [Field K] (h : UnitaryFieldData ℓ f K), 5 ≤ p → 4 ≤ n → p.Prime →
    p ∣ ℓ ^ f + 1 → p ∣ n →
    ∀ E : Subgroup (MulAut (primeFormP h (idGram K n))), IsElemAbelian p E →
      Nat.card E = p ^ 2 → E ≤ primeFormD h (idGram K n) → ¬ E ≤ innU h n →
        DiagLiftsCommute h E → PlaneGen E

@[expose] def UnitaryOuterAbTwo : Prop :=
  ∀ (K : Type) [Field K] (h : UnitaryFieldData 2 1 K) (n : ℕ), 4 ≤ n → 3 ∣ n →
    ∀ E : Subgroup (MulAut (primeFormP h (idGram K n))), IsElemAbelian 3 E →
      Nat.card E = 3 ^ 2 → E ≤ primeFormD h (idGram K n) → ¬ E ≤ innU h n →
        DiagLiftsCommute h E → PlaneGen E

namespace OuterUnitaryWide

section Diag

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem conjHom_eq_one_iff (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (A : primeFormUnitary h (idGram K n)) :
    primeFormConjHom h (idGram K n) A = 1 ↔ ∃ c : Kˣ, h.norm (c : K) = 1 ∧
      (A : GL (Fin n) K) = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have := primeFormPsi_eq_one_iff h hC hn ⟨A, RingEquiv.refl K⟩
  rw [primeFormPsi_apply] at this
  have h1 : primeFormFieldHom h hC (RingEquiv.refl K) = 1 := map_one _
  rw [h1, mul_one] at this
  simpa using this

noncomputable def toPn (h : UnitaryFieldData ℓ f K) (n : ℕ) :
    unitarySU ℓ f K n →* primeFormP h (idGram K n) :=
  (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)).comp
    (Subgroup.inclusion (le_of_eq (unitarySU_eq_gramSU h n)))

theorem toPn_surjective (h : UnitaryFieldData ℓ f K) (n : ℕ) :
    Function.Surjective (toPn h n) := by
  intro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨⟨g.1, (unitarySU_eq_gramSU h n).symm ▸ g.2⟩, rfl⟩

theorem conj_scalar_aux {a b : GL (Fin n) K} {u : Kˣ}
    (h : b * a = Matrix.GeneralLinearGroup.scalar (Fin n) u * (a * b)) :
    (a * b * a⁻¹)⁻¹ * b = Matrix.GeneralLinearGroup.scalar (Fin n) u := by
  have h2 : a⁻¹ * b = Matrix.GeneralLinearGroup.scalar (Fin n) u * (b * a⁻¹) := by
    calc a⁻¹ * b = a⁻¹ * (b * a) * a⁻¹ := by group
      _ = a⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin n) u * (a * b)) * a⁻¹ := by rw [h]
      _ = Matrix.GeneralLinearGroup.scalar (Fin n) u * (b * a⁻¹) := by
        rw [mul_scalarGL_mul_comm]; group
  calc (a * b * a⁻¹)⁻¹ * b = a * b⁻¹ * (a⁻¹ * b) := by group
    _ = a * b⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin n) u * (b * a⁻¹)) := by rw [h2]
    _ = Matrix.GeneralLinearGroup.scalar (Fin n) u := by
      rw [mul_assoc, mul_scalarGL_mul_comm, mul_scalarGL_mul_comm]; group

theorem conjHom_toPn_of_mem_FixUn (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    {A : primeFormUnitary h (idGram K n)} {g : unitarySU ℓ f K n}
    (hg : g ∈ FixUn ℓ f n K ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    primeFormConjHom h (idGram K n) A (toPn h n g) = toPn h n g := by
  obtain ⟨c, hc⟩ := hg
  have hdA : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det (A : GL (Fin n) K)).ne_zero
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
  have hcn : c ^ n = 1 := by
    have h1 := congrArg Matrix.det hc
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_mul, ((mem_unitarySU_iff h).1 g.2).1,
      Fintype.card_fin] at h1
    have h2 : (c ^ n - 1) * ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 0 := by
      linear_combination -h1
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hdA)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hcn
    exact zero_ne_one hcn
  obtain ⟨u, hu⟩ : ∃ u : Kˣ, (u : K) = c := ⟨Units.mk0 c hc0, rfl⟩
  have hGL : (g : GL (Fin n) K) * A = Matrix.GeneralLinearGroup.scalar (Fin n) u *
      ((A : GL (Fin n) K) * g) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_scalarGL, hu, Matrix.smul_mul,
      Matrix.one_mul]
    exact hc
  have hgram : (g : GL (Fin n) K) ∈ gramSU h (idGram K n) :=
    (le_of_eq (unitarySU_eq_gramSU h n)) g.2
  have hS : Matrix.GeneralLinearGroup.scalar (Fin n) u ∈ primeFormUnitary h (idGram K n) := by
    have hmem : (g : GL (Fin n) K) * A * ((A : GL (Fin n) K) * g)⁻¹ ∈
        primeFormUnitary h (idGram K n) :=
      mul_mem (mul_mem hgram.1 A.2) (inv_mem (mul_mem A.2 hgram.1))
    rwa [hGL, mul_inv_cancel_right] at hmem
  have hnorm : h.norm (u : K) = 1 :=
    norm_eq_one_of_scalar_mem_primeFormUnitary h (by omega) 1 hS
  have hun : u ^ n = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, hu, hcn, Units.val_one])
  have hkey := conj_scalar_aux hGL
  show primeFormConjHom h (idGram K n) A ((⟨(g : GL (Fin n) K), hgram⟩ : gramSU h (idGram K n)) :
      primeFormP h (idGram K n)) = ((⟨(g : GL (Fin n) K), hgram⟩ : gramSU h (idGram K n)) :
      primeFormP h (idGram K n))
  rw [primeFormConjHom_mk, QuotientGroup.eq]
  exact ⟨u, hnorm, hun, hkey⟩

theorem planeGen_of_closure_fixUn (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    {E : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hcl : Subgroup.closure {g : unitarySU ℓ f K n |
      ∃ B : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) B ∈ E ∧
        primeFormConjHom h (idGram K n) B ≠ 1 ∧
        g ∈ FixUn ℓ f n K ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)} = ⊤) :
    PlaneGen E := by
  have hcomap : (planeClosure E).comap (toPn h n) = ⊤ := by
    rw [eq_top_iff, ← hcl, Subgroup.closure_le]
    rintro g ⟨B, hBE, hB1, hg⟩
    exact mem_planeClosure_of_fixed hBE hB1 (conjHom_toPn_of_mem_FixUn h hn hg)
  unfold PlaneGen
  rw [eq_top_iff]
  intro z _
  obtain ⟨g, rfl⟩ := toPn_surjective h n z
  have : g ∈ (planeClosure E).comap (toPn h n) := by
    rw [hcomap]
    exact Subgroup.mem_top g
  exact this

theorem planeGen_of_diag_abelian_three (h : UnitaryFieldData ℓ f K) (hq3 : 3 ∣ ℓ ^ f + 1)
    (hq : ℓ ^ f ≠ 2) (hn : 3 ≤ n) {E : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 2) (hD : E ≤ primeFormD h (idGram K n))
    (hab : DiagLiftsCommute h E) : PlaneGen E := by
  classical
  have hfin := h.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn0 : 0 < n := by omega
  obtain ⟨e₁, he₁, e₂, he₂, he₂1, he₁₂⟩ := exists_independent_pair Nat.prime_three E hE.2 hc
  set κ := primeFormConjHom h (idGram K n) with hκ
  obtain ⟨A₁, hA₁⟩ : ∃ A : primeFormUnitary h (idGram K n), κ A = e₁ := hD he₁
  obtain ⟨A₂, hA₂⟩ : ∃ A : primeFormUnitary h (idGram K n), κ A = e₂ := hD he₂
  have hA₁E : κ A₁ ∈ E := hA₁ ▸ he₁
  have hA₂E : κ A₂ ∈ E := hA₂ ▸ he₂
  have hcomm : A₁ * A₂ = A₂ * A₁ := hab A₁ A₂ hA₁E hA₂E
  have hcube : ∀ A : primeFormUnitary h (idGram K n), κ A ∈ E →
      ∃ α : Kˣ, ((A : GL (Fin n) K) ^ 3 : GL (Fin n) K) =
        Matrix.GeneralLinearGroup.scalar (Fin n) α := by
    intro A hA
    have h1 : κ (A ^ 3) = 1 := by rw [map_pow]; exact hE.2 _ hA
    obtain ⟨c, -, hc'⟩ := (conjHom_eq_one_iff h hn (A ^ 3)).1 h1
    exact ⟨c, hc'⟩
  obtain ⟨α, hα⟩ := hcube A₁ hA₁E
  obtain ⟨β, hβ⟩ := hcube A₂ hA₂E
  have hx3 : (((A₁ : GL (Fin n) K) ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (α : K) • 1 := by rw [hα]; exact coe_scalarGL α
  have hy3 : (((A₂ : GL (Fin n) K) ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (β : K) • 1 := by rw [hβ]; exact coe_scalarGL β
  have hind : ∀ a b : ℕ, (∃ c : K, (((A₁ : GL (Fin n) K) ^ a * (A₂ : GL (Fin n) K) ^ b :
      GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1) → 3 ∣ a ∧ 3 ∣ b := by
    rintro a b ⟨c, hcab⟩
    obtain ⟨u, hu⟩ := exists_scalarGL_of_coe_eq hn0 hcab
    have hmem : (A₁ : GL (Fin n) K) ^ a * (A₂ : GL (Fin n) K) ^ b ∈
        primeFormUnitary h (idGram K n) := mul_mem (pow_mem A₁.2 a) (pow_mem A₂.2 b)
    have hnorm : h.norm (u : K) = 1 :=
      norm_eq_one_of_scalar_mem_primeFormUnitary h (by omega) 1 (hu ▸ hmem)
    have h1 : κ (A₁ ^ a * A₂ ^ b) = 1 := by
      refine (conjHom_eq_one_iff h hn _).2 ⟨u, hnorm, ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]
      exact hu
    rw [map_mul, map_pow, map_pow, hA₁, hA₂] at h1
    exact three_dvd_of_pow_mul_pow_eq_one (hE.2 _ he₁) (hE.2 _ he₂) he₂1 he₁₂ h1
  have hgen := closure_planeFixUn_abelian h hq3 hq hn A₁.2 A₂.2 (congrArg Subtype.val hcomm)
    α.ne_zero β.ne_zero hx3 hy3 hind
  have hne : ∀ k : ℕ, e₁ * e₂ ^ k ≠ 1 := by
    intro k hk
    apply he₁₂
    have : e₁ = (e₂ ^ k)⁻¹ := eq_inv_of_mul_eq_one_left hk
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k)
  have hne1 : e₁ ≠ 1 := fun h1 => he₁₂ (h1 ▸ Subgroup.one_mem _)
  have hB3E : κ (A₁ * A₂) ∈ E := by rw [map_mul]; exact E.mul_mem hA₁E hA₂E
  have hB4E : κ (A₁ * A₂ ^ 2) ∈ E := by
    rw [map_mul, map_pow]; exact E.mul_mem hA₁E (E.pow_mem hA₂E 2)
  refine planeGen_of_closure_fixUn h hn ?_
  rw [eq_top_iff, ← hgen]
  refine Subgroup.closure_mono ?_
  rintro g (((hg | hg) | hg) | hg)
  · exact ⟨A₁, hA₁E, by rw [hA₁]; exact hne1, hg⟩
  · exact ⟨A₂, hA₂E, by rw [hA₂]; exact he₂1, hg⟩
  · exact ⟨A₁ * A₂, hB3E, by rw [map_mul, hA₁, hA₂]; simpa using hne 1, hg⟩
  · exact ⟨A₁ * A₂ ^ 2, hB4E, by rw [map_mul, map_pow, hA₁, hA₂]; exact hne 2, hg⟩

end Diag

end OuterUnitaryWide

theorem unitaryHeisTensorPlanes_of_gu :
    UnitaryHeisTensorPlanes := by
  have hGU := unitaryHeisTensorPlanesGU_holds
  intro ℓ f n K _ h hq3 hn6 hn3 x y hx hy ω hω hxy hα hβ
  have hsu : ∀ g : GL (Fin n) K, g ∈ unitarySU ℓ f K n → g ∈ primeFormUnitary h (idGram K n) :=
    fun g hg => ((le_of_eq (unitarySU_eq_gramSU h n)) hg).1
  exact hGU ℓ f n K h hq3 hn6 hn3 x y (hsu x hx) (hsu y hy) ω hω hxy hα hβ

theorem unitaryOuterHeisThree_of_gu : UnitaryOuterHeisThree := by
  have hGU := unitaryHeisTensorPlanesGU_holds
  intro ℓ f n p K _ h hp3 hn4 hp hp2 hpq hpn E hE hc hD hout hab
  subst hp3
  classical
  have hn3 : 3 ≤ n := by omega
  have hn6 : 6 ≤ n := by omega
  have hn0 : 0 < n := by omega
  set κ := primeFormConjHom h (idGram K n) with hκ
  unfold DiagLiftsCommute at hab
  push Not at hab
  obtain ⟨A, B, hAE, hBE, hAB⟩ := hab
  have hscal : ∀ k : ℕ, κ (A * B ^ k) = 1 → A * B = B * A := by
    intro k hk
    obtain ⟨c, -, hc'⟩ := (OuterUnitaryWide.conjHom_eq_one_iff h hn3 (A * B ^ k)).1 hk
    have hAeq : (A : GL (Fin n) K) =
        Matrix.GeneralLinearGroup.scalar (Fin n) c * ((B : GL (Fin n) K) ^ k)⁻¹ := by
      have : (A : GL (Fin n) K) * (B : GL (Fin n) K) ^ k =
          Matrix.GeneralLinearGroup.scalar (Fin n) c := hc'
      rw [← this]
      group
    apply Subtype.ext
    change (A : GL (Fin n) K) * B = B * A
    rw [hAeq]
    have h1 : Commute (B : GL (Fin n) K) (Matrix.GeneralLinearGroup.scalar (Fin n) c) :=
      commute_scalar c _
    have h2 : Commute (B : GL (Fin n) K) (((B : GL (Fin n) K) ^ k)⁻¹) :=
      ((Commute.refl (B : GL (Fin n) K)).pow_right k).inv_right
    exact ((h1.mul_right h2).eq).symm
  have hcomm : κ A * κ B = κ B * κ A :=
    congrArg Subtype.val (hE.1.is_comm.comm (⟨_, hAE⟩ : E) ⟨_, hBE⟩)
  obtain ⟨ω', hω'N, hω'⟩ : ∃ c : Kˣ, h.norm (c : K) = 1 ∧
      ((B * A * (A * B)⁻¹ : primeFormUnitary h (idGram K n)) : GL (Fin n) K) =
        Matrix.GeneralLinearGroup.scalar (Fin n) c := by
    refine (OuterUnitaryWide.conjHom_eq_one_iff h hn3 _).1 ?_
    rw [map_mul, map_mul, map_inv, map_mul, hcomm]
    exact mul_inv_cancel _
  have hBA : (B : GL (Fin n) K) * A =
      Matrix.GeneralLinearGroup.scalar (Fin n) ω' * ((A : GL (Fin n) K) * B) := by
    have : (B : GL (Fin n) K) * A * ((A : GL (Fin n) K) * B)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin n) ω' := hω'
    rw [← this]
    group
  have hBAm : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((A : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (ω' : K) • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hBA
    simp only [Units.val_mul, coe_scalarGL, Matrix.smul_mul, Matrix.one_mul] at this
    exact this
  have hcube : ∀ C : primeFormUnitary h (idGram K n), κ C ∈ E →
      ∃ α : Kˣ, ((C : GL (Fin n) K) ^ 3 : GL (Fin n) K) =
        Matrix.GeneralLinearGroup.scalar (Fin n) α := by
    intro C hC
    have h1 : κ (C ^ 3) = 1 := by rw [map_pow]; exact hE.2 _ hC
    obtain ⟨c, -, hc'⟩ := (OuterUnitaryWide.conjHom_eq_one_iff h hn3 (C ^ 3)).1 h1
    exact ⟨c, hc'⟩
  obtain ⟨α, hα⟩ := hcube A hAE
  obtain ⟨β, hβ⟩ := hcube B hBE
  have hα3 : (((A : GL (Fin n) K) ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (α : K) • 1 := by rw [hα]; exact coe_scalarGL α
  have hβ3 : (((B : GL (Fin n) K) ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (β : K) • 1 := by rw [hβ]; exact coe_scalarGL β
  have hω3 : (ω' : K) ^ 3 = 1 := cube_eq_one_of_smul_comm hn0 α.ne_zero hα3 hBAm
  have hω1 : (ω' : K) ≠ 1 := by
    intro h1
    apply hAB
    have : (B : GL (Fin n) K) * A = (A : GL (Fin n) K) * B := by
      rw [hBA, show ω' = 1 from Units.ext h1, map_one, one_mul]
    exact (Subtype.ext this).symm
  have hprim : IsPrimitiveRoot (ω' : K) 3 := by
    have h1 := IsPrimitiveRoot.orderOf (ω' : K)
    rwa [orderOf_eq_prime hω3 hω1] at h1
  have hcl := hGU ℓ f n K h hpq hn6 hpn (A : GL (Fin n) K) (B : GL (Fin n) K) A.2 B.2 (ω' : K)
    hprim hBAm ⟨α, hα3⟩ ⟨β, hβ3⟩
  have hA1 : κ A ≠ 1 := fun h1 => hAB (hscal 0 (by rw [pow_zero, mul_one]; exact h1))
  have hB1 : κ B ≠ 1 := by
    intro h1
    apply hAB
    obtain ⟨c, -, hc'⟩ := (OuterUnitaryWide.conjHom_eq_one_iff h hn3 B).1 h1
    apply Subtype.ext
    change (A : GL (Fin n) K) * B = B * A
    rw [hc']
    exact (commute_scalar c (A : GL (Fin n) K)).eq
  have hAB1 : κ (A * B) ≠ 1 := fun h1 => hAB (hscal 1 (by rw [pow_one]; exact h1))
  have hAB2 : κ (A * B ^ 2) ≠ 1 := fun h1 => hAB (hscal 2 h1)
  have hAB1E : κ (A * B) ∈ E := by rw [map_mul]; exact E.mul_mem hAE hBE
  have hAB2E : κ (A * B ^ 2) ∈ E := by
    rw [map_mul, map_pow]; exact E.mul_mem hAE (E.pow_mem hBE 2)
  refine OuterUnitaryWide.planeGen_of_closure_fixUn h hn3 ?_
  rw [eq_top_iff, ← hcl]
  refine Subgroup.closure_mono ?_
  rintro g (((hg | hg) | hg) | hg)
  · exact ⟨A, hAE, hA1, hg⟩
  · exact ⟨B, hBE, hB1, hg⟩
  · exact ⟨A * B, hAB1E, hAB1, hg⟩
  · exact ⟨A * B ^ 2, hAB2E, hAB2, hg⟩

section Leaf



theorem unitaryOuterHeisThree : UnitaryOuterHeisThree :=
  unitaryOuterHeisThree_of_gu

theorem planeGen_outer_su_wide (h8 : UnitaryOuterEightPlanes) (hH3 : UnitaryOuterHeisThree)
    (hH5 : UnitaryOuterHeisFive) (hA2 : UnitaryOuterAbTwo) (hA5 : UnitaryOuterAbFive)
    {ℓ f n p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (hn3 : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (hpq : p ∣ ℓ ^ f + 1) (hpn : p ∣ n) {E : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2) (hout : ¬ E ≤ innU h n) : PlaneGen E := by
  classical
  by_cases hD : E ≤ primeFormD h (idGram K n)
  · by_cases hn : n = 3
    · subst hn
      have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hpn
      subst hp3
      exact planeGen_of_unitaryDiagAut unitaryHeisCore (unitaryOuterHeisCore_of_finite_cases
          HeisSmall.outerB12AtCard_five HeisSmall.outerB12AtCard_eight
          HeisSmall.outerB12AtCard_eleven) h hpq
        (fun h2 => hne ⟨rfl, h2⟩) hE hc hD
    · have hn4 : 4 ≤ n := by omega
      rcases prime_eq_three_or_five_le hp hp2 with rfl | hp5
      · by_cases hab : DiagLiftsCommute h E
        · by_cases hq2 : ℓ ^ f = 2
          · obtain ⟨hℓ2, hf1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).1 hq2
            subst hℓ2
            subst hf1
            exact hA2 K h n hn4 hpn E hE hc hD hout hab
          · exact OuterUnitaryWide.planeGen_of_diag_abelian_three h hpq hq2 hn3 hE hc hD hab
        · exact hH3 ℓ f n 3 K h rfl hn4 hp hp2 hpq hpn E hE hc hD hout hab
      · by_cases hab : DiagLiftsCommute h E
        · exact hA5 ℓ f n p K h hp5 hn4 hp hpq hpn E hE hc hD hout hab
        · exact hH5 ℓ f n p K h hp5 hn4 hp hp2 hpq hpn E hE hc hD hout hab
  · refine planeGen_outer_su_field h hn3 hne hp hp2 hpℓ hE hc hD ?_
    intro hn3' hq2 hpf
    subst hn3'
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hpn
    subst hp3
    obtain ⟨hℓ2, hf1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).1 hq2
    subst hℓ2
    have hf3 : f = 3 := by omega
    subst hf3
    exact h8 K h E hE hc hD

theorem seitzOuterUnitaryWide_of (h8 : UnitaryOuterEightPlanes) (hH3 : UnitaryOuterHeisThree)
    (hH5 : UnitaryOuterHeisFive) (hA2 : UnitaryOuterAbTwo) (hA5 : UnitaryOuterAbFive) :
    SeitzOuterUnitaryWide := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, -, ⟨m, q, hd⟩, hlift⟩
  subst hd
  obtain ⟨hℓ, hf, hn3, hne, F, _, hU, ⟨θ⟩⟩ :=
    CFSG.RankThree.PartOne.exists_primeFormP_of_statedClassicalModel_PSU
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m q hv
        (MulEquiv.refl (Cat ⟨.twistedA m q, hv⟩)))
  have hl : p ∣ q.card + 1 ∧ p ∣ m + 1 := by simpa [CentralPrimeFree] using hlift
  have hpq : p ∣ q.p ^ q.exponent + 1 := by
    rw [← TauCeti.PrimePower.card_def]
    exact hl.1
  refine planeGen_of_outer_model θ ?_
  exact planeGen_outer_su_wide h8 hH3 hH5 hA2 hA5 hU hn3 hne hp hp2 (by simpa using hpd) hpq
    hl.2 (isElemAbelian_map_congr θ hE) ((card_map_congr θ E).trans hc)
    (not_le_range_conj_map_congr θ hout)

theorem seitzOuterUnitaryWide_of_gu (h8 : UnitaryOuterEightPlanes)
    (hH5 : UnitaryOuterHeisFive) (hA2 : UnitaryOuterAbTwo) (hA5 : UnitaryOuterAbFive) :
    SeitzOuterUnitaryWide :=
  seitzOuterUnitaryWide_of h8 unitaryOuterHeisThree_of_gu hH5 hA2 hA5

end Leaf

end CFSG.LieType.SeitzGeneration
