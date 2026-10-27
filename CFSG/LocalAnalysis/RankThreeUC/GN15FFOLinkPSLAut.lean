module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearAut
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner
public import CFSG.RankThree.PartOne.S11d.OutLinear

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification
open CFSG.QuasithinUnique.K1 (stdAut descendAut_stdAut)
open scoped commutatorElement

section Scalars

variable {K : Type} [Field K] {n : ℕ}

theorem scalarElement_mul (c d : Kˣ) (hc : c ^ n = 1) (hd : d ^ n = 1) :
    scalarElement c hc * scalarElement d hd =
      scalarElement (c * d) (by rw [mul_pow, hc, hd, one_mul]) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement, coe_scalarElement, ← map_mul,
    ← Units.val_mul]
  rfl

theorem scalarElement_one : scalarElement (1 : Kˣ) (one_pow n) = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [coe_scalarElement, Units.val_one, map_one]
  rfl

theorem scalarElement_inv (c : Kˣ) (hc : c ^ n = 1) :
    (scalarElement c hc)⁻¹ = scalarElement c⁻¹ (by rw [inv_pow, hc, inv_one]) := by
  apply inv_eq_of_mul_eq_one_right
  rw [scalarElement_mul]
  convert scalarElement_one (K := K) (n := n)
  exact mul_inv_cancel c

theorem slGraphAut_scalarElement (c : Kˣ) (hc : c ^ n = 1) :
    CatalogueBGraphForm.slGraphAut n K (scalarElement c hc) =
      scalarElement c⁻¹ (by rw [inv_pow, hc, inv_one]) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [CatalogueBGraphForm.slGraphAut_matrix, scalarElement_inv, coe_scalarElement,
    Matrix.scalar_apply, Matrix.diagonal_transpose]


theorem slConjugation_scalarElement (A : GL (Fin n) K) (c : Kˣ) (hc : c ^ n = 1) :
    CatalogueBHigherLinearAction.slConjugation n K A (scalarElement c hc) = scalarElement c hc := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hcomm : Commute (Matrix.scalar (Fin n) (c : K)) (A.val : Matrix (Fin n) (Fin n) K) :=
    Matrix.scalar_commute _ (fun r => Commute.all _ _) _
  have h2 : A.val * (A⁻¹).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [CatalogueBHigherLinearAction.slConjugation_matrix, coe_scalarElement, ← hcomm.eq,
    Matrix.mul_assoc, h2, Matrix.mul_one]

theorem slFieldAut_scalarElement (σ : K ≃+* K) (c : Kˣ) (hc : c ^ n = 1) :
    CatalogueBHigherLinearField.slFieldAut (Fin n) K σ (scalarElement c hc) =
      scalarElement (Units.map (σ : K →* K) c) (by rw [← map_pow, hc, map_one]) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change σ ((scalarElement c hc : Matrix (Fin n) (Fin n) K) i j) = _
  rw [coe_scalarElement, coe_scalarElement, Matrix.scalar_apply, Matrix.scalar_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.diagonal_apply_ne _ h]

theorem stdAut_scalarElement (A : GL (Fin n) K) (σ : K ≃+* K) (ε : ℕ) (hε : ε ≤ 1) (c : Kˣ)
    (hc : c ^ n = 1) :
    stdAut A σ ε (scalarElement c hc) =
      scalarElement (if ε = 0 then Units.map (σ : K →* K) c else (Units.map (σ : K →* K) c)⁻¹)
        (by
          have h : (Units.map (σ : K →* K) c) ^ n = 1 := by rw [← map_pow, hc, map_one]
          split_ifs
          · exact h
          · rw [inv_pow, h, inv_one]) := by
  unfold stdAut
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · simp only [pow_zero, mul_one, if_true]
    change CatalogueBHigherLinearAction.slConjugation n K A
        (CatalogueBHigherLinearField.slFieldAut (Fin n) K σ (scalarElement c hc)) = _
    rw [slFieldAut_scalarElement, slConjugation_scalarElement]
  · simp only [pow_one, one_ne_zero, if_false]
    change CatalogueBHigherLinearAction.slConjugation n K A
        (CatalogueBHigherLinearField.slFieldAut (Fin n) K σ
          (CatalogueBGraphForm.slGraphAut n K (scalarElement c hc))) = _
    rw [slGraphAut_scalarElement, slFieldAut_scalarElement, slConjugation_scalarElement]
    congr 1

theorem exists_exponent [Finite K] (σ : K ≃+* K) (ε : ℕ) :
    ∃ e : ℤ, ∀ x : Kˣ,
      (if ε = 0 then Units.map (σ : K →* K) x else (Units.map (σ : K →* K) x)⁻¹) = x ^ e := by
  obtain ⟨s, hs⟩ := MonoidHom.map_cyclic (Units.map (σ : K →* K))
  by_cases hε : ε = 0
  · exact ⟨s, fun x => by simp only [hε, if_true]; exact hs x⟩
  · exact ⟨-s, fun x => by simp only [hε, if_false]; rw [hs x, _root_.zpow_neg]⟩

end Scalars

section Scl

variable {K : Type} [Field K] [Finite K] {n : ℕ}

@[expose] noncomputable def sclHom (n : ℕ) (K : Type) [Field K] :
    rootsOfUnity n K →* SpecialLinearGroup (Fin n) K where
  toFun c := scalarElement (c : Kˣ) ((mem_rootsOfUnity n (c : Kˣ)).1 c.2)
  map_one' := scalarElement_one
  map_mul' _ _ := (scalarElement_mul _ _ _ _).symm

omit [Finite K] in
private theorem zpow_pow_comm' (c : Kˣ) (k : ℤ) (n : ℕ) : (c ^ k) ^ n = (c ^ n) ^ k := by
  rw [← zpow_natCast, ← zpow_natCast c n, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]

omit [Finite K] in
theorem sclHom_zpow (c : Kˣ) (hc : c ^ n = 1) (k : ℤ) :
    (scalarElement c hc) ^ k =
      scalarElement (c ^ k) (by rw [zpow_pow_comm', hc, _root_.one_zpow]) := by
  have h := map_zpow (sclHom n K) (⟨c, (mem_rootsOfUnity n c).2 hc⟩ : rootsOfUnity n K) k
  exact h.symm

omit [Finite K] in
theorem stdAut_scalarElement_exp (A : GL (Fin n) K) (σ : K ≃+* K) (ε : ℕ) (hε : ε ≤ 1) (e₀ : ℤ)
    (he₀ : ∀ x : Kˣ,
      (if ε = 0 then Units.map (σ : K →* K) x else (Units.map (σ : K →* K) x)⁻¹) = x ^ e₀)
    (c : Kˣ) (hc : c ^ n = 1) :
    stdAut A σ ε (scalarElement c hc) = (scalarElement c hc) ^ e₀ := by
  rw [stdAut_scalarElement A σ ε hε c hc, sclHom_zpow]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [coe_scalarElement, coe_scalarElement, he₀ c]


end Scl

section PLevel

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem commutator_mem_linearAutGroup (hn : 3 ≤ n) (γ α : MulAut (projectiveSL n K))
    (hα : α ∈ semilinearAutGroup n K) : ⁅γ, α⁆ ∈ linearAutGroup n K := by
  obtain ⟨hgenTop, hgen⟩ := automorphism_generation (K := K) hn
  obtain ⟨hID, -, hDn, -, -, ⟨g, -, hg⟩, -, hidx, -, -⟩ :=
    standard_outer_quotients (n := n) (K := K)
  have htrans := standard_automorphism_transport (K := K) (n := n)
  have hDnorm : (linearAutGroup n K).Normal := by
    refine ⟨fun d hd γ => ?_⟩
    have hγ : γ ∈ standardAutGroup n K := hgenTop ▸ Subgroup.mem_top γ
    have hd' : d ∈ standardAutGroup n K := hgenTop ▸ Subgroup.mem_top d
    have := hDn.conj_mem ⟨d, hd'⟩ (Subgroup.mem_subgroupOf.mpr hd) ⟨γ, hγ⟩
    exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨B, τ, rfl⟩ := mem_semilinearAutGroup_iff.mp hα
  obtain ⟨A, σ, ε, hε, rfl⟩ := hgen γ
  set π := QuotientGroup.mk' (linearAutGroup n K) with hπ
  have hπc : ∀ C : GL (Fin n) K, π (conjAut n K C) = 1 := fun C =>
    (QuotientGroup.eq_one_iff _).mpr (conjAut_mem_linearAutGroup C)
  have hfσ : Commute (π (fieldAut n K σ)) (π (fieldAut n K τ)) := by
    have h1 : fieldAut n K σ * fieldAut n K τ = fieldAut n K τ * fieldAut n K σ := by
      rw [htrans.2.1, htrans.2.1, CFSG.RankThree.PartOne.OutStructure.ringAut_comm K σ τ]
    have h3 := congrArg π h1
    rw [map_mul π, map_mul π] at h3
    exact h3
  have hδf : Commute (π (dualAut n K)) (π (fieldAut n K τ)) := by
    have h1 : dualAut n K * fieldAut n K τ = fieldAut n K τ * dualAut n K := by
      have h2 := htrans.2.2.2.2.2.1 τ
      calc dualAut n K * fieldAut n K τ
          = (dualAut n K * fieldAut n K τ * dualAut n K) * dualAut n K := by
            rw [mul_assoc (dualAut n K * fieldAut n K τ), htrans.2.2.2.1, mul_one]
        _ = fieldAut n K τ * dualAut n K := by rw [h2]
    have h3 := congrArg π h1
    rw [map_mul π, map_mul π] at h3
    exact h3
  have hc : Commute (π (conjAut n K A * fieldAut n K σ * dualAut n K ^ ε))
      (π (conjAut n K B * fieldAut n K τ)) := by
    rw [map_mul, map_mul, map_mul, hπc, hπc, one_mul, one_mul, map_pow]
    exact (hfσ.mul_left (hδf.pow_left ε))
  have h1 : π ⁅conjAut n K A * fieldAut n K σ * dualAut n K ^ ε,
      conjAut n K B * fieldAut n K τ⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr hc
  exact (QuotientGroup.eq_one_iff _).mp h1

omit [Finite K] in
private theorem det_inverseTranspose' (B : GL (Fin n) K) :
    GeneralLinearGroup.det (GeneralLinearGroup.inverseTranspose B) =
      (GeneralLinearGroup.det B)⁻¹ := by
  refine Units.ext ?_
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_inverseTranspose, det_transpose,
    ← GeneralLinearGroup.val_det_apply, map_inv]

theorem mem_linearAutGroup_of_inverted (hn : 3 ≤ n) {r : ℕ} (hr2 : Odd r)
    {βa βy : MulAut (projectiveSL n K)} (hinv : βa * βy * βa⁻¹ = βy⁻¹)
    (hpow : βy ^ r ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range) :
    βy ∈ linearAutGroup n K := by
  obtain ⟨hgenTop, hgen⟩ := automorphism_generation (K := K) hn
  obtain ⟨hID, -, hDn, -, -, ⟨g, -, hg⟩, -, hidx, -, -⟩ :=
    standard_outer_quotients (n := n) (K := K)
  have : Finite (MulAut (projectiveSL n K)) :=
    CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.finite_mulAut_projectiveSL n
  have hidx' : (semilinearAutGroup n K).index ≤ 2 := by
    have h2 : (semilinearAutGroup n K).relIndex (standardAutGroup n K) ≤ 2 := hidx
    rwa [hgenTop, Subgroup.relIndex_top_right] at h2
  have hyE : βy ∈ semilinearAutGroup n K :=
    CFSG.RankThree.PartOne.OutStructure.mem_of_pow_mem_of_index_le_two _ hidx' hr2
      (linearAutGroup_le_semilinearAutGroup (hID hpow))
  have hcomm := commutator_mem_linearAutGroup hn βa βy hyE
  have hc : ⁅βa, βy⁆ = βy⁻¹ * βy⁻¹ := by
    rw [commutatorElement_def]
    calc βa * βy * βa⁻¹ * βy⁻¹ = (βa * βy * βa⁻¹) * βy⁻¹ := rfl
      _ = βy⁻¹ * βy⁻¹ := by rw [hinv]
  rw [hc] at hcomm
  obtain ⟨m, hm⟩ := hr2
  have h2 : βy ^ 2 ∈ linearAutGroup n K := by
    have : βy ^ 2 = (βy⁻¹ * βy⁻¹)⁻¹ := by rw [_root_.mul_inv_rev, inv_inv, pow_two]
    rw [this]
    exact inv_mem hcomm
  have h3 : βy = (βy ^ 2) ^ (m + 1) * (βy ^ r)⁻¹ := by
    rw [← pow_mul, hm, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, pow_succ', mul_assoc,
      mul_inv_cancel, mul_one]
  rw [h3]
  exact mul_mem (pow_mem h2 _) (inv_mem (hID hpow))

omit [Finite K] in
private theorem conj_formula (B A : GL (Fin n) K) (σ : K ≃+* K) :
    (conjAut n K B * fieldAut n K σ) * conjAut n K A * (conjAut n K B * fieldAut n K σ)⁻¹ =
      conjAut n K (B * GeneralLinearGroup.map (σ : K →+* K) A * B⁻¹) := by
  have htrans := standard_automorphism_transport (K := K) (n := n)
  calc (conjAut n K B * fieldAut n K σ) * conjAut n K A * (conjAut n K B * fieldAut n K σ)⁻¹
      = conjAut n K B * (fieldAut n K σ * conjAut n K A * (fieldAut n K σ)⁻¹) *
          (conjAut n K B)⁻¹ := by group
    _ = _ := by rw [htrans.2.2.1, ← map_inv, ← map_mul, ← map_mul]

omit [Finite K] in
private theorem conj_formula_std (B A : GL (Fin n) K) (σ : K ≃+* K) (ε : ℕ) (hε : ε ≤ 1) :
    (conjAut n K B * fieldAut n K σ * dualAut n K ^ ε) * conjAut n K A *
        (conjAut n K B * fieldAut n K σ * dualAut n K ^ ε)⁻¹ =
      conjAut n K (B * GeneralLinearGroup.map (σ : K →+* K)
        (if ε = 0 then A else GeneralLinearGroup.inverseTranspose A) * B⁻¹) := by
  have htrans := standard_automorphism_transport (K := K) (n := n)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · simp only [pow_zero, mul_one, if_true]
    exact conj_formula B A σ
  · simp only [pow_one, one_ne_zero, if_false]
    have hδ : (dualAut n K)⁻¹ = dualAut n K := inv_eq_of_mul_eq_one_right htrans.2.2.2.1
    calc (conjAut n K B * fieldAut n K σ * dualAut n K) * conjAut n K A *
          (conjAut n K B * fieldAut n K σ * dualAut n K)⁻¹
        = (conjAut n K B * fieldAut n K σ) * (dualAut n K * conjAut n K A * dualAut n K) *
            (conjAut n K B * fieldAut n K σ)⁻¹ := by
          rw [_root_.mul_inv_rev, hδ]; group
      _ = _ := by
          rw [htrans.2.2.2.2.1]
          exact conj_formula B _ σ

theorem det_relation (hn : 3 ≤ n) (A' B : GL (Fin n) K) (σ : K ≃+* K) (ε : ℕ) (hε : ε ≤ 1)
    (h : (conjAut n K B * fieldAut n K σ * dualAut n K ^ ε) * conjAut n K A' *
        (conjAut n K B * fieldAut n K σ * dualAut n K ^ ε)⁻¹ = (conjAut n K A')⁻¹) :
    ∃ u : Kˣ, (if ε = 0 then Units.map (σ : K →* K) (GeneralLinearGroup.det A')
        else (Units.map (σ : K →* K) (GeneralLinearGroup.det A'))⁻¹) *
        GeneralLinearGroup.det A' = u ^ n := by
  rw [conj_formula_std B A' σ ε hε, ← map_inv] at h
  have h1 : conjAut n K ((B * GeneralLinearGroup.map (σ : K →+* K)
        (if ε = 0 then A' else GeneralLinearGroup.inverseTranspose A') * B⁻¹) * A') = 1 := by
    rw [map_mul, h, ← map_mul, inv_mul_cancel, map_one]
  obtain ⟨u, hu⟩ := (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.conjAut_eq_one_iff hn _).mp h1
  refine ⟨u, ?_⟩
  have h2 := congrArg GeneralLinearGroup.det hu
  rw [map_mul, map_mul, map_mul, map_inv, GeneralLinearGroup.det_scalar, Fintype.card_fin] at h2
  have h3 : GeneralLinearGroup.det (GeneralLinearGroup.map (σ : K →+* K)
      (if ε = 0 then A' else GeneralLinearGroup.inverseTranspose A')) =
      (if ε = 0 then Units.map (σ : K →* K) (GeneralLinearGroup.det A')
        else (Units.map (σ : K →* K) (GeneralLinearGroup.det A'))⁻¹) := by
    split_ifs
    · exact GeneralLinearGroup.map_det _ _
    · rw [GeneralLinearGroup.map_det, det_inverseTranspose', map_inv]
      rfl
  rw [h3] at h2
  generalize (if ε = 0 then Units.map (σ : K →* K) (GeneralLinearGroup.det A')
    else (Units.map (σ : K →* K) (GeneralLinearGroup.det A'))⁻¹) = X at h2 ⊢
  rw [← h2, mul_comm (GeneralLinearGroup.det B) X, mul_inv_cancel_right]

theorem det_pow_mem_range (hn : 3 ≤ n) {A : GL (Fin n) K} {k : ℕ}
    (hk : (conjAut n K A) ^ k ∈
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range) :
    ∃ u : Kˣ, GeneralLinearGroup.det A ^ k = u ^ n := by
  have hAk : conjAut n K A ^ k = conjAut n K (A ^ k) := (map_pow _ _ _).symm
  rw [hAk] at hk
  obtain ⟨s, hs⟩ := hk
  obtain ⟨g, rfl⟩ := proj_surjective n K s
  rw [← conjAut_toGL] at hs
  have h1 : conjAut n K (A ^ k * (SpecialLinearGroup.toGL g)⁻¹) = 1 := by
    rw [map_mul, ← hs, map_inv, mul_inv_cancel]
  obtain ⟨u, hu⟩ :=
    (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.conjAut_eq_one_iff hn _).mp h1
  have hAu : A ^ k = GeneralLinearGroup.scalar (Fin n) u * SpecialLinearGroup.toGL g := by
    rw [← hu]; group
  refine ⟨u, ?_⟩
  have h2 := congrArg GeneralLinearGroup.det hAu
  rw [map_pow, map_mul] at h2
  have h3 : GeneralLinearGroup.det (SpecialLinearGroup.toGL g) = 1 := by
    ext
    simp
  rw [h2, h3, GeneralLinearGroup.det_scalar, Fintype.card_fin, mul_one]

theorem dvd_of_det_relations {r : ℕ} (hr : r.Prime) {d u : Kˣ} {e : ℤ}
    (hd : ¬ ∃ μ : Kˣ, d = μ ^ n) (hdr : ∃ μ : Kˣ, d ^ r = μ ^ n) (h : d ^ e * d = u ^ n) :
    (r : ℤ) ∣ e + 1 := by
  have : Fact r.Prime := ⟨hr⟩
  let H : Subgroup Kˣ := (powMonoidHom n : Kˣ →* Kˣ).range
  have hmem : ∀ x : Kˣ, x ∈ H ↔ ∃ μ : Kˣ, x = μ ^ n := fun x => by
    simp only [H, MonoidHom.mem_range, powMonoidHom_apply]
    exact ⟨fun ⟨μ, hμ⟩ => ⟨μ, hμ.symm⟩, fun ⟨μ, hμ⟩ => ⟨μ, hμ.symm⟩⟩
  have hd1 : (d : Kˣ ⧸ H) ≠ 1 := fun h1 => hd ((hmem d).1 ((QuotientGroup.eq_one_iff d).1 h1))
  have hdr1 : (d : Kˣ ⧸ H) ^ r = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hmem]
    exact hdr
  have hord : orderOf (d : Kˣ ⧸ H) = r := orderOf_eq_prime hdr1 hd1
  have h2 : (d : Kˣ ⧸ H) ^ (e + 1) = 1 := by
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff, hmem, _root_.zpow_add_one, h]
    exact ⟨u, rfl⟩
  have := orderOf_dvd_iff_zpow_eq_one.2 h2
  rwa [hord] at this

theorem prime_dvd_exponent_add_one (hn : 3 ≤ n) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {βa βy : MulAut (projectiveSL n K)} (hinv : βa * βy * βa⁻¹ = βy⁻¹)
    (hpow : βy ^ r ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range)
    (hne : βy ∉ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range)
    (B : GL (Fin n) K) (σ : K ≃+* K) (ε : ℕ) (hε : ε ≤ 1)
    (hβa : βa = conjAut n K B * fieldAut n K σ * dualAut n K ^ ε) (e : ℤ)
    (he : ∀ x : Kˣ,
      (if ε = 0 then Units.map (σ : K →* K) x else (Units.map (σ : K →* K) x)⁻¹) = x ^ e) :
    (r : ℤ) ∣ e + 1 := by
  have hD := mem_linearAutGroup_of_inverted hn (hr.odd_of_ne_two hr2) hinv hpow
  obtain ⟨A', rfl⟩ := mem_linearAutGroup_iff.mp hD
  rw [hβa] at hinv
  obtain ⟨u, hu⟩ := det_relation hn A' B σ ε hε hinv
  rw [he] at hu
  have hd : ¬ ∃ μ : Kˣ, GeneralLinearGroup.det A' = μ ^ n := fun ⟨μ, hμ⟩ =>
    hne (conjAut_mem_range_conj_of_det_eq_pow hμ)
  have hdr := det_pow_mem_range hn hpow
  exact dvd_of_det_relations hr hd hdr hu

end PLevel

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO
