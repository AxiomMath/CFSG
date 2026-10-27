module

public import CFSG.ClassicalGroups.SpecialLinear.Transitive
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.CGT.T75N.L29Levi

public section

namespace CFSG.ClassicalGroups.SpecialLinear

open Matrix CFSG.Open CFSG.Open.StatedAPI
open scoped commutatorElement

variable {K : Type} [Field K]

private theorem exists_specialLinearGroup_smul_eq {n : ℕ} (hn : 2 ≤ n) {x y : Fin n → K}
    (hx : x ≠ 0) (hy : y ≠ 0) : ∃ g : SpecialLinearGroup (Fin n) K, g • x = y := by
  obtain ⟨A, hA, hAx⟩ := exists_statedSL_mulVec_eq hn hx hy
  exact ⟨⟨(A : Matrix (Fin n) (Fin n) K), det_of_mem_statedSL hA⟩, hAx⟩

section Row

variable {m : ℕ}

private def rowMat (ρ : Fin (m + 1) → K) : Matrix (Fin (m + 2)) (Fin (m + 2)) K :=
  Matrix.of fun i j =>
    Fin.cases (Fin.cases 1 ρ j)
      (fun i' => Fin.cases 0 (fun j' => (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i' j') j) i

@[simp] private theorem rowMat_zero_zero (ρ : Fin (m + 1) → K) : rowMat ρ 0 0 = 1 := rfl

@[simp] private theorem rowMat_zero_succ (ρ : Fin (m + 1) → K) (j : Fin (m + 1)) :
    rowMat ρ 0 j.succ = ρ j := rfl

@[simp] private theorem rowMat_succ_zero (ρ : Fin (m + 1) → K) (i : Fin (m + 1)) :
    rowMat ρ i.succ 0 = 0 := rfl

@[simp] private theorem rowMat_succ_succ (ρ : Fin (m + 1) → K) (i j : Fin (m + 1)) :
    rowMat ρ i.succ j.succ = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i j := rfl

private theorem det_rowMat (ρ : Fin (m + 1) → K) : (rowMat ρ).det = 1 := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [rowMat_succ_zero, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
    rowMat_zero_zero, Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
  rw [show (rowMat ρ).submatrix Fin.succ Fin.succ = 1 from by ext i j; rfl, Matrix.det_one]

private theorem rowMat_mul (ρ ρ' : Fin (m + 1) → K) :
    rowMat ρ * rowMat ρ' = rowMat (ρ + ρ') := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [Matrix.one_apply, add_comm]

private theorem rowMat_zero : rowMat (0 : Fin (m + 1) → K) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

private def rowHom (m : ℕ) (K : Type) [Field K] :
    Multiplicative (Fin (m + 1) → K) →* SpecialLinearGroup (Fin (m + 2)) K where
  toFun ρ := ⟨rowMat (Multiplicative.toAdd ρ), det_rowMat _⟩
  map_one' := Subtype.ext rowMat_zero
  map_mul' ρ ρ' := Subtype.ext (rowMat_mul _ _).symm

private theorem rowHom_single (j : Fin (m + 1)) (c : K) :
    rowHom m K (Multiplicative.ofAdd (Pi.single j c)) =
      SpecialLinearGroup.transvection (Fin.succ_ne_zero j).symm c := by
  apply Subtype.ext
  show rowMat (Pi.single j c) = Matrix.transvection 0 j.succ c
  ext a b
  refine Fin.cases ?_ (fun a' => ?_) a <;> refine Fin.cases ?_ (fun b' => ?_) b
  · simp [Matrix.transvection, Matrix.single_apply, Fin.succ_ne_zero]
  · by_cases h : b' = j
    · subst h
      simp [Matrix.transvection, Matrix.single_apply, (Fin.succ_ne_zero _).symm]
    · simp [Matrix.transvection, Matrix.single_apply, Pi.single_apply, h, Ne.symm h,
        (Fin.succ_ne_zero _).symm]
  · simp [Matrix.transvection, Matrix.single_apply, Fin.succ_ne_zero]
  · simp [Matrix.transvection, Matrix.single_apply, Matrix.one_apply, (Fin.succ_ne_zero a').symm]

end Row

theorem commutator_stabilizer_single_zero {m : ℕ} (hm : 2 ≤ m) :
    ⁅MulAction.stabilizer (SpecialLinearGroup (Fin (m + 2)) K) (Pi.single 0 1 : Fin (m + 2) → K),
      MulAction.stabilizer (SpecialLinearGroup (Fin (m + 2)) K)
        (Pi.single 0 1 : Fin (m + 2) → K)⁆ =
      MulAction.stabilizer (SpecialLinearGroup (Fin (m + 2)) K)
        (Pi.single 0 1 : Fin (m + 2) → K) := by
  set e₀ : Fin (m + 2) → K := Pi.single 0 1 with he₀
  set S := MulAction.stabilizer (SpecialLinearGroup (Fin (m + 2)) K) e₀ with hS
  refine le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb => ?_) fun g hg => ?_
  · rw [commutatorElement_def]
    exact S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)
  have hmem : ∀ x : SpecialLinearGroup (Fin (m + 2)) K,
      x ∈ S ↔ (x : Matrix (Fin (m + 2)) (Fin (m + 2)) K) *ᵥ e₀ = e₀ := fun x =>
    MulAction.mem_stabilizer_iff
  have htr : ∀ {a b : Fin (m + 2)} (hab : a ≠ b), b ≠ 0 → ∀ c : K,
      SpecialLinearGroup.transvection hab c ∈ S := by
    intro a b hab hb c
    rw [hmem]
    show Matrix.transvection a b c *ᵥ e₀ = e₀
    rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
    simp [he₀, Pi.single_apply, hb]
  have hrow : ∀ {j : Fin (m + 2)} (hj : (0 : Fin (m + 2)) ≠ j) (c : K),
      SpecialLinearGroup.transvection hj c ∈ ⁅S, S⁆ := by
    intro j hj c
    obtain ⟨k, hk0, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt (0 : Fin (m + 2)) j (by omega)
    have h := SpecialLinearGroup.commutatorElement_transvection hk0.symm hkj hj (1 : K) c
    rw [one_mul] at h
    rw [← h]
    exact Subgroup.commutator_mem_commutator (htr hk0.symm hk0 1) (htr hkj (Ne.symm hj) c)
  have hlevi : ∀ A : SpecialLinearGroup (Fin (m + 1)) K,
      CFSG.CGT.T75N.epsHom m K A ∈ ⁅S, S⁆ := by
    intro A
    have hA : A ∈ ⁅(⊤ : Subgroup (SpecialLinearGroup (Fin (m + 1)) K)),
        (⊤ : Subgroup (SpecialLinearGroup (Fin (m + 1)) K))⁆ := by
      rw [← commutator_def (SpecialLinearGroup (Fin (m + 1)) K),
        CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le (by omega)]
      exact Subgroup.mem_top A
    have h1 : CFSG.CGT.T75N.epsHom m K A ∈
        (⁅(⊤ : Subgroup (SpecialLinearGroup (Fin (m + 1)) K)),
          (⊤ : Subgroup (SpecialLinearGroup (Fin (m + 1)) K))⁆).map
          (CFSG.CGT.T75N.epsHom m K) :=
      Subgroup.mem_map_of_mem _ hA
    rw [Subgroup.map_commutator] at h1
    have hle : (⊤ : Subgroup (SpecialLinearGroup (Fin (m + 1)) K)).map
        (CFSG.CGT.T75N.epsHom m K) ≤ S := by
      rintro _ ⟨B, -, rfl⟩
      rw [hmem]
      exact CFSG.CGT.T75N.epsHom_fix_e0 B
    exact Subgroup.commutator_mono hle hle h1
  have hrowHom : ∀ ρ : Fin (m + 1) → K, rowHom m K (Multiplicative.ofAdd ρ) ∈ ⁅S, S⁆ := by
    intro ρ
    have hT : Multiplicative.ofAdd ρ ∈ (⁅S, S⁆).comap (rowHom m K) := by
      rw [← Finset.univ_sum_single ρ, ofAdd_sum]
      exact Subgroup.prod_mem _ fun j _ => by
        show rowHom m K (Multiplicative.ofAdd (Pi.single j (ρ j))) ∈ ⁅S, S⁆
        rw [rowHom_single]
        exact hrow _ _
    exact hT
  have hg' : (g : Matrix (Fin (m + 2)) (Fin (m + 2)) K) *ᵥ e₀ = e₀ := (hmem g).mp hg
  have hcol : ∀ i, (g : Matrix (Fin (m + 2)) (Fin (m + 2)) K) i 0 = if i = 0 then 1 else 0 := by
    intro i
    have := congrFun hg' i
    simpa [he₀, Pi.single_apply] using this
  set Ag : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
    (g : Matrix (Fin (m + 2)) (Fin (m + 2)) K).submatrix Fin.succ Fin.succ with hAg
  have hdet : Ag.det = 1 := by
    have h1 := g.2
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ] at h1
    simpa [hcol, Fin.succAbove_zero] using h1
  set A : SpecialLinearGroup (Fin (m + 1)) K := ⟨Ag, hdet⟩ with hA
  set B : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
    ((A⁻¹ : SpecialLinearGroup (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) with hB
  have hAB : Ag * B = 1 := congrArg Subtype.val (mul_inv_cancel A)
  set r := g * CFSG.CGT.T75N.epsHom m K A⁻¹ with hr
  have hrmat : (r : Matrix (Fin (m + 2)) (Fin (m + 2)) K) =
      (g : Matrix (Fin (m + 2)) (Fin (m + 2)) K) * CFSG.CGT.T75N.epsMat B := rfl
  have hrrow : r = rowHom m K (Multiplicative.ofAdd fun j =>
      (r : Matrix (Fin (m + 2)) (Fin (m + 2)) K) 0 j.succ) := by
    apply Subtype.ext
    ext i j
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
    · show (r : Matrix (Fin (m + 2)) (Fin (m + 2)) K) 0 0 = 1
      rw [hrmat, CFSG.CGT.T75N.mul_epsMat_zero, hcol]
      simp
    · rfl
    · show (r : Matrix (Fin (m + 2)) (Fin (m + 2)) K) i'.succ 0 = 0
      rw [hrmat, CFSG.CGT.T75N.mul_epsMat_zero, hcol]
      simp [Fin.succ_ne_zero]
    · show (r : Matrix (Fin (m + 2)) (Fin (m + 2)) K) i'.succ j'.succ =
        (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i' j'
      rw [hrmat, CFSG.CGT.T75N.mul_epsMat_succ, ← hAB, Matrix.mul_apply]
      rfl
  have hgr : g = r * CFSG.CGT.T75N.epsHom m K A := by
    rw [hr, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  rw [hgr, hrrow]
  exact Subgroup.mul_mem _ (hrowHom _) (hlevi A)

theorem commutator_stabilizer_eq {n : ℕ} (hn : 4 ≤ n) {v : Fin n → K} (hv : v ≠ 0) :
    ⁅MulAction.stabilizer (SpecialLinearGroup (Fin n) K) v,
      MulAction.stabilizer (SpecialLinearGroup (Fin n) K) v⁆ =
      MulAction.stabilizer (SpecialLinearGroup (Fin n) K) v := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have he₀ : (Pi.single 0 1 : Fin (m + 2) → K) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  obtain ⟨g₀, hg₀⟩ := exists_specialLinearGroup_smul_eq (by omega) he₀ hv
  rw [← hg₀, MulAction.stabilizer_smul_eq_stabilizer_map_conj, ← Subgroup.map_commutator,
    commutator_stabilizer_single_zero (by omega)]

theorem index_stabilizer_eq [Finite K] {n : ℕ} (hn : 2 ≤ n) {v : Fin n → K} (hv : v ≠ 0) :
    (MulAction.stabilizer (SpecialLinearGroup (Fin n) K) v).index = Nat.card K ^ n - 1 := by
  classical
  rw [MulAction.index_stabilizer]
  have horb : MulAction.orbit (SpecialLinearGroup (Fin n) K) v = {(0 : Fin n → K)}ᶜ := by
    ext w
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨g, rfl⟩ h0
      apply hv
      have h1 := congrArg (fun x => g⁻¹ • x) h0
      simpa using h1
    · intro hw
      obtain ⟨g, hg⟩ := exists_specialLinearGroup_smul_eq hn hv hw
      exact ⟨g, hg⟩
  rw [horb, Set.ncard_compl, Set.ncard_singleton, Nat.card_fun, Nat.card_fin]

theorem index_comap_stabilizer_eq [Finite K] {H : Type*} [Group H] {n : ℕ} (hn : 2 ≤ n)
    {η : H →* SpecialLinearGroup (Fin n) K} (hη : Function.Surjective η) {v : Fin n → K}
    (hv : v ≠ 0) :
    ((MulAction.stabilizer (SpecialLinearGroup (Fin n) K) v).comap η).index =
      Nat.card K ^ n - 1 := by
  rw [Subgroup.index_comap_of_surjective _ hη, index_stabilizer_eq hn hv]

theorem comap_stabilizer_eq_commutator_sup_ker {H : Type*} [Group H] {n : ℕ} (hn : 4 ≤ n)
    {η : H →* SpecialLinearGroup (Fin n) K} (hη : Function.Surjective η) {v : Fin n → K}
    (hv : v ≠ 0) :
    (MulAction.stabilizer (SpecialLinearGroup (Fin n) K) v).comap η =
      ⁅(MulAction.stabilizer (SpecialLinearGroup (Fin n) K) v).comap η,
        (MulAction.stabilizer (SpecialLinearGroup (Fin n) K) v).comap η⁆ ⊔ η.ker := by
  set S := MulAction.stabilizer (SpecialLinearGroup (Fin n) K) v with hS
  have hmap : (S.comap η).map η = S := Subgroup.map_comap_eq_self_of_surjective hη S
  calc S.comap η = (⁅S, S⁆).comap η := by rw [commutator_stabilizer_eq hn hv]
    _ = (⁅(S.comap η).map η, (S.comap η).map η⁆).comap η := by rw [hmap]
    _ = ((⁅S.comap η, S.comap η⁆).map η).comap η := by rw [Subgroup.map_commutator]
    _ = ⁅S.comap η, S.comap η⁆ ⊔ η.ker := Subgroup.comap_map_eq _ _

section Natural

variable {H : Type*} [Group H] {X : Type*} [CommGroup X] {n : ℕ}
  {η : H →* SpecialLinearGroup (Fin n) K} {ρ : H →* MulAut X} {ψ : Additive X ≃+ (Fin n → K)}

theorem stabilizer_comap_eq_of_natural
    (hψ : ∀ h x, ψ (Additive.ofMul (ρ h x)) = η h • ψ (Additive.ofMul x)) (x : X) :
    (MulAction.stabilizer (MulAut X) x).comap ρ =
      (MulAction.stabilizer (SpecialLinearGroup (Fin n) K) (ψ (Additive.ofMul x))).comap η := by
  ext h
  simp only [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MulAut.smul_def]
  rw [← hψ, ψ.injective.eq_iff, Additive.ofMul.injective.eq_iff]

theorem index_stabilizer_of_natural [Finite K] (hn : 2 ≤ n) (hη : Function.Surjective η)
    (hψ : ∀ h x, ψ (Additive.ofMul (ρ h x)) = η h • ψ (Additive.ofMul x)) {x : X} (hx : x ≠ 1) :
    ((MulAction.stabilizer (MulAut X) x).comap ρ).index = Nat.card K ^ n - 1 := by
  rw [stabilizer_comap_eq_of_natural hψ x]
  refine index_comap_stabilizer_eq hn hη fun h0 => hx ?_
  have h1 : ψ (Additive.ofMul x) = ψ 0 := by rw [h0, map_zero]
  exact Additive.ofMul.injective (ψ.injective h1)

private theorem exists_mem_ker_eq_of_eq_sup {G' : Type*} [Group G'] {f : H →* G'} {P : Subgroup H}
    (hPeq : P = ⁅P, P⁆ ⊔ f.ker) {A : Type*} [CommGroup A] (θ : ↥P →* A) (p : ↥P) :
    ∃ k : ↥P, f k = 1 ∧ θ p = θ k := by
  have hp : (p : H) ∈ ⁅P, P⁆ ⊔ f.ker := by
    rw [← hPeq]
    exact p.2
  obtain ⟨c, hc, k, hk, hck⟩ := Subgroup.mem_sup_of_normal_right.mp hp
  have hmapc : ⁅P, P⁆ = (commutator ↥P).map P.subtype := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [hmapc] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  simp only [Subgroup.coe_subtype] at hck
  have hkP : k ∈ P := by
    have e : k = (c' : H)⁻¹ * p := by rw [← hck]; group
    rw [e]
    exact P.mul_mem (P.inv_mem c'.2) p.2
  refine ⟨⟨k, hkP⟩, hk, ?_⟩
  have hθc : θ c' = 1 := MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker θ hc')
  have e : p = c' * ⟨k, hkP⟩ := Subtype.ext hck.symm
  rw [e, map_mul, hθc, one_mul]

theorem exists_mem_ker_eq_of_natural {A : Type*} [CommGroup A] (hn : 4 ≤ n)
    (hη : Function.Surjective η)
    (hψ : ∀ h x, ψ (Additive.ofMul (ρ h x)) = η h • ψ (Additive.ofMul x)) {x : X} (hx : x ≠ 1)
    (θ : ↥((MulAction.stabilizer (MulAut X) x).comap ρ) →* A)
    (p : ↥((MulAction.stabilizer (MulAut X) x).comap ρ)) :
    ∃ k : ↥((MulAction.stabilizer (MulAut X) x).comap ρ), η k = 1 ∧ θ p = θ k := by
  have hv : ψ (Additive.ofMul x) ≠ 0 := fun h0 => hx (by
    have h1 : ψ (Additive.ofMul x) = ψ 0 := by rw [h0, map_zero]
    exact Additive.ofMul.injective (ψ.injective h1))
  refine exists_mem_ker_eq_of_eq_sup ?_ θ p
  rw [stabilizer_comap_eq_of_natural hψ x]
  exact comap_stabilizer_eq_commutator_sup_ker hn hη hv

end Natural

end CFSG.ClassicalGroups.SpecialLinear
