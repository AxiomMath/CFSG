module

public import CFSG.ClassicalInvolution.RouteD.MultiModelShortF4

public section

namespace CFSG.ClassicalInvolution.RouteD

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.RootSystem CFSG.LieType.Universal
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Matrices

variable {F : Type*} [Field F] (σ : F ≃+* F)

theorem comm_heis_01 (hσ : ∀ c, σ (σ c) = c) (a b a' b' : F) :
    heisenbergMatrix σ (0 : Fin 5) 2 a b * heisenbergMatrix σ 3 2 a' b' =
      rootMatrix σ 0 1 (-a * σ a') * heisenbergMatrix σ 3 2 a' b' *
        heisenbergMatrix σ 0 2 a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisenbergMatrix, rootMatrix, Matrix.mul_apply, Fin.sum_univ_five, Matrix.single_apply,
      Matrix.one_apply, Fin.rev, hσ]
  ring

theorem comm_heis_10 (hσ : ∀ c, σ (σ c) = c) (a b a' b' : F) :
    heisenbergMatrix σ (1 : Fin 5) 2 a b * heisenbergMatrix σ 4 2 a' b' =
      rootMatrix σ 1 0 (-a * σ a') * heisenbergMatrix σ 4 2 a' b' *
        heisenbergMatrix σ 1 2 a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisenbergMatrix, rootMatrix, Matrix.mul_apply, Fin.sum_univ_five, Matrix.single_apply,
      Matrix.one_apply, Fin.rev, hσ]
  ring

theorem comm_heis_03 (hσ : ∀ c, σ (σ c) = c) (a b a' b' : F) :
    heisenbergMatrix σ (0 : Fin 5) 2 a b * heisenbergMatrix σ 1 2 a' b' =
      rootMatrix σ 0 3 (-a * σ a') * heisenbergMatrix σ 1 2 a' b' *
        heisenbergMatrix σ 0 2 a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisenbergMatrix, rootMatrix, Matrix.mul_apply, Fin.sum_univ_five, Matrix.single_apply,
      Matrix.one_apply, Fin.rev, hσ]
  ring

theorem comm_heis_30 (hσ : ∀ c, σ (σ c) = c) (a b a' b' : F) :
    heisenbergMatrix σ (3 : Fin 5) 2 a b * heisenbergMatrix σ 4 2 a' b' =
      rootMatrix σ 3 0 (-a * σ a') * heisenbergMatrix σ 4 2 a' b' *
        heisenbergMatrix σ 3 2 a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisenbergMatrix, rootMatrix, Matrix.mul_apply, Fin.sum_univ_five, Matrix.single_apply,
      Matrix.one_apply, Fin.rev, hσ]
  ring

private theorem rootMatrix_eq_rootMatrix_rev (hσ : ∀ c, σ (σ c) = c) {n : ℕ} (i j : Fin n) (c : F) :
    rootMatrix σ i j c = rootMatrix σ (Fin.rev j) (Fin.rev i) (-σ c) := by
  rw [rootMatrix, rootMatrix, Fin.rev_rev, Fin.rev_rev, map_neg, hσ]
  simp only [← Matrix.single_neg]
  abel

theorem exists_heis_param (hσ : ∀ c, σ (σ c) = c) (h2 : (2 : F) ≠ 0) (a : F) :
    ∃ b, b + σ b + σ a * a = 0 := by
  refine ⟨-(σ a * a) / 2, ?_⟩
  have hs : σ (σ a * a) = σ a * a := by rw [map_mul, hσ, mul_comm]
  have h2' : σ 2 = 2 := map_ofNat σ 2
  rw [map_div₀, map_neg, hs, h2']
  field_simp
  ring

end Matrices

section Elements

variable {F : Type*} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)
include hσ

noncomputable def heisElt {n : ℕ} {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k)
    (hk : Fin.rev k = k) (a b : F) (hab : b + σ b + σ a * a = 0) : SU σ n :=
  ⟨⟨heisenbergMatrix σ i k a b, heisenbergMatrix σ i k (-a) (-b - a * σ a),
    by
      rw [heisenbergMatrix_mul σ hi hik hk, map_neg, add_neg_cancel,
        show b + (-b - a * σ a) - a * -σ a = 0 by ring, heisenbergMatrix_zero],
    by
      rw [heisenbergMatrix_mul σ hi hik hk, neg_add_cancel,
        show -b - a * σ a + b - -a * σ a = 0 by ring, heisenbergMatrix_zero]⟩,
    det_heisenbergMatrix σ hi hik hk a b, heisenbergMatrix_isometry σ hσ hi hik hk hab⟩

theorem heisElt_mem {n : ℕ} {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k)
    (a b : F) (hab : b + σ b + σ a * a = 0) :
    heisElt hσ hi hik hk a b hab ∈ heisenbergSubgroup σ hσ hi hik hk :=
  ⟨a, b, hab, rfl⟩

omit hσ in
theorem mem_of_matrix_comm {n : ℕ} {S : Subgroup (SU σ n)} {x y z : SU σ n} (hx : x ∈ S)
    (hy : y ∈ S)
    (h : ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ((y : GL (Fin n) F) : Matrix _ _ F) =
      ((z : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ((y : GL (Fin n) F) : Matrix _ _ F) *
        ((x : GL (Fin n) F) : Matrix _ _ F)) : z ∈ S := by
  have h' : x * y = z * y * x := Subtype.ext (Units.ext (by simpa [Units.val_mul] using h))
  have e : z = x * y * x⁻¹ * y⁻¹ := by
    calc z = (z * y * x) * x⁻¹ * y⁻¹ := by group
      _ = x * y * x⁻¹ * y⁻¹ := by rw [← h']
  rw [e]
  exact S.mul_mem (S.mul_mem (S.mul_mem hx hy) (S.inv_mem hx)) (S.inv_mem hy)

theorem rootHom_mem_of_comm {S : Subgroup (SU σ 5)} (h2 : (2 : F) ≠ 0) {i j : Fin 5}
    (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j) (c : F) {p q : Fin 5}
    (hp : p ≠ Fin.rev p) (hpk : p ≠ 2) (hq : q ≠ Fin.rev q) (hqk : q ≠ 2) (a a' : F)
    (hmat : ∀ b b' : F, heisenbergMatrix σ p 2 a b * heisenbergMatrix σ q 2 a' b' =
      rootMatrix σ i j c * heisenbergMatrix σ q 2 a' b' * heisenbergMatrix σ p 2 a b)
    (hSp : heisenbergSubgroup σ hσ hp hpk (by decide) ≤ S)
    (hSq : heisenbergSubgroup σ hσ hq hqk (by decide) ≤ S) :
    rootHom σ hσ hij hi hj (Multiplicative.ofAdd c) ∈ S := by
  obtain ⟨b, hb⟩ := exists_heis_param σ hσ h2 a
  obtain ⟨b', hb'⟩ := exists_heis_param σ hσ h2 a'
  exact mem_of_matrix_comm (hSp (heisElt_mem hσ hp hpk (by decide) a b hb))
    (hSq (heisElt_mem hσ hq hqk (by decide) a' b' hb')) (hmat b b')

theorem rootHom_mem_u5 {S : Subgroup (SU σ 5)} (h2 : (2 : F) ≠ 0)
    (hS : ∀ (i : Fin 5) (hi : i ≠ Fin.rev i) (hik : i ≠ 2),
      heisenbergSubgroup σ hσ hi hik (by decide) ≤ S)
    {i j : Fin 5} (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j) (hji : j ≠ Fin.rev i)
    (c : F) : rootHom σ hσ hij hi hj (Multiplicative.ofAdd c) ∈ S := by
  have hS' : ∀ (p : Fin 5) (hp : p ≠ Fin.rev p) (hpk : p ≠ 2),
      heisenbergSubgroup σ hσ hp hpk (by decide) ≤ S := hS
  have e01 : rootMatrix σ (3 : Fin 5) 4 = fun c => rootMatrix σ 0 1 (-σ c) :=
    funext fun c => rootMatrix_eq_rootMatrix_rev σ hσ 3 4 c
  have e43 : rootMatrix σ (4 : Fin 5) 3 = fun c => rootMatrix σ 1 0 (-σ c) :=
    funext fun c => rootMatrix_eq_rootMatrix_rev σ hσ 4 3 c
  have e14 : rootMatrix σ (1 : Fin 5) 4 = fun c => rootMatrix σ 0 3 (-σ c) :=
    funext fun c => rootMatrix_eq_rootMatrix_rev σ hσ 1 4 c
  have e41 : rootMatrix σ (4 : Fin 5) 1 = fun c => rootMatrix σ 3 0 (-σ c) :=
    funext fun c => rootMatrix_eq_rootMatrix_rev σ hσ 4 1 c
  have hi4 : i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 4 := by
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact absurd rfl hi
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  have hj4 : j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 := by
    fin_cases j
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact absurd rfl hj
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  rcases hi4 with rfl | rfl | rfl | rfl <;> rcases hj4 with rfl | rfl | rfl | rfl <;> first
    | exact absurd rfl hij
    | exact absurd rfl hi
    | exact absurd rfl hj
    | exact absurd rfl hji
    | exact rootHom_mem_of_comm hσ h2 hij hi hj c (p := 0) (q := 3) (by decide) (by decide)
        (by decide) (by decide) (-c) 1 (fun b b' => by
          have := comm_heis_01 σ hσ (-c) b 1 b'
          rwa [map_one, mul_one, neg_neg] at this) (hS' 0 (by decide) (by decide))
        (hS' 3 (by decide) (by decide))
    | exact rootHom_mem_of_comm hσ h2 hij hi hj c (p := 0) (q := 1) (by decide) (by decide)
        (by decide) (by decide) (-c) 1 (fun b b' => by
          have := comm_heis_03 σ hσ (-c) b 1 b'
          rwa [map_one, mul_one, neg_neg] at this) (hS' 0 (by decide) (by decide))
        (hS' 1 (by decide) (by decide))
    | exact rootHom_mem_of_comm hσ h2 hij hi hj c (p := 1) (q := 4) (by decide) (by decide)
        (by decide) (by decide) (-c) 1 (fun b b' => by
          have := comm_heis_10 σ hσ (-c) b 1 b'
          rwa [map_one, mul_one, neg_neg] at this) (hS' 1 (by decide) (by decide))
        (hS' 4 (by decide) (by decide))
    | exact rootHom_mem_of_comm hσ h2 hij hi hj c (p := 3) (q := 4) (by decide) (by decide)
        (by decide) (by decide) (-c) 1 (fun b b' => by
          have := comm_heis_30 σ hσ (-c) b 1 b'
          rwa [map_one, mul_one, neg_neg] at this) (hS' 3 (by decide) (by decide))
        (hS' 4 (by decide) (by decide))
    | exact rootHom_mem_of_comm hσ h2 hij hi hj c (p := 0) (q := 3) (by decide) (by decide)
        (by decide) (by decide) (σ c) 1 (fun b b' => by
          have := comm_heis_01 σ hσ (σ c) b 1 b'
          rw [map_one, mul_one] at this
          rw [e01]
          exact this) (hS' 0 (by decide) (by decide)) (hS' 3 (by decide) (by decide))
    | exact rootHom_mem_of_comm hσ h2 hij hi hj c (p := 0) (q := 1) (by decide) (by decide)
        (by decide) (by decide) (σ c) 1 (fun b b' => by
          have := comm_heis_03 σ hσ (σ c) b 1 b'
          rw [map_one, mul_one] at this
          rw [e14]
          exact this) (hS' 0 (by decide) (by decide)) (hS' 1 (by decide) (by decide))
    | exact rootHom_mem_of_comm hσ h2 hij hi hj c (p := 1) (q := 4) (by decide) (by decide)
        (by decide) (by decide) (σ c) 1 (fun b b' => by
          have := comm_heis_10 σ hσ (σ c) b 1 b'
          rw [map_one, mul_one] at this
          rw [e43]
          exact this) (hS' 1 (by decide) (by decide)) (hS' 4 (by decide) (by decide))
    | exact rootHom_mem_of_comm hσ h2 hij hi hj c (p := 3) (q := 4) (by decide) (by decide)
        (by decide) (by decide) (σ c) 1 (fun b b' => by
          have := comm_heis_30 σ hσ (σ c) b 1 b'
          rw [map_one, mul_one] at this
          rw [e41]
          exact this) (hS' 3 (by decide) (by decide)) (hS' 4 (by decide) (by decide))

end Elements

section Generation

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

omit [Finite F] in
theorem heisenberg_le_rootGroup' {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {n : ℕ} {i k : Fin n}
    (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k) {γ : Fin (n / 2) → ℤ}
    (hw : weight n i = toStd n γ) :
    heisenbergSubgroup σ hσ hi hik hk ≤ rootGroup σ hσ n γ := by
  unfold rootGroup
  refine le_trans ?_ le_sup_right
  exact le_iSup_of_le i (le_iSup_of_le k (le_iSup_of_le hi (le_iSup_of_le hik
    (le_iSup_of_le hk (le_iSup_of_le hw le_rfl)))))

omit [Finite F] in
theorem longRootHom_mem_heisenberg' {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {n : ℕ} {i k : Fin n}
    (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k) (c : Multiplicative (traceZero σ)) :
    longRootHom σ hi c ∈ heisenbergSubgroup σ hσ hi hik hk := by
  refine ⟨0, (c.toAdd : F), ?_, ?_⟩
  · rw [map_zero, zero_mul, add_zero]
    exact c.toAdd.2
  · rw [coe_longRootHom, longRootMatrix, heisenbergMatrix]
    simp

@[expose] def shortSetU5 : Set (Fin 2 → ℤ) := {![1, 1], ![-1, -1], ![0, 1], ![0, -1]}

theorem iSup_shortSetU5_eq_top (hF : Nat.card F = (p ^ f) ^ 2) (h2 : (2 : F) ≠ 0) :
    (⨆ γ ∈ shortSetU5, (rootDatum hF 5).rootGroup γ) = ⊤ := by
  have hσ := unitaryInvolution_involutive hF
  set T := ⨆ γ ∈ shortSetU5, (rootDatum hF 5).rootGroup γ with hT
  have hle : ∀ γ ∈ shortSetU5, rootGroup (unitaryInvolution F p f) hσ 5 γ ≤ T := fun γ hγ =>
    le_iSup₂_of_le γ hγ le_rfl
  have hheis : ∀ (i : Fin 5) (hi : i ≠ Fin.rev i) (hik : i ≠ 2),
      heisenbergSubgroup (unitaryInvolution F p f) hσ hi hik (by decide) ≤ T := by
    intro i hi hik
    fin_cases i
    · exact (heisenberg_le_rootGroup' hσ hi hik (by decide) (γ := ![1, 1]) (by decide)).trans
        (hle _ (by simp [shortSetU5]))
    · exact (heisenberg_le_rootGroup' hσ hi hik (by decide) (γ := ![0, 1]) (by decide)).trans
        (hle _ (by simp [shortSetU5]))
    · exact absurd rfl hi
    · exact (heisenberg_le_rootGroup' hσ hi hik (by decide) (γ := ![0, -1]) (by decide)).trans
        (hle _ (by simp [shortSetU5]))
    · exact (heisenberg_le_rootGroup' hσ hi hik (by decide) (γ := ![-1, -1]) (by decide)).trans
        (hle _ (by simp [shortSetU5]))
  obtain ⟨w, H, hct⟩ := exists_isCTGroupDatum hF 5 (by norm_num)
  refine eq_top_iff.mpr ?_
  rw [← hct.iSup_eq_top]
  refine iSup₂_le fun γ _ => ?_
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
      iSup_le fun hj => iSup_le fun hji => iSup_le fun _ => ?_
    rintro _ ⟨c, rfl⟩
    have := rootHom_mem_u5 (S := T) hσ h2 hheis hij hi hj hji c.toAdd
    rwa [ofAdd_toAdd] at this
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun _ => ?_
    rintro _ ⟨c, rfl⟩
    have hik : i ≠ 2 := fun h => hi (by rw [h]; rfl)
    exact hheis i hi hik (longRootHom_mem_heisenberg' hσ hi hik (by decide) c)
  · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
      iSup_le fun hk => iSup_le fun _ => ?_
    have hk2 : k = 2 := by
      fin_cases k <;> first | rfl | exact absurd hk (by decide)
    subst hk2
    exact hheis i hi hik

end Generation

section Criterion

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

@[expose] def bBC2 (θ δ : Fin 2 → ℤ) : ℤ :=
  4 * θ 0 * δ 0 - 2 * θ 0 * δ 1 - 2 * θ 1 * δ 0 + 2 * θ 1 * δ 1

theorem form_BC2_explicit {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : TauCeti.IsFiniteType A)
    (hAe : A = !![2, -1; -2, 2]) (θ δ : Fin 2 → ℤ) :
    form hA (toRat θ) (toRat δ) = symmetrizer hA 1 * ((bBC2 θ δ : ℤ) : ℚ) := by
  have r01 := symmetrizer_rel hA 0 1
  subst hAe
  simp at r01
  rw [form_eq_sum]
  simp only [form_single_right, Fin.sum_univ_two, toRat_apply, bBC2]
  simp
  rw [r01]
  ring

theorem form_BC2_eq_zero {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : TauCeti.IsFiniteType A)
    (hAe : A = !![2, -1; -2, 2]) {θ δ : Fin 2 → ℤ} (h : bBC2 θ δ = 0) :
    form hA (toRat θ) (toRat δ) = 0 := by
  rw [form_BC2_explicit hA hAe, h]
  simp

theorem lenSq_BC2 {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : TauCeti.IsFiniteType A)
    (hAe : A = !![2, -1; -2, 2]) (θ : Fin 2 → ℤ) :
    ModelFacts.lenSq hA θ = symmetrizer hA 1 * ((bBC2 θ θ : ℤ) : ℚ) :=
  form_BC2_explicit hA hAe θ θ

theorem bBC2_nu_a : bBC2 (2 • Pi.single (1 : Fin 2) 1) ![1, 1] = 0 := by decide

theorem bBC2_nu_b : bBC2 (2 • Pi.single (1 : Fin 2) 1) ![-1, -1] = 0 := by decide

theorem bBC2_nu_eps : bBC2 (2 • Pi.single (1 : Fin 2) 1) ![2, 2] = 0 := by decide

theorem bBC2_eps_c : bBC2 ![2, 2] ![0, 1] = 0 := by decide

theorem bBC2_eps_d : bBC2 ![2, 2] ![0, -1] = 0 := by decide

variable (hF : Nat.card F = (p ^ f) ^ 2)

theorem su5_short_data (h2 : (2 : F) ≠ 0) :
    ∃ (α : Fin (rootDatum hF 5).rank → ℤ) (Ψ : Set (Fin (rootDatum hF 5).rank → ℤ)),
      ModelFacts.IsLongestRoot (rootDatum hF 5) α ∧ (∀ γ ∈ Ψ, γ ∈ (rootDatum hF 5).roots) ∧
      (⨆ γ ∈ Ψ, (rootDatum hF 5).rootGroup γ) = ⊤ ∧
      ∀ γ ∈ Ψ, γ = α ∨ γ = -α ∨
        form (rootDatum hF 5).isFiniteType (toRat α) (toRat γ) = 0 ∨
        ∃ ε, ModelFacts.IsLongestRoot (rootDatum hF 5) ε ∧
          form (rootDatum hF 5).isFiniteType (toRat α) (toRat ε) = 0 ∧
          form (rootDatum hF 5).isFiniteType (toRat ε) (toRat γ) = 0 := by
  have hcart : (rootDatum hF 5).cartan = !![2, -1; -2, 2] := by
    show cartan 5 = _
    decide
  obtain ⟨hc, hd⟩ := ModelFacts.unitary_odd (n := 5) (by decide)
  have hlongν : ModelFacts.IsLongestRoot (rootDatum hF 5)
      (2 • Pi.single (⟨1, (by decide : 1 < 5 / 2)⟩ : Fin 2) 1 : Fin 2 → ℤ) := by
    unfold ModelFacts.IsLongestRoot
    show ModelFacts.IsLongest (isFiniteType_cartan 5) (divisible 5) _
    rw [hd]
    exact ModelFacts.isLongest_two_nsmul_single_BC (m := 2) (by norm_num) hc
      (isFiniteType_cartan 5) (k := ⟨1, (by decide : 1 < 2)⟩) rfl
  have hεroot : (![2, 2] : Fin 2 → ℤ) ∈ (rootDatum hF 5).roots := by
    show _ ∈ roots (isFiniteType_cartan 5) (divisible 5)
    rw [roots_eq]
    exact Or.inr (Or.inl ⟨0, by decide, by decide⟩)
  have hlongε : ModelFacts.IsLongestRoot (rootDatum hF 5) (![2, 2] : Fin 2 → ℤ) := by
    refine ⟨hεroot, fun ε' hε' => ?_⟩
    have h1 := hlongν.2 ε' hε'
    have e1 : ModelFacts.lenSq (rootDatum hF 5).isFiniteType (![2, 2] : Fin 2 → ℤ) =
        ModelFacts.lenSq (rootDatum hF 5).isFiniteType
          (2 • Pi.single (1 : Fin 2) 1 : Fin 2 → ℤ) := by
      refine (lenSq_BC2 _ hcart _).trans ?_
      refine Eq.trans ?_ (lenSq_BC2 _ hcart _).symm
      congr 2
    exact h1.trans_eq e1.symm
  refine ⟨2 • Pi.single (⟨1, (by decide : 1 < 5 / 2)⟩ : Fin 2) 1, shortSetU5, hlongν, ?_,
    iSup_shortSetU5_eq_top hF h2, ?_⟩
  · intro γ hγ
    show γ ∈ roots (isFiniteType_cartan 5) (divisible 5)
    rw [roots_eq]
    rcases hγ with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr ⟨by decide, 0, by decide, by decide⟩)
    · exact Or.inr (Or.inr ⟨by decide, 4, by decide, by decide⟩)
    · exact Or.inr (Or.inr ⟨by decide, 1, by decide, by decide⟩)
    · exact Or.inr (Or.inr ⟨by decide, 3, by decide, by decide⟩)
  · intro γ hγ
    rcases hγ with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl (form_BC2_eq_zero _ hcart bBC2_nu_a)))
    · exact Or.inr (Or.inr (Or.inl (form_BC2_eq_zero _ hcart bBC2_nu_b)))
    · exact Or.inr (Or.inr (Or.inr ⟨![2, 2], hlongε, form_BC2_eq_zero _ hcart bBC2_nu_eps,
        form_BC2_eq_zero _ hcart bBC2_eps_c⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨![2, 2], hlongε, form_BC2_eq_zero _ hcart bBC2_nu_eps,
        form_BC2_eq_zero _ hcart bBC2_eps_d⟩))

theorem commFamilyConnected_psu_five {e : ℕ} (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSU 5 p e) : CommFamilyConnected (ModelFund p .PSU 5 e) := by
  refine commFamilyConnected_modelFund_of_short hp2 trivial hadm (by decide) (by decide) ?_
  have hf : 1 ≤ e := hadm.2.1
  have h : modelUniv .PSU 5 p e Fact.out =
      ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField p (2 * e)) p e) 5,
        Unitary.rootDatum (card_galoisField_two_mul p e hf) 5⟩ :=
    ModelFacts.modelUniv_PSU hf
  generalize modelUniv .PSU 5 p e Fact.out = L at h ⊢
  subst h
  exact su5_short_data (card_galoisField_two_mul p e hf)
    (ModelFacts.two_ne_zero_galoisField (2 * e) hp2)

end Criterion

end CFSG.ClassicalInvolution.RouteD
