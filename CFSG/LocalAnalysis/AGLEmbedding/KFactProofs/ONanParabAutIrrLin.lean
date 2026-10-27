module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrNice
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrIso

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartOne.OutStructure
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem linearAutGroup_cyclic_mod_inn (hn : 1 ≤ n) :
    ∃ d ∈ linearAutGroup n K, ∀ x ∈ linearAutGroup n K,
      ∃ k : ℤ, d ^ k * x ∈ inn (projectiveSL n K) := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨ω, hω⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨A₀, hA₀⟩ := GeneralLinearGroup.det_surjective (n := Fin n) (R := K) ω
  refine ⟨conjAut n K A₀, conjAut_mem_linearAutGroup A₀, fun x hx => ?_⟩
  obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hx
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hω (GeneralLinearGroup.det A))
  refine ⟨-m, ?_⟩
  have hdet : GeneralLinearGroup.det (A₀ ^ (-m) * A) = 1 := by
    rw [map_mul, map_zpow, hA₀]
    have : ω ^ (-m) * GeneralLinearGroup.det A = 1 := by
      rw [← hm, ← _root_.zpow_add, neg_add_cancel, zpow_zero]
    exact this
  obtain ⟨g, hg⟩ : A₀ ^ (-m) * A ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →*
      GL (Fin n) K).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hdet
  rw [← map_zpow, ← map_mul, ← hg, conjAut_toGL]
  exact ⟨_, rfl⟩

theorem outPTwoGen_projectiveSL {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n) :
    OutPTwoGen (projectiveSL n K) p := by
  obtain ⟨hgenTop, -⟩ := automorphism_generation (K := K) hn
  obtain ⟨-, -, hDn, -, -, hE, -, hidx, -, -⟩ := standard_outer_quotients (n := n) (K := K)
  have : Finite (MulAut (projectiveSL n K)) := inferInstance
  have hDnorm : (linearAutGroup n K).Normal := by
    refine ⟨fun d hd γ => ?_⟩
    have hγ : γ ∈ standardAutGroup n K := hgenTop ▸ Subgroup.mem_top γ
    have hd' : d ∈ standardAutGroup n K := hgenTop ▸ Subgroup.mem_top d
    have := hDn.conj_mem ⟨d, hd'⟩ (mem_subgroupOf.mpr hd) ⟨γ, hγ⟩
    exact mem_subgroupOf.mp this
  have hidx' : (semilinearAutGroup n K).index ≤ 2 := by
    have h2 : (semilinearAutGroup n K).relIndex (standardAutGroup n K) ≤ 2 := hidx
    rwa [hgenTop, Subgroup.relIndex_top_right] at h2
  refine OutPTwoGen.of_tower (linearAutGroup n K) (semilinearAutGroup n K) ?_
    (linearAutGroup_cyclic_mod_inn (by omega)) hE ?_
  · intro e _
    exact Subgroup.normalizer_eq_top_iff.2 hDnorm ▸ Subgroup.mem_top e
  · rintro α ⟨k, hk⟩
    have hpodd : Odd (p ^ k) := (Nat.Prime.odd_of_ne_two hp hp2).pow
    exact mem_of_pow_mem_of_index_le_two _ hidx' hpodd (by rw [hk]; exact one_mem _)

theorem semilinearAutGroup_le_inn_of_card_two (hK : Nat.card K = 2) :
    semilinearAutGroup n K ≤ inn (projectiveSL n K) := by
  intro x hx
  obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.mp hx
  have hσ : σ = 1 := by
    obtain ⟨-, -, -, -, hcard, -⟩ := finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (le_refl 1) (show Nat.card K = 2 ^ 1 by simpa using hK)
    have := (Nat.card_eq_one_iff_unique.1 hcard).1
    exact Subsingleton.elim _ _
  have hdet : GeneralLinearGroup.det A = 1 := by
    classical
    have := Fintype.ofFinite K
    have hc : Fintype.card Kˣ = 1 := by
      rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
    have := Fintype.card_le_one_iff_subsingleton.1 hc.le
    exact Subsingleton.elim _ _
  obtain ⟨g, hg⟩ : A ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →*
      GL (Fin n) K).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hdet
  rw [hσ, map_one, mul_one, ← hg, conjAut_toGL]
  exact ⟨_, rfl⟩

theorem outPInner_projectiveSL_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = 2)
    (hn : 3 ≤ n) : OutPInner (projectiveSL n K) p := by
  obtain ⟨hgenTop, -⟩ := automorphism_generation (K := K) hn
  obtain ⟨-, -, -, -, -, -, -, hidx, -, -⟩ := standard_outer_quotients (n := n) (K := K)
  have hidx' : (semilinearAutGroup n K).index ≤ 2 := by
    have h2 : (semilinearAutGroup n K).relIndex (standardAutGroup n K) ≤ 2 := hidx
    rwa [hgenTop, Subgroup.relIndex_top_right] at h2
  intro P hP x hx
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hpodd : Odd (p ^ k) := (Nat.Prime.odd_of_ne_two hp hp2).pow
  have hxE : x ∈ semilinearAutGroup n K := mem_of_pow_mem_of_index_le_two _ hidx' hpodd (by
    have : x ^ p ^ k = 1 := congrArg Subtype.val hk
    rw [this]
    exact one_mem _)
  exact semilinearAutGroup_le_inn_of_card_two hK hxE

section Model

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

theorem exists_equiv_projectiveSL {Y : Type} [Group Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSL n 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ f ∧
      Nonempty (Y ≃* projectiveSL n K) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, ⟨(e.trans
    (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)⟩⟩

theorem outPTwoGen_psl {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSL n 2 f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    OutPTwoGen Y p := by
  have hn : 2 ≤ n := h.1.2.2.1
  rcases Nat.eq_or_lt_of_le hn with rfl | hn3
  · exact OutPTwoGen.of_outPNice (outPNice_PSL_two hp h)
  · obtain ⟨K, _, _, -, ⟨e⟩⟩ := exists_equiv_projectiveSL h
    exact OutPTwoGen.of_mulEquiv e.symm (outPTwoGen_projectiveSL hp hp2 hn3)

theorem outPInner_psl_two {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : StatedClassicalModel Y .PSL n 2 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    OutPInner Y p := by
  have hn : 2 ≤ n := h.1.2.2.1
  have hn2 : n ≠ 2 := fun h2 => h.1.2.2.2.1 (by rw [h2]; rfl)
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_equiv_projectiveSL h
  exact OutPInner.of_mulEquiv e.symm
    (outPInner_projectiveSL_two hp hp2 (by simpa using hK) (by omega))

end Model

section Torus

open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)

variable {K : Type} [Field K] {n : ℕ}

@[expose] def diagHom (n : ℕ) (K : Type) [Field K] : upperTriangular n K →* (Fin n → K) where
  toFun b i := ((b : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i i
  map_one' := by
    ext i
    simp
  map_mul' b c := by
    ext i
    have hb : ((b : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).IsUpperTriangular :=
      mem_upperTriangular_iff_isUpperTriangular.1 b.2
    have hc : ((c : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).IsUpperTriangular :=
      mem_upperTriangular_iff_isUpperTriangular.1 c.2
    simp only [Subgroup.coe_mul, Pi.mul_apply]
    exact mul_apply_self_of_isUpperTriangular hb hc i

theorem diagHom_apply (b : upperTriangular n K) (i : Fin n) :
    diagHom n K b i = ((b : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i i := rfl

theorem mem_unitriangular_iff_diagHom {b : upperTriangular n K} :
    (b : SpecialLinearGroup (Fin n) K) ∈ unitriangular n K ↔ diagHom n K b = 1 := by
  constructor
  · intro h
    ext i
    exact h.2 i
  · intro h
    exact ⟨b.2, fun i => congrFun h i⟩

theorem coe_inv_isUpperTriangular_gl {A : GL (Fin n) K}
    (hA : (A : Matrix (Fin n) (Fin n) K).IsUpperTriangular) :
    ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsUpperTriangular := by
  have h : (A : Matrix (Fin n) (Fin n) K) * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have := Units.invertible A
  rw [← Matrix.inv_eq_right_inv h]
  exact Matrix.blockTriangular_inv_of_blockTriangular hA

theorem slConjugation_mem_upperTriangular {A : GL (Fin n) K}
    (hA : (A : Matrix (Fin n) (Fin n) K).IsUpperTriangular) {h : SpecialLinearGroup (Fin n) K}
    (hh : h ∈ upperTriangular n K) : slConjugation n K A h ∈ upperTriangular n K := by
  have hh' := mem_upperTriangular_iff_isUpperTriangular.1 hh
  have hAi := coe_inv_isUpperTriangular_gl hA
  rw [mem_upperTriangular_iff_isUpperTriangular, slConjugation_matrix]
  exact (hA.mul hh').mul hAi

theorem slConjugation_diag {A : GL (Fin n) K}
    (hA : (A : Matrix (Fin n) (Fin n) K).IsUpperTriangular) {h : SpecialLinearGroup (Fin n) K}
    (hh : h ∈ upperTriangular n K) (i : Fin n) :
    ((slConjugation n K A h : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i i =
      (h : Matrix (Fin n) (Fin n) K) i i := by
  have hh' := mem_upperTriangular_iff_isUpperTriangular.1 hh
  have hAi := coe_inv_isUpperTriangular_gl hA
  have hone : (A : Matrix (Fin n) (Fin n) K) i i *
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i = 1 := by
    have h1 : (A : Matrix (Fin n) (Fin n) K) * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [← mul_apply_self_of_isUpperTriangular hA hAi, h1, one_apply_eq]
  rw [slConjugation_matrix, mul_apply_self_of_isUpperTriangular (hA.mul hh') hAi,
    mul_apply_self_of_isUpperTriangular hA hh']
  calc _ = (h : Matrix (Fin n) (Fin n) K) i i *
          ((A : Matrix (Fin n) (Fin n) K) i i *
            ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i) := by ring
    _ = _ := by rw [hone, mul_one]

theorem exists_diag_gl [Nonempty (Fin n)] (d : Kˣ) :
    ∃ A₀ : GL (Fin n) K, (A₀ : Matrix (Fin n) (Fin n) K).IsUpperTriangular ∧
      GeneralLinearGroup.det A₀ = d := by
  classical
  obtain ⟨i⟩ := ‹Nonempty (Fin n)›
  refine ⟨⟨diagonal fun j => if j = i then (d : K) else 1,
    diagonal fun j => if j = i then ((d⁻¹ : Kˣ) : K) else 1, ?_, ?_⟩, ?_, ?_⟩
  · simp only [diagonal_mul_diagonal, mul_ite, ite_mul, Units.mul_inv, one_mul, mul_one,
      diagonal_eq_one]
    funext j
    split_ifs <;> simp
  · simp only [diagonal_mul_diagonal, mul_ite, ite_mul, Units.inv_mul, one_mul, mul_one,
      diagonal_eq_one]
    funext j
    split_ifs <;> simp
  · intro a b hab
    exact diagonal_apply_ne _ (ne_of_gt hab)
  · apply Units.ext
    rw [GeneralLinearGroup.val_det_apply]
    simp [det_diagonal]

end Torus

section Normalizing

open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Finite K] [CharP K 2] in
theorem conjAut_mem_projUnitriangular {A : GL (Fin n) K}
    (hA : (A : Matrix (Fin n) (Fin n) K).IsUpperTriangular) {w : projectiveSL n K}
    (hw : w ∈ projUnitriangular n K) : conjAut n K A w ∈ projUnitriangular n K := by
  obtain ⟨u, hu, rfl⟩ := hw
  rw [conjAut_proj]
  refine ⟨slConjugation n K A u, ?_, rfl⟩
  have hub := unitriangular_le_upperTriangular n K hu
  refine ⟨slConjugation_mem_upperTriangular hA hub, fun i => ?_⟩
  rw [slConjugation_diag hA hub]
  exact hu.2 i

theorem isUpperTriangular_of_normalizes (hn : 1 ≤ n) {A : GL (Fin n) K}
    (hA : ∀ w : projectiveSL n K,
      w ∈ projUnitriangular n K ↔ conjAut n K A w ∈ projUnitriangular n K) :
    (A : Matrix (Fin n) (Fin n) K).IsUpperTriangular := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨A₀, hA₀t, hA₀d⟩ := exists_diag_gl (K := K) (n := n) (GeneralLinearGroup.det A)
  have hsdet : GeneralLinearGroup.det (A * A₀⁻¹) = 1 := by
    rw [map_mul, map_inv, hA₀d, mul_inv_cancel]
  obtain ⟨g, hg⟩ : A * A₀⁻¹ ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →*
      GL (Fin n) K).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hsdet
  have hAeq : A = SpecialLinearGroup.toGL g * A₀ := by
    rw [hg]
    group
  have hA₀i : ∀ w, w ∈ projUnitriangular n K ↔ conjAut n K A₀ w ∈ projUnitriangular n K := by
    intro w
    refine ⟨conjAut_mem_projUnitriangular hA₀t, fun hw => ?_⟩
    have := conjAut_mem_projUnitriangular (coe_inv_isUpperTriangular_gl hA₀t) hw
    rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at this
  have hgn : ∀ w, w ∈ projUnitriangular n K ↔
      MulAut.conj (proj n K g) w ∈ projUnitriangular n K := by
    intro w
    set w' := conjAut n K A₀⁻¹ w with hw'def
    have hw' : conjAut n K A₀ w' = w := by
      rw [hw'def, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    have h1 : conjAut n K A w' = MulAut.conj (proj n K g) w := by
      rw [hAeq, map_mul, MulAut.mul_apply, hw', conjAut_toGL]
    calc w ∈ projUnitriangular n K ↔ conjAut n K A₀ w' ∈ projUnitriangular n K := by rw [hw']
      _ ↔ w' ∈ projUnitriangular n K := (hA₀i w').symm
      _ ↔ conjAut n K A w' ∈ projUnitriangular n K := hA w'
      _ ↔ MulAut.conj (proj n K g) w ∈ projUnitriangular n K := by rw [h1]
  have hgmem : proj n K g ∈
      Subgroup.normalizer (projUnitriangular n K : Set (projectiveSL n K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    rw [hgn w]
    rfl
  rw [normalizer_projUnitriangular (n := n) (K := K) 2] at hgmem
  obtain ⟨b, hb, hbg⟩ := hgmem
  have hz : b⁻¹ * g ∈ scalars n K := by
    rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, hbg, inv_mul_cancel]
  have hgB : g ∈ upperTriangular n K := by
    have : g = b * (b⁻¹ * g) := by group
    rw [this]
    exact (upperTriangular n K).mul_mem hb (scalars_le_upperTriangular n K hz)
  rw [hAeq, Units.val_mul]
  exact (mem_upperTriangular_iff_isUpperTriangular.1 hgB).mul hA₀t

end Normalizing

section PowerMap

open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem exists_pow_two_of_ringEquiv (σ : K ≃+* K) : ∃ j : ℕ, ∀ x : K, σ x = x ^ 2 ^ j := by
  have := Fintype.ofFinite K
  obtain ⟨m, hp, hm⟩ := FiniteField.card K 2
  obtain ⟨σ₀, hσ₀, hord, hzp, -⟩ := finite_field_automorphism_fixed_field_cardinality
    Nat.prime_two m.pos (show Nat.card K = 2 ^ (m : ℕ) by rw [Nat.card_eq_fintype_card, hm])
  have hmem : σ ∈ Subgroup.zpowers σ₀ := hzp ▸ Subgroup.mem_top σ
  have hfin : Finite (K ≃+* K) := Finite.of_injective (fun f : K ≃+* K => (f : K → K))
    fun f g h => RingEquiv.ext (congrFun h)
  obtain ⟨j, hj⟩ := (mem_powers_iff_mem_zpowers (x := σ₀) (y := σ)).2 hmem
  refine ⟨j, ?_⟩
  have key : ∀ (j : ℕ) (x : K), (σ₀ ^ j) x = x ^ 2 ^ j := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [pow_succ, RingAut.mul_apply, hσ₀ x, ih, ← pow_mul, pow_succ, mul_comm]
  intro x
  rw [← hj]
  exact key j x

theorem lin_power_map (hn : 1 ≤ n) {α : MulAut (projectiveSL n K)}
    (hαE : α ∈ semilinearAutGroup n K)
    (hα : ∀ w, w ∈ projUnitriangular n K ↔ α w ∈ projUnitriangular n K) :
    ∃ k : ℕ, ∀ b ∈ Subgroup.normalizer (projUnitriangular n K : Set (projectiveSL n K)),
      α b * (b ^ k)⁻¹ ∈ projUnitriangular n K := by
  obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.mp hαE
  obtain ⟨j, hj⟩ := exists_pow_two_of_ringEquiv σ
  have hmap : ∀ (τ : K ≃+* K) (u : SpecialLinearGroup (Fin n) K),
      (u ∈ unitriangular n K → SpecialLinearGroup.map τ.toRingHom u ∈ unitriangular n K) ∧
      (u ∈ upperTriangular n K → SpecialLinearGroup.map τ.toRingHom u ∈ upperTriangular n K) := by
    intro τ u
    refine ⟨fun hu => ⟨fun i j hij => ?_, fun i => ?_⟩, fun hu i j hij => ?_⟩
    · simp [hu.1 i j hij]
    · simp [hu.2 i]
    · simp [hu i j hij]
  have hσ : ∀ τ : K ≃+* K, ∀ w, w ∈ projUnitriangular n K →
      fieldAut n K τ w ∈ projUnitriangular n K := by
    rintro τ _ ⟨u, hu, rfl⟩
    rw [fieldAut_proj]
    exact ⟨_, (hmap τ u).1 hu, rfl⟩
  have hσi : ∀ τ : K ≃+* K, ∀ w, w ∈ projUnitriangular n K ↔
      fieldAut n K τ w ∈ projUnitriangular n K := by
    intro τ w
    refine ⟨hσ τ w, fun hw => ?_⟩
    have := hσ τ⁻¹ _ hw
    rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at this
  have hcA : ∀ w, w ∈ projUnitriangular n K ↔ conjAut n K A w ∈ projUnitriangular n K := by
    intro w
    have e : fieldAut n K σ (fieldAut n K σ⁻¹ w) = w := by simp
    have hw' : (conjAut n K A * fieldAut n K σ) (fieldAut n K σ⁻¹ w) = conjAut n K A w := by
      change conjAut n K A (fieldAut n K σ (fieldAut n K σ⁻¹ w)) = _
      rw [e]
    have h1 := hα (fieldAut n K σ⁻¹ w)
    rw [hw'] at h1
    exact (hσi σ⁻¹ w).trans h1
  have hA := isUpperTriangular_of_normalizes hn hcA
  refine ⟨2 ^ j, fun b hb => ?_⟩
  rw [normalizer_projUnitriangular (n := n) (K := K) 2] at hb
  obtain ⟨β, hβ, rfl⟩ := hb
  have hσβ := (hmap σ β).2 hβ
  set y := slConjugation n K A (SpecialLinearGroup.map σ.toRingHom β) with hy
  have hyU : y ∈ upperTriangular n K := slConjugation_mem_upperTriangular hA hσβ
  have hα' : (conjAut n K A * fieldAut n K σ) (proj n K β) = proj n K y := by
    rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj]
  set Z : upperTriangular n K := (⟨β, hβ⟩ : upperTriangular n K) ^ 2 ^ j with hZ
  have hdiag : diagHom n K ⟨y, hyU⟩ = diagHom n K Z := by
    ext i
    rw [diagHom_apply, hZ, map_pow, Pi.pow_apply, diagHom_apply]
    change ((y : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i i = _
    rw [hy, slConjugation_diag hA hσβ i]
    simp [hj]
  have hx : ((⟨y, hyU⟩ * Z⁻¹ : upperTriangular n K) : SpecialLinearGroup (Fin n) K) ∈
      unitriangular n K := by
    rw [mem_unitriangular_iff_diagHom, map_mul, hdiag, ← map_mul, mul_inv_cancel, map_one]
  rw [hα']
  refine ⟨_, hx, ?_⟩
  have hxe : ((⟨y, hyU⟩ * Z⁻¹ : upperTriangular n K) : SpecialLinearGroup (Fin n) K) =
      y * (β ^ 2 ^ j)⁻¹ := by
    simp [hZ]
  rw [hxe, map_mul, map_inv, map_pow]

end PowerMap

section Two

open CFSG.RankThree.PartOne.KCRootAxis (SL₂ slFieldAut exists_conj_mul_slFieldAut)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem proj_two_injective : Function.Injective (proj 2 K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h : g ∈ scalars 2 K := by
    rw [← ker_proj]
    exact hg
  rw [scalars_eq_center, CFSG.RankThree.PartOne.KCRootAxis.sl2_center_eq_bot] at h
  exact h

theorem mem_semilinearAutGroup_two (α : MulAut (projectiveSL 2 K)) :
    α ∈ semilinearAutGroup 2 K := by
  set e₂ : SL₂ K ≃* projectiveSL 2 K :=
    MulEquiv.ofBijective (proj 2 K) ⟨proj_two_injective, proj_surjective 2 K⟩ with he₂
  obtain ⟨M, σ, hφ⟩ := exists_conj_mul_slFieldAut (K := K) (MulAut.congr e₂.symm α)
  rw [mem_semilinearAutGroup_iff]
  refine ⟨SpecialLinearGroup.toGL M, σ, ?_⟩
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective 2 K x
  have h1 : α (proj 2 K g) = proj 2 K (M * SpecialLinearGroup.map σ.toRingHom g * M⁻¹) := by
    have h2 : e₂.symm (α (e₂ g)) = (MulAut.conj M * slFieldAut K σ : MulAut (SL₂ K)) g := by
      rw [← hφ]
      rfl
    have h4 : α (proj 2 K g) = e₂ ((MulAut.conj M * slFieldAut K σ : MulAut (SL₂ K)) g) := by
      rw [← h2, MulEquiv.apply_symm_apply]
      rfl
    rw [h4]
    rfl
  rw [h1, MulAut.mul_apply, fieldAut_proj, conjAut_toGL, MulAut.conj_apply, map_mul, map_mul,
    map_inv]

end Two

section R2Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem autScalarTorus_projectiveSL_of_mem (hn : 1 ≤ n)
    (hE : ∀ α : MulAut (projectiveSL n K),
      (∃ e : ℕ, 0 < e ∧ Nat.Coprime e 6 ∧ α ^ e ∈ inn (projectiveSL n K)) →
        α ∈ semilinearAutGroup n K) :
    AutScalarTorus (projectiveSL n K) := by
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := K) 2 (n := n) hn
  let S₁ : Sylow 2 (projectiveSL n K) := Sylow.mapSurjective (proj_surjective n K) P
  have hS₁ : (S₁ : Subgroup (projectiveSL n K)) = projUnitriangular n K := by
    rw [show (S₁ : Subgroup (projectiveSL n K)) = (P : Subgroup _).map (proj n K) from rfl, hP]
    rfl
  refine AutScalarTorus.of_sylow S₁ fun α hα hinn => ?_
  have hαE := hE α hinn
  have hiff := forall_iff_of_map_eq hα
  rw [hS₁] at hiff
  obtain ⟨k, hk⟩ := lin_power_map hn hαE hiff
  refine ⟨k, fun b hb => ?_⟩
  rw [hS₁] at hb ⊢
  exact hk b hb

variable (K) in
theorem autScalarTorus_projectiveSL (hn : 3 ≤ n) : AutScalarTorus (projectiveSL n K) := by
  obtain ⟨hgenTop, -⟩ := automorphism_generation (K := K) hn
  obtain ⟨hID, -, -, -, -, -, -, hidx, -, -⟩ := standard_outer_quotients (n := n) (K := K)
  have hidx' : (semilinearAutGroup n K).index ≤ 2 := by
    have h2 : (semilinearAutGroup n K).relIndex (standardAutGroup n K) ≤ 2 := hidx
    rwa [hgenTop, Subgroup.relIndex_top_right] at h2
  refine autScalarTorus_projectiveSL_of_mem (by omega) fun α ⟨e, he, he6, heinn⟩ => ?_
  have hodd : Odd e :=
    Nat.Coprime.odd_of_right (Nat.Coprime.coprime_dvd_right (by norm_num) he6)
  exact mem_of_pow_mem_of_index_le_two _ hidx' hodd
    (linearAutGroup_le_semilinearAutGroup (hID heinn))

variable (K) in
theorem autScalarTorus_projectiveSL_two : AutScalarTorus (projectiveSL 2 K) :=
  autScalarTorus_projectiveSL_of_mem (by omega) fun α _ => mem_semilinearAutGroup_two α

end R2Main

section ModelR2

open CFSG.Assembly.LowTwoRank

theorem autScalarTorus_psl {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSL n 2 f) : AutScalarTorus Y := by
  have hn : 2 ≤ n := h.1.2.2.1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_equiv_projectiveSL h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hK)
  refine AutScalarTorus.of_mulEquiv e.symm ?_
  rcases Nat.eq_or_lt_of_le hn with rfl | hn3
  · exact autScalarTorus_projectiveSL_two K
  · exact autScalarTorus_projectiveSL K hn3

end ModelR2

end CFSG.AGLEmbedding.ParabAutIrr
