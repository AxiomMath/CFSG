module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.NonsplitGen
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.DiagField
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartOne.KC.UnitaryRigidityNonsplit
public import CFSG.RankThree.PartOne.KC.UnitaryRigidityOne

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCUnitaryExact
  CFSG.RankThree.PartOne.KCUnitaryLines CFSG.RankThree.PartOne.KCUnitaryNonsplit
  CFSG.RankThree.PartOne.KCUnitaryOne CFSG.RankThree.PartOne.KCUnitaryFrame
  CFSG.RankThree.PartOne.KCUnitaryBlock CFSG.RankThree.PartOne.KCUnitaryScalar
  CFSG.RankThree.PartOne.KCUnitaryPair
  CFSG.HardMathSupport.Timmesfeld.Balance

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

variable (h) in
@[expose] noncomputable def gBlock (x : primeFormUnitary h (idGram K n)) (a : K[X]) :
    Subgroup (primeFormUnitary h (idGram K n)) :=
  (specialBlock (idForm h n) (toLinU h n x) a).comap (toLinU h n)

theorem mem_gBlock {x Y : primeFormUnitary h (idGram K n)} {a : K[X]} :
    Y ∈ gBlock h x a ↔ toLinU h n Y ∈ specialBlock (idForm h n) (toLinU h n x) a := Iff.rfl

theorem centralizer_eq_comap_unitaryCentralizer' (x : primeFormUnitary h (idGram K n)) :
    Subgroup.centralizer ({x} : Set (primeFormUnitary h (idGram K n))) =
      (unitaryCentralizer (idForm h n) (toLinU h n x)).comap (toLinU h n) := by
  ext A
  rw [Subgroup.mem_comap, mem_unitaryCentralizer]
  refine ⟨fun hA => ⟨toLinU_mem A, ?_⟩, fun hA => ?_⟩
  · have hA' := Subgroup.mem_centralizer_singleton_iff.mp hA
    have := congrArg (toLinU h n) hA'
    rw [map_mul, map_mul] at this
    have h2 := congrArg (fun g : LinearMap.GeneralLinearGroup K (Fin n → K) =>
      (g : Module.End K (Fin n → K))) this
    exact h2
  · have h1 : toLinU h n (A * x) = toLinU h n (x * A) := by
      rw [map_mul, map_mul]
      apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      exact hA.2.eq
    exact Subgroup.mem_centralizer_singleton_iff.mpr (toLinU_injective h1)

theorem mem_centralizer_iff_toLinU' (x A : primeFormUnitary h (idGram K n)) :
    A ∈ Subgroup.centralizer ({x} : Set (primeFormUnitary h (idGram K n))) ↔
      toLinU h n A ∈ unitaryCentralizer (idForm h n) (toLinU h n x) := by
  rw [centralizer_eq_comap_unitaryCentralizer']
  rfl

theorem gBlock_le_centralizer (x : primeFormUnitary h (idGram K n)) (a : K[X]) :
    gBlock h x a ≤ Subgroup.centralizer ({x} : Set _) := fun A hA =>
  (mem_centralizer_iff_toLinU' x A).mpr (specialBlock_le_unitaryCentralizer hA)

theorem specialBlock_le_range' (x : primeFormUnitary h (idGram K n)) (a : K[X]) :
    specialBlock (idForm h n) (toLinU h n x) a ≤ (toLinU h n).range := by
  rw [range_toLinU]
  exact specialBlock_le_unitaryCentralizer.trans (fun g hg => hg.1)

theorem map_toLinU_gBlock (x : primeFormUnitary h (idGram K n)) (a : K[X]) :
    (gBlock h x a).map (toLinU h n) = specialBlock (idForm h n) (toLinU h n x) a := by
  unfold gBlock
  rw [Subgroup.map_comap_eq]
  exact inf_of_le_right (specialBlock_le_range' x a)


section Data

theorem toLinU_coe_eq_toLin' (x : primeFormUnitary h (idGram K n)) :
    ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) =
      Matrix.toLin' (((x : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) := rfl

theorem squarefree_minpoly_of_pow_eq_scalar (hp : p.Prime) (hpℓ : p ≠ ℓ)
    {x : primeFormUnitary h (idGram K n)} {c : Kˣ}
    (hx : (x : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) c) :
    Squarefree (minpoly K ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K))) := by
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hp0 : (p : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K ℓ p).mp h0
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq h.prime hp).mp this).symm
  have hsep : (X ^ p - C (c : K)).Separable :=
    Polynomial.separable_X_pow_sub_C (c : K) hp0 c.ne_zero
  refine squarefree_minpoly_of_aeval_eq_zero (p := X ^ p - C (c : K)) hsep.squarefree ?_
  exact aeval_X_pow_sub_C_eq_zero hx

theorem primaryData_of_pow_eq_scalar (hp : p.Prime) (hpℓ : p ≠ ℓ)
    {x : primeFormUnitary h (idGram K n)} {c : Kˣ}
    (hx : (x : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) c) :
    UnitaryPrimaryData h.bar (idForm h n) (toLinU h n x) :=
  ⟨h.bar_bar, idForm_isSymm h n, idForm_separatingLeft h n, toLinU_mem x,
    squarefree_minpoly_of_pow_eq_scalar hp hpℓ hx⟩

theorem torusUnitary_mem_gBlock (x : primeFormUnitary h (idGram K n))
    (H : UnitaryPrimaryData h.bar (idForm h n) (toLinU h n x)) {μ : K}
    (hμ : h.bar μ * μ = 1)
    (ha : (X - C μ : K[X]) ∈ primaryFactors ((toLinU h n x :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)))
    {b₁ b₂ : Fin n → K} (hb : IsONPair h b₁ b₂)
    (hx₁ : ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) b₁ = μ • b₁)
    (hx₂ : ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) b₂ = μ • b₂) (c : Kˣ) (hc : h.norm (c : K) = 1) :
    torusUnitary h hb c hc ∈ gBlock h x (X - C μ) := by
  set T := torusUnitary h hb c hc with hT
  have hTmat : (((T : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = torusMat h b₁ b₂ c := rfl
  have hgapply : ∀ v, ((toLinU h n T : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) v = torusMat h b₁ b₂ c *ᵥ v := fun v => by
    rw [toLinU_apply_eq, hTmat]
  have hxiso := toLinU_mem x
  refine mem_specialBlock_of_degree_one H hμ ha (toLinU_mem T) ?_ ?_ ?_
  · show (_ : Module.End K (Fin n → K)) * _ = _ * _
    refine LinearMap.ext fun v => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hgapply, hgapply, torusMat_mulVec,
      torusMat_mulVec, map_add, map_add, map_smul, map_smul, hx₁, hx₂,
      idForm_apply_of_eigen h hxiso hμ hx₁, idForm_apply_of_eigen h hxiso hμ hx₂]
    module
  · intro v hv
    have h1 : idForm h n b₁ v = 0 := hv b₁ (by simp [mem_primaryComponent, hx₁])
    have h2 : idForm h n b₂ v = 0 := hv b₂ (by simp [mem_primaryComponent, hx₂])
    rw [hgapply, torusMat_mulVec, h1, h2]
    simp
  · have : ((toLinU h n T : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) = Matrix.toLin' (torusMat h b₁ b₂ c) :=
      LinearMap.ext fun v => by rw [hgapply, Matrix.toLin'_apply]
    rw [this, LinearMap.det_toLin']
    exact det_torusMat h hb c.ne_zero

end Data


section Component

@[expose] def suSub (h : UnitaryFieldData ℓ f K) (n : ℕ) :
    Subgroup (primeFormUnitary h (idGram K n)) :=
  (gramSU h (idGram K n)).subgroupOf (primeFormUnitary h (idGram K n))

theorem mem_suSub {A : primeFormUnitary h (idGram K n)} :
    A ∈ suSub h n ↔ ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
  unfold suSub
  rw [Subgroup.mem_subgroupOf, mem_gramSU_iff_unitary h]
  exact ⟨fun h' => h'.2, fun h' => ⟨A.2, h'⟩⟩

theorem gBlock_le_suSub (hq2 : 2 ≤ ℓ ^ f) {x : primeFormUnitary h (idGram K n)}
    (H0 : UnitaryPrimaryData h.bar (idForm h n) (toLinU h n x))
    (a : primaryFactors ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K))) (ha : IsGoodBlock h (toLinU h n x) a) :
    gBlock h x (a : K[X]) ≤ suSub h n := by
  intro A hA
  have h1 := specialBlock_le_sesqSpecialUnitaryGroup_of_good H0 hq2 a ha hA
  have h2 := (toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K n) (A : GL (Fin n) K)).mp h1
  rw [mem_suSub]
  exact ((mem_gramSU_iff_unitary h).mp h2).2

theorem isQuasisimple_gBlock (hq2 : 2 ≤ ℓ ^ f) {x : primeFormUnitary h (idGram K n)}
    (H0 : UnitaryPrimaryData h.bar (idForm h n) (toLinU h n x))
    (a : primaryFactors ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K))) (ha : IsGoodBlock h (toLinU h n x) a) :
    CFSG.IsQuasisimple (gBlock h x (a : K[X])) := by
  have hQ := (specialBlockFacts_of_good H0 hq2 a ha).quasisimple ha.1
  have hinj := (toLinU_injective (h := h) (n := n))
  let e := (gBlock h x (a : K[X])).equivMapOfInjective (toLinU h n) hinj
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (e.trans (MulEquiv.subgroupCongr (map_toLinU_gBlock x _))).symm hQ

theorem isQuasisimple_map_gBlock (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hq2 : 2 ≤ ℓ ^ f)
    {x : primeFormUnitary h (idGram K n)}
    (H0 : UnitaryPrimaryData h.bar (idForm h n) (toLinU h n x))
    (a : primaryFactors ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K))) (ha : IsGoodBlock h (toLinU h n x) a) :
    CFSG.IsQuasisimple ((gBlock h x (a : K[X])).map (primeFormConjHom h (idGram K n))) := by
  have hQ := isQuasisimple_gBlock hq2 H0 a ha
  let φ : gBlock h x (a : K[X]) →* MulAut (primeFormP h (idGram K n)) :=
    (primeFormConjHom h (idGram K n)).comp (gBlock h x (a : K[X])).subtype
  have hker : φ.ker ≤ Subgroup.center (gBlock h x (a : K[X])) := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro g'
    apply Subtype.ext
    exact (commute_of_mem_ker_of_ne hn hne (z := (g : primeFormUnitary h (idGram K n))) hg
      (g' : primeFormUnitary h (idGram K n))).eq.symm
  have := isQuasisimple_range hQ φ hker
  have hrange : φ.range = (gBlock h x (a : K[X])).map (primeFormConjHom h (idGram K n)) := by
    ext y
    constructor
    · rintro ⟨Y, rfl⟩
      exact ⟨Y, Y.2, rfl⟩
    · rintro ⟨Y, hY, rfl⟩
      exact ⟨⟨Y, hY⟩, rfl⟩
  rw [hrange] at this
  exact this


theorem idActU'_mem_suSub (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (α : MulAut (primeFormP h (idGram K n))) {w : primeFormUnitary h (idGram K n)}
    (hw : w ∈ suSub h n) : idActU' h n hn hne α w ∈ suSub h n := by
  rw [mem_suSub] at hw ⊢
  rw [coe_idActU' hn hne]
  exact det_idAct' hn hne α hw

theorem idActU'_commute_of_commute (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    {α : MulAut (primeFormP h (idGram K n))} {x w : primeFormUnitary h (idGram K n)}
    (hα : α * primeFormConjHom h (idGram K n) x * α⁻¹ = primeFormConjHom h (idGram K n) x)
    (hw : w * x = x * w) :
    idActU' h n hn hne α w * x = x * idActU' h n hn hne α w := by
  set y := idActU' h n hn hne α x with hy
  have hρ : primeFormConjHom h (idGram K n) y = primeFormConjHom h (idGram K n) x := by
    rw [hy, ← conj_primeFormConjHom' hn hne α, hα]
  set z := x⁻¹ * y with hz
  have hz1 : primeFormConjHom h (idGram K n) z = 1 := by
    rw [hz, map_mul, map_inv, hρ, inv_mul_cancel]
  have hzc : ∀ g, Commute z g := fun g => commute_of_mem_ker_of_ne hn hne hz1 g
  have hyx : y = x * z := by rw [hz, mul_inv_cancel_left]
  have h1 : idActU' h n hn hne α w * y = y * idActU' h n hn hne α w := by
    rw [hy, ← map_mul, ← map_mul, hw]
  rw [hyx] at h1
  have h2 : idActU' h n hn hne α w * x * z = x * idActU' h n hn hne α w * z := by
    calc idActU' h n hn hne α w * x * z = idActU' h n hn hne α w * (x * z) := by rw [mul_assoc]
      _ = x * z * idActU' h n hn hne α w := h1
      _ = x * (z * idActU' h n hn hne α w) := by rw [mul_assoc]
      _ = x * (idActU' h n hn hne α w * z) := by rw [(hzc _).eq]
      _ = x * idActU' h n hn hne α w * z := by rw [mul_assoc]
  exact mul_right_cancel h2

theorem isComponent_map_gBlock (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hq2 : 2 ≤ ℓ ^ f)
    {x : primeFormUnitary h (idGram K n)}
    (H0 : UnitaryPrimaryData h.bar (idForm h n) (toLinU h n x))
    (a : primaryFactors ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K))) (ha : IsGoodBlock h (toLinU h n x) a)
    {H : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hH : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ H) :
    CFSG.IsComponent (((gBlock h x (a : K[X])).map (primeFormConjHom h (idGram K n))).subgroupOf
      (H ⊓ Subgroup.centralizer ({primeFormConjHom h (idGram K n) x} : Set _))) := by
  set ρ := primeFormConjHom h (idGram K n) with hρ
  set J := (gBlock h x (a : K[X])).map ρ with hJ
  set N := (Subgroup.centralizer ({x} : Set (primeFormUnitary h (idGram K n))) ⊓
    suSub h n).map ρ with hN
  have hJN : J ≤ N := Subgroup.map_mono (le_inf (gBlock_le_centralizer x _)
    (gBlock_le_suSub hq2 H0 a ha))
  have hNH : N ≤ H := by
    rintro _ ⟨w, hw, rfl⟩
    refine hH ?_
    rw [← map_gramSU_eq_range_conj]
    exact ⟨w, hw.2, rfl⟩
  have hNC : N ≤ H ⊓ Subgroup.centralizer ({ρ x} : Set _) := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨hNH ⟨w, hw, rfl⟩, ?_⟩
    show ρ w ∈ Subgroup.centralizer ({ρ x} : Set _)
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hw).1]
  have hJC : J ≤ H ⊓ Subgroup.centralizer ({ρ x} : Set _) := hJN.trans hNC
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJC).symm
    (isQuasisimple_map_gBlock hn hne hq2 H0 a ha), ?_⟩
  refine isSubnormal_subgroupOf_of_normalizes hJN hNC ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩ _ ⟨Y, hY, rfl⟩
    refine ⟨w * Y * w⁻¹, ?_, by simp [map_mul, map_inv]⟩
    show w * Y * w⁻¹ ∈ gBlock h x (a : K[X])
    rw [mem_gBlock, map_mul, map_mul, map_inv]
    exact conj_mem_specialBlock ((mem_centralizer_iff_toLinU' x w).mp (Subgroup.mem_inf.mp hw).1) hY
  · rintro c hc _ ⟨w, hw, rfl⟩
    have hw' := Subgroup.mem_inf.mp hw
    have hcx : c * ρ x * c⁻¹ = ρ x := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hc.2
      rw [this, mul_assoc, mul_inv_cancel, mul_one]
    rw [conj_primeFormConjHom' hn hne]
    refine ⟨idActU' h n hn hne c w,
      Subgroup.mem_inf.mpr ⟨?_, idActU'_mem_suSub hn hne c hw'.2⟩, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (idActU'_commute_of_commute hn hne hcx (Subgroup.mem_centralizer_singleton_iff.mp hw'.1))


theorem map_gBlock_le (hq2 : 2 ≤ ℓ ^ f) {x : primeFormUnitary h (idGram K n)}
    (H0 : UnitaryPrimaryData h.bar (idForm h n) (toLinU h n x))
    (a : primaryFactors ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K))) (ha : IsGoodBlock h (toLinU h n x) a)
    {H : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hH : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ H) :
    (gBlock h x (a : K[X])).map (primeFormConjHom h (idGram K n)) ≤
      H ⊓ Subgroup.centralizer ({primeFormConjHom h (idGram K n) x} : Set _) := by
  rintro _ ⟨Y, hY, rfl⟩
  refine ⟨hH ?_, ?_⟩
  · rw [← map_gramSU_eq_range_conj]
    exact ⟨Y, gBlock_le_suSub hq2 H0 a ha hY, rfl⟩
  · show primeFormConjHom h (idGram K n) Y ∈ Subgroup.centralizer _
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (gBlock_le_centralizer x _ hY)]

theorem commute_of_mem_localDeltaIn_gBlock (hp : p.Prime) (hn : 3 ≤ n)
    (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hq2 : 2 ≤ ℓ ^ f) {x : primeFormUnitary h (idGram K n)}
    (H0 : UnitaryPrimaryData h.bar (idForm h n) (toLinU h n x))
    (a : primaryFactors ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K))) (ha : IsGoodBlock h (toLinU h n x) a)
    {E H : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hH : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ H)
    {g : MulAut (primeFormP h (idGram K n))} (hg : g ∈ localDeltaIn p H E)
    (hxE : primeFormConjHom h (idGram K n) x ∈ E) (hx1 : primeFormConjHom h (idGram K n) x ≠ 1)
    (hJp : p ∣ Nat.card ((gBlock h x (a : K[X])).map (primeFormConjHom h (idGram K n)))) :
    ∀ Y ∈ gBlock h x (a : K[X]),
      g * primeFormConjHom h (idGram K n) Y = primeFormConjHom h (idGram K n) Y * g := by
  have := h.finite
  have : Finite (primeFormP h (idGram K n)) := finite_primeFormP
  have hcore := le_core_of_mem_localDeltaIn hg hxE hx1
  intro Y hY
  exact commute_of_mem_gLAPPrimeCoreOf_of_isComponent hp (map_gBlock_le hq2 H0 a ha hH)
    (isComponent_map_gBlock hn hne hq2 H0 a ha hH)
    (by rwa [Nat.Prime.coprime_iff_not_dvd hp, not_not]) hcore _ (Subgroup.mem_map_of_mem _ hY)

end Component

section Torus

theorem torusMat_pow {b₁ b₂ : Fin n → K} (hb : IsONPair h b₁ b₂) (c : K) (k : ℕ) :
    (torusMat h b₁ b₂ c) ^ k = torusMat h b₁ b₂ (c ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, torusMat_one]
  | succ k ih => rw [pow_succ, ih, torusMat_mul h hb, pow_succ]

theorem torusUnitary_pow {b₁ b₂ : Fin n → K} (hb : IsONPair h b₁ b₂) (c : Kˣ)
    (hc : h.norm (c : K) = 1) (k : ℕ) (hck : c ^ k = 1) :
    torusUnitary h hb c hc ^ k = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_torusUnitary, torusMat_pow hb,
    show (c : K) ^ k = ((c ^ k : Kˣ) : K) by simp, hck]
  simp [torusMat_one]

theorem torusUnitary_ne_one_aux (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) {b₁ b₂ : Fin n → K}
    (hb : IsONPair h b₁ b₂) (c : Kˣ) (hc : h.norm (c : K) = 1) (hc2 : c ^ 2 ≠ 1) :
    primeFormConjHom h (idGram K n) (torusUnitary h hb c hc) ≠ 1 := by
  intro h1
  obtain ⟨d, -, hd⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hne _).mp h1
  have hmat : torusMat h b₁ b₂ c = Matrix.scalar (Fin n) (d : K) := by
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hd
    simpa [coe_torusUnitary, GeneralLinearGroup.coe_scalar] using this
  have e1 : torusMat h b₁ b₂ c *ᵥ b₁ = (d : K) • b₁ := by
    rw [hmat]; simp [Matrix.scalar_apply]
  have e2 : torusMat h b₁ b₂ c *ᵥ b₂ = (d : K) • b₂ := by
    rw [hmat]; simp [Matrix.scalar_apply]
  rw [torus_apply_first h hb] at e1
  rw [torus_apply_second h hb] at e2
  have hb1 : b₁ ≠ 0 := hb.ne_zero_left
  have hb2 : b₂ ≠ 0 := by
    rintro rfl
    exact (zero_ne_one : (0 : K) ≠ 1) (by simpa using hb.self₂)
  have h1' := smul_left_injective K hb1 e1
  have h2' := smul_left_injective K hb2 e2
  apply hc2
  have : (c : K) = (c : K)⁻¹ := h1'.trans h2'.symm
  have h3 : (c : K) * c = 1 := by
    calc (c : K) * c = c * (c : K)⁻¹ := by rw [← this]
      _ = 1 := mul_inv_cancel₀ c.ne_zero
  apply Units.ext
  simpa [pow_two] using h3


theorem dvd_card_map_gBlock_of_torus (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) {x : primeFormUnitary h (idGram K n)}
    (H0 : UnitaryPrimaryData h.bar (idForm h n) (toLinU h n x)) {μ : K}
    (hμ : h.bar μ * μ = 1)
    (ha : (X - C μ : K[X]) ∈ primaryFactors ((toLinU h n x :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)))
    {b₁ b₂ : Fin n → K} (hb : IsONPair h b₁ b₂)
    (hx₁ : ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) b₁ = μ • b₁)
    (hx₂ : ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) b₂ = μ • b₂) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p)
    (hζn : h.norm (ζ : K) = 1) :
    p ∣ Nat.card ((gBlock h x (X - C μ)).map (primeFormConjHom h (idGram K n))) := by
  have : Fact p.Prime := ⟨hp⟩
  set T := torusUnitary h hb ζ hζn with hT
  have hTmem : T ∈ gBlock h x (X - C μ) :=
    torusUnitary_mem_gBlock x H0 hμ ha hb hx₁ hx₂ ζ hζn
  have hζ2 : ζ ^ 2 ≠ 1 := by
    intro h2
    have := hζ.dvd_of_pow_eq_one 2 h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  set y : (gBlock h x (X - C μ)).map (primeFormConjHom h (idGram K n)) :=
    ⟨primeFormConjHom h (idGram K n) T, Subgroup.mem_map_of_mem _ hTmem⟩ with hy
  have hyp : y ^ p = 1 := by
    apply Subtype.ext
    change (primeFormConjHom h (idGram K n) T) ^ p = 1
    rw [← map_pow, torusUnitary_pow hb ζ hζn p hζ.pow_eq_one, map_one]
  have hy1 : y ≠ 1 := fun h1 => torusUnitary_ne_one_aux hn hne hb ζ hζn hζ2
    (congrArg Subtype.val h1)
  rw [← orderOf_eq_prime hyp hy1]
  exact orderOf_dvd_natCard y

end Torus

section Rigidity

variable (h) in
@[expose] def TorusComm (M : Matrix (Fin n) (Fin n) K) (τ : K ≃+* K) (u v : Fin n → K) : Prop :=
  ∀ c : Kˣ, h.norm (c : K) = 1 → M * (torusMat h u v c).map τ = torusMat h u v c * M

theorem torusMat_swap (u v : Fin n → K) (c : K) :
    torusMat h u v c = torusMat h v u c⁻¹ := by
  unfold torusMat
  rw [inv_inv, add_assoc, add_comm ((c - 1) • projMat h u), ← add_assoc]

theorem eq_smul_of_torus_eigen {u v : Fin n → K} (hb : IsONPair h u v) {ζ : K} (hζ0 : ζ ≠ 0)
    (hζ1 : ζ ≠ 1) (hζ2 : ζ ^ 2 ≠ 1) {w : Fin n → K} (hw : torusMat h u v ζ *ᵥ w = ζ • w) :
    ∃ c : K, w = c • u := by
  rw [torusMat_mulVec] at hw
  have e2 := congrArg (idForm h n v) hw
  simp only [map_add, map_smul, smul_eq_mul, hb.self₂, hb.cross₂₁, mul_zero, mul_one,
    add_zero] at e2
  have hv0 : idForm h n v w = 0 := by
    have h3 : (ζ⁻¹ - ζ) * idForm h n v w = 0 := by linear_combination e2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exfalso
      apply hζ2
      have : ζ⁻¹ = ζ := sub_eq_zero.mp h4
      field_simp at this
      linear_combination -this
    · exact h4
  rw [hv0] at hw
  refine ⟨idForm h n u w, ?_⟩
  have h5 : (ζ - 1) • (w - idForm h n u w • u) = 0 := by
    rw [smul_sub, sub_eq_zero, smul_smul]
    simp only [mul_zero, zero_smul, add_zero] at hw
    rw [sub_smul, one_smul]
    rw [mul_comm] at hw
    rw [← hw]
    ext i
    simp [mul_comm]
  have := smul_eq_zero.mp h5
  rcases this with h6 | h6
  · exact absurd (sub_eq_zero.mp h6) hζ1
  · exact sub_eq_zero.mp h6

theorem norm_inv_eq_one {c : K} (hn : h.norm c = 1) : h.norm c⁻¹ = 1 := by
  change c⁻¹ * h.bar c⁻¹ = 1
  have : c * h.bar c = 1 := hn
  rw [map_inv₀, ← mul_inv, this, inv_one]

theorem isONPair_symm {u v : Fin n → K} (hb : IsONPair h u v) : IsONPair h v u :=
  ⟨hb.self₂, hb.self₁, hb.cross₂₁, hb.cross₁₂⟩

theorem exists_smul_of_torusComm {u v : Fin n → K} (hb : IsONPair h u v)
    {M : Matrix (Fin n) (Fin n) K} (hT : TorusComm h M (RingEquiv.refl K) u v)
    (hζ : ∃ ζ : Kˣ, h.norm (ζ : K) = 1 ∧ ζ ≠ 1 ∧ ζ ^ 2 ≠ 1) :
    (∃ c : K, M *ᵥ u = c • u) ∧ ∃ c : K, M *ᵥ v = c • v := by
  obtain ⟨ζ, hζn, hζ1, hζ2⟩ := hζ
  have hmap : ∀ A : Matrix (Fin n) (Fin n) K, A.map (RingEquiv.refl K) = A := fun A => by
    ext; rfl
  have key : ∀ {u v : Fin n → K} (hb : IsONPair h u v),
      TorusComm h M (RingEquiv.refl K) u v → ∀ ζ : Kˣ, h.norm (ζ : K) = 1 → ζ ≠ 1 → ζ ^ 2 ≠ 1 →
        ∃ c : K, M *ᵥ u = c • u := by
    intro u v hb hT ζ hζn hζ1 hζ2
    have h1 := hT ζ hζn
    rw [hmap] at h1
    refine eq_smul_of_torus_eigen hb (ζ := ζ) ζ.ne_zero (fun h' => hζ1 (Units.ext h'))
      (fun h' => hζ2 (by apply Units.ext; simpa using h')) ?_
    rw [Matrix.mulVec_mulVec, ← h1, ← Matrix.mulVec_mulVec, torus_apply_first h hb,
      Matrix.mulVec_smul]
  refine ⟨key hb hT ζ hζn hζ1 hζ2, key (isONPair_symm hb) ?_ ζ⁻¹ ?_ ?_ ?_⟩
  · intro c hc
    have := hT c⁻¹ (by simpa [Units.val_inv_eq_inv_val] using norm_inv_eq_one hc)
    rw [torusMat_swap v u (c : K)]
    simpa [Units.val_inv_eq_inv_val] using this
  · simpa using norm_inv_eq_one hζn
  · simpa using hζ1
  · rw [inv_pow]
    simpa using hζ2


theorem exists_eScalar_of_commute_gBlock (hq2 : 2 ≤ ℓ ^ f) {x : primeFormUnitary h (idGram K n)}
    (H0 : UnitaryPrimaryData h.bar (idForm h n) (toLinU h n x))
    (a : primaryFactors ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K))) (ha : IsGoodBlock h (toLinU h n x) a)
    (M : primeFormUnitary h (idGram K n)) (hMx : M * x = x * M)
    (hblock : ∀ g ∈ gBlock h x (a : K[X]), M * g = g * M) :
    ∃ c : AdjoinRoot (a : K[X]), ∀ v : primaryComponent ((toLinU h n x :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) (a : K[X]),
      ((toLinU h n M : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) (v : Fin n → K) =
        ((c • v : primaryComponent ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
          Module.End K (Fin n → K)) (a : K[X])) : Fin n → K) := by
  have hY : toLinU h n M ∈ unitaryCentralizer (idForm h n) (toLinU h n x) :=
    (mem_centralizer_iff_toLinU' x M).mp (Subgroup.mem_centralizer_singleton_iff.mpr hMx)
  refine (commute_specialBlock_iff_scalar H0 hq2 a ha hY).mp fun g hg => ?_
  rw [← map_toLinU_gBlock] at hg
  obtain ⟨g₀, hg₀, rfl⟩ := Subgroup.mem_map.mp hg
  exact commute_toLinU (hblock g₀ hg₀)

theorem exists_scalar_of_commute_gBlock_X_sub_C (hq2 : 2 ≤ ℓ ^ f)
    {x : primeFormUnitary h (idGram K n)}
    (H0 : UnitaryPrimaryData h.bar (idForm h n) (toLinU h n x)) {μ : K}
    (hmem : (X - C μ : K[X]) ∈ primaryFactors ((toLinU h n x :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)))
    (hgood : IsGoodBlock h (toLinU h n x) ⟨X - C μ, hmem⟩)
    (M : primeFormUnitary h (idGram K n)) (hMx : M * x = x * M)
    (hblock : ∀ g ∈ gBlock h x (X - C μ), M * g = g * M) :
    ∃ c : K, ∀ v : Fin n → K, ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) v = μ • v →
        ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = c • v := by
  obtain ⟨c', hc'⟩ := exists_eScalar_of_commute_gBlock hq2 H0 ⟨X - C μ, hmem⟩ hgood M hMx hblock
  obtain ⟨r, rfl⟩ := AdjoinRoot.mk_surjective c'
  refine ⟨r.eval μ, fun v hv => ?_⟩
  have hvmem : v ∈ primaryComponent ((toLinU h n x :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) (X - C μ) :=
    mem_primaryComponent_X_sub_C.mpr hv
  have h1 := hc' ⟨v, hvmem⟩
  rw [coe_mk_smul_primaryComponent] at h1
  by_cases hv0 : v = 0
  · simp [hv0]
  have heig : Module.End.HasEigenvector ((toLinU h n x :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) μ v :=
    ⟨Module.End.mem_eigenspace_iff.mpr hv, hv0⟩
  rw [Module.End.aeval_apply_of_hasEigenvector heig] at h1
  rw [← toLinU_apply_eq]
  exact h1

theorem isGoodBlock_of_eigenpair (hq3 : 3 < ℓ ^ f) {x : primeFormUnitary h (idGram K n)}
    {μ : K} {u v : Fin n → K} (hb : IsONPair h u v)
    (hx₁ : ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) u = μ • u)
    (hx₂ : ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) v = μ • v) :
    ∃ hmem : (X - C μ : K[X]) ∈ primaryFactors ((toLinU h n x :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)),
      IsGoodBlock h (toLinU h n x) ⟨X - C μ, hmem⟩ := by
  have hev : Module.End.HasEigenvalue ((toLinU h n x :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) μ :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hx₁, hb.ne_zero_left⟩
  have hmem := X_sub_C_mem_primaryFactors hev
  have hm : 2 ≤ Module.finrank K (primaryComponent ((toLinU h n x :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) (X - C μ)) :=
    two_le_finrank_of_pair (mem_primaryComponent_X_sub_C.mpr hx₁)
      (mem_primaryComponent_X_sub_C.mpr hx₂) hb.linearIndependent
  exact ⟨hmem, isGoodBlock_X_sub_C (hK := h) hmem hm (not_exceptional_of_three_lt hq3)⟩

theorem torusComm_of_block (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hq2 : 2 ≤ ℓ ^ f)
    {x : primeFormUnitary h (idGram K n)}
    (H0 : UnitaryPrimaryData h.bar (idForm h n) (toLinU h n x)) {μ : K}
    (hμ : h.bar μ * μ = 1)
    (hmem : (X - C μ : K[X]) ∈ primaryFactors ((toLinU h n x :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)))
    (hgood : IsGoodBlock h (toLinU h n x) ⟨X - C μ, hmem⟩) {u v : Fin n → K}
    (hb : IsONPair h u v)
    (hx₁ : ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) u = μ • u)
    (hx₂ : ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) v = μ • v)
    (M : primeFormUnitary h (idGram K n)) (τ : K ≃+* K)
    (hβ : ∀ Y ∈ gBlock h x (X - C μ),
      primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩ *
        primeFormConjHom h (idGram K n) Y =
      primeFormConjHom h (idGram K n) Y *
        primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩) :
    TorusComm h ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) τ u v := by
  have hF : Group.IsPerfect (gBlock h x (X - C μ)) :=
    (isQuasisimple_gBlock hq2 H0 ⟨X - C μ, hmem⟩ hgood).1
  intro c hc
  exact matrix_comm_of_perfect hn hne hF M τ hβ _
    (torusUnitary_mem_gBlock x H0 hμ hmem hb hx₁ hx₂ c hc)

end Rigidity

end CFSG.HardMathSupport.Timmesfeld.CrossChar
