module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.Quasithin.Background.A3Structure316
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis
public import CFSG.GroupTheory.WeirSylow.FormSpace

public section

namespace CFSG.GroupTheory.WeirSylow

open Module Finset
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData sesqUnitaryGroup)
open CFSG.Quasithin (StatedGU)
open scoped Matrix

theorem exists_unitaryFieldData (L : Type) [Field L] [Fintype L] {q : ℕ}
    (hq : Fintype.card L = q ^ 2) :
    ∃ f, q = ringChar L ^ f ∧ UnitaryFieldData (ringChar L) f L := by
  obtain ⟨m, hp, hm⟩ := FiniteField.card L (ringChar L)
  have hdvd : q ∣ ringChar L ^ (m : ℕ) := ⟨q, by rw [← hm, hq, sq]⟩
  obtain ⟨f, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have h2 : ringChar L ^ (2 * f) = ringChar L ^ (m : ℕ) := by rw [pow_mul', ← hq, hm]
  have hmf : (m : ℕ) = 2 * f := (Nat.pow_right_injective hp.two_le h2).symm
  refine ⟨f, rfl, hp, ?_, ?_⟩
  · have := m.pos
    omega
  · rw [Nat.card_eq_fintype_card, hm, hmf]

variable {p₀ f : ℕ} {L : Type} [Field L]

theorem unitaryBar_eq_pow (h : UnitaryFieldData p₀ f L) {q : ℕ} (hq : q = p₀ ^ f)
    (c : L) : h.bar c = c ^ q := by
  rw [h.bar_apply, hq]

section Standard

variable (h : UnitaryFieldData p₀ f L) (n : ℕ)

@[expose] noncomputable def stdHerm : (Fin n → L) →ₛₗ[h.bar] (Fin n → L) →ₗ[L] L :=
  LinearMap.mk₂'ₛₗ h.bar (RingHom.id L) (fun x y => ∑ i, h.bar (x i) * y i)
    (fun x x' y => by simp [add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum, mul_assoc])
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum, mul_left_comm])

variable {h n}

theorem stdHerm_apply (x y : Fin n → L) : stdHerm h n x y = ∑ i, h.bar (x i) * y i :=
  rfl

theorem stdHerm_single (i j : Fin n) :
    stdHerm h n (Pi.single i 1) (Pi.single j 1) = if i = j then 1 else 0 := by
  rw [stdHerm_apply, Finset.sum_eq_single i (fun k _ hk => by
    rw [Pi.single_eq_of_ne hk, map_zero, zero_mul]) (by simp), Pi.single_eq_same, map_one,
    one_mul, Pi.single_apply]

variable (h n) in
theorem stdHerm_isSymm : (stdHerm h n).IsSymm :=
  ⟨fun x y => by
    rw [stdHerm_apply, stdHerm_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, h.bar_bar, mul_comm]⟩

variable (h n) in
theorem stdHerm_separatingLeft : (stdHerm h n).SeparatingLeft := fun x hx => by
  funext i
  have := hx (Pi.single i 1)
  rw [stdHerm_apply, Finset.sum_eq_single i (fun k _ hk => by
    rw [Pi.single_eq_of_ne hk, mul_zero]) (by simp), Pi.single_eq_same, mul_one] at this
  exact (map_eq_zero_iff h.bar h.bar.injective).1 this

end Standard

section Matrix

variable (h : UnitaryFieldData p₀ f L) {q : ℕ} (hq : q = p₀ ^ f) (n : ℕ)

noncomputable abbrev stdHermIsom : Subgroup ((Fin n → L) ≃ₗ[L] (Fin n → L)) :=
  formIsometryGroup L (fun x y => stdHerm h n x y)

variable {h n}

include hq in
theorem mem_stdHermIsom_iff (g : (Fin n → L) ≃ₗ[L] (Fin n → L)) :
    g ∈ stdHermIsom h n ↔
      ((LinearMap.toMatrix' g.toLinearMap).map (· ^ q))ᵀ * LinearMap.toMatrix' g.toLinearMap =
        1 := by
  set A := LinearMap.toMatrix' g.toLinearMap with hA
  have hcol : ∀ j, g (Pi.single j 1) = fun i => A i j := fun j => funext fun i => by
    rw [hA, LinearMap.toMatrix'_apply]
    rfl
  have hentry : ∀ j k, stdHerm h n (g (Pi.single j 1)) (g (Pi.single k 1)) =
      ((A.map (· ^ q))ᵀ * A) j k := fun j k => by
    rw [hcol, hcol, stdHerm_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.transpose_apply, Matrix.map_apply, unitaryBar_eq_pow h hq]
  constructor
  · intro hg
    ext j k
    rw [← hentry, Matrix.one_apply]
    exact (hg (Pi.single j 1) (Pi.single k 1)).trans (stdHerm_single j k)
  · intro hAq x y
    have hB := LinearMap.ext_basis (Pi.basisFun L (Fin n)) (Pi.basisFun L (Fin n))
      (B := ((stdHerm h n).comp g.toLinearMap).compl₂ g.toLinearMap) (B' := stdHerm h n)
      fun j k => by
        simp only [Pi.basisFun_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
          LinearEquiv.coe_coe]
        rw [hentry, hAq, stdHerm_single, Matrix.one_apply]
    have := congrArg (fun B : (Fin n → L) →ₛₗ[h.bar] (Fin n → L) →ₗ[L] L => B x y) hB
    simpa using this

noncomputable abbrev matrixEquiv : ((Fin n → L) ≃ₗ[L] (Fin n → L)) ≃* GL (Fin n) L :=
  CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv
    (Pi.basisFun L (Fin n))

theorem matrixEquiv_val (g : (Fin n → L) ≃ₗ[L] (Fin n → L)) :
    ((matrixEquiv (n := n) (L := L) g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      LinearMap.toMatrix' g.toLinearMap := by
  rw [CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv_val,
    LinearMap.toMatrix_eq_toMatrix']

include hq in
theorem map_stdHermIsom_eq_statedGU :
    (stdHermIsom h n).map (matrixEquiv (n := n) (L := L)).toMonoidHom = StatedGU n q L := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    refine Subgroup.subset_closure ?_
    change ((((matrixEquiv g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map (· ^ q))ᵀ *
      ((matrixEquiv g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) = 1
    rw [matrixEquiv_val]
    exact (mem_stdHermIsom_iff hq g).1 hg
  · refine (Subgroup.closure_le _).2 fun A hA => ?_
    rw [SetLike.mem_coe, Subgroup.mem_map_equiv, mem_stdHermIsom_iff hq, ← matrixEquiv_val,
      MulEquiv.apply_symm_apply]
    exact hA

include hq in
theorem natCard_statedGU_eq :
    Nat.card (StatedGU n q L) = Nat.card (stdHermIsom h n) := by
  rw [← map_stdHermIsom_eq_statedGU (h := h) hq]
  exact Subgroup.card_map_of_injective (MulEquiv.injective _)

theorem natCard_formIsometryGroup_eq_sesqUnitaryGroup {V : Type*} [AddCommGroup V] [Module L V]
    (B : V →ₛₗ[h.bar] V →ₗ[L] L) :
    Nat.card (formIsometryGroup L (fun x y => B x y)) = Nat.card (sesqUnitaryGroup B) := by
  refine Nat.card_congr ⟨fun g => ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv L V).symm g.1,
    fun x y => g.2 x y⟩, fun g => ⟨LinearMap.GeneralLinearGroup.generalLinearEquiv L V g.1,
    fun x y => g.2 x y⟩, fun g => ?_, fun g => ?_⟩
  · exact Subtype.ext (MulEquiv.apply_symm_apply _ _)
  · exact Subtype.ext (MulEquiv.symm_apply_apply _ _)

end Matrix

theorem natCard_statedGU_cast [Fintype L] {q : ℕ} (hq : Fintype.card L = q ^ 2) {n : ℕ}
    (hn : 1 ≤ n) : (Nat.card (StatedGU n q L) : ℤ) =
      ((q : ℤ) ^ (n * (n - 1) / 2) * ∏ i ∈ Icc 1 n, (-1 : ℤ) ^ i) *
        ∏ i ∈ Icc 1 n, ((-(q : ℤ)) ^ i - 1) := by
  obtain ⟨f, hqf, h⟩ := exists_unitaryFieldData L hq
  rw [natCard_statedGU_eq (h := h) hqf, natCard_formIsometryGroup_eq_sesqUnitaryGroup,
    (CFSG.LinearGroups.unitary_full_group_order h (stdHerm_isSymm h n)
      (stdHerm_separatingLeft h n) (Module.finrank_fin_fun L) hn).1, ← hqf, mul_assoc,
    ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have h1 : ((-1 : ℤ) ^ i) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [neg_pow]
  linear_combination (-(q : ℤ) ^ i) * h1

section Spaces

variable (h : UnitaryFieldData p₀ f L)

@[expose] def IsHermitianSpace (S : FormSpace L L) : Prop :=
  ∃ B : S.V →ₛₗ[h.bar] S.V →ₗ[L] L, (∀ x y, S.F x y = B x y) ∧ B.IsSymm ∧ B.SeparatingLeft

@[expose] noncomputable def piHerm {ι : Type*} [Fintype ι] {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module L (V i)] (B : ∀ i, V i →ₛₗ[h.bar] V i →ₗ[L] L) :
    (∀ i, V i) →ₛₗ[h.bar] (∀ i, V i) →ₗ[L] L :=
  LinearMap.mk₂'ₛₗ h.bar (RingHom.id L) (fun x y => ∑ i, B i (x i) (y i))
    (fun x x' y => by simp [Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum])
    (fun x y y' => by simp [Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum])

theorem piHerm_apply {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, AddCommGroup (V i)]
    [∀ i, Module L (V i)] (B : ∀ i, V i →ₛₗ[h.bar] V i →ₗ[L] L) (x y : ∀ i, V i) :
    piHerm h B x y = ∑ i, B i (x i) (y i) :=
  rfl

@[expose] noncomputable def prodHerm {V W : Type*} [AddCommGroup V] [Module L V]
    [AddCommGroup W] [Module L W] (B : V →ₛₗ[h.bar] V →ₗ[L] L) (C : W →ₛₗ[h.bar] W →ₗ[L] L) :
    (V × W) →ₛₗ[h.bar] (V × W) →ₗ[L] L :=
  LinearMap.mk₂'ₛₗ h.bar (RingHom.id L) (fun x y => B x.1 y.1 + C x.2 y.2)
    (fun x x' y => by
      simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
      ring)
    (fun c x y => by
      simp only [Prod.smul_fst, Prod.smul_snd, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
        smul_eq_mul]
      ring)
    (fun x y y' => by
      simp only [Prod.fst_add, Prod.snd_add, map_add]
      ring)
    (fun c x y => by
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul, RingHom.id_apply]
      ring)

theorem prodHerm_apply {V W : Type*} [AddCommGroup V] [Module L V] [AddCommGroup W]
    [Module L W] (B : V →ₛₗ[h.bar] V →ₗ[L] L) (C : W →ₛₗ[h.bar] W →ₗ[L] L) (x y : V × W) :
    prodHerm h B C x y = B x.1 y.1 + C x.2 y.2 :=
  rfl

variable {h}

theorem isHermitianSpace_pi {ι : Type} [Fintype ι] (S : ι → FormSpace L L)
    (hS : ∀ i, IsHermitianSpace h (S i)) : IsHermitianSpace h (FormSpace.pi S) := by
  classical
  choose B hBF hBs hBn using hS
  refine ⟨piHerm h B, fun x y => ?_, ⟨fun x y => ?_⟩, fun x hx => ?_⟩
  · change ∑ i, (S i).F (x i) (y i) = _
    simp [hBF, piHerm_apply]
  · rw [piHerm_apply, piHerm_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => (hBs i).eq _ _
  · funext i
    refine hBn i (x i) fun z => ?_
    have := hx (Pi.single i z)
    rwa [piHerm_apply, Finset.sum_eq_single i
      (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero]) (by simp),
      Pi.single_eq_same] at this

theorem isHermitianSpace_prod (S T : FormSpace L L) (hS : IsHermitianSpace h S)
    (hT : IsHermitianSpace h T) : IsHermitianSpace h (S.prod T) := by
  obtain ⟨B, hBF, hBs, hBn⟩ := hS
  obtain ⟨C, hCF, hCs, hCn⟩ := hT
  refine ⟨prodHerm h B C, fun x y => ?_, ⟨fun x y => ?_⟩, fun x hx => ?_⟩
  · change S.F x.1 y.1 + T.F x.2 y.2 = _
    rw [hBF, hCF, prodHerm_apply]
  · rw [prodHerm_apply, prodHerm_apply, map_add, hBs.eq, hCs.eq]
  · refine Prod.ext (hBn x.1 fun z => ?_) (hCn x.2 fun z => ?_)
    · simpa [prodHerm_apply] using hx (z, 0)
    · simpa [prodHerm_apply] using hx (0, z)

variable (h) in
@[expose] noncomputable def stdHermSpace (n : ℕ) : FormSpace L L :=
  ⟨Fin n → L, fun x y => stdHerm h n x y⟩

theorem isHermitianSpace_stdHermSpace (n : ℕ) : IsHermitianSpace h (stdHermSpace h n) :=
  ⟨stdHerm h n, fun _ _ => rfl, stdHerm_isSymm h n, stdHerm_separatingLeft h n⟩

theorem finrank_stdHermSpace (n : ℕ) : finrank L (stdHermSpace h n).V = n :=
  Module.finrank_fin_fun L

theorem exists_injective_isom_statedGU {q : ℕ} (hq : q = p₀ ^ f) [Finite L]
    (S : FormSpace L L) (hS : IsHermitianSpace h S) {n : ℕ} (hdim : finrank L S.V = n) :
    ∃ ψ : S.isom →* StatedGU n q L, Function.Injective ψ := by
  obtain ⟨B, hBF, hBs, hBn⟩ := hS
  obtain ⟨e₀, he₀⟩ := h.exists_orthonormal_basis hBs hBn
  let e := e₀.reindex (finCongr hdim)
  have he : ∀ i j, B (e i) (e j) = if i = j then 1 else 0 := fun i j => by
    simp only [e, Module.Basis.reindex_apply, he₀, (finCongr hdim).symm.injective.eq_iff]
  have hι : ∀ x y, stdHerm h n (e.equivFun x) (e.equivFun y) = B x y := by
    have := LinearMap.ext_basis e e
      (B := ((stdHerm h n).comp e.equivFun.toLinearMap).compl₂ e.equivFun.toLinearMap) (B' := B)
      fun i j => by
        simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
        rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, Module.Basis.repr_self,
          Module.Basis.repr_self, Finsupp.single_eq_pi_single, Finsupp.single_eq_pi_single,
          stdHerm_single, he]
    intro x y
    have h' := congrArg (fun C : S.V →ₛₗ[h.bar] S.V →ₗ[L] L => C x y) this
    simpa using h'
  let e₁ : S.isom ≃* stdHermIsom h n :=
    formIsometryGroupCongr e.equivFun fun x y => by rw [hBF]; exact hι x y
  have hmem : ∀ g : stdHermIsom h n, matrixEquiv g.1 ∈ StatedGU n q L := fun g => by
    rw [← map_stdHermIsom_eq_statedGU (h := h) hq]
    exact Subgroup.mem_map_of_mem _ g.2
  let ψ₀ : stdHermIsom h n →* StatedGU n q L :=
    { toFun := fun g => ⟨matrixEquiv g.1, hmem g⟩
      map_one' := Subtype.ext (map_one matrixEquiv)
      map_mul' := fun g g' => Subtype.ext (map_mul matrixEquiv g.1 g'.1) }
  refine ⟨ψ₀.comp e₁.toMonoidHom, fun g g' hgg => e₁.injective (Subtype.ext ?_)⟩
  exact matrixEquiv.injective (congrArg Subtype.val hgg)

end Spaces

end CFSG.GroupTheory.WeirSylow
