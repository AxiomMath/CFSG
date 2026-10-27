module

public import CFSG.LieType.Chevalley.RootWeightOptimalParabolic
public import CFSG.LieType.Chevalley.GraphFixedParabolicLevi
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalOpposite
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public noncomputable section

namespace CFSG.LieType.Chevalley.EvenOddRadical

open CFSG.Blueprint CFSG.Blueprint.Chevalley RootWeightSpace RootWeight
open scoped RealInnerProductSpace

variable {τ : Tag} {K : Type} [Field K]

@[expose] def innerHom
    (l : RootWeightSpace τ) : (Fin τ.rank → ℤ) →+ ℝ where
  toFun v := ⟪ofLattice v, l⟫
  map_zero' := by rw [ofLattice_zero, inner_zero_left]
  map_add' u v := by rw [ofLattice_add, inner_add_left]

theorem inner_ofLattice_eq_sum
    (l : RootWeightSpace τ) (v : Fin τ.rank → ℤ) :
    ⟪ofLattice v, l⟫ = ∑ i, (v i : ℝ) * ⟪ofLattice (Pi.single i 1 : Fin τ.rank → ℤ), l⟫ := by
  have h := congrArg (innerHom l) (eq_sum_smul_single v)
  rw [map_sum] at h
  refine h.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [map_zsmul, zsmul_eq_mul]
  rfl

theorem exists_pos_le_inner
    {l : RootWeightSpace τ}
    (hl : ∀ i, 0 ≤ ⟪ofLattice (Pi.single i 1 : Fin τ.rank → ℤ), l⟫) {A : Set (Fin τ.rank)}
    (hA : ∀ i, i ∈ A ↔ ⟪ofLattice (Pi.single i 1 : Fin τ.rank → ℤ), l⟫ = 0) :
    ∃ ε > 0, ∀ α ∈ parabolicRadicalRoots τ A, ε ≤ ⟪ofLattice α, l⟫ := by
  classical
  by_cases hne : (Finset.univ.filter fun i => i ∉ A).Nonempty
  · obtain ⟨i₀, hi₀, hmin⟩ := (Finset.univ.filter fun i => i ∉ A).exists_min_image
      (fun i => ⟪ofLattice (Pi.single i 1 : Fin τ.rank → ℤ), l⟫) hne
    have hi₀A : i₀ ∉ A := (Finset.mem_filter.1 hi₀).2
    have hpos : 0 < ⟪ofLattice (Pi.single i₀ 1 : Fin τ.rank → ℤ), l⟫ :=
      lt_of_le_of_ne (hl i₀) fun h => hi₀A ((hA i₀).2 h.symm)
    refine ⟨_, hpos, fun α hα => ?_⟩
    obtain ⟨hroot, hht, i, hi, hαi⟩ := mem_parabolicRadicalRoots_iff.1 hα
    have hnn := (IsRoot.height_pos_iff hroot).1 hht
    have h1 : (1 : ℝ) ≤ α i := by
      have := hnn i
      exact_mod_cast (show (1 : ℤ) ≤ α i by omega)
    rw [inner_ofLattice_eq_sum l α]
    calc ⟪ofLattice (Pi.single i₀ 1 : Fin τ.rank → ℤ), l⟫
        ≤ ⟪ofLattice (Pi.single i 1 : Fin τ.rank → ℤ), l⟫ :=
          hmin i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
      _ ≤ (α i : ℝ) * ⟪ofLattice (Pi.single i 1 : Fin τ.rank → ℤ), l⟫ :=
          le_mul_of_one_le_left (hl i) h1
      _ ≤ ∑ j, (α j : ℝ) * ⟪ofLattice (Pi.single j 1 : Fin τ.rank → ℤ), l⟫ :=
          Finset.single_le_sum (f := fun j => (α j : ℝ) *
            ⟪ofLattice (Pi.single j 1 : Fin τ.rank → ℤ), l⟫)
            (fun j _ => mul_nonneg (by exact_mod_cast hnn j) (hl j)) (Finset.mem_univ i)
  · refine ⟨1, one_pos, fun α hα => ?_⟩
    obtain ⟨-, -, i, hi, -⟩ := mem_parabolicRadicalRoots_iff.1 hα
    exact absurd ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩ hne

theorem eq_one_of_labelRaises_mul
    {l : RootWeightSpace τ}
    (hl : ∀ i, 0 ≤ ⟪ofLattice (Pi.single i 1 : Fin τ.rank → ℤ), l⟫) {A : Set (Fin τ.rank)}
    (hA : ∀ i, i ∈ A ↔ ⟪ofLattice (Pi.single i 1 : Fin τ.rank → ℤ), l⟫ = 0)
    {u m : ModGL τ K} (hu : u ∈ parabolicRadical τ K A) (hm : m ∈ parabolicLevi τ K A)
    {ε : ℝ} (hε : 0 < ε)
    (h : LabelRaises (latticeGrade l)
      ε (((u * m : ModGL τ K) : Module.End K (RootModule τ K)) - 1)) :
    m = 1 := by
  obtain ⟨ε₁, hε₁, hR⟩ := exists_pos_le_inner hl hA
  have hQ := rootSpan_le_labelRaisingSubgroup (K := K) (innerHom l) hε₁.le
    (X := parabolicRadicalRoots τ A) fun α hα => ⟨hα.1.1, hR α hα⟩
  have hu' := (hQ (inv_mem hu)).1
  have hM := parabolicLevi_le_labelRaisingSubgroup (K := K) (-innerHom l) (J := A)
    fun j hj => by rw [AddMonoidHom.neg_apply, neg_eq_zero]; exact (hA j).1 hj
  have hm' := (hM hm).1
  have h' : LabelRaises (gradeBy (innerHom l)) ε
      (((u * m : ModGL τ K) : Module.End K (RootModule τ K)) - 1) := h
  have huu : (↑u⁻¹ : Module.End K (RootModule τ K)) * (u : Module.End K (RootModule τ K)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e : (m : Module.End K (RootModule τ K)) - 1 =
      (↑u⁻¹ : Module.End K (RootModule τ K)) *
          (((u * m : ModGL τ K) : Module.End K (RootModule τ K)) - 1) +
        ((↑u⁻¹ : Module.End K (RootModule τ K)) - 1) := by
    rw [Units.val_mul]
    calc (m : Module.End K (RootModule τ K)) - 1 =
        (↑u⁻¹ : Module.End K (RootModule τ K)) * (u : Module.End K (RootModule τ K)) *
          (m : Module.End K (RootModule τ K)) - 1 := by rw [huu, one_mul]
      _ = _ := by noncomm_ring
  have hraise : LabelRaises (gradeBy (innerHom l)) (min ε ε₁)
      ((m : Module.End K (RootModule τ K)) - 1) := by
    rw [e]
    refine LabelRaises.add ?_ (hu'.mono (min_le_right _ _))
    exact ((LabelRaises.of_sub_one (hu'.mono hε₁.le)).mul h').mono
      (by rw [zero_add]; exact min_le_left _ _)
  exact eq_one_of_labelRaises (-innerHom l) (lt_min hε hε₁) hm' (by rwa [neg_neg])

theorem labelRaises_of_map_filtration_le
    (D : RootWeightDatum K)
    {T : Module.End K (RootModule D.tag K)} {ε : ℝ} (l : D.space)
    (h : ∀ c, (D.filtration l c).map T ≤ D.filtration l (c + ε)) :
    LabelRaises (latticeGrade (l : RootWeightSpace D.tag)) ε T := by
  intro a b hab
  have hb : Finsupp.single b (1 : K) ∈ D.filtration l ⟪D.labelWeight b, l⟫ :=
    (D.single_mem_filtration_iff l _ b).2 le_rfl
  have hTb := h _ (Submodule.mem_map_of_mem hb)
  rw [D.filtration_eq_supported] at hTb
  have ha := (Finsupp.mem_supported K _).1 hTb (Finsupp.mem_support_iff.2 hab)
  simp only [Set.mem_ofPred_eq] at ha
  rw [D.inner_labelWeight, D.inner_labelWeight] at ha
  exact ha

open _root_.Classical in
theorem exists_optimal_parabolic_prime
    [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (D : RootWeightDatum K)
    {R : Subgroup (ModGL D.tag K)} (hRG : R ≤ D.group) (hR2 : IsPGroup p R) (hR : R ≠ ⊥) :
    ∃ g ∈ D.group, ∃ l ∈ D.dominant, ∃ M : ℝ, 0 < M ∧
      (∀ x ∈ D.group, x ∈ Subgroup.normalizer (R : Set (ModGL D.tag K)) →
        g⁻¹ * x * g ∈ D.parabolic (D.face l)) ∧
      ∀ q ∈ R, LabelRaises (latticeGrade (l : RootWeightSpace D.tag)) M
        (((g⁻¹ * q * g : ModGL D.tag K) : Module.End K (RootModule D.tag K)) - 1) := by
  obtain ⟨M, hM0, -, -, F, -, -, ⟨g, hg, l, hl, hl1, hgl⟩, hdom, -⟩ :=
    D.root_p_subgroup_optimal_parabolic_containment p R hRG hR2 hR
  obtain ⟨-, -, hNF, hstab, -⟩ := hdom g hg l hl hl1 hgl
  refine ⟨g, hg, l, hl, M, hM0, fun x hxG hxN => ?_, fun q hq => ?_⟩
  · have h1 : x ∈ {y : ModGL D.tag K | y ∈ D.group ∧ ∀ c : ℝ,
        (F c).map (y : Module.End K (RootModule D.tag K)) = F c} :=
      ⟨hxG, hNF x (Subgroup.mem_inf.2 ⟨hxG, hxN⟩)⟩
    rw [hstab] at h1
    obtain ⟨y, hy, rfl⟩ := h1
    have e : g⁻¹ * ((MulAut.conj g).toMonoidHom y) * g = y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact hy
  · by_cases hq1 : q = 1
    · subst hq1
      rw [mul_one, inv_mul_cancel, Units.val_one, sub_self]
      exact LabelRaises.zero
    · have hA := subgroupShifts_nonempty hR
      have hA0 := zero_notMem_subgroupShifts R
      have key := (le_minWeightShift_iff D.isInternal_weightSpace (conjFamily_nonempty hA g)
        (zero_notMem_conjFamily hA0 g) l M).1 hgl.ge
      have hmem : (↑g⁻¹ : Module.End K (RootModule D.tag K)) *
          ((q : Module.End K (RootModule D.tag K)) - 1) * ↑g ∈ conjFamily (subgroupShifts R) g :=
        Finset.mem_image_of_mem _ (mem_subgroupShifts.2 ⟨q, hq, hq1, rfl⟩)
      have := labelRaises_of_map_filtration_le D l (key _ hmem)
      rwa [units_inv_mul_sub_one_mul] at this

theorem exists_optimal_radical_ordinary_prime
    [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] {R : Subgroup (ModGL τ K)} (hRG : R ≤ adjointGroup τ K) (hR2 : IsPGroup p R)
    (hR : R ≠ ⊥) :
    ∃ g ∈ adjointGroup τ K, ∃ J : Set (Fin τ.rank),
      (∀ x ∈ adjointGroup τ K, x ∈ Subgroup.normalizer (R : Set (ModGL τ K)) →
        g⁻¹ * x * g ∈ parabolicSubgroup τ K J) ∧
      ∀ q ∈ R, g⁻¹ * q * g ∈ parabolicRadical τ K J := by
  obtain ⟨g, hg, l, hl, M, hM0, hP, hraise⟩ : ∃ g ∈ adjointGroup τ K,
      ∃ l ∈ (RootWeightDatum.ordinary (K := K) τ).dominant, ∃ M : ℝ, 0 < M ∧
        (∀ x ∈ adjointGroup τ K, x ∈ Subgroup.normalizer (R : Set (ModGL τ K)) →
          g⁻¹ * x * g ∈ parabolicSubgroup τ K ((RootWeightDatum.ordinary (K := K) τ).face l)) ∧
        ∀ q ∈ R, LabelRaises (latticeGrade (τ := τ) l.1) M
          (((g⁻¹ * q * g : ModGL τ K) : Module.End K (RootModule τ K)) -
            (1 : Module.End K (RootModule τ K))) :=
    exists_optimal_parabolic_prime p (RootWeightDatum.ordinary τ) hRG hR2 hR
  refine ⟨g, hg, (RootWeightDatum.ordinary τ).face l, hP, fun q hq => ?_⟩
  have hl' : ∀ i, 0 ≤ ⟪ofLattice (Pi.single i 1 : Fin τ.rank → ℤ), (l.1 : RootWeightSpace τ)⟫ :=
    fun i => hl i
  have hA : ∀ i, i ∈ (RootWeightDatum.ordinary (K := K) τ).face l ↔
      ⟪ofLattice (Pi.single i 1 : Fin τ.rank → ℤ), (l.1 : RootWeightSpace τ)⟫ = 0 :=
    fun i => Iff.rfl
  obtain ⟨qm, ⟨hu, hm, hy⟩, -⟩ :=
    (parabolic_root_radical_Levi_factors τ K ((RootWeightDatum.ordinary τ).face l)).2.2.2.2.2.2.1
      _ (hP q (hRG hq) (Subgroup.le_normalizer hq))
  have h := hraise q hq
  rw [hy] at h
  have hm1 := eq_one_of_labelRaises_mul hl' hA hu hm hM0 h
  rw [hy, hm1, mul_one]
  exact hu

theorem exists_optimal_radical_ordinary
    [Finite K] [CharP K 2]
    {R : Subgroup (ModGL τ K)} (hRG : R ≤ adjointGroup τ K) (hR2 : IsPGroup 2 R)
    (hR : R ≠ ⊥) :
    ∃ g ∈ adjointGroup τ K, ∃ J : Set (Fin τ.rank),
      (∀ x ∈ adjointGroup τ K, x ∈ Subgroup.normalizer (R : Set (ModGL τ K)) →
        g⁻¹ * x * g ∈ parabolicSubgroup τ K J) ∧
      ∀ q ∈ R, g⁻¹ * q * g ∈ parabolicRadical τ K J :=
  exists_optimal_radical_ordinary_prime 2 hRG hR2 hR

theorem fixed_dominant_unfold
    (t : TwistTag) (σ : K ≃+* K) (hσ : σ ^ t.order = 1)
    {l : (RootWeightDatum.fixed t σ hσ).space} (hl : l ∈ (RootWeightDatum.fixed t σ hσ).dominant) :
    (∀ j, 0 ≤ ⟪ofLattice (Pi.single j 1 : Fin t.tag.rank → ℤ), l.1⟫) ∧
      ∀ j, j ∈ t.orbitUnion ((RootWeightDatum.fixed t σ hσ).face l) ↔
        ⟪ofLattice (Pi.single j 1 : Fin t.tag.rank → ℤ), l.1⟫ = 0 := by
  set l' : RootWeightSpace t.tag := l.1 with hl'def
  have hlE : l' ∈ twistFixedSpace t := l.2
  have key : ∀ j, ⟪ofLattice (t.orbitSum (t.orbitIndex j)), l'⟫ =
      (t.orbit (t.orbitIndex j)).card * ⟪ofLattice (Pi.single j 1 : Fin t.tag.rank → ℤ), l'⟫ :=
    fun j => inner_orbitSum hlE (t.mem_orbit_orbitIndex j)
  have hcard : ∀ j, (0 : ℝ) < (t.orbit (t.orbitIndex j)).card := fun j => by
    exact_mod_cast card_orbit_pos t _
  have hdom : ∀ a, 0 ≤ ⟪ofLattice (t.orbitSum a), l'⟫ := fun a => hl a
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have h1 := hdom (t.orbitIndex j)
    rw [key j] at h1
    exact (mul_nonneg_iff_of_pos_left (hcard j)).1 h1
  · refine (TwistTag.mem_orbitUnion t (J := (RootWeightDatum.fixed t σ hσ).face l)).trans ?_
    constructor
    · rintro ⟨a, ha, hja⟩
      have hja' := (t.mem_orbit_iff).1 hja
      have h0 : ⟪ofLattice (t.orbitSum a), l'⟫ = 0 := ha
      rw [← hja', key j] at h0
      exact (mul_eq_zero.1 h0).resolve_left (hcard j).ne'
    · intro h0
      refine ⟨t.orbitIndex j, ?_, t.mem_orbit_orbitIndex j⟩
      show ⟪ofLattice (t.orbitSum (t.orbitIndex j)), l'⟫ = 0
      rw [key j, h0, mul_zero]

theorem exists_optimal_radical_fixed
    [Finite K] [CharP K 2] (t : TwistTag) (σ : K ≃+* K)
    (hσ : σ ^ t.order = 1) {R : Subgroup (ModGL t.tag K)}
    (hRG : R ≤ graphFixedRootGroup t K σ.toRingHom) (hR2 : IsPGroup 2 R) (hR : R ≠ ⊥) :
    ∃ g ∈ graphFixedRootGroup t K σ.toRingHom, ∃ J : Set (Fin t.foldedTag.rank),
      (∀ x ∈ graphFixedRootGroup t K σ.toRingHom,
        x ∈ Subgroup.normalizer (R : Set (ModGL t.tag K)) →
          g⁻¹ * x * g ∈ graphFixedParabolic t K σ.toRingHom J) ∧
      ∀ q ∈ R, g⁻¹ * q * g ∈ graphFixedParabolicRadical t K σ.toRingHom J := by
  obtain ⟨g, hg, l, hl, M, hM0, hP, hraise⟩ : ∃ g ∈ graphFixedRootGroup t K σ.toRingHom,
      ∃ l ∈ (RootWeightDatum.fixed t σ hσ).dominant, ∃ M : ℝ, 0 < M ∧
        (∀ x ∈ graphFixedRootGroup t K σ.toRingHom,
          x ∈ Subgroup.normalizer (R : Set (ModGL t.tag K)) →
          g⁻¹ * x * g ∈
            graphFixedParabolic t K σ.toRingHom ((RootWeightDatum.fixed t σ hσ).face l)) ∧
        ∀ q ∈ R, LabelRaises (latticeGrade (τ := t.tag) l.1) M
          (((g⁻¹ * q * g : ModGL t.tag K) : Module.End K (RootModule t.tag K)) -
            (1 : Module.End K (RootModule t.tag K))) :=
    exists_optimal_parabolic_prime 2 (RootWeightDatum.fixed t σ hσ) hRG hR2 hR
  set J := (RootWeightDatum.fixed t σ hσ).face l with hJ
  refine ⟨g, hg, J, hP, fun q hq => ?_⟩
  obtain ⟨hl', hA⟩ := fixed_dominant_unfold t σ hσ hl
  obtain ⟨qm, ⟨hu, hm, hy⟩, -⟩ :=
    (diagram_fixed_parabolic_root_radical_Levi_factors t K σ J).2.2.2.2.2.2.2.2.2.2.2.1 _
      (hP q (hRG hq) (Subgroup.le_normalizer hq))
  have h := hraise q hq
  rw [hy] at h
  have hm1 := eq_one_of_labelRaises_mul hl' hA (Subgroup.mem_inf.1 hu).1
    (Subgroup.mem_inf.1 hm).1 hM0 h
  rw [hy, hm1, mul_one]
  exact hu

end CFSG.LieType.Chevalley.EvenOddRadical
