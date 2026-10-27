module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslType
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.InducedInner
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.BlocksAbstract
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslSplit

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Polynomial Matrix CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.CALinearPrimary CFSG.RankThree.PartTwo.KFacts
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns CFSG.LocalAnalysis.GLTheoremB

section Lift

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem exists_scalar_cube (hZ : ∀ z ∈ scalars n K, z ^ 3 = 1 → z = 1)
    {z : SpecialLinearGroup (Fin n) K} (hz : z ∈ scalars n K) :
    ∃ w ∈ scalars n K, w ^ 3 = z := by
  classical
  let f : ↥(scalars n K) → ↥(scalars n K) := fun w => ⟨(w : SpecialLinearGroup (Fin n) K) ^ 3,
    (scalars n K).pow_mem w.2 3⟩
  have hinj : Function.Injective f := by
    intro w1 w2 h12
    have h12' : (w1 : SpecialLinearGroup (Fin n) K) ^ 3 = (w2 : SpecialLinearGroup (Fin n) K) ^ 3 :=
      congrArg Subtype.val h12
    have hc : Commute (w1 : SpecialLinearGroup (Fin n) K) (w2 : SpecialLinearGroup (Fin n) K) :=
      (Subgroup.mem_center_iff.mp (scalars_le_center n K w1.2) _).symm
    have h1 : ((w1 : SpecialLinearGroup (Fin n) K) * (w2 : SpecialLinearGroup (Fin n) K)⁻¹) ^ 3 =
        1 := by
      rw [(hc.inv_right).mul_pow, h12', inv_pow, mul_inv_cancel]
    have h2 := hZ _ ((scalars n K).mul_mem w1.2 ((scalars n K).inv_mem w2.2)) h1
    exact Subtype.ext (mul_inv_eq_one.1 h2)
  obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨z, hz⟩
  exact ⟨w, w.2, congrArg Subtype.val hw⟩

theorem exists_lift_cube (hZ : ∀ z ∈ scalars n K, z ^ 3 = 1 → z = 1) {y : projectiveSL n K}
    (hy : y ^ 3 = 1) : ∃ b : SpecialLinearGroup (Fin n) K, proj n K b = y ∧ b ^ 3 = 1 := by
  obtain ⟨b0, rfl⟩ := proj_surjective n K y
  have h1 : b0 ^ 3 ∈ scalars n K := by
    rw [← proj_eq_one_iff, map_pow]
    exact hy
  obtain ⟨w, hw, hw3⟩ := exists_scalar_cube hZ ((scalars n K).inv_mem h1)
  have hwc : Commute w b0 := (Subgroup.mem_center_iff.mp (scalars_le_center n K hw) _).symm
  refine ⟨w * b0, ?_, ?_⟩
  · rw [map_mul, (proj_eq_one_iff.mpr hw), one_mul]
  · rw [hwc.mul_pow, hw3, inv_mul_cancel]

end Lift

section Main

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem fixSub_conj_eq_centralizer {G : Type*} [Group G] (x : G) :
    fixSub (MulAut.conj x) = Subgroup.centralizer ({x} : Set G) := by
  ext y
  rw [mem_fixSub, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    calc y * x = (x * y * x⁻¹) * x := by rw [h]
      _ = x * y := by group
  · intro h
    calc x * y * x⁻¹ = (y * x) * x⁻¹ := by rw [h]
      _ = y := by group

theorem s1431_false_psl (hn : 3 ≤ n) (hpk : (3 : K) ≠ 0)
    (hZ : ∀ z ∈ scalars n K, z ^ 3 = 1 → z = 1)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {A : Subgroup (MulAut (projectiveSL n K))} {ψ : MulAut (projectiveSL n K)}
    {J : Subgroup (projectiveSL n K)} {q : ℕ} (c : S1431Cfg (projectiveSL n K) A ψ J q)
    (hq : 10 ≤ q) (hA : ∀ a ∈ A, IsInnerAut a) : False := by
  classical
  have hinj : Function.Injective
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)) :=
    CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (k := K) hn
  refine c.false_of_induced_inner ?_
  intro η hηA hηψ hstab
  obtain ⟨x, hx⟩ := hA ψ c.mem
  obtain ⟨y, hy⟩ := hA η hηA
  have hψ3 : ψ ^ 3 = 1 := c.elemAbelian.2 ψ c.mem
  have hη3 : η ^ 3 = 1 := c.elemAbelian.2 η hηA
  have hx3 : x ^ 3 = 1 := hinj (by rw [map_pow, hx, hψ3, map_one])
  have hy3 : y ^ 3 = 1 := hinj (by rw [map_pow, hy, hη3, map_one])
  have hxy : x * y = y * x := by
    apply hinj
    rw [map_mul, map_mul, hx, hy]
    have := c.elemAbelian.1.is_comm.comm ⟨ψ, c.mem⟩ ⟨η, hηA⟩
    exact congrArg Subtype.val this
  obtain ⟨a, hax, ha3⟩ := exists_lift_cube hZ hx3
  obtain ⟨b, hby, hb3⟩ := exists_lift_cube hZ hy3
  have hba : b * a = a * b := by
    have h1 : proj n K (b * a * b⁻¹) = proj n K a := by
      rw [map_mul, map_mul, map_inv, hax, hby]
      calc y * x * y⁻¹ = x * y * y⁻¹ := by rw [← hxy]
        _ = x := by group
    have h2 := conj_eq_of_proj_eq_of_scalars hZ ha3 h1
    calc b * a = b * a * b⁻¹ * b := by group
      _ = a * b := by rw [h2]
  set X := Subgroup.centralizer ({proj n K a} : Set (projectiveSL n K)) with hX
  have hψX : fixSub ψ = X := by
    rw [← hx, ← hax, fixSub_conj_eq_centralizer]
  have hJ : GLAPComponent 3 X J := hψX ▸ c.comp
  have hbX : y ∈ X := by
    rw [hX, Subgroup.mem_centralizer_singleton_iff, hax]
    exact hxy.symm ▸ rfl
  let N : PslIdx a → Subgroup (projectiveSL n K) := fun i => pslBlock a i.1.1
  have hNX : ∀ i, N i ≤ X := fun i => pslBlock_le_centralizer i.1.1
  have hNn : ∀ i, ∀ c ∈ X, ∀ m ∈ N i, c * m * c⁻¹ ∈ N i := fun i => pslBlock_normal hZ ha3 i.1.1
  have hNq : ∀ i, CFSG.IsQuasisimple (N i) := fun i => isQuasisimple_pslBlock hpk ha3 i.1.2 i.2
  have hk : ∃ k : ℕ, ∀ x ∈ derivedSeries ↥X k, (x : projectiveSL n K) ∈ ⨆ i, N i :=
    pslBlocks_derived hZ ha3 hpk
  have hb : ∀ i, barX 3 X (N i) = barX 3 X J →
      ∃ m ∈ N i, ∃ c ∈ X, (∀ m' ∈ N i, c * m' = m' * c) ∧ y = m * c := by
    intro i hi
    have hT : IsTypeL2 q ↥(N i) :=
      isTypeL2_of_barX_eq hJ (hNX i) (hNn i) (hNq i) hi.symm c.typeL2
    have hm2 := pslBlock_multiplicity_eq_two hO hpk ha3 i.1.2 i.2 hq hT
    obtain ⟨s, hs, c', hc', hcomm, hbsc⟩ := sl_block_split hpk ha3 i.1.2 hm2 hba hb3
    refine ⟨proj n K s, ⟨s, hs, rfl⟩, proj n K c', ?_, ?_, ?_⟩
    · rw [hX, centralizer_proj_eq_map hZ ha3]
      exact ⟨c', hc', rfl⟩
    · rintro _ ⟨m', hm', rfl⟩
      rw [← map_mul, ← map_mul, hcomm m' hm']
    · rw [← map_mul, ← hbsc, hby]
  obtain ⟨j₀, hj₀, hbj⟩ := exists_inner_of_blocks hJ N hNX hNn hNq hk hbX hb
  subst hy
  exact isInnerAut_inducedBarHom_of_barX hJ hbX hstab hj₀ hbj

end Main

end CFSG.HardMathSupport.Dickson.Sec6.I1431
