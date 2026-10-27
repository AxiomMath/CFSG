module

public import CFSG.RankThree.PartOne.KC.SymplecticMultiplicity
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAlt6
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneBlocks

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCSymplectic
  CFSG.RankThree.PartOne.KCSpFull
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

section Diag

variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W] {m : ℕ}

theorem det_diagEquiv (b : Basis (Fin m) E W) (c : Fin m → Eˣ) :
    LinearMap.det (diagEquiv b c : W →ₗ[E] W) = ∏ i, (c i : E) := by
  classical
  rw [← LinearMap.det_toMatrix b]
  have : LinearMap.toMatrix b b (diagEquiv b c : W →ₗ[E] W) =
      Matrix.diagonal fun i => (c i : E) := by
    ext i j
    rw [LinearMap.toMatrix_apply, LinearEquiv.coe_coe, diagEquiv_apply_basis, map_smul,
      Basis.repr_self, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  rw [this, Matrix.det_diagonal]

theorem exists_diag_pair (b : Basis (Fin m) E W) (hm : 2 ≤ m) {p : ℕ} (hp : p.Prime)
    (lam : Eˣ) (hlam : orderOf lam = p) :
    ∃ c : Fin m → Eˣ, (∀ j, c j ∈ Subgroup.zpowers lam) ∧
      LinearMap.det (diagEquiv b c : W →ₗ[E] W) = 1 ∧ diagEquiv b c ^ p = 1 ∧
        diagEquiv b c ≠ 1 := by
  classical
  set i₀ : Fin m := ⟨0, by omega⟩
  set i₁ : Fin m := ⟨1, by omega⟩
  have hi : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  set c : Fin m → Eˣ := Pi.mulSingle i₀ lam * Pi.mulSingle i₁ lam⁻¹ with hc
  have hlamp : lam ^ p = 1 := by rw [← hlam]; exact pow_orderOf_eq_one lam
  have hlam1 : lam ≠ 1 := fun h => hp.one_lt.ne' (by rw [← hlam, h, orderOf_one])
  have hcz : ∀ j, c j ∈ Subgroup.zpowers lam := by
    intro j
    refine Subgroup.mul_mem _ ?_ ?_
    · by_cases hj : j = i₀
      · rw [hj, Pi.mulSingle_eq_same]
        exact Subgroup.mem_zpowers lam
      · rw [Pi.mulSingle_eq_of_ne hj]
        exact one_mem _
    · by_cases hj : j = i₁
      · rw [hj, Pi.mulSingle_eq_same]
        exact inv_mem (Subgroup.mem_zpowers lam)
      · rw [Pi.mulSingle_eq_of_ne hj]
        exact one_mem _
  refine ⟨c, hcz, ?_, ?_, ?_⟩
  · rw [det_diagEquiv, ← Units.coe_prod, hc]
    simp only [Pi.mul_apply]
    rw [Finset.prod_mul_distrib, Finset.prod_pi_mulSingle', Finset.prod_pi_mulSingle']
    simp
  · have hcp : c ^ p = 1 := by
      funext j
      obtain ⟨k, hk⟩ := hcz j
      rw [Pi.pow_apply, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        hlamp, one_zpow, Pi.one_apply]
    have := (diagHom b).map_pow c p
    change diagEquiv b (c ^ p) = diagEquiv b c ^ p at this
    rw [← this, hcp]
    exact diagEquiv_one b
  · intro h1
    have h2 : c = 1 := diagEquiv_injective b (h1.trans (diagEquiv_one b).symm)
    have h3 := congrFun h2 i₀
    rw [hc, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hi, mul_one,
      Pi.one_apply] at h3
    exact hlam1 h3

end Diag

section Pull

variable {r : ℕ} {K : Type} [Field K]

theorem exists_mem_spPull_of_hom {x : StatedSp r K} {h : K[X]} {F : Subgroup (StatedSp r K)}
    (hF : F ≤ spSupported x {h, reciprocalPolynomial h}) (ψ : F →* blockGL (spEnd x) h)
    (hψ : Function.Injective ψ)
    (hact : ∀ (g : F) (v : Fin r ⊕ Fin r → K) (hv : v ∈ primaryComponent (spEnd x) h),
      blockApply (ψ g) v hv = spEnd (g : StatedSp r K) v)
    {δ : blockGL (spEnd x) h} (hδ : δ ∈ ψ.range)
    (hdet : LinearMap.det (δ : Module.End (AdjoinRoot h) (primaryComponent (spEnd x) h)) = 1)
    {p : ℕ} (hδp : δ ^ p = 1) (hδ1 : δ ≠ 1) :
    ∃ g ∈ spPull x h, g ^ p = 1 ∧ g ≠ 1 := by
  obtain ⟨g, rfl⟩ := hδ
  refine ⟨g, mem_spPull_of_blockGLDet (hF g.2) (ψ g) (hact g) (Units.ext hdet), ?_, ?_⟩
  · have : g ^ p = 1 := hψ (by rw [map_pow, hδp, map_one])
    simpa using congrArg Subtype.val this
  · intro h1
    apply hδ1
    rw [show g = 1 from Subtype.ext h1, map_one]

theorem exists_mem_spPull {ℓ f p : ℕ} (hp : p.Prime) {x : StatedSp r K}
    (blocks : SpPrimaryBlocks ℓ f p x (proj r K x)) (h : primaryFactors (spEnd x))
    (hh1 : (h : K[X]) ≠ X - 1) (hm : 2 ≤ primaryMultiplicity (spEnd x) (h : K[X])) :
    ∃ g ∈ spPull x (h : K[X]), g ^ p = 1 ∧ g ≠ 1 := by
  classical
  obtain ⟨lam, hlam, hlamo⟩ := exists_unit_root (h := h) hp.pos (blocks.nontrivial h h.2 hh1)
  let gl := LinearMap.GeneralLinearGroup.generalLinearEquiv (AdjoinRoot (h : K[X]))
    (primaryComponent (spEnd x) (h : K[X]))
  have hcoe : ∀ δ : primaryComponent (spEnd x) (h : K[X]) ≃ₗ[AdjoinRoot (h : K[X])]
      primaryComponent (spEnd x) (h : K[X]),
      ((gl.symm δ : blockGL (spEnd x) (h : K[X])) :
        Module.End (AdjoinRoot (h : K[X])) (primaryComponent (spEnd x) (h : K[X]))) =
        (δ : Module.End (AdjoinRoot (h : K[X])) (primaryComponent (spEnd x) (h : K[X]))) := by
    intro δ
    conv_rhs => rw [← gl.apply_symm_apply δ]
    rfl
  by_cases hself : reciprocalPolynomial (h : K[X]) = h
  · obtain ⟨d, -, -, σ, -, -, -, hσroot, -, hE, hbar, Hf, -, -, -, ⟨e, he⟩, φ, hφ⟩ :=
      (blocks.selfDual h hh1 hself).exists_half
    obtain ⟨c, hcz, hdet, hpow, hne⟩ := exists_diag_pair e hm hp lam hlamo
    have hσlam : hE.bar (lam : AdjoinRoot (h : K[X])) = (lam : AdjoinRoot (h : K[X]))⁻¹ := by
      rw [hbar, hlam, hσroot]
    have hnorm : ∀ i, hE.bar (c i : AdjoinRoot (h : K[X])) * (c i : AdjoinRoot (h : K[X])) = 1 := by
      intro i
      obtain ⟨k, hk⟩ := hcz i
      rw [← hk, Units.val_zpow_eq_zpow_val, map_zpow₀, hσlam, ← mul_zpow,
        inv_mul_cancel₀ lam.ne_zero, one_zpow]
    have hmem : gl.symm (diagEquiv e c) ∈ sesqUnitaryGroup Hf :=
      mem_sesqUnitaryGroup.2 fun u v => by
        rw [hcoe]
        exact herm_diag e Hf he c hnorm u v
    let ψ : spSupported x {(h : K[X])} →* blockGL (spEnd x) (h : K[X]) :=
      (sesqUnitaryGroup Hf).subtype.comp φ.toMonoidHom
    have hδ : gl.symm (diagEquiv e c) ∈ ψ.range := ⟨φ.symm ⟨_, hmem⟩, by simp [ψ]⟩
    refine exists_mem_spPull_of_hom (F := spSupported x {(h : K[X])}) (fun g hg => by
        rwa [hself, Set.pair_eq_singleton]) ψ (Subtype.val_injective.comp φ.injective)
      (fun g v hv => hφ g v hv) hδ (by rw [hcoe]; exact hdet) ?_ ?_
    · rw [← map_pow, hpow, map_one]
    · intro h1
      exact hne (gl.symm.injective (h1.trans (map_one _).symm))
  · obtain ⟨φ, hφ, -⟩ := (blocks.paired h fun h' => hself h'.symm).factor
    set b := Module.finBasis (AdjoinRoot (h : K[X])) (primaryComponent (spEnd x) (h : K[X]))
    obtain ⟨c, -, hdet, hpow, hne⟩ := exists_diag_pair b hm hp lam hlamo
    have hδ : gl.symm (diagEquiv b c) ∈ φ.toMonoidHom.range :=
      ⟨φ.symm (gl.symm (diagEquiv b c)), by simp⟩
    refine exists_mem_spPull_of_hom le_rfl φ.toMonoidHom φ.injective hφ hδ
      (by rw [hcoe]; exact hdet) ?_ ?_
    · rw [← map_pow, hpow, map_one]
    · intro h1
      exact hne (gl.symm.injective (h1.trans (map_one _).symm))

variable [Finite K]

theorem dvd_card_map_proj (hr : 1 ≤ r) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {L : Subgroup (StatedSp r K)} {g : StatedSp r K} (hg : g ∈ L) (hgp : g ^ p = 1)
    (hg1 : g ≠ 1) : p ∣ Nat.card (L.map (proj r K)) := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : proj r K g ≠ 1 := fun h => hg1 (eq_one_of_proj_eq_one_of_pow_eq_one hr hp2 hp h hgp)
  have h2 : orderOf (proj r K g) = p := orderOf_eq_prime (by rw [← map_pow, hgp, map_one]) h1
  rw [← h2]
  exact Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_map_of_mem _ hg)

theorem dvd_card_spBlockImage {ℓ f p : ℕ} (hr : 1 ≤ r) (hp : p.Prime) (hp2 : p ≠ 2)
    {x : StatedSp r K} (blocks : SpPrimaryBlocks ℓ f p x (proj r K x))
    (h : primaryFactors (spEnd x)) (hh1 : (h : K[X]) ≠ X - 1)
    (hm : 2 ≤ primaryMultiplicity (spEnd x) (h : K[X])) :
    p ∣ Nat.card (spBlockImage x (h : K[X])) := by
  obtain ⟨g, hg, hgp, hg1⟩ := exists_mem_spPull hp blocks h hh1 hm
  rw [spBlockImage_eq]
  exact dvd_card_map_proj hr hp hp2 hg hgp hg1

end Pull

section Fixed

variable {r : ℕ} {K : Type} [Field K]

theorem exists_mem_spFixedFactor {ℓ f p : ℕ} {x y : StatedSp r K}
    (blocks : SpPrimaryBlocks ℓ f p x (proj r K x)) (hxy : y * x = x * y) (hyp : y ^ p = 1)
    {u : Fin r ⊕ Fin r → K} (hu : u ∈ LinearMap.ker (spEnd x - 1)) (hyu : spEnd y u ≠ u) :
    ∃ g ∈ spFixedFactor x, g ^ p = 1 ∧ g ≠ 1 := by
  classical
  have hWk : primaryComponent (spEnd x) (X - 1) = LinearMap.ker (spEnd x - 1) := blocks.fixed_eq
  have hu0 : u ≠ 0 := fun h0 => hyu (by rw [h0, map_zero])
  have huW : u ∈ primaryComponent (spEnd x) (X - 1) := hWk ▸ hu
  have hpos : 0 < spFixedDim x := by
    refine Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨u, huW⟩, fun h0 => hu0 ?_⟩
    exact congrArg Subtype.val h0
  obtain ⟨φ, -⟩ := blocks.fixedFactor (X_sub_one_mem_primaryFactors x hpos)
  have hc : ∀ z : StatedSp r K, z * x = x * z →
      ∀ w ∈ primaryComponent (spEnd x) (X - 1), spEnd z w ∈ primaryComponent (spEnd x) (X - 1) := by
    intro z hz w hw
    rw [hWk] at hw ⊢
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hw ⊢
    have := congrArg (fun g => spEnd g w) hz
    simp only [spEnd_mul, Module.End.mul_apply] at this
    rw [← this, hw]
  have hyinv : y⁻¹ * x = x * y⁻¹ := (Commute.inv_left (show Commute y x from hxy)).eq
  set fy : Module.End K (primaryComponent (spEnd x) (X - 1)) := (spEnd y).restrict (hc y hxy)
    with hfy
  set fyi : Module.End K (primaryComponent (spEnd x) (X - 1)) :=
    (spEnd y⁻¹).restrict (hc y⁻¹ hyinv) with hfyi
  have h1 : fy * fyi = 1 := LinearMap.ext fun w => Subtype.ext (by
    change spEnd y (spEnd y⁻¹ w) = w
    rw [← Module.End.mul_apply, ← spEnd_mul, mul_inv_cancel, spEnd_one, Module.End.one_apply])
  have h2 : fyi * fy = 1 := LinearMap.ext fun w => Subtype.ext (by
    change spEnd y⁻¹ (spEnd y w) = w
    rw [← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one, Module.End.one_apply])
  set δ : LinearMap.GeneralLinearGroup K (primaryComponent (spEnd x) (X - 1)) :=
    ⟨fy, fyi, h1, h2⟩ with hδdef
  have hδ : δ ∈ sesqUnitaryGroup ((spForm r K).restrict (primaryComponent (spEnd x) (X - 1))) :=
    mem_sesqUnitaryGroup.2 fun a b => by
      change spForm r K (spEnd y a) (spEnd y b) = spForm r K a b
      exact mem_sesqUnitaryGroup.mp (spLin_mem y) a b
  have hpow : ∀ (n : ℕ) (w : primaryComponent (spEnd x) (X - 1)),
      (((δ ^ n : LinearMap.GeneralLinearGroup K (primaryComponent (spEnd x) (X - 1))) :
        Module.End K (primaryComponent (spEnd x) (X - 1))) w : Fin r ⊕ Fin r → K) =
        (spEnd y ^ n) w := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [pow_succ, Units.val_mul, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
      rfl
  have hδp : δ ^ p = 1 := by
    refine Units.ext (LinearMap.ext fun w => Subtype.ext ?_)
    rw [hpow, spEnd_pow hyp]
    rfl
  have hδ1 : δ ≠ 1 := by
    intro h0
    apply hyu
    have := congrArg (fun g : LinearMap.GeneralLinearGroup K (primaryComponent (spEnd x) (X - 1)) =>
      (((g : Module.End K (primaryComponent (spEnd x) (X - 1))) ⟨u, huW⟩ :
        primaryComponent (spEnd x) (X - 1)) : Fin r ⊕ Fin r → K)) h0
    exact this
  refine ⟨φ.symm ⟨δ, hδ⟩, (φ.symm ⟨δ, hδ⟩).2, ?_, ?_⟩
  · have : (φ.symm ⟨δ, hδ⟩) ^ p = 1 := by
      rw [← map_pow]
      have : (⟨δ, hδ⟩ : sesqUnitaryGroup ((spForm r K).restrict
          (primaryComponent (spEnd x) (X - 1)))) ^ p = 1 := Subtype.ext (by simpa using hδp)
      rw [this, map_one]
    simpa using congrArg Subtype.val this
  · intro h0
    have h3 : (φ.symm ⟨δ, hδ⟩) = 1 := Subtype.ext h0
    rw [MulEquiv.symm_apply_eq, map_one] at h3
    exact hδ1 (congrArg Subtype.val h3)

variable [Finite K]

theorem dvd_card_spFixedLayerImage {ℓ f p : ℕ} (hr : 1 ≤ r) (hp : p.Prime) (hp2 : p ≠ 2)
    {x y : StatedSp r K} (blocks : SpPrimaryBlocks ℓ f p x (proj r K x))
    (hlisted : SpFixedListed x) (hxy : y * x = x * y) (hyp : y ^ p = 1)
    {u : Fin r ⊕ Fin r → K} (hu : u ∈ LinearMap.ker (spEnd x - 1)) (hyu : spEnd y u ≠ u) :
    p ∣ Nat.card (spFixedLayerImage x) := by
  classical
  obtain ⟨g, hg, hgp, hg1⟩ := exists_mem_spFixedFactor blocks hxy hyp hu hyu
  by_cases h42 : spFixedDim x = 4 ∧ Nat.card K = 2
  · have himg : spFixedLayerImage x = (⁅spFixedFactor x, spFixedFactor x⁆).map (proj r K) := by
      simp [spFixedLayerImage, hlisted, h42.1, h42.2]
    rw [himg]
    exact dvd_card_map_proj hr hp hp2 ((spFixed_four_two h42.2 blocks h42.1).2 hp hp2 g hg hgp)
      hgp hg1
  · have himg : spFixedLayerImage x = (spFixedFactor x).map (proj r K) := by
      simp [spFixedLayerImage, hlisted, h42]
    rw [himg]
    exact dvd_card_map_proj hr hp hp2 hg hgp hg1

end Fixed

end CFSG.HardMathSupport.Timmesfeld.CrossChar
