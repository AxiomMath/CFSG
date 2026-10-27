module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.GroupTheory.SteinbergCDCyclicNormalHall
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.RankThree.PartOne.KE.E6TwThreeLayer
public import CFSG.RankThree.PartOne.KE.OrdinaryEPointwise

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwE6Three

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.KE
open CFSG.RankThree.E6
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Lattice
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2
open scoped Pointwise commutatorElement Matrix MatrixGroups

set_option linter.unusedSectionVars false


variable {ℓ f : ℕ} {K : Type} [Field K] {σ : K ≃+* K} {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] {Fr : Ω →+* Ω} {g : ModGL Tag.E6 Ω}

private theorem phi3_A2_frame (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1)
    {x : ModGL Tag.E6 Ω} (hx : x ∈ phi3Torus Ω Fr) (hxp : orderOf x = p)
    (hA2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 support13) :
    ∃ w : WeylGroup Tag.E6,
      (rootSpan Tag.E6 Ω (torusRootKernel x)).map
          (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
        subsystemGroup Tag.E6 Ω support13 ∧
      ⁅rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr,
          rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr⁆ =
        rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr ∧
      ∃ H : SL(3, Ω), ∀ Y : SL(3, fixSubfield σ),
        ∃ y ∈ rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr,
          a2Mat₁ (canonicalRep (coxeterSystem Tag.E6) Ω w * y *
              (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹) =
            ((H * Matrix.SpecialLinearGroup.map
                ((algebraMap K Ω).comp (fixSubfield σ).subtype) Y * H⁻¹ : SL(3, Ω)) :
              Matrix (Fin 3) (Fin 3) Ω) := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
  obtain ⟨-, ⟨ζ, hζ⟩, hr⟩ := phi3_prime_setup (Ω := Ω) hf hp hpq
  have hxp' : x ^ p = 1 := hxp ▸ pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hxp
    exact hp.one_lt.ne hxp
  have hxT : x ∈ phi3TorusTorsion Ω Fr p := ⟨hx, hxp'⟩
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos f)
    exact ⟨z, by rw [hFr, hz]⟩
  obtain ⟨w, hQ₁, π, hθ⟩ := phi3_A2_transport hp3 hFr hζ hr hxT hx1 hA2
  obtain ⟨hmaps, Φ, hΦ₀, b, hΦt⟩ := exists_sl3_root_permuting_of_theta hFrs
    (phi3ThetaConj Ω Fr w) (phi3ThetaConj_injective w) π hθ
  obtain ⟨e, he⟩ := exists_mulEquiv_fixSubgroup hQ₁ hmaps Φ hΦ₀
  have : Module.Finite (fixSubfield σ) K := Module.Finite.of_finite
  have : Algebra.IsAlgebraic (fixSubfield σ) K := Algebra.IsAlgebraic.of_finite _ K
  have : IsAlgClosure (fixSubfield σ) Ω := IsAlgClosure.ofAlgebraic (fixSubfield σ) K Ω
  have hk : fixSubfield σ = RingHom.eqLocusField (σ : K →+* K) (RingHom.id K) := by
    ext c
    rw [mem_fixSubfield, RingHom.mem_eqLocusField, RingHom.id_apply]
    rfl
  have hkcard : Nat.card (fixSubfield σ) = ℓ ^ f := by
    rw [hk]
    exact natCard_eqLocusField hℓ hf hK hσ
  obtain ⟨-, ⟨H, hH⟩, -, hqsΦ, -, -⟩ := sln_root_permuting_frobenius_fixed_split hℓ hf
    hkcard (le_refl 3) π Φ b (fun i j hij t => by rw [hΦt, hFr])
  have hqsP := CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv e.symm hqsΦ
  have : Group.IsPerfect ↥(rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr) :=
    hqsP.1
  refine ⟨w, hQ₁, Subgroup.commutator_eq_self, H, fun Y => ?_⟩
  have hX := (hH (H * Matrix.SpecialLinearGroup.map (algebraMap (fixSubfield σ) Ω) Y * H⁻¹)).2
    ⟨Y, rfl⟩
  refine ⟨e.symm ⟨_, hX⟩, (e.symm ⟨_, hX⟩).2, ?_⟩
  have h1 := he (e.symm ⟨_, hX⟩)
  rw [MulEquiv.apply_symm_apply] at h1
  exact h1.symm

theorem phi3_A2_exists_rootSL2 (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = canonicalRep (coxeterSystem Tag.E6) Ω phi3V)
    {x : ModGL Tag.E6 Ω} (hx : x ∈ phi3TStar K σ Ω Fr g) (hxp : orderOf x = p)
    (hA2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 support13) :
    ∃ h ∈ adjointGroup Tag.E6 Ω, ∀ B : SL2 (fixSubfield σ),
      h * simpleRootSL2 Tag.E6 Ω (e6Index 0)
        (Matrix.SpecialLinearGroup.map ((algebraMap K Ω).comp (fixSubfield σ).subtype) B) *
          h⁻¹ ∈ rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr := by
  classical
  obtain ⟨w, hQ₁, -, H, hY⟩ := phi3_A2_frame hℓ hf hK hσ hFr hp hp3 hpq hx.1 hxp hA2
  set n := canonicalRep (coxeterSystem Tag.E6) Ω w with hn
  set ι : fixSubfield σ →+* Ω := (algebraMap K Ω).comp (fixSubfield σ).subtype with hι
  set H₁ : subsystemGroup Tag.E6 Ω support13 := (a2Equiv₁ Ω).symm H with hH₁
  have hH₁' : a2Equiv₁ Ω H₁ = H := MulEquiv.apply_symm_apply _ _
  have hkey : ∀ (Y : SL(3, fixSubfield σ)) (z : subsystemGroup Tag.E6 Ω support13),
      a2Mat₁ (z : ModGL Tag.E6 Ω) =
          ((Matrix.SpecialLinearGroup.map ι Y : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) →
        (n⁻¹ * (H₁ : ModGL Tag.E6 Ω)) * z * (n⁻¹ * (H₁ : ModGL Tag.E6 Ω))⁻¹ ∈
          rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr := by
    intro Y z hz
    obtain ⟨y, hyQ, hy⟩ := hY Y
    have hny : n * y * n⁻¹ ∈ subsystemGroup Tag.E6 Ω support13 := by
      rw [← hQ₁]
      exact ⟨y, hyQ.1, rfl⟩
    have hz' : a2Equiv₁ Ω z = Matrix.SpecialLinearGroup.map ι Y :=
      Subtype.ext (by rw [a2Equiv₁_apply, coe_a2Rep₁]; exact hz)
    have h1 : a2Equiv₁ Ω ⟨n * y * n⁻¹, hny⟩ = a2Equiv₁ Ω (H₁ * z * H₁⁻¹) := by
      rw [map_mul, map_mul, map_inv, hH₁', hz']
      exact Subtype.ext (by rw [a2Equiv₁_apply, coe_a2Rep₁]; exact hy)
    have h2 : n * y * n⁻¹ = (H₁ : ModGL Tag.E6 Ω) * z * (H₁ : ModGL Tag.E6 Ω)⁻¹ :=
      congrArg Subtype.val ((a2Equiv₁ Ω).injective h1)
    have h3 : y = (n⁻¹ * (H₁ : ModGL Tag.E6 Ω)) * z * (n⁻¹ * (H₁ : ModGL Tag.E6 Ω))⁻¹ := by
      calc y = n⁻¹ * (n * y * n⁻¹) * n := by group
        _ = _ := by rw [h2]; group
    rw [← h3]
    exact hyQ
  have hQ₁le : subsystemGroup Tag.E6 Ω support13 ≤ adjointGroup Tag.E6 Ω :=
    (Subgroup.closure_le _).2 fun _ ⟨i, _, c, h⟩ => by
      rcases h with rfl | rfl
      exacts [xUnit_mem_adjointGroup i c, yUnit_mem_adjointGroup i c]
  refine ⟨n⁻¹ * (H₁ : ModGL Tag.E6 Ω),
    mul_mem (inv_mem (canonicalRep_mem_adjointGroup _ Ω w)) (hQ₁le H₁.2), fun B => ?_⟩
  set ψ : SL2 (fixSubfield σ) →* ModGL Tag.E6 Ω :=
    ((MulAut.conj (n⁻¹ * (H₁ : ModGL Tag.E6 Ω))).toMonoidHom.comp
      (simpleRootSL2 Tag.E6 Ω (e6Index 0))).comp (Matrix.SpecialLinearGroup.map ι) with hψ
  have hB : B ∈ (⊤ : Subgroup (SL2 (fixSubfield σ))) := Subgroup.mem_top B
  rw [← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower] at hB
  refine (Subgroup.closure_le
    ((rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr).comap ψ)).2 ?_ hB
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · have hu : Matrix.SpecialLinearGroup.map ι
        (CFSG.LocalAnalysis.ComponentInitial.sl2Upper (fixSubfield σ) c) = uSL (ι c) := by
      ext i j
      rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
      fin_cases i <;> fin_cases j <;> simp [CFSG.LocalAnalysis.ComponentInitial.sl2Upper, uSL]
    have hmem := hkey (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c)
      ⟨_, xUnit_mem_subsystemGroup e6Index_0_mem_support13 (ι c)⟩ (by
        rw [Matrix.SpecialLinearGroup.map_transvection]
        exact a2Mat₁_x1 _)
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    rw [hψ, MonoidHom.comp_apply, hu, MonoidHom.comp_apply, simpleRootSL2_uSL]
    exact hmem
  · have hv : Matrix.SpecialLinearGroup.map ι
        (CFSG.LocalAnalysis.ComponentInitial.sl2Lower (fixSubfield σ) c) = vSL (ι c) := by
      ext i j
      rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
      fin_cases i <;> fin_cases j <;> simp [CFSG.LocalAnalysis.ComponentInitial.sl2Lower, vSL]
    have hmem := hkey (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c)
      ⟨_, yUnit_mem_subsystemGroup e6Index_0_mem_support13 (ι c)⟩ (by
        rw [Matrix.SpecialLinearGroup.map_transvection]
        exact a2Mat₁_y1 _)
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    rw [hψ, MonoidHom.comp_apply, hv, MonoidHom.comp_apply, simpleRootSL2_vSL]
    exact hmem

theorem phi3_A2_commute_roots (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = canonicalRep (coxeterSystem Tag.E6) Ω phi3V)
    {x : ModGL Tag.E6 Ω} (hx : x ∈ phi3TStar K σ Ω Fr g) (hxp : orderOf x = p)
    (hA2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 support13)
    {h : ModGL Tag.E6 Ω} (hh : h ∈ torusGroup Tag.E6 Ω)
    (hc : ∀ u ∈ ⁅rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr,
      rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr⁆, h * u = u * h) :
    ∀ α ∈ torusRootKernel x, ∀ c : Ω, h * pinnedX Tag.E6 Ω α c = pinnedX Tag.E6 Ω α c * h := by
  classical
  obtain ⟨w, hQ₁, hPP, H, hY⟩ := phi3_A2_frame hℓ hf hK hσ hFr hp hp3 hpq hx.1 hxp hA2
  rw [hPP] at hc
  set n := canonicalRep (coxeterSystem Tag.E6) Ω w with hn
  have hnN := canonicalRep_mem_normalizer (R := Ω) w
  have hh' : n * h * n⁻¹ ∈ torusGroup Tag.E6 Ω := (Subgroup.mem_normalizer_iff.1 hnN h).1 hh
  obtain ⟨χ, hχ, -⟩ := exists_simple_root_characters hh'
  set s₀ := χ (e6Index 0)
  set t₀ := χ (e6Index 2)
  have hkey : ∀ (i j : Fin 3) (hij : i ≠ j),
      diagonal ![((s₀ * t₀ : Ωˣ) : Ω), (t₀ : Ω), 1] *
          ((H * Matrix.SpecialLinearGroup.transvection hij 1 * H⁻¹ : SL(3, Ω)) :
            Matrix (Fin 3) (Fin 3) Ω) =
        ((H * Matrix.SpecialLinearGroup.transvection hij 1 * H⁻¹ : SL(3, Ω)) :
            Matrix (Fin 3) (Fin 3) Ω) * diagonal ![((s₀ * t₀ : Ωˣ) : Ω), (t₀ : Ω), 1] := by
    intro i j hij
    obtain ⟨y, hyQ, hy⟩ := hY (Matrix.SpecialLinearGroup.transvection hij 1)
    rw [Matrix.SpecialLinearGroup.map_transvection, map_one] at hy
    have hyQ₁ : n * y * n⁻¹ ∈ subsystemGroup Tag.E6 Ω support13 := by
      rw [← hQ₁]
      exact ⟨y, hyQ.1, rfl⟩
    have hc0 : h * y = y * h := hc y hyQ
    have hc1 : (n * h * n⁻¹) * 1 * (n * y * n⁻¹) = (n * y * n⁻¹) * ((n * h * n⁻¹) * 1) := by
      calc (n * h * n⁻¹) * 1 * (n * y * n⁻¹) = n * (h * y) * n⁻¹ := by group
        _ = n * (y * h) * n⁻¹ := by rw [hc0]
        _ = (n * y * n⁻¹) * ((n * h * n⁻¹) * 1) := by group
    have h2 := diagonal_mul_a2Mat₁_comm hh' (hχ (e6Index 0)) (hχ (e6Index 2)) (one_mem _) hyQ₁
      hc1
    rwa [a2Mat₁_one, Matrix.mul_one, hy] at h2
  have hD₁ : diagonal ![((s₀ * t₀ : Ωˣ) : Ω), (t₀ : Ω), 1] *
      diagonal ![(((s₀ * t₀)⁻¹ : Ωˣ) : Ω), ((t₀⁻¹ : Ωˣ) : Ω), 1] = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    fin_cases k <;> first | (simp; done) | (simp; field_simp)
  have hD₂ : diagonal ![(((s₀ * t₀)⁻¹ : Ωˣ) : Ω), ((t₀⁻¹ : Ωˣ) : Ω), 1] *
      diagonal ![((s₀ * t₀ : Ωˣ) : Ω), (t₀ : Ω), 1] = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    fin_cases k <;> first | (simp; done) | (simp; field_simp)
  let Dg : GL (Fin 3) Ω := ⟨_, _, hD₁, hD₂⟩
  obtain ⟨c₀, hc₀⟩ := exists_eq_scalar_of_commute_conj Dg (Matrix.SpecialLinearGroup.toGL H)
    fun i j hij => by
      rw [← map_inv, ← map_mul, ← map_mul]
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
      exact hkey i j hij
  have e0 := congrFun (congrFun hc₀ 0) 0
  have e1 := congrFun (congrFun hc₀ 1) 1
  have e2 := congrFun (congrFun hc₀ 2) 2
  simp [Dg] at e0 e1 e2
  have ht₀ : t₀ = 1 := Units.ext (by rw [Units.val_one, e1, ← e2])
  have hs₀ : s₀ = 1 := Units.ext (by
    have e0' : (s₀ : Ω) * t₀ = c₀ := e0
    rw [ht₀, Units.val_one, mul_one, ← e2] at e0'
    rw [Units.val_one, e0'])
  have hfix : ∀ z ∈ subsystemGroup Tag.E6 Ω support13,
      (n * h * n⁻¹) * z * (n * h * n⁻¹)⁻¹ = z := by
    intro z hz
    obtain ⟨hmem, hmat⟩ := a2Mat₁_conj_torus hh' (hχ (e6Index 0)) (hχ (e6Index 2)) hz
    have hd1 : diagonal ![((s₀ * t₀ : Ωˣ) : Ω), (t₀ : Ω), 1] = 1 := by
      rw [hs₀, ht₀, ← diagonal_one]
      congr 1
      funext k
      fin_cases k <;> simp
    have hd2 : diagonal ![(((s₀ * t₀)⁻¹ : Ωˣ) : Ω), ((t₀⁻¹ : Ωˣ) : Ω), 1] = 1 := by
      rw [hs₀, ht₀, ← diagonal_one]
      congr 1
      funext k
      fin_cases k <;> simp
    rw [hd1, hd2, Matrix.one_mul, Matrix.mul_one] at hmat
    have heq : (⟨_, hmem⟩ : subsystemGroup Tag.E6 Ω support13) = ⟨z, hz⟩ :=
      a2Rep₁_injective (Subtype.ext (by rw [coe_a2Rep₁, coe_a2Rep₁]; exact hmat))
    exact congrArg Subtype.val heq
  intro α hα c
  have hX : n * pinnedX Tag.E6 Ω α c * n⁻¹ ∈ subsystemGroup Tag.E6 Ω support13 := by
    rw [← hQ₁]
    exact ⟨_, pinnedX_mem_rootSpan hα c, rfl⟩
  have h1 := hfix _ hX
  have h2 : h * pinnedX Tag.E6 Ω α c * h⁻¹ = pinnedX Tag.E6 Ω α c :=
    calc h * pinnedX Tag.E6 Ω α c * h⁻¹ =
        n⁻¹ * ((n * h * n⁻¹) * (n * pinnedX Tag.E6 Ω α c * n⁻¹) * (n * h * n⁻¹)⁻¹) * n := by
          group
      _ = n⁻¹ * (n * pinnedX Tag.E6 Ω α c * n⁻¹) * n := by rw [h1]
      _ = pinnedX Tag.E6 Ω α c := by group
  calc h * pinnedX Tag.E6 Ω α c = (h * pinnedX Tag.E6 Ω α c * h⁻¹) * h := by group
    _ = pinnedX Tag.E6 Ω α c * h := by rw [h2]

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwE6Three
