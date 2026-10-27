module

public import CFSG.RankThree.PartOne.KE.E6TwFourData
public import CFSG.RankThree.GroupTheory.SteinbergCDCyclicNormalHall
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.KE
open CFSG.RankThree.E6 (charVal charVal_smul charVal_single)
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (weylMatrix e6Index dualMatrix e6Rho)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise commutatorElement Matrix MatrixGroups

theorem e6Four_coe_map_transvection_one {k L : Type} [Field k] [Field L] (φ : k →+* L) {i j : Fin 4}
    (hij : i ≠ j) :
    ((Matrix.SpecialLinearGroup.map φ (Matrix.SpecialLinearGroup.transvection hij (1 : k)) :
      SL(4, L)) : Matrix (Fin 4) (Fin 4) L) = 1 + Matrix.single i j 1 := by
  rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.transvection_coe]
  ext a b
  by_cases hab : a = b <;> by_cases hi : a = i <;> by_cases hj : b = j <;>
    simp [RingHom.mapMatrix_apply, Matrix.single_apply, hab, hi, hj, Matrix.one_apply]

theorem e6_tw_four_coordinates {ℓ f : ℕ} [Fact ℓ.Prime] (K : Type) [Field K] [Finite K]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hord : orderOf ((ℓ ^ f : ℕ) : ZMod p) = 4) (hΦ : ((ℓ ^ f : ℕ) : ZMod p) ^ 2 + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL Tag.E6 L) (hnm : n ∈ monomialSubgroup Tag.E6 L)
    (hnW : ∀ x, weylQuotientHom Tag.E6 L ⟨n, hnm⟩ • x = e6SM (-1) *ᵥ permLattice e6Rho x)
    (g0 : ModGL Tag.E6 L) (hg0C : g0 ∈ adjointGroup Tag.E6 L)
    (hg0 : twistE6 (iterateFrobenius L ℓ f) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL Tag.E6 L), Finite P → P ≤ adjointGroup Tag.E6 L →
      (∀ x ∈ P, twistE6 (iterateFrobenius L ℓ f) x = x) → ⁅P, P⁆ = P →
        P ≤ (twE6Emb K σ L).range)
    (hT : twistedTorusOf n (twistE6 (iterateFrobenius L ℓ f)) =
      (fixedCharTuples (e6SM (-1)) (iterateFrobenius L ℓ f)).map (rootDiagUnitHom Tag.E6 L))
    {x : twistedE6RootGroup K σ} (hx : orderOf x = p) (c : twistedE6RootGroup K σ)
    (hh : g0⁻¹ * twE6Emb K σ L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n (twistE6 (iterateFrobenius L ℓ f)))
    {b : Fin Tag.E6.rank → Lˣ}
    (hb : rootDiagUnit Tag.E6 b = g0⁻¹ * twE6Emb K σ L (c * x * c⁻¹) * g0)
    (hne : (rootCharKernel b).Nonempty)
    (m : ModGL Tag.E6 L) (hmadj : m ∈ adjointGroup Tag.E6 L)
    (hmx : m * twE6Emb K σ L x * m⁻¹ = twE6Emb K σ L x)
    (hmD : ∀ d ∈ (⁅Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ)),
      Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))⁆ :
        Subgroup (twistedE6RootGroup K σ)), m * twE6Emb K σ L d * m⁻¹ = twE6Emb K σ L d) :
    ∃ a' : Fin Tag.E6.rank → Lˣ,
      rootDiagUnit Tag.E6 a' = g0⁻¹ * twE6Emb K σ L c * m * (twE6Emb K σ L c)⁻¹ * g0 ∧
        ∀ α ∈ rootCharKernel b, rootChar a' α = 1 := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hinj0 : Function.Injective (rootDiagUnitHom Tag.E6 L) := rootDiagUnit_injective
  obtain ⟨ψ, hψinj, hψ, hψb⟩ := e6_tw_four_perx K hf hK σ hσ hp hp3 hord hΦ L n hnm hnW g0 hg0C
    hg0 hperf hT hx c hh
  obtain ⟨-, hψne⟩ := hψb b hb
  obtain ⟨Pt, hPq, hcomm, ⟨h₀, hh₀⟩, v, hSeq, H, hH⟩ := hψne hne
  obtain ⟨hq, h2, h1⟩ := isQuasisimple_commutator_of_embedding ψ hψinj hPq hcomm
  set ι : twistedE6RootGroup K σ →* ModGL Tag.E6 L := twE6Emb K σ L with hιdef
  set φ : fixSubfield σ →+* L := (algebraMap K L).comp (fixSubfield σ).subtype with hφdef
  set m' : ModGL Tag.E6 L := g0⁻¹ * ι c * m * (ι c)⁻¹ * g0 with hm'
  have hm'adj : m' ∈ adjointGroup Tag.E6 L :=
    mul_mem (mul_mem (mul_mem (mul_mem (inv_mem hg0C) (twE6Emb_mem c)) hmadj)
      (inv_mem (twE6Emb_mem c))) hg0C
  have hfixψ : ∀ d : twistedE6RootGroup K σ, m * ι d * m⁻¹ = ι d →
      m' * (g0⁻¹ * ι (c * d * c⁻¹) * g0) * m'⁻¹ = g0⁻¹ * ι (c * d * c⁻¹) * g0 := by
    intro d hd
    have e : m' * (g0⁻¹ * ι (c * d * c⁻¹) * g0) * m'⁻¹ =
        g0⁻¹ * ι c * (m * ι d * m⁻¹) * (ι c)⁻¹ * g0 := by
      rw [hm']
      simp only [map_mul, map_inv]
      group
    rw [e, hd]
    simp only [map_mul, map_inv]
    group
  have hbfix : b ∈ fixedCharTuples (e6SM (-1)) Fr := by
    have hh' := hh
    rw [hT] at hh'
    obtain ⟨a', ha', haa⟩ := hh'
    have : a' = b := hinj0 (haa.trans hb.symm)
    exact this ▸ ha'
  have hbp : orderOf (rootDiagUnit Tag.E6 b) = p := by
    rw [hb]
    have e1 : orderOf (g0⁻¹ * ι (c * x * c⁻¹) * g0) = orderOf (ι (c * x * c⁻¹)) := by
      have := orderOf_injective (MulAut.conj g0⁻¹).toMonoidHom (MulAut.conj g0⁻¹).injective
        (ι (c * x * c⁻¹))
      simpa [MulAut.conj_apply] using this
    have e2 : orderOf (ι (c * x * c⁻¹)) = orderOf (c * x * c⁻¹) :=
      orderOf_injective _ twE6Emb_injective _
    have e3 : orderOf (c * x * c⁻¹) = orderOf x := by
      have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
      simpa [MulAut.conj_apply] using this
    rw [e1, e2, e3, hx]
  have hbap := pow_eq_one_of_orderOf_rootDiagUnit hbp
  have hb1 := ne_one_of_orderOf_rootDiagUnit hp hbp
  have hstabb := e6TwFour_stab_of_fixed Fr hFr hp hp3 hord hΦ hbfix hbap hb1
  have hCent : ∀ y ∈ adjointGroup Tag.E6 L, y * rootDiagUnit Tag.E6 b = rootDiagUnit Tag.E6 b * y →
      y ∈ (torusGroup Tag.E6 L : Set (ModGL Tag.E6 L)) *
        (rootSpan Tag.E6 L (sigmaSetE6A3 v) : Set (ModGL Tag.E6 L)) := fun y hy hcomm' =>
    mem_torus_mul_rootSpan_of_commute_of_stab hstabb (sigmaSetE6A3_isRoot v)
      (sigmaSetE6A3_neg v) (by rw [hSeq]) hy hcomm'
  have hfixh : m' * rootDiagUnit Tag.E6 b * m'⁻¹ = rootDiagUnit Tag.E6 b := by
    rw [hb]
    exact hfixψ x hmx
  have hcommb : m' * rootDiagUnit Tag.E6 b = rootDiagUnit Tag.E6 b * m' :=
    mul_inv_eq_iff_eq_mul.1 hfixh
  obtain ⟨t, ht, s, hs, hts⟩ := Set.mem_mul.1 (hCent m' hm'adj hcommb)
  have hs' : s ∈ (rhoSigmaE6A3 L v).range := by
    rw [rhoSigmaE6A3_range]
    exact hs
  obtain ⟨S, rfl⟩ := hs'
  obtain ⟨b0, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hρinj : Function.Injective (rhoSigmaE6A3 L v) := rhoSigmaE6A3_injective v
  set d : Fin 4 → Lˣ := fun i => rootChar b0 (wbE6A3 v i) with hd
  have hconj : ∀ A : SL(4, L), (rootDiagUnit Tag.E6 b0 * rhoSigmaE6A3 L v S) * rhoSigmaE6A3 L v A *
      (rootDiagUnit Tag.E6 b0 * rhoSigmaE6A3 L v S)⁻¹ =
        rhoSigmaE6A3 L v (conjDiagn d (S * A * S⁻¹)) := by
    intro A
    rw [← rhoSigmaE6A3_torus v b0 (S * A * S⁻¹)]
    simp only [map_mul, map_inv, _root_.mul_inv_rev]
    group
  have hfixρ : ∀ Y : SL(4, fixSubfield σ),
      m' * rhoSigmaE6A3 L v (H * Matrix.SpecialLinearGroup.map φ Y * H⁻¹) * m'⁻¹ =
        rhoSigmaE6A3 L v (H * Matrix.SpecialLinearGroup.map φ Y * H⁻¹) := by
    intro Y
    have hmem := hH Y
    rw [← h2] at hmem
    obtain ⟨d', hd', hd'ψ⟩ := hmem
    have hd'D : ((d' : Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))) :
        twistedE6RootGroup K σ) ∈ (⁅Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ)),
          Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))⁆ :
            Subgroup (twistedE6RootGroup K σ)) := by
      rw [← h1]
      exact ⟨d', hd', rfl⟩
    rw [← hd'ψ, hψ d']
    exact hfixψ _ (hmD _ hd'D)
  have key : ∀ Y : SL(4, fixSubfield σ),
      conjDiagn d (S * (H * Matrix.SpecialLinearGroup.map φ Y * H⁻¹) * S⁻¹) =
        H * Matrix.SpecialLinearGroup.map φ Y * H⁻¹ := by
    intro Y
    apply hρinj
    rw [← hconj, hts]
    exact hfixρ Y
  have htoGL_conj : ∀ A : SL(4, L), Matrix.SpecialLinearGroup.toGL (conjDiagn d A) =
      diagGLn d * Matrix.SpecialLinearGroup.toGL A * (diagGLn d)⁻¹ := fun A =>
    Units.ext (coe_conjDiagn d A)
  set W : GL (Fin 4) L := diagGLn d * Matrix.SpecialLinearGroup.toGL S with hW
  have hWcomm : ∀ Y : SL(4, fixSubfield σ),
      W * (Matrix.SpecialLinearGroup.toGL H * Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.map φ Y) * (Matrix.SpecialLinearGroup.toGL H)⁻¹) * W⁻¹ =
        Matrix.SpecialLinearGroup.toGL H * Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.map φ Y) * (Matrix.SpecialLinearGroup.toGL H)⁻¹ := by
    intro Y
    have h3 := congrArg Matrix.SpecialLinearGroup.toGL (key Y)
    simp only [htoGL_conj, map_mul, map_inv] at h3
    rw [hW]
    simpa [mul_assoc] using h3
  have hW' : (Matrix.SpecialLinearGroup.toGL H)⁻¹ * W * Matrix.SpecialLinearGroup.toGL H ∈
      (Matrix.GeneralLinearGroup.scalar (Fin 4) : Lˣ →* GL (Fin 4) L).range := by
    refine CFSG.RankThree.Classical.mem_range_scalar_of_commute_elementary _ fun i j hij => ?_
    have h4 := hWcomm (Matrix.SpecialLinearGroup.transvection hij (1 : fixSubfield σ))
    have h5 : W * (Matrix.SpecialLinearGroup.toGL H * Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.map φ (Matrix.SpecialLinearGroup.transvection hij
            (1 : fixSubfield σ))) * (Matrix.SpecialLinearGroup.toGL H)⁻¹) =
        (Matrix.SpecialLinearGroup.toGL H * Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.map φ (Matrix.SpecialLinearGroup.transvection hij
            (1 : fixSubfield σ))) * (Matrix.SpecialLinearGroup.toGL H)⁻¹) * W := by
      calc _ = (W * (Matrix.SpecialLinearGroup.toGL H * Matrix.SpecialLinearGroup.toGL
            (Matrix.SpecialLinearGroup.map φ (Matrix.SpecialLinearGroup.transvection hij
              (1 : fixSubfield σ))) * (Matrix.SpecialLinearGroup.toGL H)⁻¹) * W⁻¹) * W := by
            group
        _ = _ := by rw [h4]
    set T : GL (Fin 4) L := Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.map φ (Matrix.SpecialLinearGroup.transvection hij
        (1 : fixSubfield σ))) with hT'
    have h6 : T * ((Matrix.SpecialLinearGroup.toGL H)⁻¹ * W * Matrix.SpecialLinearGroup.toGL H) =
        ((Matrix.SpecialLinearGroup.toGL H)⁻¹ * W * Matrix.SpecialLinearGroup.toGL H) * T := by
      calc _ = (Matrix.SpecialLinearGroup.toGL H)⁻¹ * ((Matrix.SpecialLinearGroup.toGL H * T *
              (Matrix.SpecialLinearGroup.toGL H)⁻¹) * W) * Matrix.SpecialLinearGroup.toGL H := by
            group
        _ = (Matrix.SpecialLinearGroup.toGL H)⁻¹ * (W * (Matrix.SpecialLinearGroup.toGL H * T *
              (Matrix.SpecialLinearGroup.toGL H)⁻¹)) * Matrix.SpecialLinearGroup.toGL H := by
            rw [h5]
        _ = _ := by group
    have hTm : (T : Matrix (Fin 4) (Fin 4) L) = 1 + Matrix.single i j 1 :=
      e6Four_coe_map_transvection_one φ hij
    have := congrArg (fun g : GL (Fin 4) L => (g : Matrix (Fin 4) (Fin 4) L)) h6
    simpa [hTm] using this
  obtain ⟨lam, hlam⟩ := hW'
  have hWsc : W = Matrix.GeneralLinearGroup.scalar (Fin 4) lam := by
    have e : W = Matrix.SpecialLinearGroup.toGL H * ((Matrix.SpecialLinearGroup.toGL H)⁻¹ * W *
        Matrix.SpecialLinearGroup.toGL H) * (Matrix.SpecialLinearGroup.toGL H)⁻¹ := by group
    rw [e, ← hlam, ← Matrix.GeneralLinearGroup.scalar_commute lam]
    group
  have hSdiag : ∀ i j : Fin 4, i ≠ j → (S : Matrix (Fin 4) (Fin 4) L) i j = 0 := by
    intro i j hij
    have h := congrArg (fun g : GL (Fin 4) L => ((g : Matrix (Fin 4) (Fin 4) L)) i j) hWsc
    simp only [hW, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at h
    simp [diagGLn, Matrix.diagonal_mul, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij] at h
    exact h
  have hsT : rhoSigmaE6A3 L v S ∈ torusGroup Tag.E6 L := rhoSigmaE6A3_diagonal v S hSdiag
  have hm'T : m' ∈ torusGroup Tag.E6 L := by
    rw [← hts]
    exact mul_mem (rootDiagUnit_mem_torusGroup b0) hsT
  have hall : ∀ A : SL(4, L), m' * rhoSigmaE6A3 L v A * m'⁻¹ = rhoSigmaE6A3 L v A := by
    intro A
    rw [← hts, hconj A]
    congr 1
    have e : Matrix.SpecialLinearGroup.toGL (conjDiagn d (S * A * S⁻¹)) =
        Matrix.SpecialLinearGroup.toGL A := by
      rw [htoGL_conj]
      have e1 : diagGLn d * Matrix.SpecialLinearGroup.toGL (S * A * S⁻¹) * (diagGLn d)⁻¹ =
          W * Matrix.SpecialLinearGroup.toGL A * W⁻¹ := by
        rw [hW]
        simp only [map_mul, map_inv]
        group
      rw [e1, hWsc, Matrix.GeneralLinearGroup.scalar_commute lam]
      group
    exact Subtype.ext (congrArg (fun g : GL (Fin 4) L => (g : Matrix (Fin 4) (Fin 4) L)) e)
  obtain ⟨a', ha'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hm'T
  refine ⟨a', ha'.symm, fun α hα => ?_⟩
  have hXmem : pinnedX Tag.E6 L α 1 ∈ (rhoSigmaE6A3 L v).range := by
    rw [rhoSigmaE6A3_range, ← hSeq]
    exact pinnedX_mem_rootSpan hα 1
  obtain ⟨A, hA⟩ := hXmem
  have hcomm' := hall A
  rw [hA, ha'] at hcomm'
  have hconj' := rootDiagUnit_conj_pinnedX a' hα.1 (1 : L)
  have h3 : pinnedX Tag.E6 L α (((rootChar a' α : Lˣ) : L) * 1) = pinnedX Tag.E6 L α 1 :=
    hconj'.symm.trans hcomm'
  have h4 := pinnedX_injective (τ := Tag.E6) (R := L) α h3
  exact Units.ext (by simpa using h4)

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
