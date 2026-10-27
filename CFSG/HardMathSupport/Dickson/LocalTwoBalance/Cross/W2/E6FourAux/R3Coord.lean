module

public import CFSG.RankThree.PartOne.KE.E6FourData
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
open CFSG.RankThree.E6 (weylMatrix e6Index dualMatrix)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2 (unitarySet)
open scoped Pointwise commutatorElement Matrix MatrixGroups

theorem e6_four_coordinates (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 4)
    (hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 2 + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E6 L) (hnm : n ∈ monomialSubgroup .E6 L)
    (hnW : ∀ u, weylQuotientHom .E6 L ⟨n, hnm⟩ • u = (weylMatrix e6F4U) *ᵥ u)
    (g0 : ModGL .E6 L) (hg0C : g0 ∈ adjointGroup .E6 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL .E6 L), Finite P → P ≤ adjointGroup .E6 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb .E6 K L).range)
    (hT : twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) =
      (fixedCharTuples e6FourM (iterateFrobenius L ℓ f)).map (rootDiagUnitHom .E6 L))
    {x : adjointGroup .E6 K} (hx : orderOf x = p) (c : adjointGroup .E6 K)
    (hh : g0⁻¹ * adjEmb .E6 K L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    {b : Fin Tag.E6.rank → Lˣ}
    (hb : rootDiagUnit .E6 b = g0⁻¹ * adjEmb .E6 K L (c * x * c⁻¹) * g0)
    (hne : (rootCharKernel b).Nonempty)
    (m : ModGL .E6 K)
    (hmadj : baseChangeGL (algebraMap K L) m ∈ adjointGroup .E6 L)
    (hmx : m * (x : ModGL .E6 K) * m⁻¹ = (x : ModGL .E6 K))
    (hmD : ∀ d ∈ (⁅Subgroup.centralizer ({x} : Set (adjointGroup .E6 K)),
      Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))⁆ : Subgroup (adjointGroup .E6 K)),
        m * (d : ModGL .E6 K) * m⁻¹ = (d : ModGL .E6 K)) :
    ∃ a' : Fin Tag.E6.rank → Lˣ,
      rootDiagUnit .E6 a' = g0⁻¹ * adjEmb .E6 K L c * baseChangeGL (algebraMap K L) m *
        (adjEmb .E6 K L c)⁻¹ * g0 ∧ ∀ α ∈ rootCharKernel b, rootChar a' α = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL .E6 L →* ModGL .E6 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  have hinj0 : Function.Injective (rootDiagUnitHom .E6 L) := rootDiagUnit_injective
  obtain ⟨ψ, hψinj, hψ, hψb⟩ := e6_four_perx K hf hK hp hp3 hord hΦ L n hnm hnW g0 hg0C hg0 hperf
    hT hx c hh
  obtain ⟨-, hψne⟩ := hψb b hb
  obtain ⟨Pt, hPq, hcomm, ⟨h₀, hh₀⟩, v, hSeq, H, hH⟩ := hψne hne
  obtain ⟨hq, h2, h1⟩ := isQuasisimple_commutator_of_embedding ψ hψinj hPq hcomm
  set ι : ModGL .E6 K →* ModGL .E6 L := baseChangeGL (algebraMap K L) with hιdef
  set m' : ModGL .E6 L := g0⁻¹ * adjEmb .E6 K L c * ι m * (adjEmb .E6 K L c)⁻¹ * g0 with hm'
  have hm'adj : m' ∈ adjointGroup .E6 L :=
    mul_mem (mul_mem (mul_mem (mul_mem (inv_mem hg0C) (adjEmb_mem c)) hmadj)
      (inv_mem (adjEmb_mem c))) hg0C
  have hfixψ : ∀ d : adjointGroup .E6 K, m * (d : ModGL .E6 K) * m⁻¹ = (d : ModGL .E6 K) →
      m' * (g0⁻¹ * adjEmb .E6 K L (c * d * c⁻¹) * g0) * m'⁻¹ =
        g0⁻¹ * adjEmb .E6 K L (c * d * c⁻¹) * g0 := by
    intro d hd
    have hd' : ι m * adjEmb .E6 K L d * (ι m)⁻¹ = adjEmb .E6 K L d := by
      have := congrArg ι hd
      rw [map_mul, map_mul, map_inv] at this
      exact this
    have e : m' * (g0⁻¹ * adjEmb .E6 K L (c * d * c⁻¹) * g0) * m'⁻¹ =
        g0⁻¹ * adjEmb .E6 K L c * (ι m * adjEmb .E6 K L d * (ι m)⁻¹) *
          (adjEmb .E6 K L c)⁻¹ * g0 := by
      rw [hm']
      simp only [map_mul, map_inv]
      group
    rw [e, hd']
    simp only [map_mul, map_inv]
    group
  have hbfix : b ∈ fixedCharTuples e6FourM Fr := by
    have hh' := hh
    rw [hT] at hh'
    obtain ⟨a', ha', haa⟩ := hh'
    have : a' = b := hinj0 (haa.trans hb.symm)
    exact this ▸ ha'
  have hbp : orderOf (rootDiagUnit .E6 b) = p := by
    rw [hb]
    have e1 : orderOf (g0⁻¹ * adjEmb .E6 K L (c * x * c⁻¹) * g0) =
        orderOf (adjEmb .E6 K L (c * x * c⁻¹)) := by
      have := orderOf_injective (MulAut.conj g0⁻¹).toMonoidHom (MulAut.conj g0⁻¹).injective
        (adjEmb .E6 K L (c * x * c⁻¹))
      simpa [MulAut.conj_apply] using this
    have e2 : orderOf (adjEmb .E6 K L (c * x * c⁻¹)) = orderOf (c * x * c⁻¹) :=
      orderOf_injective _ adjEmb_injective _
    have e3 : orderOf (c * x * c⁻¹) = orderOf x := by
      have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
      simpa [MulAut.conj_apply] using this
    rw [e1, e2, e3, hx]
  have hbap := pow_eq_one_of_orderOf_rootDiagUnit hbp
  have hb1 := ne_one_of_orderOf_rootDiagUnit hp hbp
  have hstabb := e6Four_stab_of_fixed Fr hFr hp hp3 hord hΦ hbfix hbap hb1
  have hCent : ∀ y ∈ adjointGroup .E6 L, y * rootDiagUnit .E6 b = rootDiagUnit .E6 b * y →
      y ∈ (torusGroup .E6 L : Set (ModGL .E6 L)) *
        (rootSpan .E6 L (sigmaSetE6A3 v) : Set (ModGL .E6 L)) := fun y hy hcomm =>
    mem_torus_mul_rootSpan_of_commute_of_stab hstabb (sigmaSetE6A3_isRoot v) (sigmaSetE6A3_neg v)
      (by rw [hSeq]) hy hcomm
  have hfixh : m' * rootDiagUnit .E6 b * m'⁻¹ = rootDiagUnit .E6 b := by
    rw [hb]
    exact hfixψ x hmx
  have hcommb : m' * rootDiagUnit .E6 b = rootDiagUnit .E6 b * m' := mul_inv_eq_iff_eq_mul.1 hfixh
  obtain ⟨t, ht, s, hs, hts⟩ := Set.mem_mul.1 (hCent m' hm'adj hcommb)
  have hs' : s ∈ (rhoSigmaE6A3 L v).range := by
    rw [rhoSigmaE6A3_range]
    exact hs
  obtain ⟨S, rfl⟩ := hs'
  obtain ⟨b0, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hρinj : Function.Injective (rhoSigmaE6A3 L v) := rhoSigmaE6A3_injective v
  set d : Fin 4 → Lˣ := fun i => rootChar b0 (wbE6A3 v i) with hd
  have hconj : ∀ A : SL(4, L), (rootDiagUnit .E6 b0 * rhoSigmaE6A3 L v S) * rhoSigmaE6A3 L v A *
      (rootDiagUnit .E6 b0 * rhoSigmaE6A3 L v S)⁻¹ = rhoSigmaE6A3 L v (conjDiagn d (S * A * S⁻¹)) := by
    intro A
    rw [← rhoSigmaE6A3_torus v b0 (S * A * S⁻¹)]
    simp only [map_mul, map_inv, _root_.mul_inv_rev]
    group
  have hfixρ : ∀ Z : SL(4, L), (∃ Y ∈ unitarySet (Ω := L) (Nat.card K) 4,
        Matrix.SpecialLinearGroup.toGL Z = Matrix.SpecialLinearGroup.toGL H * Y *
          (Matrix.SpecialLinearGroup.toGL H)⁻¹) →
      m' * rhoSigmaE6A3 L v Z * m'⁻¹ = rhoSigmaE6A3 L v Z := by
    intro Z hZ
    have hmem := hH Z hZ
    rw [← h2] at hmem
    obtain ⟨d', hd', hd'ψ⟩ := hmem
    have hd'D : ((d' : Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))) :
        adjointGroup .E6 K) ∈ (⁅Subgroup.centralizer ({x} : Set (adjointGroup .E6 K)),
          Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))⁆ :
            Subgroup (adjointGroup .E6 K)) := by
      rw [← h1]
      exact ⟨d', hd', rfl⟩
    rw [← hd'ψ, hψ d']
    exact hfixψ _ (hmD _ hd'D)
  have key : ∀ Z : SL(4, L), (∃ Y ∈ unitarySet (Ω := L) (Nat.card K) 4,
        Matrix.SpecialLinearGroup.toGL Z = Matrix.SpecialLinearGroup.toGL H * Y *
          (Matrix.SpecialLinearGroup.toGL H)⁻¹) → conjDiagn d (S * Z * S⁻¹) = Z := by
    intro Z hZ
    apply hρinj
    rw [← hconj Z, hts]
    exact hfixρ Z hZ
  have htoGL_conj : ∀ A : SL(4, L), Matrix.SpecialLinearGroup.toGL (conjDiagn d A) =
      diagGLn d * Matrix.SpecialLinearGroup.toGL A * (diagGLn d)⁻¹ := fun A =>
    Units.ext (coe_conjDiagn d A)
  set W : GL (Fin 4) L := diagGLn d * Matrix.SpecialLinearGroup.toGL S with hW
  have hWcomm : ∀ Y ∈ unitarySet (Ω := L) (Nat.card K) 4,
      W * (Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹) * W⁻¹ =
        Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹ := by
    intro Y hY
    let Ysl : SL(4, L) := ⟨(Y : Matrix (Fin 4) (Fin 4) L), hY.2.1⟩
    have hYsl : Matrix.SpecialLinearGroup.toGL Ysl = Y := Units.ext rfl
    have hZ : ∃ Y' ∈ unitarySet (Ω := L) (Nat.card K) 4,
        Matrix.SpecialLinearGroup.toGL (H * Ysl * H⁻¹) = Matrix.SpecialLinearGroup.toGL H * Y' *
          (Matrix.SpecialLinearGroup.toGL H)⁻¹ :=
      ⟨Y, hY, by rw [map_mul, map_mul, map_inv, hYsl]⟩
    have h3 := congrArg Matrix.SpecialLinearGroup.toGL (key (H * Ysl * H⁻¹) hZ)
    simp only [htoGL_conj, map_mul, map_inv, hYsl] at h3
    rw [hW]
    simpa [mul_assoc] using h3
  have hW' : (Matrix.SpecialLinearGroup.toGL H)⁻¹ * W * Matrix.SpecialLinearGroup.toGL H ∈
      Subgroup.centralizer (unitarySet (Ω := L) (Nat.card K) 4) := by
    rw [Subgroup.mem_centralizer_iff]
    intro Y hY
    have h4 := hWcomm Y hY
    have h5 : W * (Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹) =
        (Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹) * W := by
      calc _ = (W * (Matrix.SpecialLinearGroup.toGL H * Y *
              (Matrix.SpecialLinearGroup.toGL H)⁻¹) * W⁻¹) * W := by group
        _ = _ := by rw [h4]
    calc Y * ((Matrix.SpecialLinearGroup.toGL H)⁻¹ * W * Matrix.SpecialLinearGroup.toGL H)
        = (Matrix.SpecialLinearGroup.toGL H)⁻¹ * ((Matrix.SpecialLinearGroup.toGL H * Y *
            (Matrix.SpecialLinearGroup.toGL H)⁻¹) * W) * Matrix.SpecialLinearGroup.toGL H := by
          group
      _ = (Matrix.SpecialLinearGroup.toGL H)⁻¹ * (W * (Matrix.SpecialLinearGroup.toGL H * Y *
            (Matrix.SpecialLinearGroup.toGL H)⁻¹)) * Matrix.SpecialLinearGroup.toGL H := by
          rw [h5]
      _ = ((Matrix.SpecialLinearGroup.toGL H)⁻¹ * W * Matrix.SpecialLinearGroup.toGL H) * Y := by
          group
  rw [CFSG.RankThree.Classical2.centralizer_unitary_eq_range_scalar (Ω := L) (k := K) rfl (by norm_num : 3 ≤ 4)] at hW'
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
  have hsT : rhoSigmaE6A3 L v S ∈ torusGroup .E6 L := rhoSigmaE6A3_diagonal v S hSdiag
  have hm'T : m' ∈ torusGroup .E6 L := by
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
  have hXmem : pinnedX .E6 L α 1 ∈ (rhoSigmaE6A3 L v).range := by
    rw [rhoSigmaE6A3_range, ← hSeq]
    exact pinnedX_mem_rootSpan hα 1
  obtain ⟨A, hA⟩ := hXmem
  have hcomm' := hall A
  rw [hA, ha'] at hcomm'
  have hconj' := rootDiagUnit_conj_pinnedX a' hα.1 (1 : L)
  have h3 : pinnedX .E6 L α (((rootChar a' α : Lˣ) : L) * 1) = pinnedX .E6 L α 1 :=
    hconj'.symm.trans hcomm'
  have h4 := pinnedX_injective (τ := Tag.E6) (R := L) α h3
  exact Units.ext (by simpa using h4)

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
