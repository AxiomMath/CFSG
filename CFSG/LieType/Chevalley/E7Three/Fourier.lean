module

public import CFSG.LieType.Chevalley.E7Three.Cycle
public import CFSG.LieType.Chevalley.E7Three.Multiplicity

public noncomputable section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.Fourier

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KA5L CFSG.LieType.Chevalley.E7Three.Product
  CFSG.LieType.Chevalley.E7Three.PauliWords CFSG.LieType.Chevalley.E7Three.Images
  CFSG.LieType.Chevalley.E7Three.Cycle CFSG.LieType.Chevalley.E7Three.Cube
  CFSG.LieType.Chevalley.E7Three.Multiplicity

open scoped MatrixGroups

theorem paired_parameters_conj {G : Type*} [Group G] (F X C Z : G)
    (hZ : Commute Z F) (hX : F * X * F⁻¹ = C ^ 2) (hC : F * C * F⁻¹ = X)
    (hC3 : C ^ 3 = 1) (hF4 : F ^ 4 = 1) :
    let f : Fin 3 → G := ![F, F, F⁻¹]
    let g : Fin 3 → G := ![Z, Z, 1]
    let b : Fin 3 → G := ![X, X, X]
    let c : Fin 3 → G := ![C, C, C ^ 2]
    f * g * f⁻¹ = g ∧ f * b * f⁻¹ = c ^ 2 ∧ f * c * f⁻¹ = b ∧ f ^ 4 = 1 := by
  have hIX : F⁻¹ * X * F = C := by
    rw [← hC]
    group
  have hIC : F⁻¹ * C ^ 2 * F = X := by
    rw [← hX]
    group
  have hC4 : C ^ 4 = C := by rw [pow_succ, hC3, one_mul]
  have hG : F * Z * F⁻¹ = Z := by
    rw [hZ.symm.eq, mul_assoc, mul_inv_cancel, mul_one]
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext r
    fin_cases r
    · change F * Z * F⁻¹ = Z
      exact hG
    · change F * Z * F⁻¹ = Z
      exact hG
    · change F⁻¹ * 1 * (F⁻¹)⁻¹ = 1
      group
  · funext r
    fin_cases r
    · change F * X * F⁻¹ = C ^ 2
      exact hX
    · change F * X * F⁻¹ = C ^ 2
      exact hX
    · change F⁻¹ * X * (F⁻¹)⁻¹ = (C ^ 2) ^ 2
      rw [inv_inv, hIX, ← pow_mul]
      exact hC4.symm
  · funext r
    fin_cases r
    · change F * C * F⁻¹ = X
      exact hC
    · change F * C * F⁻¹ = X
      exact hC
    · change F⁻¹ * C ^ 2 * (F⁻¹)⁻¹ = X
      rw [inv_inv]
      exact hIC
  · funext r
    fin_cases r
    · change F ^ 4 = 1
      exact hF4
    · change F ^ 4 = 1
      exact hF4
    · change (F⁻¹) ^ 4 = 1
      rw [inv_pow, hF4, inv_one]

variable {K : Type} [Field K] [CharP K 2]

theorem exists_fourier_cube_and_multiplicity (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (hζ1 : (ζ : K) ≠ 1) :
    ∃ n : adjointGroup .E7 K,
      n * scalarWord ζ * n⁻¹ = scalarWord ζ ∧
      n * pairedWord ζ * n⁻¹ = (cyclic (K := K)) ^ 2 ∧
      n * cyclic * n⁻¹ = pairedWord ζ ∧ n ^ 4 = 1 ∧
      n * multiplicityWord ζ * n⁻¹ = multiplicityWord ζ := by
  have h3 : (ζ : K) ^ 3 = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one]
      using congrArg (fun u : Kˣ => (u : K)) hζ
  let F : SL(3, K) := fourierWord (ζ : K) h3 hζ1
  let X : SL(3, K) := diagonalWord ζ
  let C : SL(3, K) := cycleWord
  let Z : SL(3, K) := centralWord ζ
  obtain ⟨hX, hC⟩ := fourierWord_conj_words ζ hζ hζ1
  change F * X * F⁻¹ = C ^ 2 at hX
  change F * C * F⁻¹ = X at hC
  obtain ⟨hg, hb, hc, hf⟩ := paired_parameters_conj F X C Z
    (centralWord_commute ζ hζ F) hX hC cycleWord_pow_three (fourierWord_pow_four _ h3 hζ1)
  obtain ⟨w⟩ := nativeFrame_exists (K := K)
  let N : (Fin 3 → SL(3, K)) →* adjointGroup .E7 K := adjProdHom w
  have hG : N ![Z, Z, 1] = scalarWord ζ := by
    apply Subtype.ext
    exact prodHom_central w ζ
  have hB : N ![X, X, X] = pairedWord ζ := by
    apply Subtype.ext
    exact prodHom_diagonal w ζ
  have hCycle : N ![C, C, C ^ 2] = cyclic (K := K) := by
    apply Subtype.ext
    exact prodHom_cycle w
  refine ⟨N ![F, F, F⁻¹], ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [map_mul, map_inv, hG] using congrArg N hg
  · simpa only [map_mul, map_inv, map_pow, hB, hCycle] using congrArg N hb
  · simpa only [map_mul, map_inv, hB, hCycle] using congrArg N hc
  · simpa only [map_pow, map_one] using congrArg N hf
  · exact mul_inv_eq_iff_eq_mul.mpr
      (multiplicityWord_commute_adjProdHom w ζ hζ ![F, F, F⁻¹]).symm.eq

theorem exists_fourier_normalizer_and_multiplicity (ζ : Kˣ) (hζ : ζ ^ 3 = 1)
    (hζ1 : (ζ : K) ≠ 1) :
    ∃ n : adjointGroup .E7 K,
      n ∈ Subgroup.normalizer ((cubeHom ζ hζ).range : Set (adjointGroup .E7 K)) ∧
      n * scalarWord ζ * n⁻¹ = scalarWord ζ ∧
      n * pairedWord ζ * n⁻¹ = (cyclic (K := K)) ^ 2 ∧
      n * cyclic * n⁻¹ = pairedWord ζ ∧ n ^ 4 = 1 ∧
      n * multiplicityWord ζ * n⁻¹ = multiplicityWord ζ := by
  classical
  obtain ⟨n, hg, hb, hc, h4, hm⟩ := exists_fourier_cube_and_multiplicity ζ hζ hζ1
  let E := (cubeHom ζ hζ).range
  let Q : adjointGroup .E7 K →* adjointGroup .E7 K := (MulAut.conj n).toMonoidHom
  have h0 : Q (scalarWord ζ) = scalarWord ζ := hg
  have h1 : Q (pairedWord ζ) = (cyclic (K := K)) ^ 2 := hb
  have h2 : Q (cyclic (K := K)) = pairedWord ζ := hc
  have hclose : ∀ y : adjointGroup .E7 K, y ∈ E → n * y * n⁻¹ ∈ E := by
    intro y hy
    obtain ⟨f, rfl⟩ := hy
    change Q (cubeHom ζ hζ f) ∈ E
    rw [cubeHom_apply, Q.map_mul _ _, Q.map_mul _ _, Q.map_pow _ _, Q.map_pow _ _,
      Q.map_pow _ _, h0, h1, h2]
    exact E.mul_mem (E.mul_mem
      (E.pow_mem (generators_mem_range ζ hζ 0) _)
      (E.pow_mem (E.pow_mem (generators_mem_range ζ hζ 2) 2) _))
      (E.pow_mem (generators_mem_range ζ hζ 1) _)
  letI : Fintype E := MonoidHom.fintypeRange (cubeHom ζ hζ)
  exact ⟨n, Subgroup.mem_normalizer_fintype hclose, hg, hb, hc, h4, hm⟩

end CFSG.LieType.Chevalley.E7Three.Fourier
