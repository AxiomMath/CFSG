module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverSylow
public import CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoMatrices
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticSixCoverCore
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverComplement

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryFiveCover

open Matrix CFSG.ClassicalGroups.UnitaryFlag MatrixExtension UnitaryOddCover
  CFSG.LieType.Universal.SpecialLinear
open scoped commutatorElement

variable {K : Type} [Field K] [CharP K 2] (h : UnitaryFieldData 2 1 K)

omit [CharP K 2] in
theorem hconj_one_fin {r : ℕ} : hconj (1 : Matrix (Fin r) (Fin r) K) = 1 := by
  rw [hconj, Matrix.map_one _ (by simp) (by simp), transpose_one]

theorem barInvT_one_add_single {i j : Fin 2} (hij : i ≠ j) (a : K) :
    barInvT h (1 + single i j a) = 1 + single j i (a ^ 2) := by
  refine (eq_barInvT_of_mul_eq_one ?_).symm
  have hX : single j i (a ^ 2) * single j i (a ^ 2) = (0 : Matrix (Fin 2) (Fin 2) K) := by
    simp [hij]
  rw [map_bar_transpose h, hconj_add, hconj_single, hconj_one_fin, Matrix.add_mul,
    Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, hX, add_zero, add_assoc,
    show single j i (a ^ 2) + single j i (a ^ 2) = (0 : Matrix (Fin 2) (Fin 2) K) from by
      ext x y
      exact CharTwo.add_self_eq_zero _, add_zero]

theorem lMat_one_add_single (a : K) :
    lMat h (1 + single (0 : Fin 2) 1 a) = 1 + single (Sum.inl 0 : HypIndex 2 1) (.inl 1) a +
      single (Sum.inr (.inr 1) : HypIndex 2 1) (.inr (.inr 0)) (a ^ 2) := by
  have hdet : (1 + single (0 : Fin 2) 1 a).det = 1 := by
    rw [← hElem, hElem_eq_transvection]
    exact det_transvection_of_ne 0 1 (by decide) a
  rw [lMat_eq_oddDiag hdet, oddDiag, barInvT_one_add_single h (by decide)]
  ext x y
  rcases x with k | l | k <;> rcases y with m | n | m <;> simp [single_apply, one_apply]
  exact Subsingleton.elim l n

omit [CharP K 2] in
theorem oddUni_hermO (a : K) :
    oddUni h 0 (hermO (0 : Fin 2) 1 a) = 1 + single (Sum.inl 0 : HypIndex 2 1) (.inr (.inr 1)) a +
      single (Sum.inl 1 : HypIndex 2 1) (.inr (.inr 0)) (a ^ 2) := by
  rw [oddUni, hermO]
  ext x y
  rcases x with k | l | k <;> rcases y with m | n | m <;> simp [single_apply, one_apply]

@[expose] def swapTwo : hypSU h 2 1 :=
  weylElt h (UnitarySixFieldTwo.one_mem_traceZero h) one_ne_zero
    (UnitarySixFieldTwo.swapSet_mem_hypWeyl ({1} : Finset (Fin 2)))

omit [CharP K 2] in
theorem coe_swapTwo :
    (((swapTwo h : hypSU h 2 1) : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) =
      signedPerm (weylPerm (swapSet ({1} : Finset (Fin 2)))) fun _ => 1 := by
  rw [swapTwo, coe_weylElt, weylMat, UnitarySixFieldTwo.weylCoeff_one]

theorem swapTwo_mul_lMat (a : K) :
    (((swapTwo h : hypSU h 2 1) : GL (HypIndex 2 1) K) :
        Matrix (HypIndex 2 1) (HypIndex 2 1) K) * lMat h (1 + single 0 1 a) =
      oddUni h 0 (hermO 0 1 a) * (((swapTwo h : hypSU h 2 1) : GL (HypIndex 2 1) K) :
        Matrix (HypIndex 2 1) (HypIndex 2 1) K) := by
  rw [coe_swapTwo, lMat_one_add_single h, UnitarySixFieldTwo.signedPerm_mul_one_add_single,
    oddUni_hermO]
  simp [UnitarySixFieldTwo.swapSet_inl, UnitarySixFieldTwo.swapSet_inr, lineCoord]

theorem swapTwo_mul_lHom {B : GL (Fin 2) K} {a : K}
    (hB : (B : Matrix (Fin 2) (Fin 2) K) = 1 + single 0 1 a) (hBr : IsRad h 0 (hermO 0 1 a)) :
    swapTwo h * lHom h 2 B * (swapTwo h)⁻¹ = nElt hBr := by
  rw [mul_inv_eq_iff_eq_mul]
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_lHom, coe_nElt, hB]
  exact swapTwo_mul_lMat h a

omit [CharP K 2] in
theorem coe_eq_one_add_single_of_mem {A : SpecialLinearGroup (Fin 2) K}
    (hA : A ∈ LinearFlag.unitriangular 2 K) :
    (A : Matrix (Fin 2) (Fin 2) K) = 1 + single 0 1 ((A : Matrix (Fin 2) (Fin 2) K) 0 1) := by
  obtain ⟨hlow, hdiag⟩ := hA
  have h10 := hlow 1 0 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [one_apply, h10, hdiag]

variable {E : Type*} [Group E] {θ : E →* hypPSU h 2 1}

include h in
theorem exists_levi_lift [Finite E] (hθ : Function.Surjective θ)
    (hC : θ.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 θ.ker) :
    ∃ Y : Subgroup E, (∀ y ∈ Y, θ y = 1 → y = 1) ∧
      ∀ A : SpecialLinearGroup (Fin 2) K, ∃ y ∈ Y,
        θ y = hypProj h 2 1 (lHom h 2 (SpecialLinearGroup.toGL A)) := by
  have hK := card_eq_four h
  have := h.finite
  have : Fintype K := Fintype.ofFinite K
  set ι : SpecialLinearGroup (Fin 2) K →* hypPSU h 2 1 :=
    (hypProj h 2 1).comp ((lHom h 2).comp SpecialLinearGroup.toGL) with hιdef
  have hι : Function.Injective ι := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro A hA
    have h1 := eq_one_of_hypProj_lHom (h := h) (A := SpecialLinearGroup.toGL A) A.2 hA
    exact Subgroup.mem_bot.mpr (SpecialLinearGroup.toGL_injective (h1.trans (map_one _).symm))
  have : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) :=
    CFSG.LinearGroups.special_linear_isPerfect le_rfl
      (Or.inr ⟨Finset.univ, by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK]⟩)
  have : Group.IsPerfect ι.range := Group.IsPerfect.range _
  set Y := ⁅ι.range.comap θ, ι.range.comap θ⁆ with hY
  obtain ⟨θF, hθF, hθFι⟩ := SymplecticSixCover.exists_derivedComap_cover hθ ι hι
  have hθFker : ∀ z : Y, θF z = 1 ↔ θ z = 1 := fun z => by
    rw [← hθFι, ← map_one ι]
    exact hι.eq_iff.symm
  have : Group.IsPerfect Y := SymplecticSixCover.isPerfect_derivedComap hθ hC _
  have hcenF : θF.ker ≤ Subgroup.center Y := fun z hz => Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hC ((hθFker z).mp hz)) g)
  obtain ⟨S, hS⟩ := LinearFlag.exists_sylow_unitriangular (K := K) 2 (n := 2) (by norm_num)
  obtain ⟨P, hP, hzP⟩ := LinearCover.exists_sylow_map_eq_twoPart_le θF hθF hcenF S
  obtain ⟨w, hw⟩ := hθ (hypProj h 2 1 (swapTwo h))
  have hconjT : ∀ p ∈ (P : Subgroup Y), w * (p : E) * w⁻¹ ∈ preV θ := by
    intro p hp
    have hpS : θF p ∈ (S : Subgroup (SpecialLinearGroup (Fin 2) K)) :=
      hP ▸ Subgroup.mem_map_of_mem θF hp
    rw [hS] at hpS
    have hmat := coe_eq_one_add_single_of_mem hpS
    have hBr : IsRad h 0 (hermO (0 : Fin 2) 1 (((θF p : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) 0 1)) := isRad_zero_iff.mpr (hconj_hermO hK 0 1 _)
    refine ⟨nElt hBr, nElt_mem_radV hBr, ?_⟩
    rw [map_mul, map_mul, map_inv, hw, ← hθFι p]
    change hypProj h 2 1 (nElt hBr) = hypProj h 2 1 (swapTwo h) *
      hypProj h 2 1 (lHom h 2 (SpecialLinearGroup.toGL (θF p))) * (hypProj h 2 1 (swapTwo h))⁻¹
    rw [← map_mul, ← map_inv, ← map_mul, swapTwo_mul_lHom h hmat hBr]
  have hPP : ⁅(P : Subgroup Y), (P : Subgroup Y)⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro p hp q hq
    have hpq := mul_comm_of_mem_preV hθ hC (hconjT p hp) (hconjT q hq)
    have e : (p : E) * q = q * p := by
      have := congrArg (fun z => w⁻¹ * z * w) hpq
      simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at this
      exact this
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext e
  refine ⟨Y, fun y hy hy1 => ?_, fun A => ?_⟩
  · have hk : (⟨y, hy⟩ : Y) ∈ θF.ker := (hθFker _).mpr hy1
    obtain ⟨n, hn⟩ := h2 ⟨y, hy1⟩
    have := hzP _ hk ⟨n, Subtype.ext (by simpa using congrArg Subtype.val hn)⟩
    rw [hPP, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  · obtain ⟨z, hz⟩ := hθF A
    exact ⟨z, z.2, by rw [← hθFι, hz]; rfl⟩

include h in
theorem ker_eq_bot_of_sq [Finite E] [Group.IsPerfect E] (hθ : Function.Surjective θ)
    (hC : θ.ker ≤ Subgroup.center E) (hsq : ∀ c, θ c = 1 → c ^ 2 = 1) : θ.ker = ⊥ := by
  have h2 : IsPGroup 2 θ.ker := fun c => ⟨1, Subtype.ext (by
    rw [Subgroup.coe_pow, pow_one, OneMemClass.coe_one]
    exact hsq c c.2)⟩
  obtain ⟨M₀, hM₀N, hM₀inj, hM₀surj, hM₀norm⟩ := exists_radical_complement hθ hC le_rfl hsq
  obtain ⟨Y, hYinj, hYsurj⟩ := exists_levi_lift h hθ hC h2
  exact ker_eq_bot_of_lifts hθ hC h2 (by norm_num) M₀ hM₀N hM₀inj hM₀surj hM₀norm Y hYinj
    fun A _ => hYsurj A

include h in
theorem ker_eq_bot_of_hypPSU [Finite E] [Group.IsPerfect E] (hθ : Function.Surjective θ)
    (hC : θ.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 θ.ker) : θ.ker = ⊥ :=
  ker_eq_bot_of_sq_reduction (fun _ hθ' hC' hsq => ker_eq_bot_of_sq h hθ' hC' hsq) θ hθ hC h2

end CFSG.LocalAnalysis.ComponentInitial.UnitaryFiveCover

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.ClassicalGroups.UnitaryFlag

theorem even_unitary_five_prime_field_central_two_cover_trivial {E : Type*} {J : Type}
    [Group E] [Group J] [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    (hJ : CFSG.Blueprint.LieModel J .PSU 5 2 1) : η.ker = ⊥ ∧ Function.Bijective η := by
  rcases hJ with ⟨-, -, K, _, _, hcard, ⟨e⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · have h : UnitaryFieldData 2 1 K := ⟨Nat.prime_two, le_rfl, by rw [hcard]; norm_num⟩
    have := h.charP
    obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 1) h
    let φ : hypPSU h 2 1 ≃* J := (hypPSUEquivStatedProj h hR (by norm_num)).trans e.symm
    set η' : E →* hypPSU h 2 1 := φ.symm.toMonoidHom.comp η with hη'
    have hker : η'.ker = η.ker := by
      ext z
      exact φ.symm.map_eq_one_iff
    have hbot := UnitaryFiveCover.ker_eq_bot_of_hypPSU h (φ.symm.surjective.comp hη)
      (hker ▸ hC) (hker ▸ h2)
    rw [hker] at hbot
    exact ⟨hbot, (MonoidHom.ker_eq_bot_iff η).mp hbot, hη⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end CFSG.LocalAnalysis.ComponentInitial
