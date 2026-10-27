module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCData
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCProj
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOUnitComp
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOAntiComp
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.C

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU)
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] [Finite K]

theorem isQuasisimple_isoCent_unit (hK : ringChar K ≠ 2) {c : K} (hc : ¬ IsSquare c) {p f : ℕ}
    (hp : p.Prime) (hKc : Nat.card K = p ^ f) {n : ℕ} (hn : 3 ≤ n) {R A : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-c)))
    (hA : (A : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (jMat c)) :
    IsQuasisimple (⁅isoCent R A, isoCent R A⁆ : Subgroup (GL (Fin (2 * n)) K)) := by
  have hc0 : c ≠ 0 := fun h => hc ⟨0, by rw [h, mul_zero]⟩
  have : Fact (Irreducible (sqPoly c)) := ⟨irreducible_sqPoly hc⟩
  have h := unitaryFieldData_EAlg hc0 hp hKc
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (EAlg c) := h.finite
  have : CharP (EAlg c) p := h.charP
  have hσ : ∀ x : EAlg c, h.bar x = x ^ Nat.card K := fun x => by rw [h.bar_apply, hKc]
  have hW : ∀ x, ((phiE c).toRingHom x)ᵀ * wMat 1 (-c) =
      wMat 1 (-c) * (phiE c).toRingHom (h.bar x) := fun x => by
    rw [hσ]
    exact transpose_phiE_mul_wNeg hK hc x
  have hRG : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (wMat 1 (-c)) * resMat (phiE c).toRingHom n 1 := by
    rw [map_one, Matrix.mul_one, hR]
  have hZ := commutator_iso_inf_centralizer_eq (φ := (phiE c).toRingHom) (σ := h.bar)
    (r := AdjoinRoot.root (sqPoly c)) (phiE_injective c) (wMat_inv_mul hc0) hW (phiE_root c)
    (fun M hM => phiE_mem_range hc0 hM) 1 hRG hA
  have hq : p ^ f ≠ 2 := by
    rw [← hKc]
    intro h2
    have := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
    rw [h2] at this
    exact (by decide : ¬ Odd 2) this
  rw [hZ, commutator_uGrp_eq_unitarySU h hn hq]
  have hqs := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := EAlg c)
    (p := p) (f := f) (by rw [h.card, ← pow_mul, mul_comm]) hn
    (fun e => hq (Prod.ext_iff.1 e).2)).1
  exact LocalCores.isQuasisimple_of_mulEquiv
    ((unitarySU p f (EAlg c) n).equivMapOfInjective _ (resGL_injective (phiE_injective c) n)) hqs

omit [Finite K] in
theorem isQuasisimple_isoCent_anti (h2 : (2 : K) ≠ 0) {s : K} (hs : s ≠ 0) {n : ℕ} (hn : 3 ≤ n)
    {R A : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-(s ^ 2))))
    (hA : (A : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (jMat (s ^ 2))) :
    IsQuasisimple (⁅isoCent R A, isoCent R A⁆ : Subgroup (GL (Fin (2 * n)) K)) := by
  have hc0 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have hW₀ : wMat 1 (-(s ^ 2)⁻¹) * wMat 1 (-(s ^ 2)) = 1 := by
    rw [wMat, wMat, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp [hc0]
  have hRG : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (wMat 1 (-(s ^ 2))) * resMat (phiS h2 hs).toRingHom n 1 := by
    rw [map_one, Matrix.mul_one, hR]
  have hZ := commutator_iso_inf_centralizer_eq (φ := (phiS h2 hs).toRingHom) (σ := swapS)
    (r := (s, -s)) (phiS_injective h2 hs) hW₀ (fun x => transpose_phiS_mul h2 hs x)
    (phiS_root h2 hs) (fun M hM => phiS_mem_range h2 hs hM) 1 hRG hA
  rw [hZ, commutator_uGrp_swap_eq hn]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hq := CFSG.LieType.Universal.SpecialLinear.isQuasisimple m K (by omega)
  have hinj : Function.Injective ((iotaS (m + 1)).comp
      (SpecialLinearGroup.toGL : SL(m + 1, K) →* GL (Fin (m + 1)) K)) :=
    iotaS_injective.comp (fun x y h => Subtype.ext (congrArg Units.val h))
  have hqr : IsQuasisimple ((iotaS (m + 1)).comp
      (SpecialLinearGroup.toGL : SL(m + 1, K) →* GL (Fin (m + 1)) K)).range :=
    LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective hinj) hq
  exact LocalCores.isQuasisimple_of_mulEquiv
    (((iotaS (m + 1)).comp (SpecialLinearGroup.toGL :
      SL(m + 1, K) →* GL (Fin (m + 1)) K)).range.equivMapOfInjective
      _ (resGL_injective (phiS_injective h2 hs) (m + 1))) hqr

theorem isQuasisimple_isoCent_pc (hK : ringChar K ≠ 2) {p f : ℕ} (hp : p.Prime)
    (hKc : Nat.card K = p ^ f) {c : K} (hc : c ≠ 0) {n : ℕ} (hn : 3 ≤ n)
    {R A : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-c)))
    (hA : (A : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (jMat c)) :
    IsQuasisimple (⁅isoCent R A, isoCent R A⁆ : Subgroup (GL (Fin (2 * n)) K)) := by
  by_cases hsq : IsSquare c
  · obtain ⟨s, hs⟩ := hsq
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact hc (by rw [hs, mul_zero])
    have hcs : c = s ^ 2 := by rw [hs, sq]
    exact isQuasisimple_isoCent_anti (Ring.two_ne_zero hK) hs0 hn (by rw [hR, hcs])
      (by rw [hA, hcs])
  · exact isQuasisimple_isoCent_unit hK hsq hp hKc hn hR hA

theorem pc_propC (hK : ringChar K ≠ 2) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hKc : Nat.card K = ℓ ^ f)
    {c : K} (hc : c ≠ 0) {n : ℕ} (hn : 3 ≤ n) {R : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-c)))
    {A : matrixDerived (oQ R)}
    (hA : ((A : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (jMat c))
    {R₁ R₂ : Subgroup (StatedProj (matrixDerived (oQ R)))} {p m : ℕ} [Fact p.Prime]
    (hC : PropCData (projH _ A) R₁ R₂ p m) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hRs : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R := by
    rw [hR, blkDiag_transpose, wMat, diagonal_transpose]
  set Z := isoCent R (A : GL (Fin (2 * n)) K) with hZ
  have hq := isQuasisimple_isoCent_pc hK hℓ hKc hc hn hR hA
  have hZΩ : ⁅Z, Z⁆ ≤ matrixDerived (oQ R) := by
    rw [matrixDerived_oQ h2 R hRs]
    exact commutator_mono inf_le_left inf_le_left
  set N := ((⁅Z, Z⁆).subgroupOf (matrixDerived (oQ R))).map (projH _) with hN
  have hleN : ∀ {L : Subgroup (StatedProj (matrixDerived (oQ R)))},
      L ≤ centralizer ({projH _ A} : Set _) → ⁅L, L⁆ = L → L ≤ N := by
    intro L hL hperf
    refine (le_map_commutator_of_perfect A hL hperf).trans (map_mono ?_)
    rw [commutator_le]
    intro B hB B' hB'
    rw [mem_subgroupOf]
    have hZB : ∀ {C : matrixDerived (oQ R)}, C ∈ centralizer ({A} : Set _) →
        (C : GL (Fin (2 * n)) K) ∈ Z := by
      intro C hC
      refine ⟨?_, mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hC))⟩
      have := matrixDerived_le_isometries (oQ R) C.2
      rwa [matrixIsometries_oQ h2 R hRs] at this
    exact commutator_mem_commutator (hZB hB) (hZB hB')
  have hNC : N ≤ centralizer ({projH _ A} : Set _) := by
    rintro _ ⟨g, hg, rfl⟩
    replace hg : (g : GL (Fin (2 * n)) K) ∈ ⁅Z, Z⁆ := hg
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hgZ : (g : GL (Fin (2 * n)) K) ∈ Z :=
      commutator_le_self _ hg
    exact mem_centralizer_singleton_iff.1 (mem_inf.1 hgZ).2
  have hNq : IsQuasisimple N := by
    set f := (projH (matrixDerived (oQ R))).comp
      (((⁅Z, Z⁆).subgroupOf (matrixDerived (oQ R))).subtype.comp
        (subgroupOfEquivOfLe hZΩ).symm.toMonoidHom) with hf
    have hfr : f.range = N := by
      rw [hf, MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.2
        (subgroupOfEquivOfLe hZΩ).symm.surjective, Subgroup.map_top, Subgroup.range_subtype]
    rcases LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images hq f with h | h
    · exfalso
      rw [hfr] at h
      have hR₂N := hleN hC.le₂ (commutator_eq_of_isPComponent hC.le₂ hC.comp₂)
      rw [h, le_bot_iff] at hR₂N
      exact ne_bot_of_isPComponent hC.le₂ hC.comp₂ hR₂N
    · rwa [hfr] at h
  have h₁ := eq_of_le_of_isQuasisimple (hleN hC.le₁ (commutator_eq_of_isPComponent hC.le₁ hC.comp₁))
    hNC hC.comp₁ hNq
  have h₂ := eq_of_le_of_isQuasisimple (hleN hC.le₂ (commutator_eq_of_isPComponent hC.le₂ hC.comp₂))
    hNC hC.comp₂ hNq
  have h12 : R₁ = R₂ := h₁.trans h₂.symm
  obtain ⟨e₁⟩ := hC.iso₁
  obtain ⟨e₂⟩ := hC.iso₂
  subst h12
  have hGF : ringChar (GaloisField p m) ≠ 2 := by
    rw [ringChar.eq (GaloisField p m) p]
    exact hC.p_ne_two
  have h1 := Nat.card_congr e₁.toEquiv
  rw [Nat.card_congr e₂.toEquiv, ← card_PSL_mul_two hGF] at h1
  have hpos : 0 < Nat.card PSL(2, GaloisField p m) := Nat.card_pos
  omega

end CFSG.ComponentClassification.Burgoyne.C
