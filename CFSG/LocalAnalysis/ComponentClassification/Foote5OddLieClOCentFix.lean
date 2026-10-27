module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOKronElts
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClSpField
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClUGraphFix

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (signMat reflGL rotGL)
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K]

section

variable {d : ℕ}

theorem ClO.cent_fix (hK : ringChar K ≠ 2) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R)
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))))
    {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1)
    (hcd : CompData ⁅isoCent R g.val.left, isoCent R g.val.left⁆)
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))} (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ g = oκ _ g * y)
    (hRc : ∀ s, oκ _ g s = s → Odd (orderOf s) → ∀ y ∈ Ro,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro)
    {g' : similarityPairs (oQ R)} (hy : oκ _ g' ∈ Ro)
    {X : GL (Fin d) K} (hX : X ∈ ⁅isoCent R g.val.left, isoCent R g.val.left⁆) :
    (g'.val.left : Matrix (Fin d) (Fin d) K) * (X : Matrix (Fin d) (Fin d) K).map g'.val.right *
        ((g'.val.left⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (X : Matrix (Fin d) (Fin d) K) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hHeq : matrixDerived (oQ R) = ⁅CatalogueBGraphForm.isometryGroup d K R,
      CatalogueBGraphForm.isometryGroup d K R⁆ := matrixDerived_oQ h2 R hR
  set A := g.val.left with hA
  set Z := isoCent R A with hZ
  set t := oκ (oQ R) g with ht
  set φ := (matrixDerivedConjugation (oQ R) g).toMonoidHom with hφ
  have hφc : ∀ Y : matrixDerived (oQ R), ((φ Y : matrixDerived (oQ R)) : GL (Fin d) K) =
      A * Y * A⁻¹ := by
    intro Y
    change (matrixDerivedConjugation (oQ R) g Y).val = _
    rw [matrixDerivedConjugation_val, hg1, map_one, MulAut.one_apply]
  have hφt : ∀ Y, t (projH (matrixDerived (oQ R)) Y) = projH (matrixDerived (oQ R)) (φ Y) :=
    fun Y => kappa_lift _ Y
  have hZH : ⁅Z, Z⁆ ≤ matrixDerived (oQ R) := by
    rw [hHeq]
    exact commutator_mono inf_le_left inf_le_left
  have hZZ : ⁅Z, Z⁆ ≤ Z := Subgroup.commutator_le_self Z
  set F := ⁅Z, Z⁆.subgroupOf (matrixDerived (oQ R)) with hF
  have hF1 : ∀ Y ∈ F, φ Y = Y := by
    intro Y hY
    apply Subtype.ext
    rw [hφc]
    have hc := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hZZ (mem_subgroupOf.1 hY))).2
    rw [← hc, mul_inv_cancel_right]
  have hF2 : ∀ h : matrixDerived (oQ R), h⁻¹ * φ h ∈
      (StatedScalars (Fin d) K).subgroupOf (matrixDerived (oQ R)) →
      ∀ Y ∈ F, h * Y * h⁻¹ ∈ F := by
    intro h hh Y hY
    obtain ⟨c, hc⟩ := hh
    have hc' : ((h : GL (Fin d) K))⁻¹ * (A * h * A⁻¹) = GeneralLinearGroup.scalar (Fin d) c := by
      rw [hc]
      change _ = ((h : GL (Fin d) K))⁻¹ * ((φ h : matrixDerived (oQ R)) : GL (Fin d) K)
      rw [hφc]
    have hcA : A * h * A⁻¹ = GeneralLinearGroup.scalar (Fin d) c * h := by
      calc A * h * A⁻¹ = (h : GL (Fin d) K) * (((h : GL (Fin d) K))⁻¹ * (A * h * A⁻¹)) := by
            group
        _ = (h : GL (Fin d) K) * GeneralLinearGroup.scalar (Fin d) c := by rw [hc']
        _ = GeneralLinearGroup.scalar (Fin d) c * h := (commute_scalar c (h : GL (Fin d) K)).eq
    have hhI : (h : GL (Fin d) K) ∈ CatalogueBGraphForm.isometryGroup d K R :=
      Subgroup.commutator_le_self _ (by rw [← hHeq]; exact h.2)
    rw [mem_subgroupOf] at hY ⊢
    exact conj_mem_commutator_isoCent hhI hcA hY
  obtain ⟨hperf, m, L, hsup, hL⟩ := hcd
  have hfixL : ∀ i, ∀ Y : matrixDerived (oQ R), (Y : GL (Fin d) K) ∈ L i →
      oκ (oQ R) g' (projH (matrixDerived (oQ R)) Y) = projH (matrixDerived (oQ R)) Y := by
    intro i Y hY
    obtain ⟨hq, hLI, hLn⟩ := hL i
    set Lh := (L i).subgroupOf (matrixDerived (oQ R)) with hLh
    have hLhq : IsQuasisimple Lh :=
      LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe (hLI.trans hZH)).symm hq
    have hLF : Lh ≤ F := fun Z' hZ' => mem_subgroupOf.2 (hLI (mem_subgroupOf.1 hZ'))
    have hLn' : ∀ x ∈ F, ∀ l ∈ Lh, x * l * x⁻¹ ∈ Lh := by
      intro x hx l hl
      have hx' : (x : GL (Fin d) K) ∈ ⁅Z, Z⁆ := mem_subgroupOf.1 hx
      have hl' : (l : GL (Fin d) K) ∈ L i := mem_subgroupOf.1 hl
      exact mem_subgroupOf.2 (by simpa using hLn _ hx' _ hl')
    exact ClU.fix_of_lift_sub hinj hRodd hRi hRc φ
      (matrixDerivedConjugation (oQ R) g).injective hφt
      (fun Z hZ => hF1 Z hZ)
      (fun x hx Z hZ => hF2 x (by
        rw [show φ x = x from hx, inv_mul_cancel]
        exact one_mem _) Z hZ) hLF hLn' hLhq hy (mem_subgroupOf.2 hY)
  have hFsup : F ≤ MonoidHom.eqLocus ((oκ (oQ R) g').toMonoidHom.comp
      (projH (matrixDerived (oQ R)))) (projH (matrixDerived (oQ R))) := by
    intro Y hY
    have hY' : (Y : GL (Fin d) K) ∈ ⨆ i, L i := by rw [hsup]; exact mem_subgroupOf.1 hY
    have hmap : (⨆ i, (L i).subgroupOf (matrixDerived (oQ R))).map
        (matrixDerived (oQ R)).subtype = ⨆ i, L i := by
      rw [Subgroup.map_iSup]
      exact iSup_congr fun i => by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 ((hL i).2.1.trans hZH)]
    rw [← hmap] at hY'
    obtain ⟨Y', hY'L, e⟩ := hY'
    rw [← Subtype.ext e]
    refine (iSup_le fun i Z' hZ' => ?_ :
      (⨆ i, (L i).subgroupOf (matrixDerived (oQ R))) ≤ _) hY'L
    exact hfixL i Z' (mem_subgroupOf.1 hZ')
  have hperfF : ⁅F, F⁆ = F := by
    apply Subgroup.map_injective (matrixDerived (oQ R)).subtype_injective
    rw [map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hZH, hperf]
  exact kappa_eq_of_fix g' hperfF (fun Y hY => hFsup hY) (X := ⟨X, hZH hX⟩) (mem_subgroupOf.2 hX)

end

variable {n : ℕ}

theorem ClO.kron_core (hK : ringChar K ≠ 2) {R : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R) (hker : OKer (oQ R))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))))
    {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1) {c : K} (hc : c ≠ 0)
    (hA2 : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g.val.left = c • 1)
    (hcd : CompData ⁅isoCent R g.val.left, isoCent R g.val.left⁆)
    {I₀ : Finset (Fin n)} (hI₀ : 3 ≤ I₀.card)
    (hrefl : ∀ i ∈ I₀, kronGL K n (reflGL i) ∈ isoCent R g.val.left)
    (hrot : ∀ i ∈ I₀, ∀ j ∈ I₀, ∀ (hij : i ≠ j) (a b : K) (hab : a ^ 2 + b ^ 2 = 1),
      kronGL K n (rotGL i j hij hab) ∈ isoCent R g.val.left)
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))} (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ g = oκ _ g * y)
    (hRc : ∀ s, oκ _ g s = s → Odd (orderOf s) → ∀ y ∈ Ro,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro)
    {g' : similarityPairs (oQ R)} (hy : oκ _ g' ∈ Ro) :
    g'.val.right = 1 ∧
      (g'.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g.val.left =
        (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g'.val.left ∧
      (∀ X ∈ ⁅isoCent R g.val.left, isoCent R g.val.left⁆,
        (g'.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
            (X : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
          (X : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g'.val.left) ∧
      ∀ i ∈ I₀, ∀ j ∈ I₀, i ≠ j →
        (g'.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * kronI K n (signMat K {i, j}) =
          kronI K n (signMat K {i, j}) * g'.val.left := by
  have hodd := ClSp.odd_orderOf_of_mem hRodd hy
  have hτm : g'.val.right ^ orderOf (oκ _ g') = 1 := hker.right_pow_eq_one (pow_orderOf_eq_one _)
  have hfix := fun X (hX : X ∈ ⁅isoCent R g.val.left, isoCent R g.val.left⁆) =>
    ClO.cent_fix hK hR hinj hg1 hcd hRodd hRi hRc hy hX
  have hcomm2 : ∀ X Y : GL (Fin n) K, kronGL K n X ∈ isoCent R g.val.left →
      kronGL K n Y ∈ isoCent R g.val.left →
      kronGL K n ⁅X, Y⁆ ∈ ⁅isoCent R g.val.left, isoCent R g.val.left⁆ := by
    intro X Y hX hY
    rw [map_commutatorElement]
    exact commutator_mem_commutator hX hY
  obtain ⟨i, hi, j, hj, hij⟩ : ∃ i ∈ I₀, ∃ j ∈ I₀, i ≠ j := by
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (by omega : 0 < I₀.card)
    obtain ⟨j, hj⟩ := Finset.card_pos.1 (by
      have := Finset.pred_card_le_card_erase (s := I₀) (a := i); omega : 0 < (I₀.erase i).card)
    exact ⟨i, hi, j, (Finset.mem_erase.1 hj).2, Ne.symm (Finset.mem_erase.1 hj).1⟩
  have hτ1 : g'.val.right = 1 := by
    refine tau_eq_one_of_kron (D := g'.val.left) hK hij hodd hτm fun a b hab => ?_
    have e := hfix _ (hcomm2 _ _ (hrefl i hi) (hrot i hi j hj hij a b hab))
    rw [coe_kronGL] at e
    exact e
  have hfix1 : ∀ X ∈ ⁅isoCent R g.val.left, isoCent R g.val.left⁆,
      (g'.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
          (X : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
        (X : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g'.val.left := by
    intro X hX
    have e := hfix X hX
    rw [hτ1, show (X : Matrix (Fin (2 * n)) (Fin (2 * n)) K).map ⇑(1 : K ≃+* K) = X from by
      ext; rfl] at e
    calc (g'.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
          (X : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
        (g'.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
          (X : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
          (((g'.val.left⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
            (g'.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K)) := by
          rw [← Units.val_mul (g'.val.left⁻¹), inv_mul_cancel, Units.val_one, Matrix.mul_one]
      _ = (X : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g'.val.left := by
          rw [← Matrix.mul_assoc, e]
  have hd : 0 < 2 * n := by
    have := I₀.card_le_univ
    rw [Fintype.card_fin] at this
    omega
  refine ⟨hτ1, commute_of_odd_gen hd hker hg1 hτ1 hA2 hc hodd (hRi _ hy),
    hfix1, fun i' hi' j' hj' hij' => ?_⟩
  have h01 : (0 : K) ^ 2 + (1 : K) ^ 2 = 1 := by ring
  have hm := hcomm2 _ _ (hrefl i' hi') (hrot i' hi' j' hj' hij' 0 1 h01)
  have e := hfix1 _ hm
  rwa [coe_kronGL, signMat_pair_eq_commutator] at e

end CFSG.ComponentClassification.Foote5.OddLieCore
