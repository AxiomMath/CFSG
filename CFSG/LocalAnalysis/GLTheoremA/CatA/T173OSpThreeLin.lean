module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ODefs
public import CFSG.RankThree.PartOne.KF.FlagSplit
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection
public import CFSG.LieType.BorelTits.Symplectic
public import CFSG.LieType.SeitzGeneration.SpHyperRad
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA
open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.PartOne.KFU
open Module
open scoped commutatorElement

variable {F : Type} [Field F] [Finite F] {ℓ : ℕ}

local notation "V" => (Fin ℓ ⊕ Fin ℓ → F)

theorem exists_isotropic_of_le_normalizer [CharP F 2] {S E : Subgroup ↥(StatedSp ℓ F)}
    (hS2 : IsPGroup 2 ↥S) (hS1 : S ≠ ⊥)
    (hE : E ≤ Subgroup.normalizer (S : Set ↥(StatedSp ℓ F))) :
    ∃ W : Submodule F (Fin ℓ ⊕ Fin ℓ → F), W ≠ ⊥ ∧
      (∀ u ∈ W, ∀ v ∈ W, spForm ℓ F u v = 0) ∧
      ∀ g ∈ E, ∀ w ∈ W, spEnd g w ∈ W := by
  obtain ⟨W, hW0, hWiso, hWE⟩ := exists_invariant_isotropic
    (CFSG.LieType.BorelTits.spForm ℓ F) (CFSG.LieType.BorelTits.natRep (StatedSp ℓ F))
    (CFSG.LieType.BorelTits.isIsometric_natRep_statedSp ℓ F)
    (CFSG.LieType.BorelTits.natRep_injective _) hS2 hS1 hE
  exact ⟨W, hW0, fun u hu v hv => by
      have h : (CFSG.LieType.BorelTits.spForm ℓ F).β u v = 0 := hWiso hv u hu
      rw [spForm_apply]
      exact h,
    fun g hg w hw => hWE g hg w hw⟩

theorem eqOn_of_fixes_flag [CharP F 2] {b : ↥(StatedSp ℓ F)} (hb3 : b ^ 3 = 1)
    {R Y : Submodule F (Fin ℓ ⊕ Fin ℓ → F)} (hbY : ∀ v ∈ Y, spEnd b v ∈ Y)
    (hbR : ∀ r ∈ R, spEnd b r = r)
    (hperp : ∀ v ∈ Y, (∀ r ∈ R, spForm ℓ F v r = 0) → v ∈ R) :
    ∀ v ∈ Y, spEnd b v = v := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hneg : ∀ x : V, -x = x := fun x => by
    funext i
    show -(x i) = x i
    exact neg_eq_of_add_eq_zero_left (G := F) (a := x i) (b := x i) (by
      rw [← two_mul, htwo, zero_mul])
  intro v hv
  have hmem : spEnd b v - v ∈ R := by
    refine hperp _ (Y.sub_mem (hbY v hv) hv) ?_
    intro r hr
    have hbinv : spEnd b⁻¹ r = r := by
      have h1 : spEnd b r = r := hbR r hr
      have h2 := congrArg (spEnd b⁻¹) h1
      rw [← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one,
        Module.End.one_apply] at h2
      exact h2.symm
    have hiso := (CFSG.LocalAnalysis.ComponentInitial.mem_sesqUnitaryGroup).mp
      (spLin_mem b) v (spEnd b⁻¹ r)
    have hbr : spEnd b (spEnd b⁻¹ r) = r := by
      rw [← Module.End.mul_apply, ← spEnd_mul, mul_inv_cancel, spEnd_one,
        Module.End.one_apply]
    rw [hbr, hbinv] at hiso
    rw [map_sub, LinearMap.sub_apply, hiso, sub_self]
  have h2v : spEnd b (spEnd b v) = v := by
    have hsub : spEnd b (spEnd b v - v) = spEnd b v - v := hbR _ hmem
    have h1 : spEnd b (spEnd b v) - spEnd b v = spEnd b v - v := by
      rw [← map_sub]
      exact hsub
    have h1' : spEnd b (spEnd b v) + spEnd b v = spEnd b v + v := by
      simpa [sub_eq_add_neg, hneg] using h1
    rw [add_comm (spEnd b v) v] at h1'
    exact add_right_cancel h1'
  have h3 : spEnd b v = v := by
    have h1 : spEnd b (spEnd b (spEnd b v)) = v := by
      have := congrArg (fun f : Module.End F V => f v) (spEnd_pow (p := 3) hb3)
      simpa [pow_three', Module.End.mul_apply] using this
    rw [h2v] at h1
    exact h1
  exact h3

theorem card_le_card_mul_pow_restrict [CharP F 2] (hF : Nat.card F = 2)
    {E N : Subgroup ↥(StatedSp ℓ F)} (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g)
    (hexp : ∀ g ∈ E, g ^ 3 = 1) {Y : Submodule F (Fin ℓ ⊕ Fin ℓ → F)}
    (hY : ∀ g ∈ E, ∀ v ∈ Y, spEnd g v ∈ Y)
    (hN : ∀ g ∈ E, (∀ v ∈ Y, spEnd g v = v) → g ∈ N) :
    Nat.card E ≤ Nat.card N * 3 ^ (finrank F Y / 2) := by
  classical
  let ρ : E →* Module.End F Y :=
    { toFun := fun g => (spEnd (g : ↥(StatedSp ℓ F))).restrict (hY g g.2)
      map_one' := by
        ext v
        simp [spEnd_one]
      map_mul' := by
        intro g h
        ext v
        simp [spEnd_mul, Module.End.mul_apply] }
  let ψ : E →* (Y ≃ₗ[F] Y) := FlagSplit.repAut ρ
  have hker : ψ.ker ≤ Subgroup.comap E.subtype N := by
    intro g hg
    rw [Subgroup.mem_comap]
    refine hN g g.2 ?_
    intro v hv
    have h1 : (ψ g : Y →ₗ[F] Y) = LinearMap.id := by
      have := congrArg (fun e : Y ≃ₗ[F] Y => (e : Y →ₗ[F] Y)) hg
      simpa using this
    have h2 := LinearMap.congr_fun h1 ⟨v, hv⟩
    simpa [ψ, ρ, FlagSplit.repAut, LinearMap.restrict_apply] using h2
  have hkerN : Nat.card ψ.ker ≤ Nat.card N := by
    refine Nat.card_le_card_of_injective
      (fun x : ψ.ker => (⟨((x.1 : E) : StatedSp ℓ F), hker x.2⟩ : N)) ?_
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : N => (z : StatedSp ℓ F)) hxy
  have hrange : Nat.card ψ.range ≤ 3 ^ (finrank F Y / 2) := by
    refine FlagSplit.card_range_le_pow_div ψ Nat.prime_three
      (CFSG.RankThree.PartOne.LIT.natCast_ne_zero_of_charTwo Nat.prime_three (by norm_num))
      (by norm_num) ?_ ?_ ?_
    · intro i hi hi2
      have hi1 : i = 1 := by omega
      subst hi1
      rw [hF]
      norm_num
    · intro g h
      exact Subtype.ext (hcomm g g.2 h h.2)
    · intro g
      exact Subtype.ext (hexp g g.2)
  have hcard : Nat.card E = Nat.card ψ.ker * Nat.card ψ.range := by
    have hq : Nat.card (E ⧸ ψ.ker) = Nat.card ψ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker, hq, mul_comm]
  calc Nat.card E = Nat.card ψ.ker * Nat.card ψ.range := hcard
    _ ≤ Nat.card N * 3 ^ (finrank F Y / 2) := Nat.mul_le_mul hkerN hrange

theorem mem_of_perp_of_lagrangian {R Y : Submodule F (Fin ℓ ⊕ Fin ℓ → F)} (hRY : R ≤ Y)
    (hY : ∀ y ∈ Y, (∀ y' ∈ Y, spForm ℓ F y y' = 0) → y = 0)
    (hR : ∀ u ∈ R, ∀ v ∈ R, spForm ℓ F u v = 0)
    (hdim : finrank F Y = 2 * finrank F R) :
    ∀ v ∈ Y, (∀ r ∈ R, spForm ℓ F v r = 0) → v ∈ R := by
  intro v hv hvR
  let B' : LinearMap.BilinForm F Y := (spForm ℓ F).restrict Y
  let R' : Submodule F Y := R.comap Y.subtype
  have hB' : B'.Nondegenerate := by
    refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft ?_
    intro x hx
    apply Subtype.ext
    refine hY x.1 x.2 fun y' hy' => ?_
    have h := hx ⟨y', hy'⟩
    simpa [B', LinearMap.BilinForm.restrict_apply] using h
  have hR'dim : finrank F ↥R' = finrank F ↥R :=
    (Submodule.comapSubtypeEquivOfLe hRY).finrank_eq
  have hR' : R' ≤ B'.orthogonal R' := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    have hxR : x.1 ∈ R := by simpa [R', Submodule.mem_comap] using hx
    have hyR : y.1 ∈ R := by simpa [R', Submodule.mem_comap] using hy
    have h := hR y.1 hyR x.1 hxR
    simpa [B', LinearMap.BilinForm.restrict_apply] using h
  have horth : finrank F ↥(B'.orthogonal R') = finrank F ↥R' := by
    rw [LinearMap.BilinForm.finrank_orthogonal hB' R', hdim, hR'dim]
    omega
  have heq : R' = B'.orthogonal R' :=
    Submodule.eq_of_le_of_finrank_le hR' (le_of_eq horth)
  have hv' : (⟨v, hv⟩ : Y) ∈ B'.orthogonal R' := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    have hyR : y.1 ∈ R := by simpa [R', Submodule.mem_comap] using hy
    have h := hvR y.1 hyR
    have h' : spForm ℓ F y.1 v = 0 := by
      have hneg := LinearMap.BilinForm.IsAlt.neg_eq spForm_isAlt y.1 v
      rw [h] at hneg
      exact neg_eq_zero.mp hneg
    simpa [B', LinearMap.BilinForm.restrict_apply] using h'
  rw [← heq] at hv'
  simpa [R', Submodule.mem_comap] using hv'

theorem spEnd_commutator_transvection [CharP F 2] {u v : Fin ℓ ⊕ Fin ℓ → F}
    (huv : spForm ℓ F u v = 1) (x : Fin ℓ ⊕ Fin ℓ → F) :
    spEnd ⁅spTransvection u (1 : F), spTransvection v (1 : F)⁆ x =
      x + spForm ℓ F x u • u + (spForm ℓ F x u + spForm ℓ F x v) • v := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hnegF : ∀ a : F, -a = a := fun a => by
    refine neg_eq_of_add_eq_zero_left ?_
    rw [← two_mul, htwo, zero_mul]
  have hvu : spForm ℓ F v u = 1 := by
    have h := LinearMap.BilinForm.IsAlt.neg_eq spForm_isAlt v u
    rw [huv] at h
    rw [hnegF] at h
    exact h
  have huu : spForm ℓ F u u = 0 := spForm_isAlt.self_eq_zero u
  have hvv : spForm ℓ F v v = 0 := spForm_isAlt.self_eq_zero v
  rw [commutatorElement_def, spEnd_mul, spEnd_mul, spEnd_mul, spTransvection_inv,
    spTransvection_inv]
  have h3 : (3 : F) = 1 := by
    rw [show (3 : F) = 1 + 2 by norm_num, htwo, add_zero]
  have h4 : (4 : F) = 0 := by
    rw [show (4 : F) = 2 + 2 by norm_num, htwo, add_zero]
  simp only [Module.End.mul_apply, spEnd_spTransvection, map_add, map_smul, one_mul,
    one_smul, smul_eq_mul, hvu, huu, hvv, huv, add_zero, zero_add, zero_smul, mul_zero, hnegF,
    htwo, h3, h4, mul_one]
  have h2V : ∀ w : V, w + w = 0 := fun w => by
    rw [← two_smul F w, htwo, zero_smul]
  linear_combination (norm := module)
    (spForm ℓ F x u + 2 * spForm ℓ F x v) • h2V u + spForm ℓ F x v • h2V v

theorem commutator_transvection_pow_three [CharP F 2] {u v : Fin ℓ ⊕ Fin ℓ → F}
    (huv : spForm ℓ F u v = 1) :
    ⁅spTransvection u (1 : F), spTransvection v (1 : F)⁆ ^ 3 = 1 := by
  set c : ↥(StatedSp ℓ F) := ⁅spTransvection u (1 : F), spTransvection v (1 : F)⁆
  have hc : ∀ x : V, spEnd c x =
      x + spForm ℓ F x u • u + (spForm ℓ F x u + spForm ℓ F x v) • v :=
    spEnd_commutator_transvection huv
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hnegF : ∀ a : F, -a = a := fun a => by
    refine neg_eq_of_add_eq_zero_left ?_
    rw [← two_mul, htwo, zero_mul]
  have hinj : Function.Injective (spEnd (r := ℓ) (K := F)) := by
    intro a b h
    exact spLin_injective (Units.ext h)
  have hsp : spEnd (c ^ 3) = spEnd c ^ 3 :=
    CFSG.LieType.SeitzGeneration.spEnd_pow c 3
  apply hinj
  rw [hsp, spEnd_one]
  apply LinearMap.ext
  intro x
  have hvu : spForm ℓ F v u = 1 := by
    have h := LinearMap.BilinForm.IsAlt.neg_eq spForm_isAlt v u
    rw [huv] at h
    rw [hnegF] at h
    exact h
  have huu : spForm ℓ F u u = 0 := spForm_isAlt.self_eq_zero u
  have hvv : spForm ℓ F v v = 0 := spForm_isAlt.self_eq_zero v
  have h2V : ∀ w : V, w + w = 0 := fun w => by
    rw [← two_smul F w, htwo, zero_smul]
  have hc2 : spEnd c (spEnd c x) = x + (spForm ℓ F x u + spForm ℓ F x v) • u +
      spForm ℓ F x v • v := by
    rw [hc, hc]
    simp only [map_add, map_smul, one_smul, smul_eq_mul, hvu, huu, hvv, huv, hnegF, htwo,
      LinearMap.add_apply, LinearMap.smul_apply, add_zero, zero_add, zero_smul, mul_zero,
      mul_one]
    linear_combination (norm := module) (spForm ℓ F x u) • h2V u +
      (2 * spForm ℓ F x u + spForm ℓ F x v) • h2V v
  calc (spEnd c ^ 3) x = spEnd c (spEnd c (spEnd c x)) := by
        rw [pow_three']
        simp only [Module.End.mul_apply]
    _ = x := by
        rw [hc2, hc]
        simp only [map_add, map_smul, one_smul, smul_eq_mul, hvu, huu, hvv, huv, hnegF, htwo,
          LinearMap.add_apply, LinearMap.smul_apply, add_zero, zero_add, zero_smul, mul_zero,
          mul_one]
        linear_combination (norm := module) (spForm ℓ F x u + spForm ℓ F x v) • h2V u +
          (spForm ℓ F x u + 2 * spForm ℓ F x v) • h2V v

theorem false_of_isotropic_of_move {W : Submodule F (Fin ℓ ⊕ Fin ℓ → F)}
    (hW : ∀ u ∈ W, ∀ v ∈ W, spForm ℓ F u v = 0) {κ : ↥(StatedSp ℓ F)}
    (hκ : ∀ w ∈ W, spEnd κ w ∈ W) {u v : Fin ℓ ⊕ Fin ℓ → F} (hu : u ∈ W)
    (hmove : spEnd κ u - u = v) (huv : spForm ℓ F u v = 1) : False := by
  have hv : v ∈ W := by
    rw [← hmove]
    exact W.sub_mem (hκ u hu) hu
  have h := hW u hu v hv
  rw [huv] at h
  exact one_ne_zero h

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
