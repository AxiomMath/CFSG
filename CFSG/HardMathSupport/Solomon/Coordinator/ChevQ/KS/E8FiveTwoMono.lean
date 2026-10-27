module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveOneSylow
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoWeyl
public import CFSG.LieType.AlgebraicGroups.E6GraphCentralizerRationalBase
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five

namespace Two

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.KE8F CFSG.RankThree.Lattice
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec)
open One (sylowW)

set_option linter.unusedSectionVars false

section Row


theorem mulVec_four_mod {M : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ}
    (hM : ∀ j, (5 : ℤ) ∣ M 4 j - if j = 4 then 1 else 0) (v : Fin Tag.E8.rank → ℤ) :
    (M.mulVec v) 4 % 5 = v 4 % 5 := by
  have h1 : (M.mulVec v) 4 - v 4 = ∑ j, (M 4 j - if j = 4 then 1 else 0) * v j := by
    simp only [Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h2 : (5 : ℤ) ∣ (M.mulVec v) 4 - v 4 := by
    rw [h1]
    exact Finset.dvd_sum fun j _ => Dvd.dvd.mul_right (hM j) _
  omega

theorem e8FiveG1_fix (v : Fin Tag.E8.rank → ℤ) : (e8FiveG1 • v) 4 % 5 = v 4 % 5 := by
  rw [← weylMatrix_mulVec, weylMatrix_e8FiveG1]
  exact mulVec_four_mod (by decide +kernel) v

theorem e8FiveG2_fix (v : Fin Tag.E8.rank → ℤ) : (e8FiveG2 • v) 4 % 5 = v 4 % 5 := by
  rw [← weylMatrix_mulVec, weylMatrix_e8FiveG2]
  exact mulVec_four_mod (by decide +kernel) v

theorem sylowW_fix_z : ∀ w ∈ sylowW,
    ∀ v : Fin Tag.E8.rank → ℤ, (w • v) 4 % 5 = v 4 % 5 := by
  let H : Subgroup (WeylGroup Tag.E8) :=
    { carrier := {w | ∀ v : Fin Tag.E8.rank → ℤ, (w • v) 4 % 5 = v 4 % 5}
      one_mem' := fun v => by simp
      mul_mem' := fun {w w'} hw hw' v => by
        show ((w * w') • v) 4 % 5 = v 4 % 5
        rw [mul_smul, hw, hw']
      inv_mem' := fun {w} hw v => by
        show (w⁻¹ • v) 4 % 5 = v 4 % 5
        have := hw (w⁻¹ • v)
        rw [smul_inv_smul] at this
        exact this.symm }
  have hle : sylowW ≤ H := by
    unfold sylowW
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]; exact e8FiveG1_fix
    · rw [hx]; exact e8FiveG2_fix
  exact fun w hw => hle hw

end Row

section Conj


theorem rootChar_mulSingle {L : Type} [Field L] (u : Lˣ) (v : Fin Tag.E8.rank → ℤ) :
    rootChar (Pi.mulSingle (4 : Fin Tag.E8.rank) u) v = u ^ (v 4) := by
  unfold rootChar
  rw [Finset.prod_eq_single (4 : Fin Tag.E8.rank)]
  · simp
  · intro j _ hj
    simp [Pi.mulSingle_eq_of_ne hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem monomial_commute_z {K₂ L : Type} [Field K₂] [Field L] (ψ : K₂ →+* L)
    {m : ModGL Tag.E8 K₂} (hm : m ∈ monomialSubgroup Tag.E8 K₂)
    (hW : weylQuotientHom Tag.E8 K₂ ⟨m, hm⟩ ∈
      sylowW)
    {u : Lˣ} (hu : IsPrimitiveRoot u 5) :
    baseChangeGL ψ m * rootDiagUnit Tag.E8 (Pi.mulSingle (4 : Fin Tag.E8.rank) u) =
      rootDiagUnit Tag.E8 (Pi.mulSingle (4 : Fin Tag.E8.rank) u) * baseChangeGL ψ m := by
  have hn : baseChangeGL ψ m ∈ monomialSubgroup Tag.E8 L := baseChangeGL_mem_monomialSubgroup ψ hm
  have hmaps : MapsRootLines (baseChangeGL ψ m) (weylQuotientHom Tag.E8 K₂ ⟨m, hm⟩) :=
    CFSG.LieType.AlgebraicGroups.MapsRootLines.baseChangeGL ψ
      (mapsRootLines_weylQuotientHom ⟨m, hm⟩)
  have hq : weylQuotientHom Tag.E8 L ⟨baseChangeGL ψ m, hn⟩ =
      weylQuotientHom Tag.E8 K₂ ⟨m, hm⟩ := weylQuotientHom_eq hmaps
  have hact : weylAct (weylQuotientHom Tag.E8 K₂ ⟨m, hm⟩) (Pi.mulSingle (4 : Fin Tag.E8.rank) u) =
      Pi.mulSingle (4 : Fin Tag.E8.rank) u := by
    apply eq_of_rootChar_eq
    intro v
    rw [rootChar_weylAct, rootChar_mulSingle, rootChar_mulSingle]
    exact zpow_eq_zpow_of_modEq hu (sylowW_fix_z _ (inv_mem hW) v)
  have h := monomial_conj_rootDiagUnit (⟨baseChangeGL ψ m, hn⟩ : monomialSubgroup Tag.E8 L)
    (Pi.mulSingle (4 : Fin Tag.E8.rank) u)
  rw [hq, hact] at h
  exact (mul_inv_eq_iff_eq_mul.1 h)

theorem exists_conj_commute_z {K : Type} [Field K] [Finite K] (hK5 : 5 ∣ Nat.card K + 1)
    {L : Type} [Field L] [Algebra K L] [IsAlgClosed L] {ζ : L} (hζ : IsPrimitiveRoot ζ 5)
    {E₀ : Subgroup (adjointGroup Tag.E8 K)} (hE₀ : IsPGroup 5 E₀) :
    ∃ γ ∈ adjointGroup Tag.E8 L, ∀ x ∈ E₀,
      (γ * baseChangeGL (algebraMap K L) (x : ModGL Tag.E8 K) * γ⁻¹) * griessZ hζ =
        griessZ hζ * (γ * baseChangeGL (algebraMap K L) (x : ModGL Tag.E8 K) * γ⁻¹) := by
  classical
  obtain ⟨p, hp⟩ := CharP.exists K
  haveI : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  haveI : CharP K p := hp
  let K₂ : Type := FiniteField.Extension K p 2
  have hcard : Nat.card K₂ = Nat.card K ^ 2 := FiniteField.natCard_extension K p 2
  have h5₂ : 5 ∣ Nat.card K₂ - 1 := by
    rw [hcard]
    have h1 := Nat.sq_sub_sq (Nat.card K) 1
    rw [one_pow] at h1
    rw [h1]
    exact Dvd.dvd.mul_right hK5 _
  set f : adjointGroup Tag.E8 K →* adjointGroup Tag.E8 K₂ :=
    adjointBaseChangeHom Tag.E8 (algebraMap K K₂) with hf
  set Q : Subgroup (adjointGroup Tag.E8 K₂) := E₀.map f with hQ
  have hQp : IsPGroup 5 Q := by
    intro g
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 g.2
    obtain ⟨k, hk⟩ := hE₀ ⟨x, hx⟩
    refine ⟨k, Subtype.ext ?_⟩
    have : x ^ 5 ^ k = 1 := congrArg Subtype.val hk
    rw [Subgroup.coe_pow, ← hxg, ← map_pow, this, map_one]
    rfl
  obtain ⟨c, hcN, hcW⟩ := One.exists_conj_monomialN_weyl_le K₂ h5₂ hQp
  haveI : Algebra.IsAlgebraic K K₂ := Algebra.IsAlgebraic.of_finite K K₂
  let ψ : K₂ →ₐ[K] L := IsAlgClosed.lift
  refine ⟨baseChangeGL ψ.toRingHom (c : ModGL Tag.E8 K₂),
    (adjointBaseChangeHom Tag.E8 ψ.toRingHom c).2, fun x hx => ?_⟩
  have hfx : f x ∈ Q := Subgroup.mem_map.2 ⟨x, hx, rfl⟩
  have hm := hcN (f x) hfx
  have hmono : ((c * f x * c⁻¹ : adjointGroup Tag.E8 K₂) : ModGL Tag.E8 K₂) ∈
      monomialSubgroup Tag.E8 K₂ := hm
  have hW := hcW (f x) hfx
  have hcomm := monomial_commute_z ψ.toRingHom hmono hW (griessU_prim hζ)
  have hι : baseChangeGL (algebraMap K L) (x : ModGL Tag.E8 K) =
      baseChangeGL ψ.toRingHom (baseChangeGL (algebraMap K K₂) (x : ModGL Tag.E8 K)) := by
    rw [baseChangeGL_baseChangeGL]
    congr 2
    exact RingHom.ext fun a => (ψ.commutes a).symm
  have himg : baseChangeGL ψ.toRingHom (c : ModGL Tag.E8 K₂) *
      baseChangeGL (algebraMap K L) (x : ModGL Tag.E8 K) *
      (baseChangeGL ψ.toRingHom (c : ModGL Tag.E8 K₂))⁻¹ =
      baseChangeGL ψ.toRingHom ((c * f x * c⁻¹ : adjointGroup Tag.E8 K₂) : ModGL Tag.E8 K₂) := by
    rw [hι]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hf,
      coe_adjointBaseChangeHom]
  have hz : griessZ hζ = rootDiagUnit Tag.E8 (Pi.mulSingle (4 : Fin Tag.E8.rank) (griessU hζ)) := by
    rw [griessZ, powVec_czVec]
  rw [himg, hz]
  exact hcomm

end Conj

end Two

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five
