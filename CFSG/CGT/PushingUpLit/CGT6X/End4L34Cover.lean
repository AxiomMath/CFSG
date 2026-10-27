module

public import CFSG.RankThree.PerfectCover.HopfCover
public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.LieType.Multipliers.L34Upper
public import CFSG.LieType.Steinberg.CentralExt.PSLMultiplier
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.Open.StatedDefs
public import CFSG.Assembly.Subnormal
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End4

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PerfectCover
  CFSG.LieType.Steinberg.CentralExt
open scoped commutatorElement

theorem card_center_sl3_four {K : Type} [Field K] [Fintype K] (hK : Fintype.card K = 4) :
    Nat.card (Subgroup.center (SpecialLinearGroup (Fin 3) K)) = 3 := by
  have hroots : rootsOfUnity (max (Fintype.card (Fin 3)) 1) K = rootsOfUnity 3 K := by simp
  let e2 : Subgroup.center (SpecialLinearGroup (Fin 3) K) ≃* rootsOfUnity 3 K :=
    (SpecialLinearGroup.center_equiv_rootsOfUnity).trans (MulEquiv.subgroupCongr hroots)
  rw [Nat.card_congr e2.toEquiv, SLClosed.card_rootsOfUnity_eq_gcd, hK]
  norm_num

open CFSG.Open (StatedClassicalModel)

theorem exists_cover_l34
    {L : Type} [Group L] [Finite L] [Group.IsPerfect L]
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 3 2 2)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (e : (L ⧸ Subgroup.center L) ≃* projectiveSL 3 K)
    (hodd : Odd (Nat.card (Subgroup.center L))) :
    ∃ ρ : SpecialLinearGroup (Fin 3) K →* L, ∀ g, e (QuotientGroup.mk (ρ g)) = proj 3 K g := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hperf : Group.IsPerfect (SpecialLinearGroup (Fin 3) K) :=
    LinearGroups.special_linear_isPerfect (by norm_num) (Or.inl le_rfl)
  let q₁ : SpecialLinearGroup (Fin 3) K →* L ⧸ Subgroup.center L :=
    e.symm.toMonoidHom.comp (proj 3 K)
  have hq₁ : Function.Surjective q₁ := e.symm.surjective.comp (proj_surjective 3 K)
  have hker₁ : q₁.ker = scalars 3 K := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff e.symm e.symm.injective, ← MonoidHom.mem_ker, ker_proj]
  have hker₁c : q₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
    rw [hker₁]
    exact scalars_le_center 3 K
  let q₂ : L →* L ⧸ Subgroup.center L := QuotientGroup.mk' (Subgroup.center L)
  have hq₂ : Function.Surjective q₂ := QuotientGroup.mk'_surjective _
  have hker₂ : q₂.ker = Subgroup.center L := QuotientGroup.ker_mk' _
  have hker₂c : q₂.ker ≤ Subgroup.center L := hker₂.le
  let h₁ := hopfLift q₁ hq₁ hker₁c
  let h₂ := hopfLift q₂ hq₂ hker₂c
  have hh₁ : Function.Surjective h₁ := hopfLift_surjective q₁ hq₁ hker₁c
  have hm₁ := map_hopfMultiplier_hopfLift q₁ hq₁ hker₁c
  have hm₂ := map_hopfMultiplier_hopfLift q₂ hq₂ hker₂c
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Multipliers.L34Upper.multiplier_PSL_three_four
    (L ⧸ Subgroup.center L) (Or.inl ⟨by decide, hmod⟩)
  have hM48 : Nat.card (hopfMultiplier (L ⧸ Subgroup.center L)) = 48 := by
    rw [← Nat.card_congr (hopfMultiplierEquivGriess (L ⧸ Subgroup.center L)).toEquiv,
      Nat.card_congr eM.toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 3 × ZMod 4 × ZMod 4) ≃ _),
      Nat.card_prod, Nat.card_prod, Nat.card_zmod]
    norm_num
  have hk3 : Nat.card q₁.ker = 3 := by
    rw [hker₁, scalars_eq_center]
    exact card_center_sl3_four (by rw [Fintype.card_eq_nat_card, hK])
  set M := hopfMultiplier (L ⧸ Subgroup.center L) with hM
  have hrange : (h₁.comp M.subtype).range = q₁.ker := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hm₁]
  have hN16 : Nat.card (h₁.comp M.subtype).ker = 16 := by
    have h := Subgroup.card_ker_mul_card_range (h₁.comp M.subtype)
    rw [hrange, hk3, hM48] at h
    omega
  have hker : h₁.ker ≤ h₂.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hxM : x ∈ M := by
      have h := congrArg (fun u => q₁ u) hx
      have h2 : q₁ (h₁ x) = hopfCoverMap (L ⧸ Subgroup.center L) x :=
        congrArg (fun φ => φ x) (comp_hopfLift q₁ hq₁ hker₁c)
      show hopfCoverMap (L ⧸ Subgroup.center L) x = 1
      rw [← h2, hx, map_one]
    have hxN : (⟨x, hxM⟩ : M) ∈ (h₁.comp M.subtype).ker := by
      rw [MonoidHom.mem_ker]
      exact hx
    have h16 : x ^ 16 = 1 := by
      have := pow_card_eq_one' (G := ↥(h₁.comp M.subtype).ker) (x := ⟨⟨x, hxM⟩, hxN⟩)
      rw [hN16] at this
      have h3 := congrArg
        (fun u : ↥(h₁.comp M.subtype).ker => ((u : M).1 : HopfCover (L ⧸ Subgroup.center L)))
        this
      simpa using h3
    have hmem : h₂ x ∈ Subgroup.center L := by
      have hmem' : h₂ x ∈ q₂.ker := by
        rw [← hm₂]
        exact ⟨x, hxM, rfl⟩
      exact hker₂c hmem'
    have h162 : (h₂ x) ^ 16 = 1 := by rw [← map_pow, h16, map_one]
    have hd1 : orderOf (h₂ x) ∣ 16 := orderOf_dvd_of_pow_eq_one h162
    have hd2 : orderOf (h₂ x) ∣ Nat.card (Subgroup.center L) :=
      Subgroup.orderOf_dvd_natCard (Subgroup.center L) hmem
    have hcop : Nat.Coprime 16 (Nat.card (Subgroup.center L)) := by
      have := Nat.Coprime.pow_left 4 (Nat.coprime_two_left.mpr hodd)
      simpa using this
    have h1 : orderOf (h₂ x) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
    exact orderOf_eq_one_iff.mp h1
  refine ⟨(h₁.liftOfSurjective hh₁) ⟨h₂, hker⟩, fun g => ?_⟩
  obtain ⟨u, rfl⟩ := hh₁ g
  have h3 : (h₁.liftOfSurjective hh₁) ⟨h₂, hker⟩ (h₁ u) = h₂ u :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨h₂, hker⟩ u
  rw [h3]
  have h4 : q₂ (h₂ u) = hopfCoverMap (L ⧸ Subgroup.center L) u :=
    congrArg (fun φ => φ u) (comp_hopfLift q₂ hq₂ hker₂c)
  have h5 : q₁ (h₁ u) = hopfCoverMap (L ⧸ Subgroup.center L) u :=
    congrArg (fun φ => φ u) (comp_hopfLift q₁ hq₁ hker₁c)
  have h6 : e (QuotientGroup.mk (h₂ u)) = e (hopfCoverMap (L ⧸ Subgroup.center L) u) :=
    congrArg e h4
  rw [h6, ← h5]
  simp [q₁]

theorem le_map_of_perfect_cover {L M P : Type*} [Group L] [Group M] [Group P]
    (e : L ⧸ Subgroup.center L ≃* P) (q : M →* P) (ρ : M →* L)
    (hρ : ∀ m, e (QuotientGroup.mk (ρ m)) = q m) (Y : Subgroup L) (hY : ⁅Y, Y⁆ = Y)
    (O : Subgroup M) (hYO : ∀ y ∈ Y, ∃ o ∈ O, e (QuotientGroup.mk y) = q o) : Y ≤ O.map ρ := by
  have hcomm : ∀ {a b z w : L}, (∀ g, g * z = z * g) → (∀ g, g * w = w * g) →
      ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
    intro a b z w hz hw
    have h1 : z * (b * w) * z⁻¹ = b * w := by
      rw [← hz (b * w)]; group
    have h2 : w * a⁻¹ * w⁻¹ = a⁻¹ := by
      rw [← hw a⁻¹]; group
    calc ⁅a * z, b * w⁆ = a * (z * (b * w) * z⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = a * (b * w) * a⁻¹ * w⁻¹ * b⁻¹ := by rw [h1]
      _ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by group
      _ = ⁅a, b⁆ := by rw [h2]; simp only [commutatorElement_def]
  have hdecomp : ∀ y ∈ Y, ∃ o ∈ O, ∃ z ∈ Subgroup.center L, y = ρ o * z := by
    intro y hy
    obtain ⟨o, ho, h⟩ := hYO y hy
    refine ⟨o, ho, (ρ o)⁻¹ * y, ?_, by group⟩
    have h1 : (QuotientGroup.mk (ρ o) : L ⧸ Subgroup.center L) = QuotientGroup.mk y := by
      apply e.injective
      rw [hρ, h]
    exact QuotientGroup.eq.mp h1
  have hY' : ⁅Y, Y⁆ ≤ O.map ρ := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨o₁, ho₁, z₁, hz₁, rfl⟩ := hdecomp g₁ hg₁
    obtain ⟨o₂, ho₂, z₂, hz₂, rfl⟩ := hdecomp g₂ hg₂
    rw [hcomm (Subgroup.mem_center_iff.mp hz₁) (Subgroup.mem_center_iff.mp hz₂)]
    refine ⟨⁅o₁, o₂⁆, ?_, map_commutatorElement ρ o₁ o₂⟩
    simp only [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ho₁ ho₂) (inv_mem ho₁)) (inv_mem ho₂)
  rwa [hY] at hY'

end CFSG.CGT.PushingUpLit.CGT6X.End4
