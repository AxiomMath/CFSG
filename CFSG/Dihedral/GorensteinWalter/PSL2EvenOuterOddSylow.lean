module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
import CFSG.Quasithin.SteinbergOuterPrimeControl
import CFSG.RankThree.PartOne.CTP.SeitzL2
import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.PGammaL2ProjectiveHilbert90
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear

public section

namespace CFSG

noncomputable section

namespace GorensteinWalter

open scoped MatrixGroups
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem psl2_even_exists_sylow_fixed_of_pow_mem_inner_eq_one
    {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) {z : MulAut (PSL2 F)} (hzodd : Odd (orderOf z))
    (hz : ∀ k : ℕ, z ^ k ∈ (MulAut.conj : PSL2 F →* MulAut (PSL2 F)).range →
      z ^ k = 1) :
    ∃ ω : Sylow 2 (PSL2 F), z • ω = ω := by
  classical
  let γ : PGammaL2 F := (semilinearEquivAut F).symm z
  have hγz : semilinearAction F γ = z := (semilinearEquivAut F).apply_symm_apply z
  have hγord : orderOf γ = orderOf z := by
    rw [← MulEquiv.orderOf_eq (semilinearEquivAut F) γ]
    exact congrArg orderOf ((semilinearEquivAut F).apply_symm_apply z)
  have hγodd : Odd (orderOf γ) := by
    rw [hγord]
    exact hzodd
  set r : ℕ := orderOf γ.right with hrdef
  have hγr_right : (γ ^ r).right = 1 := by
    rw [hrdef]
    change SemidirectProduct.rightHom (γ ^ orderOf γ.right) = 1
    rw [map_pow]
    exact pow_orderOf_eq_one _
  have hγr_odd : Odd (orderOf (γ ^ r)) :=
    Odd.of_dvd_nat hγodd (orderOf_pow_dvd r)
  obtain ⟨k, hk⟩ := hγr_odd
  have hpow : (γ ^ r) ^ (2 * k + 1) = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one (γ ^ r)
  have hγr_psl : γ ^ r ∈ pGammaL2PSLRange F :=
    @CFSG.RankThree.PartOne.CTP.mem_pslRange_of_odd_pow F _ _ (γ ^ r) hγr_right k hpow
  have hzr_inner : z ^ r ∈
      (MulAut.conj : PSL2 F →* MulAut (PSL2 F)).range := by
    obtain ⟨y, hy⟩ := hγr_psl
    refine ⟨y, ?_⟩
    have hy' : γ ^ r = CFSG.ComponentClassification.AutL2Facts.incl F y := hy.symm
    calc MulAut.conj y
        = semilinearAction F (CFSG.ComponentClassification.AutL2Facts.incl F y) :=
          (CFSG.ComponentClassification.AutL2Facts.semilinearAction_incl F y).symm
      _ = semilinearAction F (γ ^ r) := by rw [hy']
      _ = (semilinearAction F γ) ^ r := map_pow (semilinearAction F) γ r
      _ = z ^ r := by rw [hγz]
  have hγr_one : γ ^ r = 1 := by
    have h : z ^ r = 1 := hz r hzr_inner
    apply (semilinearEquivAut F).injective
    rw [map_pow, map_one]
    change semilinearAction F γ ^ r = 1
    rw [hγz, h]
  have hγr_one' : γ ^ orderOf γ.right = 1 := by
    rw [← hrdef]
    exact hγr_one
  obtain ⟨C, hC⟩ := pGammaL2_conj_inr_of_pow_eq_one γ hγr_one'
  have hzdecomp : z = pglAction F C * psl2FieldAut F γ.right * (pglAction F C)⁻¹ := by
    have h := congrArg (semilinearAction F) hC
    rw [map_mul, map_mul, map_inv, semilinearAction_inl, semilinearAction_inr] at h
    rw [hγz] at h
    calc z = pglAction F C * ((pglAction F C)⁻¹ * z * pglAction F C) *
          (pglAction F C)⁻¹ := by group
      _ = pglAction F C * psl2FieldAut F γ.right * (pglAction F C)⁻¹ := by rw [h]
  let Sinf : Sylow 2 (PSL2 F) :=
    psl2ProjectiveLineEquivSylow F hF (psl2ProjectiveInfinity F)
  have hfS : psl2FieldAut F γ.right • Sinf = Sinf := by
    have h1 :=
      CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_projectiveLine_infinity
        F hF γ.right
    rw [psl2MulAutProjectiveLine_apply] at h1
    have h2 := congrArg (psl2ProjectiveLineEquivSylow F hF) h1
    rwa [Equiv.apply_symm_apply] at h2
  exact ⟨pglAction F C • Sinf, by
    rw [hzdecomp, mul_smul, mul_smul, inv_smul_smul, hfS]⟩

theorem psl2_even_exists_sylow_fixed_of_inf_inner_eq_bot
    {F : Type} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (A : Subgroup (MulAut (PSL2 F)))
    (hodd : Odd (Nat.card A))
    (hA : A ⊓ (MulAut.conj : PSL2 F →* MulAut (PSL2 F)).range = ⊥) :
    ∃ ω : Sylow 2 (PSL2 F), ∀ a ∈ A, a • ω = ω := by
  classical
  have hn : n ≠ 0 := by
    rintro rfl
    have h1 : Nat.card F = 1 := by simpa using hF
    have h2 := Finite.one_lt_card (α := F)
    omega
  have hev : Even (Nat.card F) := by
    rw [hF]
    exact Nat.even_pow.2 ⟨even_two, hn⟩
  have hcycOuter :
      IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer (PSL2 F)) :=
    CFSG.Quasithin.OuterPrimeControl.outer_psl2_isCyclic F (Or.inl hev)
  let f : A →* CFSG.ComponentClassification.OuterAutomorphisms.Outer (PSL2 F) :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (PSL2 F))).comp
      A.subtype
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : f (a⁻¹ * b) = 1 := by
      rw [map_mul, map_inv, hab, inv_mul_cancel]
    have hmem : ((a⁻¹ * b : A) : MulAut (PSL2 F)) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (PSL2 F) := by
      refine (QuotientGroup.eq_one_iff _).mp ?_
      simpa [f, QuotientGroup.mk'_apply] using h1
    have hbot : ((a⁻¹ * b : A) : MulAut (PSL2 F)) ∈
        (⊥ : Subgroup (MulAut (PSL2 F))) := by
      rw [← hA]
      exact ⟨(a⁻¹ * b).2, hmem⟩
    have h2 : ((a⁻¹ * b : A) : MulAut (PSL2 F)) = 1 := Subgroup.mem_bot.mp hbot
    apply Subtype.ext
    have h3 : (a : MulAut (PSL2 F))⁻¹ * b = 1 := by simpa using h2
    exact inv_mul_eq_one.mp h3
  have hcyc : IsCyclic A :=
    @isCyclic_of_injective A
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (PSL2 F)) _ _ hcycOuter f hf
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := A)
  let z : MulAut (PSL2 F) := (g : MulAut (PSL2 F))
  have hzodd : Odd (orderOf z) :=
    Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard A g.2)
  have hzinner : ∀ k : ℕ,
      z ^ k ∈ (MulAut.conj : PSL2 F →* MulAut (PSL2 F)).range → z ^ k = 1 := by
    intro k hk
    have hzA : z ^ k ∈ A := by
      change (g : MulAut (PSL2 F)) ^ k ∈ A
      exact pow_mem g.2 k
    have hbot : z ^ k ∈ (⊥ : Subgroup (MulAut (PSL2 F))) := by
      rw [← hA]
      exact ⟨hzA, hk⟩
    exact Subgroup.mem_bot.mp hbot
  obtain ⟨ω, hω⟩ :=
    psl2_even_exists_sylow_fixed_of_pow_mem_inner_eq_one hF hzodd hzinner
  refine ⟨ω, fun a ha => ?_⟩
  have hgen : (⟨a, ha⟩ : A) ∈ Subgroup.zpowers g := hg ⟨a, ha⟩
  obtain ⟨k, hk⟩ :=
    (mem_powers_iff_mem_zpowers (x := g) (y := (⟨a, ha⟩ : A))).2 hgen
  have hk' : z ^ k = a := by
    have := congrArg (Subgroup.subtype A) hk
    simpa [z] using this
  have hpow : ∀ k : ℕ, z ^ k • ω = ω := by
    intro k
    induction k with
    | zero => rw [pow_zero, one_smul]
    | succ k ih => rw [pow_succ, mul_smul, hω, ih]
  rw [← hk']
  exact hpow k

end GorensteinWalter

end

end CFSG
