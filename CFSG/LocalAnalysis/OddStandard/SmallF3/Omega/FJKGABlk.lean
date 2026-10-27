module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGABlock
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClKL2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GTGen
import CFSG.GH74.Uniqueness.Bender.Frame311
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrSix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def fjOmegaInl (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1) :
    omegaGroup (nondegenerate_restrict_fixSp hQ hs) →* omegaGroup hQ :=
  (((blockHom hs).comp (MonoidHom.inl _ _)).comp
    (omegaGroup (nondegenerate_restrict_fixSp hQ hs)).subtype).codRestrict (omegaGroup hQ)
    (fun a => cl_blockHom_left_mem_omegaGroup hQ hs a.2)

theorem coe_fjOmegaInl (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (a : omegaGroup (nondegenerate_restrict_fixSp hQ hs)) :
    ((fjOmegaInl hQ hs a : omegaGroup hQ) : OGroup Q) =
      blockHom hs ((a : OGroup (Q.restrict (fixSp s))), 1) :=
  rfl

theorem clFixHom_eq_comp (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1) :
    clFixHom hQ hs = (omegaToProj hQ).comp (fjOmegaInl hQ hs) :=
  rfl

@[expose] noncomputable def fjOmegaInr (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1) :
    omegaGroup (nondegenerate_restrict_commSp hQ hs) →* omegaGroup hQ :=
  (((blockHom hs).comp (MonoidHom.inr _ _)).comp
    (omegaGroup (nondegenerate_restrict_commSp hQ hs)).subtype).codRestrict (omegaGroup hQ)
    (fun b => cl_blockHom_right_mem_omegaGroup hQ hs b.2)

theorem omegaInr_eq_fjOmegaInr (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (hU : 2 ≤ Module.finrank (ZMod 3) (commSp s)) : omegaInr hQ hs hU = fjOmegaInr hQ hs :=
  rfl

theorem fj_blockHom_inl_conj (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1) {c : OGroup Q}
    (hc : c ∈ Subgroup.centralizer ({s} : Set (OGroup Q))) (a : OGroup (Q.restrict (fixSp s))) :
    ∃ c₁ : OGroup (Q.restrict (fixSp s)),
      c * blockHom hs (a, 1) * c⁻¹ = blockHom hs (c₁ * a * c₁⁻¹, 1) := by
  rw [← range_blockHom hQ hs] at hc
  obtain ⟨p, rfl⟩ := hc
  refine ⟨p.1, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  ext <;> simp

theorem fj_isComponentIn_clFixHom (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (hU : 0 < Module.finrank (ZMod 3) (commSp s))
    (hq : CFSG.IsQuasisimple (omegaGroup (nondegenerate_restrict_fixSp hQ hs))) :
    IsComponentIn (clFixHom hQ hs).range (fixSub (projAut hQ s)) := by
  have hinj := cl_clFixHom_injective hQ hs hU
  let φ : omegaGroup (nondegenerate_restrict_fixSp hQ hs) ≃* (clFixHom hQ hs).range :=
    MonoidHom.ofInjective hinj
  have hquasi : CFSG.IsQuasisimple ↥(clFixHom hQ hs).range :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv φ hq
  have hKle : (fjOmegaInl hQ hs).range ≤ cOmega hQ s := by
    rintro _ ⟨a, rfl⟩
    rw [mem_cOmega_iff, coe_fjOmegaInl]
    have hmem : blockHom hs ((a : OGroup (Q.restrict (fixSp s))), 1) ∈
        Subgroup.centralizer ({s} : Set (OGroup Q)) := by
      rw [← range_blockHom hQ hs]
      exact ⟨(_, 1), rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp hmem
  have hKn : ∀ g ∈ cOmega hQ s, ∀ k ∈ (fjOmegaInl hQ hs).range,
      g * k * g⁻¹ ∈ (fjOmegaInl hQ hs).range := by
    intro g hg k hk
    obtain ⟨a, rfl⟩ := hk
    have hgc : (g : OGroup Q) ∈ Subgroup.centralizer ({s} : Set (OGroup Q)) := hg
    obtain ⟨c₁, hc₁⟩ := fj_blockHom_inl_conj hQ hs hgc (a : OGroup _)
    have hmem : c₁ * (a : OGroup _) * c₁⁻¹ ∈ omegaGroup (nondegenerate_restrict_fixSp hQ hs) :=
      (omegaGroup_normal _).conj_mem _ a.2 c₁
    refine ⟨⟨c₁ * (a : OGroup _) * c₁⁻¹, hmem⟩, ?_⟩
    apply Subtype.ext
    exact hc₁.symm
  have hmap : (fjOmegaInl hQ hs).range.map (omegaToProj hQ) = (clFixHom hQ hs).range :=
    MonoidHom.map_range _ _
  rw [← hmap]
  exact isComponentIn_fix hQ hs hKle hKn (by rw [hmap]; exact hquasi)

theorem fj_odd_block_comm (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (hW : Module.finrank (ZMod 3) (fixSp s) ≤ 2) {g : OGroup Q}
    (hg : g ∈ Subgroup.centralizer ({s} : Set (OGroup Q))) (hodd : Odd (orderOf g)) :
    ∃ b ∈ omegaGroup (nondegenerate_restrict_commSp hQ hs), blockHom hs (1, b) = g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← range_blockHom hQ hs] at hg
  obtain ⟨⟨p, c⟩, rfl⟩ := MonoidHom.mem_range.mp hg
  have hord : orderOf (p, c) = orderOf (blockHom hs (p, c)) :=
    (orderOf_injective (blockHom hs) (blockHom_injective hs) _).symm
  have hlcm : orderOf (p, c) = Nat.lcm (orderOf p) (orderOf c) := Prod.orderOf (p, c)
  have hoddpc : Odd (orderOf (p, c)) := hord ▸ hodd
  have hcodd : Odd (orderOf c) := hoddpc.of_dvd_nat (hlcm ▸ Nat.dvd_lcm_right _ _)
  have hpodd : Odd (orderOf p) := hoddpc.of_dvd_nat (hlcm ▸ Nat.dvd_lcm_left _ _)
  have hP := fj_isPGroup_two_oGroup_of_finrank_le_two (nondegenerate_restrict_fixSp hQ hs) hW
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) p
  have hk0 : k = 0 := by
    by_contra hne
    have h2 : 2 ∣ orderOf p := hk ▸ dvd_pow_self 2 hne
    exact (Nat.not_even_iff_odd.mpr hpodd) (even_iff_two_dvd.mpr h2)
  have hp1 : p = 1 := by
    rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  subst hp1
  exact ⟨c, CFSG.GH74.Uniqueness.Bender.mem_of_mul_self_mem_of_odd hcodd
    (mul_self_mem_omegaGroup (nondegenerate_restrict_commSp hQ hs) c), rfl⟩

theorem fj_le_fixBlock_of_finrank_le_two (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (hU : Module.finrank (ZMod 3) (commSp s) ≤ 2) {K : Subgroup (omegaGroup hQ)}
    (hK : K ≤ cOmega hQ s) (hKsl : IsSL23Mod K) : K ≤ (fjOmegaInl hQ hs).range := by
  haveI : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  haveI : Finite (omegaGroup hQ) := Subtype.finite
  refine (l34g_le_closure_odd hKsl).trans ?_
  rw [Subgroup.closure_le]
  rintro c ⟨hcK, hcodd⟩
  have hcc : (c : OGroup Q) ∈ Subgroup.centralizer ({s} : Set (OGroup Q)) := hK hcK
  have hodd' : Odd (orderOf (c : OGroup Q)) := by
    rw [Subgroup.orderOf_coe]
    exact hcodd
  obtain ⟨p, hp, hpc⟩ := fj_odd_block_fix hQ hs hU hcc hodd'
  exact ⟨⟨p, hp⟩, Subtype.ext hpc⟩

theorem fj_le_commBlock_of_finrank_le_two (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (hW : Module.finrank (ZMod 3) (fixSp s) ≤ 2) {K : Subgroup (omegaGroup hQ)}
    (hK : K ≤ cOmega hQ s) (hKsl : IsSL23Mod K) : K ≤ (fjOmegaInr hQ hs).range := by
  haveI : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  haveI : Finite (omegaGroup hQ) := Subtype.finite
  refine (l34g_le_closure_odd hKsl).trans ?_
  rw [Subgroup.closure_le]
  rintro c ⟨hcK, hcodd⟩
  have hcc : (c : OGroup Q) ∈ Subgroup.centralizer ({s} : Set (OGroup Q)) := hK hcK
  have hodd' : Odd (orderOf (c : OGroup Q)) := by
    rw [Subgroup.orderOf_coe]
    exact hcodd
  obtain ⟨b, hb, hbc⟩ := fj_odd_block_comm hQ hs hW hcc hodd'
  exact ⟨⟨b, hb⟩, Subtype.ext hbc⟩

end CFSG.OddStandard.SmallF3.Omega
