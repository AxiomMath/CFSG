module

public import CFSG.ClassicalInvolution.Asc77.AscR10E9
public import CFSG.ClassicalInvolution.Asc77.AscR10E2
public import CFSG.ClassicalInvolution.Asc77.AscR10E5
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E7Pair
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E7Main
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryE7Main
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2IsogenyE7
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2InterfaceE7
public import CFSG.ClassicalInvolution.Asc77.AscR10E10

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts.Levi



open CFSG.ClassicalInvolution.Asc77.T3CII (GenSq eq_of_map_eq_of_genSq
  commute_of_map_commute_of_genSq)

section Iface

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.ModelFacts
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)

variable {p e : ℕ} [Fact p.Prime]

@[expose] def A2UnitaryE7_three (p e : ℕ) [Fact p.Prime] : Prop :=
  StatedLieAdmissible .E7 0 p e → p ≠ 2 → p ^ e = 3 →
    ∀ (R₂ : Subgroup (E7sc p e)) (c₂ : E7sc p e),
      R₂ ∈ longestFundamental (e7Datum (GaloisField p e)) → c₂ ∈ R₂ → orderOf c₂ = 2 →
      ((e7Isogeny (GaloisField p e) c₂ : ↥(adjointGroup .E7 (GaloisField p e))) :
        ModGL .E7 (GaloisField p e)) * signDiagE7 (GaloisField p e) thetaE7 =
        signDiagE7 (GaloisField p e) thetaE7 *
          ((e7Isogeny (GaloisField p e) c₂ : ↥(adjointGroup .E7 (GaloisField p e))) :
            ModGL .E7 (GaloisField p e)) →
      ¬ (∀ r ∈ stdRankOne (e7Datum (GaloisField p e)) thetaE7, c₂ * r = r * c₂) →
      (∃ v ∈ h1E7 (AlgClosGF p e),
        v * baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e))
            ((e7Isogeny (GaloisField p e) c₂ : ↥(adjointGroup .E7 (GaloisField p e))) :
              ModGL .E7 (GaloisField p e)) * v⁻¹ = signDiagE7 (AlgClosGF p e) deltaE7 ∧
        ∃ m ∈ parabolicLevi .E7 (AlgClosGF p e) JE7,
          entrywiseFrobGL .E7 (AlgClosGF p e) p e v * v⁻¹ =
            m * rootSL2 .E7 (AlgClosGF p e) thetaE7 WSL) →
      ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W
        (stdRankOne (e7Datum (GaloisField p e)) thetaE7) R₂

end Iface

section Unit

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups CFSG.LieType.Universal CFSG.LieType
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Timmesfeld
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.Steinberg CFSG.ClassicalInvolution.WeakCT Matrix
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
open scoped MatrixGroups

variable {p e : ℕ} [Fact p.Prime]

local notation "ψ" => e7Isogeny (GaloisField p e)

theorem a2UnitaryImageE7_three (hadm : StatedLieAdmissible .E7 0 p e) (hp2 : p ≠ 2)
    (hq3 : p ^ e = 3)
    {R₂ : Subgroup (E7sc p e)} {c₂ : E7sc p e}
    (hR₂ : R₂ ∈ longestFundamental (e7Datum (GaloisField p e))) (hc₂ : c₂ ∈ R₂)
    (ho : orderOf c₂ = 2)
    (hv : ∃ v ∈ h1E7 (AlgClosGF p e),
      v * baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e))
          ((e7Isogeny (GaloisField p e) c₂ : ↥(adjointGroup .E7 (GaloisField p e))) :
            ModGL .E7 (GaloisField p e)) * v⁻¹ = signDiagE7 (AlgClosGF p e) deltaE7 ∧
      ∃ m ∈ parabolicLevi .E7 (AlgClosGF p e) JE7,
        entrywiseFrobGL .E7 (AlgClosGF p e) p e v * v⁻¹ =
          m * rootSL2 .E7 (AlgClosGF p e) thetaE7 WSL) :
    ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W
      ((stdRankOne (e7Datum (GaloisField p e)) thetaE7).map ψ) (R₂.map ψ) := by
  obtain ⟨v, hv, hd, m, hm, hcoc⟩ := hv
  have hne : NeZero e := ⟨by rintro rfl; simp at hq3⟩
  have h2e : NeZero (2 * e) := ⟨by have := NeZero.ne e; omega⟩
  have hk2 : ringChar (AlgClosGF p e) ≠ 2 := by
    rw [ringChar.eq (AlgClosGF p e) p]
    exact hp2
  have hcardE : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := by
    rw [GaloisField.card p (2 * e) (NeZero.ne _), pow_mul' p 2 e]
  obtain ⟨Em⟩ := nonempty_a2Embedding_E7 (GaloisField p (2 * e))
  have hcocycle := cocycle_conj_pinnedX_E7 p hk2 e
    (entrywiseFrobGL_baseChangeGL_algebraMap
      ((ψ c₂ : ↥(adjointGroup .E7 (GaloisField p e))) : ModGL .E7 (GaloisField p e))) hd hm hcoc
  have hv' : ∀ t ∈ torusGroup .E7 (AlgClosGF p e), t * v ∈ h1E7 (AlgClosGF p e) :=
    fun t ht => mul_mem (levi_le_h1E7 (torusGroup_le_parabolicLevi JE7 ht)) hv
  obtain ⟨θ, hinj, hB12', hneg⟩ := exists_unitary_hom_odd hp2 isRoot_thetaE7
    isPartnerE7_deltaE7.1 a2Pairing_E7 Em hd hcocycle
    (fun t ht => rootDiagUnit_mul_comm_of_mem_torusGroup (thetaDiag deltaE7 (-1)) ht)
    (fun t ht => h1E7_le_adjointGroup (hv' t ht))
    (fun t ht A => conj_rootSL2_of_mem_h1E7 (hv' t ht) A)
    (fun j => by
      rw [rootSL2_HSL_eq_thetaDiag_E7 isPartnerE7_deltaE7.1,
        baseChangeGL_rootDiagUnit_thetaDiag_E7 j deltaE7]
      rfl)
  have hR₁ := stdRankOne_mem_longestFundamental_E7 (p := p) (e := e) hadm isRoot_thetaE7
  have hmap := map_stdRankOne_e7_root (p := p) (e := e) isRoot_thetaE7
  have hB12eq : (Phan.B12 (GaloisField p (2 * e)) p e).map θ =
      (stdRankOne (e7Datum (GaloisField p e)) thetaE7).map ψ := by
    rw [hmap]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, ⟨A, rfl⟩, rfl⟩
      obtain ⟨A₀, hA₀⟩ := hB12' A
      exact (mem_stdRankOne_e7_iff' isRoot_thetaE7 _).2 ⟨A₀, hA₀⟩
    · rw [natCard_rankOne hp2 (stdRankOne (e7AdjDatum (GaloisField p e)) thetaE7)
        (fun g => mem_stdRankOne_e7_iff' isRoot_thetaE7 g),
        Subgroup.card_map_of_injective hinj, natCard_B12 hcardE]
  obtain ⟨g, hg⟩ := e7Isogeny_surjective (GaloisField p e)
    (θ (swapElt (GaloisField p (2 * e)) p e))
  have hB23eq : (Phan.B23 (GaloisField p (2 * e)) p e).map θ =
      ((stdRankOne (e7Datum (GaloisField p e)) thetaE7).map (MulAut.conj g).toMonoidHom).map ψ := by
    rw [map_conj_map_e7, hg, ← map_conj_swapElt_B12 (GaloisField p (2 * e)) p e,
      Subgroup.map_map, ← hB12eq, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply]
  have hR₃ := map_conj_mem_longestFundamental g hR₁
  set R₃ := (stdRankOne (e7Datum (GaloisField p e)) thetaE7).map (MulAut.conj g).toMonoidHom
    with hR₃def
  have hc : ψ c₂ ∈ R₃.map ψ := by
    rw [← hB23eq, ← hneg]
    exact ⟨_, ⟨suNegOne (GaloisField p (2 * e)) p e, rfl⟩, rfl⟩
  obtain ⟨c₃, hc₃, hc₃ψ⟩ := hc
  have hinjR₃ : ∀ x ∈ R₃, ψ x = 1 → x = 1 := by
    intro x hx hx1
    obtain ⟨y, hy, rfl⟩ := hx
    have : ψ y = 1 := by
      have h : ψ g * ψ y * (ψ g)⁻¹ = 1 := by simpa using hx1
      calc ψ y = (ψ g)⁻¹ * (ψ g * ψ y * (ψ g)⁻¹) * ψ g := by group
        _ = 1 := by rw [h]; group
    simp [injOn_e7Isogeny_stdRankOne hp2 hadm isRoot_thetaE7 y hy this]
  have hc₂ne : ψ c₂ ≠ 1 := by
    rw [← hneg]
    intro h1
    have := hinj (h1.trans (map_one θ).symm)
    have h2 := embSUid_injective (unitaryInvolution (GaloisField p (2 * e)) p e) 0
      (this.trans (map_one _).symm)
    have h3 := congrArg
      (fun s : Su (GaloisField p (2 * e)) p e 2 => suMat s 0 0) h2
    have h4 : (-1 : GaloisField p (2 * e)) = 1 := by
      simpa [suNegOne, suMat, Units.val_neg] using h3
    have h5 : ((2 : ℕ) : GaloisField p (2 * e)) = 0 := by
      push_cast
      linear_combination -h4
    have h6 := (CharP.cast_eq_zero_iff (GaloisField p (2 * e)) p 2).1 h5
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 h6)
  have ho₃ : orderOf c₃ = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · have h2 : ψ (c₃ ^ 2) = 1 := by
        have ho_sq : c₂ ^ 2 = 1 := by
          have := pow_orderOf_eq_one c₂
          rwa [ho] at this
        rw [map_pow, hc₃ψ, ← map_pow, ho_sq, map_one]
      exact hinjR₃ _ (R₃.pow_mem hc₃ 2) h2
    · intro h1
      exact hc₂ne (by rw [← hc₃ψ, h1, map_one])
  have hRR : R₃ = R₂ := eq_of_mem_longestFundamental_E7_three hp2 hq3 hadm hR₃ hR₂ hc₃ hc₂ ho₃ ho
    (by exact_mod_cast congrArg Subtype.val hc₃ψ)
  have hker : θ.ker ≤ Subgroup.center (Su (GaloisField p (2 * e)) p e 3) := by
    rw [(MonoidHom.ker_eq_bot_iff θ).mpr hinj]
    exact bot_le
  refine ⟨θ.range, unitaryBlockStandardPair_of_normalized hker rfl hB12eq ?_⟩
  rw [hB23eq, hRR]

end Unit

section Iso

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.ModelFacts

variable {p e : ℕ} [Fact p.Prime]

theorem a2UnitaryE7_three : A2UnitaryE7_three p e := by
  intro hadm hp2 hq3 R₂ c₂ hR₂ hc₂ ho _ _ hv
  have hne : NeZero e := ⟨by rintro rfl; simp at hq3⟩
  have h2e : NeZero (2 * e) := ⟨by have := NeZero.ne e; omega⟩
  have hcard : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := by
    rw [GaloisField.card p (2 * e) (NeZero.ne _), pow_mul' p 2 e]
  have hR₁ := stdRankOne_mem_longestFundamental_E7 (p := p) (e := e) hadm isRoot_thetaE7
  have : Finite (E7sc p e) := ChevAut.finite_minGroup e7Data_valid (GaloisField p e)
  exact exists_uni_of_map_three hq3 hcard (e7Isogeny (GaloisField p e))
    (ChevAut.e7Isogeny_ker_le_center (GaloisField p e)) e7Isogeny_ker_sq
    (genSq_of_mem_longestFundamental3 (t := .E7) hq3 trivial hadm (by decide) (by decide) hR₁)
    (genSq_of_mem_longestFundamental3 (t := .E7) hq3 trivial hadm (by decide) (by decide) hR₂)
    (a2UnitaryImageE7_three hadm hp2 hq3 hR₂ hc₂ ho hv)

end Iso

section Main

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Universal CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)

variable {p e : ℕ} [Fact p.Prime]

theorem a2_normalized_E7_three (hadm : StatedLieAdmissible .E7 0 p e) (hU : A2UnitaryE7_three p e)
    (hp2 : p ≠ 2) (hq3 : p ^ e = 3) [NeZero e]
    {R₂ : Subgroup (E7sc p e)} (hR₂ : R₂ ∈ longestFundamental (e7Datum (GaloisField p e)))
    {c₁ c₂ : E7sc p e} (hc₁ : c₁ ∈ stdRankOne (e7Datum (GaloisField p e)) thetaE7)
    (hc₂ : c₂ ∈ R₂) (ho₁ : orderOf c₁ = 2) (ho₂ : orderOf c₂ = 2) (hcomm : c₁ * c₂ = c₂ * c₁)
    (hn : ¬ ∀ r ∈ stdRankOne (e7Datum (GaloisField p e)) thetaE7, c₂ * r = r * c₂) :
    (∃ W, WeakCT.LinearBlockStandardPair (GaloisField p e) W
      (stdRankOne (e7Datum (GaloisField p e)) thetaE7) R₂) ∨
    ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W
      (stdRankOne (e7Datum (GaloisField p e)) thetaE7) R₂ := by
  have hsingle : Generic.FundamentalSingleClass .E7 (e7Datum (GaloisField p e)) :=
    fundamentalSingleClass .E7 0 p e Fact.out trivial hadm (by decide) (by decide)
  have hθmem : stdRankOne (e7Datum (GaloisField p e)) thetaE7 ∈
      Generic.fundamentalSubgroups .E7 (e7Datum (GaloisField p e)) :=
    ⟨1, thetaE7, Or.inl (isLongestRoot_e7Datum hadm isRoot_thetaE7),
      (Generic.conjSub_one _).symm⟩
  have hθl := stdRankOne_mem_longestFundamental_E7 hadm (p := p) (e := e) isRoot_thetaE7
  obtain ⟨h, hh⟩ := hsingle _ hθmem R₂ (longestFundamental_subset .E7 _ hR₂)
  have hd₂ : h⁻¹ * c₂ * h ∈ stdRankOne (e7Datum (GaloisField p e)) thetaE7 :=
    Generic.mem_conjSub_iff.1 (hh ▸ hc₂)
  have hord : orderOf (h⁻¹ * c₂ * h) = 2 := by
    have := a2_orderOf_conj_eq_two ho₂ h⁻¹
    simpa using this
  have z1 := e7Isogeny_involution hp2 hadm isRoot_thetaE7 hc₁ ho₁
  have z2 := e7Isogeny_involution hp2 hadm isRoot_thetaE7 hd₂ hord
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at z2
  have hgc : ((e7Isogeny (GaloisField p e) h : ↥(adjointGroup .E7 (GaloisField p e))) :
      ModGL .E7 (GaloisField p e)) * signDiagE7 (GaloisField p e) thetaE7 *
        ((e7Isogeny (GaloisField p e) h : ↥(adjointGroup .E7 (GaloisField p e))) :
          ModGL .E7 (GaloisField p e))⁻¹ =
      ((e7Isogeny (GaloisField p e) c₂ : ↥(adjointGroup .E7 (GaloisField p e))) :
        ModGL .E7 (GaloisField p e)) := by
    rw [← z2]
    group
  have hcd : ((e7Isogeny (GaloisField p e) c₂ : ↥(adjointGroup .E7 (GaloisField p e))) :
      ModGL .E7 (GaloisField p e)) * signDiagE7 (GaloisField p e) thetaE7 =
      signDiagE7 (GaloisField p e) thetaE7 *
        ((e7Isogeny (GaloisField p e) c₂ : ↥(adjointGroup .E7 (GaloisField p e))) :
          ModGL .E7 (GaloisField p e)) := by
    have := congrArg (fun x : E7sc p e =>
      ((e7Isogeny (GaloisField p e) x : ↥(adjointGroup .E7 (GaloisField p e))) :
        ModGL .E7 (GaloisField p e))) hcomm
    simp only [map_mul, Subgroup.coe_mul, z1] at this
    exact this.symm
  have hc2 : ((e7Isogeny (GaloisField p e) c₂ : ↥(adjointGroup .E7 (GaloisField p e))) :
      ModGL .E7 (GaloisField p e)) *
        ((e7Isogeny (GaloisField p e) c₂ : ↥(adjointGroup .E7 (GaloisField p e))) :
          ModGL .E7 (GaloisField p e)) = 1 := by
    have h1 := ((orderOf_eq_prime_iff (p := 2)).1 ho₂).1
    have h2 := congrArg (fun x : E7sc p e =>
      ((e7Isogeny (GaloisField p e) x : ↥(adjointGroup .E7 (GaloisField p e))) :
        ModGL .E7 (GaloisField p e))) h1
    simpa [sq] using h2
  have hnc : ¬ ∀ A : SL2 (GaloisField p e),
      ((e7Isogeny (GaloisField p e) c₂ : ↥(adjointGroup .E7 (GaloisField p e))) :
        ModGL .E7 (GaloisField p e)) * rootSL2 .E7 (GaloisField p e) thetaE7 A =
      rootSL2 .E7 (GaloisField p e) thetaE7 A *
        ((e7Isogeny (GaloisField p e) c₂ : ↥(adjointGroup .E7 (GaloisField p e))) :
          ModGL .E7 (GaloisField p e)) := by
    intro hA
    apply hn
    refine fun r hr => (commute_of_map_commute_of_genSq (e7Isogeny (GaloisField p e))
      ker_e7Isogeny_le_center e7Isogeny_ker_sq
      (genSq_of_mem_longestFundamental3 (t := .E7) hq3 trivial hadm (by decide) (by decide) hθl)
          (b := c₂) (fun r hr => ?_) r hr).symm
    have hmem : e7Isogeny (GaloisField p e) r ∈
        stdRankOne (e7AdjDatum (GaloisField p e)) thetaE7 := by
      rw [← map_stdRankOne_e7_root (p := p) (e := e) isRoot_thetaE7]
      exact Subgroup.mem_map_of_mem _ hr
    obtain ⟨A, hAr⟩ := (mem_stdRankOne_e7_iff' isRoot_thetaE7 _).1 hmem
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hAr]
    exact (hA A).symm
  rcases exists_split_or_anti_E7 hp2 (e7Isogeny (GaloisField p e) c₂).2
    (e7Isogeny (GaloisField p e) h).2 hc2 hcd hgc hnc with ⟨ū, hū, hūc, hūθ⟩ | hanti
  · left
    obtain ⟨u, hu⟩ := e7Isogeny_surjective (GaloisField p e)
      (⟨ū, hū⟩ : ↥(adjointGroup .E7 (GaloisField p e)))
    have hu' : ((e7Isogeny (GaloisField p e) u : ↥(adjointGroup .E7 (GaloisField p e))) :
        ModGL .E7 (GaloisField p e)) = ū := congrArg Subtype.val hu
    refine linearBlockStandardPair_of_split_E7_three hp2 hq3 hadm hc₁ ho₁ hR₂ hc₂ ho₂ (u := u) ?_ ?_
    · rw [hu']
      exact hūθ
    · simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hu']
      exact hūc
  · right
    exact hU hadm hp2 hq3 R₂ c₂ hR₂ hc₂ ho₂ hcd hn hanti

theorem a2BranchLeft_e7_aux_three (hadm : StatedLieAdmissible .E7 0 p e)
    (hU : A2UnitaryE7_three p e)
    (hp2 : p ≠ 2) (hq3 : p ^ e = 3)
    {R₁ R₂ : Subgroup (E7sc p e)}
    (h₁ : R₁ ∈ longestFundamental (e7Datum (GaloisField p e)))
    (h₂ : R₂ ∈ longestFundamental (e7Datum (GaloisField p e)))
    {c₁ c₂ : E7sc p e} (hc₁ : c₁ ∈ R₁) (hc₂ : c₂ ∈ R₂)
    (ho₁ : orderOf c₁ = 2) (ho₂ : orderOf c₂ = 2) (hcomm : c₁ * c₂ = c₂ * c₁)
    (hn : ¬ ∀ r ∈ R₁, c₂ * r = r * c₂) :
    (∃ W, WeakCT.LinearBlockStandardPair (GaloisField p e) W R₁ R₂) ∨
      ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₁ R₂ := by
  have : NeZero e := ⟨by
    rintro rfl
    norm_num at hq3⟩
  have hsingle : Generic.FundamentalSingleClass .E7 (e7Datum (GaloisField p e)) :=
    fundamentalSingleClass .E7 0 p e Fact.out trivial hadm (by decide) (by decide)
  have hθmem : stdRankOne (e7Datum (GaloisField p e)) thetaE7 ∈
      Generic.fundamentalSubgroups .E7 (e7Datum (GaloisField p e)) :=
    ⟨1, thetaE7, Or.inl (isLongestRoot_e7Datum hadm isRoot_thetaE7),
      (Generic.conjSub_one _).symm⟩
  obtain ⟨g, hg⟩ := hsingle _ hθmem R₁ (longestFundamental_subset .E7 _ h₁)
  have hR₁ : R₁ = (stdRankOne (e7Datum (GaloisField p e)) thetaE7).map
      (MulAut.conj g).toMonoidHom := hg
  obtain ⟨r₁, hr₁, rfl⟩ : ∃ r ∈ stdRankOne (e7Datum (GaloisField p e)) thetaE7,
      c₁ = g * r * g⁻¹ := by
    rw [hR₁] at hc₁
    obtain ⟨r, hr, hrc⟩ := hc₁
    exact ⟨r, hr, hrc.symm⟩
  have hor₁ : orderOf r₁ = 2 := by
    have := a2_orderOf_conj_eq_two ho₁ g⁻¹
    simpa [mul_assoc] using this
  set R₂' := R₂.map (MulAut.conj g⁻¹).toMonoidHom with hR₂'
  set c₂' : E7sc p e := g⁻¹ * c₂ * g with hc₂'
  have hR₂'l : R₂' ∈ longestFundamental (e7Datum (GaloisField p e)) :=
    map_conj_mem_longestFundamental g⁻¹ h₂
  have hc₂'R : c₂' ∈ R₂' := ⟨c₂, hc₂, by simp [hc₂']⟩
  have ho₂' : orderOf c₂' = 2 := by
    have := a2_orderOf_conj_eq_two ho₂ g⁻¹
    simpa [hc₂'] using this
  have hcomm' : r₁ * c₂' = c₂' * r₁ := by
    have h : g * r₁ * g⁻¹ * c₂ = c₂ * (g * r₁ * g⁻¹) := hcomm
    calc r₁ * c₂' = g⁻¹ * (g * r₁ * g⁻¹ * c₂) * g := by simp [hc₂']; group
      _ = g⁻¹ * (c₂ * (g * r₁ * g⁻¹)) * g := by rw [h]
      _ = c₂' * r₁ := by simp [hc₂']; group
  have hn' : ¬ ∀ r ∈ stdRankOne (e7Datum (GaloisField p e)) thetaE7, c₂' * r = r * c₂' := by
    intro h
    apply hn
    intro r hr
    rw [hR₁] at hr
    obtain ⟨r', hr', rfl⟩ := hr
    have h' := h r' hr'
    calc c₂ * (MulAut.conj g).toMonoidHom r' = g * (c₂' * r') * g⁻¹ := by
          simp [hc₂', MulAut.conj_apply]; group
      _ = g * (r' * c₂') * g⁻¹ := by rw [h']
      _ = (MulAut.conj g).toMonoidHom r' * c₂ := by
          simp [hc₂', MulAut.conj_apply]; group
  rcases a2_normalized_E7_three hadm hU hp2 hq3 hR₂'l hr₁ hc₂'R hor₁ ho₂' hcomm' hn' with
    ⟨W, hW⟩ | ⟨W, hW⟩
  · left
    have h := linearBlockStandardPair_map_conj hW g
    have e2 : R₂'.map (MulAut.conj g).toMonoidHom = R₂ := by
      have := a2_map_conj_inv_map_conj g⁻¹ R₂
      rwa [inv_inv] at this
    rw [e2, ← hR₁] at h
    exact ⟨_, h⟩
  · right
    have h := CFSG.ClassicalInvolution.Models.unitaryBlockStandardPair_map hW
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    have e2 : R₂'.map (MulAut.conj g).toMonoidHom = R₂ := by
      have := a2_map_conj_inv_map_conj g⁻¹ R₂
      rwa [inv_inv] at this
    rw [e2, ← hR₁] at h
    exact ⟨_, h⟩

end Main

end CFSG.ClassicalInvolution.ModelFacts.Levi
