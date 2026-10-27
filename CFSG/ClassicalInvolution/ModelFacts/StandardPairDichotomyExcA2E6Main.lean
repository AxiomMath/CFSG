module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E6Pair
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2InterfaceE6
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E6Rational

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Universal CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)

section Split

variable {p e : ℕ} [Fact p.Prime]

theorem exists_involution_stdRankOne_E6 (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .E6 0 p e)
    {c₁ : E6sc p e} (hc₁ : c₁ ∈ stdRankOne (e6Datum (GaloisField p e)) thetaE6)
    (ho₁ : orderOf c₁ = 2) {β : Fin (Tag.rank .E6) → ℤ} (hβ : IsRoot .E6 β) :
    ∃ c ∈ stdRankOne (e6Datum (GaloisField p e)) β, orderOf c = 2 ∧
      ((e6Isogeny (GaloisField p e) c : ↥(adjointGroup .E6 (GaloisField p e))) :
        ModGL .E6 (GaloisField p e)) = signDiagE6 (GaloisField p e) β := by
  have hsingle : Generic.FundamentalSingleClass .E6 (e6Datum (GaloisField p e)) :=
    fundamentalSingleClass .E6 0 p e Fact.out trivial hadm (by decide) (by decide)
  have hθmem : stdRankOne (e6Datum (GaloisField p e)) thetaE6 ∈
      Generic.fundamentalSubgroups .E6 (e6Datum (GaloisField p e)) :=
    ⟨1, thetaE6, Or.inl (isLongestRoot_e6Datum hadm isRoot_thetaE6),
      (Generic.conjSub_one _).symm⟩
  have hβl := stdRankOne_mem_longestFundamental_E6 hadm (p := p) (e := e) hβ
  obtain ⟨k, hk⟩ := hsingle _ hθmem _ (longestFundamental_subset .E6 _ hβl)
  have hmem : k * c₁ * k⁻¹ ∈ stdRankOne (e6Datum (GaloisField p e)) β := by
    rw [hk]
    exact ⟨c₁, hc₁, rfl⟩
  have hord := a2_orderOf_conj_eq_two ho₁ k
  exact ⟨k * c₁ * k⁻¹, hmem, hord, e6Isogeny_involution hp2 hadm hβ hmem hord⟩

theorem linearBlockStandardPair_theta_deltaE6 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .E6 0 p e) {c₁ : E6sc p e}
    (hc₁ : c₁ ∈ stdRankOne (e6Datum (GaloisField p e)) thetaE6) (ho₁ : orderOf c₁ = 2) :
    ∃ W, WeakCT.LinearBlockStandardPair (GaloisField p e) W
      (stdRankOne (e6Datum (GaloisField p e)) thetaE6)
      (stdRankOne (e6Datum (GaloisField p e)) deltaE6) := by
  have hδ₀ := isPartnerE6_deltaE6
  have hθlong : ModelFacts.IsLongestRoot (e6Datum (GaloisField p e)) thetaE6 :=
    isLongestRoot_e6Datum hadm isRoot_thetaE6
  obtain ⟨δ', hδ'l, hδ'p, W, hW⟩ := exists_standardPair_partner_E6 p e hadm hθlong
  have hδ'root : IsRoot .E6 δ' :=
    (e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 (GaloisField p e)).1
      ((isLongestRoot_iff _ _).1 hδ'l).1
  have hδ'PF : IsPartnerE6 δ' := isPartnerE6_of_isPartner hδ'root hδ'p
  obtain ⟨W', hW'⟩ : ∃ W' : Subgroup (E6sc p e),
      WeakCT.LinearBlockStandardPair (GaloisField p e) W'
        (stdRankOne (e6Datum (GaloisField p e)) thetaE6)
        (stdRankOne (e6Datum (GaloisField p e)) δ') := ⟨W, hW⟩
  obtain ⟨n, hn, hnd⟩ := exists_levi_conj_partnerE6 (F := GaloisField p e) hδ'PF
  have hnG : n ∈ adjointGroup .E6 (GaloisField p e) := parabolicSubgroup_le_adjointGroup _ _ _
    (parabolicLevi_le_parabolicSubgroup JE6 hn)
  obtain ⟨ν, hν⟩ := e6Isogeny_surjective (GaloisField p e)
    (⟨n⁻¹, inv_mem hnG⟩ : ↥(adjointGroup .E6 (GaloisField p e)))
  have hν' : ((e6Isogeny (GaloisField p e) ν : ↥(adjointGroup .E6 (GaloisField p e))) :
      ModGL .E6 (GaloisField p e)) = n⁻¹ := congrArg Subtype.val hν
  have hνθ : ((e6Isogeny (GaloisField p e) ν : ↥(adjointGroup .E6 (GaloisField p e))) :
      ModGL .E6 (GaloisField p e)) * signDiagE6 (GaloisField p e) thetaE6 =
      signDiagE6 (GaloisField p e) thetaE6 *
        ((e6Isogeny (GaloisField p e) ν : ↥(adjointGroup .E6 (GaloisField p e))) :
          ModGL .E6 (GaloisField p e)) := by
    rw [hν']
    exact (rootDiagUnit_thetaDiag_comm_levi_E6 (-1 : (GaloisField p e)ˣ) (inv_mem hn)).symm
  obtain ⟨c', hc'R, hc'o, hc'ε⟩ := exists_involution_stdRankOne_E6 hp2 hadm hc₁ ho₁ hδ'root
  obtain ⟨c₀, hc₀R, hc₀o, hc₀ε⟩ := exists_involution_stdRankOne_E6 hp2 hadm hc₁ ho₁ hδ₀.1
  have hRδ' := stdRankOne_mem_longestFundamental_E6 hadm (p := p) (e := e) hδ'root
  have hRδ₀ := stdRankOne_mem_longestFundamental_E6 hadm (p := p) (e := e) hδ₀.1
  have hν_R : (stdRankOne (e6Datum (GaloisField p e)) δ').map (MulAut.conj ν).toMonoidHom =
      stdRankOne (e6Datum (GaloisField p e)) deltaE6 := by
    refine eq_of_mem_longestFundamental_E6 hp2 hq hadm (map_conj_mem_longestFundamental ν hRδ')
      hRδ₀ (c := ν * c' * ν⁻¹) (c' := c₀) ⟨c', hc'R, rfl⟩ hc₀R (a2_orderOf_conj_eq_two hc'o ν)
      hc₀o ?_
    rw [hc₀ε]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hν', hc'ε]
    have h1 : n * signDiagE6 (GaloisField p e) deltaE6 * n⁻¹ =
        signDiagE6 (GaloisField p e) δ' := hnd
    rw [← h1]
    group
  have hpair := linearBlockStandardPair_map_conj hW' ν
  rw [conj_stdRankOne_theta_E6 hp2 hq hadm hνθ, hν_R] at hpair
  exact ⟨_, hpair⟩

theorem linearBlockStandardPair_of_split_E6 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .E6 0 p e) {c₁ : E6sc p e}
    (hc₁ : c₁ ∈ stdRankOne (e6Datum (GaloisField p e)) thetaE6) (ho₁ : orderOf c₁ = 2)
    {R₂ : Subgroup (E6sc p e)} (hR₂ : R₂ ∈ longestFundamental (e6Datum (GaloisField p e)))
    {c₂ u : E6sc p e} (hc₂ : c₂ ∈ R₂) (ho₂ : orderOf c₂ = 2)
    (hu : ((e6Isogeny (GaloisField p e) u : ↥(adjointGroup .E6 (GaloisField p e))) :
        ModGL .E6 (GaloisField p e)) * signDiagE6 (GaloisField p e) thetaE6 =
      signDiagE6 (GaloisField p e) thetaE6 *
        ((e6Isogeny (GaloisField p e) u : ↥(adjointGroup .E6 (GaloisField p e))) :
          ModGL .E6 (GaloisField p e)))
    (hcu : ((e6Isogeny (GaloisField p e) (u * c₂ * u⁻¹) :
        ↥(adjointGroup .E6 (GaloisField p e))) : ModGL .E6 (GaloisField p e)) =
      signDiagE6 (GaloisField p e) deltaE6) :
    ∃ W, WeakCT.LinearBlockStandardPair (GaloisField p e) W
      (stdRankOne (e6Datum (GaloisField p e)) thetaE6) R₂ := by
  have hδ₀ := isPartnerE6_deltaE6
  obtain ⟨c₀, hc₀R, hc₀o, hc₀ε⟩ := exists_involution_stdRankOne_E6 hp2 hadm hc₁ ho₁ hδ₀.1
  have hRδ₀ := stdRankOne_mem_longestFundamental_E6 hadm (p := p) (e := e) hδ₀.1
  have hR₂u : R₂.map (MulAut.conj u).toMonoidHom =
      stdRankOne (e6Datum (GaloisField p e)) deltaE6 :=
    eq_of_mem_longestFundamental_E6 hp2 hq hadm (map_conj_mem_longestFundamental u hR₂) hRδ₀
      (c := u * c₂ * u⁻¹) (c' := c₀) ⟨c₂, hc₂, rfl⟩ hc₀R (a2_orderOf_conj_eq_two ho₂ u) hc₀o
      (hcu.trans hc₀ε.symm)
  obtain ⟨W₁, hW₁⟩ := linearBlockStandardPair_theta_deltaE6 hp2 hq hadm hc₁ ho₁
  have huinv : ((e6Isogeny (GaloisField p e) u⁻¹ : ↥(adjointGroup .E6 (GaloisField p e))) :
      ModGL .E6 (GaloisField p e)) * signDiagE6 (GaloisField p e) thetaE6 =
      signDiagE6 (GaloisField p e) thetaE6 *
        ((e6Isogeny (GaloisField p e) u⁻¹ : ↥(adjointGroup .E6 (GaloisField p e))) :
          ModGL .E6 (GaloisField p e)) := by
    simp only [map_inv, Subgroup.coe_inv]
    calc ((e6Isogeny (GaloisField p e) u : ↥(adjointGroup .E6 (GaloisField p e))) :
          ModGL .E6 (GaloisField p e))⁻¹ * signDiagE6 (GaloisField p e) thetaE6 =
        (↑(e6Isogeny (GaloisField p e) u) : ModGL .E6 (GaloisField p e))⁻¹ *
          (signDiagE6 (GaloisField p e) thetaE6 *
            (↑(e6Isogeny (GaloisField p e) u) : ModGL .E6 (GaloisField p e))) *
          (↑(e6Isogeny (GaloisField p e) u) : ModGL .E6 (GaloisField p e))⁻¹ := by group
      _ = (↑(e6Isogeny (GaloisField p e) u) : ModGL .E6 (GaloisField p e))⁻¹ *
          ((↑(e6Isogeny (GaloisField p e) u) : ModGL .E6 (GaloisField p e)) *
            signDiagE6 (GaloisField p e) thetaE6) *
          (↑(e6Isogeny (GaloisField p e) u) : ModGL .E6 (GaloisField p e))⁻¹ := by rw [hu]
      _ = _ := by group
  have hfin := linearBlockStandardPair_map_conj hW₁ u⁻¹
  rw [conj_stdRankOne_theta_E6 hp2 hq hadm huinv, ← hR₂u, a2_map_conj_inv_map_conj] at hfin
  exact ⟨_, hfin⟩

end Split

section Main

variable {p e : ℕ} [Fact p.Prime]

theorem a2_normalized_E6 (hadm : StatedLieAdmissible .E6 0 p e) (hU : A2UnitaryE6 p e)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) [NeZero e]
    {R₂ : Subgroup (E6sc p e)} (hR₂ : R₂ ∈ longestFundamental (e6Datum (GaloisField p e)))
    {c₁ c₂ : E6sc p e} (hc₁ : c₁ ∈ stdRankOne (e6Datum (GaloisField p e)) thetaE6)
    (hc₂ : c₂ ∈ R₂) (ho₁ : orderOf c₁ = 2) (ho₂ : orderOf c₂ = 2) (hcomm : c₁ * c₂ = c₂ * c₁)
    (hn : ¬ ∀ r ∈ stdRankOne (e6Datum (GaloisField p e)) thetaE6, c₂ * r = r * c₂) :
    (∃ W, WeakCT.LinearBlockStandardPair (GaloisField p e) W
      (stdRankOne (e6Datum (GaloisField p e)) thetaE6) R₂) ∨
    ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W
      (stdRankOne (e6Datum (GaloisField p e)) thetaE6) R₂ := by
  have hsingle : Generic.FundamentalSingleClass .E6 (e6Datum (GaloisField p e)) :=
    fundamentalSingleClass .E6 0 p e Fact.out trivial hadm (by decide) (by decide)
  have hθmem : stdRankOne (e6Datum (GaloisField p e)) thetaE6 ∈
      Generic.fundamentalSubgroups .E6 (e6Datum (GaloisField p e)) :=
    ⟨1, thetaE6, Or.inl (isLongestRoot_e6Datum hadm isRoot_thetaE6),
      (Generic.conjSub_one _).symm⟩
  have hθl := stdRankOne_mem_longestFundamental_E6 hadm (p := p) (e := e) isRoot_thetaE6
  obtain ⟨h, hh⟩ := hsingle _ hθmem R₂ (longestFundamental_subset .E6 _ hR₂)
  have hd₂ : h⁻¹ * c₂ * h ∈ stdRankOne (e6Datum (GaloisField p e)) thetaE6 :=
    Generic.mem_conjSub_iff.1 (hh ▸ hc₂)
  have hord : orderOf (h⁻¹ * c₂ * h) = 2 := by
    have := a2_orderOf_conj_eq_two ho₂ h⁻¹
    simpa using this
  have z1 := e6Isogeny_involution hp2 hadm isRoot_thetaE6 hc₁ ho₁
  have z2 := e6Isogeny_involution hp2 hadm isRoot_thetaE6 hd₂ hord
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at z2
  have hgc : ((e6Isogeny (GaloisField p e) h : ↥(adjointGroup .E6 (GaloisField p e))) :
      ModGL .E6 (GaloisField p e)) * signDiagE6 (GaloisField p e) thetaE6 *
        ((e6Isogeny (GaloisField p e) h : ↥(adjointGroup .E6 (GaloisField p e))) :
          ModGL .E6 (GaloisField p e))⁻¹ =
      ((e6Isogeny (GaloisField p e) c₂ : ↥(adjointGroup .E6 (GaloisField p e))) :
        ModGL .E6 (GaloisField p e)) := by
    rw [← z2]
    group
  have hcd : ((e6Isogeny (GaloisField p e) c₂ : ↥(adjointGroup .E6 (GaloisField p e))) :
      ModGL .E6 (GaloisField p e)) * signDiagE6 (GaloisField p e) thetaE6 =
      signDiagE6 (GaloisField p e) thetaE6 *
        ((e6Isogeny (GaloisField p e) c₂ : ↥(adjointGroup .E6 (GaloisField p e))) :
          ModGL .E6 (GaloisField p e)) := by
    have := congrArg (fun x : E6sc p e =>
      ((e6Isogeny (GaloisField p e) x : ↥(adjointGroup .E6 (GaloisField p e))) :
        ModGL .E6 (GaloisField p e))) hcomm
    simp only [map_mul, Subgroup.coe_mul, z1] at this
    exact this.symm
  have hc2 : ((e6Isogeny (GaloisField p e) c₂ : ↥(adjointGroup .E6 (GaloisField p e))) :
      ModGL .E6 (GaloisField p e)) *
        ((e6Isogeny (GaloisField p e) c₂ : ↥(adjointGroup .E6 (GaloisField p e))) :
          ModGL .E6 (GaloisField p e)) = 1 := by
    have h1 := ((orderOf_eq_prime_iff (p := 2)).1 ho₂).1
    have h2 := congrArg (fun x : E6sc p e =>
      ((e6Isogeny (GaloisField p e) x : ↥(adjointGroup .E6 (GaloisField p e))) :
        ModGL .E6 (GaloisField p e))) h1
    simpa [sq] using h2
  have hnc : ¬ ∀ A : SL2 (GaloisField p e),
      ((e6Isogeny (GaloisField p e) c₂ : ↥(adjointGroup .E6 (GaloisField p e))) :
        ModGL .E6 (GaloisField p e)) * rootSL2 .E6 (GaloisField p e) thetaE6 A =
      rootSL2 .E6 (GaloisField p e) thetaE6 A *
        ((e6Isogeny (GaloisField p e) c₂ : ↥(adjointGroup .E6 (GaloisField p e))) :
          ModGL .E6 (GaloisField p e)) := by
    intro hA
    apply hn
    refine commute_of_commutator_central _
      (le_of_eq (commutator_eq_of_mem_longestFundamental (t := .E6) hp2 hq trivial hadm hθl).symm)
      c₂ fun r hr => ?_
    have hmem : e6Isogeny (GaloisField p e) r ∈
        stdRankOne (e6AdjDatum (GaloisField p e)) thetaE6 := by
      rw [← map_stdRankOne_e6_root (p := p) (e := e) isRoot_thetaE6]
      exact Subgroup.mem_map_of_mem _ hr
    obtain ⟨A, hAr⟩ := (mem_stdRankOne_e6_iff' isRoot_thetaE6 _).1 hmem
    apply ker_e6Isogeny_le_center
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
    rw [hAr]
    exact mul_inv_eq_one.2 (by rw [mul_inv_eq_iff_eq_mul]; exact hA A)
  rcases exists_split_or_anti_E6 hp2 (e6Isogeny (GaloisField p e) c₂).2
    (e6Isogeny (GaloisField p e) h).2 hc2 hcd hgc hnc with ⟨ū, hū, hūc, hūθ⟩ | hanti
  · left
    obtain ⟨u, hu⟩ := e6Isogeny_surjective (GaloisField p e)
      (⟨ū, hū⟩ : ↥(adjointGroup .E6 (GaloisField p e)))
    have hu' : ((e6Isogeny (GaloisField p e) u : ↥(adjointGroup .E6 (GaloisField p e))) :
        ModGL .E6 (GaloisField p e)) = ū := congrArg Subtype.val hu
    refine linearBlockStandardPair_of_split_E6 hp2 hq hadm hc₁ ho₁ hR₂ hc₂ ho₂ (u := u) ?_ ?_
    · rw [hu']
      exact hūθ
    · simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hu']
      exact hūc
  · right
    exact hU hadm hp2 hq R₂ c₂ hR₂ hc₂ ho₂ hcd hn hanti

theorem a2BranchLeft_e6_aux (hadm : StatedLieAdmissible .E6 0 p e) (hU : A2UnitaryE6 p e)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    {R₁ R₂ : Subgroup (E6sc p e)}
    (h₁ : R₁ ∈ longestFundamental (e6Datum (GaloisField p e)))
    (h₂ : R₂ ∈ longestFundamental (e6Datum (GaloisField p e)))
    {c₁ c₂ : E6sc p e} (hc₁ : c₁ ∈ R₁) (hc₂ : c₂ ∈ R₂)
    (ho₁ : orderOf c₁ = 2) (ho₂ : orderOf c₂ = 2) (hcomm : c₁ * c₂ = c₂ * c₁)
    (hn : ¬ ∀ r ∈ R₁, c₂ * r = r * c₂) :
    (∃ W, WeakCT.LinearBlockStandardPair (GaloisField p e) W R₁ R₂) ∨
      ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₁ R₂ := by
  have : NeZero e := ⟨by
    rintro rfl
    norm_num at hq⟩
  have hsingle : Generic.FundamentalSingleClass .E6 (e6Datum (GaloisField p e)) :=
    fundamentalSingleClass .E6 0 p e Fact.out trivial hadm (by decide) (by decide)
  have hθmem : stdRankOne (e6Datum (GaloisField p e)) thetaE6 ∈
      Generic.fundamentalSubgroups .E6 (e6Datum (GaloisField p e)) :=
    ⟨1, thetaE6, Or.inl (isLongestRoot_e6Datum hadm isRoot_thetaE6),
      (Generic.conjSub_one _).symm⟩
  obtain ⟨g, hg⟩ := hsingle _ hθmem R₁ (longestFundamental_subset .E6 _ h₁)
  have hR₁ : R₁ = (stdRankOne (e6Datum (GaloisField p e)) thetaE6).map
      (MulAut.conj g).toMonoidHom := hg
  obtain ⟨r₁, hr₁, rfl⟩ : ∃ r ∈ stdRankOne (e6Datum (GaloisField p e)) thetaE6,
      c₁ = g * r * g⁻¹ := by
    rw [hR₁] at hc₁
    obtain ⟨r, hr, hrc⟩ := hc₁
    exact ⟨r, hr, hrc.symm⟩
  have hor₁ : orderOf r₁ = 2 := by
    have := a2_orderOf_conj_eq_two ho₁ g⁻¹
    simpa [mul_assoc] using this
  set R₂' := R₂.map (MulAut.conj g⁻¹).toMonoidHom with hR₂'
  set c₂' : E6sc p e := g⁻¹ * c₂ * g with hc₂'
  have hR₂'l : R₂' ∈ longestFundamental (e6Datum (GaloisField p e)) :=
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
  have hn' : ¬ ∀ r ∈ stdRankOne (e6Datum (GaloisField p e)) thetaE6, c₂' * r = r * c₂' := by
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
  rcases a2_normalized_E6 hadm hU hp2 hq hR₂'l hr₁ hc₂'R hor₁ ho₂' hcomm' hn' with
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

theorem a2BranchLeft_e6 (hadm : StatedLieAdmissible .E6 0 p e) (hU : A2UnitaryE6 p e) :
    A2BranchLeft p .E6 0 e :=
  fun hp2 hq _ h₁ _ h₂ _ _ hc₁ hc₂ ho₁ ho₂ hcomm hn =>
    a2BranchLeft_e6_aux hadm hU hp2 hq h₁ h₂ hc₁ hc₂ ho₁ ho₂ hcomm hn

end Main

end CFSG.ClassicalInvolution.ModelFacts.Levi
