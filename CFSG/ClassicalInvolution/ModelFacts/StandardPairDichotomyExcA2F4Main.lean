module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2F4Pair
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Interface
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcOrth
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.Pairs
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
public import Certificates.Certificate3952
public import CFSG.ClassicalInvolution.Models.SymplecticPairs

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Universal CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)

section Main

variable {p e : ℕ} [Fact p.Prime]

theorem a2_normalized_F4 (hadm : StatedLieAdmissible .F4 0 p e) (hU : A2UnitaryF4 p e)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) [NeZero e]
    {R₂ : Subgroup ↥(adjointGroup .F4 (GaloisField p e))}
    (hR₂ : R₂ ∈ longestFundamental (f4Datum (GaloisField p e)))
    {c₂ : ↥(adjointGroup .F4 (GaloisField p e))} (hc₂ : c₂ ∈ R₂) (ho : orderOf c₂ = 2)
    (hcd : (c₂ : ModGL .F4 (GaloisField p e)) * signDiagF4 (GaloisField p e) thetaF4 =
      signDiagF4 (GaloisField p e) thetaF4 * (c₂ : ModGL .F4 (GaloisField p e)))
    (hn : ¬ ∀ r ∈ stdRankOne (f4Datum (GaloisField p e)) thetaF4, c₂ * r = r * c₂) :
    (∃ W, WeakCT.LinearBlockStandardPair (GaloisField p e) W
      (stdRankOne (f4Datum (GaloisField p e)) thetaF4) R₂) ∨
    ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W
      (stdRankOne (f4Datum (GaloisField p e)) thetaF4) R₂ := by
  have hK := ringChar_galoisField_ne_two (p := p) (e := e) hp2
  have hsingle : Generic.FundamentalSingleClass .F4 (f4Datum (GaloisField p e)) :=
    fundamentalSingleClass .F4 0 p e Fact.out trivial hadm (by decide) (by decide)
  have hθmem : stdRankOne (f4Datum (GaloisField p e)) thetaF4 ∈
      Generic.fundamentalSubgroups .F4 (f4Datum (GaloisField p e)) :=
    ⟨1, thetaF4, Or.inl (isLongestRoot_f4Datum_of_iform_eq_four isRoot_thetaF4
      iform_thetaF4_self), (Generic.conjSub_one _).symm⟩
  obtain ⟨y, hy⟩ := hsingle _ hθmem R₂ (longestFundamental_subset .F4 _ hR₂)
  have h1 : y⁻¹ * c₂ * y ∈ stdRankOne (f4Datum (GaloisField p e)) thetaF4 :=
    Generic.mem_conjSub_iff.1 (hy ▸ hc₂)
  have hord : orderOf (y⁻¹ * c₂ * y) = 2 := by
    rw [← ho]
    have := orderOf_injective (MulAut.conj y⁻¹).toMonoidHom (MulAut.conj y⁻¹).injective c₂
    simpa [MulAut.conj_apply] using this
  have z1 := eq_signDiagF4_of_orderOf_eq_two hK isRoot_thetaF4 iform_thetaF4_self h1 hord
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at z1
  have hgc : (y : ModGL .F4 (GaloisField p e)) * signDiagF4 (GaloisField p e) thetaF4 *
      (y : ModGL .F4 (GaloisField p e))⁻¹ = (c₂ : ModGL .F4 (GaloisField p e)) := by
    rw [← z1]
    group
  have hc2 : (c₂ : ModGL .F4 (GaloisField p e)) * c₂ = 1 := by
    have := (orderOf_eq_prime_iff (p := 2)).1 ho
    have h := congrArg
      (fun x : ↥(adjointGroup .F4 (GaloisField p e)) => (x : ModGL .F4 (GaloisField p e))) this.1
    simpa [sq] using h
  have hnc : ¬ ∀ A : SL2 (GaloisField p e),
      (c₂ : ModGL .F4 (GaloisField p e)) * rootSL2 .F4 (GaloisField p e) thetaF4 A =
        rootSL2 .F4 (GaloisField p e) thetaF4 A * (c₂ : ModGL .F4 (GaloisField p e)) := by
    intro h
    apply hn
    intro r hr
    obtain ⟨A, hA⟩ := (mem_stdRankOne_f4_iff' isRoot_thetaF4 r).1 hr
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, hA]
    exact h A
  rcases exists_split_or_anti_F4 hp2 c₂.2 y.2 hc2 hcd hgc hnc with
    ⟨u, hu, hud, huθ⟩ | hanti
  · left
    exact linearBlockStandardPair_of_split_F4 hp2 hadm hR₂ hc₂ ho (u := ⟨u, hu⟩) huθ hud
  · right
    exact hU hadm hp2 hq R₂ c₂ hR₂ hc₂ ho hcd hn hanti

theorem a2BranchLeft_f4_aux (hadm : StatedLieAdmissible .F4 0 p e) (hU : A2UnitaryF4 p e)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    {R₁ R₂ : Subgroup ↥(adjointGroup .F4 (GaloisField p e))}
    (h₁ : R₁ ∈ longestFundamental (f4Datum (GaloisField p e)))
    (h₂ : R₂ ∈ longestFundamental (f4Datum (GaloisField p e)))
    {c₁ c₂ : ↥(adjointGroup .F4 (GaloisField p e))} (hc₁ : c₁ ∈ R₁) (hc₂ : c₂ ∈ R₂)
    (ho₁ : orderOf c₁ = 2) (ho₂ : orderOf c₂ = 2) (hcomm : c₁ * c₂ = c₂ * c₁)
    (hn : ¬ ∀ r ∈ R₁, c₂ * r = r * c₂) :
    (∃ W, WeakCT.LinearBlockStandardPair (GaloisField p e) W R₁ R₂) ∨
      ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₁ R₂ := by
  have : NeZero e := ⟨by
    rintro rfl
    norm_num at hq⟩
  have hK := ringChar_galoisField_ne_two (p := p) (e := e) hp2
  have hsingle : Generic.FundamentalSingleClass .F4 (f4Datum (GaloisField p e)) :=
    fundamentalSingleClass .F4 0 p e Fact.out trivial hadm (by decide) (by decide)
  have hθmem : stdRankOne (f4Datum (GaloisField p e)) thetaF4 ∈
      Generic.fundamentalSubgroups .F4 (f4Datum (GaloisField p e)) :=
    ⟨1, thetaF4, Or.inl (isLongestRoot_f4Datum_of_iform_eq_four isRoot_thetaF4
      iform_thetaF4_self), (Generic.conjSub_one _).symm⟩
  obtain ⟨g, hg⟩ := hsingle _ hθmem R₁ (longestFundamental_subset .F4 _ h₁)
  have hR₁ : R₁ = (stdRankOne (f4Datum (GaloisField p e)) thetaF4).map
      (MulAut.conj g).toMonoidHom := hg
  obtain ⟨r₁, hr₁, rfl⟩ : ∃ r ∈ stdRankOne (f4Datum (GaloisField p e)) thetaF4,
      c₁ = g * r * g⁻¹ := by
    rw [hR₁] at hc₁
    obtain ⟨r, hr, hrc⟩ := hc₁
    exact ⟨r, hr, hrc.symm⟩
  have hor₁ : orderOf r₁ = 2 := by
    have := a2_orderOf_conj_eq_two ho₁ g⁻¹
    simpa [mul_assoc] using this
  have hd₁ := eq_signDiagF4_of_orderOf_eq_two hK isRoot_thetaF4 iform_thetaF4_self hr₁ hor₁
  set R₂' := R₂.map (MulAut.conj g⁻¹).toMonoidHom with hR₂'
  set c₂' : ↥(adjointGroup .F4 (GaloisField p e)) := g⁻¹ * c₂ * g with hc₂'
  have hR₂'l : R₂' ∈ longestFundamental (f4Datum (GaloisField p e)) :=
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
  have hcd : (c₂' : ModGL .F4 (GaloisField p e)) * signDiagF4 (GaloisField p e) thetaF4 =
      signDiagF4 (GaloisField p e) thetaF4 * (c₂' : ModGL .F4 (GaloisField p e)) := by
    rw [← hd₁]
    exact (congrArg Subtype.val hcomm').symm
  have hn' : ¬ ∀ r ∈ stdRankOne (f4Datum (GaloisField p e)) thetaF4, c₂' * r = r * c₂' := by
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
  rcases a2_normalized_F4 hadm hU hp2 hq hR₂'l hc₂'R ho₂' hcd hn' with ⟨W, hW⟩ | ⟨W, hW⟩
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

theorem a2BranchLeft_f4 (hadm : StatedLieAdmissible .F4 0 p e) (hU : A2UnitaryF4 p e) :
    A2BranchLeft p .F4 0 e :=
  fun hp2 hq _ h₁ _ h₂ _ _ hc₁ hc₂ ho₁ ho₂ hcomm hn =>
    a2BranchLeft_f4_aux hadm hU hp2 hq h₁ h₂ hc₁ hc₂ ho₁ ho₂ hcomm hn

end Main

end CFSG.ClassicalInvolution.ModelFacts.Levi
