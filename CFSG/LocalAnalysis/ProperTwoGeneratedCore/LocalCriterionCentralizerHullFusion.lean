module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullAction
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OrbitGeometry
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingConjugacy

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.PFAppendixIII
open CFSG.BenderSuzuki.PFchapter1section1 CFSG.ShultStronglyClosedTI

universe u v

variable {G : Type u} {X : Type v} [Group G] [MulAction G X]

theorem outside_two_hull_cosets_not_mem_join
    (L : Subgroup G) [L.Normal] (x u : G) (hx : IsInvolution x)
    (huL : u ∉ L) (huxL : u * x ∉ L) : u ∉ L ⊔ Subgroup.zpowers x := by
  intro huA
  obtain ⟨l, hl, k, hk, hlku⟩ := Subgroup.mem_sup_of_normal_left.mp huA
  have hxorder : orderOf x = 2 := orderOf_eq_prime_iff.mpr ⟨hx.sq_eq_one, hx.ne_one⟩
  rcases (mem_zpowers_involution_iff hxorder).mp hk with hkone | hkx
  · apply huL
    have hlu : l = u := by simpa only [hkone, mul_one] using hlku
    exact hlu ▸ hl
  · apply huxL
    have heq : u * x = l := by
      rw [← hlku, hkx, mul_assoc, ← pow_two, hx.sq_eq_one, mul_one]
    exact heq.symm ▸ hl

theorem stabilizer_strong_embedding_of_unique_involution_fixed_points [Finite G]
    (a : X) (hproper : MulAction.stabilizer G a ≠ ⊤)
    (z : G) (hz : IsInvolution z) (hza : z • a = a)
    (hunique : ∀ (x : G), IsInvolution x → ∀ (b c : X),
      x • b = b → x • c = c → b = c) :
    IsStronglyEmbedded (MulAction.stabilizer G a) := by
  refine ⟨hproper, ⟨z, hza, hz⟩, ?_⟩
  intro g hg x hxa hxconj hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxconj
  have hyfix : y • a = a := hy
  have hyx' : g⁻¹ * y * g = x := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hyx
  have hxother : x • (g⁻¹ • a) = g⁻¹ • a := by
    rw [← hyx']
    simp only [mul_smul, smul_inv_smul, hyfix]
  have heq := hunique x hx a (g⁻¹ • a) hxa hxother
  apply hg
  change g • a = a
  have h := congrArg (fun b : X => g • b) heq
  simpa only [smul_inv_smul] using h

theorem entire_involution_two_hull_cosets [Finite G]
    (L : Subgroup G) [L.Normal]
    (hdouble : MulAction.IsMultiplyPretransitive L X 2)
    (a b : X) (hab : a ≠ b)
    (hrank : twoRank ↥((MulAction.stabilizer G a) ⊓ (MulAction.stabilizer G b)) ≤ 1)
    (u : G) (hu : IsInvolution u) (huZ : u ∈ Subgroup.center G)
    (huL : u ∉ L) (hua : u • a = a) (hub : u • b = b)
    (z : G) (hzL : z ∈ L) (hz : IsInvolution z) (hza : z • a = a) :
    ∀ x : G, IsInvolution x → x = u ∨ x ∈ L ∨ u * x ∈ L := by
  have hdoubleG : MulAction.IsMultiplyPretransitive G X 2 := by
    apply MulAction.is_two_pretransitive_iff.mpr
    intro c d c' d' hcd hcd'
    obtain ⟨l, hlc, hld⟩ := MulAction.is_two_pretransitive_iff.mp hdouble hcd hcd'
    exact ⟨l, hlc, hld⟩
  intro x hx
  by_cases hxu : x = u
  · exact Or.inl hxu
  by_cases hxL : x ∈ L
  · exact Or.inr (Or.inl hxL)
  by_cases huxL : u * x ∈ L
  · exact Or.inr (Or.inr huxL)
  exfalso
  let A := L ⊔ Subgroup.zpowers x
  have huA : u ∉ A := outside_two_hull_cosets_not_mem_join L x u hx huL huxL
  have hdoubleA : MulAction.IsMultiplyPretransitive A X 2 := by
    apply MulAction.is_two_pretransitive_iff.mpr
    intro c d c' d' hcd hcd'
    obtain ⟨l, hlc, hld⟩ := MulAction.is_two_pretransitive_iff.mp hdouble hcd hcd'
    exact ⟨⟨l, Subgroup.mem_sup_left l.property⟩, hlc, hld⟩
  have hproper : MulAction.stabilizer A a ≠ ⊤ := by
    intro htop
    obtain ⟨g, hga, _hgb⟩ := MulAction.is_two_pretransitive_iff.mp hdoubleA hab hab.symm
    have hgmem : g ∈ MulAction.stabilizer A a := by
      rw [htop]
      exact Subgroup.mem_top g
    have hgfix : g • a = a := hgmem
    exact hab (hgfix.symm.trans hga)
  have hzA : z ∈ A := Subgroup.mem_sup_left hzL
  have hSE : IsStronglyEmbedded (MulAction.stabilizer A a) :=
    stabilizer_strong_embedding_of_unique_involution_fixed_points a hproper
      ⟨z, hzA⟩ (IsInvolution.subtype hz hzA) hza (by
        intro y hy c d hyc hyd
        by_contra hcd
        have hyG : IsInvolution (y : G) :=
          ⟨fun h => hy.ne_one (Subtype.ext h), congrArg Subtype.val hy.sq_eq_one⟩
        have heq : (y : G) = u := involution_with_two_fixed_points_eq_central
          hdoubleG a b hab hrank u y hu hyG huZ hua hub c d hcd hyc hyd
        exact huA (heq ▸ y.property))
  have hxA : x ∈ A := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  obtain ⟨g, hgz⟩ := hSE.involutions_conjugate
    (IsInvolution.subtype hz hzA) (IsInvolution.subtype hx hxA)
  have hconj : (g : G)⁻¹ * z * g = x := congrArg Subtype.val hgz
  apply hxL
  rw [← hconj]
  exact (inferInstance : L.Normal).conj_mem' z hzL g

end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
