module

public import CFSG.CharacterTheory.TwoRankLowerBound.CommutingInvolutions
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.Open CFSG.TwoRankLowerBound.Helpers CFSG.BenderSuzuki.PFAppendixIII

universe u v

variable {G : Type u} {X : Type v} [Group G] [MulAction G X]

theorem commuting_map_fixes_of_two_pretransitive
    (hdouble : MulAction.IsMultiplyPretransitive G X 2) (hcard : 3 ≤ Nat.card X)
    (pi : X → X) (hcommute : ∀ (g : G) (x : X), pi (g • x) = g • pi x) :
    ∀ x : X, pi x = x := by
  intro x
  by_contra hmove
  have hpair : ({x, pi x} : Set X).ncard = 2 := Set.ncard_pair (Ne.symm hmove)
  have hlt : ({x, pi x} : Set X).ncard < (Set.univ : Set X).ncard := by
    rw [hpair, Set.ncard_univ]
    omega
  obtain ⟨y, hy⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
  have hxy : x ≠ y := by
    intro h
    exact hy.2 (by simp [h])
  obtain ⟨g, hgx, hgpi⟩ :=
    MulAction.is_two_pretransitive_iff.mp hdouble (Ne.symm hmove) hxy
  have heq : pi x = y := by
    calc
      pi x = pi (g • x) := by rw [hgx]
      _ = g • pi x := hcommute g x
      _ = y := hgpi
  exact hy.2 (by simp [heq])

theorem full_centralizer_fixes_two_pretransitive_action
    (L : Subgroup G) (hdouble : MulAction.IsMultiplyPretransitive L X 2)
    (hcard : 3 ≤ Nat.card X) (k : G) (hk : k ∈ Subgroup.centralizer (L : Set G)) :
    ∀ x : X, k • x = x := by
  apply commuting_map_fixes_of_two_pretransitive hdouble hcard (fun x : X => k • x)
  intro l x
  change k • ((l : G) • x) = (l : G) • (k • x)
  rw [← mul_smul, ← mul_smul, ← Subgroup.mem_centralizer_iff.mp hk l l.property]

theorem central_involution_eq_of_pair_rank_one [Finite G]
    (a b : X) (hrank : twoRank ↥((MulAction.stabilizer G a) ⊓
      (MulAction.stabilizer G b)) ≤ 1)
    (u x : G) (hu : IsInvolution u) (hx : IsInvolution x)
    (huZ : u ∈ Subgroup.center G) (hua : u • a = a) (hub : u • b = b)
    (hxa : x • a = a) (hxb : x • b = b) : x = u := by
  let B := (MulAction.stabilizer G a) ⊓ (MulAction.stabilizer G b)
  have huB : u ∈ B := ⟨hua, hub⟩
  have hxB : x ∈ B := ⟨hxa, hxb⟩
  have hcomm : Commute (⟨x, hxB⟩ : B) (⟨u, huB⟩ : B) := by
    rw [commute_iff_eq]
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp huZ x
  have hxorder : orderOf (⟨x, hxB⟩ : B) = 2 :=
    (Subgroup.orderOf_mk x hxB).trans (orderOf_eq_prime_iff.mpr ⟨hx.sq_eq_one, hx.ne_one⟩)
  have huorder : orderOf (⟨u, huB⟩ : B) = 2 :=
    (Subgroup.orderOf_mk u huB).trans (orderOf_eq_prime_iff.mpr ⟨hu.sq_eq_one, hu.ne_one⟩)
  exact congrArg Subtype.val
    (commuting_involutions_eq_of_twoRank_le_one B hrank _ _ hxorder huorder hcomm)

theorem involution_with_two_fixed_points_eq_central [Finite G]
    (hdouble : MulAction.IsMultiplyPretransitive G X 2)
    (a b : X) (hab : a ≠ b) (hrank : twoRank ↥((MulAction.stabilizer G a) ⊓
      (MulAction.stabilizer G b)) ≤ 1)
    (u x : G) (hu : IsInvolution u) (hx : IsInvolution x)
    (huZ : u ∈ Subgroup.center G) (hua : u • a = a) (hub : u • b = b)
    (c d : X) (hcd : c ≠ d) (hxc : x • c = c) (hxd : x • d = d) : x = u := by
  obtain ⟨g, hga, hgb⟩ := MulAction.is_two_pretransitive_iff.mp hdouble hcd hab
  let y := g * x * g⁻¹
  have hy : IsInvolution y := by
    have h := isInvolution_rightConjugateElem (g := g⁻¹) hx
    simpa only [rightConjugateElem, inv_inv] using h
  have hyfix (e : X) (hxe : x • e = e) : y • (g • e) = g • e := by
    simp only [y, mul_smul, inv_smul_smul, hxe]
  have hyu : y = u := central_involution_eq_of_pair_rank_one a b hrank u y hu hy
    huZ hua hub (hga ▸ hyfix c hxc) (hgb ▸ hyfix d hxd)
  have hconj : g⁻¹ * y * g = x := by simp only [y, mul_assoc, inv_mul_cancel_left,
    inv_mul_cancel, mul_one]
  calc
    x = g⁻¹ * y * g := hconj.symm
    _ = g⁻¹ * u * g := by rw [hyu]
    _ = u := by rw [Subgroup.mem_center_iff.mp huZ g⁻¹, mul_assoc,
      inv_mul_cancel, mul_one]

theorem full_centralizer_involutions_singleton [Finite G]
    (L : Subgroup G) (hdouble : MulAction.IsMultiplyPretransitive L X 2)
    (hcard : 3 ≤ Nat.card X) (a b : X)
    (hrank : twoRank ↥((MulAction.stabilizer G a) ⊓ (MulAction.stabilizer G b)) ≤ 1)
    (u : G) (hu : IsInvolution u) (huZ : u ∈ Subgroup.center G)
    (hua : u • a = a) (hub : u • b = b) :
    {x : G | x ∈ Subgroup.centralizer (L : Set G) ∧ IsInvolution x} = {u} := by
  ext x
  constructor
  · rintro ⟨hxK, hx⟩
    have hfix := full_centralizer_fixes_two_pretransitive_action L hdouble hcard x hxK
    exact Set.mem_singleton_iff.mpr
      (central_involution_eq_of_pair_rank_one a b hrank u x hu hx huZ hua hub
        (hfix a) (hfix b))
  · intro hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    refine ⟨?_, hu⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l _
    exact Subgroup.mem_center_iff.mp huZ l

end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
