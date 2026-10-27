module

public import CFSG.LieType.Chevalley.G2FieldFourCover
public import CFSG.LocalAnalysis.EvenSmallLie.GTwoFour.Centralizers

public noncomputable section

namespace CFSG.EvenSmallLie.GTwoFour

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.LieType.Chevalley.G2FieldFour CFSG.LocalAnalysis.ComponentInitial
open Subgroup
open scoped commutatorElement

variable {K : Type} [Field K] {M : Type*} [Group M] {π : M →* adjointGroup .G2 K}

local notation "X" => pinnedX Tag.G2 K

theorem commute_of_commutatorElement (hker : ∀ k, π k = 1 → k ∈ center M) {e p q : M}
    (hp : π e * π p = π p * π e) (hq : π e * π q = π q * π e) : e * ⁅p, q⁆ = ⁅p, q⁆ * e := by
  have h1 : π (e * p * e⁻¹) = π p := by rw [map_mul, map_mul, map_inv, hp, mul_inv_cancel_right]
  have h2 : π (e * q * e⁻¹) = π q := by rw [map_mul, map_mul, map_inv, hq, mul_inv_cancel_right]
  have h := LinearCover.HeisenbergRoots.commutatorElement_eq_of_map_eq π hker h1 h2
  have e' : ⁅e * p * e⁻¹, e * q * e⁻¹⁆ = e * ⁅p, q⁆ * e⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e', mul_inv_eq_iff_eq_mul] at h
  exact h

theorem mul_comm_of_map_eq (hker : ∀ k, π k = 1 → k ∈ center M) {e e' f : M} (he : π e = π e')
    (hf : e * f = f * e) : e' * f = f * e' := by
  have hc : e⁻¹ * e' ∈ center M := hker _ (by rw [map_mul, map_inv, he, inv_mul_cancel])
  have h' : e' = e * (e⁻¹ * e') := by group
  rw [h', mul_assoc, (mem_center_iff.1 hc f).symm, ← mul_assoc, hf, mul_assoc]

section CharTwo

variable [CharP K 2]

theorem commute_rootX_a_nr
    (x y : K) : Commute (rootX rootA x) (rootX g2nr y) :=
  Subtype.ext (commute_a_nr x y)

theorem commutator_rootX_v_nr
    (x y : K) :
    ⁅rootX rootV x, rootX g2nr y⁆ = rootX rootA (x * y ^ 2) * rootX rootC (x ^ 2 * y) :=
  Subtype.ext (comm_v_nr x y)

variable (hη : Function.Surjective π) (hker : ∀ k, π k = 1 → k ∈ center M)
include hη hker

theorem lift_commute_c
    {e e' : M} {s s' : K} (he : π e = rootX rootC s)
    (he' : π e' = rootX rootC s') : e * e' = e' * e := by
  obtain ⟨p, hp⟩ := hη (rootX rootU s')
  obtain ⟨q, hq⟩ := hη (rootX rootV 1)
  have hpq : π ⁅p, q⁆ = π e' := by
    rw [map_commutatorElement, hp, hq, commutator_rootX_uv, mul_one, he']
  have hc := commute_of_commutatorElement hker (e := e) (p := p) (q := q)
    (by rw [he, hp]; exact (commute_rootX_uc s' s).eq.symm)
    (by rw [he, hq]; exact (commute_rootX_vc 1 s).eq.symm)
  exact (mul_comm_of_map_eq hker hpq hc.symm).symm

theorem lift_commute_b
    {e e' : M} {s s' : K} (he : π e = rootX rootB s)
    (he' : π e' = rootX rootB s') : e * e' = e' * e := by
  obtain ⟨p, hp⟩ := hη (rootX rootR 1)
  obtain ⟨q, hq⟩ := hη (rootX rootV s')
  have hpq : π ⁅p, q⁆ = π e' := by
    rw [map_commutatorElement, hp, hq, commutator_rootX_rv, one_mul, he']
  have hc := commute_of_commutatorElement hker (e := e) (p := p) (q := q)
    (by rw [he, hp]; exact (commute_rootX_rb 1 s).eq.symm)
    (by rw [he, hq]; exact (commute_rootX_vb s' s).eq.symm)
  exact (mul_comm_of_map_eq hker hpq hc.symm).symm

theorem lift_commute_a_c
    {e e' : M} {s s' : K} (he : π e = rootX rootA s)
    (he' : π e' = rootX rootC s') : e * e' = e' * e := by
  obtain ⟨p, hp⟩ := hη (rootX rootU s')
  obtain ⟨q, hq⟩ := hη (rootX rootV 1)
  have hpq : π ⁅p, q⁆ = π e' := by
    rw [map_commutatorElement, hp, hq, commutator_rootX_uv, mul_one, he']
  have hc := commute_of_commutatorElement hker (e := e) (p := p) (q := q)
    (by rw [he, hp]; exact (commute_rootX_au s s').eq)
    (by rw [he, hq]; exact (commute_rootX_av s 1).eq)
  exact (mul_comm_of_map_eq hker hpq hc.symm).symm

theorem lift_commute_b_c
    {e e' : M} {s s' : K} (he : π e = rootX rootB s)
    (he' : π e' = rootX rootC s') : e * e' = e' * e := by
  obtain ⟨p, hp⟩ := hη (rootX rootU s')
  obtain ⟨q, hq⟩ := hη (rootX rootV 1)
  have hpq : π ⁅p, q⁆ = π e' := by
    rw [map_commutatorElement, hp, hq, commutator_rootX_uv, mul_one, he']
  have hc := commute_of_commutatorElement hker (e := e) (p := p) (q := q)
    (by rw [he, hp]; exact (commute_rootX_ub s' s).eq.symm)
    (by rw [he, hq]; exact (commute_rootX_vb 1 s).eq.symm)
  exact (mul_comm_of_map_eq hker hpq hc.symm).symm

theorem lift_commute_a
    {e e' : M} {s s' : K} (he : π e = rootX rootA s)
    (he' : π e' = rootX rootA s') : e * e' = e' * e := by
  obtain ⟨p, hp⟩ := hη (rootX rootV s')
  obtain ⟨q, hq⟩ := hη (rootX g2nr 1)
  obtain ⟨w, hw⟩ := hη (rootX rootC (s' ^ 2))
  have hc := commute_of_commutatorElement hker (e := e) (p := p) (q := q)
    (by rw [he, hp]; exact (commute_rootX_av s s').eq)
    (by rw [he, hq]; exact (commute_rootX_a_nr s 1).eq)
  have hcw : e * w = w * e := lift_commute_a_c hη hker he hw
  have hpq : π (⁅p, q⁆ * w⁻¹) = π e' := by
    rw [map_mul, map_inv, map_commutatorElement, hp, hq, commutator_rootX_v_nr, one_pow, mul_one,
      mul_one, hw, mul_inv_cancel_right, he']
  have hc' : e * (⁅p, q⁆ * w⁻¹) = (⁅p, q⁆ * w⁻¹) * e := by
    have hw' : e * w⁻¹ = w⁻¹ * e := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, hcw, inv_mul_cancel_left]
    rw [← mul_assoc, hc, mul_assoc, hw', mul_assoc]
  exact (mul_comm_of_map_eq hker hpq hc'.symm).symm

end CharTwo

section Squares

variable [CharP K 2] {z : M} (hz1 : z ≠ 1) (hz : ∀ k, π k = 1 ↔ k = 1 ∨ k = z)
include hz1 hz

omit [CharP K 2] in
theorem mul_self_z : z * z = 1 := by
  have hz0 : π z = 1 := (hz z).2 (Or.inr rfl)
  rcases (hz (z * z)).1 (by rw [map_mul, hz0, mul_one]) with h | h
  · exact h
  · exact absurd (mul_eq_left.1 h) hz1

omit [CharP K 2] in
theorem mul_self_eq_of_map_eq (hker : ∀ k, π k = 1 → k ∈ center M) {e e' : M}
    (he : π e = π e') : e' * e' = e * e := by
  have hk : π (e⁻¹ * e') = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
  have hc := hker _ hk
  have hkk : (e⁻¹ * e') * (e⁻¹ * e') = 1 := by
    rcases (hz _).1 hk with h | h
    · rw [h, mul_one]
    · rw [h]; exact mul_self_z hz1 hz
  set k := e⁻¹ * e' with hk_def
  have h' : e' = e * k := by rw [hk_def]; group
  rw [h']
  calc e * k * (e * k) = e * (k * e) * k := by group
    _ = e * (e * k) * k := by rw [← mem_center_iff.1 hc e]
    _ = e * e * (k * k) := by group
    _ = e * e := by rw [hkk, mul_one]

omit [CharP K 2] hz1 in
theorem mul_self_eq_one_or
    (d : Fin Tag.G2.rank → ℤ) {e : M} {s : K}
    (he : π e = rootX d s) (h2 : rootX d s * rootX d s = 1) : e * e = 1 ∨ e * e = z :=
  (hz _).1 (by rw [map_mul, he, h2])

theorem mul_self_eq_one_of_isConj_rootX_c
    (hK : Nat.card K = 4) (hη : Function.Surjective π)
    (hker : ∀ k, π k = 1 → k ∈ center M) {m : M} (hm : IsConj (π m) (rootX rootC 1)) :
    m * m = 1 := by
  obtain ⟨g, hg⟩ := isConj_iff.1 hm
  obtain ⟨ĝ, hĝ⟩ := hη g
  suffices h : (ĝ * m * ĝ⁻¹) * (ĝ * m * ĝ⁻¹) = 1 by
    have h' : ĝ * (m * m) * ĝ⁻¹ = 1 := by rw [← h]; group
    rwa [mul_inv_eq_one, mul_eq_left] at h'
  set m₀ := ĝ * m * ĝ⁻¹ with hm₀
  have hm₀π : π m₀ = rootX rootC 1 := by rw [hm₀, map_mul, map_mul, map_inv, hĝ, hg]
  obtain ⟨ω, hω1, -, hωsq⟩ := exists_unit_ne_one (K := K) hK
  let h₀ : adjointGroup .G2 K := ⟨torusElt .G2 K g2ia ω, torusElt_mem_adjointGroup _ _⟩
  obtain ⟨ĥ, hĥ⟩ := hη h₀
  have hconj : ∀ x : K, h₀ * rootX rootC x * h₀⁻¹ = rootX rootC ((ω : K) * x) := fun x =>
    Subtype.ext (torus_a_c ω x)
  set m₁ := ĥ * m₀ * ĥ⁻¹ with hm₁
  set m₂ := ĥ * m₁ * ĥ⁻¹ with hm₂
  have hm₁π : π m₁ = rootX rootC (ω : K) := by
    rw [hm₁, map_mul, map_mul, map_inv, hĥ, hm₀π, hconj, mul_one]
  have hm₂π : π m₂ = rootX rootC ((ω : K) ^ 2) := by
    rw [hm₂, map_mul, map_mul, map_inv, hĥ, hm₁π, hconj, sq]
  have hc01 := lift_commute_c hη hker hm₀π hm₁π
  have hc02 := lift_commute_c hη hker hm₀π hm₂π
  have hc12 := lift_commute_c hη hker hm₁π hm₂π
  have hprod : π (m₀ * m₁ * m₂) = 1 := by
    rw [map_mul, map_mul, hm₀π, hm₁π, hm₂π, ← rootX_add, ← rootX_add]
    have : (1 : K) + ω + (ω : K) ^ 2 = 0 := by linear_combination hωsq
    rw [this, rootX_zero]
  have hk : (m₀ * m₁ * m₂) * (m₀ * m₁ * m₂) = 1 := by
    rcases (hz _).1 hprod with h | h
    · rw [h, mul_one]
    · rw [h]; exact mul_self_z hz1 hz
  have hsq₁ : m₁ * m₁ = m₀ * m₀ := by
    have hc := hker _ ((hz _).2 (mul_self_eq_one_or hz rootC hm₀π
      (by rw [← rootX_add, CharTwo.add_self_eq_zero, rootX_zero])))
    rw [hm₁, show ĥ * m₀ * ĥ⁻¹ * (ĥ * m₀ * ĥ⁻¹) = ĥ * (m₀ * m₀) * ĥ⁻¹ by group,
      mem_center_iff.1 hc ĥ, mul_inv_cancel_right]
  have hsq₂ : m₂ * m₂ = m₀ * m₀ := by
    have hc := hker _ ((hz _).2 (mul_self_eq_one_or hz rootC hm₁π
      (by rw [← rootX_add, CharTwo.add_self_eq_zero, rootX_zero])))
    rw [hm₂, show ĥ * m₁ * ĥ⁻¹ * (ĥ * m₁ * ĥ⁻¹) = ĥ * (m₁ * m₁) * ĥ⁻¹ by group,
      mem_center_iff.1 hc ĥ, mul_inv_cancel_right, hsq₁]
  have hsq0 : m₀ * m₀ * (m₀ * m₀) = 1 := by
    rcases mul_self_eq_one_or hz rootC hm₀π
      (by rw [← rootX_add, CharTwo.add_self_eq_zero, rootX_zero]) with h | h
    · rw [h, mul_one]
    · rw [h]; exact mul_self_z hz1 hz
  have hexp : (m₀ * m₁ * m₂) * (m₀ * m₁ * m₂) = (m₀ * m₀) * (m₁ * m₁) * (m₂ * m₂) := by
    calc (m₀ * m₁ * m₂) * (m₀ * m₁ * m₂) = m₀ * m₁ * (m₂ * m₀) * m₁ * m₂ := by group
      _ = m₀ * m₁ * (m₀ * m₂) * m₁ * m₂ := by rw [hc02]
      _ = m₀ * (m₁ * m₀) * (m₂ * m₁) * m₂ := by group
      _ = m₀ * (m₀ * m₁) * (m₁ * m₂) * m₂ := by rw [hc01, hc12]
      _ = (m₀ * m₀) * (m₁ * m₁) * (m₂ * m₂) := by group
  rw [hexp, hsq₁, hsq₂, hsq0, one_mul] at hk
  exact hk

theorem mul_self_eq_of_isConj_rootX_v
    (hK : Nat.card K = 4) [Finite M] [Group.IsPerfect M]
    (hη : Function.Surjective π) (hker : ∀ k, π k = 1 → k ∈ center M) {m : M}
    (hm : IsConj (π m) (rootX rootV 1)) : m * m = z := by
  have key : ∀ m₀ : M, π m₀ = rootX rootV 1 → m₀ * m₀ = z := by
    intro m₀ hm₀
    by_contra hne
    have hsq0 : m₀ * m₀ = 1 := (mul_self_eq_one_or hz rootV hm₀
      (by rw [← rootX_add, CharTwo.add_self_eq_zero, rootX_zero])).resolve_right hne
    have hinv : ∀ (e : M) (s : K), π e = rootX rootV s → e * e = 1 := by
      intro e s he
      by_cases hs : s = 0
      · have h0 : π e = 1 := by rw [he, hs, rootX_zero]
        rcases (hz e).1 h0 with h | h
        · rw [h, mul_one]
        · rw [h]; exact mul_self_z hz1 hz
      · let d : adjointGroup .G2 K :=
          ⟨torusElt .G2 K g2ir (Units.mk0 s hs), torusElt_mem_adjointGroup _ _⟩
        obtain ⟨d', hd'⟩ := hη d
        have hπ : π (d' * m₀ * d'⁻¹) = π e := by
          rw [map_mul, map_mul, map_inv, hd', hm₀, he]
          apply Subtype.ext
          change torusElt .G2 K g2ir (Units.mk0 s hs) * X g2v 1 *
            (torusElt .G2 K g2ir (Units.mk0 s hs))⁻¹ = X g2v s
          rw [torus_r_v, Units.val_mk0, mul_one]
        rw [mul_self_eq_of_map_eq hz1 hz hker hπ,
          show d' * m₀ * d'⁻¹ * (d' * m₀ * d'⁻¹) = d' * (m₀ * m₀) * d'⁻¹ by group, hsq0,
          mul_one, mul_inv_cancel]
    have habv : ∀ (e e' : M) (s s' : K), π e = rootX rootV s → π e' = rootX rootV s' →
        e * e' = e' * e := by
      intro e e' s s' he he'
      have h1 := hinv (e * e') (s + s') (by rw [map_mul, he, he', rootX_add])
      have h2 := inv_eq_of_mul_eq_one_right (hinv e s he)
      have h3 := inv_eq_of_mul_eq_one_right (hinv e' s' he')
      have h4 := (inv_eq_of_mul_eq_one_right h1).symm
      rwa [mul_inv_rev, h2, h3] at h4
    have hweyl : ∀ (i : Fin Tag.G2.rank) {d d' : Fin Tag.G2.rank → ℤ}, IsRoot .G2 d →
        reflect .G2 i d = d' → (∀ (e e' : M) (s s' : K), π e = rootX d' s → π e' = rootX d' s' →
          e * e' = e' * e) →
        ∀ (e e' : M) (s s' : K), π e = rootX d s → π e' = rootX d s' → e * e' = e' * e := by
      intro i d d' hd hdd' hab' e e' s s' he he'
      let n : adjointGroup .G2 K := ⟨weylElt .G2 K i 1, weylElt_mem_adjointGroup _ _⟩
      obtain ⟨n', hn'⟩ := hη n
      have hconj : ∀ x : K, n * rootX d x * n⁻¹ = rootX d' x := fun x => Subtype.ext (by
        change weylElt .G2 K i 1 * X d x * (weylElt .G2 K i 1)⁻¹ = X d' x
        rw [weylElt_conj i hd, hdd'])
      have h := hab' (n' * e * n'⁻¹) (n' * e' * n'⁻¹) s s'
        (by rw [map_mul, map_mul, map_inv, hn', he, hconj])
        (by rw [map_mul, map_mul, map_inv, hn', he', hconj])
      have h' : n' * (e * e') * n'⁻¹ = n' * (e' * e) * n'⁻¹ := by
        rw [show n' * (e * e') * n'⁻¹ = n' * e * n'⁻¹ * (n' * e' * n'⁻¹) by group, h]
        group
      exact mul_left_cancel (mul_right_cancel h')
    have habu := hweyl g2ir isRoot_g2u reflect_r_u habv
    have habr := hweyl g2ia isRoot_g2r reflect_a_r habu
    have hab : ∀ d : Fin Tag.G2.rank → ℤ, IsRoot .G2 d → 0 < height d →
        ∀ x ∈ ((rootSubgroup .G2 K d).subgroupOf (adjointGroup .G2 K)).comap π,
        ∀ y ∈ ((rootSubgroup .G2 K d).subgroupOf (adjointGroup .G2 K)).comap π,
          x * y = y * x := by
      intro d hd1 hd2 x hx y hy
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, mem_rootSubgroup] at hx hy
      obtain ⟨c, hc⟩ := hx
      obtain ⟨c', hc'⟩ := hy
      have hx' : π x = rootX d c := Subtype.ext hc.symm
      have hy' : π y = rootX d c' := Subtype.ext hc'.symm
      have hd : d ∈ G2FieldFour.posRoots := G2FieldFour.mem_posRoots.2 ⟨hd1, hd2⟩
      rcases Finset.mem_insert.1 hd with rfl | hd
      · exact lift_commute_a hη hker hx' hy'
      rcases Finset.mem_insert.1 hd with rfl | hd
      · exact habr x y c c' hx' hy'
      rcases Finset.mem_insert.1 hd with rfl | hd
      · exact habu x y c c' hx' hy'
      rcases Finset.mem_insert.1 hd with rfl | hd
      · exact habv x y c c' hx' hy'
      rcases Finset.mem_insert.1 hd with rfl | hd
      · exact lift_commute_b hη hker hx' hy'
      rw [Finset.mem_singleton.1 hd] at hx' hy'
      exact lift_commute_c hη hker hx' hy'
    have h2 : IsPGroup 2 π.ker := fun k => ⟨1, Subtype.ext (by
      rw [pow_one, SubgroupClass.coe_pow, sq, OneMemClass.coe_one]
      rcases (hz k).1 k.2 with h | h
      · rw [h, mul_one]
      · rw [h]; exact mul_self_z hz1 hz)⟩
    obtain ⟨hbot, -⟩ := G2_field_four_abelian_root_central_two_cover_trivial K hK π hη
      (fun k hk => hker k hk) h2 hab
    have hzk : z ∈ π.ker := (hz z).2 (Or.inr rfl)
    rw [hbot, Subgroup.mem_bot] at hzk
    exact hz1 hzk
  obtain ⟨g, hg⟩ := isConj_iff.1 hm
  obtain ⟨ĝ, hĝ⟩ := hη g
  have h := key (ĝ * m * ĝ⁻¹) (by rw [map_mul, map_mul, map_inv, hĝ, hg])
  have hzc : z ∈ center M := hker z ((hz z).2 (Or.inr rfl))
  have h' : ĝ * (m * m) * ĝ⁻¹ = z := by rw [← h]; group
  rw [mul_inv_eq_iff_eq_mul, ← mem_center_iff.1 hzc ĝ] at h'
  exact mul_left_cancel h'

end Squares

end CFSG.EvenSmallLie.GTwoFour
