module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.FibreSplit
public import CFSG.RankThree.Literature.FSmithForm
public import CFSG.Assembly.Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

open CFSG.RankThree.Literature.FSmith

variable {Q Q' : Type} [Group Q] [Group Q'] [Finite Q] [Finite Q']
  [Module (ZMod 2) (Additive (Abelianization Q))] [Module (ZMod 2) (Additive (Abelianization Q'))]

theorem exists_mulEquiv_of_isometry (hE : IsExtraspecialPGroup 2 Q) (hE' : IsExtraspecialPGroup 2 Q')
    (a : Additive (Abelianization Q) ≃ₗ[ZMod 2] Additive (Abelianization Q'))
    (ha : ∀ v, extraspecialQuadForm hE' (a v) = extraspecialQuadForm hE v) :
    ∃ φ : Q ≃* Q', ∀ x : Q,
      a (Additive.ofMul (Abelianization.of x)) = Additive.ofMul (Abelianization.of (φ x)) := by
  classical
  obtain ⟨z0, hz0ne, -⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center Q)).1 hE.2.2.2
  let z : Q := (z0 : Q)
  have hzcenter : z ∈ Subgroup.center Q := z0.2
  have hz1 : z ≠ 1 := fun h => hz0ne (Subtype.ext h)
  obtain ⟨z0', hz0'ne, -⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center Q')).1 hE'.2.2.2
  let z' : Q' := (z0' : Q')
  have hz'center : z' ∈ Subgroup.center Q' := z0'.2
  have hz'1 : z' ≠ 1 := fun h => hz0'ne (Subtype.ext h)
  let ofQ : Q → Additive (Abelianization Q) := fun x => Additive.ofMul (Abelianization.of x)
  let ofQ' : Q' → Additive (Abelianization Q') := fun x => Additive.ofMul (Abelianization.of x)
  have ofQ_mul : ∀ x y : Q, ofQ (x * y) = ofQ x + ofQ y := fun x y => ofMul_of_mul x y
  have ofQ'_mul : ∀ x y : Q', ofQ' (x * y) = ofQ' x + ofQ' y := fun x y => ofMul_of_mul x y
  have ofQ_one : ofQ 1 = 0 := by simp [ofQ]
  have ofQ'_one : ofQ' 1 = 0 := by simp [ofQ']
  have ofQ_inv : ∀ x : Q, ofQ x⁻¹ = -ofQ x := fun x => by simp [ofQ]
  have ofQ'_inv : ∀ x : Q', ofQ' x⁻¹ = -ofQ' x := fun x => by simp [ofQ']
  let F : Subgroup (Q × Q') :=
    { carrier := {p | a (ofQ p.1) = ofQ' p.2}
      one_mem' := by
        change a (ofQ 1) = ofQ' 1
        rw [ofQ_one, ofQ'_one, map_zero]
      mul_mem' := by
        intro p q hp hq
        change a (ofQ (p.1 * q.1)) = ofQ' (p.2 * q.2)
        change a (ofQ p.1) = ofQ' p.2 at hp
        change a (ofQ q.1) = ofQ' q.2 at hq
        rw [ofQ_mul, ofQ'_mul, map_add, hp, hq]
      inv_mem' := by
        intro p hp
        change a (ofQ p.1⁻¹) = ofQ' p.2⁻¹
        change a (ofQ p.1) = ofQ' p.2 at hp
        rw [ofQ_inv, ofQ'_inv, map_neg, hp] }
  have hz_ofQ : ofQ z = 0 := (ofMul_of_eq_zero_iff hE z).mpr hzcenter
  have hz'_ofQ' : ofQ' z' = 0 := (ofMul_of_eq_zero_iff hE' z').mpr hz'center
  have hz_mem : (z, (1 : Q')) ∈ F := by
    change a (ofQ z) = ofQ' 1
    rw [hz_ofQ, ofQ'_one, map_zero]
  have hz'_mem : ((1 : Q), z') ∈ F := by
    change a (ofQ 1) = ofQ' z'
    rw [ofQ_one, hz'_ofQ', map_zero]
  have hzz'F : (z, z') ∈ F := by
    have := F.mul_mem hz_mem hz'_mem
    simpa using this
  have hπ₁ : ∀ l : Q, ∃ l' : Q', (l, l') ∈ F := by
    intro l
    obtain ⟨l', hl'⟩ := exists_ofMul_of (a (ofQ l))
    refine ⟨l', ?_⟩
    change a (ofQ l) = ofQ' l'
    exact hl'.symm
  have hπ₂ : ∀ l' : Q', ∃ l : Q, (l, l') ∈ F := by
    intro l'
    obtain ⟨l, hl⟩ := exists_ofMul_of (a.symm (ofQ' l'))
    refine ⟨l, ?_⟩
    change a (Additive.ofMul (Abelianization.of l)) = ofQ' l'
    rw [hl, LinearEquiv.apply_symm_apply]
  have hk₁ : ∀ l' : Q', ((1 : Q), l') ∈ F → l' = 1 ∨ l' = z' := by
    intro l' hl'
    have h0 : ofQ' l' = 0 := by
      have := hl'
      change a (ofQ 1) = ofQ' l' at this
      rw [ofQ_one, map_zero] at this
      exact this.symm
    have hmem : l' ∈ Subgroup.center Q' := (ofMul_of_eq_zero_iff hE' l').mp h0
    by_cases h1 : l' = 1
    · exact Or.inl h1
    · exact Or.inr (eq_of_mem_center hE' hmem hz'center h1 hz'1)
  have hk₂ : ∀ l : Q, (l, (1 : Q')) ∈ F → l = 1 ∨ l = z := by
    intro l hl
    have h0 : ofQ l = 0 := by
      have := hl
      change a (ofQ l) = ofQ' 1 at this
      rw [ofQ'_one] at this
      exact a.injective (this.trans (map_zero a).symm)
    have hmem : l ∈ Subgroup.center Q := (ofMul_of_eq_zero_iff hE l).mp h0
    by_cases h1 : l = 1
    · exact Or.inl h1
    · exact Or.inr (eq_of_mem_center hE hmem hzcenter h1 hz1)
  have center_pair : ∀ (c : Q) (c' : Q') (hcc' : (c, c') ∈ F),
      c ∈ Subgroup.center Q → c' ∈ Subgroup.center Q' →
      (⟨(c, c'), hcc'⟩ : F) ∈ Subgroup.center F := by
    intro c c' hcc' hc hc'
    rw [Subgroup.mem_center_iff]
    intro t
    apply Subtype.ext
    apply Prod.ext
    · change (t : Q × Q').1 * c = c * (t : Q × Q').1
      exact Subgroup.mem_center_iff.mp hc (t : Q × Q').1
    · change (t : Q × Q').2 * c' = c' * (t : Q × Q').2
      exact Subgroup.mem_center_iff.mp hc' (t : Q × Q').2
  let g : F := ⟨(z, z'), hzz'F⟩
  let hzF : F := ⟨(z, 1), hz_mem⟩
  have hzF_center : hzF ∈ Subgroup.center F :=
    center_pair z 1 hz_mem hzcenter (Subgroup.one_mem _)
  have hg_center : g ∈ Subgroup.center F := center_pair z z' hzz'F hzcenter hz'center
  let Δ : Subgroup F := Subgroup.zpowers g
  have hΔcenter : Δ ≤ Subgroup.center F := by
    change Subgroup.zpowers g ≤ Subgroup.center F
    exact Subgroup.zpowers_le.mpr hg_center
  haveI : Δ.Normal := Subgroup.normal_of_le_center hΔcenter
  have hzF_ne_one : hzF ≠ 1 := by
    intro h
    exact hz1 (congrArg (fun t : F => (t : Q × Q').1) h)
  have hzF_ne_g : hzF ≠ g := by
    intro h
    exact hz'1 (congrArg (fun t : F => (t : Q × Q').2) h).symm
  have hg_sq : g ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    change ((z, z') : Q × Q') ^ 2 = (1 : Q × Q')
    have hp : ((z, z') : Q × Q') ^ 2 = (z ^ 2, z' ^ 2) := Prod.ext rfl rfl
    rw [hp, sq_eq_one_of_mem_center hE hzcenter, sq_eq_one_of_mem_center hE' hz'center]
    rfl
  have hg1 : g ≠ 1 := by
    intro h
    exact hz1 (congrArg (fun t : F => (t : Q × Q').1) h)
  have hord : orderOf g = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hg_sq hg1
  have hzΔ : hzF ∉ Δ := by
    change hzF ∉ Subgroup.zpowers g
    intro hmem
    rw [mem_zpowers_iff_mem_range_orderOf, hord] at hmem
    obtain ⟨n, hn, hn_eq⟩ := Finset.mem_image.mp hmem
    have hn2 : n < 2 := Finset.mem_range.mp hn
    have hn01 : n = 0 ∨ n = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp hn2)
    rcases hn01 with rfl | rfl
    · rw [pow_zero] at hn_eq
      exact hzF_ne_one hn_eq.symm
    · rw [pow_one] at hn_eq
      exact hzF_ne_g hn_eq.symm
  have hzz'_mem : g ∈ Δ := by
    change g ∈ Subgroup.zpowers g
    exact Subgroup.mem_zpowers_iff.mpr ⟨1, zpow_one g⟩
  have hzz' : ∃ h : (z, z') ∈ F, (⟨(z, z'), h⟩ : F) ∈ Δ :=
    ⟨hzz'F, by simpa [g] using hzz'_mem⟩
  have hsq_all : ∀ t : F, t ^ 2 ∈ Δ := by
    intro t
    let x : Q := (t : Q × Q').1
    let y : Q' := (t : Q × Q').2
    have hf : a (ofQ x) = ofQ' y := t.2
    have hx2 : x ^ 2 = 1 ∨ x ^ 2 = z := by
      by_cases h : x ^ 2 = 1
      · exact Or.inl h
      · exact Or.inr (eq_of_mem_center hE (sq_mem_center hE x) hzcenter h hz1)
    have hy2 : y ^ 2 = 1 ∨ y ^ 2 = z' := by
      by_cases h : y ^ 2 = 1
      · exact Or.inl h
      · exact Or.inr (eq_of_mem_center hE' (sq_mem_center hE' y) hz'center h hz'1)
    have hquad : extraspecialQuadForm hE (ofQ x) = 0 ↔ extraspecialQuadForm hE' (ofQ' y) = 0 := by
      have h1 : extraspecialQuadForm hE (ofQ x) = extraspecialQuadForm hE' (a (ofQ x)) :=
        (ha (ofQ x)).symm
      rw [h1, hf]
    have hx0 : extraspecialQuadForm hE (ofQ x) = 0 ↔ x ^ 2 = 1 := by
      change extraspecialQuadForm hE (Additive.ofMul (Abelianization.of x)) = 0 ↔ x ^ 2 = 1
      rw [extraspecialQuadForm_apply]
      constructor
      · intro h
        by_contra hne
        rw [if_neg hne] at h
        exact one_ne_zero h
      · intro h
        rw [if_pos h]
    have hy0 : extraspecialQuadForm hE' (ofQ' y) = 0 ↔ y ^ 2 = 1 := by
      change extraspecialQuadForm hE' (Additive.ofMul (Abelianization.of y)) = 0 ↔ y ^ 2 = 1
      rw [extraspecialQuadForm_apply]
      constructor
      · intro h
        by_contra hne
        rw [if_neg hne] at h
        exact one_ne_zero h
      · intro h
        rw [if_pos h]
    have hiff : x ^ 2 = 1 ↔ y ^ 2 = 1 := hx0.symm.trans (hquad.trans hy0)
    have ht2eq : (t : Q × Q') ^ 2 = (x ^ 2, y ^ 2) := Prod.ext rfl rfl
    rcases hx2 with hx1 | hxz
    · have hy1 : y ^ 2 = 1 := hiff.mp hx1
      have ht2 : t ^ 2 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one, ht2eq, hx1, hy1]
        rfl
      rw [ht2]
      exact Δ.one_mem
    · have hx_ne1 : x ^ 2 ≠ 1 := by rw [hxz]; exact hz1
      have hy_ne1 : y ^ 2 ≠ 1 := fun h => hx_ne1 (hiff.mpr h)
      have hyz : y ^ 2 = z' := by
        rcases hy2 with h | h
        · exact absurd h hy_ne1
        · exact h
      have ht2 : t ^ 2 = g := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, ht2eq, hxz, hyz]
      rw [ht2]
      exact hzz'_mem
  have hT : Odd (⊤ : Subgroup F).index := by
    rw [Subgroup.index_top]
    exact ⟨0, rfl⟩
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_of_fibre F z z' hz_mem hz'_mem hπ₁ hπ₂ hk₁ hk₂ Δ
    hzF_center hzΔ hzz' ⊤ le_top (Subgroup.mem_top _) hT (fun t _ => hsq_all t)
  refine ⟨φ, ?_⟩
  intro x
  have hmem := hφ x
  change a (ofQ x) = ofQ' (φ x) at hmem
  exact hmem

end CFSG.EvenSporadicStandard.HNRecog.ML1
