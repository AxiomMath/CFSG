module

public import CFSG.RankThree.PartOne.SEITZ3.PlaneCount

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Proving

open Subgroup

theorem centralizer_le_closure_cenGen {G : Type*} [Group G] [Finite G] {r : ℕ} [Fact r.Prime]
    {E : Subgroup G} (P : Sylow r G) (hEP : E ≤ (P : Subgroup G))
    (hPab : ∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), x * y = y * x)
    (hΩ : ∀ x ∈ (P : Subgroup G), x ^ r = 1 → x ∈ E) {c : G}
    (hc : c ∈ Subgroup.closure (CFSG.RankThree.PartOne.SEITZ3.cenGen E)) (hcr : c ^ r = 1)
    (hc1 : c ≠ 1) :
    Subgroup.centralizer {c} ≤ Subgroup.closure (CFSG.RankThree.PartOne.SEITZ3.cenGen E) := by
  have mem_cenGen : ∀ k x : G, x ∈ E → x ≠ 1 → k * x = x * k →
      k ∈ CFSG.RankThree.PartOne.SEITZ3.cenGen E := by
    intro k x hx hx1 hk
    unfold CFSG.RankThree.PartOne.SEITZ3.cenGen
    exact ⟨x, hx, hx1, hk⟩
  obtain ⟨e, heE, he1⟩ : ∃ e ∈ E, e ≠ 1 := by
    by_contra hno
    simp only [not_exists, not_and, ne_eq, not_not] at hno
    have hempty : CFSG.RankThree.PartOne.SEITZ3.cenGen E = ∅ := by
      ext k
      constructor
      · rintro ⟨x, hx, hx1, -⟩
        exact absurd (hno x hx) hx1
      · intro h
        simp at h
    rw [hempty, Subgroup.closure_empty, Subgroup.mem_bot] at hc
    exact hc1 hc
  set H : Subgroup G := Subgroup.closure (CFSG.RankThree.PartOne.SEITZ3.cenGen E) with hH
  have hPH : (P : Subgroup G) ≤ H := by
    intro x hx
    exact Subgroup.subset_closure (mem_cenGen x e heE he1 (hPab x hx e (hEP heE)))
  let P' : Sylow r H :=
    { toSubgroup := (P : Subgroup G).subgroupOf H
      isPGroup' := P.isPGroup'.comap_subtype
      is_maximal' := by
        intro Q hQ hle
        have hQg : IsPGroup r (Q.map H.subtype) := hQ.map H.subtype
        have hPle : (P : Subgroup G) ≤ Q.map H.subtype := by
          intro x hx
          have hmem : (⟨x, hPH hx⟩ : H) ∈ (P : Subgroup G).subgroupOf H :=
            Subgroup.mem_subgroupOf.2 hx
          exact Subgroup.mem_map_of_mem H.subtype (hle hmem)
        have hQeq : Q.map H.subtype = (P : Subgroup G) := P.is_maximal' hQg hPle
        ext y
        rw [Subgroup.mem_subgroupOf]
        constructor
        · intro hy
          have hy' : (y : G) ∈ Q.map H.subtype := Subgroup.mem_map_of_mem H.subtype hy
          rwa [hQeq] at hy'
        · intro hy
          have hy' : (y : G) ∈ Q.map H.subtype := by
            rw [hQeq]
            exact hy
          obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hy'
          have hzeq : z = y := Subtype.ext hzy
          exact hzeq ▸ hz }
  have hcH : c ∈ H := hc
  let ch : H := ⟨c, hcH⟩
  have hchr : ch ^ r = 1 := Subtype.ext (by simpa using hcr)
  have hch1 : ch ≠ 1 := by
    intro h1
    apply hc1
    have := congrArg Subtype.val h1
    simpa [ch] using this
  have hzp : IsPGroup r (Subgroup.zpowers ch) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one, orderOf_eq_prime hchr hch1]
  obtain ⟨Q1, hQ1⟩ := IsPGroup.exists_le_sylow hzp
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H P' Q1
  have hchQ : ch ∈ (Q1 : Subgroup H) := hQ1 (Subgroup.mem_zpowers ch)
  rw [← hh, Sylow.coe_subgroup_smul] at hchQ
  have hchP : (MulAut.conj h)⁻¹ • ch ∈ (P : Subgroup G).subgroupOf H :=
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem.1 hchQ
  set g : G := (h : G) with hg
  have hgH : g ∈ H := h.2
  have hc'P : g⁻¹ * c * g ∈ (P : Subgroup G) := by
    have hmem := Subgroup.mem_subgroupOf.1 hchP
    simpa [ch, hg, MulAut.conj_inv_apply] using hmem
  have hc'r : (g⁻¹ * c * g) ^ r = 1 := by
    have hconj := conj_pow (a := g⁻¹) (b := c) (i := r)
    rw [inv_inv, hcr, mul_one] at hconj
    rw [hconj]
    simp
  have hc'1 : g⁻¹ * c * g ≠ 1 := by
    intro h1
    apply hc1
    have hcg : c = g * (g⁻¹ * c * g) * g⁻¹ := by group
    rw [hcg, h1]
    simp
  have hc'E : g⁻¹ * c * g ∈ E := hΩ _ hc'P hc'r
  intro y hy
  have hyc : c * y = y * c := Subgroup.mem_centralizer_iff.1 hy c (Set.mem_singleton c)
  have hy' : g⁻¹ * y * g ∈ H := by
    apply Subgroup.subset_closure
    refine mem_cenGen _ _ hc'E hc'1 ?_
    rw [show g⁻¹ * y * g * (g⁻¹ * c * g) = g⁻¹ * (y * c) * g by group,
      show g⁻¹ * c * g * (g⁻¹ * y * g) = g⁻¹ * (c * y) * g by group, hyc]
  have hyeq : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
  have := H.mul_mem (H.mul_mem hgH hy') (H.inv_mem hgH)
  rwa [hyeq] at this

end CFSG.HardMathSupport.Seitz.TrialityOdd.Proving

end
