module

public import CFSG.GH74.Uniqueness.Section12Stmts
public import CFSG.GH74.Uniqueness.Section7Cor713Defs

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem sq_eq_one_of_mem_zHull_conjugate (hZ : IsInvariantInvolutionSet Z)
    (hM : ∀ x ∈ zHull Z M, x ^ 2 = 1) (g : X) {x : X} (hx : x ∈ zHull Z (conjugate M g)) :
    x ^ 2 = 1 := by
  have hle : zHull Z (conjugate M g) ≤ (zHull Z M).comap (MulAut.conj g).toMonoidHom := by
    rw [zHull, Subgroup.closure_le]
    rintro y ⟨hyZ, hyM⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    have e : (MulAut.conj g).toMonoidHom y = g * y * g⁻¹ := by simp
    rw [e]
    refine Subgroup.subset_closure ⟨?_, mem_conjugate_iff.mp hyM⟩
    have := hZ.2 y hyZ g⁻¹
    rwa [inv_inv] at this
  have e : (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := by simp
  have h1 : ((MulAut.conj g).toMonoidHom x) ^ 2 = 1 := hM _ (hle hx)
  rw [e] at h1
  have h3 : g * x ^ 2 * g⁻¹ = 1 := by
    have e2 : (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ := by simp [pow_two, mul_assoc]
    rwa [e2] at h1
  have h4 := congrArg (fun w => g⁻¹ * w * g) h3
  simpa [mul_assoc] using h4

omit [Finite X] in
theorem eq_one_of_sq_eq_one_of_odd {Y : Subgroup X} (hY : Odd (Nat.card Y)) {x : X} (hxY : x ∈ Y)
    (hx2 : x ^ 2 = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  have h2 : orderOf x ∣ Nat.card Y := by
    have := orderOf_dvd_natCard (⟨x, hxY⟩ : ↥Y)
    simpa [Subgroup.orderOf_coe] using this
  have h3 : orderOf x ∣ Nat.gcd 2 (Nat.card Y) := Nat.dvd_gcd h1 h2
  have h4 : Nat.gcd 2 (Nat.card Y) = 1 := by
    have : Nat.Coprime 2 (Nat.card Y) := (Nat.coprime_two_left.mpr hY)
    exact this
  rw [h4] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

omit [Finite X] in
theorem isElemAbelian_zpowers_of_orderOf_two {x : X} (hx : orderOf x = 2) :
    Open.IsElemAbelian 2 (zpowers x) := by
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]
    exact (Commute.zpow_zpow_self x i j).eq
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx2, one_zpow]

theorem ZDSetup.lemma1212 (S : ZDSetup X Z M) : Lemma1212Stmt Z M := by
  intro c n i hL Y hY ⟨s, hs, hsN, y₀, hy₀Y, hy₀⟩
  have hY' : Odd (Nat.card Y) := hY
  set N : Subgroup X := normalizer (Y : Set X) with hN
  have hs2 : orderOf s = 2 := S.invariant.1 s hs
  obtain ⟨β, ⟨hβΩ, hsβ⟩, -⟩ := S.prodDisc.existsUnique_fixed_point S.invariant hs
  have hsβmem : s ∈ β := (S.prodDisc.conjugate_eq_iff_mem hβΩ).mp hsβ
  obtain ⟨g, rfl⟩ := hβΩ
  have hsinv : s⁻¹ ∈ normalizer (Y : Set X) := (normalizer (Y : Set X)).inv_mem hsN
  have hrank : Open.pRank 2 (zHull Z N) ≤ 1 := by
    by_contra hge
    push Not at hge
    have hYβ : Y ≤ conjugate M g := S.lemma313 hY' (Nat.succ_le_of_lt hge) hs hsN ⟨g, rfl⟩ hsβ
    apply hy₀
    have hcomm : ∀ y ∈ Y, s * y = y * s := by
      intro y hy
      have hyβ : y ∈ conjugate M g := hYβ hy
      have h1 : y⁻¹ * s * y ∈ Z := S.invariant.2 s hs y
      have h2 : y⁻¹ * s * y ∈ zHull Z (conjugate M g) :=
        Subgroup.subset_closure ⟨h1, (conjugate M g).mul_mem
          ((conjugate M g).mul_mem ((conjugate M g).inv_mem hyβ) hsβmem) hyβ⟩
      have h3 : s ∈ zHull Z (conjugate M g) := Subgroup.subset_closure ⟨hs, hsβmem⟩
      have h4 : s⁻¹ * (y⁻¹ * s * y) ∈ zHull Z (conjugate M g) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ h3) h2
      have h5 : s⁻¹ * (y⁻¹ * s * y) ∈ Y := by
        have e : s⁻¹ * (y⁻¹ * s * y) = (s⁻¹ * y⁻¹ * s) * y := by group
        rw [e]
        refine Y.mul_mem ?_ hy
        have := (Subgroup.mem_normalizer_iff.mp hsinv y⁻¹).mp (Y.inv_mem hy)
        simpa using this
      have h6 : s⁻¹ * (y⁻¹ * s * y) = 1 :=
        eq_one_of_sq_eq_one_of_odd hY' h5
          (sq_eq_one_of_mem_zHull_conjugate S.invariant hL.m_abelian.2 g h4)
      have h7 : y⁻¹ * s * y = s := by
        have := congrArg (fun w => s * w) h6
        simpa using this
      calc s * y = y * (y⁻¹ * s * y) := by group
        _ = y * s := by rw [h7]
    exact hcomm y₀ hy₀Y
  have hNs : s ∈ zHull Z N := Subgroup.subset_closure ⟨hs, hsN⟩
  have hrank1 : 1 ≤ Open.pRank 2 (zHull Z N) := by
    refine CFSG.SectionRank.le_pRank (p := 2) (by norm_num) (E := zpowers s) ?_
      (isElemAbelian_zpowers_of_orderOf_two hs2) (k := 1) ?_
    · rw [Subgroup.zpowers_le]
      exact hNs
    · rw [Nat.card_zpowers, hs2, pow_one]
  refine ⟨le_antisymm hrank hrank1, ?_⟩
  have hrk : Open.twoRank ↥(zHull Z N) ≤ 1 := by
    rw [Open.twoRank, ← CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 2
      (by norm_num)]
    exact hrank
  have hempty : Z ∩ ((centralizer (Y : Set X) : Subgroup X) : Set X) = ∅ := by
    ext w
    simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_empty_iff_false, iff_false, not_and]
    intro hwZ hwC
    have hCN : centralizer (Y : Set X) ≤ N := (Subgroup.centralizer_le_normalizer _)
    have hwN : w ∈ zHull Z N := Subgroup.subset_closure ⟨hwZ, hCN hwC⟩
    obtain ⟨c', hc'⟩ := isConj_iff.mp (isConj_of_involutions_of_twoRank_le_one hrk
      (x := (⟨s, hNs⟩ : ↥(zHull Z N))) (y := (⟨w, hwN⟩ : ↥(zHull Z N)))
      (by rw [Subgroup.orderOf_mk]; exact hs2) (by rw [Subgroup.orderOf_mk]; exact S.invariant.1 w hwZ))
    have hc'X : (c' : X) * s * (c' : X)⁻¹ = w := by
      have := congrArg Subtype.val hc'
      simpa using this
    have hc'N : (c' : X) ∈ N := Cor713.zHull_le N c'.2
    have hy' : (c' : X) * y₀ * (c' : X)⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp hc'N y₀).mp hy₀Y
    have hw1 := Subgroup.mem_centralizer_iff.mp hwC _ hy'
    rw [← hc'X] at hw1
    have h2 : (c' : X) * (y₀ * s) * (c' : X)⁻¹ = (c' : X) * (s * y₀) * (c' : X)⁻¹ := by
      calc (c' : X) * (y₀ * s) * (c' : X)⁻¹
          = ((c' : X) * y₀ * (c' : X)⁻¹) * ((c' : X) * s * (c' : X)⁻¹) := by group
        _ = ((c' : X) * s * (c' : X)⁻¹) * ((c' : X) * y₀ * (c' : X)⁻¹) := hw1
        _ = (c' : X) * (s * y₀) * (c' : X)⁻¹ := by group
    exact hy₀ (mul_left_cancel (mul_right_cancel h2)).symm
  rw [zHull, hempty, Subgroup.closure_empty]

end CFSG.GH74.Uniqueness
