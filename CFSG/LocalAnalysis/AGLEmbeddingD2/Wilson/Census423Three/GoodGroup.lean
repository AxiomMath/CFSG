module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census423Three.LocalStep

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census423Three

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Res423Two
open scoped commutatorElement

structure GoodGroup (S : Type) [Group S] : Prop where
  rad : ∀ N : Subgroup S, N.Normal → Group.IsSolvable N → ∀ n ∈ N, ∀ y : S, n * y = y * n
  elt3 : ∃ s : S, s ≠ 1 ∧ s ^ 3 = 1
  noCentral3 : ∀ z : S, (∀ y, z * y = y * z) → z ^ 3 = 1 → z = 1
  conj3 : ∀ x y : S, x ≠ 1 → x ^ 3 = 1 → y ≠ 1 → y ^ 3 = 1 →
    ∃ g : S, Subgroup.zpowers (g * x * g⁻¹) = Subgroup.zpowers y
  inner3 : ∀ α : MulAut S, α ^ 3 = 1 → ∃ s : S, ∀ y : S,
    (s * y * s⁻¹)⁻¹ * α y ∈ Subgroup.center S

theorem GoodGroup.of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T) (h : GoodGroup S) :
    GoodGroup T where
  rad N hN hs n hn y := by
    set N' : Subgroup S := N.comap e.toMonoidHom with hN'def
    have hN' : N'.Normal := hN.comap e.toMonoidHom
    have hs' : Group.IsSolvable N' := by
      have hmap : N'.map e.toMonoidHom = N :=
        Subgroup.map_comap_eq_self_of_surjective e.surjective N
      have : Group.IsSolvable ↥(N'.map e.toMonoidHom) := by rw [hmap]; exact hs
      exact Group.isSolvable_of_isSolvable_injective
        (f := (N'.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
        (N'.equivMapOfInjective e.toMonoidHom e.injective).injective
    have hn' : e.symm n ∈ N' := by
      rw [hN'def, Subgroup.mem_comap]
      simpa using hn
    have := h.rad N' hN' hs' _ hn' (e.symm y)
    have := congrArg e this
    simpa using this
  elt3 := by
    obtain ⟨s, hs1, hs3⟩ := h.elt3
    exact ⟨e s, fun h1 => hs1 (e.injective (by simpa using h1)), by rw [← map_pow, hs3, map_one]⟩
  noCentral3 z hz hz3 := by
    have hz' : ∀ y, e.symm z * y = y * e.symm z := by
      intro y
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hz (e y)
    have := h.noCentral3 (e.symm z) hz' (by rw [← map_pow, hz3, map_one])
    simpa using congrArg e this
  conj3 x y hx1 hx3 hy1 hy3 := by
    have hx1' : e.symm x ≠ 1 := fun h1 => hx1 (by simpa using congrArg e h1)
    have hy1' : e.symm y ≠ 1 := fun h1 => hy1 (by simpa using congrArg e h1)
    obtain ⟨g, hg⟩ := h.conj3 (e.symm x) (e.symm y) hx1' (by rw [← map_pow, hx3, map_one])
      hy1' (by rw [← map_pow, hy3, map_one])
    refine ⟨e g, ?_⟩
    have h1 := congrArg (Subgroup.map e.toMonoidHom) hg
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h1
    simpa using h1
  inner3 α hα := by
    obtain ⟨s, hs⟩ := h.inner3 ((MulAut.congr e.symm) α) (by rw [← map_pow, hα, map_one])
    refine ⟨e s, fun y => ?_⟩
    have h1 := hs (e.symm y)
    rw [Subgroup.mem_center_iff] at h1 ⊢
    intro t
    apply e.symm.injective
    have h2 := h1 (e.symm t)
    simpa [MulAut.congr_apply, mul_assoc] using h2

@[expose] noncomputable def conjQ {X : Type} [Group X] {d e : X}
    (he : e ∈ Subgroup.centralizer ({d} : Set X)) : MulAut ↥(qRes d) where
  toFun y := ⟨e * y * e⁻¹, qRes_normalized he y.2⟩
  invFun y := ⟨e⁻¹ * y * e, by
    have h1 : e⁻¹ ∈ Subgroup.centralizer ({d} : Set X) := Subgroup.inv_mem _ he
    simpa using qRes_normalized h1 y.2⟩
  left_inv y := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' y z := Subtype.ext (by simp [mul_assoc])

theorem conjQ_pow_apply {X : Type} [Group X] {d e : X} (he : e ∈ Subgroup.centralizer ({d} : Set X))
    (n : ℕ) (y : ↥(qRes d)) : ((conjQ he ^ n) y : X) = e ^ n * y * (e ^ n)⁻¹ := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih]
    simp [conjQ, mul_assoc, pow_succ]

theorem goodAt_of_goodGroup {X : Type} [Group X] [Finite X] {d : X}
    (h : GoodGroup ↥(qRes d)) : GoodAt d where
  rad N hNQ hNn hNs n hn y hy := by
    set N' : Subgroup ↥(qRes d) := N.subgroupOf (qRes d) with hN'def
    have hN' : N'.Normal := by
      refine ⟨fun m hm g => ?_⟩
      rw [hN'def, Subgroup.mem_subgroupOf] at hm ⊢
      simpa using hNn g g.2 m hm
    have hs' : Group.IsSolvable N' :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hNQ).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hNQ).injective
    have := h.rad N' hN' hs' ⟨n, hNQ hn⟩ (by rw [hN'def, Subgroup.mem_subgroupOf]; exact hn)
      ⟨y, hy⟩
    exact congrArg Subtype.val this
  elt3 := by
    obtain ⟨s, hs1, hs3⟩ := h.elt3
    refine ⟨s, s.2, fun h1 => hs1 (Subtype.ext h1), ?_⟩
    simpa using congrArg Subtype.val hs3
  noCentral3 z hz hzc hz3 := by
    have := h.noCentral3 ⟨z, hz⟩ (fun y => Subtype.ext (hzc y y.2))
      (Subtype.ext (by simpa using hz3))
    exact congrArg Subtype.val this
  conj3 x hx y hy hx1 hx3 hy1 hy3 := by
    obtain ⟨g, hg⟩ := h.conj3 ⟨x, hx⟩ ⟨y, hy⟩ (fun h1 => hx1 (congrArg Subtype.val h1))
      (Subtype.ext (by simpa using hx3)) (fun h1 => hy1 (congrArg Subtype.val h1))
      (Subtype.ext (by simpa using hy3))
    refine ⟨g, g.2, ?_⟩
    have h1 := congrArg (Subgroup.map (qRes d).subtype) hg
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h1
    simpa using h1
  inner3 e he3 he := by
    obtain ⟨s, hs⟩ := h.inner3 (conjQ he) (by
      ext y
      rw [conjQ_pow_apply, he3]
      simp)
    refine ⟨s, s.2, fun y hy w hw => ?_⟩
    have h1 := Subgroup.mem_center_iff.mp (hs ⟨y, hy⟩) ⟨w, hw⟩
    simpa [conjQ] using (congrArg Subtype.val h1).symm

end CFSG.AGLEmbeddingD2.Wilson.Census423Three
