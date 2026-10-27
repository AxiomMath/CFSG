module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E7TwoSevenLang
public import CFSG.RankThree.PartOne.KE.E7FourHI
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralSevenProved
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7TwoLowEven

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups


@[expose] def E7SplitTorusNonSimple : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 7 ∣ Nat.card K + 1 →
    ∃ a : Fin Tag.E7.rank → Kˣ, rootDiagUnit Tag.E7 a ∉ adjointGroup Tag.E7 K

@[expose] def E7TorusNormalizesFrame : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (a : Fin Tag.E7.rank → Kˣ) (y : adjointGroup Tag.E7 K),
    y ∈ e7FrameGroup K → ∃ z ∈ e7FrameGroup K,
      (z : ModGL Tag.E7 K) = rootDiagUnit Tag.E7 a * (y : ModGL Tag.E7 K) * (rootDiagUnit Tag.E7 a)⁻¹

section Index

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

theorem finite_fixed_E7 (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ] [IsAlgClosed L] (hf : 1 ≤ f) :
    {x : ModGL Tag.E7 L | entrywiseFrobGL Tag.E7 L ℓ f x = x}.Finite :=
  finite_setOf_entrywiseFrobGL_eq ℓ hf

end Index

section Coset

theorem mem_or_left_mul_mem_of_relIndex_two {G : Type*} [Group G] {H X : Subgroup G}
    (h2 : H.relIndex X = 2) {t : G} (htX : t ∈ X) (htH : t ∉ H) {y : G} (hyX : y ∈ X) :
    y ∈ H ∨ t * y ∈ H := by
  classical
  by_cases hy : y ∈ H
  · exact Or.inl hy
  right
  have h2' : (H.subgroupOf X).index = 2 := h2
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 h2'
  set Y : X := ⟨y, hyX⟩ with hY
  set T : X := ⟨t, htX⟩ with hT
  have hYH : Y ∉ H.subgroupOf X := fun h => hy (Subgroup.mem_subgroupOf.1 h)
  have hYiH : Y⁻¹ ∉ H.subgroupOf X := fun h => hy (by
    have := Subgroup.mem_subgroupOf.1 h
    simpa [hY] using H.inv_mem_iff.1 this)
  have hTH : T ∉ H.subgroupOf X := fun h => htH (Subgroup.mem_subgroupOf.1 h)
  have k1 : Y⁻¹ * a ∈ H.subgroupOf X := by
    have := ha Y⁻¹
    rcases this with h | h
    · exact h.1
    · exact absurd h.1 hYiH
  have k2 : T * a ∈ H.subgroupOf X := by
    have := ha T
    rcases this with h | h
    · exact h.1
    · exact absurd h.1 hTH
  have k3 : (Y⁻¹ * a) * (T * a)⁻¹ ∈ H.subgroupOf X := mul_mem k1 (inv_mem k2)
  have k4 : T * Y ∈ H.subgroupOf X := by
    have e : (Y⁻¹ * a) * (T * a)⁻¹ = (T * Y)⁻¹ := by group
    rw [e] at k3
    simpa using inv_mem k3
  exact Subgroup.mem_subgroupOf.1 k4

end Coset

section Fixed

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  [IsAlgClosed L]

variable (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ]

abbrev fixedSubE7 : Subgroup (ModGL Tag.E7 L) :=
  (Units.map (entrywiseHom (iterateFrobenius L ℓ f))).eqLocus (MonoidHom.id _)

theorem mem_fixedSubE7 {x : ModGL Tag.E7 L} :
    x ∈ fixedSubE7 (L := L) ℓ f ↔ entrywiseFrobGL Tag.E7 L ℓ f x = x :=
  Iff.rfl

theorem finite_fixedSubE7 (hf : 1 ≤ f) : Finite (fixedSubE7 (L := L) ℓ f) := by
  have h := finite_fixed_E7 (L := L) ℓ f hf
  exact h.to_subtype

end Fixed

section Dichotomy

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  [IsAlgClosed L]

theorem fixed_mem_or_mul_mem (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f)
    (hq : Nat.card K = ℓ ^ f) {t h : ModGL Tag.E7 L}
    (htG : t ∈ adjointGroup Tag.E7 L) (hhG : h ∈ adjointGroup Tag.E7 L)
    (htF : entrywiseFrobGL Tag.E7 L ℓ f t = t) (hhF : entrywiseFrobGL Tag.E7 L ℓ f h = h)
    (hts : t ∉ (adjointGroup Tag.E7 K).map (baseChangeGL (algebraMap K L))) :
    h ∈ (adjointGroup Tag.E7 K).map (baseChangeGL (algebraMap K L)) ∨
      t * h ∈ (adjointGroup Tag.E7 K).map (baseChangeGL (algebraMap K L)) := by
  classical
  set H := (adjointGroup Tag.E7 K).map (baseChangeGL (algebraMap K L)) with hH
  have hHle : H ≤ adjointGroup Tag.E7 L := by
    rintro _ ⟨x, hx, rfl⟩
    exact CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ hx
  have hHF : H ≤ fixedSubE7 (L := L) ℓ f := by
    rintro _ ⟨x, -, rfl⟩
    rw [mem_fixedSubE7]
    have hFr : ∀ c : L, iterateFrobenius L ℓ f c = c ^ Nat.card K := fun c => by
      rw [iterateFrobenius_def, hq]
    exact baseChangeGL_frobenius_fixed (iterateFrobenius L ℓ f) hFr x
  have htFix : t ∈ fixedSubE7 (L := L) ℓ f := (mem_fixedSubE7 ℓ f).2 htF
  have hhFix : h ∈ fixedSubE7 (L := L) ℓ f := (mem_fixedSubE7 ℓ f).2 hhF
  set X : Subgroup (ModGL Tag.E7 L) := H ⊔ Subgroup.closure {h, t} with hX
  have hXFix : X ≤ fixedSubE7 (L := L) ℓ f := by
    refine sup_le hHF (Subgroup.closure_le _ |>.2 ?_)
    rintro _ (rfl | rfl)
    · exact hhFix
    · exact htFix
  have hXle : X ≤ adjointGroup Tag.E7 L := by
    refine sup_le hHle (Subgroup.closure_le _ |>.2 ?_)
    rintro _ (rfl | rfl)
    · exact hhG
    · exact htG
  haveI : Finite (fixedSubE7 (L := L) ℓ f) := finite_fixedSubE7 ℓ f hf
  haveI : Finite X := Finite.of_injective
    (fun x : X => (⟨x.1, hXFix x.2⟩ : fixedSubE7 (L := L) ℓ f))
    (by intro x y hxy; have h := congrArg Subtype.val hxy; exact Subtype.ext h)
  have hFr : ∀ c : L, iterateFrobenius L ℓ f c = c ^ Nat.card K := fun c => by
    rw [iterateFrobenius_def, hq]
  have hXF : ∀ x ∈ X, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x :=
    fun x hx => (mem_fixedSubE7 ℓ f).1 (hXFix hx)
  have hdiv := (finite_fixed_subgroup_rational (d := 2) (τ := Tag.E7) (K := K) (L := L)
    (Or.inr (Or.inl ⟨rfl, rfl⟩)) (iterateFrobenius L ℓ f) hFr X hXle hXF).1
  have htX : t ∈ X := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hhX : h ∈ X := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hrel : H.relIndex X = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdiv with h1 | h1
    · exfalso
      have := (Subgroup.relIndex_eq_one).1 h1
      exact hts (this htX)
    · exact h1
  rcases mem_or_left_mul_mem_of_relIndex_two hrel htX hts hhX with h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1

end Dichotomy

section Seven

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  [IsAlgClosed L]

theorem seven_mem_of_fixed (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f)
    (hq : Nat.card K = ℓ ^ f) {x : ModGL Tag.E7 L} (hx : x ∈ adjointGroup Tag.E7 L)
    (hxF : entrywiseFrobGL Tag.E7 L ℓ f x = x) (hx7 : x ^ 7 = 1) :
    x ∈ (adjointGroup Tag.E7 K).map (baseChangeGL (algebraMap K L)) := by
  classical
  have hxFix : x ∈ fixedSubE7 (L := L) ℓ f := (mem_fixedSubE7 ℓ f).2 hxF
  set X : Subgroup (ModGL Tag.E7 L) := Subgroup.zpowers x with hXdef
  have hXFix' : X ≤ fixedSubE7 (L := L) ℓ f := (Subgroup.zpowers_le).2 hxFix
  have hXle : X ≤ adjointGroup Tag.E7 L := (Subgroup.zpowers_le).2 hx
  haveI : Finite (fixedSubE7 (L := L) ℓ f) := finite_fixedSubE7 ℓ f hf
  haveI : Finite X := Finite.of_injective
    (fun y : X => (⟨y.1, hXFix' y.2⟩ : fixedSubE7 (L := L) ℓ f))
    (by intro y z hyz; have h := congrArg Subtype.val hyz; exact Subtype.ext h)
  have hFr : ∀ c : L, iterateFrobenius L ℓ f c = c ^ Nat.card K := fun c => by
    rw [iterateFrobenius_def, hq]
  have hXF : ∀ y ∈ X, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) y = y :=
    fun y hy => (mem_fixedSubE7 ℓ f).1 (hXFix' hy)
  have hPgrp : IsPGroup 7 X := by
    haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    rw [IsPGroup.iff_card]
    have hd : orderOf x ∣ 7 := orderOf_dvd_of_pow_eq_one hx7
    rw [hXdef, Nat.card_zpowers]
    rcases (Nat.dvd_prime Nat.prime_seven).1 hd with h | h
    · exact ⟨0, by rw [h]; simp⟩
    · exact ⟨1, by rw [h]; norm_num⟩
  have hP := (finite_fixed_subgroup_rational (d := 2) (τ := Tag.E7) (K := K) (L := L)
    (Or.inr (Or.inl ⟨rfl, rfl⟩)) (iterateFrobenius L ℓ f) hFr X hXle hXF).2 7
    Nat.prime_seven (by norm_num) X le_rfl hPgrp
  exact hP (Subgroup.mem_zpowers x)

end Seven

section Descent

theorem frame_descent {K : Type} [Field K] [Finite K] (ℓ f : ℕ) [Fact ℓ.Prime]
    [CharP (AlgebraicClosure K) ℓ] (hf : 1 ≤ f) (hq : Nat.card K = ℓ ^ f)
    (hpq : 7 ∣ Nat.card K + 1) (hT : E7SplitTorusNonSimple) (hN : E7TorusNormalizesFrame)
    (w0 : WeylGroup Tag.E7) (hw0 : ∀ u : Fin Tag.E7.rank → ℤ, w0 • u = -u)
    (gf : ModGL Tag.E7 (AlgebraicClosure K)) (hgf : gf ∈ adjointGroup Tag.E7 (AlgebraicClosure K))
    (hgfF : Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) ℓ f)) gf =
      gf * canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) w0)
    (hfr : ∀ y : adjointGroup Tag.E7 K, y ^ 7 = 1 →
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL Tag.E7 K) ∈
        (twistedTorusOf (canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) w0)
          (Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) ℓ f)))).map
            (MulAut.conj gf).toMonoidHom → y ∈ e7FrameGroup K)
    (g : ModGL Tag.E7 (AlgebraicClosure K)) (hg : g ∈ adjointGroup Tag.E7 (AlgebraicClosure K))
    (hgF : Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) ℓ f)) g =
      g * canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) w0)
    (A : Subgroup (adjointGroup Tag.E7 K)) (hA7 : ∀ x ∈ A, x ^ 7 = 1)
    (hAT : ∀ x ∈ A, baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.E7 K) ∈
        (twistedTorusOf (canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) w0)
          (Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) ℓ f)))).map
            (MulAut.conj g).toMonoidHom) :
    ∃ e : adjointGroup Tag.E7 K, ∀ x ∈ A, e * x * e⁻¹ ∈ e7FrameGroup K := by
  classical
  have hFr : ∀ c : AlgebraicClosure K, iterateFrobenius (AlgebraicClosure K) ℓ f c = c ^ Nat.card K :=
    fun c => by rw [iterateFrobenius_def, hq]
  set L := AlgebraicClosure K with hLdef
  set bc := baseChangeGL (algebraMap K L) with hbc
  have hbcinj : Function.Injective bc := baseChangeGL_injective _
  set Gs : Subgroup (ModGL Tag.E7 L) := (adjointGroup Tag.E7 K).map bc with hGs
  have hbcF : ∀ x : ModGL Tag.E7 K,
      Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (bc x) = bc x := fun x =>
    baseChangeGL_frobenius_fixed (τ := Tag.E7) (iterateFrobenius L ℓ f) hFr x
  set h : ModGL Tag.E7 L := gf * g⁻¹ with hh
  have hhG : h ∈ adjointGroup Tag.E7 L := mul_mem hgf (inv_mem hg)
  have hhF : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) h = h := by
    rw [hh, map_mul, map_inv, hgfF, hgF]
    group
  have hkey : ∀ x ∈ A, ∃ y ∈ e7FrameGroup K,
      bc (y : ModGL Tag.E7 K) = h * bc (x : ModGL Tag.E7 K) * h⁻¹ := by
    intro x hx
    obtain ⟨τ, hτ, hτg⟩ := Subgroup.mem_map.1 (hAT x hx)
    have hbx : bc (x : ModGL Tag.E7 K) = g * τ * g⁻¹ := hτg.symm
    have hbG : bc (x : ModGL Tag.E7 K) ∈ adjointGroup Tag.E7 L :=
      CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ x.2
    have hhb : h * bc (x : ModGL Tag.E7 K) * h⁻¹ ∈ adjointGroup Tag.E7 L :=
      mul_mem (mul_mem hhG hbG) (inv_mem hhG)
    have hhbF : Units.map (entrywiseHom (iterateFrobenius L ℓ f))
        (h * bc (x : ModGL Tag.E7 K) * h⁻¹) = h * bc (x : ModGL Tag.E7 K) * h⁻¹ := by
      rw [map_mul, map_mul, map_inv, hhF, hbcF]
    have h7 : (bc (x : ModGL Tag.E7 K)) ^ 7 = 1 := by
      rw [← map_pow, ← Subgroup.coe_pow, hA7 x hx, Subgroup.coe_one, map_one]
    have hhb7 : (h * bc (x : ModGL Tag.E7 K) * h⁻¹) ^ 7 = 1 := by
      rw [conj_pow, h7, mul_one, mul_inv_cancel]
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.1
      (seven_mem_of_fixed ℓ f hf hq hhb hhbF hhb7)
    let ys : adjointGroup Tag.E7 K := ⟨y, hy⟩
    have hys : (ys : ModGL Tag.E7 K) = y := rfl
    have hy7 : ys ^ 7 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, hys]
      apply hbcinj
      rw [map_pow, hyeq, hhb7, map_one]
    have hmemT : bc (ys : ModGL Tag.E7 K) ∈
        (twistedTorusOf (canonicalRep (coxeterSystem Tag.E7) L w0)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))).map (MulAut.conj gf).toMonoidHom := by
      rw [hys, hyeq]
      refine Subgroup.mem_map.2 ⟨τ, hτ, ?_⟩
      show gf * τ * gf⁻¹ = h * bc (x : ModGL Tag.E7 K) * h⁻¹
      rw [hbx, hh]
      group
    exact ⟨ys, hfr ys hy7 hmemT, by rw [hys]; exact hyeq⟩
  by_cases hG : h ∈ Gs
  · obtain ⟨e0, he0mem, he0⟩ := Subgroup.mem_map.1 hG
    refine ⟨⟨e0, he0mem⟩, fun x hx => ?_⟩
    obtain ⟨y, hy, hyeq⟩ := hkey x hx
    have hconj : (⟨e0, he0mem⟩ : adjointGroup Tag.E7 K) * x * (⟨e0, he0mem⟩)⁻¹ = y := by
      apply Subtype.ext
      apply hbcinj
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      show bc (e0 * (x : ModGL Tag.E7 K) * e0⁻¹) = bc (y : ModGL Tag.E7 K)
      rw [map_mul, map_mul, map_inv, he0, hyeq]
    rw [hconj]
    exact hy
  · obtain ⟨a, ha⟩ := hT K hpq
    have htG : bc (rootDiagUnit Tag.E7 a) ∈ adjointGroup Tag.E7 L := by
      rw [hbc, CFSG.LieType.Chevalley.baseChangeGL_rootDiagUnit]
      exact torusGroup_le_adjointGroup' (rootDiagUnit_mem_torusGroup _)
    have htF : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (bc (rootDiagUnit Tag.E7 a)) =
        bc (rootDiagUnit Tag.E7 a) := hbcF _
    have hts : bc (rootDiagUnit Tag.E7 a) ∉ Gs := by
      intro hmem
      obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.1 hmem
      apply ha
      have hz' : z = rootDiagUnit Tag.E7 a := hbcinj hzeq
      rw [← hz']
      exact hz
    have hdich := fixed_mem_or_mul_mem ℓ f hf hq htG hhG htF hhF hts
    have hth : bc (rootDiagUnit Tag.E7 a) * h ∈ Gs := hdich.resolve_left hG
    obtain ⟨e0, he0mem, he0⟩ := Subgroup.mem_map.1 hth
    refine ⟨⟨e0, he0mem⟩, fun x hx => ?_⟩
    obtain ⟨y, hy, hyeq⟩ := hkey x hx
    obtain ⟨z, hz, hzeq⟩ := hN K a y hy
    have hconj : (⟨e0, he0mem⟩ : adjointGroup Tag.E7 K) * x * (⟨e0, he0mem⟩)⁻¹ = z := by
      apply Subtype.ext
      apply hbcinj
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      show bc (e0 * (x : ModGL Tag.E7 K) * e0⁻¹) = bc (z : ModGL Tag.E7 K)
      rw [hzeq, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, he0, hyeq]
      group
    rw [hconj]
    exact hz

end Descent


theorem e7TwoSylowSeven_of_frame_inputs (hS : E7SevenPlaneWeyl) (hF : E7SevenFrameDatum)
    (hT : E7SplitTorusNonSimple) (hN : E7TorusNormalizesFrame) : E7TwoSylowSeven := by
  obtain ⟨w0, hw0, hframe⟩ := hF
  intro K _ _ hpq E₀ hE₀p hE₀c _
  have hpK : ¬ 7 ∣ Nat.card K := fun h => by
    have h1 : 7 ∣ 1 := (Nat.dvd_add_right h).1 hpq
    norm_num at h1
  obtain ⟨w, Fr, hFr, g0, hg0C, hg0, c, hc⟩ :=
    (langToralPlane_of_bar Nat.prime_seven planesToralBar_E7_seven) K hpK E₀ hE₀p hE₀c
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  have hfr : Fr = iterateFrobenius (AlgebraicClosure K) (ringChar K) (f : ℕ) :=
    RingHom.ext fun x => by rw [hFr, iterateFrobenius_def, hq]
  subst hfr
  have hq7 : 7 ∣ ringChar K ^ (f : ℕ) + 1 := hq ▸ hpq
  have hf1 : 1 ≤ (f : ℕ) := f.pos
  obtain ⟨x1, hx1, x2, hx2, hgenE⟩ := exists_two_gen_of_card_sq Nat.prime_seven E₀ hE₀c hE₀p
  let ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  let Φ : ModGL Tag.E7 (AlgebraicClosure K) →* ModGL Tag.E7 (AlgebraicClosure K) :=
    entrywiseFrobGL Tag.E7 (AlgebraicClosure K) (ringChar K) (f : ℕ)
  let bb : adjointGroup Tag.E7 K → ModGL Tag.E7 (AlgebraicClosure K) := fun x =>
    baseChangeGL ι ((c * x * c⁻¹ : adjointGroup Tag.E7 K) : ModGL Tag.E7 K)
  let ψ : adjointGroup Tag.E7 K →* ModGL Tag.E7 (AlgebraicClosure K) :=
    (MulAut.conj g0⁻¹).toMonoidHom.comp ((baseChangeGL ι).comp
      ((adjointGroup Tag.E7 K).subtype.comp (MulAut.conj c).toMonoidHom))
  have hψ : ∀ x, ψ x = g0⁻¹ * bb x * g0 := fun x => by
    show g0⁻¹ * bb x * g0⁻¹⁻¹ = g0⁻¹ * bb x * g0
    rw [inv_inv]
  let Tw : Subgroup (ModGL Tag.E7 (AlgebraicClosure K)) :=
    twistedTorusOf (canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) w) Φ
  have hψT : ∀ x ∈ E₀, ψ x ∈ Tw := by
    intro x hx
    obtain ⟨t, ht, htb⟩ := Subgroup.mem_map.1 (hc x hx)
    have htb' : g0 * t * g0⁻¹ = bb x := htb
    have : ψ x = t := by
      rw [hψ, ← htb']
      group
    rw [this]
    exact ht
  have h7 : ∀ x ∈ E₀, ψ x ^ 7 = 1 := fun x hx => by
    rw [← map_pow, hE₀p x hx, map_one]
  have hSS : E₀.map ψ = Subgroup.closure {ψ x1, ψ x2} := by
    conv_lhs => rw [hgenE]
    rw [MonoidHom.map_closure, Set.image_pair]
  have htor1 : ψ x1 ∈ torusGroup Tag.E7 (AlgebraicClosure K) :=
    (mem_twistedTorusOf.1 (hψT x1 hx1)).1
  have htor2 : ψ x2 ∈ torusGroup Tag.E7 (AlgebraicClosure K) :=
    (mem_twistedTorusOf.1 (hψT x2 hx2)).1
  obtain ⟨a1, ha1⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup htor1
  obtain ⟨a2, ha2⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup htor2
  have hfix1 := (mem_twistedTorusOf.1 (hψT x1 hx1)).2
  have hfix2 := (mem_twistedTorusOf.1 (hψT x2 hx2)).2
  rw [ha1] at hfix1
  rw [ha2] at hfix2
  let a : Fin 2 → Fin Tag.E7.rank → (AlgebraicClosure K)ˣ := ![a1, a2]
  have ha_exp : ∀ (s : Fin 2) (i : Fin Tag.E7.rank), a s i ^ 7 = 1 := by
    intro s
    fin_cases s
    · exact exp_seven_of_rootDiagUnit a1 (by rw [← ha1]; exact h7 x1 hx1)
    · exact exp_seven_of_rootDiagUnit a2 (by rw [← ha2]; exact h7 x2 hx2)
  have hyfix : ∀ (s : Fin 2) (v : Fin Tag.E7.rank → ℤ),
      rootChar (a s) ((w0⁻¹ * w) • v) = rootChar (a s) v := by
    intro s v
    fin_cases s
    · exact rootChar_y_fix (ringChar K) (f : ℕ) hw0 (fun i => ha_exp 0 i) hq7 hfix1 v
    · exact rootChar_y_fix (ringChar K) (f : ℕ) hw0 (fun i => ha_exp 1 i) hq7 hfix2 v
  have hy_mem : canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) (w0⁻¹ * w) ∈
      familyGroup (τ := Tag.E7) (K := AlgebraicClosure K) a :=
    canonicalRep_mem_familyGroup_of_closure a (hS (AlgebraicClosure K) a ha_exp (w0⁻¹ * w) hyfix)
  have hw0img := image_neg_familyKernel (L := AlgebraicClosure K) a hw0
  have hfix0 : entrywiseFrobGL Tag.E7 (AlgebraicClosure K) (ringChar K) (f : ℕ) g0 =
      g0 * canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) w := hg0
  obtain ⟨z, hz, hzF⟩ :=
    exists_datum_change (ringChar K) (f : ℕ) hf1 a w w0 g0 hfix0 hw0img hy_mem
  have hzC := mem_familyCentralizer.1
    (familyGroup_le_familyCentralizer (K := AlgebraicClosure K) a hz)
  have hzG : z ∈ adjointGroup Tag.E7 (AlgebraicClosure K) := hzC.1
  have hz1 : z * ψ x1 = ψ x1 * z := comm_of_conj_eq (by
    rw [ha1]
    exact hzC.2 0)
  have hz2 : z * ψ x2 = ψ x2 * z := comm_of_conj_eq (by
    rw [ha2]
    exact hzC.2 1)
  have hzS : ∀ t ∈ E₀.map ψ, z * t = t * z := by
    intro t ht
    have hle : Subgroup.closure ({ψ x1, ψ x2} : Set (ModGL Tag.E7 (AlgebraicClosure K))) ≤
        Subgroup.centralizer ({z} : Set (ModGL Tag.E7 (AlgebraicClosure K))) := by
      refine (Subgroup.closure_le _).2 ?_
      rintro t' (rfl | rfl)
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact hz1
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact hz2
    rw [hSS] at ht
    have := hle ht
    rw [Subgroup.mem_centralizer_iff] at this
    exact this z (Set.mem_singleton z)
  let Tw0 : Subgroup (ModGL Tag.E7 (AlgebraicClosure K)) :=
    twistedTorusOf (canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) w0) Φ
  have hnewT : ∀ x ∈ E₀, (g0 * z)⁻¹ * bb x * (g0 * z) ∈ Tw0 := by
    intro x hx
    have hcomm := hzS (ψ x) (Subgroup.mem_map_of_mem ψ hx)
    have hb : bb x = g0 * ψ x * g0⁻¹ := by
      rw [hψ]
      group
    have key : (g0 * z)⁻¹ * bb x * (g0 * z) = ψ x := by
      rw [hb]
      calc (g0 * z)⁻¹ * (g0 * ψ x * g0⁻¹) * (g0 * z) = z⁻¹ * ψ x * z := by group
        _ = z⁻¹ * (ψ x * z) := by group
        _ = z⁻¹ * (z * ψ x) := by rw [hcomm]
        _ = ψ x := by group
    rw [key]
    have hT := mem_twistedTorusOf.1 (hψT x hx)
    obtain ⟨b, hb'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT.1
    have hb7 : ∀ i, b i ^ 7 = 1 :=
      exp_seven_of_rootDiagUnit b (by rw [← hb']; exact h7 x hx)
    rw [mem_twistedTorusOf]
    refine ⟨hT.1, ?_⟩
    rw [hb']
    exact twisted_w0_fix (ringChar K) (f : ℕ) hw0 hq7 hb7
  have hg'mem : g0 * z ∈ adjointGroup Tag.E7 (AlgebraicClosure K) := mul_mem hg0C hzG
  have hg'eq : Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) (ringChar K) (f : ℕ)))
      (g0 * z) = g0 * z * canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) w0 := hzF
  obtain ⟨gf, hgfmem, hgfeq, hgfframe⟩ := hframe K hpq _ hFr
  let A : Subgroup (adjointGroup Tag.E7 K) := E₀.map (MulAut.conj c).toMonoidHom
  have hA7 : ∀ x ∈ A, x ^ 7 = 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    show (c * y * c⁻¹) ^ 7 = 1
    rw [conj_pow, hE₀p y hy, mul_one, mul_inv_cancel]
  have hAcard : Nat.card A = 7 ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hE₀c]
  have hAT : ∀ x ∈ A, baseChangeGL ι (x : ModGL Tag.E7 K) ∈
      Tw0.map (MulAut.conj (g0 * z)).toMonoidHom := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_map.2 ⟨(g0 * z)⁻¹ * bb y * (g0 * z), hnewT y hy, ?_⟩
    show (g0 * z) * ((g0 * z)⁻¹ * bb y * (g0 * z)) * (g0 * z)⁻¹ = bb y
    group
  obtain ⟨e, he⟩ := frame_descent (ringChar K) (f : ℕ) hf1 hq hpq hT hN w0 hw0 gf hgfmem hgfeq
    hgfframe (g0 * z) hg'mem hg'eq A hA7 hAT
  refine ⟨e * c, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  have hmemA : c * v * c⁻¹ ∈ A := Subgroup.mem_map.2 ⟨v, hv, rfl⟩
  have hconj : (MulAut.conj (e * c)).toMonoidHom v = e * (c * v * c⁻¹) * e⁻¹ := by
    show (e * c) * v * (e * c)⁻¹ = e * (c * v * c⁻¹) * e⁻¹
    group
  rw [hconj]
  exact he _ hmemA


theorem seitzExcHighE7TwoSeven_of_frame_inputs (hS : E7SevenPlaneWeyl) (hF : E7SevenFrameDatum)
    (hT : E7SplitTorusNonSimple) (hN : E7TorusNormalizesFrame) : SeitzExcHighE7TwoSeven := by
  refine seitzExcHighE7Two_of_native_for (R := fun p => p = 7) ?_
  intro K _ _ p hpF hp5 hR hpq E₀ hE₀p hE₀c hN'
  subst hR
  exact closure_centralizers_eq_top_of_conj_frame
    (fun E hE hEp hEc => e7A1D6_le_closure_centralizers_two hpF.out (by norm_num) hpq E hE hEp hEc)
    E₀ hE₀p hE₀c (e7TwoSylowSeven_of_frame_inputs hS hF hT hN K hpq E₀ hE₀p hE₀c hN')


end CFSG.LieType.SeitzGeneration.ExcHigh
