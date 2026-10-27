module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.Lift
public import CFSG.GroupTheory.QuasisimpleCenterDivisibility

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81Orth

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.Open CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x y : V ≃ₗ[K] V}

section Spaces

theorem exists_mem_othersSpace_sub_eq (hx : OddOrderIsometry Q p x) {r : V}
    (hr : r ∈ othersSpace x.toLinearMap (X - 1)) :
    ∃ s ∈ othersSpace x.toLinearMap (X - 1), x s - s = r := by
  obtain ⟨hcompl, -⟩ := hx.fixed_others
  set R := othersSpace x.toLinearMap (X - 1)
  have hinv : ∀ s ∈ R, x s - s ∈ R := fun s hs => by
    refine R.sub_mem ?_ hs
    exact mem_othersSpace_of_apply (Subgroup.mem_centralizer_singleton_iff.mpr rfl) hs
  let f : R →ₗ[K] R := ((x.toLinearMap - LinearMap.id).restrict hinv)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro s hs
    have h0 : x s - s = 0 := congrArg Subtype.val hs
    have hsW : (s : V) ∈ fixedSpace x := by rw [mem_fixedSpace]; exact sub_eq_zero.mp h0
    exact Subtype.ext ((Submodule.disjoint_def.mp hcompl.disjoint) _ hsW s.2)
  obtain ⟨s, hs⟩ := (LinearMap.injective_iff_surjective.mp hf) ⟨r, hr⟩
  exact ⟨s, s.2, congrArg Subtype.val hs⟩

theorem sub_mem_othersSpace (hx : OddOrderIsometry Q p x) (v : V) :
    x v - v ∈ othersSpace x.toLinearMap (X - 1) := by
  obtain ⟨hcompl, -⟩ := hx.fixed_others
  obtain ⟨u, hu, t, ht, rfl⟩ := exists_add_of_isCompl hcompl v
  have hxu : x u = u := mem_fixedSpace.mp hu
  have hxt : x t ∈ othersSpace x.toLinearMap (X - 1) :=
    mem_othersSpace_of_apply (Subgroup.mem_centralizer_singleton_iff.mpr rfl) ht
  rw [map_add, hxu, add_sub_add_left_eq_sub]
  exact Submodule.sub_mem _ hxt ht

end Spaces

section Product

variable (hx : OddOrderIsometry Q p x) (hy : OddOrderIsometry Q p y) (hxy : x * y = y * x)
  (hyR : ∀ v, y (x v - v) = x v - v)
include hx hy hxy hyR

theorem oddOrderIsometry_mul : OddOrderIsometry Q p (x * y) where
  mem := Subgroup.mul_mem _ hx.mem hy.mem
  pow_eq_one := by rw [(Commute.mul_pow hxy p), hx.pow_eq_one, hy.pow_eq_one, one_mul]
  cast_ne_zero := hx.cast_ne_zero
  regular := hx.regular

omit hy in
theorem apply_eq_of_mem_othersSpace {r : V} (hr : r ∈ othersSpace x.toLinearMap (X - 1)) :
    y r = r := by
  obtain ⟨s, -, rfl⟩ := exists_mem_othersSpace_sub_eq hx hr
  exact hyR s

theorem othersSpace_le_othersSpace_mul :
    othersSpace x.toLinearMap (X - 1) ≤ othersSpace (x * y).toLinearMap (X - 1) := by
  intro r hr
  obtain ⟨s, hs, rfl⟩ := exists_mem_othersSpace_sub_eq hx hr
  have hys : y s = s := apply_eq_of_mem_othersSpace hx hxy hyR hs
  have := sub_mem_othersSpace (oddOrderIsometry_mul hx hy hxy hyR) s
  rwa [LinearEquiv.mul_apply, hys] at this

theorem fixedSpace_mul_le : fixedSpace (x * y) ≤ fixedSpace x := by
  intro v hv
  obtain ⟨hcompl, -⟩ := hx.fixed_others
  obtain ⟨u, hu, r, hr, rfl⟩ := exists_add_of_isCompl hcompl v
  have hyu : y u ∈ fixedSpace x :=
    mem_fixedSpace_of_apply (Subgroup.mem_centralizer_singleton_iff.mpr hxy.symm) hu
  have hyr : y r = r := apply_eq_of_mem_othersSpace hx hxy hyR hr
  have hxr : x r ∈ othersSpace x.toLinearMap (X - 1) :=
    mem_othersSpace_of_apply (Subgroup.mem_centralizer_singleton_iff.mpr rfl) hr
  have hw : (x * y) (u + r) = y u + x r := by
    rw [LinearEquiv.mul_apply, map_add, hyr, map_add, mem_fixedSpace.mp hyu]
  rw [mem_fixedSpace, hw] at hv
  have h1 : y u - u = r - x r := by rw [sub_eq_sub_iff_add_eq_add, hv, add_comm]
  have h0 : r - x r = 0 :=
    (Submodule.disjoint_def.mp hcompl.disjoint) _ (h1 ▸ (fixedSpace x).sub_mem hyu hu)
      (Submodule.sub_mem _ hr hxr)
  have hrW : r ∈ fixedSpace x := by rw [mem_fixedSpace]; exact (sub_eq_zero.mp h0).symm
  have hr0 : r = 0 := (Submodule.disjoint_def.mp hcompl.disjoint) r hrW hr
  rw [hr0, add_zero]
  exact hu

theorem supportedBlock_mul_le :
    supportedBlock Q (x * y) (X - 1) ≤ supportedBlock Q x (X - 1) := by
  intro s hs
  obtain ⟨⟨hsO, hsw⟩, hsR⟩ := mem_supportedBlock.mp hs
  have hsw' : s * (x * y) = (x * y) * s := Subgroup.mem_centralizer_singleton_iff.mp hsw
  have hw := oddOrderIsometry_mul hx hy hxy hyR
  refine mem_supportedBlock.mpr ⟨⟨hsO, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩,
    fun r hr => hsR r (othersSpace_le_othersSpace_mul hx hy hxy hyR hr)⟩
  obtain ⟨hcompl, -⟩ := hw.fixed_others
  apply LinearEquiv.ext
  intro v
  obtain ⟨u, hu, t, ht, rfl⟩ := exists_add_of_isCompl hcompl v
  have hxw : x * (x * y) = (x * y) * x := ((Commute.refl x).mul_right hxy).eq
  have hxt : x t ∈ othersSpace (x * y).toLinearMap (X - 1) :=
    mem_othersSpace_of_apply (Subgroup.mem_centralizer_singleton_iff.mpr hxw) ht
  have hxu : x u = u := mem_fixedSpace.mp (fixedSpace_mul_le hx hy hxy hyR hu)
  have hsu : s u ∈ fixedSpace (x * y) :=
    mem_fixedSpace_of_apply (Subgroup.mem_centralizer_singleton_iff.mpr hsw') hu
  have hxsu : x (s u) = s u := mem_fixedSpace.mp (fixedSpace_mul_le hx hy hxy hyR hsu)
  simp only [LinearEquiv.mul_apply, map_add]
  rw [hxu, hsR _ hxt, hsR t ht, hxsu]

theorem supportedFixedDerived_mul_le :
    supportedFixedDerived Q (x * y) ≤ supportedFixedDerived Q x := by
  rw [(oddOrderIsometry_mul hx hy hxy hyR).supportedFixedDerived_eq, hx.supportedFixedDerived_eq]
  exact Subgroup.commutator_mono (supportedBlock_mul_le hx hy hxy hyR)
    (supportedBlock_mul_le hx hy hxy hyR)

theorem commute_of_mem_supportedBlock_mul {s : V ≃ₗ[K] V}
    (hs : s ∈ supportedBlock Q (x * y) (X - 1)) : s * y = y * s := by
  have hsx : s * x = x * s := Subgroup.mem_centralizer_singleton_iff.mp
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (supportedBlock_mul_le hx hy hxy hyR hs)).1).2
  have hsw : s * (x * y) = (x * y) * s := Subgroup.mem_centralizer_singleton_iff.mp
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hs).1).2
  have : x * (s * y) = x * (y * s) := by
    calc x * (s * y) = (x * s) * y := by rw [mul_assoc]
      _ = (s * x) * y := by rw [hsx]
      _ = s * (x * y) := by rw [mul_assoc]
      _ = (x * y) * s := hsw
      _ = x * (y * s) := by rw [mul_assoc]
  exact mul_left_cancel this

end Product

section Image

variable {x y : ↥(orthDerived Q)} (hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V))
  (hy : OddOrderIsometry Q p (y : V ≃ₗ[K] V))
  (hxy : (x : V ≃ₗ[K] V) * y = y * x)
  (hyR : ∀ v, (y : V ≃ₗ[K] V) ((x : V ≃ₗ[K] V) v - v) = (x : V ≃ₗ[K] V) v - v)
include hx hy hxy hyR

theorem fixedComponentImage_mul_le :
    fixedComponentImage Q ((x : V ≃ₗ[K] V) * y) ≤
      fixedComponentImage Q (x : V ≃ₗ[K] V) ⊓ Subgroup.centralizer {projT Q y} := by
  refine le_inf (Subgroup.map_mono fun z hz => ?_) ?_
  · exact Subgroup.mem_subgroupOf.mpr
      (supportedFixedDerived_mul_le hx hy hxy hyR (Subgroup.mem_subgroupOf.mp hz))
  · rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show projT Q z * projT Q y = projT Q y * projT Q z
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (commute_of_mem_supportedBlock_mul hx hy hxy hyR
      (supportedFixedDerived_le_supportedBlock (Subgroup.mem_subgroupOf.mp hz)))

theorem le_centralizerImage_mul [Finite K] (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hp : p.Prime) (hp2 : p ≠ 2)
    (hy1 : y ≠ 1) :
    fixedComponentImage Q (x : V ≃ₗ[K] V) ⊓ Subgroup.centralizer {projT Q y} ≤
      centralizerImage Q ((x : V ≃ₗ[K] V) * y) := by
  intro t ⟨htJ, htC⟩
  have hyp : y ^ p = 1 := Subtype.ext hy.pow_eq_one
  rw [centralizer_projT_eq hQ hT hp hp2 hy1 hyp] at htC
  obtain ⟨s₁, hs₁, rfl⟩ := htC
  obtain ⟨s₂, hs₂, h12⟩ := (fixedComponentImage_le_centralizerImage (Q := Q) (x := (x : V ≃ₗ[K] V)))
    htJ
  have hs₁y := Subgroup.mem_subgroupOf.mp hs₁
  have hs₂x := Subgroup.mem_subgroupOf.mp hs₂
  have hc : projT Q (s₂⁻¹ * s₁) = 1 := by
    rw [map_mul, map_inv, inv_mul_eq_one]
    exact h12
  have hcZ : ((s₂⁻¹ * s₁ : ↥(orthDerived Q)) : V ≃ₗ[K] V) ∈ scalars K V :=
    Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hc)
  have hs₁eq : (s₁ : V ≃ₗ[K] V) = s₂ * ((s₂⁻¹ * s₁ : ↥(orthDerived Q)) : V ≃ₗ[K] V) := by
    simp
  have hs₁x : (s₁ : V ≃ₗ[K] V) * x = x * s₁ := by
    rw [hs₁eq, mul_assoc, ← commute_of_mem_scalars hcZ, ← mul_assoc,
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hs₂x).2, mul_assoc]
  have hs₁y' : (s₁ : V ≃ₗ[K] V) * y = y * s₁ :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hs₁y).2
  refine ⟨s₁, Subgroup.mem_subgroupOf.mpr ⟨(Subgroup.mem_inf.mp hs₁y).1,
    Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, rfl⟩
  rw [← mul_assoc, hs₁x, mul_assoc, hs₁y', ← mul_assoc]

theorem normal_fixedComponentImage_mul [Finite K] (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hp : p.Prime) (hp2 : p ≠ 2)
    (hy1 : y ≠ 1) :
    ((fixedComponentImage Q ((x : V ≃ₗ[K] V) * y)).subgroupOf
      (fixedComponentImage Q (x : V ≃ₗ[K] V) ⊓ Subgroup.centralizer {projT Q y})).Normal := by
  have hw := oddOrderIsometry_mul hx hy hxy hyR
  have hN := hw.normal_fixedComponentImage
  have hLM := fixedComponentImage_mul_le hx hy hxy hyR
  have hMC := le_centralizerImage_mul hx hy hxy hyR hQ hT hp hp2 hy1
  rw [Subgroup.normal_subgroupOf_iff hLM]
  rw [Subgroup.normal_subgroupOf_iff fixedComponentImage_le_centralizerImage] at hN
  intro j n hj hn
  exact hN j n hj (hMC hn)

end Image

section Low

variable [Finite K] {w : V ≃ₗ[K] V}

theorem dvd_card_fixedComponentImage (hw : OddOrderIsometry Q p w) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : ringChar K ≠ 2) (hR : othersSpace w.toLinearMap (X - 1) ≠ ⊥) {t : V ≃ₗ[K] V}
    (ht : t ∈ isometryCentralizer Q w) (htp : t ^ p = 1) {u : V} (hu : u ∈ fixedSpace w)
    (htu : t u ≠ u) : p ∣ Nat.card ↥(fixedComponentImage Q w) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have htw : t ∈ Subgroup.centralizer ({w} : Set (V ≃ₗ[K] V)) := (Subgroup.mem_inf.mp ht).2
  have htw' : t.symm ∈ Subgroup.centralizer ({w} : Set (V ≃ₗ[K] V)) :=
    Subgroup.inv_mem _ htw
  set φ : fixedSpace w ≃ₗ[K] fixedSpace w := restrictEquiv (fixedSpace w) t
    (fun _ hv => mem_fixedSpace_of_apply htw hv) (fun _ hv => mem_fixedSpace_of_apply htw' hv)
  have hφO : φ ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace w).subtype) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    show Q (t v) = Q v
    exact (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (Subgroup.mem_inf.mp ht).1) v
  obtain ⟨g, hg⟩ := restrictFixed_surjective hw φ hφO
  have hgp : g ^ p = 1 := by
    apply restrictFixed_injective hw
    rw [map_pow, map_one, hg]
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    have : ∀ n : ℕ, ((φ ^ n) v : V) = (t ^ n) v := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ', pow_succ', LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← ih]
        rfl
    rw [this p, htp]
    rfl
  have hgS : (g : V ≃ₗ[K] V) ∈ supportedFixedDerived Q w := by
    refine mem_supportedFixedDerived.mpr ⟨g.2, ?_⟩
    have hodd : Odd (orderOf (restrictFixed Q w g)) := by
      have hd : orderOf (restrictFixed Q w g) ∣ p := orderOf_dvd_of_pow_eq_one (by
        rw [← map_pow, hgp, map_one])
      exact (hp.eq_two_or_odd'.resolve_left hp2).of_dvd_nat hd
    exact CFSG.ComponentClassification.HarrisLit.L33.OC.mem_omega_of_odd hK
      hw.polarBilin_fixed_nondegenerate (restrictFixed_mem_orthogonalGroup _) hodd
  have hgΩ : (g : V ≃ₗ[K] V) ∈ orthDerived Q := hw.supportedFixedDerived_le_orthDerived hgS
  set gΩ : ↥(orthDerived Q) := ⟨g, hgΩ⟩
  have hgΩ1 : gΩ ≠ 1 := by
    intro h1
    apply htu
    have hgu : (g : V ≃ₗ[K] V) u = u := by
      have := congrArg (fun f : ↥(orthDerived Q) => (f : V ≃ₗ[K] V) u) h1
      simpa [gΩ] using this
    have := congrArg (fun f : fixedSpace w ≃ₗ[K] fixedSpace w => (f ⟨u, hu⟩ : V)) hg
    simp only [coe_restrictFixed, φ, coe_restrictEquiv] at this
    rw [← this, hgu]
  have hπg1 : projT Q gΩ ≠ 1 := by
    intro h
    apply hgΩ1
    exact projT_injOn_supportedFixedDerived hw hR hgS (Subgroup.one_mem _) (by rw [h, map_one])
  have hord : orderOf (projT Q gΩ) = p :=
    orderOf_eq_prime (by rw [← map_pow]; rw [show gΩ ^ p = 1 from Subtype.ext (by
      show ((g : V ≃ₗ[K] V)) ^ p = 1
      exact congrArg Subtype.val hgp), map_one]) hπg1
  have hmem : projT Q gΩ ∈ fixedComponentImage Q w :=
    ⟨gΩ, Subgroup.mem_subgroupOf.mpr hgS, rfl⟩
  rw [← hord, ← Subgroup.orderOf_mk (projT Q gΩ) hmem]
  exact orderOf_dvd_natCard _

theorem card_sup_dvd_mul_of_commute {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : Nat.card ↥(A ⊔ B) ∣ Nat.card A * Nat.card B := by
  have hc : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) :=
    fun a b => hAB a a.2 b b.2
  have hr : (MonoidHom.noncommCoprod A.subtype B.subtype hc).range = A ⊔ B := by
    have := MonoidHom.noncommCoprod_range A.subtype B.subtype hc
    rwa [Subgroup.range_subtype, Subgroup.range_subtype] at this
  rw [← hr, ← Nat.card_prod]
  exact Subgroup.card_range_dvd _

theorem exists_quasisimple_le_fixedComponentImage (hw : OddOrderIsometry Q p w) (hp : p.Prime)
    (hR : othersSpace w.toLinearMap (X - 1) ≠ ⊥) (hodd : Odd (Nat.card K))
    (hK3 : Nat.card K ≠ 3)
    (hdim : finrank K (fixedSpace w) = 3 ∨ finrank K (fixedSpace w) = 4)
    (hpdvd : p ∣ Nat.card ↥(fixedComponentImage Q w)) :
    ∃ L : Subgroup (ProjOrthDerived Q), L ≤ fixedComponentImage Q w ∧
      (L.subgroupOf (fixedComponentImage Q w)).Normal ∧ CFSG.IsQuasisimple ↥L ∧
        p ∣ Nat.card ↥L := by
  classical
  set J := fixedComponentImage Q w
  set e := fixedComponentImageEquiv hw hR
  set Q' := Q.comp (fixedSpace w).subtype
  have hQ' := hw.polarBilin_fixed_nondegenerate
  set C := commutator (TauCeti.QuadraticMap.orthogonalGroup Q')
  have hpC : p ∣ Nat.card ↥C := by rw [← Nat.card_congr e.toEquiv]; exact hpdvd
  have hwhole : CFSG.IsQuasisimple ↥C → ∃ L : Subgroup (ProjOrthDerived Q), L ≤ J ∧
      (L.subgroupOf J).Normal ∧ CFSG.IsQuasisimple ↥L ∧ p ∣ Nat.card ↥L := fun hC =>
    ⟨J, le_rfl, by rw [Subgroup.subgroupOf_self]; infer_instance,
      CFSG.IsQuasisimple.of_mulEquiv e hC, hpdvd⟩
  rcases hdim with h3 | h4
  · obtain ⟨-, -, -, -, -, -, hq, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.orthogonal_three_derived hodd hK3 Q' hQ' h3
    exact hwhole hq
  by_cases hS : ∃ S : Submodule K (fixedSpace w), finrank K S = 2 ∧ ∀ v ∈ S, Q' v = 0
  ·
    have hK2 : Nat.card K ≠ 2 := fun h => by rw [h] at hodd; exact absurd hodd (by decide)
    obtain ⟨-, e', -, -, hsup, hqA, hqB, hnA, hnB, hcomm, -, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.orthogonal_split_four_derived hK2 hK3 Q' hQ' h4 hS
    set A := (CFSG.LocalAnalysis.ComponentInitial.determinantLeftFactor
      K).map e'.symm.toMonoidHom
    set B := (CFSG.LocalAnalysis.ComponentInitial.determinantRightFactor
      K).map e'.symm.toMonoidHom
    have hsupC : C = A ⊔ B := hsup
    have hAC : A ≤ C := by rw [hsupC]; exact le_sup_left
    have hBC : B ≤ C := by rw [hsupC]; exact le_sup_right
    have hdvd : p ∣ Nat.card A * Nat.card B := by
      rw [hsupC] at hpC
      exact hpC.trans (card_sup_dvd_mul_of_commute hcomm)
    have key : ∀ F : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup Q'), F ≤ C →
        (F.subgroupOf C).Normal → CFSG.IsQuasisimple ↥F → p ∣ Nat.card F →
        ∃ L : Subgroup (ProjOrthDerived Q), L ≤ J ∧ (L.subgroupOf J).Normal ∧
          CFSG.IsQuasisimple ↥L ∧ p ∣ Nat.card ↥L := by
      intro F hFC hFn hFq hFp
      set F₁ : Subgroup ↥J := (F.subgroupOf C).map e.symm.toMonoidHom
      refine ⟨F₁.map J.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
      · have hF₁ : (F₁.map J.subtype).subgroupOf J = F₁ := by
          ext z
          rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
          constructor
          · rintro ⟨y, hy, hyz⟩
            rwa [show y = z from Subtype.ext hyz] at hy
          · intro hz
            exact ⟨z, hz, rfl⟩
        rw [hF₁]
        exact hFn.map _ e.symm.surjective
      · have e₁ : ↥(F₁.map J.subtype) ≃* ↥F :=
          ((Subgroup.equivMapOfInjective F₁ J.subtype J.subtype_injective).symm.trans
            (Subgroup.equivMapOfInjective _ e.symm.toMonoidHom e.symm.injective).symm).trans
            (Subgroup.subgroupOfEquivOfLe hFC)
        exact CFSG.IsQuasisimple.of_mulEquiv e₁ hFq
      · have e₁ : ↥(F₁.map J.subtype) ≃* ↥F :=
          ((Subgroup.equivMapOfInjective F₁ J.subtype J.subtype_injective).symm.trans
            (Subgroup.equivMapOfInjective _ e.symm.toMonoidHom e.symm.injective).symm).trans
            (Subgroup.subgroupOfEquivOfLe hFC)
        rw [Nat.card_congr e₁.toEquiv]
        exact hFp
    haveI : Fact p.Prime := ⟨hp⟩
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with hA | hB
    · exact key A hAC hnA hqA hA
    · exact key B hBC hnB hqB hB
  · obtain ⟨-, -, -, -, -, -, -, -, hq, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.orthogonal_nonsplit_four_derived hodd Q' hQ' h4 hS
    exact hwhole hq

theorem glaPLayer_ne_bot_of_mul [Finite K] (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {x y : ↥(orthDerived Q)}
    (hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V)) (hy : OddOrderIsometry Q p (y : V ≃ₗ[K] V))
    (hxy : (x : V ≃ₗ[K] V) * (y : V ≃ₗ[K] V) = (y : V ≃ₗ[K] V) * x)
    (hyR : ∀ v, (y : V ≃ₗ[K] V) ((x : V ≃ₗ[K] V) v - v) = (x : V ≃ₗ[K] V) v - v)
    (hp : p.Prime) (hp2 : p ≠ 2) (hy1 : y ≠ 1) (hK : ringChar K ≠ 2) (hodd : Odd (Nat.card K))
    (hK3 : Nat.card K ≠ 3) (hR : othersSpace (x : V ≃ₗ[K] V).toLinearMap (X - 1) ≠ ⊥)
    (hdim : finrank K (fixedSpace ((x : V ≃ₗ[K] V) * (y : V ≃ₗ[K] V))) = 3 ∨
      finrank K (fixedSpace ((x : V ≃ₗ[K] V) * (y : V ≃ₗ[K] V))) = 4)
    {t : V ≃ₗ[K] V} (ht : t ∈ isometryCentralizer Q ((x : V ≃ₗ[K] V) * (y : V ≃ₗ[K] V))) (htp : t ^ p = 1)
    {u : V} (hu : u ∈ fixedSpace ((x : V ≃ₗ[K] V) * (y : V ≃ₗ[K] V))) (htu : t u ≠ u) :
    GLAPLayer p (fixedComponentImage Q (x : V ≃ₗ[K] V) ⊓ Subgroup.centralizer {projT Q y}) ≠
      ⊥ := by
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hw := oddOrderIsometry_mul hx hy hxy hyR
  have hRw : othersSpace ((x : V ≃ₗ[K] V) * (y : V ≃ₗ[K] V)).toLinearMap (X - 1) ≠ ⊥ := fun h =>
    hR (le_bot_iff.mp (h ▸ othersSpace_le_othersSpace_mul hx hy hxy hyR))
  have hpdvd := dvd_card_fixedComponentImage hw hp hp2 hK hRw ht htp hu htu
  obtain ⟨L, hLJ, hLn, hLq, hLp⟩ :=
    exists_quasisimple_le_fixedComponentImage hw hp hRw hodd hK3 hdim hpdvd
  have hJX := fixedComponentImage_mul_le hx hy hxy hyR
  have hJn := normal_fixedComponentImage_mul hx hy hxy hyR hQ hT hp hp2 hy1
  have hsub : CFSG.Open.IsSubnormal L
      (fixedComponentImage Q (x : V ≃ₗ[K] V) ⊓ Subgroup.centralizer {projT Q y}) :=
    CFSG.Open.IsSubnormal.step hLJ hLn
      (CFSG.Open.IsSubnormal.step hJX hJn (CFSG.Open.IsSubnormal.refl _))
  have hLq' : CFSG.Open.IsQuasisimple ↥L := ⟨hLq.1.commutator_eq_top, hLq.2.1⟩
  have hcomp := CFSG.LocalAnalysis.GLTheoremA.S10.glaPComponent_of_quasisimple hp hsub hLq'
    (CFSG.dvd_card_quotient_center_of_quasisimple hLq hp hLp)
  intro hbot
  have hle : L ≤ GLAPLayer p
      (fixedComponentImage Q (x : V ≃ₗ[K] V) ⊓ Subgroup.centralizer {projT Q y}) :=
    le_sSup hcomp
  rw [hbot, le_bot_iff] at hle
  exact CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_ne_bot hcomp hle

end Low

end CFSG.LocalAnalysis.GLTheoremA.H81Orth
