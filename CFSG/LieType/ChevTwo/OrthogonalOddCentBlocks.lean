module

public import CFSG.RankThree.PartOne.KC.OrthogonalSelfDualBlock

public section

namespace CFSG.LieType.ChevTwo

open Module CFSG.RankThree.PartOne.KCOrthogonal

namespace OddCentBlocks

open Polynomial CFSG.RankThree.PartOne.KCPrimary

section Monomial

variable {E : Type*} [Field E] {m : ℕ}

@[expose] noncomputable def monoDiag (μ : Fin m → Eˣ) : (Fin m → E) ≃ₗ[E] (Fin m → E) :=
  LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfUnit (μ i)

theorem monoDiag_apply (μ : Fin m → Eˣ) (a : Fin m → E) (i : Fin m) :
    monoDiag μ a i = (μ i : E) * a i := rfl

@[expose] noncomputable def monoSwap (i j : Fin m) : (Fin m → E) ≃ₗ[E] (Fin m → E) :=
  LinearEquiv.funCongrLeft E E (Equiv.swap i j)

theorem monoSwap_apply (i j : Fin m) (a : Fin m → E) (k : Fin m) :
    monoSwap i j a k = a (Equiv.swap i j k) := rfl

theorem sum_monoDiag {σ : E → E} (hσ : ∀ a b, σ (a * b) = σ a * σ b) (μ : Fin m → Eˣ)
    (hμ : ∀ i, σ (μ i) * μ i = 1) (a b : Fin m → E) :
    ∑ i, σ (monoDiag μ a i) * monoDiag μ b i = ∑ i, σ (a i) * b i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [monoDiag_apply, monoDiag_apply, hσ]
  calc σ (μ i) * σ (a i) * ((μ i : E) * b i) = (σ (μ i) * μ i) * (σ (a i) * b i) := by ring
    _ = σ (a i) * b i := by rw [hμ i, one_mul]

theorem sum_monoSwap (σ : E → E) (i j : Fin m) (a b : Fin m → E) :
    ∑ k, σ (monoSwap i j a k) * monoSwap i j b k = ∑ k, σ (a k) * b k :=
  Equiv.sum_comp (Equiv.swap i j) (fun k => σ (a k) * b k)

theorem eq_top_of_monomial_invariant {u : Eˣ} (hu : (u : E) ≠ 1) (S : Submodule E (Fin m → E))
    (hD : ∀ j, ∀ a ∈ S, monoDiag (Pi.mulSingle j u) a ∈ S)
    (hP : ∀ i j, ∀ a ∈ S, monoSwap i j a ∈ S) (hS : S ≠ ⊥) : S = ⊤ := by
  classical
  obtain ⟨a, haS, ha0⟩ := (Submodule.ne_bot_iff S).mp hS
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := Function.ne_iff.mp ha0
  have hc : ((u : E) - 1) * a i ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hu) hi
  have h1 : monoDiag (Pi.mulSingle i u) a - a = Pi.single i (((u : E) - 1) * a i) := by
    ext k
    by_cases hk : k = i
    · subst hk
      simp only [Pi.sub_apply, monoDiag_apply, Pi.mulSingle_eq_same, Pi.single_eq_same]
      ring
    · simp [monoDiag_apply, hk, Pi.mulSingle_eq_of_ne hk]
  have h2 : Pi.single i (1 : E) ∈ S := by
    have h3 : Pi.single i (((u : E) - 1) * a i) ∈ S := h1 ▸ S.sub_mem (hD i a haS) haS
    have h4 : Pi.single i (1 : E) =
        (((u : E) - 1) * a i)⁻¹ • Pi.single i (((u : E) - 1) * a i) := by
      ext k
      by_cases hk : k = i
      · subst hk
        rw [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, smul_eq_mul,
          inv_mul_cancel₀ hc]
      · simp [hk]
    rw [h4]
    exact S.smul_mem _ h3
  have h5 : ∀ j, Pi.single j (1 : E) ∈ S := by
    intro j
    have h6 := hP i j _ h2
    convert h6 using 1
    ext k
    rw [monoSwap_apply]
    by_cases hkj : k = j
    · rw [hkj, Equiv.swap_apply_right]
      simp
    · by_cases hki : k = i
      · rw [hki, Equiv.swap_apply_left]
        rw [hki] at hkj
        simp [Pi.single_apply, hkj, Ne.symm hkj]
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
        simp [Pi.single_apply, hki, hkj]
  rw [Submodule.eq_top_iff']
  intro b
  rw [pi_eq_sum_univ' b]
  exact S.sum_mem fun j _ => S.smul_mem _ (h5 j)

end Monomial

section Frame

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem exists_mem_isometryCentralizer_of_mem_range {h : K[X]} {m : ℕ}
    (ι : (Fin m → AdjoinRoot h) ≃ₗ[AdjoinRoot h] primaryComponent x.toLinearMap h)
    (M : (Fin m → AdjoinRoot h) ≃ₗ[AdjoinRoot h] (Fin m → AdjoinRoot h))
    (hM : LinearMap.GeneralLinearGroup.ofLinearEquiv (ι.symm.trans (M.trans ι)) ∈
      (blockGL Q x h).range) :
    ∃ g ∈ isometryCentralizer Q x, ∀ a, g (ι a : V) = ι (M a) := by
  obtain ⟨g, hg⟩ := hM
  refine ⟨g.1, supportedBlock_le_isometryCentralizer h g.2, fun a => ?_⟩
  rw [← coe_blockGL h g (ι a), hg]
  simp

variable [FiniteDimensional K V] {p : ℕ}

theorem exists_frame_paired (hx : OddOrderIsometry Q p x) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ reciprocalPolynomial h) :
    ∃ ι : (Fin (finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h)) → AdjoinRoot h) ≃ₗ[
        AdjoinRoot h] primaryComponent x.toLinearMap h,
      ∀ M : (Fin (finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h)) → AdjoinRoot h) ≃ₗ[
          AdjoinRoot h] (Fin (finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h)) →
            AdjoinRoot h),
        ∃ g ∈ isometryCentralizer Q x, ∀ a, g (ι a : V) = ι (M a) :=
  ⟨(Module.finBasis _ _).equivFun.symm, fun M =>
    exists_mem_isometryCentralizer_of_mem_range _ M (hx.blockGL_surjective_paired hh hne _)⟩

variable [Finite K]

theorem exists_frame_selfDual (hx : OddOrderIsometry Q p x) (hp2 : Odd p) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) :
    ∃ (σ : AdjoinRoot h ≃ₐ[K] AdjoinRoot h)
      (ι : (Fin (finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h)) → AdjoinRoot h) ≃ₗ[
        AdjoinRoot h] primaryComponent x.toLinearMap h),
      σ (AdjoinRoot.root h) * AdjoinRoot.root h = 1 ∧
      ∀ M : (Fin (finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h)) → AdjoinRoot h) ≃ₗ[
          AdjoinRoot h] (Fin (finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h)) →
            AdjoinRoot h),
        (∀ a b, ∑ i, σ (M a i) * M b i = ∑ i, σ (a i) * b i) →
        ∃ g ∈ isometryCentralizer Q x, ∀ a, g (ι a : V) = ι (M a) := by
  classical
  have hirr : Irreducible h := Fact.out
  obtain ⟨d, -, hdeg, hroot, -⟩ := hx.exists_selfDual_hermitian hp2 hh hne1 hself
  have hd : finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  set σ := frobPow K (AdjoinRoot h) d with hσdef
  have hσroot : σ (AdjoinRoot.root h) = (AdjoinRoot.root h)⁻¹ := by
    rw [hσdef, frobPow_apply, hroot]
  have hp0 : p ≠ 0 := hp2.pos.ne'
  have hlamp : AdjoinRoot.root h ^ p = 1 := root_pow_eq_one (hx.dvd_X_pow_sub_one hh)
  have hlam0 : AdjoinRoot.root h ≠ 0 := fun h0 => by
    rw [h0, zero_pow hp0] at hlamp
    exact zero_ne_one hlamp
  have hbal := hx.polar_smul_balanced σ hσroot hlam0
  have hnd : ∀ u : primaryComponent x.toLinearMap h, (∀ w, componentPolar Q x h u w = 0) →
      u = 0 := fun u hu =>
    Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => hu ⟨w, hw⟩)
  obtain ⟨ι, hι⟩ := exists_hermitian_trace_coordinates (componentPolar Q x h) σ
    (isUnitaryInvolution K (AdjoinRoot h) hd) (fun u w => QuadraticMap.polar_comm Q _ _) hbal hnd
  refine ⟨σ, ι, by rw [hσroot, inv_mul_cancel₀ hlam0], fun M hM => ?_⟩
  let H : primaryComponent x.toLinearMap h → primaryComponent x.toLinearMap h → AdjoinRoot h :=
    fun u w => ∑ i, σ (ι.symm u i) * ι.symm w i
  have hH : ∀ u w c, Algebra.trace K (AdjoinRoot h) (H u w * c) =
      QuadraticMap.polar Q (u : V) ((c • w : primaryComponent x.toLinearMap h) : V) := by
    intro u w c
    have h1 := hι (ι.symm u) (c • ι.symm w)
    rw [ι.apply_symm_apply, map_smul, ι.apply_symm_apply] at h1
    rw [← componentPolar_apply, h1]
    congr 1
    simp only [H, Finset.sum_mul, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  refine exists_mem_isometryCentralizer_of_mem_range ι M
    ((hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH _).mpr fun u w => ?_)
  simp only [H]
  have e1 : ∀ v, ((LinearMap.GeneralLinearGroup.ofLinearEquiv (ι.symm.trans (M.trans ι)) :
      Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) v) = ι (M (ι.symm v)) :=
    fun v => rfl
  rw [e1, e1, ι.symm_apply_apply, ι.symm_apply_apply]
  exact hM _ _

theorem exists_monomial_frame (hx : OddOrderIsometry Q p x) (hp2 : Odd p) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (u : (AdjoinRoot h)ˣ) (hu : (u : AdjoinRoot h) = AdjoinRoot.root h) :
    ∃ ι : (Fin (finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h)) → AdjoinRoot h) ≃ₗ[
        AdjoinRoot h] primaryComponent x.toLinearMap h,
      (∀ j, ∃ g ∈ isometryCentralizer Q x, ∀ a, g (ι a : V) = ι (monoDiag (Pi.mulSingle j u) a)) ∧
      ∀ i j, ∃ g ∈ isometryCentralizer Q x, ∀ a, g (ι a : V) = ι (monoSwap i j a) := by
  classical
  by_cases hself : h = reciprocalPolynomial h
  · obtain ⟨σ, ι, hσ, hι⟩ := exists_frame_selfDual hx hp2 hh hne1 hself
    refine ⟨ι, fun j => hι _ (sum_monoDiag (map_mul σ) _ fun i => ?_ ),
      fun i j => hι _ (sum_monoSwap _ i j)⟩
    by_cases hij : i = j
    · subst hij
      rw [Pi.mulSingle_eq_same, hu, hσ]
    · rw [Pi.mulSingle_eq_of_ne hij, Units.val_one, map_one, one_mul]
  · obtain ⟨ι, hι⟩ := exists_frame_paired hx hh hself
    exact ⟨ι, fun j => hι _, fun i j => hι _⟩

end Frame

section FixedSub

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {x : V ≃ₗ[K] V}

@[expose] noncomputable def fixedSub (N : Subgroup (V ≃ₗ[K] V))
    (hN : N ≤ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V))) (h : K[X]) :
    Submodule (AdjoinRoot h) (primaryComponent x.toLinearMap h) where
  carrier := {v | ∀ φ ∈ N, φ (v : V) = v}
  add_mem' := by
    intro u w hu hw φ hφ
    rw [Submodule.coe_add, map_add, hu φ hφ, hw φ hφ]
  zero_mem' := by
    intro φ _
    simp
  smul_mem' := by
    intro c v hv φ hφ
    have h1 := coe_centralizerGL x h ⟨φ, hN hφ⟩ (c • v)
    have h2 : (centralizerGL x h ⟨φ, hN hφ⟩ : Module.End (AdjoinRoot h)
        (primaryComponent x.toLinearMap h)) v = v :=
      Subtype.ext ((coe_centralizerGL x h ⟨φ, hN hφ⟩ v).trans (hv φ hφ))
    rw [map_smul, h2] at h1
    exact h1.symm

theorem mem_fixedSub {N : Subgroup (V ≃ₗ[K] V)}
    {hN : N ≤ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V))} {h : K[X]}
    {v : primaryComponent x.toLinearMap h} :
    v ∈ fixedSub N hN h ↔ ∀ φ ∈ N, φ (v : V) = v := Iff.rfl

end FixedSub

theorem inv_mul_mul_mem_of_normal {G : Type*} [Group G] {N C : Subgroup G} (hN : N ≤ C)
    (hNn : (N.subgroupOf C).Normal) {g φ : G} (hg : g ∈ C) (hφ : φ ∈ N) : g⁻¹ * φ * g ∈ N := by
  have h1 := hNn.conj_mem ⟨φ, hN hφ⟩ (Subgroup.mem_subgroupOf.mpr hφ) ⟨g, hg⟩⁻¹
  rw [Subgroup.mem_subgroupOf] at h1
  simpa using h1

section Two

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem fixes_primaryComponent (q : QuadraticForm (ZMod 2) V) {p : ℕ} {x : V ≃ₗ[ZMod 2] V}
    (hx : OddOrderIsometry q p x) (hp2 : Odd p) (N : Subgroup (V ≃ₗ[ZMod 2] V))
    (hN : N ≤ isometryCentralizer q x) (hNn : (N.subgroupOf (isometryCentralizer q x)).Normal)
    (hN2 : IsPGroup 2 N) {h : (ZMod 2)[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) : ∀ φ ∈ N, ∀ v ∈ primaryComponent x.toLinearMap h, φ v = v := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hNc : N ≤ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V)) :=
    fun φ hφ => (Subgroup.mem_inf.mp (hN hφ)).2
  have hS0 : fixedSub N hNc h ≠ ⊥ := by
    letI : MulAction N (primaryComponent x.toLinearMap h) :=
      { smul := fun φ v => ⟨φ.1 v, apply_mem_primaryComponent
          (commute_toLinearMap_of_mem_centralizer x (hNc φ.2)) v.2⟩
        one_smul := fun v => rfl
        mul_smul := fun φ ψ v => rfl }
    haveI : Finite V := Module.finite_of_finite (ZMod 2)
    have hpos : 1 ≤ finrank (ZMod 2) (primaryComponent x.toLinearMap h) :=
      Submodule.one_le_finrank_iff.mpr (primaryComponent_ne_bot hx.squarefree_minpoly hh)
    have hdvd : 2 ∣ Nat.card (primaryComponent x.toLinearMap h) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
      exact dvd_pow_self 2 (by omega)
    obtain ⟨b, hb, hb0⟩ := hN2.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      (primaryComponent x.toLinearMap h) hdvd (a := 0)
      (MulAction.mem_fixedPoints.mpr fun φ => Subtype.ext (map_zero φ.1))
    refine (Submodule.ne_bot_iff _).mpr ⟨b, mem_fixedSub.mpr fun φ hφ => ?_, fun h0 => hb0 h0.symm⟩
    exact congrArg Subtype.val (MulAction.mem_fixedPoints.mp hb ⟨φ, hφ⟩)
  have hmon := (mem_primaryFactors.mp hh).2.1
  have hlam1 : AdjoinRoot.root h ≠ 1 := root_ne_one hmon hne1
  have hlamp : AdjoinRoot.root h ^ p = 1 := root_pow_eq_one (hx.dvd_X_pow_sub_one hh)
  have hlam0 : AdjoinRoot.root h ≠ 0 := fun h0 => by
    rw [h0, zero_pow hp2.pos.ne'] at hlamp
    exact zero_ne_one hlamp
  obtain ⟨ι, hD, hP⟩ := exists_monomial_frame hx hp2 hh hne1 (Units.mk0 _ hlam0) rfl
  have hinv : ∀ g ∈ isometryCentralizer q x, ∀ a b, g (ι a : V) = ι b →
      ι a ∈ fixedSub N hNc h → ι b ∈ fixedSub N hNc h := by
    intro g hg a b hab ha
    refine mem_fixedSub.mpr fun φ hφ => ?_
    rw [← hab]
    have h2 := mem_fixedSub.mp ha _ (inv_mul_mul_mem_of_normal hN hNn hg hφ)
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv] at h2
    calc φ (g (ι a : V)) = g (g.symm (φ (g (ι a : V)))) := (g.apply_symm_apply _).symm
      _ = g (ι a : V) := by rw [h2]
  have htop := eq_top_of_monomial_invariant (u := Units.mk0 _ hlam0) hlam1
    ((fixedSub N hNc h).comap ι.toLinearMap)
    (fun j a ha => by
      obtain ⟨g, hg, hga⟩ := hD j
      exact hinv g hg a _ (hga a) ha)
    (fun i j a ha => by
      obtain ⟨g, hg, hga⟩ := hP i j
      exact hinv g hg a _ (hga a) ha)
    (by
      obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hS0
      refine (Submodule.ne_bot_iff _).mpr ⟨ι.symm v, ?_, fun h0 => hv0 ?_⟩
      · rw [Submodule.mem_comap, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
        exact hv
      · rw [← ι.apply_symm_apply v, h0, map_zero])
  intro φ hφ v hv
  have h1 := (Submodule.eq_top_iff'.mp htop) (ι.symm ⟨v, hv⟩)
  rw [Submodule.mem_comap, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h1
  exact mem_fixedSub.mp h1 φ hφ

end Two

end OddCentBlocks

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem normal_two_subgroup_fixes_range (q : QuadraticForm (ZMod 2) V) {p : ℕ}
    {x : V ≃ₗ[ZMod 2] V} (hx : OddOrderIsometry q p x) (hp : p.Prime) (hp2 : p ≠ 2)
    (N : Subgroup (V ≃ₗ[ZMod 2] V)) (hN : N ≤ isometryCentralizer q x)
    (hNn : (N.subgroupOf (isometryCentralizer q x)).Normal) (hN2 : IsPGroup 2 N) :
    ∀ φ ∈ N, ∀ v ∈ LinearMap.range (x.toLinearMap - 1), φ v = v := by
  open Polynomial CFSG.RankThree.PartOne.KCPrimary in
  intro φ hφ v hv
  obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hv
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have key : φ.toLinearMap ∘ₗ (x.toLinearMap - 1) = x.toLinearMap - 1 := by
    refine ext_primaryComponent hx.squarefree_minpoly fun a ha u hu => ?_
    by_cases ha1 : a = X - 1
    · subst ha1
      have h0 : (x.toLinearMap - 1) u = 0 := by
        have := mem_primaryComponent.mp hu
        simpa using this
      rw [LinearMap.comp_apply, h0, map_zero]
    · have hc : Commute (x.toLinearMap - 1) x.toLinearMap :=
        (Commute.refl x.toLinearMap).sub_left (Commute.one_left x.toLinearMap)
      have hmem : (x.toLinearMap - 1) u ∈ primaryComponent x.toLinearMap a :=
        apply_mem_primaryComponent hc hu
      exact OddCentBlocks.fixes_primaryComponent q hx hodd N hN hNn hN2 ha ha1 φ hφ _ hmem
  exact LinearMap.congr_fun key w

end CFSG.LieType.ChevTwo
