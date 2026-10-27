module

public import CFSG.LieType.ChevTwo.Defs
public import CFSG.LieType.ChevTwo.OrthogonalOddCentGeom
public import CFSG.LieType.ChevTwo.OrthogonalOddCentBlocks
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.ArfFpf
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedBlock

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremB (IsTransvection HasFixedPointFreeOrder)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def OrthOddCentCoreStrong (Q : (ι → ZMod 2) → ZMod 2) (ε : Bool) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ d ∈ isoGrp Q, d ≠ 1 → d ^ p = 1 →
    ∀ N : Subgroup (GL ι (ZMod 2)),
      N ≤ isoGrp Q ⊓ Subgroup.centralizer ({d} : Set (GL ι (ZMod 2))) →
      (N.subgroupOf (isoGrp Q ⊓ Subgroup.centralizer ({d} : Set (GL ι (ZMod 2))))).Normal →
      IsPGroup 2 N → N ≠ ⊥ →
        (∃ t ∈ N, IsTransvection t ∧ N = Subgroup.zpowers t) ∧ HasFixedPointFreeOrder ε n p

theorem orthOddCentCore_of_strong {Q : (ι → ZMod 2) → ZMod 2} {ε : Bool} {n : ℕ}
    (h : OrthOddCentCoreStrong Q ε n) : OrthOddCentCore Q ε n :=
  fun p hp hp2 d hd hd1 hdp N hN hNn hN2 _ hN1 => h p hp hp2 d hd hd1 hdp N hN hNn hN2 hN1

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace OrthOddCent

open Module Polynomial QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration (cs cs_eq_sum cs_perpSplit
  dvd_of_fpf_of_cs polarPerp isCompl_polarPerp)

section Abstract

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V} {p : ℕ} {x : V ≃ₗ[ZMod 2] V}

theorem othersSpace_le_range (hx : OddOrderIsometry q p x) :
    othersSpace x.toLinearMap (X - 1) ≤ LinearMap.range (x.toLinearMap - 1) := by
  set O := othersSpace x.toLinearMap (X - 1) with hO
  have hxO : ∀ v ∈ O, (x.toLinearMap - 1) v ∈ O := fun v hv => by
    have h1 : x v ∈ O :=
      mem_othersSpace_of_apply (Subgroup.mem_centralizer_singleton_iff.mpr rfl) hv
    simpa using O.sub_mem h1 hv
  set f : O →ₗ[ZMod 2] O := (x.toLinearMap - 1).restrict hxO with hf
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    have h1 : (v : V) ∈ fixedSpace x := by
      rw [fixedSpace, LinearMap.mem_ker]
      have := congrArg Subtype.val (LinearMap.mem_ker.mp hv)
      simpa [f] using this
    exact Subtype.ext (Submodule.disjoint_def.mp hx.fixed_others.1.disjoint _ h1 v.2)
  intro r hr
  obtain ⟨r', hr'⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨r, hr⟩
  exact ⟨r', congrArg Subtype.val hr'⟩

theorem polarNondegOn_fixedSpace (hx : OddOrderIsometry q p x) :
    CFSG.ClassicalGroups.Orthogonal.PolarNondegOn q (fixedSpace x) := by
  intro w hw hperp
  refine hx.regular w fun v => ?_
  obtain ⟨u, hu, r, hr, rfl⟩ := exists_add_of_isCompl hx.fixed_others.1 v
  rw [polar_add_right, hperp u hu, hx.fixed_others.2 w hw r hr, add_zero]

theorem exists_transvection_of_normal (hx : OddOrderIsometry q p x) (hp : p.Prime) (hp2 : p ≠ 2)
    (N : Subgroup (V ≃ₗ[ZMod 2] V)) (hN : N ≤ isometryCentralizer q x)
    (hNn : (N.subgroupOf (isometryCentralizer q x)).Normal) (hN2 : IsPGroup 2 N) (hN1 : N ≠ ⊥) :
    finrank (ZMod 2) (fixedSpace x) = 2 ∧ ∃ u ∈ fixedSpace x, q u = 1 ∧
      (∀ y ∈ fixedSpace x, q y = 1 → y = u) ∧
      ∃ t ∈ N, (∀ v, t v = v + polar q v u • u) ∧ ∀ g ∈ N, g = 1 ∨ g = t := by
  classical
  obtain ⟨hc, horth⟩ := hx.fixed_others
  set U := fixedSpace x with hU
  set O := othersSpace x.toLinearMap (X - 1) with hO
  have hfixR := normal_two_subgroup_fixes_range q hx hp hp2 N hN hNn hN2
  have hfixO : ∀ g ∈ N, ∀ r ∈ O, g r = r := fun g hg r hr =>
    hfixR g hg r (othersSpace_le_range hx hr)
  set B := supportedBlock q x (X - 1) with hB
  have hNB : N ≤ B := fun g hg => mem_supportedBlock.mpr ⟨hN hg, hfixO g hg⟩
  have hBM : B ≤ isometryCentralizer q x := inf_le_left
  let N' : Subgroup (U ≃ₗ[ZMod 2] U) := (N.subgroupOf B).map (restrictFixed q x)
  have hres : ∀ g (hg : g ∈ N), restrictFixed q x ⟨g, hNB hg⟩ ∈ N' := fun g hg =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hg)
  have h1 : N' ≤ TauCeti.QuadraticMap.orthogonalGroup (q.comp U.subtype) := by
    rintro _ ⟨g, -, rfl⟩
    exact restrictFixed_mem_orthogonalGroup g
  have h2 : (N'.subgroupOf (TauCeti.QuadraticMap.orthogonalGroup (q.comp U.subtype))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff h1]
    rintro _ k ⟨g, hg, rfl⟩ hk
    obtain ⟨b, rfl⟩ := restrictFixed_surjective hx k hk
    refine ⟨b * g * b⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.normal_subgroupOf_iff hN).mp hNn g b (Subgroup.mem_subgroupOf.mp hg)
      (hBM b.2)
  have h3 : IsPGroup 2 N' := (hN2.comap_subtype (K := B)).map _
  have hreg : ∀ v : U, (∀ w : U, polar (q.comp U.subtype) v w = 0) → v = 0 := by
    intro v hv
    exact Subtype.ext (polarNondegOn_fixedSpace hx v v.2 fun y hy => hv ⟨y, hy⟩)
  rcases orthogonal_normal_two_subgroup (q.comp U.subtype) hreg N' h1 h2 h3 with
    hall | ⟨hdim, u, hu1, huniq, hφ⟩
  · exfalso
    apply hN1
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    have h := hall _ (hres g hg)
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hc v
    have hw' : (restrictFixed q x ⟨g, hNB hg⟩ ⟨w, hw⟩ : V) = w := by rw [h]; rfl
    rw [coe_restrictFixed] at hw'
    rw [map_add, hw', hfixO g hg r hr]
    rfl
  · have hform : ∀ g ∈ N, g = 1 ∨ ∀ v, g v = v + polar q v u • u := by
      intro g hg
      rcases hφ _ (hres g hg) with hid | ht
      · left
        refine LinearEquiv.ext fun v => ?_
        obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hc v
        have := congrArg Subtype.val (hid ⟨w, hw⟩)
        rw [coe_restrictFixed] at this
        rw [map_add, this, hfixO g hg r hr]
        rfl
      · right
        intro v
        obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hc v
        have hgw : g w = w + polar q w u • (u : V) := congrArg Subtype.val (ht ⟨w, hw⟩)
        have hru : polar q r u = 0 := by rw [polar_comm]; exact horth u u.2 r hr
        rw [map_add, hgw, hfixO g hg r hr, polar_add_left, hru, add_zero]
        abel
    obtain ⟨t, htN, ht1⟩ : ∃ t ∈ N, t ≠ 1 := by
      by_contra! h
      exact hN1 ((Subgroup.eq_bot_iff_forall N).mpr h)
    have htform : ∀ v, t v = v + polar q v u • u := (hform t htN).resolve_left ht1
    refine ⟨hdim, u, u.2, hu1, fun y hy hy1 => congrArg Subtype.val (huniq ⟨y, hy⟩ hy1), t, htN,
      htform, fun g hg => ?_⟩
    rcases hform g hg with h | h
    · exact Or.inl h
    · exact Or.inr (LinearEquiv.ext fun v => by rw [h v, htform v])

theorem cs_restrict_eq_two {W : Submodule (ZMod 2) V} (hW : finrank (ZMod 2) W = 2) {u : V}
    (hu : u ∈ W) (hu1 : q u = 1) (huniq : ∀ y ∈ W, q y = 1 → y = u) :
    cs (q.restrict W) = 2 := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Fintype W := Fintype.ofFinite W
  have hcard : Fintype.card W = 4 := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hW]
    norm_num
  rw [cs_eq_sum]
  have h : ∀ y : W,
      (-1 : ℤ) ^ (q.restrict W y).val = 1 - 2 * (if y = ⟨u, hu⟩ then 1 else 0) := by
    intro y
    by_cases hy : y = ⟨u, hu⟩
    · subst hy
      simp only [QuadraticMap.restrict_apply, hu1, if_true]
      decide
    · have hq0 : q.restrict W y = 0 := by
        rcases CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.zmod_two_cases
          (q.restrict W y) with h | h
        · exact h
        · exact absurd (Subtype.ext (huniq y y.2 h)) hy
      rw [hq0, if_neg hy]
      decide
  rw [Finset.sum_congr rfl fun y _ => h y]
  simp [Finset.sum_sub_distrib, hcard]

theorem dvd_of_hyperbolic_fixedSpace (hx : OddOrderIsometry q p x) (hp : p.Prime)
    (hU : finrank (ZMod 2) (fixedSpace x) = 2) {u : V} (hu : u ∈ fixedSpace x) (hu1 : q u = 1)
    (huniq : ∀ y ∈ fixedSpace x, q y = 1 → y = u) {ε : Bool} {n : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * (n + 1))
    (hcs : cs q = if ε then 2 ^ (n + 1) else -2 ^ (n + 1)) :
    p ∣ (if ε then 2 ^ n - 1 else 2 ^ n + 1) := by
  classical
  set U := fixedSpace x with hUdef
  have hnd := polarNondegOn_fixedSpace hx
  set R := polarPerp q U with hR
  have hc : IsCompl U R := isCompl_polarPerp hnd
  have hcsU : cs (q.restrict U) = 2 := cs_restrict_eq_two hU hu hu1 huniq
  have hfrR : finrank (ZMod 2) R = 2 * n := by
    have := Submodule.finrank_add_eq_of_isCompl hc
    omega
  have hcsR : cs (q.restrict R) = if ε then 2 ^ n else -2 ^ n := by
    have h := cs_perpSplit hnd
    rw [hcsU, hcs] at h
    cases ε
    · simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      rw [pow_succ] at h
      linarith
    · simp only [↓reduceIte] at h ⊢
      rw [pow_succ] at h
      linarith
  have hxR : ∀ r ∈ R, x r ∈ R := by
    intro r hr w hw
    rw [← mem_fixedSpace.mp hw, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hx.mem]
    exact hr w hw
  have hxR' : ∀ r ∈ R, x.symm r ∈ R := by
    intro r hr w hw
    rw [← hx.polar_apply, mem_fixedSpace.mp hw]
    exact hr w hw
  let T : R ≃ₗ[ZMod 2] R := restrictEquiv R x hxR hxR'
  have hTpow : ∀ (k : ℕ) (v : R), ((T ^ k) v : V) = (x ^ k) v := by
    intro k
    induction k with
    | zero => intro v; rfl
    | succ k ih =>
      intro v
      rw [pow_succ, LinearEquiv.mul_apply, ih, pow_succ, LinearEquiv.mul_apply]
      rfl
  refine dvd_of_fpf_of_cs hfrR hcsR hp T
    (fun v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hx.mem (v : V)) ?_ ?_
  · refine LinearEquiv.ext fun v => Subtype.ext ?_
    rw [hTpow, hx.pow_eq_one]
    rfl
  · intro v hv
    have h1 : (v : V) ∈ U := mem_fixedSpace.mpr (congrArg Subtype.val hv)
    exact Subtype.ext (Submodule.disjoint_def.mp hc.disjoint _ h1 v.2)

@[expose] def polarLeft (q : QuadraticForm (ZMod 2) V) (u : V) : V →ₗ[ZMod 2] ZMod 2 where
  toFun y := polar q y u
  map_add' a b := polar_add_left q a b u
  map_smul' c a := by simp [polar_smul_left q]

end Abstract

theorem regular_quadPlus (n : ℕ) : ∀ v : Fin n ⊕ Fin n → ZMod 2,
    (∀ w, polar (CFSG.LieType.Universal.Spin.quadPlus n (ZMod 2)) v w = 0) → v = 0 := by
  have hQ := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus n (ZMod 2)
  intro v hv
  exact hQ.1 v fun y => by simpa using hv y

theorem regular_quadMinus (n : ℕ) : ∀ v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ZMod 2,
    (∀ w, polar (CFSG.LieType.Universal.Spin.quadMinus n (ZMod 2) 1 1) v w = 0) → v = 0 := by
  have hQ := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite n (ZMod 2)
    (b := 1) (c := 1) (by decide)
  intro v hv
  exact hQ.1 v fun y => by simpa using hv y

end OrthOddCent

open Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal OrthOddCent in
theorem orthOddCentCoreStrong_of_regular (q : QuadraticForm (ZMod 2) (ι → ZMod 2))
    (hreg : ∀ v, (∀ w, polar q v w = 0) → v = 0) {ε : Bool} {n : ℕ} (hn : 1 ≤ n)
    (hdim : Fintype.card ι = 2 * (n + 1))
    (hcs : CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.cs q =
      if ε then 2 ^ (n + 1) else -2 ^ (n + 1)) :
    OrthOddCentCoreStrong (⇑q) ε n := by
  intro p hp hp2 d hd _hd1 hdp N hN hNn hN2 hN1
  set e := CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2) with he
  have hmemO : ∀ g : GL ι (ZMod 2),
      g ∈ isoGrp ⇑q ↔ e g ∈ TauCeti.QuadraticMap.orthogonalGroup q := fun g => by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    rfl
  have hmemC : ∀ g : GL ι (ZMod 2), g ∈ Subgroup.centralizer ({d} : Set (GL ι (ZMod 2))) ↔
      e g ∈ Subgroup.centralizer ({e d} : Set ((ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2))) := by
    intro g
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
      ← map_mul, ← map_mul, e.injective.eq_iff]
  have hmemM : ∀ g, g ∈ isoGrp ⇑q ⊓ Subgroup.centralizer ({d} : Set (GL ι (ZMod 2))) ↔
      e g ∈ isometryCentralizer q (e d) := by
    intro g
    rw [Subgroup.mem_inf, hmemO, hmemC]
    rfl
  have hx : OddOrderIsometry q p (e d) :=
    { mem := (hmemO d).mp hd
      pow_eq_one := by rw [← map_pow, hdp, map_one]
      cast_ne_zero := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro h2
        exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
      regular := hreg }
  set N' := N.map e.toMonoidHom with hN'
  have hN'M : N' ≤ isometryCentralizer q (e d) := by
    rintro _ ⟨g, hg, rfl⟩
    exact (hmemM g).mp (hN hg)
  have hN'n : (N'.subgroupOf (isometryCentralizer q (e d))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hN'M]
    rintro _ k ⟨g, hg, rfl⟩ hk
    refine ⟨e.symm k * g * (e.symm k)⁻¹, ?_, by simp⟩
    have hk' : e.symm k ∈ isoGrp ⇑q ⊓ Subgroup.centralizer ({d} : Set (GL ι (ZMod 2))) := by
      rw [hmemM]
      simpa using hk
    exact (Subgroup.normal_subgroupOf_iff hN).mp hNn g _ hg hk'
  have hN'2 : IsPGroup 2 N' := hN2.map _
  have hN'1 : N' ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ e.injective]
    exact hN1
  obtain ⟨hU, u, hu, hu1, huniq, t, htN, htform, hall⟩ :=
    exists_transvection_of_normal hx hp hp2 N' hN'M hN'n hN'2 hN'1
  obtain ⟨t0, ht0N, rfl⟩ := Subgroup.mem_map.mp htN
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu1
  refine ⟨⟨t0, ht0N, ?_, ?_⟩, ?_⟩
  · refine ⟨u, polarLeft q u, hu0, ?_, ?_, fun y => htform y⟩
    · intro hf
      apply hu0
      refine hreg u fun w => ?_
      rw [polar_comm]
      exact LinearMap.congr_fun hf w
    · show polar q u u = 0
      rw [polar_self, two_nsmul]
      exact ZModModule.add_self _
  · apply le_antisymm
    · intro g hg
      rcases hall (e.toMonoidHom g) (Subgroup.mem_map_of_mem _ hg) with h | h
      · rw [show g = 1 from e.injective (by simpa using h)]
        exact one_mem _
      · rw [show g = t0 from e.injective h]
        exact Subgroup.mem_zpowers t0
    · exact Subgroup.zpowers_le.mpr ht0N
  · have hdimV : finrank (ZMod 2) (ι → ZMod 2) = 2 * (n + 1) := by
      rw [Module.finrank_fintype_fun_eq_card, hdim]
    exact CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.exists_hasFixedPointFreeOrder_of_dvd
      hp hp2 hn (dvd_of_hyperbolic_fixedSpace hx hp hU hu hu1 huniq hdimV hcs)

theorem orthOddCentCoreStrong : ∀ n : ℕ, 1 ≤ n →
    OrthOddCentCoreStrong (StatedQuadPlus (n + 1) (ZMod 2)) true n ∧
      OrthOddCentCoreStrong (StatedQuadMinus (n + 1) (ZMod 2) 1 1) false n := by
  intro n hn
  constructor
  · have h := orthOddCentCoreStrong_of_regular
      (CFSG.LieType.Universal.Spin.quadPlus (n + 1) (ZMod 2)) (OrthOddCent.regular_quadPlus (n + 1))
      (ε := true) hn (by simp only [Fintype.card_sum, Fintype.card_fin]; ring)
      (by simpa using CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.cs_quadPlus (n + 1))
    rwa [CFSG.LieType.Universal.Spin.coe_quadPlus] at h
  · have h := orthOddCentCoreStrong_of_regular
      (CFSG.LieType.Universal.Spin.quadMinus (n + 1) (ZMod 2) 1 1)
      (OrthOddCent.regular_quadMinus (n + 1))
      (ε := false) hn (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)
      (by simpa using CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.cs_quadMinus n)
    rwa [CFSG.LieType.Universal.Spin.coe_quadMinus] at h

end CFSG.LieType.ChevTwo
