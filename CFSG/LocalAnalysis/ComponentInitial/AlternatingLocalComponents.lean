module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingLocalBetween
public import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBAlternating

theorem isComponent_le_centralizer_of_isPGroup {H : Type*} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] {K N : Subgroup H} (hK : CFSG.IsComponent K) (hN : N.Normal)
    (hNp : IsPGroup p N) : K ≤ centralizer (N : Set H) := by
  rcases component_normal_subgroup hK hN with h | h
  · have : Group.IsNilpotent N := hNp.isNilpotent
    exact absurd h (not_le_of_isComponent_of_isSolvable hK inferInstance)
  · exact commutator_eq_bot_iff_le_centralizer.1 h

variable {Ω : Type*}

theorem perfect_normalizer_fixedSupport [Finite Ω] {p : ℕ} [Fact p.Prime]
    {P : Subgroup (Equiv.Perm Ω)} (hP : IsPGroup p P)
    {L : Subgroup (normalizer (P : Set (Equiv.Perm Ω)))} [Group.IsPerfect L]
    (hLP : L ≤ centralizer (P.subgroupOf (normalizer (P : Set (Equiv.Perm Ω))) : Set _))
    (hLU : L ≤ centralizer (normalizerOrbitKernel P : Set _)) (c : L) {x : Ω}
    (hx : x ∉ MulAction.fixedPoints P Ω) : c.val.val x = x := by
  have hequiv : ∀ d : L, d.val.val ∈ equivariantSubgroup P Ω := fun d => by
    rw [equivariantSubgroup_eq_centralizer]
    refine mem_centralizer_iff.2 fun g hg => ?_
    exact congrArg Subtype.val (mem_centralizer_iff.1 (hLP d.2) ⟨g, P.le_normalizer hg⟩ hg)
  let o : MulAction.orbitRel.Quotient P Ω := Quotient.mk'' x
  have hxo : x ∈ o.orbit := MulAction.orbitRel.Quotient.mem_orbit.mpr rfl
  have hnot : ¬∀ g : P, g • x = x := fun h => hx (MulAction.mem_fixedPoints.mpr h)
  obtain ⟨g, hg⟩ := not_forall.mp hnot
  have : Nontrivial o.orbit := nontrivial_of_ne
    (⟨g • x, o.mapsTo_smul_orbit g hxo⟩ : o.orbit) ⟨x, hxo⟩
    (fun h => hg (congrArg Subtype.val h))
  have hpreserves : ∀ d : L, ∀ y : Ω, d.val.val y ∈ o.orbit ↔ y ∈ o.orbit := by
    intro d y
    constructor
    · intro hy
      have hinv := normalizerOrbitKernel_centralizer_preserves p P hP d.val⁻¹
        (hLU (L.inv_mem d.property)) o (d.val.val y) hy
      change d.val.val.symm (d.val.val y) ∈ o.orbit at hinv
      simpa only [Equiv.symm_apply_apply] using hinv
    · exact normalizerOrbitKernel_centralizer_preserves p P hP d.val (hLU d.property) o y
  let f : L →* equivariantSubgroup P o.orbit :=
    { toFun d := ⟨d.val.val.subtypePerm (hpreserves d), by
        apply (mem_equivariantSubgroup _).mpr
        intro a y
        apply Subtype.ext
        exact (mem_equivariantSubgroup _).mp (hequiv d) a y.val⟩
      map_one' := Subtype.ext (Equiv.ext fun _ => rfl)
      map_mul' _ _ := Subtype.ext (Equiv.ext fun _ => rfl) }
  have : Group.IsNilpotent (equivariantSubgroup P o.orbit) :=
    (transitive_equivariant_isPGroup p hP ⟨x, hxo⟩).isNilpotent
  have hf : f = 1 := SolvableKernelContainment.hom_eq_one f
  exact congrArg (fun d : equivariantSubgroup P o.orbit => (d.val ⟨x, hxo⟩).val)
    (DFunLike.congr_fun hf c)

theorem ofSubtype_mem_centralizer_of_fixedPoints (P : Subgroup (Equiv.Perm Ω))
    [DecidablePred (· ∈ MulAction.fixedPoints P Ω)]
    (f : Equiv.Perm (MulAction.fixedPoints P Ω)) :
    Equiv.Perm.ofSubtype f ∈ centralizer (P : Set (Equiv.Perm Ω)) := by
  refine mem_centralizer_iff.2 fun g hg => Equiv.ext fun x => ?_
  change g (Equiv.Perm.ofSubtype f x) = Equiv.Perm.ofSubtype f (g x)
  by_cases hx : x ∈ MulAction.fixedPoints P Ω
  · have hgx : g x = x := MulAction.mem_fixedPoints.mp hx (⟨g, hg⟩ : P)
    rw [hgx, Equiv.Perm.ofSubtype_apply_of_mem _ hx]
    exact MulAction.mem_fixedPoints.mp (f ⟨x, hx⟩).property (⟨g, hg⟩ : P)
  · have hgx : g x ∉ MulAction.fixedPoints P Ω := by
      intro h
      have hfix := MulAction.mem_fixedPoints.mp h (⟨g⁻¹, P.inv_mem hg⟩ : P)
      change g.symm (g x) = g x at hfix
      rw [Equiv.symm_apply_apply] at hfix
      exact hx (hfix.symm ▸ h)
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hx, Equiv.Perm.ofSubtype_apply_of_not_mem _ hgx]

open scoped Classical in
theorem ordinary_permutation_local_component_fixed_support [Fintype Ω] [DecidableEq Ω]
    {T : Subgroup (Equiv.Perm Ω)} (hT : alternatingGroup Ω ≤ T) {p : ℕ} (hp : p.Prime)
    {P : Subgroup (Equiv.Perm Ω)} (_hPT : P ≤ T) (hP : IsPGroup p P)
    {K : Subgroup (Equiv.Perm Ω)}
    (hK : CFSG.Assembly.IsComponentOf K (T ⊓ normalizer (P : Set (Equiv.Perm Ω)))) :
    5 ≤ Nat.card (MulAction.fixedPoints P Ω) ∧
      K = (alternatingGroup (MulAction.fixedPoints P Ω)).map Equiv.Perm.ofSubtype := by
  have : Fact p.Prime := ⟨hp⟩
  set N := normalizer (P : Set (Equiv.Perm Ω))
  set F := MulAction.fixedPoints P Ω
  have hKN : CFSG.Assembly.IsComponentOf K N := by
    refine ⟨hK.1.trans inf_le_right, assembly_isSubnormal_trans hK.2.1
      (CFSG.Assembly.IsSubnormal.step inf_le_right ?_ (CFSG.Assembly.IsSubnormal.refl N)),
      hK.2.2⟩
    rw [inf_subgroupOf_right]
    exact (between_alternating_normal T hT).subgroupOf N
  have hK' : CFSG.IsComponent (K.subgroupOf N) :=
    (isComponentOf_iff_isComponent_subgroupOf hKN.1).1 hKN
  have : Group.IsPerfect (K.subgroupOf N) := hK'.1.1
  have hLP := isComponent_le_centralizer_of_isPGroup hK' normal_in_normalizer hP.comap_subtype
  have hLU := isComponent_le_centralizer_of_isPGroup hK' (normalizerOrbitKernel_normal P)
    (normalizerOrbitKernel_isPGroup p P hP)
  have hsupport : ∀ c ∈ K, ∀ x ∉ F, c x = x := fun c hc x hx =>
    perfect_normalizer_fixedSupport hP hLP hLU ⟨⟨c, hKN.1 hc⟩, hc⟩ hx
  let φ : Equiv.Perm F →* N := MonoidHom.codRestrict
    (Equiv.Perm.ofSubtype : Equiv.Perm F →* Equiv.Perm Ω) N fun f =>
      centralizer_le_normalizer _ (ofSubtype_mem_centralizer_of_fixedPoints P f)
  have hφ : Function.Injective φ := fun f g h =>
    Equiv.Perm.ofSubtype_injective (congrArg Subtype.val h)
  have hrange : K.subgroupOf N ≤ φ.range := by
    intro c hc
    have hc' : (c : Equiv.Perm Ω) ∈ K := hc
    have hpres : ∀ x, (c : Equiv.Perm Ω) x ∈ F ↔ x ∈ F := fun x => by
      constructor
      · intro h
        by_contra hx
        exact hx (hsupport _ hc' x hx ▸ h)
      · intro hx
        by_contra h
        exact h (((c : Equiv.Perm Ω).injective (hsupport _ hc' _ h)).symm ▸ hx)
    exact ⟨(c : Equiv.Perm Ω).subtypePerm hpres, Subtype.ext
      (Equiv.Perm.ofSubtype_subtypePerm hpres fun x h =>
        by_contra fun hx => h (hsupport _ hc' x hx))⟩
  set J := (K.subgroupOf N).comap φ
  have hJmap : J.map φ = K.subgroupOf N := map_comap_eq_self hrange
  let e : J ≃* K.subgroupOf N :=
    (J.equivMapOfInjective φ hφ).trans (MulEquiv.subgroupCongr hJmap)
  have : Group.IsPerfect J :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have : Nontrivial (K.subgroupOf N) := CFSG.LocalCores.isQuasisimple_nontrivial hK'.1
  have : Nontrivial J := e.toEquiv.nontrivial
  obtain ⟨hdeg, hJalt⟩ := symmetric_perfect_subnormal J (hK'.2.comap φ)
  refine ⟨hdeg, ?_⟩
  have hKeq : K = (J.map φ).map N.subtype := by rw [hJmap, map_subgroupOf_eq_of_le hKN.1]
  rw [hKeq, map_map, hJalt]
  rfl

theorem centralizer_singleton_eq_normalizer_zpowers {G : Type*} [Group G] {x : G}
    (hx : orderOf x = 2) : centralizer ({x} : Set G) = normalizer (zpowers x : Set G) := by
  apply le_antisymm
  · rw [← centralizer_closure, ← zpowers_eq_closure]
    exact centralizer_le_normalizer _
  · intro g hg
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 ((mem_normalizer_iff.1 hg x).1 (mem_zpowers x))
    rw [← zpow_mod_orderOf, hx, Nat.cast_ofNat] at hk
    rw [mem_centralizer_singleton_iff]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · rw [h, zpow_zero] at hk
      have hx1 : x = 1 := conj_eq_one_iff.1 hk.symm
      rw [hx1, orderOf_one] at hx
      exact absurd hx (by decide)
    · rw [h, zpow_one] at hk
      calc g * x = g * x * g⁻¹ * g := by group
        _ = x * g := by rw [← hk]

theorem mem_fixedPoints_zpowers_iff {x : Equiv.Perm Ω} {ω : Ω} :
    ω ∈ MulAction.fixedPoints (zpowers x) Ω ↔ x ω = ω := by
  rw [MulAction.mem_fixedPoints]
  constructor
  · intro h
    exact h ⟨x, mem_zpowers x⟩
  · rintro h ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self h k

theorem isPGroup_zpowers_of_orderOf_eq_two {G : Type*} [Group G] {x : G} (hx : orderOf x = 2) :
    IsPGroup 2 (zpowers x) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])

theorem exists_two_ne_of_three_le_card {α : Type*} [Finite α] (h : 3 ≤ Nat.card α) (u : α) :
    ∃ v w : α, v ≠ u ∧ w ≠ u ∧ v ≠ w := by
  classical
  have := Fintype.ofFinite α
  have hcard : 1 < (Finset.univ.erase u).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨v, hv, w, hw, hvw⟩ := Finset.one_lt_card.1 hcard
  exact ⟨v, w, Finset.ne_of_mem_erase hv, Finset.ne_of_mem_erase hw, hvw⟩

variable [DecidableEq Ω]

theorem swap_mul_swap_mem_alternatingGroup_map {S : Set Ω} [Fintype S] [DecidablePred (· ∈ S)]
    {a b c d : S} (hab : a ≠ b) (hcd : c ≠ d) :
    Equiv.swap (a : Ω) b * Equiv.swap (c : Ω) d ∈
      (alternatingGroup S).map Equiv.Perm.ofSubtype := by
  refine ⟨Equiv.swap a b * Equiv.swap c d, ?_, ?_⟩
  · rw [SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap hab,
      Equiv.Perm.sign_swap hcd]
    decide
  · rw [map_mul, Equiv.Perm.ofSubtype_swap_eq, Equiv.Perm.ofSubtype_swap_eq]

theorem orderOf_swap_mul_swap {a b c d : Ω} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    orderOf (Equiv.swap a b * Equiv.swap c d) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · have hcomm : Commute (Equiv.swap a b) (Equiv.swap c d) := by
      refine Equiv.Perm.Disjoint.commute fun z => ?_
      by_cases hza : z = a
      · subst hza
        exact Or.inr (Equiv.swap_apply_of_ne_of_ne hac had)
      by_cases hzb : z = b
      · subst hzb
        exact Or.inr (Equiv.swap_apply_of_ne_of_ne hbc hbd)
      exact Or.inl (Equiv.swap_apply_of_ne_of_ne hza hzb)
    rw [hcomm.mul_pow, sq, sq, Equiv.swap_mul_self, Equiv.swap_mul_self, one_mul]
  · intro h
    have h' := congrArg (fun σ : Equiv.Perm Ω => σ a) h
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hac had,
      Equiv.swap_apply_left, Equiv.Perm.one_apply] at h'
    exact hab h'.symm

open scoped Classical in
theorem alternating_commuting_universal_pair_exclusion [Fintype Ω]
    {T : Subgroup (Equiv.Perm Ω)} (hT : alternatingGroup Ω ≤ T) :
    ¬ ∃ K₁ K₂ : Subgroup (Equiv.Perm Ω), K₁ ≤ T ∧ K₂ ≤ T ∧
      CFSG.Assembly.IsQuasisimple K₁ ∧ CFSG.Assembly.IsQuasisimple K₂ ∧
      Even (Nat.card K₁) ∧ Even (Nat.card K₂) ∧ ⁅K₁, K₂⁆ = ⊥ ∧
      (∀ t ∈ K₂, orderOf t = 2 →
        CFSG.Assembly.IsComponentOf K₁ (T ⊓ centralizer ({t} : Set (Equiv.Perm Ω)))) ∧
      (∀ t ∈ K₁, orderOf t = 2 →
        CFSG.Assembly.IsComponentOf K₂ (T ⊓ centralizer ({t} : Set (Equiv.Perm Ω)))) := by
  rintro ⟨K₁, K₂, hK₁T, hK₂T, -, -, -, he₂, hcomm, h₁, h₂⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K₂) 2 (even_iff_two_dvd.1 he₂)
  have hx2 : orderOf (x : Equiv.Perm Ω) = 2 := by rw [Subgroup.orderOf_coe, hx]
  have hc₁ := h₁ x x.2 hx2
  rw [centralizer_singleton_eq_normalizer_zpowers hx2] at hc₁
  obtain ⟨hF, hK₁⟩ := ordinary_permutation_local_component_fixed_support hT Nat.prime_two
    (zpowers_le.2 (hK₂T x.2)) (isPGroup_zpowers_of_orderOf_eq_two hx2) hc₁
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 5)
    (β := MulAction.fixedPoints (zpowers (x : Equiv.Perm Ω)) Ω)
    (by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]; exact hF)
  have hne : ∀ i j : Fin 5, i ≠ j → (e i : Ω) ≠ e j := fun i j hij h =>
    hij (e.injective (Subtype.ext h))
  obtain ⟨y, hy⟩ : ∃ y : Equiv.Perm Ω,
      y = Equiv.swap (e 0 : Ω) (e 1) * Equiv.swap (e 2 : Ω) (e 3) := ⟨_, rfl⟩
  have hyK : y ∈ K₁ := by
    rw [hy, hK₁]
    exact swap_mul_swap_mem_alternatingGroup_map (e.injective.ne (by decide))
      (e.injective.ne (by decide))
  have hy2 : orderOf y = 2 := by
    rw [hy]
    exact orderOf_swap_mul_swap (hne 0 1 (by decide)) (hne 0 2 (by decide))
      (hne 0 3 (by decide)) (hne 1 2 (by decide)) (hne 1 3 (by decide))
  have hc₂ := h₂ y hyK hy2
  rw [centralizer_singleton_eq_normalizer_zpowers hy2] at hc₂
  obtain ⟨hB, hK₂⟩ := ordinary_permutation_local_component_fixed_support hT Nat.prime_two
    (zpowers_le.2 (hK₁T hyK)) (isPGroup_zpowers_of_orderOf_eq_two hy2) hc₂
  have hfB : (e 4 : Ω) ∈ MulAction.fixedPoints (zpowers y) Ω := by
    rw [mem_fixedPoints_zpowers_iff, hy, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (hne 4 2 (by decide)) (hne 4 3 (by decide)),
      Equiv.swap_apply_of_ne_of_ne (hne 4 0 (by decide)) (hne 4 1 (by decide))]
  have haB : (e 0 : Ω) ∉ MulAction.fixedPoints (zpowers y) Ω := by
    rw [mem_fixedPoints_zpowers_iff, hy, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (hne 0 2 (by decide)) (hne 0 3 (by decide)),
      Equiv.swap_apply_left]
    exact hne 1 0 (by decide)
  have hbB : (e 1 : Ω) ∉ MulAction.fixedPoints (zpowers y) Ω := by
    rw [mem_fixedPoints_zpowers_iff, hy, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (hne 1 2 (by decide)) (hne 1 3 (by decide)),
      Equiv.swap_apply_right]
    exact hne 0 1 (by decide)
  obtain ⟨u, v, hu, hv, huv⟩ := exists_two_ne_of_three_le_card (le_trans (by norm_num) hB)
    (⟨e 4, hfB⟩ : MulAction.fixedPoints (zpowers y) Ω)
  have hσ : Equiv.swap (e 4 : Ω) (e 1) * Equiv.swap (e 4 : Ω) (e 0) ∈ K₁ := by
    rw [hK₁]
    exact swap_mul_swap_mem_alternatingGroup_map (e.injective.ne (by decide))
      (e.injective.ne (by decide))
  have hτ : Equiv.swap (e 4 : Ω) u * Equiv.swap (e 4 : Ω) v ∈ K₂ := by
    have h := swap_mul_swap_mem_alternatingGroup_map
      (a := (⟨e 4, hfB⟩ : MulAction.fixedPoints (zpowers y) Ω))
      (c := (⟨e 4, hfB⟩ : MulAction.fixedPoints (zpowers y) Ω)) hu.symm hv.symm
    rwa [← hK₂] at h
  have hv0 : (v : Ω) ≠ e 0 := fun h => haB (h ▸ v.2)
  have hv1 : (v : Ω) ≠ e 1 := fun h => hbB (h ▸ v.2)
  have hu0 : (u : Ω) ≠ e 0 := fun h => haB (h ▸ u.2)
  have hv4 : (v : Ω) ≠ e 4 := fun h => hv (Subtype.ext h)
  have huv' : (u : Ω) ≠ v := fun h => huv (Subtype.ext h)
  have hc := mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hcomm hσ) _ hτ
  have key := congrArg (fun ρ : Equiv.Perm Ω => ρ (e 4)) hc
  simp only [Equiv.Perm.mul_apply] at key
  rw [Equiv.swap_apply_left (e 4 : Ω) (e 0 : Ω),
    Equiv.swap_apply_of_ne_of_ne (hne 0 4 (by decide)) (hne 0 1 (by decide)),
    Equiv.swap_apply_of_ne_of_ne (hne 0 4 (by decide)) hv0.symm,
    Equiv.swap_apply_of_ne_of_ne (hne 0 4 (by decide)) hu0.symm,
    Equiv.swap_apply_left (e 4 : Ω) (v : Ω), Equiv.swap_apply_of_ne_of_ne hv4 huv'.symm,
    Equiv.swap_apply_of_ne_of_ne hv4 hv0, Equiv.swap_apply_of_ne_of_ne hv4 hv1] at key
  exact hv0 key.symm

end CFSG.LocalAnalysis.ComponentInitial
