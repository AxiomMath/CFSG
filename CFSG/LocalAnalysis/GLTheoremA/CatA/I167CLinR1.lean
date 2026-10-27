module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open

private noncomputable def i167CLin_smallG {F : Type} [Field F] {V : Type} [AddCommGroup V]
    [Module F V] (H : Subgroup (V ≃ₗ[F] V)) {N₁ : Submodule F V}
    (hstab : ∀ h ∈ H, ∀ v ∈ N₁, h v ∈ N₁) : H →* Module.End F N₁ :=
  { toFun := fun h => ((h : V ≃ₗ[F] V) : V →ₗ[F] V).restrict (hstab h h.2)
    map_one' := by ext m; simp
    map_mul' := by intro a b; ext m; simp }

private noncomputable def i167CLin_smallA {F : Type} [Field F] {V : Type} [AddCommGroup V]
    [Module F V] (H : Subgroup (V ≃ₗ[F] V)) {N₁ : Submodule F V}
    (hstab : ∀ h ∈ H, ∀ v ∈ N₁, h v ∈ N₁) : Subalgebra F (Module.End F N₁) :=
  Algebra.adjoin F (Set.range (i167CLin_smallG H hstab))

private lemma i167CLin_stable_small_aux1 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (H : Subgroup (V ≃ₗ[F] V)) {N : Submodule F V} (hN0 : N ≠ ⊥)
    (hN : ∀ h ∈ H, ∀ v ∈ N, h v ∈ N) :
    ∃ N₁ : Submodule F V, N₁ ≤ N ∧ N₁ ≠ ⊥ ∧ (∀ h ∈ H, ∀ v ∈ N₁, h v ∈ N₁) ∧
      (∀ M : Submodule F V, M ≤ N₁ → (∀ h ∈ H, ∀ v ∈ M, h v ∈ M) → M = ⊥ ∨ M = N₁) := by
  classical
  haveI : Module.Finite F V := inferInstance
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Submodule F V) :=
    Finite.of_injective (fun S : Submodule F V => (S : Set V)) SetLike.coe_injective
  let P : Set (Submodule F V) := {M | M ≤ N ∧ M ≠ ⊥ ∧ (∀ h ∈ H, ∀ v ∈ M, h v ∈ M)}
  have hP : (Set.toFinite P).toFinset.Nonempty :=
    ⟨N, (Set.toFinite P).mem_toFinset.mpr ⟨le_rfl, hN0, hN⟩⟩
  obtain ⟨N₁, hN₁P, hmin⟩ := (Set.toFinite P).toFinset.exists_min_image (fun M => Nat.card M) hP
  obtain ⟨hle, hne, hstab⟩ := (Set.toFinite P).mem_toFinset.mp hN₁P
  refine ⟨N₁, hle, hne, hstab, fun M hMle hMstab => ?_⟩
  by_cases hM0 : M = ⊥
  · exact Or.inl hM0
  · right
    have hMP : M ∈ P := ⟨hMle.trans hle, hM0, hMstab⟩
    have hcard := hmin M ((Set.toFinite P).mem_toFinset.mpr hMP)
    have h1 : (M : Set V) = N₁ := Set.eq_of_subset_of_ncard_le hMle (by
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      exact hcard) (Set.toFinite _)
    exact SetLike.coe_injective h1

private def i167CLin_stable_small_aux2 {F : Type} [Field F] {B : Type} [Ring B] [Algebra F B]
    {ζ : B} (hζ : ζ ^ 2 = -ζ - 1) : Subalgebra F B where
  carrier := Submodule.span F ({1, ζ} : Set B)
  one_mem' := Submodule.subset_span (Set.mem_insert _ _)
  mul_mem' := by
    have h1 : (1 : B) ∈ Submodule.span F ({1, ζ} : Set B) :=
      Submodule.subset_span (Set.mem_insert _ _)
    have hζm : ζ ∈ Submodule.span F ({1, ζ} : Set B) :=
      Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    intro a b ha hb
    induction ha using Submodule.span_induction with
    | mem x hx =>
        induction hb using Submodule.span_induction with
        | mem y hy =>
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
            · simpa using h1
            · simpa using hζm
            · simpa using hζm
            · rw [← pow_two, hζ]
              exact Submodule.sub_mem _ (Submodule.neg_mem _ hζm) h1
        | zero => simp
        | add y z hy hz ihy ihz => rw [mul_add]; exact Submodule.add_mem _ ihy ihz
        | smul c y hy ihy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ihy
    | zero => simp
    | add x z hx hz ihx ihz => rw [add_mul]; exact Submodule.add_mem _ ihx ihz
    | smul c x hx ihx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ihx
  add_mem' := by intro a b ha hb; exact Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  algebraMap_mem' := fun c => by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_insert _ _))

private lemma i167CLin_stable_small_aux3 {F : Type} [Field F] {B : Type} [Ring B] [Algebra F B]
    {ζ : B} (hζ : ζ ^ 2 = -ζ - 1) :
    Algebra.adjoin F ({ζ} : Set B) ≤ i167CLin_stable_small_aux2 (F := F) hζ := by
  apply Algebra.adjoin_le
  rintro x rfl
  exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

private lemma i167CLin_stable_small_aux4 {F : Type} [Field F] {B : Type} [Ring B] [Algebra F B]
    {A : Subalgebra F B} (hA : IsField A) {ζ η : A}
    (hζ : ζ ^ 2 + ζ + 1 = 0) (hη3 : η ^ 3 = 1) (hη1 : η ≠ 1) :
    η = ζ ∨ η = ζ ^ 2 := by
  letI : Field A := hA.toField
  have hη : η ^ 2 + η + 1 = 0 := by
    have hfac : (η - 1) * (η ^ 2 + η + 1) = 0 := by
      have : (η - 1) * (η ^ 2 + η + 1) = η ^ 3 - 1 := by ring
      rw [this, hη3, sub_self]
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (sub_eq_zero.mp h) hη1
    · exact h
  have hfac2 : (η - ζ) * (η + ζ + 1) = 0 := by
    have : (η - ζ) * (η + ζ + 1) = (η ^ 2 + η + 1) - (ζ ^ 2 + ζ + 1) := by ring
    rw [this, hη, hζ, sub_self]
  rcases mul_eq_zero.mp hfac2 with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · refine Or.inr ?_
    have h1 : η = -ζ - 1 := by linear_combination h
    have h2 : ζ ^ 2 = -ζ - 1 := by linear_combination hζ
    rw [h1, ← h2]

private lemma i167CLin_stable_small_aux5 {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    {N₁ : Submodule F V} {A : Subalgebra F (Module.End F N₁)} (hA : IsField A)
    {x : A} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) : x ^ 2 + x + 1 = 0 := by
  letI : Field A := hA.toField
  have hfac : (x - 1) * (x ^ 2 + x + 1) = 0 := by
    have : (x - 1) * (x ^ 2 + x + 1) = x ^ 3 - 1 := by ring
    rw [this, hx3, sub_self]
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (sub_eq_zero.mp h) hx1
  · exact h

private lemma i167CLin_stable_small_aux6 {F : Type} [Field F] [Finite F]
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (H : Subgroup (V ≃ₗ[F] V)) {N₁ : Submodule F V}
    (hstab : ∀ h ∈ H, ∀ v ∈ N₁, h v ∈ N₁)
    (hsimple : ∀ M : Submodule F V, M ≤ N₁ → (∀ h ∈ H, ∀ v ∈ M, h v ∈ M) → M = ⊥ ∨ M = N₁) :
    ∀ M : Submodule F N₁,
      (∀ h : H, ∀ v ∈ M, i167CLin_smallG H hstab h v ∈ M) → M = ⊥ ∨ M = ⊤ := by
  intro M hM
  let g := i167CLin_smallG H hstab
  let Mv : Submodule F V := M.map N₁.subtype
  have hMvle : Mv ≤ N₁ := Submodule.map_subtype_le N₁ M
  have hMvstab : ∀ h ∈ H, ∀ v ∈ Mv, h v ∈ Mv := by
    intro h hh v hv
    obtain ⟨m, hm, rfl⟩ := hv
    exact ⟨g ⟨h, hh⟩ m, hM ⟨h, hh⟩ m hm, by simp [g, i167CLin_smallG, LinearMap.restrict_apply]⟩
  rcases hsimple Mv hMvle hMvstab with h | h
  · left
    rw [Submodule.eq_bot_iff]
    intro m hm
    have hmv : (N₁.subtype m : V) ∈ Mv := ⟨m, hm, rfl⟩
    rw [h, Submodule.mem_bot] at hmv
    exact Subtype.ext hmv
  · right
    rw [Submodule.eq_top_iff']
    intro m
    have hmv : (N₁.subtype m : V) ∈ Mv := by rw [h]; exact m.2
    obtain ⟨m', hm', hm'eq⟩ := hmv
    have : m' = m := Subtype.ext hm'eq
    rwa [← this]

private lemma i167CLin_stable_small_aux7b {F : Type} [Field F] [Finite F]
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (H : Subgroup (V ≃ₗ[F] V)) {N₁ : Submodule F V}
    (hstab : ∀ h ∈ H, ∀ v ∈ N₁, h v ∈ N₁)
    (hsimpleN : ∀ M : Submodule F N₁,
      (∀ h : H, ∀ v ∈ M, i167CLin_smallG H hstab h v ∈ M) → M = ⊥ ∨ M = ⊤)
    (hcommA : ∀ a b : i167CLin_smallA H hstab, a * b = b * a) :
    ∀ a : i167CLin_smallA H hstab, a ≠ 0 → Function.Injective (a : Module.End F N₁) := by
  intro a ha
  have hkerstab : ∀ h : H, ∀ v ∈ LinearMap.ker (a : Module.End F N₁),
      i167CLin_smallG H hstab h v ∈ LinearMap.ker (a : Module.End F N₁) := by
    intro h v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have hcomm' : (a : Module.End F N₁) * i167CLin_smallG H hstab h
        = i167CLin_smallG H hstab h * (a : Module.End F N₁) :=
      congrArg Subtype.val (hcommA a ⟨i167CLin_smallG H hstab h,
        Algebra.subset_adjoin (Set.mem_range_self h)⟩)
    calc (a : Module.End F N₁) (i167CLin_smallG H hstab h v)
        = ((a : Module.End F N₁) * i167CLin_smallG H hstab h) v := rfl
      _ = (i167CLin_smallG H hstab h * (a : Module.End F N₁)) v := by rw [hcomm']
      _ = (i167CLin_smallG H hstab h) ((a : Module.End F N₁) v) := rfl
      _ = 0 := by rw [hv, map_zero]
  rcases hsimpleN (LinearMap.ker (a : Module.End F N₁)) hkerstab with h | h
  · exact LinearMap.ker_eq_bot.mp h
  · exfalso
    apply ha
    ext m
    have hm : m ∈ LinearMap.ker (a : Module.End F N₁) := by rw [h]; trivial
    simpa using LinearMap.mem_ker.mp hm

private lemma i167CLin_stable_small_aux7 {F : Type} [Field F] [Finite F]
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (H : Subgroup (V ≃ₗ[F] V)) (hH : IsElemAbelian 3 H) {N₁ : Submodule F V}
    (hne : N₁ ≠ ⊥) (hstab : ∀ h ∈ H, ∀ v ∈ N₁, h v ∈ N₁)
    (hsimpleN : ∀ M : Submodule F N₁,
      (∀ h : H, ∀ v ∈ M, i167CLin_smallG H hstab h v ∈ M) → M = ⊥ ∨ M = ⊤) :
    IsField (i167CLin_smallA H hstab) := by
  classical
  haveI : Module.Finite F V := inferInstance
  haveI : Finite V := Module.finite_of_finite F
  haveI : Nontrivial N₁ := Submodule.nontrivial_iff_ne_bot.mpr hne
  haveI : Finite N₁ := inferInstance
  haveI : Finite (Module.End F N₁) :=
    Finite.of_injective (fun f : Module.End F N₁ => (f : N₁ → N₁))
      (fun a b h => LinearMap.ext (congrFun h))
  let g := i167CLin_smallG H hstab
  let A := i167CLin_smallA H hstab
  have hgencomm : (Set.range g).Pairwise Commute := by
    rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩ -
    show g a * g b = g b * g a
    rw [← map_mul, ← map_mul, hH.1.1.comm a b]
  have hcommA : ∀ a b : A, a * b = b * a := by
    haveI : IsMulCommutative A := Algebra.isMulCommutative_adjoin F hgencomm
    intro a b
    exact IsMulCommutative.is_comm.comm a b
  have hinj := i167CLin_stable_small_aux7b H hstab hsimpleN hcommA
  refine ⟨⟨0, 1, zero_ne_one⟩, hcommA, fun {a} ha => ?_⟩
  have ha0 : (a : Module.End F N₁) ≠ 0 := fun h => ha (Subtype.ext h)
  have hai := hinj a ha
  have hunit : IsUnit (a : Module.End F N₁) :=
    (LinearMap.isUnit_iff_ker_eq_bot _).mpr (LinearMap.ker_eq_bot.mpr hai)
  obtain ⟨u, hu⟩ := hunit
  haveI : Finite (Module.End F N₁)ˣ := Finite.of_injective _ Units.val_injective
  have hpos := orderOf_pos u
  have hpow : (a : Module.End F N₁) ^ orderOf u = 1 := by
    rw [← hu, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  refine ⟨⟨(a : Module.End F N₁) ^ (orderOf u - 1), Subalgebra.pow_mem _ a.2 _⟩, Subtype.ext ?_⟩
  show (a : Module.End F N₁) * (a : Module.End F N₁) ^ (orderOf u - 1) = 1
  rw [← pow_succ', Nat.sub_add_cancel hpos, hpow]

private lemma i167CLin_stable_small_aux9 {F : Type} [Field F] [Finite F]
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (H : Subgroup (V ≃ₗ[F] V)) (hH : IsElemAbelian 3 H) {N₁ : Submodule F V}
    (hstab : ∀ h ∈ H, ∀ v ∈ N₁, h v ∈ N₁)
    (hAfield : IsField (i167CLin_smallA H hstab)) {h₀ : H}
    (hζrel : (⟨i167CLin_smallG H hstab h₀, Algebra.subset_adjoin (Set.mem_range_self h₀)⟩ :
        i167CLin_smallA H hstab) ^ 2 +
      ⟨i167CLin_smallG H hstab h₀, Algebra.subset_adjoin (Set.mem_range_self h₀)⟩ + 1 = 0)
    (hh₀ : i167CLin_smallG H hstab h₀ ≠ 1) :
    ∀ h : H, i167CLin_smallG H hstab h ∈
      Algebra.adjoin F ({i167CLin_smallG H hstab h₀} : Set (Module.End F N₁)) := by
  intro h
  by_cases hh : i167CLin_smallG H hstab h = 1
  · rw [hh]; exact Subalgebra.one_mem _
  · have hη3 : (⟨i167CLin_smallG H hstab h, Algebra.subset_adjoin (Set.mem_range_self h)⟩ :
        i167CLin_smallA H hstab) ^ 3 = 1 := Subtype.ext (by
      rw [Subalgebra.coe_pow, Subalgebra.coe_one]
      rw [show i167CLin_smallG H hstab h ^ 3 = 1 from by
        rw [← map_pow, show h ^ 3 = 1 from Subtype.ext (hH.2 (h : V ≃ₗ[F] V) h.2), map_one]])
    have hη1 : (⟨i167CLin_smallG H hstab h, Algebra.subset_adjoin (Set.mem_range_self h)⟩ :
        i167CLin_smallA H hstab) ≠ 1 := fun hc => hh (Subtype.ext_iff.mp hc)
    rcases i167CLin_stable_small_aux4 hAfield hζrel hη3 hη1 with heq | heq
    · rw [show i167CLin_smallG H hstab h = i167CLin_smallG H hstab h₀ from
          congrArg Subtype.val heq]
      exact Algebra.subset_adjoin (Set.mem_singleton _)
    · rw [show i167CLin_smallG H hstab h = (i167CLin_smallG H hstab h₀) ^ 2 from by
          simpa using congrArg Subtype.val heq]
      exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) 2

private lemma i167CLin_stable_small_aux10 {F : Type} [Field F] [Finite F]
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (H : Subgroup (V ≃ₗ[F] V)) {N₁ : Submodule F V}
    (hstab : ∀ h ∈ H, ∀ v ∈ N₁, h v ∈ N₁) {h₀ : H}
    (hζsq : (i167CLin_smallG H hstab h₀) ^ 2 = -(i167CLin_smallG H hstab h₀) - 1)
    (hgen : ∀ h : H, i167CLin_smallG H hstab h ∈
      Algebra.adjoin F ({i167CLin_smallG H hstab h₀} : Set (Module.End F N₁))) :
    Module.finrank F (i167CLin_smallA H hstab) ≤ 2 := by
  classical
  haveI : Module.Finite F V := inferInstance
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite N₁ := inferInstance
  haveI : Finite (Module.End F N₁) :=
    Finite.of_injective (fun f : Module.End F N₁ => (f : N₁ → N₁))
      (fun a b h => LinearMap.ext (congrFun h))
  let g := i167CLin_smallG H hstab
  let A := i167CLin_smallA H hstab
  have hAle : A ≤ Algebra.adjoin F ({g h₀} : Set (Module.End F N₁)) := by
    change Algebra.adjoin F (Set.range g) ≤ _
    apply Algebra.adjoin_le
    rintro x ⟨h, rfl⟩; exact hgen h
  have hAle2 : A ≤ i167CLin_stable_small_aux2 (F := F) hζsq :=
    hAle.trans (i167CLin_stable_small_aux3 hζsq)
  have hfin : Module.finrank F A ≤
      Module.finrank F (i167CLin_stable_small_aux2 (F := F) hζsq) :=
    Submodule.finrank_mono (show A.toSubmodule ≤
      (i167CLin_stable_small_aux2 (F := F) hζsq).toSubmodule from hAle2)
  haveI : Fintype ({1, g h₀} : Set (Module.End F N₁)) := (Set.toFinite _).fintype
  have hcard : Module.finrank F (i167CLin_stable_small_aux2 (F := F) hζsq) ≤ 2 := by
    have h := finrank_span_le_card (R := F) ({1, g h₀} : Set (Module.End F N₁))
    have h2 : ({1, g h₀} : Set (Module.End F N₁)).toFinset.card ≤ 2 := by
      rw [Set.toFinset_insert, Set.toFinset_singleton]
      exact le_trans (Finset.card_insert_le _ _) (by norm_num)
    exact le_trans h h2
  exact le_trans hfin hcard

private lemma i167CLin_stable_small_aux8 {F : Type} [Field F] [Finite F]
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (H : Subgroup (V ≃ₗ[F] V)) (hH : IsElemAbelian 3 H) {N₁ : Submodule F V}
    (hne : N₁ ≠ ⊥) (hstab : ∀ h ∈ H, ∀ v ∈ N₁, h v ∈ N₁)
    (hAfield : IsField (i167CLin_smallA H hstab)) :
    Module.finrank F (i167CLin_smallA H hstab) ≤ 2 := by
  classical
  haveI : Module.Finite F V := inferInstance
  haveI : Finite V := Module.finite_of_finite F
  haveI : Nontrivial N₁ := Submodule.nontrivial_iff_ne_bot.mpr hne
  haveI : Finite N₁ := inferInstance
  haveI : Nontrivial (Module.End F N₁) :=
    ⟨⟨0, 1, fun h => by
      obtain ⟨w, hw⟩ := exists_ne (0 : N₁)
      exact hw (by simpa using (congrFun (congrArg DFunLike.coe h) w).symm)⟩⟩
  let g := i167CLin_smallG H hstab
  let A := i167CLin_smallA H hstab
  have hAfield' : IsField A := hAfield
  letI : Field A := hAfield'.toField
  by_cases htriv : ∀ h : H, g h = 1
  · have hAeq : i167CLin_smallA H hstab = ⊥ := by
      apply le_antisymm _ bot_le
      change Algebra.adjoin F (Set.range g) ≤ (⊥ : Subalgebra F (Module.End F N₁))
      apply Algebra.adjoin_le
      rintro x ⟨h, rfl⟩; rw [htriv h]; exact Subalgebra.one_mem _
    rw [hAeq, Subalgebra.finrank_bot]
    norm_num
  · push Not at htriv
    obtain ⟨h₀, hh₀⟩ := htriv
    let ζ : A := ⟨g h₀, Algebra.subset_adjoin (Set.mem_range_self h₀)⟩
    have hζ3 : ζ ^ 3 = 1 := Subtype.ext (by
      rw [Subalgebra.coe_pow, Subalgebra.coe_one]
      rw [show g h₀ ^ 3 = 1 from by
        rw [← map_pow, show h₀ ^ 3 = 1 from Subtype.ext (hH.2 (h₀ : V ≃ₗ[F] V) h₀.2), map_one]])
    have hζ1 : ζ ≠ 1 := fun hc => hh₀ (Subtype.ext_iff.mp hc)
    have hζrel : ζ ^ 2 + ζ + 1 = 0 := i167CLin_stable_small_aux5 hAfield' hζ3 hζ1
    have hζsq : (g h₀) ^ 2 = -(g h₀) - 1 := by
      have : ζ ^ 2 = -ζ - 1 := by linear_combination hζrel
      simpa [ζ] using congrArg Subtype.val this
    have hgen := i167CLin_stable_small_aux9 H hH hstab hAfield' hζrel hh₀
    exact i167CLin_stable_small_aux10 H hstab hζsq hgen

theorem i167CLin_stable_small {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (H : Subgroup (V ≃ₗ[F] V)) (hH : IsElemAbelian 3 H) {N : Submodule F V} (hN0 : N ≠ ⊥)
    (hN : ∀ h ∈ H, ∀ v ∈ N, h v ∈ N) :
    ∃ N₁ : Submodule F V, N₁ ≤ N ∧ N₁ ≠ ⊥ ∧ (∀ h ∈ H, ∀ v ∈ N₁, h v ∈ N₁) ∧ Module.finrank F N₁ ≤ 2 := by
  classical
  haveI : Module.Finite F V := inferInstance
  haveI : Finite V := Module.finite_of_finite F
  obtain ⟨N₁, hle, hne, hstab, hsimple⟩ := i167CLin_stable_small_aux1 hF H hN0 hN
  haveI : Nontrivial N₁ := Submodule.nontrivial_iff_ne_bot.mpr hne
  haveI : Finite N₁ := inferInstance
  haveI : Finite (Module.End F N₁) :=
    Finite.of_injective (fun f : Module.End F N₁ => (f : N₁ → N₁))
      (fun a b h => LinearMap.ext (congrFun h))
  have hsimpleN := i167CLin_stable_small_aux6 H hstab hsimple
  have hAfield := i167CLin_stable_small_aux7 H hH hne hstab hsimpleN
  let g : H →* Module.End F N₁ := i167CLin_smallG H hstab
  let A : Subalgebra F (Module.End F N₁) := i167CLin_smallA H hstab
  have hgA : ∀ h : H, g h ∈ A := fun h => Algebra.subset_adjoin (Set.mem_range_self h)
  obtain ⟨v, hv⟩ : ∃ v : N₁, v ≠ 0 := by
    by_contra h
    push Not at h
    exact hne ((Submodule.eq_bot_iff N₁).mpr fun m hm => congrArg Subtype.val (h ⟨m, hm⟩))
  let φ : A →ₗ[F] N₁ :=
    { toFun := fun a => (a : Module.End F N₁) v
      map_add' := by intro a b; simp
      map_smul' := by intro c a; simp }
  have hφsurj : Function.Surjective φ := by
    have hrange_stab : ∀ h : H, ∀ w ∈ LinearMap.range φ, g h w ∈ LinearMap.range φ := by
      intro h w hw
      obtain ⟨a, rfl⟩ := hw
      refine ⟨⟨g h, hgA h⟩ * a, ?_⟩
      simp [φ, Module.End.mul_apply]
    have hne' : LinearMap.range φ ≠ ⊥ := by
      intro h
      have : φ 1 ∈ (⊥ : Submodule F N₁) := by rw [← h]; exact LinearMap.mem_range_self _ _
      rw [Submodule.mem_bot] at this
      exact hv (by simpa [φ] using this)
    rcases hsimpleN (LinearMap.range φ) hrange_stab with h | h
    · exact absurd h hne'
    · intro w
      have : w ∈ LinearMap.range φ := by rw [h]; trivial
      exact this
  have hfr_le : Module.finrank F N₁ ≤ Module.finrank F A :=
    LinearMap.finrank_le_finrank_of_surjective hφsurj
  have hA2 : Module.finrank F A ≤ 2 := i167CLin_stable_small_aux8 H hH hne hstab hAfield
  exact ⟨N₁, hle, hne, hstab, le_trans hfr_le hA2⟩

private lemma i167CLin_stable_complement_aux1 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (H : Subgroup (V ≃ₗ[F] V)) (hH : IsElemAbelian 3 H) : (Nat.card H : F) = 1 := by
  haveI : Module.Finite F V := inferInstance
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) :=
    Finite.of_injective (fun f : V ≃ₗ[F] V => (f : V → V)) (fun a b h => by
      ext v; exact congrFun h v)
  haveI : CharP F 2 := by
    haveI : Fintype F := Fintype.ofFinite F
    refine charP_of_card_eq_prime (p := 2) ?_
    rw [Fintype.card_eq_nat_card]; exact hF
  obtain ⟨k, hk⟩ := CFSG.LocalAnalysis.GLTheoremA.exists_card_eq_pow_of_isElemAbelian
    (G := V ≃ₗ[F] V) Nat.prime_three hH
  rw [hk, Nat.cast_pow]
  have h3 : ((3 : ℕ) : F) = 1 := by
    have h2 : ((2 : ℕ) : F) = 0 := CharP.cast_eq_zero F 2
    have : ((3 : ℕ) : F) = ((2 : ℕ) : F) + 1 := by norm_num
    rw [this, h2, zero_add]
  rw [h3, one_pow]

private lemma i167CLin_stable_complement_aux3 {F : Type} [Field F]
    {V : Type} [AddCommGroup V] [Module F V]
    (H : Subgroup (V ≃ₗ[F] V)) {N : Submodule F V}
    {P : Module.End F V} (hP1 : ∀ v, P v ∈ N) (hP2 : ∀ u ∈ N, P u = u)
    (hP3 : ∀ g : H, ((g : V ≃ₗ[F] V) : V →ₗ[F] V) * P = P * ((g : V ≃ₗ[F] V) : V →ₗ[F] V)) :
    ∃ N' : Submodule F V, IsCompl N N' ∧ ∀ h ∈ H, ∀ v ∈ N', h v ∈ N' := by
  let f : V →ₗ[F] N := P.codRestrict N hP1
  have hf : ∀ x : N, f x = x := fun x => Subtype.ext (hP2 x x.2)
  refine ⟨LinearMap.ker f, LinearMap.isCompl_of_proj hf, ?_⟩
  intro m hm u hu
  have hPu : P u = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hu)
  have hcomm : P (m u) = m (P u) :=
    congrArg (fun y => y u) (hP3 ⟨m, hm⟩).symm
  refine LinearMap.mem_ker.mpr (Subtype.ext ?_)
  change P (m u) = 0
  rw [hcomm, hPu, map_zero]

private lemma i167CLin_stable_complement_aux2 {F : Type} [Field F] [Finite F]
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (H : Subgroup (V ≃ₗ[F] V)) {N : Submodule F V}
    (hN : ∀ h ∈ H, ∀ v ∈ N, h v ∈ N) (hcard : (Nat.card H : F) = 1) :
    ∃ N' : Submodule F V, IsCompl N N' ∧ ∀ h ∈ H, ∀ v ∈ N', h v ∈ N' := by
  classical
  haveI : Module.Finite F V := inferInstance
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) :=
    Finite.of_injective (fun f : V ≃ₗ[F] V => (f : V → V)) (fun a b h => by
      ext v; exact congrFun h v)
  haveI : Fintype H := Fintype.ofFinite H
  let ρ : H →* Module.End F V :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := F)).comp H.subtype
  obtain ⟨π₀, hπ₀⟩ := LinearMap.exists_leftInverse_of_injective N.subtype (by simp)
  let X : Module.End F V := N.subtype ∘ₗ π₀
  let P : Module.End F V := ∑ h : H, ρ h * X * ρ h⁻¹
  have hXU : ∀ v, X v ∈ N := fun v => (π₀ v).2
  have hXu : ∀ u ∈ N, X u = u := fun u hu => by
    have := congrArg Subtype.val (LinearMap.congr_fun hπ₀ ⟨u, hu⟩)
    simpa [X] using this
  have hP1 : ∀ v, P v ∈ N := by
    intro v
    simp only [P, LinearMap.sum_apply, Module.End.mul_apply]
    exact N.sum_mem fun h _ => hN h h.2 _ (hXU _)
  have hP2 : ∀ u ∈ N, P u = u := by
    intro u hu
    simp only [P, LinearMap.sum_apply, Module.End.mul_apply]
    have hterm : ∀ h : H, ρ h (X (ρ h⁻¹ u)) = u := by
      intro h
      have hm : ρ h⁻¹ u ∈ N := hN h⁻¹ (H.inv_mem h.2) u hu
      rw [hXu _ hm]
      simp
    simp only [hterm, Finset.sum_const, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul F, hcard, one_smul]
  have hP3 : ∀ g : H, ρ g * P = P * ρ g := by
    intro g
    simp only [P, Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ ?_
    intro h
    simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, mul_assoc, map_inv, mul_inv_rev]
    have h1 : ρ g⁻¹ * ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    rw [h1, mul_one]
  exact i167CLin_stable_complement_aux3 H hP1 hP2 hP3

theorem i167CLin_stable_complement {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (H : Subgroup (V ≃ₗ[F] V)) (hH : IsElemAbelian 3 H) {N : Submodule F V}
    (hN : ∀ h ∈ H, ∀ v ∈ N, h v ∈ N) :
    ∃ N' : Submodule F V, IsCompl N N' ∧ ∀ h ∈ H, ∀ v ∈ N', h v ∈ N' :=
  i167CLin_stable_complement_aux2 H hN (i167CLin_stable_complement_aux1 hF H hH)

variable {F : Type} [Field F] [Finite F]
variable {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

private theorem i167CLin_r_one_module_aux2 (hF : Nat.card F = 2) (v : V) : v + v = 0 := by
  letI : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card]; exact hF
  haveI : CharP F 2 := charP_of_card_eq_prime hcard
  rw [← two_smul F v, CharTwo.two_eq_zero, zero_smul]

private theorem i167CLin_r_one_module_aux3 (hF : Nat.card F = 2) :
    IsCoprime (Polynomial.X - Polynomial.C 1 : Polynomial F)
      (Polynomial.X ^ 2 + Polynomial.X + 1) := by
  letI : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card]; exact hF
  haveI : CharP F 2 := charP_of_card_eq_prime hcard
  refine ⟨Polynomial.X, 1, ?_⟩
  have h2 : (2 : Polynomial F) = 0 := CharTwo.two_eq_zero
  have key : Polynomial.X * (Polynomial.X - Polynomial.C 1) +
      1 * (Polynomial.X ^ 2 + Polynomial.X + 1)
      = (2 : Polynomial F) * Polynomial.X ^ 2 + 1 := by
    rw [Polynomial.C_1]; ring
  rw [key, h2, zero_mul, zero_add]

private theorem i167CLin_r_one_module_aux4 (hF : Nat.card F = 2) {g : V ≃ₗ[F] V} (hg3 : g ^ 3 = 1) :
    IsCompl (LinearMap.ker ((g : V →ₗ[F] V) - (1 : V →ₗ[F] V)))
      (LinearMap.ker ((g : V →ₗ[F] V) ^ 2 + (g : V →ₗ[F] V) + (1 : V →ₗ[F] V))) := by
  letI : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card]; exact hF
  haveI : CharP F 2 := charP_of_card_eq_prime hcard
  set f : V →ₗ[F] V := (g : V →ₗ[F] V)
  have hf3 : f ^ 3 = 1 := by
    have h : (↑(g ^ 3) : V →ₗ[F] V) = (↑(1 : V ≃ₗ[F] V) : V →ₗ[F] V) := by rw [hg3]
    have h1 : (↑(g ^ 3) : V →ₗ[F] V) = f ^ 3 := by
      simp [f, pow_succ, LinearEquiv.coe_toLinearMap_mul]
    rwa [h1] at h
  have h1 : Polynomial.aeval f (Polynomial.X - Polynomial.C 1 : Polynomial F) =
      f - (1 : V →ₗ[F] V) := by
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, map_one]
  have h2 : Polynomial.aeval f (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial F) =
      f ^ 2 + f + (1 : V →ₗ[F] V) := by
    rw [map_add, map_add, map_pow, Polynomial.aeval_X, map_one]
  have hdisj : Disjoint (LinearMap.ker (f - (1 : V →ₗ[F] V)))
      (LinearMap.ker (f ^ 2 + f + (1 : V →ₗ[F] V))) := by
    have h := Polynomial.disjoint_ker_aeval_of_isCoprime f (i167CLin_r_one_module_aux3 hF)
    rwa [h1, h2] at h
  have hsup : LinearMap.ker (f - (1 : V →ₗ[F] V)) ⊔
      LinearMap.ker (f ^ 2 + f + (1 : V →ₗ[F] V)) = ⊤ := by
    have h := Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime f
      (i167CLin_r_one_module_aux3 hF)
    rw [h1, h2] at h
    rw [h]
    have hzero : Polynomial.aeval f ((Polynomial.X - Polynomial.C 1) *
        (Polynomial.X ^ 2 + Polynomial.X + 1) : Polynomial F) = 0 := by
      rw [Polynomial.aeval_mul, h1, h2]
      have : (f - (1 : V →ₗ[F] V)) * (f ^ 2 + f + (1 : V →ₗ[F] V)) =
          f ^ 3 - (1 : V →ₗ[F] V) := by noncomm_ring
      rw [this, hf3, sub_self]
    rw [hzero]
    simp
  exact isCompl_iff.mpr ⟨hdisj, codisjoint_iff.mpr hsup⟩

private theorem i167CLin_r_one_module_aux5 {H : Subgroup (V ≃ₗ[F] V)} (hH : IsElemAbelian 3 H)
    {g a : V ≃ₗ[F] V} (hgH : g ∈ H) (ha : a ∈ H) : a * g = g * a := by
  have h := hH.1.is_comm.comm ⟨a, ha⟩ ⟨g, hgH⟩
  simpa using congrArg Subtype.val h

private theorem i167CLin_r_one_module_aux6 {H : Subgroup (V ≃ₗ[F] V)} (hH : IsElemAbelian 3 H)
    {g : V ≃ₗ[F] V} (hgH : g ∈ H) {a : V ≃ₗ[F] V} (ha : a ∈ H) {v : V}
    (hv : v ∈ LinearMap.ker ((g : V →ₗ[F] V) - (1 : V →ₗ[F] V))) :
    a v ∈ LinearMap.ker ((g : V →ₗ[F] V) - (1 : V →ₗ[F] V)) := by
  have hcomm : a * g = g * a := i167CLin_r_one_module_aux5 hH hgH ha
  have hv' : g v = v := by
    have h := hv
    rw [LinearMap.mem_ker] at h
    simpa [sub_eq_zero] using h
  rw [LinearMap.mem_ker]
  change g (a v) - a v = 0
  rw [sub_eq_zero]
  calc g (a v) = (g * a) v := rfl
    _ = (a * g) v := by rw [hcomm]
    _ = a (g v) := rfl
    _ = a v := by rw [hv']

private theorem i167CLin_r_one_module_aux7 {H : Subgroup (V ≃ₗ[F] V)} (hH : IsElemAbelian 3 H)
    {g : V ≃ₗ[F] V} (hgH : g ∈ H) {a : V ≃ₗ[F] V} (ha : a ∈ H) {v : V}
    (hv : v ∈ LinearMap.ker ((g : V →ₗ[F] V) ^ 2 + (g : V →ₗ[F] V) + (1 : V →ₗ[F] V))) :
    a v ∈ LinearMap.ker ((g : V →ₗ[F] V) ^ 2 + (g : V →ₗ[F] V) + (1 : V →ₗ[F] V)) := by
  have hcomm : a * g = g * a := i167CLin_r_one_module_aux5 hH hgH ha
  have hv' : ((g : V →ₗ[F] V) ^ 2 + (g : V →ₗ[F] V) + (1 : V →ₗ[F] V)) v = 0 := by
    simpa [LinearMap.mem_ker] using hv
  have happ : ∀ x, (g : V →ₗ[F] V) ((a : V →ₗ[F] V) x) =
      (a : V →ₗ[F] V) ((g : V →ₗ[F] V) x) := by
    intro x
    have h := congrArg (fun e : V ≃ₗ[F] V => e x) hcomm
    simpa [LinearEquiv.mul_apply] using h.symm
  rw [LinearMap.mem_ker]
  calc ((g : V →ₗ[F] V) ^ 2 + (g : V →ₗ[F] V) + (1 : V →ₗ[F] V)) (a v)
      = (g : V →ₗ[F] V) ((g : V →ₗ[F] V) ((a : V →ₗ[F] V) v)) +
          (g : V →ₗ[F] V) ((a : V →ₗ[F] V) v) + a v := rfl
    _ = a ((g : V →ₗ[F] V) ((g : V →ₗ[F] V) v)) + a ((g : V →ₗ[F] V) v) + a v := by
        simp only [happ]
        rfl
    _ = a ((g : V →ₗ[F] V) ((g : V →ₗ[F] V) v) + (g : V →ₗ[F] V) v + v) := by
        rw [map_add, map_add]
    _ = a (((g : V →ₗ[F] V) ^ 2 + (g : V →ₗ[F] V) + (1 : V →ₗ[F] V)) v) := rfl
    _ = 0 := by rw [hv', map_zero]

private theorem i167CLin_r_one_module_aux8 {g : V ≃ₗ[F] V} {v : V}
    (hv : v ∈ LinearMap.ker ((g : V →ₗ[F] V) ^ 2 + (g : V →ₗ[F] V) + (1 : V →ₗ[F] V))) :
    (g : V →ₗ[F] V) v ∈ LinearMap.ker ((g : V →ₗ[F] V) ^ 2 + (g : V →ₗ[F] V) +
      (1 : V →ₗ[F] V)) := by
  have hv' : ((g : V →ₗ[F] V) ^ 2 + (g : V →ₗ[F] V) + (1 : V →ₗ[F] V)) v = 0 := by
    simpa [LinearMap.mem_ker] using hv
  have hpoly : ((g : V →ₗ[F] V) ^ 2 + (g : V →ₗ[F] V) + (1 : V →ₗ[F] V)) *
      (g : V →ₗ[F] V) =
      (g : V →ₗ[F] V) * ((g : V →ₗ[F] V) ^ 2 + (g : V →ₗ[F] V) + (1 : V →ₗ[F] V)) := by
    noncomm_ring
  have h := congrArg (fun e : V →ₗ[F] V => e v) hpoly
  rw [Module.End.mul_apply, Module.End.mul_apply, hv', map_zero] at h
  rw [LinearMap.mem_ker]
  exact h

private theorem i167CLin_r_one_module_aux9 (hF : Nat.card F = 2) {g : V ≃ₗ[F] V} {v : V}
    (hv : v ∈ LinearMap.ker ((g : V →ₗ[F] V) ^ 2 + (g : V →ₗ[F] V) + (1 : V →ₗ[F] V)))
    (hgv : g v = v) : v = 0 := by
  have hgv' : (g : V →ₗ[F] V) v = v := hgv
  have hv' : ((g : V →ₗ[F] V) ^ 2 + (g : V →ₗ[F] V) + (1 : V →ₗ[F] V)) v = 0 := by
    simpa [LinearMap.mem_ker] using hv
  have h1 : ((g : V →ₗ[F] V) ^ 2 + (g : V →ₗ[F] V) + (1 : V →ₗ[F] V)) v = v := by
    change (g : V →ₗ[F] V) ((g : V →ₗ[F] V) v) + (g : V →ₗ[F] V) v + v = v
    simp only [hgv']
    simp [i167CLin_r_one_module_aux2 hF]
  rw [h1] at hv'
  exact hv'

private theorem i167CLin_r_one_module_aux10 (hF : Nat.card F = 2) {g : V ≃ₗ[F] V}
    (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) :
    LinearMap.ker ((g : V →ₗ[F] V) ^ 2 + (g : V →ₗ[F] V) + (1 : V →ₗ[F] V)) ≠ ⊥ := by
  intro hU
  apply hg1
  ext v
  have hcompl := i167CLin_r_one_module_aux4 hF hg3
  have hv : v ∈ LinearMap.ker ((g : V →ₗ[F] V) - (1 : V →ₗ[F] V)) := by
    have hmem : v ∈ LinearMap.ker ((g : V →ₗ[F] V) - (1 : V →ₗ[F] V)) ⊔
        LinearMap.ker ((g : V →ₗ[F] V) ^ 2 + (g : V →ₗ[F] V) + (1 : V →ₗ[F] V)) := by
      rw [hcompl.sup_eq_top]; exact Submodule.mem_top
    rwa [hU, sup_bot_eq] at hmem
  have h := hv
  rw [LinearMap.mem_ker] at h
  simpa [sub_eq_zero] using h

private theorem i167CLin_r_one_module_aux11 (hF : Nat.card F = 2) {g : V ≃ₗ[F] V}
    (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) :
    2 ≤ Module.finrank F (LinearMap.ker ((g : V →ₗ[F] V) ^ 2 + (g : V →ₗ[F] V) +
      (1 : V →ₗ[F] V))) := by
  let U := LinearMap.ker ((g : V →ₗ[F] V) ^ 2 + (g : V →ₗ[F] V) + (1 : V →ₗ[F] V))
  have hUne : U ≠ ⊥ := i167CLin_r_one_module_aux10 hF hg3 hg1
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
  have hgu : (g : V →ₗ[F] V) u ∈ U := i167CLin_r_one_module_aux8 hu
  have hgu0 : g u ≠ 0 := by
    intro h
    exact hu0 (g.injective (by rw [h, map_zero]))
  let u' : U := ⟨u, hu⟩
  let gu' : U := ⟨(g : V →ₗ[F] V) u, hgu⟩
  have hu'0 : u' ≠ 0 := by simpa [u'] using hu0
  have hli : LinearIndependent F ![u', gu'] := by
    refine (LinearIndependent.pair_iff' hu'0).mpr ?_
    intro a
    have h01 : a = 0 ∨ a = 1 := by
      classical
      letI : Fintype F := Fintype.ofFinite F
      have hcard : Fintype.card F ≤ 2 := by
        rw [← Nat.card_eq_fintype_card]; omega
      have huniv := Finset.univ_of_card_le_two (R := F) hcard
      have : a ∈ ({0, 1} : Finset F) := by rw [← huniv]; exact Finset.mem_univ a
      simpa using this
    rcases h01 with rfl | rfl
    · intro h
      have h1 : (g : V →ₗ[F] V) u = 0 := by
        have h2 := congrArg Subtype.val h
        simpa [u', gu'] using h2.symm
      exact hgu0 h1
    · simp only [one_smul]
      intro h
      apply hu0
      have hval : u = g u := by
        have h2 := congrArg Subtype.val h
        simpa [u', gu'] using h2
      exact i167CLin_r_one_module_aux9 hF hu hval.symm
  have := hli.fintype_card_le_finrank
  simpa using this

private theorem i167CLin_r_one_module_aux12 (hF : Nat.card F = 2) {g : V ≃ₗ[F] V}
    (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) {t : V ≃ₗ[F] V} (ht : t ∈ Subgroup.zpowers g) {v : V}
    (hvU : v ∈ LinearMap.ker ((g : V →ₗ[F] V) ^ 2 + (g : V →ₗ[F] V) + (1 : V →ₗ[F] V)))
    (hv0 : v ≠ 0) (htv : t v = v) : t = 1 := by
  have horder : orderOf g = 3 := by
    have hdvd : orderOf g ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hg3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h (fun hh => hg1 (orderOf_eq_one_iff.mp hh))
    · exact h
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp ht
  have hmod : g ^ (j % (3 : ℤ)) = g ^ j := by
    have h := zpow_mod_orderOf g j
    rw [horder] at h
    exact h
  have hgv : (g ^ j) v = v := by rw [hj]; exact htv
  have hge : (0 : ℤ) ≤ j % 3 := Int.emod_nonneg j (by norm_num)
  have hlt : j % 3 < 3 := Int.emod_lt_of_pos j (by norm_num)
  have hcases : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases hcases with hk | hk | hk
  · rw [← hj, ← hmod, hk]; simp
  · rw [hk] at hmod
    have hgvv : g v = v := by
      have : g v = (g ^ j) v := by rw [← hmod]; simp
      rwa [hgv] at this
    exact absurd (i167CLin_r_one_module_aux9 hF hvU hgvv) hv0
  · rw [hk] at hmod
    have hg2v : (g ^ 2) v = v := by
      have : (g ^ 2) v = (g ^ j) v := by rw [← hmod]; simp
      rwa [hgv] at this
    have hgvv : g v = v := by
      have h1 : g ((g ^ 2) v) = g v := congrArg g hg2v
      have h2 : g ((g ^ 2) v) = v := by
        rw [← LinearEquiv.mul_apply, ← pow_succ', hg3]
        rfl
      rw [h2] at h1
      exact h1.symm
    exact absurd (i167CLin_r_one_module_aux9 hF hvU hgvv) hv0

private theorem i167CLin_r_one_module_aux13 {W U N₁ N'' : Submodule F V} (hWU : IsCompl W U)
    (hN₁U : N₁ ≤ U) (hN''compl : IsCompl N₁ N'')
    (hN₁dim : Module.finrank F N₁ ≤ 2) (h3 : 3 ≤ Module.finrank F U) :
    IsCompl N₁ (W ⊔ (U ⊓ N'')) ∧ (U ⊓ N'') ≠ ⊥ := by
  have hN₁inf : N₁ ⊓ (U ⊓ N'') = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨hv₁, hv₂⟩ := Submodule.mem_inf.mp hv
    have hmem : v ∈ N₁ ⊓ N'' := Submodule.mem_inf.mpr ⟨hv₁, (Submodule.mem_inf.mp hv₂).2⟩
    rwa [hN''compl.inf_eq_bot, Submodule.mem_bot] at hmem
  have hN₁sup : N₁ ⊔ (U ⊓ N'') = U := by
    have hmod := sup_inf_assoc_of_le (x := N₁) N'' (z := U) hN₁U
    rw [hN''compl.sup_eq_top, top_inf_eq, inf_comm] at hmod
    exact hmod.symm
  have hN₂ne : U ⊓ N'' ≠ ⊥ := by
    intro hN₂
    have hUN₁ : U = N₁ := by rw [← hN₁sup, hN₂, sup_bot_eq]
    have hfin : Module.finrank F U = Module.finrank F N₁ := by rw [hUN₁]
    omega
  refine ⟨?_, hN₂ne⟩
  refine isCompl_iff.mpr ⟨?_, ?_⟩
  · rw [disjoint_iff, Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨hv₁, hvN'⟩ := Submodule.mem_inf.mp hv
    obtain ⟨w, hw, n₂, hn₂, hwn⟩ := Submodule.mem_sup.mp hvN'
    have hwU : w ∈ U := by
      have hw_eq : w = v - n₂ := by rw [← hwn]; abel
      rw [hw_eq]
      exact U.sub_mem (hN₁U hv₁) (Submodule.mem_inf.mp hn₂).1
    have hwbot : w = 0 := by
      have hmem : w ∈ W ⊓ U := Submodule.mem_inf.mpr ⟨hw, hwU⟩
      rwa [hWU.inf_eq_bot, Submodule.mem_bot] at hmem
    have hv_eq : v = n₂ := by rw [← hwn, hwbot, zero_add]
    have hn₂N₁ : n₂ ∈ N₁ := hv_eq ▸ hv₁
    have hmem : n₂ ∈ N₁ ⊓ (U ⊓ N'') := Submodule.mem_inf.mpr ⟨hn₂N₁, hn₂⟩
    rw [hN₁inf, Submodule.mem_bot] at hmem
    rw [hv_eq, hmem]
  · rw [codisjoint_iff]
    have hsup : N₁ ⊔ (W ⊔ (U ⊓ N'')) = W ⊔ U := by
      rw [show N₁ ⊔ (W ⊔ (U ⊓ N'')) = W ⊔ (N₁ ⊔ (U ⊓ N'')) by ac_rfl, hN₁sup]
    rw [hsup, hWU.sup_eq_top]

private theorem i167CLin_r_one_module_aux14 {H : Subgroup (V ≃ₗ[F] V)}
    {g : V ≃ₗ[F] V} (hgH : g ∈ H) (hg3 : g ^ 3 = 1)
    {N₁ N' : Submodule F V} (hN'compl : IsCompl N₁ N')
    (hN₁stab : ∀ h ∈ H, ∀ v ∈ N₁, h v ∈ N₁) :
    ∃ t₀ : V →ₗ[F] V, t₀ ^ 3 = 1 ∧ (∀ v ∈ N₁, t₀ v = (g : V →ₗ[F] V) v) ∧
      (∀ v ∈ N', t₀ v = v) := by
  let ρ : V →ₗ[F] V := Submodule.projection N₁ N' hN'compl
  let t₀ : V →ₗ[F] V := (1 : V →ₗ[F] V) + ((g : V →ₗ[F] V) - (1 : V →ₗ[F] V)) * ρ
  have hg3' : (g : V →ₗ[F] V) ^ 3 = 1 := by
    have h : (↑(g ^ 3) : V →ₗ[F] V) = (↑(1 : V ≃ₗ[F] V) : V →ₗ[F] V) := by rw [hg3]
    have h1 : (↑(g ^ 3) : V →ₗ[F] V) = (g : V →ₗ[F] V) ^ 3 := by
      simp [pow_succ, LinearEquiv.coe_toLinearMap_mul]
    rwa [h1] at h
  have ht₀_left : ∀ x ∈ N₁, t₀ x = (g : V →ₗ[F] V) x := by
    intro x hx
    have hρ : ρ x = x := Submodule.projection_apply_of_mem_left hN'compl hx
    change x + ((g : V →ₗ[F] V) - (1 : V →ₗ[F] V)) (ρ x) = (g : V →ₗ[F] V) x
    rw [hρ]
    change x + ((g : V →ₗ[F] V) x - x) = (g : V →ₗ[F] V) x
    abel
  have ht₀_right : ∀ x ∈ N', t₀ x = x := by
    intro x hx
    have hρ : ρ x = 0 := Submodule.projection_apply_of_mem_right hN'compl hx
    change x + ((g : V →ₗ[F] V) - (1 : V →ₗ[F] V)) (ρ x) = x
    rw [hρ]
    simp
  have ht₀3 : t₀ ^ 3 = 1 := by
    ext v
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      Submodule.mem_sup.mp ((hN'compl.sup_eq_top ▸ Submodule.mem_top) : v ∈ N₁ ⊔ N')
    rw [← hxy, map_add]
    have hx3 : (t₀ ^ 3) x = x := by
      change t₀ (t₀ (t₀ x)) = x
      have h2 : (g : V →ₗ[F] V) x ∈ N₁ := hN₁stab g hgH x hx
      have h3 : (g : V →ₗ[F] V) ((g : V →ₗ[F] V) x) ∈ N₁ := hN₁stab g hgH _ h2
      rw [ht₀_left x hx, ht₀_left ((g : V →ₗ[F] V) x) h2,
        ht₀_left ((g : V →ₗ[F] V) ((g : V →ₗ[F] V) x)) h3]
      change ((g : V →ₗ[F] V) ^ 3) x = x
      rw [hg3']
      rfl
    have hy3 : (t₀ ^ 3) y = y := by
      change t₀ (t₀ (t₀ y)) = y
      rw [ht₀_right y hy, ht₀_right y hy, ht₀_right y hy]
    rw [hx3, hy3]
    rfl
  exact ⟨t₀, ht₀3, ht₀_left, ht₀_right⟩

private theorem i167CLin_r_one_module_aux14a {H : Subgroup (V ≃ₗ[F] V)}
    (hH : IsElemAbelian 3 H) {g : V ≃ₗ[F] V} (hgH : g ∈ H)
    {N₁ N' : Submodule F V} (hN'compl : IsCompl N₁ N')
    (hN₁stab : ∀ h ∈ H, ∀ v ∈ N₁, h v ∈ N₁) (hN'stab : ∀ h ∈ H, ∀ v ∈ N', h v ∈ N')
    {t₀ : V →ₗ[F] V} (ht₀_left : ∀ v ∈ N₁, t₀ v = (g : V →ₗ[F] V) v)
    (ht₀_right : ∀ v ∈ N', t₀ v = v) :
    ∀ a ∈ H, (a : V →ₗ[F] V) * t₀ = t₀ * (a : V →ₗ[F] V) := by
  intro a ha
  have hcommg : a * g = g * a := i167CLin_r_one_module_aux5 hH hgH ha
  have hag : ∀ z, (g : V →ₗ[F] V) ((a : V →ₗ[F] V) z) =
      (a : V →ₗ[F] V) ((g : V →ₗ[F] V) z) := by
    intro z
    have h := congrArg (fun e : V ≃ₗ[F] V => e z) hcommg
    simpa [LinearEquiv.mul_apply] using h.symm
  ext v
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    Submodule.mem_sup.mp ((hN'compl.sup_eq_top ▸ Submodule.mem_top) : v ∈ N₁ ⊔ N')
  have hax : a x ∈ N₁ := hN₁stab a ha x hx
  have hay : a y ∈ N' := hN'stab a ha y hy
  rw [Module.End.mul_apply, Module.End.mul_apply]
  calc (a : V →ₗ[F] V) (t₀ v) = (a : V →ₗ[F] V) (t₀ (x + y)) := by rw [hxy]
    _ = (a : V →ₗ[F] V) (t₀ x + t₀ y) := by rw [LinearMap.map_add t₀ x y]
    _ = (a : V →ₗ[F] V) ((g : V →ₗ[F] V) x + y) := by rw [ht₀_left x hx, ht₀_right y hy]
    _ = (a : V →ₗ[F] V) ((g : V →ₗ[F] V) x) + (a : V →ₗ[F] V) y := by
        rw [LinearMap.map_add (a : V →ₗ[F] V) ((g : V →ₗ[F] V) x) y]
    _ = (g : V →ₗ[F] V) ((a : V →ₗ[F] V) x) + (a : V →ₗ[F] V) y := by rw [← hag x]
    _ = t₀ ((a : V →ₗ[F] V) x) + t₀ ((a : V →ₗ[F] V) y) := by
        rw [ht₀_left ((a : V →ₗ[F] V) x) hax, ht₀_right ((a : V →ₗ[F] V) y) hay]
    _ = t₀ ((a : V →ₗ[F] V) x + (a : V →ₗ[F] V) y) := by
        rw [LinearMap.map_add t₀ ((a : V →ₗ[F] V) x) ((a : V →ₗ[F] V) y)]
    _ = t₀ ((a : V →ₗ[F] V) (x + y)) := by
        rw [LinearMap.map_add (a : V →ₗ[F] V) x y]
    _ = t₀ ((a : V →ₗ[F] V) v) := by rw [hxy]

private theorem i167CLin_r_one_module_aux15 {H : Subgroup (V ≃ₗ[F] V)} {g : V ≃ₗ[F] V}
    {N₁ N' : Submodule F V} {t₀ : V →ₗ[F] V} (ht₀3 : t₀ ^ 3 = 1)
    (ht₀left : ∀ v ∈ N₁, t₀ v = (g : V →ₗ[F] V) v) (ht₀right : ∀ v ∈ N', t₀ v = v)
    (ht₀comm : ∀ a ∈ H, (a : V →ₗ[F] V) * t₀ = t₀ * (a : V →ₗ[F] V)) :
    ∃ t : V ≃ₗ[F] V, t ^ 3 = 1 ∧ (∀ a ∈ H, a * t = t * a) ∧
      (∀ v ∈ N₁, t v = (g : V →ₗ[F] V) v) ∧ (∀ v ∈ N', t v = v) := by
  have ht₀inj : Function.Injective t₀ := by
    intro x y hxy
    have hsub : t₀ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hzero : x - y = 0 := by
      calc x - y = (t₀ ^ 3) (x - y) := by rw [ht₀3]; rfl
        _ = (t₀ ^ 2) (t₀ (x - y)) := by
            rw [show t₀ ^ 3 = t₀ ^ 2 * t₀ by rw [pow_succ], Module.End.mul_apply]
        _ = 0 := by rw [hsub, map_zero]
    rwa [sub_eq_zero] at hzero
  let t : V ≃ₗ[F] V := t₀.linearEquivOfInjective ht₀inj rfl
  have ht_coe : (t : V →ₗ[F] V) = t₀ := by
    ext w
    exact LinearMap.linearEquivOfInjective_apply ht₀inj rfl w
  have ht_apply : ∀ z, t z = t₀ z := fun z => congrArg (fun f : V →ₗ[F] V => f z) ht_coe
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · ext z
    rw [LinearEquiv.pow_apply]
    change t (t (t z)) = z
    simp only [ht_apply]
    change (t₀ ^ 3) z = z
    rw [ht₀3]
    rfl
  · intro a ha
    ext v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    have h := congrArg (fun f : V →ₗ[F] V => f v) (ht₀comm a ha)
    simpa [Module.End.mul_apply, ht_apply] using h
  · intro v hv
    rw [ht_apply v, ht₀left v hv]
  · intro v hv
    rw [ht_apply v, ht₀right v hv]

private theorem i167CLin_r_one_module_aux16a {H : Subgroup (V ≃ₗ[F] V)}
    {W U N'' : Submodule F V}
    (hWstab : ∀ h ∈ H, ∀ v ∈ W, h v ∈ W) (hUstab : ∀ h ∈ H, ∀ v ∈ U, h v ∈ U)
    (hN''stab : ∀ h ∈ H, ∀ v ∈ N'', h v ∈ N'') :
    ∀ h ∈ H, ∀ v ∈ W ⊔ (U ⊓ N''), h v ∈ W ⊔ (U ⊓ N'') := by
  intro h hh v hv
  obtain ⟨w, hw, n₂, hn₂, hwn⟩ := Submodule.mem_sup.mp hv
  have hn₂' : h n₂ ∈ U ⊓ N'' := by
    obtain ⟨hvU, hvN''⟩ := Submodule.mem_inf.mp hn₂
    exact Submodule.mem_inf.mpr ⟨hUstab h hh n₂ hvU, hN''stab h hh n₂ hvN''⟩
  rw [← hwn, map_add]
  exact Submodule.mem_sup.mpr ⟨h w, hWstab h hh w hw, h n₂, hn₂', rfl⟩

private theorem i167CLin_r_one_module_aux16 (hF : Nat.card F = 2)
    {H : Subgroup (V ≃ₗ[F] V)} (hH : IsElemAbelian 3 H)
    (hmax : ∀ s : V ≃ₗ[F] V, s ^ 3 = 1 → (∀ a ∈ H, a * s = s * a) → s ∈ H)
    {g : V ≃ₗ[F] V} (hgH : g ∈ H) (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1)
    (hCA : ∀ a ∈ H, (∀ v, g v = v → a v = v) → a ∈ Subgroup.zpowers g) :
    Module.finrank F (LinearMap.ker ((g : V →ₗ[F] V) ^ 2 + (g : V →ₗ[F] V) +
      (1 : V →ₗ[F] V))) ≤ 2 := by
  let W : Submodule F V := LinearMap.ker ((g : V →ₗ[F] V) - (1 : V →ₗ[F] V))
  let U : Submodule F V := LinearMap.ker ((g : V →ₗ[F] V) ^ 2 + (g : V →ₗ[F] V) +
    (1 : V →ₗ[F] V))
  by_contra hle
  have h3 : 3 ≤ Module.finrank F U := by
    have hle' : ¬ (Module.finrank F U ≤ 2) := hle
    omega
  have hWU : IsCompl W U := i167CLin_r_one_module_aux4 hF hg3
  have hUne : U ≠ ⊥ := i167CLin_r_one_module_aux10 hF hg3 hg1
  have hUstab : ∀ h ∈ H, ∀ v ∈ U, h v ∈ U :=
    fun h hh v hv => i167CLin_r_one_module_aux7 hH hgH hh hv
  obtain ⟨N₁, hN₁U, hN₁ne, hN₁stab, hN₁dim⟩ :=
    i167CLin_stable_small hF H hH hUne hUstab
  obtain ⟨N'', hN''compl, hN''stab⟩ := i167CLin_stable_complement hF H hH hN₁stab
  obtain ⟨hN'compl, hN₂ne⟩ :=
    i167CLin_r_one_module_aux13 hWU hN₁U hN''compl hN₁dim h3
  let N' : Submodule F V := W ⊔ (U ⊓ N'')
  have hN'stab : ∀ h ∈ H, ∀ v ∈ N', h v ∈ N' :=
    i167CLin_r_one_module_aux16a (fun h hh v hv => i167CLin_r_one_module_aux6 hH hgH hh hv)
      hUstab hN''stab
  obtain ⟨t₀, ht₀3, ht₀left, ht₀right⟩ :=
    i167CLin_r_one_module_aux14 hgH hg3 hN'compl hN₁stab
  have ht₀comm := i167CLin_r_one_module_aux14a hH hgH hN'compl hN₁stab hN'stab ht₀left ht₀right
  obtain ⟨t, ht3, htcomm, htN₁, htN'⟩ :=
    i167CLin_r_one_module_aux15 ht₀3 ht₀left ht₀right ht₀comm
  have htW : ∀ v, g v = v → t v = v := by
    intro v hv
    have hvW : v ∈ W := by simpa [W, LinearMap.mem_ker, sub_eq_zero] using hv
    exact htN' v (Submodule.mem_sup.mpr ⟨v, hvW, 0, (U ⊓ N'').zero_mem, add_zero v⟩)
  have htCA : t ∈ Subgroup.zpowers g := hCA t (hmax t ht3 htcomm) htW
  obtain ⟨v, hvN₂, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN₂ne
  have htv : t v = v := htN' v (Submodule.mem_sup.mpr ⟨0, W.zero_mem, v, hvN₂, zero_add v⟩)
  have ht1 : t = 1 :=
    i167CLin_r_one_module_aux12 hF hg3 hg1 htCA (Submodule.mem_inf.mp hvN₂).1 hv0 htv
  obtain ⟨w, hwN₁, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN₁ne
  have hgw : g w = w := by
    have h1 : t w = w := by rw [ht1]; rfl
    rw [htN₁ w hwN₁] at h1
    exact h1
  exact hw0 (i167CLin_r_one_module_aux9 hF (hN₁U hwN₁) hgw)

theorem i167CLin_r_one_module {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (H : Subgroup (V ≃ₗ[F] V)) (hH : IsElemAbelian 3 H)
    (hmax : ∀ s : V ≃ₗ[F] V, s ^ 3 = 1 → (∀ a ∈ H, a * s = s * a) → s ∈ H)
    {g : V ≃ₗ[F] V} (hgH : g ∈ H) (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1)
    (hCA : ∀ a ∈ H, (∀ v, g v = v → a v = v) → a ∈ Subgroup.zpowers g) :
    Module.finrank F V = Module.finrank F (LinearMap.ker ((g : V →ₗ[F] V) - 1)) + 2 := by
  let W : Submodule F V := LinearMap.ker ((g : V →ₗ[F] V) - (1 : V →ₗ[F] V))
  let U : Submodule F V := LinearMap.ker ((g : V →ₗ[F] V) ^ 2 + (g : V →ₗ[F] V) +
    (1 : V →ₗ[F] V))
  have hWU : IsCompl W U := i167CLin_r_one_module_aux4 hF hg3
  have hle : Module.finrank F U ≤ 2 :=
    i167CLin_r_one_module_aux16 hF hH hmax hgH hg3 hg1 hCA
  have hge : 2 ≤ Module.finrank F U := i167CLin_r_one_module_aux11 hF hg3 hg1
  have hU2 : Module.finrank F U = 2 := le_antisymm hle hge
  have hfin : Module.finrank F W + Module.finrank F U = Module.finrank F V :=
    Submodule.finrank_add_eq_of_isCompl hWU
  show Module.finrank F V = Module.finrank F W + 2
  rw [← hfin, hU2]

end CFSG.LocalAnalysis.GLTheoremA.I167

end

