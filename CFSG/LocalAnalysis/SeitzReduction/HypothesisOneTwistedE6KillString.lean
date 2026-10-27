module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6KillSteps

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open scoped commutatorElement

variable {K : Type} [Field K]

@[expose] def TwKillStep
    (σ : K →+* K) (J : Set (Fin TwistTag.E6.tag.rank)) (i : Fin TwistTag.E6.tag.rank)
    (A : ModGL TwistTag.E6.tag K) (R : Set (Fin TwistTag.E6.tag.rank → ℤ))
    (z n : ModGL TwistTag.E6.tag K) : Prop :=
  ∃ R' : Set (Fin TwistTag.E6.tag.rank → ℤ), TwKillAdm J i R' ∧
    (∀ β ∈ R', permLattice TwistTag.E6.perm β ∈ R') ∧ R'.ncard < R.ncard ∧
    ∃ p ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J \
        {Pi.single i 1, Pi.single (TwistTag.E6.perm i) 1}),
      twistHom TwistTag.E6 K σ p = p ∧
      ∃ z' ∈ rootSpan TwistTag.E6.tag K (twKillPerp J i), twistHom TwistTag.E6 K σ z' = z' ∧
        ∃ n' ∈ rootSpan TwistTag.E6.tag K R', twistHom TwistTag.E6 K σ n' = n' ∧
          A * p * A * (z * n) * p⁻¹ = z' * n'


theorem twKill_string_core [CharP K 2] {J : Set (Fin TwistTag.E6.tag.rank)}
    {i : Fin TwistTag.E6.tag.rank} (hi : i ∈ J) {R : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hR : TwKillAdm J i R) {δ : Fin TwistTag.E6.tag.rank → ℤ} (hmin : TwKillMin i R δ)
    (hδa : IsRoot TwistTag.E6.tag (δ + Pi.single i 1))
    (hR₁ : TwKillAdm J i (R \ {δ, δ + Pi.single i 1}))
    {A : ModGL TwistTag.E6.tag K}
    (hAV : A ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J))
    (hAA : A * A = 1) {c : K} (hc : c ≠ 0)
    (hconjY : ∀ g : K, (pinnedX TwistTag.E6.tag K (δ + Pi.single i 1) (c * g) *
        pinnedX TwistTag.E6.tag K δ g)⁻¹ * (A * pinnedX TwistTag.E6.tag K δ g * A) ∈
          rootSpan TwistTag.E6.tag K (R \ {δ, δ + Pi.single i 1}))
    (hAX : ∀ e : K, A * pinnedX TwistTag.E6.tag K (δ + Pi.single i 1) e =
      pinnedX TwistTag.E6.tag K (δ + Pi.single i 1) e * A)
    {z n : ModGL TwistTag.E6.tag K} (hz : z ∈ rootSpan TwistTag.E6.tag K (twKillPerp J i))
    (hAz : A * z = z * A) (hn : n ∈ rootSpan TwistTag.E6.tag K R)
    (hcoc : A * (z * n) * A = (z * n)⁻¹) :
    ∃ d₁ : K, ∃ n' ∈ rootSpan TwistTag.E6.tag K (R \ {δ, δ + Pi.single i 1}),
      n = pinnedX TwistTag.E6.tag K (δ + Pi.single i 1) d₁ * n' ∧
      z⁻¹ * (A * pinnedX TwistTag.E6.tag K δ (d₁ * c⁻¹) * A * (z * n) *
        (pinnedX TwistTag.E6.tag K δ (d₁ * c⁻¹))⁻¹) ∈
          rootSpan TwistTag.E6.tag K (R \ {δ, δ + Pi.single i 1}) := by
  set α : Fin TwistTag.E6.tag.rank → ℤ := Pi.single i 1 with hα
  set R' := R \ {δ, δ + α} with hR'def
  have hαJ : α ∈ parabolicPosRoots TwistTag.E6.tag J := twKill_single_mem hi
  have hRpos : ∀ β ∈ R, IsRoot TwistTag.E6.tag β ∧ 0 < height β := fun β hβ =>
    (hR.subset hβ).1.2
  have hRclosed : ∀ β ∈ R, ∀ γ ∈ R, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot TwistTag.E6.tag (a • β + b • γ) → a • β + b • γ ∈ R :=
    fun β hβ γ hγ a b ha hb hr => hR.ideal β (hR.subset hβ).1 γ hγ a b ha hb hr
  have hR'sub : R' ⊆ parabolicPosRoots TwistTag.E6.tag J := fun x hx => (hR₁.subset hx).1
  have hR'pos : ∀ β ∈ R', IsRoot TwistTag.E6.tag β ∧ 0 < height β := fun β hβ =>
    (hR₁.subset hβ).1.2
  have hR'closed : ∀ β ∈ R', ∀ γ ∈ R', ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot TwistTag.E6.tag (a • β + b • γ) → a • β + b • γ ∈ R' :=
    fun β hβ γ hγ a b ha hb hr => hR₁.ideal β (hR₁.subset hβ).1 γ hγ a b ha hb hr
  have hnorm' : ∀ v ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J),
      ∀ m ∈ rootSpan TwistTag.E6.tag K R', v * m * v⁻¹ ∈ rootSpan TwistTag.E6.tag K R' :=
    fun v hv m hm => classKill_conj_mem hR'sub hR₁.ideal hv hm
  have hNV : rootSpan TwistTag.E6.tag K R' ≤
      rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J) :=
    classKill_rootSpan_mono hR'sub
  have hδR := hmin.mem
  have hδΨ := hR.subset hδR
  have hδJ : δ ∈ parabolicPosRoots TwistTag.E6.tag J := hδΨ.1
  have hδr : IsRoot TwistTag.E6.tag δ := hδJ.2.1
  have hεR : δ + α ∈ R := by
    have h := hR.ideal _ hαJ δ hδR 1 1 le_rfl le_rfl
      (by rw [one_smul, one_smul, add_comm]; exact hδa)
    rwa [one_smul, one_smul, add_comm] at h
  have hεJ : δ + α ∈ parabolicPosRoots TwistTag.E6.tag J := (hR.subset hεR).1
  have hδε : δ ≠ δ + α := fun h => by
    have := congrFun h i
    simp only [Pi.add_apply, hα, Pi.single_eq_same] at this
    omega
  have hdeg : twKillDeg i (δ + α) = twKillDeg i δ := by
    rw [twKillDeg_add, twKillDeg_single (Or.inl rfl), add_zero]
  have hhigh : ∀ x ∈ R, twKillDeg i δ < twKillDeg i x → x ∈ R' := by
    intro x hx hlt
    refine ⟨hx, fun h => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl
    · exact lt_irrefl _ hlt
    · rw [hdeg] at hlt
      exact lt_irrefl _ hlt
  have hdegpos : ∀ γ ∈ parabolicPosRoots TwistTag.E6.tag J \
      {Pi.single i 1, Pi.single (TwistTag.E6.perm i) 1}, 1 ≤ twKillDeg i γ := by
    intro γ hγ
    obtain ⟨hγJ, hγne⟩ := hγ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hγne
    exact one_le_twKillDeg hγJ.2.1 hγJ.2.2 hγne.1 hγne.2
  have hβT : ∀ β ∈ R, twKillDeg i β = twKillDeg i δ →
      ∀ γ ∈ parabolicPosRoots TwistTag.E6.tag J \
        {Pi.single i 1, Pi.single (TwistTag.E6.perm i) 1}, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
        IsRoot TwistTag.E6.tag (a • γ + b • β) → a • γ + b • β ∈ R' := by
    intro β hβ hβd γ hγ a b ha hb hr
    refine hhigh _ (hR.ideal γ hγ.1 β hβ a b ha hb hr) ?_
    rw [twKillDeg_add, twKillDeg_nsmul, twKillDeg_nsmul, hβd]
    have h1 := hdegpos γ hγ
    have h2 := hdegpos δ hδΨ
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith
  have hβR : ∀ β ∈ R, twKillDeg i β = twKillDeg i δ →
      ∀ γ ∈ R, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
        IsRoot TwistTag.E6.tag (a • γ + b • β) → a • γ + b • β ∈ R' := by
    intro β hβ hβd γ hγ a b ha hb hr
    refine hhigh _ (hR.ideal γ (hR.subset hγ).1 β hβ a b ha hb hr) ?_
    rw [twKillDeg_add, twKillDeg_nsmul, twKillDeg_nsmul, hβd]
    have h1 := hmin.deg_le γ hγ
    have h2 := hdegpos δ hδΨ
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith
  have hzU : z ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J \
      {Pi.single i 1, Pi.single (TwistTag.E6.perm i) 1}) :=
    classKill_rootSpan_mono twKillPerp_subset hz
  have hzV : z ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J) :=
    classKill_rootSpan_mono (fun x hx => (twKillPerp_subset hx).1) hz
  have hYV : ∀ g : K, pinnedX TwistTag.E6.tag K δ g ∈
      rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J) :=
    classKill_pinnedX_mem hδJ
  have hXV : ∀ e : K, pinnedX TwistTag.E6.tag K (δ + α) e ∈
      rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J) :=
    classKill_pinnedX_mem hεJ
  have hYR : ∀ g : K, pinnedX TwistTag.E6.tag K δ g ∈ rootSpan TwistTag.E6.tag K R :=
    classKill_pinnedX_mem hδR
  have hXR : ∀ e : K, pinnedX TwistTag.E6.tag K (δ + α) e ∈ rootSpan TwistTag.E6.tag K R :=
    classKill_pinnedX_mem hεR
  have hRJ : R ⊆ parabolicPosRoots TwistTag.E6.tag J := fun x hx => (hR.subset hx).1
  have hzY : ∀ g : K, ⁅z, pinnedX TwistTag.E6.tag K δ g⁆ ∈ rootSpan TwistTag.E6.tag K R' :=
    fun g => twKill_commutator_mem Set.sdiff_subset hnorm' hδJ (hβT δ hδR rfl) hzU g
  have hzX : ∀ e : K, ⁅z, pinnedX TwistTag.E6.tag K (δ + α) e⁆ ∈
      rootSpan TwistTag.E6.tag K R' :=
    fun e => twKill_commutator_mem Set.sdiff_subset hnorm' hεJ (hβT _ hεR hdeg) hzU e
  have hXY : ∀ e g : K, ⁅pinnedX TwistTag.E6.tag K (δ + α) e, pinnedX TwistTag.E6.tag K δ g⁆ ∈
      rootSpan TwistTag.E6.tag K R' :=
    fun e g => twKill_commutator_mem hRJ hnorm' hδJ (hβR δ hδR rfl) (hXR e) g
  have hYX : ∀ g e : K, ⁅pinnedX TwistTag.E6.tag K δ g, pinnedX TwistTag.E6.tag K (δ + α) e⁆ ∈
      rootSpan TwistTag.E6.tag K R' :=
    fun g e => twKill_commutator_mem hRJ hnorm' hεJ (hβR _ hεR hdeg) (hYR g) e
  have hinj : Function.Injective ![δ, δ + α] := by
    intro a b hab
    fin_cases a <;> fin_cases b
    all_goals first | rfl | exact absurd hab hδε | exact absurd hab.symm hδε
  obtain ⟨d, hd⟩ := classKill_split hRpos hRclosed ![δ, δ + α] hinj
    (fun j => by fin_cases j; exacts [hδR, hεR]) hn
  rw [Matrix.range_cons_cons_empty] at hd
  have hprod : (List.ofFn fun j => pinnedX TwistTag.E6.tag K (![δ, δ + α] j) (d j)).prod =
      pinnedX TwistTag.E6.tag K δ (d 0) * pinnedX TwistTag.E6.tag K (δ + α) (d 1) := by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_cons,
      List.prod_nil, mul_one]
    rfl
  rw [hprod] at hd
  set n' := (pinnedX TwistTag.E6.tag K δ (d 0) * pinnedX TwistTag.E6.tag K (δ + α) (d 1))⁻¹ * n
    with hn'def
  have hn_eq : n = pinnedX TwistTag.E6.tag K δ (d 0) * pinnedX TwistTag.E6.tag K (δ + α) (d 1) *
      n' := by
    rw [hn'def]
    group
  have hAXA : ∀ e : K, (pinnedX TwistTag.E6.tag K (δ + α) e)⁻¹ *
      (A * pinnedX TwistTag.E6.tag K (δ + α) e * A) ∈ rootSpan TwistTag.E6.tag K R' := fun e => by
    rw [hAX e, mul_assoc, hAA, mul_one, inv_mul_cancel]
    exact one_mem _
  have hcoc' : A * (z * (pinnedX TwistTag.E6.tag K δ (d 0) *
      pinnedX TwistTag.E6.tag K (δ + α) (d 1) * n')) * A =
      (z * (pinnedX TwistTag.E6.tag K δ (d 0) * pinnedX TwistTag.E6.tag K (δ + α) (d 1) *
        n'))⁻¹ := by
    rw [← hn_eq]
    exact hcoc
  have hzzw := classKill_rel_cocycle hNV hnorm' hAV hzV (hYV (d 0)) (hXV (d 1)) (hXV (c * d 0))
    hd hAA hAz (classKill_pinnedX_mul_self _ _) (classKill_pinnedX_mul_self _ _)
    (hconjY (d 0)) (hAXA (d 1)) (hzY (d 0)) (hzX (d 1)) (hXY (d 1) (d 0)) hcoc'
  have hzzR : z * z ∈ rootSpan TwistTag.E6.tag K R := by
    have e : z * z = (z * z * pinnedX TwistTag.E6.tag K (δ + α) (c * d 0)) *
        (pinnedX TwistTag.E6.tag K (δ + α) (c * d 0))⁻¹ := by group
    rw [e]
    exact mul_mem (classKill_rootSpan_mono Set.sdiff_subset hzzw) (inv_mem (hXR _))
  have hzz' : z * z ∈ rootSpan TwistTag.E6.tag K R' := by
    have h := classKill_rootSpan_inf_le_inter (S := twKillPerp J i) (T := R)
      (fun β hβ => (twKillPerp_subset hβ).1.2) twKillPerp_closed hRpos hRclosed
      (mul_mem hz hz) hzzR
    refine classKill_rootSpan_mono ?_ h
    rintro x ⟨hxP, hxR⟩
    refine ⟨hxR, fun h => ?_⟩
    have hx := not_isRoot_add_sub_of_classKillPair hi (twKill_hstr J i) hxP.1.1 hxP.1.2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl
    · exact hx.1 hδa
    · have h2 := hx.2
      rw [add_sub_cancel_right] at h2
      exact h2 hδr
  have hXN : pinnedX TwistTag.E6.tag K (δ + α) (c * d 0) ∈ rootSpan TwistTag.E6.tag K R' := by
    have e : pinnedX TwistTag.E6.tag K (δ + α) (c * d 0) =
        (z * z)⁻¹ * (z * z * pinnedX TwistTag.E6.tag K (δ + α) (c * d 0)) := by group
    rw [e]
    exact mul_mem (inv_mem hzz') hzzw
  have hcd : c * d 0 = 0 := by
    by_contra hne
    have := mem_of_pinnedX_mem_rootSpan hR'pos hR'closed hεJ.2 hne hXN
    exact this.2 (Or.inr rfl)
  have hd0 : d 0 = 0 := (mul_eq_zero.1 hcd).resolve_left hc
  have hcg : c * (d 1 * c⁻¹) = d 1 := by
    rw [mul_comm (d 1), ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  have h1k : (pinnedX TwistTag.E6.tag K (δ + α) (d 1) *
      pinnedX TwistTag.E6.tag K δ (d 1 * c⁻¹))⁻¹ *
      (A * pinnedX TwistTag.E6.tag K δ (d 1 * c⁻¹) * A) ∈ rootSpan TwistTag.E6.tag K R' := by
    have := hconjY (d 1 * c⁻¹)
    rwa [hcg] at this
  have hkill := classKill_rel_kill hNV hnorm' hAV hzV (hYV (d 1 * c⁻¹)) (hXV (d 1)) hd
    (classKill_pinnedX_mul_self _ _) h1k (hzY _) (hzX _) (hYX _ _)
  have hn2 : n = pinnedX TwistTag.E6.tag K (δ + α) (d 1) * n' := by
    rw [hn_eq, hd0, pinnedX_zero, one_mul]
  refine ⟨d 1, n', hd, hn2, ?_⟩
  rw [hn2]
  exact hkill

theorem twKill_complete [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    {J : Set (Fin TwistTag.E6.tag.rank)} (hJ : ∀ j ∈ J, TwistTag.E6.perm j ∈ J)
    {i : Fin TwistTag.E6.tag.rank} {R₁ T : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hR₁ : TwKillAdm J i R₁) (hT : ∀ β ∈ T, IsRoot TwistTag.E6.tag β)
    {A z n p₁ y n₁ : ModGL TwistTag.E6.tag K}
    (hAV : A ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J))
    (hAA : A * A = 1) (hFA : twistHom TwistTag.E6 K σ A = A)
    (hzV : z ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J))
    (hFz : twistHom TwistTag.E6 K σ z = z) (hFn : twistHom TwistTag.E6 K σ n = n)
    (hp₁ : p₁ ∈ rootSpan TwistTag.E6.tag K T)
    (hFp₁ : twistHom TwistTag.E6 K σ p₁ ∈ rootSpan TwistTag.E6.tag K R₁)
    (hcp : Commute p₁ (twistHom TwistTag.E6 K σ p₁))
    (hy : y ∈ rootSpan TwistTag.E6.tag K T)
    (hyV : y ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J))
    (hFy : twistHom TwistTag.E6 K σ y ∈ rootSpan TwistTag.E6.tag K R₁)
    (hcy : Commute y (twistHom TwistTag.E6 K σ y))
    (hn₁ : n₁ ∈ rootSpan TwistTag.E6.tag K R₁)
    (heq : A * p₁ * A * (z * n) * p₁⁻¹ = z * y * n₁) :
    ∃ n₂ ∈ rootSpan TwistTag.E6.tag K (R₁ ∩ {β | permLattice TwistTag.E6.perm β ∈ R₁}),
      twistHom TwistTag.E6 K σ n₂ = n₂ ∧
      A * (twistHom TwistTag.E6 K σ p₁ * p₁) * A * (z * n) *
          (twistHom TwistTag.E6 K σ p₁ * p₁)⁻¹ =
        z * y * twistHom TwistTag.E6 K σ y * n₂ ∧
      twistHom TwistTag.E6 K σ (twistHom TwistTag.E6 K σ p₁ * p₁) =
        twistHom TwistTag.E6 K σ p₁ * p₁ ∧
      twistHom TwistTag.E6 K σ (z * y * twistHom TwistTag.E6 K σ y) =
        z * y * twistHom TwistTag.E6 K σ y := by
  set F := twistHom TwistTag.E6 K σ with hF
  have hFFp : F (F p₁) = p₁ := twKill_FF hσσ hT hp₁
  have hFFy : F (F y) = y := twKill_FF hσσ hT hy
  have hR₁sub : R₁ ⊆ parabolicPosRoots TwistTag.E6.tag J := fun x hx => (hR₁.subset hx).1
  have hnorm : ∀ v ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J),
      ∀ m ∈ rootSpan TwistTag.E6.tag K R₁, v * m * v⁻¹ ∈ rootSpan TwistTag.E6.tag K R₁ :=
    fun v hv m hm => classKill_conj_mem hR₁sub hR₁.ideal hv hm
  have hAinv : A⁻¹ = A := inv_eq_of_mul_eq_one_right hAA
  have hAFp : A * F p₁ * A ∈ rootSpan TwistTag.E6.tag K R₁ := by
    have := hnorm A hAV (F p₁) hFp₁
    rwa [hAinv] at this
  set m := (z * y)⁻¹ * (A * F p₁ * A) * (z * y) * n₁ * (F p₁)⁻¹ with hm
  have hmR : m ∈ rootSpan TwistTag.E6.tag K R₁ := by
    refine mul_mem (mul_mem ?_ hn₁) (inv_mem hFp₁)
    have := hnorm (z * y)⁻¹ (inv_mem (mul_mem hzV hyV)) _ hAFp
    rwa [inv_inv] at this
  set n₂ := (F y)⁻¹ * m with hn₂def
  have hn₂ : n₂ ∈ rootSpan TwistTag.E6.tag K R₁ := mul_mem (inv_mem hFy) hmR
  have htw : A * (F p₁ * p₁) * A * (z * n) * (F p₁ * p₁)⁻¹ = z * y * F y * n₂ := by
    rw [← classKill_tw_comp hAA, heq, hn₂def, hm]
    group
  have hFp : F (F p₁ * p₁) = F p₁ * p₁ := by
    rw [map_mul, hFFp]
    exact hcp.eq
  have hFz' : F (z * y * F y) = z * y * F y := by
    rw [map_mul, map_mul, hFz, hFFy, mul_assoc, ← hcy.eq, ← mul_assoc]
  have hFlhs : F (A * (F p₁ * p₁) * A * (z * n) * (F p₁ * p₁)⁻¹) =
      A * (F p₁ * p₁) * A * (z * n) * (F p₁ * p₁)⁻¹ := by
    simp only [map_mul, map_inv, hFA, hFz, hFn]
    rw [← map_mul, hFp]
  have hFn₂ : F n₂ = n₂ := by
    have h1 : F (z * y * F y * n₂) = z * y * F y * n₂ := by
      rw [← htw]
      exact hFlhs
    rw [map_mul, hFz'] at h1
    exact mul_left_cancel h1
  have hR₁' := TwKillAdm.perm hJ hR₁
  have hn₂' : n₂ ∈ rootSpan TwistTag.E6.tag K {β | permLattice TwistTag.E6.perm β ∈ R₁} := by
    rw [← hFn₂]
    exact twKill_F_mem_rootSpan σ (fun β hβ => (hR₁.subset hβ).1.2.1)
      (fun β hβ => by
        show permLattice TwistTag.E6.perm (permLattice TwistTag.E6.perm β) ∈ R₁
        rw [permLattice_twistedE6_perm_perm]
        exact hβ) hn₂
  refine ⟨n₂, classKill_rootSpan_inf_le_inter (fun β hβ => (hR₁.subset hβ).1.2)
    (fun β hβ γ hγ a b ha hb hr => hR₁.ideal β (hR₁.subset hβ).1 γ hγ a b ha hb hr)
    (fun β hβ => (hR₁'.subset hβ).1.2)
    (fun β hβ γ hγ a b ha hb hr => hR₁'.ideal β (hR₁'.subset hβ).1 γ hγ a b ha hb hr)
    hn₂ hn₂', hFn₂, htw, hFp, hFz'⟩

theorem twKill_split_one {J : Set (Fin TwistTag.E6.tag.rank)} {i : Fin TwistTag.E6.tag.rank}
    {R : Set (Fin TwistTag.E6.tag.rank → ℤ)} (hR : TwKillAdm J i R)
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hδR : δ ∈ R) {n : ModGL TwistTag.E6.tag K}
    (hn : n ∈ rootSpan TwistTag.E6.tag K R) :
    ∃ d : K, (pinnedX TwistTag.E6.tag K δ d)⁻¹ * n ∈ rootSpan TwistTag.E6.tag K (R \ {δ}) := by
  obtain ⟨d, hd⟩ := classKill_split (fun β hβ => (hR.subset hβ).1.2)
    (fun β hβ γ hγ a b ha hb hr => hR.ideal β (hR.subset hβ).1 γ hγ a b ha hb hr) ![δ]
    (fun a b _ => Subsingleton.elim a b) (fun j => by fin_cases j; exact hδR) hn
  rw [Matrix.range_cons_empty] at hd
  have hprod : (List.ofFn fun j => pinnedX TwistTag.E6.tag K (![δ] j) (d j)).prod =
      pinnedX TwistTag.E6.tag K δ (d 0) := by
    rw [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
    rfl
  rw [hprod] at hd
  exact ⟨d 0, hd⟩

theorem twKill_sigma_fixed_of_eq [CharP K 2] {σ : K →+* K} {S : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hS : ∀ β ∈ S, IsRoot TwistTag.E6.tag β ∧ 0 < height β)
    (hSc : ∀ β ∈ S, ∀ γ ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot TwistTag.E6.tag (a • β + b • γ) → a • β + b • γ ∈ S)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β ∧ 0 < height β)
    (hβS : β ∉ S) {d : K} {n₁ n₁' : ModGL TwistTag.E6.tag K}
    (hn₁ : n₁ ∈ rootSpan TwistTag.E6.tag K S) (hn₁' : n₁' ∈ rootSpan TwistTag.E6.tag K S)
    (h : pinnedX TwistTag.E6.tag K β d * n₁ = pinnedX TwistTag.E6.tag K β (σ d) * n₁') :
    σ d = d := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have e : pinnedX TwistTag.E6.tag K β (d + σ d) = n₁' * n₁⁻¹ := by
    have h' : (pinnedX TwistTag.E6.tag K β (σ d))⁻¹ * pinnedX TwistTag.E6.tag K β d =
        n₁' * n₁⁻¹ := by
      calc (pinnedX TwistTag.E6.tag K β (σ d))⁻¹ * pinnedX TwistTag.E6.tag K β d
          = (pinnedX TwistTag.E6.tag K β (σ d))⁻¹ * (pinnedX TwistTag.E6.tag K β d * n₁) *
            n₁⁻¹ := by group
        _ = (pinnedX TwistTag.E6.tag K β (σ d))⁻¹ * (pinnedX TwistTag.E6.tag K β (σ d) * n₁') *
            n₁⁻¹ := by rw [h]
        _ = n₁' * n₁⁻¹ := by group
    rw [← h', pinnedX_neg, CharTwo.neg_eq, ← pinnedX_add, add_comm]
  have hmem : pinnedX TwistTag.E6.tag K β (d + σ d) ∈ rootSpan TwistTag.E6.tag K S := by
    rw [e]
    exact mul_mem hn₁' (inv_mem hn₁)
  by_contra hne
  have hne' : d + σ d ≠ 0 := fun h0 => hne (by linear_combination h0 - d * h2)
  exact hβS (mem_of_pinnedX_mem_rootSpan hS hSc hβ hne' hmem)

theorem twKill_step_perp_fixed [CharP K 2] {σ : K →+* K} {J : Set (Fin TwistTag.E6.tag.rank)}
    {i : Fin TwistTag.E6.tag.rank} {R : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hR : TwKillAdm J i R) (hRρ : ∀ β ∈ R, permLattice TwistTag.E6.perm β ∈ R)
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hmin : TwKillMin i R δ)
    (h1 : ¬IsRoot TwistTag.E6.tag (δ + Pi.single i 1))
    (h2 : ¬IsRoot TwistTag.E6.tag (δ + Pi.single (TwistTag.E6.perm i) 1))
    (hρδ : permLattice TwistTag.E6.perm δ = δ) {A : ModGL TwistTag.E6.tag K} (hAA : A * A = 1)
    {z n : ModGL TwistTag.E6.tag K} (hz : z ∈ rootSpan TwistTag.E6.tag K (twKillPerp J i))
    (hFz : twistHom TwistTag.E6 K σ z = z) (hn : n ∈ rootSpan TwistTag.E6.tag K R)
    (hFn : twistHom TwistTag.E6 K σ n = n) : TwKillStep σ J i A R z n := by
  have hδR := hmin.mem
  have hδΨ := hR.subset hδR
  have hδr : IsRoot TwistTag.E6.tag δ := hδΨ.1.2.1
  have hfin : R.Finite := (finite_setOf_isRoot _).subset fun β hβ => (hR.subset hβ).1.2.1
  have hR' := twKillAdm_sdiff_perp hR hmin h1 h2
  have hR'ρ : ∀ β ∈ R \ {δ}, permLattice TwistTag.E6.perm β ∈ R \ {δ} := fun β hβ =>
    ⟨hRρ β hβ.1, fun h => hβ.2 (by
      rw [Set.mem_singleton_iff] at h ⊢
      rw [← permLattice_twistedE6_perm_perm β, h, hρδ])⟩
  obtain ⟨d, hd⟩ := twKill_split_one hR hδR hn
  set n₁ := (pinnedX TwistTag.E6.tag K δ d)⁻¹ * n with hn₁
  have hFn₁ : twistHom TwistTag.E6 K σ n₁ = (pinnedX TwistTag.E6.tag K δ (σ d))⁻¹ * n := by
    rw [hn₁, map_mul, map_inv, twKill_F_pinnedX σ hδr, hρδ, hFn]
  have hn₁' : twistHom TwistTag.E6 K σ n₁ ∈ rootSpan TwistTag.E6.tag K (R \ {δ}) :=
    twKill_F_mem_rootSpan σ (fun β hβ => (hR'.subset hβ).1.2.1) hR'ρ hd
  have hσd : σ d = d := by
    refine twKill_sigma_fixed_of_eq (S := R \ {δ}) (fun β hβ => (hR'.subset hβ).1.2)
      (fun β hβ γ hγ a b ha hb hr => hR'.ideal β (hR'.subset hβ).1 γ hγ a b ha hb hr)
      hδΨ.1.2 (fun h => h.2 rfl) hd hn₁' ?_
    rw [hFn₁, hn₁]
    group
  refine ⟨R \ {δ}, hR', hR'ρ, Set.ncard_sdiff_singleton_lt_of_mem hδR hfin, 1, one_mem _,
    map_one _, z * pinnedX TwistTag.E6.tag K δ d,
    mul_mem hz (classKill_pinnedX_mem (twKill_mem_perp_of_min hR hmin h1 h2) d), ?_,
    n₁, hd, ?_, ?_⟩
  · rw [map_mul, hFz, twKill_F_pinnedX σ hδr, hρδ, hσd]
  · rw [hFn₁, hσd]
  · rw [hn₁]
    calc A * 1 * A * (z * n) * 1⁻¹ = (A * A) * (z * n) := by group
      _ = z * pinnedX TwistTag.E6.tag K δ d * ((pinnedX TwistTag.E6.tag K δ d)⁻¹ * n) := by
        rw [hAA]
        group

theorem twKill_step_perp_pair [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    {J : Set (Fin TwistTag.E6.tag.rank)} (hJ : ∀ j ∈ J, TwistTag.E6.perm j ∈ J)
    {i : Fin TwistTag.E6.tag.rank} {R : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hR : TwKillAdm J i R) (hRρ : ∀ β ∈ R, permLattice TwistTag.E6.perm β ∈ R)
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hmin : TwKillMin i R δ)
    (h1 : ¬IsRoot TwistTag.E6.tag (δ + Pi.single i 1))
    (h2 : ¬IsRoot TwistTag.E6.tag (δ + Pi.single (TwistTag.E6.perm i) 1))
    (hρδ : permLattice TwistTag.E6.perm δ ≠ δ) {A : ModGL TwistTag.E6.tag K}
    (hAV : A ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J))
    (hAA : A * A = 1) (hFA : twistHom TwistTag.E6 K σ A = A)
    {z n : ModGL TwistTag.E6.tag K} (hz : z ∈ rootSpan TwistTag.E6.tag K (twKillPerp J i))
    (hFz : twistHom TwistTag.E6 K σ z = z) (hn : n ∈ rootSpan TwistTag.E6.tag K R)
    (hFn : twistHom TwistTag.E6 K σ n = n) : TwKillStep σ J i A R z n := by
  have hδR := hmin.mem
  have hδΨ := hR.subset hδR
  have hδr : IsRoot TwistTag.E6.tag δ := hδΨ.1.2.1
  have hfin : R.Finite := (finite_setOf_isRoot _).subset fun β hβ => (hR.subset hβ).1.2.1
  have hR₁ := twKillAdm_sdiff_perp hR hmin h1 h2
  have hδP := twKill_mem_perp_of_min hR hmin h1 h2
  have hzV : z ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J) :=
    classKill_rootSpan_mono (fun x hx => (twKillPerp_subset hx).1) hz
  obtain ⟨d, hd⟩ := twKill_split_one hR hδR hn
  have hFy : twistHom TwistTag.E6 K σ (pinnedX TwistTag.E6.tag K δ d) ∈
      rootSpan TwistTag.E6.tag K (R \ {δ}) := by
    rw [twKill_F_pinnedX σ hδr]
    exact classKill_pinnedX_mem
      (show permLattice TwistTag.E6.perm δ ∈ R \ {δ} from ⟨hRρ δ hδR, hρδ⟩) _
  have heq : A * 1 * A * (z * n) * 1⁻¹ = z * pinnedX TwistTag.E6.tag K δ d *
      ((pinnedX TwistTag.E6.tag K δ d)⁻¹ * n) := by
    calc A * 1 * A * (z * n) * 1⁻¹ = (A * A) * (z * n) := by group
      _ = _ := by rw [hAA]; group
  obtain ⟨n₂, hn₂, hFn₂, htw, hFp, hFz'⟩ := twKill_complete hσσ hJ hR₁ (T := R)
    (fun β hβ => (hR.subset hβ).1.2.1) hAV hAA hFA hzV hFz hFn (one_mem _)
    (by rw [map_one]; exact one_mem _) (Commute.one_left _) (classKill_pinnedX_mem hδR d)
    (classKill_pinnedX_mem hδΨ.1 d) hFy
    (by rw [twKill_F_pinnedX σ hδr]; exact commute_pinnedX_permLattice_twistedE6 hδr _ _) hd heq
  refine ⟨_, TwKillAdm.inter hR₁ (TwKillAdm.perm hJ hR₁), twKill_inter_perm_stable, ?_, _, ?_,
    hFp, _, ?_, hFz', n₂, hn₂, hFn₂, htw⟩
  · exact lt_of_le_of_lt (Set.ncard_le_ncard Set.inter_subset_left
      (hfin.subset Set.sdiff_subset)) (Set.ncard_sdiff_singleton_lt_of_mem hδR hfin)
  · rw [map_one, one_mul]
    exact one_mem _
  · refine mul_mem (mul_mem hz (classKill_pinnedX_mem hδP d)) ?_
    rw [twKill_F_pinnedX σ hδr]
    exact classKill_pinnedX_mem (twKillPerp_perm hJ hδP) _

theorem twKill_string_hq2 {J : Set (Fin TwistTag.E6.tag.rank)} {i : Fin TwistTag.E6.tag.rank}
    (hi : i ∈ J) {R : Set (Fin TwistTag.E6.tag.rank → ℤ)} (hR : TwKillAdm J i R)
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hmin : TwKillMin i R δ) :
    ∀ p q : ℕ, 1 ≤ p → 2 ≤ q → IsRoot TwistTag.E6.tag (p • Pi.single i 1 + q • δ) →
      p • Pi.single i 1 + q • δ ∈ R \ {δ, δ + Pi.single i 1} := by
  intro p q hp hq hr
  have hδΨ := hR.subset hmin.mem
  obtain ⟨hδJ, hδne⟩ := hδΨ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hδne
  have h1 := one_le_twKillDeg hδJ.2.1 hδJ.2.2 hδne.1 hδne.2
  have hmem := hR.ideal _ (twKill_single_mem hi) δ hmin.mem p q hp (by omega) hr
  refine ⟨hmem, fun h => ?_⟩
  have hd : twKillDeg i (p • Pi.single i 1 + q • δ) = q * twKillDeg i δ := by
    rw [twKillDeg_add, twKillDeg_nsmul, twKillDeg_nsmul, twKillDeg_single (Or.inl rfl)]
    ring
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h
  · rw [h] at hd
    nlinarith
  · rw [h, twKillDeg_add, twKillDeg_single (Or.inl rfl), add_zero] at hd
    nlinarith

theorem twKill_step_string_fixed [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    {J : Set (Fin TwistTag.E6.tag.rank)} (hJ : ∀ j ∈ J, TwistTag.E6.perm j ∈ J)
    {i : Fin TwistTag.E6.tag.rank} (hi : i ∈ J) (hfix : TwistTag.E6.perm i = i) {c : K}
    (hc : c ≠ 0) (hcσ : σ c = c) {R : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hR : TwKillAdm J i R) (hRρ : ∀ β ∈ R, permLattice TwistTag.E6.perm β ∈ R)
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hmin : TwKillMin i R δ)
    (hδa : IsRoot TwistTag.E6.tag (δ + Pi.single i 1))
    (hρδ : permLattice TwistTag.E6.perm δ = δ)
    {z n : ModGL TwistTag.E6.tag K} (hz : z ∈ rootSpan TwistTag.E6.tag K (twKillPerp J i))
    (hFz : twistHom TwistTag.E6 K σ z = z) (hn : n ∈ rootSpan TwistTag.E6.tag K R)
    (hFn : twistHom TwistTag.E6 K σ n = n)
    (hcoc : twKillA σ i c * (z * n) * twKillA σ i c = (z * n)⁻¹) :
    TwKillStep σ J i (twKillA σ i c) R z n := by
  have hδR := hmin.mem
  have hδΨ := hR.subset hδR
  have hδr : IsRoot TwistTag.E6.tag δ := hδΨ.1.2.1
  have hfin : R.Finite := (finite_setOf_isRoot _).subset fun β hβ => (hR.subset hβ).1.2.1
  have hR₁ := twKillAdm_sdiff_string hR hmin (twKill_hstr J i) (Or.inl hfix)
  have hαfix : permLattice TwistTag.E6.perm (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) =
      Pi.single i 1 := by
    rw [twKill_perm_single, hfix]
  have hερ : permLattice TwistTag.E6.perm (δ + Pi.single i 1) = δ + Pi.single i 1 := by
    have e : permLattice TwistTag.E6.perm (δ + Pi.single i 1) =
        permLattice TwistTag.E6.perm δ + permLattice TwistTag.E6.perm (Pi.single i 1) := rfl
    rw [e, hρδ, hαfix]
  have hR₁ρ : ∀ β ∈ R \ {δ, δ + Pi.single i 1},
      permLattice TwistTag.E6.perm β ∈ R \ {δ, δ + Pi.single i 1} := fun β hβ =>
    ⟨hRρ β hβ.1, fun h => hβ.2 (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
      rcases h with h | h
      · left
        rw [← permLattice_twistedE6_perm_perm β, h, hρδ]
      · right
        rw [← permLattice_twistedE6_perm_perm β, h, hερ])⟩
  have hR₁sub : R \ {δ, δ + Pi.single i 1} ⊆ parabolicPosRoots TwistTag.E6.tag J :=
    fun x hx => (hR₁.subset hx).1
  have hnorm' : ∀ v ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J),
      ∀ m ∈ rootSpan TwistTag.E6.tag K (R \ {δ, δ + Pi.single i 1}),
        v * m * v⁻¹ ∈ rootSpan TwistTag.E6.tag K (R \ {δ, δ + Pi.single i 1}) :=
    fun v hv m hm => classKill_conj_mem hR₁sub hR₁.ideal hv hm
  obtain ⟨hconjY, hAX⟩ := twKillA_string σ hi c hnorm' hδΨ hδa
    (hmin.not_isRoot_sub hR (Or.inl rfl)) (Or.inl hfix) (twKill_string_hq2 hi hR hmin)
  obtain ⟨d₁, n', hn', hn_eq, hkill⟩ := twKill_string_core hi hR hmin hδa hR₁
    (twKillA_mem σ hJ hi c) (twKillA_mul_self σ i c) hc hconjY hAX hz
    (twKillA_comm_perp σ hJ hi c hz) hn hcoc
  have hεR : δ + Pi.single i 1 ∈ R := by
    have h := hR.ideal _ (twKill_single_mem hi) δ hδR 1 1 le_rfl le_rfl
      (by rw [one_smul, one_smul, add_comm]; exact hδa)
    rwa [one_smul, one_smul, add_comm] at h
  have hFn' : twistHom TwistTag.E6 K σ n' ∈ rootSpan TwistTag.E6.tag K (R \ {δ, δ + Pi.single i 1}) :=
    twKill_F_mem_rootSpan σ (fun β hβ => (hR₁.subset hβ).1.2.1) hR₁ρ hn'
  have hσd : σ d₁ = d₁ := by
    refine twKill_sigma_fixed_of_eq (S := R \ {δ, δ + Pi.single i 1})
      (fun β hβ => (hR₁.subset hβ).1.2)
      (fun β hβ γ hγ a b ha hb hr => hR₁.ideal β (hR₁.subset hβ).1 γ hγ a b ha hb hr)
      (hR.subset hεR).1.2 (fun h => h.2 (Or.inr rfl)) hn' hFn' ?_
    have h := congrArg (twistHom TwistTag.E6 K σ) hn_eq
    rw [hFn, map_mul, twKill_F_pinnedX σ hδa, hερ] at h
    rw [← hn_eq]
    exact h
  set p := pinnedX TwistTag.E6.tag K δ (d₁ * c⁻¹) with hp
  have hFp : twistHom TwistTag.E6 K σ p = p := by
    rw [hp, twKill_F_pinnedX σ hδr, hρδ, map_mul, map_inv₀, hσd, hcσ]
  have hFA := twKillA_F hσσ (i := i) (fun _ => hcσ)
  set n'' := z⁻¹ * (twKillA σ i c * p * twKillA σ i c * (z * n) * p⁻¹) with hn''
  have hFn'' : twistHom TwistTag.E6 K σ n'' = n'' := by
    rw [hn'']
    simp only [map_mul, map_inv, hFz, hFn, hFp, hFA]
  refine ⟨R \ {δ, δ + Pi.single i 1}, hR₁, hR₁ρ,
    Set.ncard_lt_ncard (LE.le.ssubset_of_mem_notMem Set.sdiff_subset hδR
      (fun h => h.2 (Or.inl rfl))) hfin,
    p, classKill_pinnedX_mem hδΨ _, hFp, z, hz, hFz, n'', hkill, hFn'', ?_⟩
  rw [hn'', mul_inv_cancel_left]

theorem twKill_step_string_pair [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    {J : Set (Fin TwistTag.E6.tag.rank)} (hJ : ∀ j ∈ J, TwistTag.E6.perm j ∈ J)
    {i : Fin TwistTag.E6.tag.rank} (hi : i ∈ J) {c : K} (hc : c ≠ 0)
    (hcσ : TwistTag.E6.perm i = i → σ c = c) {R : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hR : TwKillAdm J i R) (hRρ : ∀ β ∈ R, permLattice TwistTag.E6.perm β ∈ R)
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hmin : TwKillMin i R δ)
    (hδa : IsRoot TwistTag.E6.tag (δ + Pi.single i 1))
    (hb : TwistTag.E6.perm i = i ∨
      (¬IsRoot TwistTag.E6.tag (δ + Pi.single (TwistTag.E6.perm i) 1) ∧
        ¬IsRoot TwistTag.E6.tag (δ + Pi.single i 1 + Pi.single (TwistTag.E6.perm i) 1) ∧
        ¬IsRoot TwistTag.E6.tag (δ + Pi.single i 1 - Pi.single (TwistTag.E6.perm i) 1)))
    (hρδ : permLattice TwistTag.E6.perm δ ≠ δ)
    {z n : ModGL TwistTag.E6.tag K} (hz : z ∈ rootSpan TwistTag.E6.tag K (twKillPerp J i))
    (hFz : twistHom TwistTag.E6 K σ z = z) (hn : n ∈ rootSpan TwistTag.E6.tag K R)
    (hFn : twistHom TwistTag.E6 K σ n = n)
    (hcoc : twKillA σ i c * (z * n) * twKillA σ i c = (z * n)⁻¹) :
    TwKillStep σ J i (twKillA σ i c) R z n := by
  have hδR := hmin.mem
  have hδΨ := hR.subset hδR
  have hδr : IsRoot TwistTag.E6.tag δ := hδΨ.1.2.1
  have hfin : R.Finite := (finite_setOf_isRoot _).subset fun β hβ => (hR.subset hβ).1.2.1
  have hR₁ := twKillAdm_sdiff_string hR hmin (twKill_hstr J i) hb
  have hR₁sub : R \ {δ, δ + Pi.single i 1} ⊆ parabolicPosRoots TwistTag.E6.tag J :=
    fun x hx => (hR₁.subset hx).1
  have hnorm' : ∀ v ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J),
      ∀ m ∈ rootSpan TwistTag.E6.tag K (R \ {δ, δ + Pi.single i 1}),
        v * m * v⁻¹ ∈ rootSpan TwistTag.E6.tag K (R \ {δ, δ + Pi.single i 1}) :=
    fun v hv m hm => classKill_conj_mem hR₁sub hR₁.ideal hv hm
  have hzV : z ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J) :=
    classKill_rootSpan_mono (fun x hx => (twKillPerp_subset hx).1) hz
  obtain ⟨hconjY, hAX⟩ := twKillA_string σ hi c hnorm' hδΨ hδa
    (hmin.not_isRoot_sub hR (Or.inl rfl)) (hb.imp_right fun h => ⟨h.1, h.2.1⟩)
    (twKill_string_hq2 hi hR hmin)
  obtain ⟨d₁, n', -, -, hkill⟩ := twKill_string_core hi hR hmin hδa hR₁
    (twKillA_mem σ hJ hi c) (twKillA_mul_self σ i c) hc hconjY hAX hz
    (twKillA_comm_perp σ hJ hi c hz) hn hcoc
  set p₁ := pinnedX TwistTag.E6.tag K δ (d₁ * c⁻¹) with hp₁
  set n₁ := z⁻¹ * (twKillA σ i c * p₁ * twKillA σ i c * (z * n) * p₁⁻¹) with hn₁
  have hρδR₁ : permLattice TwistTag.E6.perm δ ∈ R \ {δ, δ + Pi.single i 1} := by
    refine ⟨hRρ δ hδR, fun h => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h
    · exact hρδ h
    · have h' := congrArg height h
      rw [twKill_height_perm, twKill_height_add, height_single] at h'
      omega
  have hFp₁ : twistHom TwistTag.E6 K σ p₁ ∈ rootSpan TwistTag.E6.tag K (R \ {δ, δ + Pi.single i 1}) := by
    rw [hp₁, twKill_F_pinnedX σ hδr]
    exact classKill_pinnedX_mem hρδR₁ _
  have heq : twKillA σ i c * p₁ * twKillA σ i c * (z * n) * p₁⁻¹ = z * 1 * n₁ := by
    rw [hn₁, mul_one, mul_inv_cancel_left]
  obtain ⟨n₂, hn₂, hFn₂, htw, hFp, hFz'⟩ := twKill_complete hσσ hJ hR₁ (T := R)
    (fun β hβ => (hR.subset hβ).1.2.1) (twKillA_mem σ hJ hi c) (twKillA_mul_self σ i c)
    (twKillA_F hσσ hcσ) hzV hFz hFn (classKill_pinnedX_mem hδR _) hFp₁
    (by rw [twKill_F_pinnedX σ hδr]; exact commute_pinnedX_permLattice_twistedE6 hδr _ _)
    (one_mem _) (one_mem _) (by rw [map_one]; exact one_mem _) (Commute.one_left _) hkill heq
  refine ⟨_, TwKillAdm.inter hR₁ (TwKillAdm.perm hJ hR₁), twKill_inter_perm_stable, ?_, _, ?_,
    hFp, _, ?_, hFz', n₂, hn₂, hFn₂, htw⟩
  · exact lt_of_le_of_lt (Set.ncard_le_ncard Set.inter_subset_left
      (hfin.subset Set.sdiff_subset)) (Set.ncard_lt_ncard (LE.le.ssubset_of_mem_notMem
        Set.sdiff_subset hδR (fun h => h.2 (Or.inl rfl))) hfin)
  · refine mul_mem ?_ (classKill_pinnedX_mem hδΨ _)
    rw [twKill_F_pinnedX σ hδr]
    exact classKill_pinnedX_mem (twKill_perm_mem_sdiff hJ hδΨ) _
  · rw [map_one, mul_one, mul_one]
    exact hz

end CFSG.SeitzReduction
