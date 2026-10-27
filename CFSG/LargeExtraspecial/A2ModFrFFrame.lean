module

public import CFSG.LargeExtraspecial.A2ModFrFRoots
public import CFSG.LargeExtraspecial.A2ModCfgARS

public section

namespace CFSG.LargeExtraspecial.A2Mod.FrF

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.ExclNS
open scoped commutatorElement

abbrev f4D {K : Type} [Group K] (hA : TauCeti.IsFiniteType f4M) (X : (Fin 4 → ℤ) → Subgroup K) :
    UniversalRootDatum K where
  rank := 4
  cartan := f4M
  isFiniteType := hA
  divisible := ∅
  rootGroup := X

structure F4Frame (G : Type) [Group G] (R : Set (Subgroup G)) where
  K : Type
  [grp : Group K]
  hA : TauCeti.IsFiniteType f4M
  X : (Fin 4 → ℤ) → Subgroup K
  n : Fin 4 → K
  H : Fin 4 → Subgroup K
  hct : IsCTGroupDatum (coxeterMatrix (f4D hA X).isFiniteType).toCoxeterSystem
    (weylAction (f4D hA X).isFiniteType) (f4D hA X).roots (f4D hA X).rootGroup n H
  hext : SteinbergExtras (f4D hA X) n H
  i₀ : Fin 4
  hi₀ : i₀.val < 2
  pgroup : ∀ γ ∈ (f4D hA X).roots, IsPGroup 2 (X γ)
  Ψ : K →* G
  surj : Function.Surjective Ψ
  ker : Ψ.ker ≤ Subgroup.center K
  mem : (X (Pi.single i₀ 1)).map Ψ ∈ R
  opp : Opposite ((X (Pi.single i₀ 1)).map Ψ) ((X (-Pi.single i₀ 1)).map Ψ)

attribute [instance] F4Frame.grp

namespace F4Frame

variable {G : Type} [Group G] {R : Set (Subgroup G)} (F : F4Frame G R)

abbrev D : UniversalRootDatum F.K := f4D F.hA F.X

abbrev s (k : Fin 4) : (coxeterMatrix F.hA).Group := (coxeterMatrix F.hA).toCoxeterSystem.simple k

@[expose] def IsLong (γ : Fin 4 → ℤ) : Prop :=
  ∃ w : (coxeterMatrix F.hA).Group, γ = weylAction F.hA w (Pi.single F.i₀ 1)

variable {F}

theorem IsLong.mem_roots {γ : Fin 4 → ℤ} (h : F.IsLong γ) : γ ∈ roots F.hA ∅ := by
  obtain ⟨w, rfl⟩ := h
  exact Or.inl ⟨w, F.i₀, rfl⟩

theorem IsLong.weylAction {γ : Fin 4 → ℤ} (h : F.IsLong γ) (w : (coxeterMatrix F.hA).Group) :
    F.IsLong (CFSG.LieType.RootSystem.weylAction F.hA w γ) := by
  obtain ⟨w', rfl⟩ := h
  exact ⟨w * w', by rw [weylAction_mul_apply]⟩

theorem IsLong.reflF {γ : Fin 4 → ℤ} (h : F.IsLong γ) (k : Fin 4) {v : Fin 4 → ℤ}
    (hv : reflF f4M k γ = v) : F.IsLong v := by
  rw [← hv, ← weylAction_simple_eq F.hA]
  exact h.weylAction _

theorem IsLong.neg {γ : Fin 4 → ℤ} (h : F.IsLong γ) : F.IsLong (-γ) := by
  obtain ⟨w, rfl⟩ := h
  refine ⟨w * F.s F.i₀, ?_⟩
  rw [weylAction_mul_apply, weylAction_simple_single, map_neg]

variable (F) in
theorem i₀_eq : F.i₀ = 0 ∨ F.i₀ = 1 := by
  have h := F.hi₀
  generalize F.i₀ = i at h ⊢
  fin_cases i <;> simp at h ⊢

theorem IsLong.form {γ : Fin 4 → ℤ} (h : F.IsLong γ) : (form F.hA).Q γ γ = 4 := by
  obtain ⟨w, rfl⟩ := h
  rw [form_weylAction_single]
  rcases F.i₀_eq with h | h <;> rw [h] <;> decide

theorem isLong_single_zero : F.IsLong (Pi.single 0 1) := by
  rcases F.i₀_eq with h | h
  · exact ⟨1, by rw [h, map_one, Module.End.one_apply]⟩
  · refine ⟨F.s 1 * F.s 0, ?_⟩
    rw [h, weylAction_mul_apply, weylAction_simple_eq, weylAction_simple_eq]
    decide

theorem isLong_single_one : F.IsLong (Pi.single 1 1) := by
  rcases F.i₀_eq with h | h
  · refine ⟨F.s 0 * F.s 1, ?_⟩
    rw [h, weylAction_mul_apply, weylAction_simple_eq, weylAction_simple_eq]
    decide
  · exact ⟨1, by rw [h, map_one, Module.End.one_apply]⟩

theorem actsAs_nrep (w : (coxeterMatrix F.hA).Group) : ActsAs F.D (nrep F.hct w) w :=
  CFSG.LieType.Steinberg.actsAs_nrep F.hct w

theorem rootGroup_weylAction (w : (coxeterMatrix F.hA).Group) {γ : Fin 4 → ℤ}
    (hγ : γ ∈ roots F.hA ∅) :
    F.X (weylAction F.hA w γ) = conjSub (F.X γ) (nrep F.hct w) :=
  ((actsAs_nrep w) γ hγ).symm

theorem rootGroup_single_inf_center (i : Fin 4) :
    F.X (Pi.single i 1) ⊓ Subgroup.center F.K = ⊥ := by
  refine eq_bot_iff.mpr fun u hu => ?_
  obtain ⟨hu, hc⟩ := Subgroup.mem_inf.mp hu
  refine (Subgroup.mem_bot).mpr (F.hext.eq_one_of_mem_normalizer i u hu ?_)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [← Subgroup.mem_center_iff.mp hc h, mul_inv_cancel_right]

theorem rootGroup_inf_center {γ : Fin 4 → ℤ} (hγ : γ ∈ roots F.hA ∅) :
    F.X γ ⊓ Subgroup.center F.K = ⊥ := by
  obtain ⟨w, i, rfl⟩ := exists_eq_weylAction_single (D := F.D) rfl hγ
  rw [rootGroup_weylAction w ((RootSystem.ofCartan F.hA ∅).single_mem i)]
  refine eq_bot_iff.mpr fun u hu => ?_
  obtain ⟨⟨v, hv, rfl⟩, hc⟩ := Subgroup.mem_inf.mp hu
  set n := nrep F.hct w
  have hcn := Subgroup.mem_center_iff.mp hc n
  change n * (n * v * n⁻¹) = n * v * n⁻¹ * n at hcn
  have hvc : n * v * n⁻¹ = v := by
    have h1 : n * v * n⁻¹ * n = n * v := by group
    rw [h1] at hcn
    exact mul_left_cancel hcn
  have hv' : v ∈ F.X (Pi.single i 1) ⊓ Subgroup.center F.K := by
    refine Subgroup.mem_inf.mpr ⟨hv, ?_⟩
    have hc' : n * v * n⁻¹ ∈ Subgroup.center F.K := hc
    rwa [hvc] at hc'
  rw [rootGroup_single_inf_center, Subgroup.mem_bot] at hv'
  rw [hv', map_one, Subgroup.mem_bot]

theorem eq_of_map_eq {γ : Fin 4 → ℤ} (hγ : γ ∈ roots F.hA ∅) {x y : F.K} (hx : x ∈ F.X γ)
    (hy : y ∈ F.X γ) (h : F.Ψ x = F.Ψ y) : x = y := by
  have hxy : x * y⁻¹ ∈ F.X γ ⊓ Subgroup.center F.K :=
    Subgroup.mem_inf.mpr ⟨mul_mem hx (inv_mem hy), F.ker (by rw [MonoidHom.mem_ker, map_mul,
      map_inv, h, mul_inv_cancel])⟩
  rw [rootGroup_inf_center hγ, Subgroup.mem_bot, mul_inv_eq_one] at hxy
  exact hxy

theorem exists_ne_one {γ : Fin 4 → ℤ} (hγ : γ ∈ roots F.hA ∅) : ∃ x ∈ F.X γ, x ≠ 1 := by
  obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (F.hext.ne_bot γ hγ)
  exact ⟨x, hx, fun h => hx1 (Subtype.ext h)⟩

variable (F) in
open Classical in
noncomputable def xL (γ : Fin 4 → ℤ) : F.K :=
  if h : ∃ x ∈ F.X γ, x ≠ 1 then h.choose else 1

theorem xL_mem {γ : Fin 4 → ℤ} (hγ : γ ∈ roots F.hA ∅) : F.xL γ ∈ F.X γ := by
  unfold xL
  split_ifs with h
  · exact h.choose_spec.1
  · exact absurd (exists_ne_one hγ) h

theorem xL_ne_one {γ : Fin 4 → ℤ} (hγ : γ ∈ roots F.hA ∅) : F.xL γ ≠ 1 := by
  unfold xL
  split_ifs with h
  · exact h.choose_spec.2
  · exact absurd (exists_ne_one hγ) h

variable {D : Set G} (hR : IsRootClass R) (hRD : ∀ E ∈ R, ∃ d ∈ D, E = Subgroup.zpowers d)
include hR

theorem map_rootGroup_mem {γ : Fin 4 → ℤ} (h : F.IsLong γ) : (F.X γ).map F.Ψ ∈ R := by
  obtain ⟨w, rfl⟩ := h
  rw [rootGroup_weylAction w ((RootSystem.ofCartan F.hA ∅).single_mem F.i₀), ← map_conjSub_eq]
  exact hR.conjSub_mem F.mem _

include hRD

theorem exists_map_xL {γ : Fin 4 → ℤ} (h : F.IsLong γ) :
    ∃ d ∈ D, (F.X γ).map F.Ψ = Subgroup.zpowers d ∧ d * d = 1 ∧ F.Ψ (F.xL γ) = d := by
  obtain ⟨d, hd, hE⟩ := hRD _ (map_rootGroup_mem hR h)
  have hdd := (mul_self_and_ne_one_of_mem hR (map_rootGroup_mem hR h) hE).1
  refine ⟨d, hd, hE, hdd, eq_of_mem_zpowers hdd ?_ fun h1 => ?_⟩
  · exact hE ▸ Subgroup.mem_map_of_mem F.Ψ (xL_mem h.mem_roots)
  · exact xL_ne_one h.mem_roots (eq_of_map_eq h.mem_roots (xL_mem h.mem_roots) (one_mem _)
      (h1.trans (map_one _).symm))

theorem map_xL_mem {γ : Fin 4 → ℤ} (h : F.IsLong γ) : F.Ψ (F.xL γ) ∈ D := by
  obtain ⟨d, hd, -, -, he⟩ := exists_map_xL hR hRD h
  exact he ▸ hd

theorem eq_xL {γ : Fin 4 → ℤ} (h : F.IsLong γ) {x : F.K} (hx : x ∈ F.X γ) (hx1 : x ≠ 1) :
    x = F.xL γ := by
  obtain ⟨d, -, hE, hdd, he⟩ := exists_map_xL hR hRD h
  refine eq_of_map_eq h.mem_roots hx (xL_mem h.mem_roots) ?_
  rw [he]
  refine eq_of_mem_zpowers hdd (hE ▸ Subgroup.mem_map_of_mem F.Ψ hx) fun h1 => hx1 ?_
  exact eq_of_map_eq h.mem_roots hx (one_mem _) (h1.trans (map_one _).symm)

theorem mem_rootGroup_iff {γ : Fin 4 → ℤ} (h : F.IsLong γ) {x : F.K} :
    x ∈ F.X γ ↔ x = 1 ∨ x = F.xL γ := by
  refine ⟨fun hx => ?_, ?_⟩
  · by_cases hx1 : x = 1
    · exact Or.inl hx1
    · exact Or.inr (eq_xL hR hRD h hx hx1)
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact xL_mem h.mem_roots

theorem xL_mul_self {γ : Fin 4 → ℤ} (h : F.IsLong γ) : F.xL γ * F.xL γ = 1 := by
  obtain ⟨d, -, -, hdd, he⟩ := exists_map_xL hR hRD h
  refine eq_of_map_eq h.mem_roots (mul_mem (xL_mem h.mem_roots) (xL_mem h.mem_roots))
    (one_mem _) ?_
  rw [map_mul, he, hdd, map_one]

theorem rootGroup_eq_zpowers {γ : Fin 4 → ℤ} (h : F.IsLong γ) :
    F.X γ = Subgroup.zpowers (F.xL γ) := by
  refine le_antisymm (fun x hx => ?_) ((Subgroup.zpowers_le).mpr (xL_mem h.mem_roots))
  rcases (mem_rootGroup_iff hR hRD h).1 hx with rfl | rfl
  · exact one_mem _
  · exact Subgroup.mem_zpowers _

theorem map_rootGroup_eq {γ : Fin 4 → ℤ} (h : F.IsLong γ) :
    (F.X γ).map F.Ψ = Subgroup.zpowers (F.Ψ (F.xL γ)) := by
  rw [rootGroup_eq_zpowers hR hRD h, MonoidHom.map_zpowers]

theorem conj_xL {x : F.K} {w : (coxeterMatrix F.hA).Group} (hx : ActsAs F.D x w)
    {γ : Fin 4 → ℤ} (h : F.IsLong γ) : x * F.xL γ * x⁻¹ = F.xL (weylAction F.hA w γ) := by
  refine eq_xL hR hRD (h.weylAction w) (hx.conj_mem h.mem_roots (xL_mem h.mem_roots)) ?_
  intro h1
  rw [conj_eq_one_iff] at h1
  exact xL_ne_one h.mem_roots h1

omit hR hRD in
theorem commuting_of_cone {γ δ : Fin 4 → ℤ} (hγ : γ ∈ roots F.hA ∅) (hδ : δ ∈ roots F.hA ∅)
    (hind : LinIndepPair γ δ)
    (hcone : ∀ ε ∈ roots F.hA ∅, ¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ε = a • γ + b • δ) :
    Commuting (F.X γ) (F.X δ) :=
  commuting_of_forall_notMem_openCone (D := F.D) F.hext hγ hδ hind hcone

omit hR hRD in
theorem commuting_of_form {γ δ : Fin 4 → ℤ} (hγ : γ ∈ roots F.hA ∅) (hδ : δ ∈ roots F.hA ∅)
    (h1 : δ ≠ γ) (h2 : δ ≠ -γ) (hg : 0 ≤ (form F.hA).Q γ γ) (hd : 0 ≤ (form F.hA).Q δ δ)
    (hc : 0 ≤ (form F.hA).Q γ δ)
    (h : 4 < (form F.hA).Q γ γ + (form F.hA).Q δ δ + 2 * (form F.hA).Q γ δ) :
    Commuting (F.X γ) (F.X δ) :=
  commuting_of_cone hγ hδ (linIndepPair_of_ne F.hA hγ hδ h1 h2)
    (forall_notMem_openCone_of_nonneg F.hA hg hd hc h)

omit hR hRD in
theorem commuting_long {γ δ : Fin 4 → ℤ} (hγ : F.IsLong γ) (hδ : F.IsLong δ)
    (hc : 0 ≤ (form F.hA).Q γ δ) (hne : δ ≠ γ) : Commuting (F.X γ) (F.X δ) := by
  refine commuting_of_form hγ.mem_roots hδ.mem_roots hne (fun e => ?_) (by rw [hγ.form]; norm_num)
    (by rw [hδ.form]; norm_num) hc (by rw [hγ.form, hδ.form]; linarith)
  rw [e, form_neg_right F.hA, hγ.form] at hc
  norm_num at hc

omit hR hRD in
theorem commute_xL {γ δ : Fin 4 → ℤ} (hγ : F.IsLong γ) (hδ : F.IsLong δ)
    (hc : 0 ≤ (form F.hA).Q γ δ) (hne : δ ≠ γ) : Commute (F.xL γ) (F.xL δ) :=
  commuting_long hγ hδ hc hne _ (xL_mem hγ.mem_roots) _ (xL_mem hδ.mem_roots)

theorem commutator_xL {γ δ : Fin 4 → ℤ} (hγ : F.IsLong γ) (hδ : F.IsLong δ)
    (hγδ : F.IsLong (γ + δ)) (hc : (form F.hA).Q γ δ = -2) :
    ⁅F.xL γ, F.xL δ⁆ = F.xL (γ + δ) := by
  have hg := hγ.form
  have hd := hδ.form
  have hind : LinIndepPair γ δ := by
    refine linIndepPair_of_ne F.hA hγ.mem_roots hδ.mem_roots (fun e => ?_) (fun e => ?_)
    · rw [e, hg] at hc
      norm_num at hc
    · rw [e, form_neg_right F.hA, hg] at hc
      norm_num at hc
  have hmem := F.hext.commutator_mem γ hγ.mem_roots δ hδ.mem_roots hind _ (xL_mem hγ.mem_roots)
    _ (xL_mem hδ.mem_roots)
  have hle : (⨆ ε ∈ openCone F.D.roots γ δ, F.D.rootGroup ε) ≤ F.X (γ + δ) :=
    iSup₂_le fun ε hε => by rw [eq_add_of_mem_openCone_long F.hA hg hd hc hε]
  refine eq_xL hR hRD hγδ (hle hmem) fun h1 => ?_
  have hcomm : Commuting (F.X γ) (F.X δ) := by
    intro x hx y hy
    rcases (mem_rootGroup_iff hR hRD hγ).1 hx with rfl | rfl
    · exact Commute.one_left _
    rcases (mem_rootGroup_iff hR hRD hδ).1 hy with rfl | rfl
    · exact Commute.one_right _
    exact commutatorElement_eq_one_iff_commute.1 h1
  obtain ⟨w, hw⟩ := id hγ
  have hcδγ : (form F.hA).Q δ (-γ) = 2 := by
    rw [form_neg_right F.hA, (form F.hA).symm, hc]
    norm_num
  have hgn : (form F.hA).Q (-γ) (-γ) = 4 := by
    rw [form_neg_left F.hA, form_neg_right F.hA, hg]; ring
  refine false_of_commuting (D := F.D) F.hct F.hext rfl hγ.mem_roots hδ.mem_roots hcomm ?_
    (forall_notMem_openCone_of_nonneg F.hA (by rw [hd]; norm_num) (by rw [hgn]; norm_num)
      (by rw [hcδγ]; norm_num) (by rw [hd, hgn, hcδγ]; norm_num)) hw.symm
    ((form F.hA).reflection_ne F.hA ?_)
  · refine linIndepPair_of_ne F.hA hδ.mem_roots hγ.neg.mem_roots (fun e => ?_) (fun e => ?_)
    · rw [e, hd] at hcδγ
      norm_num at hcδγ
    · rw [neg_inj] at e
      rw [e, hd] at hc
      norm_num at hc
  · rw [← hw, (form F.hA).symm, hc]
    norm_num

theorem xL_mul_xL_eq_conj {η δ : Fin 4 → ℤ} (hη : F.IsLong η) (hδ : F.IsLong δ)
    (hηδ : F.IsLong (η + δ)) (hc : (form F.hA).Q η δ = -2) :
    F.xL (η + δ) * F.xL δ = F.xL η * F.xL δ * (F.xL η)⁻¹ := by
  rw [← commutator_xL hR hRD hη hδ hηδ hc, commutatorElement_def, inv_mul_cancel_right]

omit hR hRD in
theorem opposite_map {γ : Fin 4 → ℤ} (h : F.IsLong γ) :
    Opposite ((F.X γ).map F.Ψ) ((F.X (-γ)).map F.Ψ) := by
  obtain ⟨w, rfl⟩ := h
  have hα := (RootSystem.ofCartan F.hA ∅).single_mem F.i₀
  have hα' := (RootSystem.ofCartan F.hA ∅).neg_mem _ hα
  rw [← map_neg, rootGroup_weylAction w hα, rootGroup_weylAction w hα', ← map_conjSub_eq,
    ← map_conjSub_eq]
  exact F.opp.conj _

variable (F) in
noncomputable abbrev lr (γ : Fin 4 → ℤ) : G := F.Ψ (F.xL γ)

theorem lr_mem {γ : Fin 4 → ℤ} (h : F.IsLong γ) : F.lr γ ∈ D :=
  map_xL_mem hR hRD h

theorem lr_mul_self {γ : Fin 4 → ℤ} (h : F.IsLong γ) : F.lr γ * F.lr γ = 1 := by
  rw [← map_mul, xL_mul_self hR hRD h, map_one]

omit hR hRD in
theorem lr_ne_one {γ : Fin 4 → ℤ} (h : F.IsLong γ) : F.lr γ ≠ 1 := fun h1 =>
  xL_ne_one h.mem_roots (eq_of_map_eq h.mem_roots (xL_mem h.mem_roots) (one_mem _)
    (h1.trans (map_one _).symm))

theorem map_rootGroup_eq_lr {γ : Fin 4 → ℤ} (h : F.IsLong γ) :
    (F.X γ).map F.Ψ = Subgroup.zpowers (F.lr γ) :=
  map_rootGroup_eq hR hRD h

omit hR hRD in
theorem commute_lr {γ δ : Fin 4 → ℤ} (hγ : F.IsLong γ) (hδ : F.IsLong δ)
    (hc : 0 ≤ (form F.hA).Q γ δ) (hne : δ ≠ γ) : Commute (F.lr γ) (F.lr δ) :=
  (commute_xL hγ hδ hc hne).map F.Ψ

theorem commutator_lr {γ δ : Fin 4 → ℤ} (hγ : F.IsLong γ) (hδ : F.IsLong δ)
    (hγδ : F.IsLong (γ + δ)) (hc : (form F.hA).Q γ δ = -2) :
    ⁅F.lr γ, F.lr δ⁆ = F.lr (γ + δ) := by
  rw [← map_commutatorElement, commutator_xL hR hRD hγ hδ hγδ hc]

theorem mul_lr_mem (hDc : ∀ g, ∀ d ∈ D, g * d * g⁻¹ ∈ D) {η δ : Fin 4 → ℤ} (hη : F.IsLong η)
    (hδ : F.IsLong δ) (hηδ : F.IsLong (η + δ)) (hc : (form F.hA).Q η δ = -2) :
    F.lr (η + δ) * F.lr δ ∈ D := by
  rw [← map_mul, xL_mul_xL_eq_conj hR hRD hη hδ hηδ hc, map_mul, map_mul, map_inv]
  exact hDc _ _ (lr_mem hR hRD hδ)

end F4Frame

end CFSG.LargeExtraspecial.A2Mod.FrF
