module

public import CFSG.LieType.Steinberg.TwistedD4.Local
public import CFSG.LieType.Steinberg.TwistedE6.Unipotent
public import CFSG.LieType.Chevalley.TwistPerfect

public noncomputable section

namespace CFSG.LieType.Steinberg.TwistedD4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
open CFSG.LieType.Steinberg.Adjoint CFSG.LieType.CurtisTits

open _root_.Classical in
@[expose] def liftRoot (β : Fin (Tag.rank .G2) → ℤ) : Fin d4.rank → ℤ :=
  if h : ∃ α, IsRoot d4 α ∧ proj α = β then h.choose else 0

theorem liftRoot_spec
    {β : Fin (Tag.rank .G2) → ℤ} (hβ : IsRoot .G2 β) :
    IsRoot d4 (liftRoot β) ∧ proj (liftRoot β) = β := by
  classical
  have h := exists_proj_eq hβ
  rw [liftRoot, dite_eq_left h]
  exact h.choose_spec

open _root_.Classical in
@[expose] def fibreList (β : Fin (Tag.rank .G2) → ℤ) : List (Fin d4.rank → ℤ) :=
  if rho (liftRoot β) = liftRoot β then [liftRoot β]
  else [liftRoot β, rho (liftRoot β), rho (rho (liftRoot β))]

theorem mem_fibreList {β : Fin (Tag.rank .G2) → ℤ} (hβ : IsRoot .G2 β)
    {γ : Fin d4.rank → ℤ} (hγ : γ ∈ fibreList β) : IsRoot d4 γ ∧ proj γ = β := by
  obtain ⟨hα, hp⟩ := liftRoot_spec hβ
  unfold fibreList at hγ
  split_ifs at hγ with h
  · rw [List.mem_singleton] at hγ
    subst hγ
    exact ⟨hα, hp⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl | rfl
    · exact ⟨hα, hp⟩
    · exact ⟨isRoot_rho hα, by rw [proj_rho, hp]⟩
    · exact ⟨isRoot_rho (isRoot_rho hα), by rw [proj_rho, proj_rho, hp]⟩

theorem nodup_fibreList
    (β : Fin (Tag.rank .G2) → ℤ) : (fibreList β).Nodup := by
  unfold fibreList
  split_ifs with h
  · exact List.nodup_singleton _
  · simp [List.nodup_cons, Ne.symm h, Ne.symm (rho_rho_ne h), Ne.symm (rho_rho_ne_rho h)]

variable {K : Type} [Field K] (σ : K →+* K)

local notation "𝕏" => rootGroup (rootOperatorFamily d4) K

local notation "𝕩" => xPar (rootOperatorFamily d4)

theorem exists_decomp_fibreList
    {β : Fin (Tag.rank .G2) → ℤ} (hβ : IsRoot .G2 β)
    {y : adjointGroup d4 K} (hy : y ∈ twistedRootSubgroupD4 σ β) :
    ∃ φ : (Fin d4.rank → ℤ) → adjointGroup d4 K,
      (∀ α ∈ fibreList β, φ α ∈ 𝕏 α) ∧ y = ((fibreList β).map φ).prod := by
  classical
  obtain ⟨hα, hp⟩ := liftRoot_spec hβ
  have hy' := twistedRootSubgroupD4_le σ hα hp hy
  unfold fibreList
  split_ifs with h
  · rw [h, h, sup_idem, sup_idem] at hy'
    refine ⟨fun _ => y, fun α hα' => ?_, ?_⟩
    · rw [List.mem_singleton] at hα'
      subst hα'
      exact hy'
    · rw [List.map_singleton, List.prod_singleton]
  · obtain ⟨c, d, f, rfl⟩ := (mem_sup_rho_iff hα h).1 hy'
    have hne1 := rho_rho_ne h
    have hne2 := rho_rho_ne_rho h
    refine ⟨fun γ => if γ = liftRoot β then 𝕩 (liftRoot β) c
      else if γ = rho (liftRoot β) then 𝕩 (rho (liftRoot β)) d
      else 𝕩 (rho (rho (liftRoot β))) f, fun γ hγ => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
      rcases hγ with rfl | rfl | rfl
      · simp only [ite_true]
        exact xPar_mem hα c
      · simp only [h, ite_false, ite_true]
        exact xPar_mem (isRoot_rho hα) d
      · simp only [hne1, hne2, ite_false]
        exact xPar_mem (isRoot_rho (isRoot_rho hα)) f
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ite_true,
        h, hne1, hne2, ite_false, ← mul_assoc]

theorem prodInjective_twisted
    (η : ℤ) (L : List (Fin (Tag.rank .G2) → ℤ)) (hnd : L.Nodup)
    (hL : ∀ β ∈ L, IsRoot .G2 β ∧ 0 < η * ht β)
    (hsort : L.Pairwise fun β δ => η * ht β ≤ η * ht δ) :
    ProdInjectiveFor (twistedRootGroup σ) L := by
  have hmem : ∀ β ∈ L, ∀ γ ∈ fibreList β, IsRoot d4 γ ∧ proj γ = β :=
    fun β hβ γ hγ => mem_fibreList (hL β hβ).1 hγ
  have hht : ∀ β ∈ L, ∀ γ ∈ fibreList β, ht γ = ht β := fun β hβ γ hγ => by
    rw [← ht_proj, (hmem β hβ γ hγ).2]
  have hnd' : (L.flatMap fibreList).Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun β _ => nodup_fibreList β, hnd.imp_of_mem fun {β δ} hβ hδ hne => ?_⟩
    intro γ h1 h2
    exact hne ((hmem β hβ γ h1).2.symm.trans (hmem δ hδ γ h2).2)
  set φ : (Fin d4.rank → ℤ) →+ ℤ := η • htHom with hφ
  have hφv : ∀ v, φ v = η * ht v := fun v => by
    rw [hφ, AddMonoidHom.smul_apply, htHom_apply, smul_eq_mul]
  refine TwistedE6.prodInjectiveFor_of_flatMap (twistedGroup σ).subtype Subtype.val_injective
    (fun β hβ y hy => exists_decomp_fibreList σ (hL β hβ).1 hy) hnd' ?_
  refine prodInjective (F := rootOperatorFamily d4) (K := K) φ _ hnd' (fun γ hγ => ?_) ?_
  · obtain ⟨β, hβ, hγβ⟩ := List.mem_flatMap.1 hγ
    exact ⟨(hmem β hβ γ hγβ).1, by rw [hφv, hht β hβ γ hγβ]; exact (hL β hβ).2⟩
  · rw [List.pairwise_flatMap]
    refine ⟨fun β hβ => (nodup_fibreList β).imp_of_mem fun {γ δ} hγ hδ _ => ?_,
      hsort.imp_of_mem fun {β δ} hβ hδ h => fun x hx y hy => ?_⟩
    · rw [hφv, hφv, hht β hβ γ hγ, hht β hβ δ hδ]
    · rw [hφv, hφv, hht β hβ x hx, hht δ hδ y hy]
      exact h

theorem iSup_twistedRootGroup_le
    (P : ℤ → Prop) :
    (⨆ β ∈ {β : Fin (Tag.rank .G2) → ℤ | IsRoot .G2 β ∧ P (ht β)}, twistedRootGroup σ β) ≤
      (⨆ γ ∈ {γ : Fin d4.rank → ℤ | IsRoot d4 γ ∧ P (ht γ)}, 𝕏 γ).comap
        (twistedGroup σ).subtype := by
  refine iSup₂_le fun β hβ x hx => ?_
  obtain ⟨α, hα, hp⟩ := exists_proj_eq hβ.1
  have hx' := twistedRootSubgroupD4_le σ hα hp hx
  rw [Subgroup.mem_comap, Subgroup.coe_subtype]
  have hP : ∀ γ : Fin d4.rank → ℤ, IsRoot d4 γ → proj γ = β → 𝕏 γ ≤
      ⨆ γ ∈ {γ : Fin d4.rank → ℤ | IsRoot d4 γ ∧ P (ht γ)}, 𝕏 γ := fun γ hγ hpγ =>
    le_iSup₂_of_le (f := fun γ (_ : γ ∈ {γ : Fin d4.rank → ℤ | IsRoot d4 γ ∧ P (ht γ)}) => 𝕏 γ)
      γ ⟨hγ, by rw [← ht_proj, hpγ]; exact hβ.2⟩ le_rfl
  exact sup_le (sup_le (hP α hα hp) (hP _ (isRoot_rho hα) (by rw [proj_rho, hp])))
    (hP _ (isRoot_rho (isRoot_rho hα)) (by rw [proj_rho, proj_rho, hp])) hx'

theorem iSup_rootGroup_le_unip
    (η : ℤ) :
    (⨆ γ ∈ {γ : Fin d4.rank → ℤ | IsRoot d4 γ ∧ 0 < η * ht γ}, 𝕏 γ) ≤
      unip (K := K) (η • htHom) :=
  iSup₂_le fun γ hγ => rootGroup_le_unip _ (by
    rw [AddMonoidHom.smul_apply, htHom_apply, smul_eq_mul]
    exact hγ.2)

theorem posPart_inf_negPart_twisted :
    (⨆ β ∈ {β : Fin (Tag.rank .G2) → ℤ | IsRoot .G2 β ∧ 0 < ht β}, twistedRootGroup σ β) ⊓
      (⨆ β ∈ {β : Fin (Tag.rank .G2) → ℤ | IsRoot .G2 β ∧ ht β < 0}, twistedRootGroup σ β) =
        ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_inf] at hg
  have h1 : (g : adjointGroup d4 K) ∈ unip (K := K) ((1 : ℤ) • htHom) := by
    refine iSup_rootGroup_le_unip 1 ?_
    have := iSup_twistedRootGroup_le σ (fun h => 0 < h) hg.1
    refine (iSup₂_le fun γ hγ => ?_ : (⨆ γ ∈ {γ : Fin d4.rank → ℤ | IsRoot d4 γ ∧ 0 < ht γ},
      𝕏 γ) ≤ _) this
    exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ {γ : Fin d4.rank → ℤ | IsRoot d4 γ ∧
      0 < 1 * ht γ}) => 𝕏 γ) γ ⟨hγ.1, by rw [one_mul]; exact hγ.2⟩ le_rfl
  have h2 : (g : adjointGroup d4 K) ∈ unip (K := K) ((-1 : ℤ) • htHom) := by
    refine iSup_rootGroup_le_unip (-1) ?_
    have := iSup_twistedRootGroup_le σ (fun h => h < 0) hg.2
    refine (iSup₂_le fun γ hγ => ?_ : (⨆ γ ∈ {γ : Fin d4.rank → ℤ | IsRoot d4 γ ∧ ht γ < 0},
      𝕏 γ) ≤ _) this
    exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ {γ : Fin d4.rank → ℤ | IsRoot d4 γ ∧
      0 < -1 * ht γ}) => 𝕏 γ) γ ⟨hγ.1, by linarith [hγ.2]⟩ le_rfl
  rw [one_smul] at h1
  rw [neg_one_smul] at h2
  have h := Subgroup.mem_inf.2 ⟨h1, h2⟩
  rw [unip_inf_unip_neg, Subgroup.mem_bot] at h
  exact Subgroup.mem_bot.2 (Subtype.ext h)

theorem hHatE_le_iSup_torus
    (i : Fin (Tag.rank .G2)) :
    hHatE σ i ≤ ⨆ a, Adjoint.torus (τ := d4) K a := by
  have hm : ∀ (a : Fin d4.rank) (t : Kˣ),
      torusElement d4 K a t ∈ ⨆ a, Adjoint.torus (τ := d4) K a :=
    fun a t => Subgroup.mem_iSup_of_mem a ⟨t, rfl⟩
  match i with
  | ⟨0, _⟩ =>
    rintro _ ⟨t, rfl⟩
    exact hm _ _
  | ⟨1, _⟩ =>
    rintro _ ⟨t, rfl⟩
    exact mul_mem (mul_mem (hm _ _) (hm _ _)) (hm _ _)

theorem torus_inf_posPart_twisted :
    (⨆ i, hHat σ i) ⊓
      (⨆ β ∈ {β : Fin (Tag.rank .G2) → ℤ | IsRoot .G2 β ∧ 0 < ht β}, twistedRootGroup σ β) =
        ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_inf] at hg
  have hle : (⨆ i, hHat σ i) ≤ (⨆ a, Adjoint.torus (τ := d4) K a).comap (twistedGroup σ).subtype :=
    iSup_le fun i x hx => by
      rw [hHat, Subgroup.mem_subgroupOf] at hx
      exact hHatE_le_iSup_torus σ i hx
  have h1 : (g : adjointGroup d4 K) ∈ ⨆ a, Adjoint.torus (τ := d4) K a := hle hg.1
  have h2 : (g : adjointGroup d4 K) ∈ unip (K := K) ((1 : ℤ) • htHom) := by
    refine iSup_rootGroup_le_unip 1 ?_
    have := iSup_twistedRootGroup_le σ (fun h => 0 < h) hg.2
    refine (iSup₂_le fun γ hγ => ?_ : (⨆ γ ∈ {γ : Fin d4.rank → ℤ | IsRoot d4 γ ∧ 0 < ht γ},
      𝕏 γ) ≤ _) this
    exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ {γ : Fin d4.rank → ℤ | IsRoot d4 γ ∧
      0 < 1 * ht γ}) => 𝕏 γ) γ ⟨hγ.1, by rw [one_mul]; exact hγ.2⟩ le_rfl
  have h := Subgroup.mem_inf.2 ⟨h1, h2⟩
  rw [iSup_torus_inf_unip, Subgroup.mem_bot] at h
  exact Subgroup.mem_bot.2 (Subtype.ext h)

theorem commute_of_mem_iSup_torus
    {g h : adjointGroup d4 K}
    (hg : g ∈ ⨆ a, Adjoint.torus (τ := d4) K a) (hh : h ∈ ⨆ a, Adjoint.torus (τ := d4) K a) :
    Commute g h := by
  refine Subgroup.iSup_induction _ (C := fun g => Commute g h) hg (fun a x hx => ?_)
    (Commute.one_left h) (fun x y hx hy => hx.mul_left hy)
  exact Subgroup.iSup_induction _ (C := fun h => Commute x h) hh
    (fun b y hy => torus_commute hx hy) (Commute.one_right x) (fun y y' hy hy' => hy.mul_right hy')

theorem hHat_commute
    {i j : Fin (Tag.rank .G2)} {h h' : twistedGroup σ} (hh : h ∈ hHat σ i)
    (hh' : h' ∈ hHat σ j) : Commute h h' := by
  rw [hHat, Subgroup.mem_subgroupOf] at hh hh'
  exact Subtype.ext (commute_of_mem_iSup_torus (hHatE_le_iSup_torus σ i hh)
    (hHatE_le_iSup_torus σ j hh')).eq

section Indep

variable {σ} (hσ : ∀ c, σ (σ (σ c)) = c)
include hσ

theorem eq_one_of_torusElement_eq_hShortHom
    {s t : Kˣ}
    (h : torusElement d4 K (nd 2) s = hShortHom σ t) : s = 1 := by
  have hconj : ∀ l : Fin d4.rank, ((s ^ d4.cartan (nd 2) l : Kˣ) : K) =
      ((t ^ d4.cartan (nd 0) l : Kˣ) : K) * (((Units.map σ.toMonoidHom t) ^ d4.cartan (nd 1) l :
        Kˣ) : K) * (((Units.map σ.toMonoidHom (Units.map σ.toMonoidHom t)) ^
          d4.cartan (nd 3) l : Kˣ) : K) := by
    intro l
    have e1 := torusElement_conj_xElement (nd 2) l s (1 : K)
    have e2 := torus3_conj_xElement (nd 0) (nd 1) (nd 3) l t (Units.map σ.toMonoidHom t)
      (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom t)) (1 : K)
    rw [h, hShortHom_apply, e2] at e1
    have := xElement_injective l e1
    simp only [mul_one] at this
    rw [mul_assoc]
    exact this.symm
  have hu : ∀ u : Kˣ, ((Units.map σ.toMonoidHom u : Kˣ) : K) = σ u := fun _ => rfl
  have h0 := hconj (nd 0)
  have h1 := hconj (nd 1)
  have h3 := hconj (nd 3)
  have h2 := hconj (nd 2)
  simp only [hu, show d4.cartan (nd 2) (nd 0) = -1 by decide,
    show d4.cartan (nd 0) (nd 0) = 2 by decide, show d4.cartan (nd 1) (nd 0) = 0 by decide,
    show d4.cartan (nd 3) (nd 0) = 0 by decide, show d4.cartan (nd 2) (nd 1) = -1 by decide,
    show d4.cartan (nd 0) (nd 1) = 0 by decide, show d4.cartan (nd 1) (nd 1) = 2 by decide,
    show d4.cartan (nd 3) (nd 1) = 0 by decide, show d4.cartan (nd 2) (nd 3) = -1 by decide,
    show d4.cartan (nd 0) (nd 3) = 0 by decide, show d4.cartan (nd 1) (nd 3) = 0 by decide,
    show d4.cartan (nd 3) (nd 3) = 2 by decide, show d4.cartan (nd 2) (nd 2) = 2 by decide,
    show d4.cartan (nd 0) (nd 2) = -1 by decide, show d4.cartan (nd 1) (nd 2) = -1 by decide,
    show d4.cartan (nd 3) (nd 2) = -1 by decide, zpow_neg, zpow_ofNat, Units.val_pow_eq_pow_val,
    Units.val_inv_eq_inv_val, Units.val_one, pow_zero, pow_one, mul_one, one_mul] at h0 h1 h3 h2
  set a : K := (t : K) with ha_def
  set x : K := (s : K) with hx_def
  have ha : a ≠ 0 := t.ne_zero
  have hx : x ≠ 0 := s.ne_zero
  have hb : σ a = a := by
    have hsq : (σ a) ^ 2 = a ^ 2 := h1.symm.trans h0
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hb | hb
    · exact hb
    ·
      have hc : σ (σ a) = a := by rw [hb, map_neg, hb, neg_neg]
      have h3' : σ (σ (σ a)) = -a := by rw [hc, hb]
      rw [hσ] at h3'
      rw [hb, ← h3']
  have hc : σ (σ a) = a := by rw [hb, hb]
  simp only [hb] at h2
  have hxa : x = (a ^ 2)⁻¹ := by
    have e : x⁻¹ = a ^ 2 := h0
    rw [← e, inv_inv]
  rw [hxa] at h2
  have h43 : a ^ 4 = a ^ 3 := by
    have e1 : ((a ^ 2)⁻¹) ^ 2 = (a ^ 4)⁻¹ := by rw [inv_pow, ← pow_mul]
    have e2 : a⁻¹ * a⁻¹ * a⁻¹ = (a ^ 3)⁻¹ := by rw [← inv_pow]; ring
    rw [e1, e2] at h2
    exact inv_inj.1 h2
  have ha1 : a = 1 := by
    have h' : a ^ 3 * a = a ^ 3 * 1 := by rw [mul_one, ← pow_succ]; exact h43
    exact mul_left_cancel₀ (pow_ne_zero 3 ha) h'
  refine Units.ext ?_
  rw [Units.val_one]
  change x = 1
  rw [hxa, ha1, one_pow, inv_one]

variable (σ) in
theorem hHat_iSupIndep :
    iSupIndep (hHat σ) := by
  have key : ∀ g : twistedGroup σ, g ∈ hHat σ (ng 0) → g ∈ hHat σ (ng 1) → g = 1 := by
    intro g h0 h1
    rw [hHat, Subgroup.mem_subgroupOf] at h0 h1
    obtain ⟨s, hs⟩ := h0
    obtain ⟨t, ht⟩ := h1
    have e : torusElement d4 K (nd 2) (s : Kˣ) = hShortHom σ t := hs.trans ht.symm
    have hs1 := eq_one_of_torusElement_eq_hShortHom hσ e
    refine Subtype.ext ?_
    rw [← hs]
    change torusElement d4 K (nd 2) (s : Kˣ) = 1
    rw [hs1]
    exact torusElement_one_eq _
  intro i
  rw [Subgroup.disjoint_def]
  intro g hg hg'
  match i with
  | ⟨0, _⟩ =>
    have hle : (⨆ (j) (_ : j ≠ ng 0), hHat σ j) ≤ hHat σ (ng 1) := iSup₂_le fun j hj => by
      match j with
      | ⟨0, _⟩ => exact absurd rfl hj
      | ⟨1, _⟩ => exact le_rfl
    exact key g hg (hle hg')
  | ⟨1, _⟩ =>
    have hle : (⨆ (j) (_ : j ≠ ng 1), hHat σ j) ≤ hHat σ (ng 0) := iSup₂_le fun j hj => by
      match j with
      | ⟨0, _⟩ => exact le_rfl
      | ⟨1, _⟩ => exact absurd rfl hj
    exact key g (hle hg') hg

end Indep

end CFSG.LieType.Steinberg.TwistedD4
