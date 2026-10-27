module

public import CFSG.LieType.Steinberg.Minuscule.Group
public import CFSG.LieType.Steinberg.Minuscule.Form
public import CFSG.LieType.Steinberg.Extras
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116

public noncomputable section

namespace CFSG.LieType.Steinberg.Minuscule

open CFSG.Blueprint.Chevalley

section Filtration

variable {k : Type*} [Field k] {d : ℕ} (dg : Fin d → ℤ)

@[expose] def filt (m : ℤ) : Submodule k (Fin d →₀ k) :=
  Submodule.span k ((fun a => Finsupp.single a 1) '' {a | m ≤ dg a})

variable {dg}

theorem single_mem_filt {m : ℤ} {a : Fin d} (h : m ≤ dg a) :
    Finsupp.single a (1 : k) ∈ filt dg m :=
  Submodule.subset_span ⟨a, h, rfl⟩

theorem filt_mono {m m' : ℤ} (h : m ≤ m') : filt (k := k) dg m' ≤ filt dg m :=
  Submodule.span_mono fun _ ⟨a, ha, hb⟩ => ⟨a, le_trans h ha, hb⟩

theorem apply_eq_zero_of_mem_filt {m : ℤ} {w : Fin d →₀ k} (hw : w ∈ filt dg m) {b : Fin d}
    (hb : dg b < m) : w b = 0 := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact Finsupp.single_eq_of_ne (fun h => by subst h; exact absurd ha (not_le.2 hb))
  | zero => rfl
  | add x y _ _ hx hy => rw [Finsupp.add_apply, hx, hy, add_zero]
  | smul c x _ hx => rw [Finsupp.smul_apply, hx, smul_zero]

theorem mem_filt_of_basis {f : Module.End k (Fin d →₀ k)} {s : ℤ}
    (hf : ∀ a, f (Finsupp.single a 1) ∈ filt dg (dg a + s)) {m : ℤ} {w : Fin d →₀ k}
    (hw : w ∈ filt dg m) : f w ∈ filt dg (m + s) := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    have ha : m ≤ dg a := ha
    exact filt_mono (by omega) (hf a)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem IsSignedMap.mem_filt {f : Module.End k (Fin d →₀ k)} {P : Fin d → Fin d → Prop}
    (hf : IsSignedMap f P) {s : ℤ} (hs : ∀ a b, P a b → dg a + s ≤ dg b) {m : ℤ}
    {w : Fin d →₀ k} (hw : w ∈ filt dg m) : f w ∈ filt dg (m + s) := by
  refine mem_filt_of_basis (fun a => ?_) hw
  rcases hf a with h0 | ⟨b, hb, h | h⟩ <;> rw [‹f _ = _›]
  · exact zero_mem _
  · exact single_mem_filt (hs a b hb)
  · exact neg_mem (single_mem_filt (hs a b hb))

theorem sub_mem_filt_of_prod {s : ℤ} (hs : 0 ≤ s) :
    ∀ (l : List (Module.End k (Fin d →₀ k))),
      (∀ g ∈ l, ∀ m (w : Fin d →₀ k), w ∈ filt dg m → g w - w ∈ filt dg (m + s)) →
      ∀ m (w : Fin d →₀ k), w ∈ filt dg m → l.prod w - w ∈ filt dg (m + s)
  | [], _, m, w, _ => by rw [List.prod_nil, Module.End.one_apply, sub_self]; exact zero_mem _
  | g :: l, hl, m, w, hw => by
    have h1 := sub_mem_filt_of_prod hs l (fun g hg => hl g (List.mem_cons_of_mem _ hg)) m w hw
    have h2 : l.prod w ∈ filt dg m := by
      have := add_mem (filt_mono (by omega) h1) hw
      rwa [sub_add_cancel] at this
    have h3 := hl g List.mem_cons_self m _ h2
    rw [List.prod_cons, Module.End.mul_apply]
    have := add_mem h3 h1
    rwa [sub_add_sub_cancel] at this

@[expose] def IsUni (dg : Fin d → ℤ) (g : Module.End k (Fin d →₀ k)) : Prop :=
  ∀ m (w : Fin d →₀ k), w ∈ filt dg m → g w - w ∈ filt dg (m + 1)

theorem isUni_one (dg : Fin d → ℤ) : IsUni dg (1 : Module.End k (Fin d →₀ k)) := fun m w _ => by
  rw [Module.End.one_apply, sub_self]
  exact zero_mem _

theorem IsUni.mul {g h : Module.End k (Fin d →₀ k)} (hg : IsUni dg g) (hh : IsUni dg h) :
    IsUni dg (g * h) := fun m w hw => by
  have h1 := hh m w hw
  have h2 : h w ∈ filt dg m := by
    have := add_mem (filt_mono (by omega) h1) hw
    rwa [sub_add_cancel] at this
  have := add_mem (hg m _ h2) h1
  rwa [sub_add_sub_cancel, ← Module.End.mul_apply] at this

end Filtration

namespace MinData

@[expose] def IsGrading {τ : Tag} (D : MinData τ) (F : Fin D.d → ℤ) (f : (Fin τ.rank → ℤ) → ℤ)
    (c : ℤ) : Prop :=
  ∀ a b : Fin D.d, ∀ γ : Fin τ.rank → ℤ, D.wt b = D.wt a + toWeight γ → F b = F a + c * f γ

@[expose] def lead {τ : Tag} (D : MinData τ) (F : Fin D.d → ℤ) (δ : Fin τ.rank → ℤ)
    (a : Fin D.d) : ℤ :=
  3 * F a - D.wt a ⬝ᵥ δ

@[expose] def sdeg {τ : Tag} (D : MinData τ) (η : ℤ) (a : Fin D.d) : ℤ := η * D.deg a

@[expose] def fgrade {τ : Tag} (D : MinData τ) (f : (Fin τ.rank → ℤ) →+ ℤ) (a : Fin D.d) : ℤ :=
  Matrix.vecMul (fun j => f (Pi.single j 1)) τ.cartan.adjugate ⬝ᵥ D.wt a

theorem toWeight_eq_mulVec {τ : Tag} (γ : Fin τ.rank → ℤ) :
    toWeight γ = Matrix.mulVec τ.cartan γ := rfl

theorem addMonoidHom_eq_dotProduct {τ : Tag} (f : (Fin τ.rank → ℤ) →+ ℤ) (γ : Fin τ.rank → ℤ) :
    (fun j => f (Pi.single j 1)) ⬝ᵥ γ = f γ := by
  conv_rhs => rw [← Finset.univ_sum_single γ]
  rw [map_sum, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : (Pi.single j (γ j) : Fin τ.rank → ℤ) = γ j • Pi.single j 1 := by
    ext l
    by_cases hl : l = j
    · subst hl; simp
    · simp [Pi.single_eq_of_ne hl]
  rw [e, map_zsmul, smul_eq_mul, mul_comm]

theorem isGrading_fgrade {τ : Tag} (D : MinData τ) (f : (Fin τ.rank → ℤ) →+ ℤ) :
    D.IsGrading (D.fgrade f) f τ.cartan.det := by
  intro a b γ h
  rw [fgrade, fgrade, h, dotProduct_add, toWeight_eq_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, Matrix.adjugate_mul, Matrix.vecMul_smul, Matrix.vecMul_one,
    smul_dotProduct, addMonoidHom_eq_dotProduct, smul_eq_mul]

theorem det_cartan_pos {τ : Tag} (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef) :
    0 < τ.cartan.det := by
  have h := hpd.det_pos
  rw [show τ.cartan.map (Int.cast : ℤ → ℚ) = (Int.castRingHom ℚ).mapMatrix τ.cartan from rfl,
    ← RingHom.map_det, Int.coe_castRingHom] at h
  exact Int.cast_pos.1 h

namespace Valid

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (k : Type*) [Field k]
include hV

theorem endo_list_prod (l : List (hV.minGroup k)) :
    hV.endo k l.prod = (l.map (hV.endo k)).prod := by
  induction l with
  | nil => rfl
  | cons g l ih => rw [List.prod_cons, endo_mul, ih, List.map_cons, List.prod_cons]

theorem isGrading_sdeg (η : ℤ) : D.IsGrading (D.sdeg η) (fun γ => η * ht γ) D.scale := by
  intro a b γ h
  simp only [sdeg, hV.deg_eq_add h]
  ring

omit hV in
theorem lead_eq_add {F : Fin D.d → ℤ} {f : (Fin τ.rank → ℤ) → ℤ} {c : ℤ}
    (hF : D.IsGrading F f c) {δ γ : Fin τ.rank → ℤ} {a b : Fin D.d}
    (h : D.wt b = D.wt a + toWeight γ) :
    D.lead F δ b = D.lead F δ a + (3 * c * f γ - toWeight γ ⬝ᵥ δ) := by
  simp only [lead, hF a b γ h, h, add_dotProduct]
  ring

theorem xm_sub_mem_filt {F : Fin D.d → ℤ} {f : (Fin τ.rank → ℤ) → ℤ} {c : ℤ}
    (hF : D.IsGrading F f c) {δ γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (u : k) {m : ℤ}
    {w : Fin D.d →₀ k} (hw : w ∈ filt (D.lead F δ) m) :
    hV.endo k (hV.xm k γ u) w - w ∈ filt (D.lead F δ) (m + (3 * c * f γ - toWeight γ ⬝ᵥ δ)) := by
  rw [endo_xm, LinearMap.add_apply, Module.End.one_apply, add_sub_cancel_left,
    LinearMap.smul_apply]
  exact Submodule.smul_mem _ u ((hV.isSignedMap_rootOp hγ).mem_filt
    (fun a b h => (lead_eq_add hF h).ge) hw)

theorem prod_sub_mem_filt {F : Fin D.d → ℤ} {f : (Fin τ.rank → ℤ) → ℤ} {c : ℤ}
    (hF : D.IsGrading F f c) {δ : Fin τ.rank → ℤ} {s : ℤ} (hs : 0 ≤ s)
    (L : List (Fin τ.rank → ℤ)) (g : (Fin τ.rank → ℤ) → hV.minGroup k)
    (hg : ∀ γ ∈ L, g γ ∈ hV.rootGroup k γ)
    (hL : ∀ γ ∈ L, IsRoot τ γ ∧ s ≤ 3 * c * f γ - toWeight γ ⬝ᵥ δ)
    {m : ℤ} {w : Fin D.d →₀ k} (hw : w ∈ filt (D.lead F δ) m) :
    hV.endo k (L.map g).prod w - w ∈ filt (D.lead F δ) (m + s) := by
  rw [endo_list_prod, List.map_map]
  refine sub_mem_filt_of_prod hs _ (fun x hx m w hw => ?_) m w hw
  obtain ⟨γ, hγL, rfl⟩ := List.mem_map.1 hx
  obtain ⟨u, hu⟩ := (hV.mem_rootGroup k).1 (hg γ hγL)
  rw [Function.comp_apply, ← hu]
  exact filt_mono (by have := (hL γ hγL).2; omega) (hV.xm_sub_mem_filt k hF (hL γ hγL).1 u hw)

theorem leading_coeff {F : Fin D.d → ℤ} {f : (Fin τ.rank → ℤ) → ℤ} {c : ℤ}
    (hF : D.IsGrading F f c) {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) {s : ℤ} (hs : 0 < s)
    (hsδ : 3 * c * f δ - toWeight δ ⬝ᵥ δ = s)
    (L : List (Fin τ.rank → ℤ)) (g : (Fin τ.rank → ℤ) → hV.minGroup k)
    (hg : ∀ γ ∈ L, g γ ∈ hV.rootGroup k γ)
    (hL : ∀ γ ∈ L, IsRoot τ γ ∧ s + 1 ≤ 3 * c * f γ - toWeight γ ⬝ᵥ δ)
    {a b : Fin D.d} {ε : k} (hab : D.rootOp k δ (Finsupp.single a 1) = ε • Finsupp.single b 1)
    (hwt : D.wt b = D.wt a + toWeight δ) (u : k) :
    hV.endo k (hV.xm k δ u * (L.map g).prod) (Finsupp.single a 1) b = u * ε := by
  have hdb : D.lead F δ b = D.lead F δ a + s := by rw [← hsδ]; exact lead_eq_add hF hwt
  have hP := hV.prod_sub_mem_filt k hF (by omega) L g hg hL (m := D.lead F δ a)
    (w := Finsupp.single a 1) (single_mem_filt le_rfl)
  set P := hV.endo k (L.map g).prod
  set r := P (Finsupp.single a 1) - Finsupp.single a 1
  have hPa : P (Finsupp.single a 1) = Finsupp.single a 1 + r := by rw [add_sub_cancel]
  have hab' : a ≠ b := fun h => by rw [h] at hdb; omega
  have hr : r b = 0 := apply_eq_zero_of_mem_filt hP (by omega)
  have hEr : D.rootOp k δ r ∈ filt (D.lead F δ) (D.lead F δ a + (s + 1) + s) :=
    (hV.isSignedMap_rootOp hδ).mem_filt (fun a' b' h => by rw [lead_eq_add hF h, hsδ]) hP
  have hEr0 : D.rootOp k δ r b = 0 := apply_eq_zero_of_mem_filt hEr (by omega)
  rw [endo_mul, Module.End.mul_apply, endo_xm, LinearMap.add_apply, Module.End.one_apply,
    LinearMap.smul_apply, hPa, map_add, hab]
  simp [hab', hr, hEr0]

theorem exists_rootOp_single_ne_zero {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) :
    ∃ a b : Fin D.d, ∃ ε : k, IsSign ε ∧
      D.rootOp k δ (Finsupp.single a 1) = ε • Finsupp.single b 1 ∧
        D.wt b = D.wt a + toWeight δ := by
  by_contra hne
  apply hV.rootOp_ne_zero (R := k) hδ
  refine ext_single fun a => ?_
  rw [LinearMap.zero_apply]
  rcases hV.isSignedMap_rootOp (R := k) hδ a with h0 | ⟨b, hb, h | h⟩
  · exact h0
  · exact absurd ⟨a, b, 1, isSign_one, by rw [h, one_smul], hb⟩ hne
  · exact absurd ⟨a, b, -1, isSign_neg_one, by rw [h, neg_one_smul], hb⟩ hne

variable {k} (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
include hpd

theorem prodInjective_of_isGrading {F : Fin D.d → ℤ} {f : (Fin τ.rank → ℤ) → ℤ} {c : ℤ}
    (hc : 0 < c) (hF : D.IsGrading F f c) :
    ∀ L : List (Fin τ.rank → ℤ), L.Nodup → (∀ γ ∈ L, IsRoot τ γ ∧ 0 < f γ) →
      L.Pairwise (fun γ δ => f γ ≤ f δ) → ProdInjectiveFor (hV.rootGroup k) L
  | [], _, _, _ => fun _ _ _ _ _ γ hγ => absurd hγ List.not_mem_nil
  | δ :: L, hnd, hroot, hsort => by
    intro f₁ f₂ hf₁ hf₂ hf
    obtain ⟨hδ, hδL⟩ := List.nodup_cons.1 hnd
    have hsort' := List.pairwise_cons.1 hsort
    have hrootL : ∀ γ ∈ L, IsRoot τ γ ∧ 0 < f γ := fun γ h =>
      hroot γ (List.mem_cons_of_mem _ h)
    have hrδ := (hroot δ List.mem_cons_self).1
    have h1δ : 1 ≤ f δ := (hroot δ List.mem_cons_self).2
    have hsδ : 3 * c * f δ - toWeight δ ⬝ᵥ δ = 3 * c * f δ - 2 := by
      rw [form_self_root hpd hrδ]
    have hs : 0 < 3 * c * f δ - 2 := by nlinarith
    have hL : ∀ γ ∈ L, IsRoot τ γ ∧ 3 * c * f δ - 2 + 1 ≤ 3 * c * f γ - toWeight γ ⬝ᵥ δ := by
      intro γ hγ
      refine ⟨(hrootL γ hγ).1, ?_⟩
      have hγδ : γ ≠ δ := fun h => hδ (h ▸ hγ)
      have h1 := form_le_one hpd (hrootL γ hγ).1 hrδ hγδ
      have h2 := hsort'.1 γ hγ
      nlinarith
    obtain ⟨u, hu⟩ := (hV.mem_rootGroup k).1 (hf₁ δ List.mem_cons_self)
    obtain ⟨u', hu'⟩ := (hV.mem_rootGroup k).1 (hf₂ δ List.mem_cons_self)
    obtain ⟨a, b, ε, hε, hab, hwt⟩ := hV.exists_rootOp_single_ne_zero k hrδ
    have hfL : ∀ γ ∈ L, f₁ γ ∈ hV.rootGroup k γ := fun γ h => hf₁ γ (List.mem_cons_of_mem _ h)
    have hgL : ∀ γ ∈ L, f₂ γ ∈ hV.rootGroup k γ := fun γ h => hf₂ γ (List.mem_cons_of_mem _ h)
    simp only [List.map_cons, List.prod_cons] at hf
    rw [← hu, ← hu'] at hf
    have e1 := hV.leading_coeff k hF hrδ hs hsδ L f₁ hfL hL hab hwt u
    have e2 := hV.leading_coeff k hF hrδ hs hsδ L f₂ hgL hL hab hwt u'
    rw [hf, e2] at e1
    have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
    have huu : u' = u := mul_right_cancel₀ hε0 e1
    have hδeq : f₁ δ = f₂ δ := by rw [← hu, ← hu', huu]
    rw [huu] at hf
    have hrest := prodInjective_of_isGrading hc hF L hδL hrootL hsort'.2 f₁ f₂ hfL hgL
      (mul_left_cancel hf)
    intro γ hγ
    rcases List.mem_cons.1 hγ with rfl | hγ
    · exact hδeq
    · exact hrest γ hγ

theorem prodInjective (η : ℤ) :
    ∀ L : List (Fin τ.rank → ℤ), L.Nodup → (∀ γ ∈ L, IsRoot τ γ ∧ 0 < η * ht γ) →
      L.Pairwise (fun γ δ => η * ht γ ≤ η * ht δ) → ProdInjectiveFor (hV.rootGroup k) L :=
  hV.prodInjective_of_isGrading hpd (by exact_mod_cast hV.scale_pos) (hV.isGrading_sdeg η)

theorem prodInjective_additive (f : (Fin τ.rank → ℤ) →+ ℤ) :
    ∀ L : List (Fin τ.rank → ℤ), L.Nodup → (∀ γ ∈ L, IsRoot τ γ ∧ 0 < f γ) →
      L.Pairwise (fun γ δ => f γ ≤ f δ) → ProdInjectiveFor (hV.rootGroup k) L :=
  hV.prodInjective_of_isGrading hpd (det_cartan_pos hpd) (D.isGrading_fgrade f)

omit hpd

variable (k)

theorem isUni_xm {η : ℤ} {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hpos : 0 < η * ht γ) (c : k) :
    IsUni (D.sdeg η) (hV.endo k (hV.xm k γ c)) := fun m w hw => by
  rw [endo_xm, LinearMap.add_apply, Module.End.one_apply, add_sub_cancel_left,
    LinearMap.smul_apply]
  refine Submodule.smul_mem _ c ((hV.isSignedMap_rootOp hγ).mem_filt (fun a b h => ?_) hw)
  have hscale : (1 : ℤ) ≤ D.scale := by exact_mod_cast hV.scale_pos
  have hpos' : 1 ≤ η * ht γ := hpos
  simp only [sdeg, hV.deg_eq_add h]
  nlinarith

theorem isUni_of_mem {η : ℤ} {g : hV.minGroup k}
    (hg : g ∈ ⨆ γ ∈ {γ | IsRoot τ γ ∧ 0 < η * ht γ}, hV.rootGroup k γ) :
    IsUni (D.sdeg η) (hV.endo k g) := by
  refine Subgroup.iSup_induction _ (C := fun x => IsUni (D.sdeg η) (hV.endo k x)) hg
    (fun γ x hx => ?_) (isUni_one _) (fun x y hx hy => hx.mul hy)
  refine Subgroup.iSup_induction _ (C := fun x => IsUni (D.sdeg η) (hV.endo k x)) hx
    (fun hγ y hy => ?_) (isUni_one _) (fun x y hx hy => hx.mul hy)
  obtain ⟨c, rfl⟩ := (hV.mem_rootGroup k).1 hy
  exact hV.isUni_xm k hγ.1 hγ.2 c

omit hV in
theorem eq_one_of_isUni {g : Module.End k (Fin D.d →₀ k)} (hp : IsUni (D.sdeg 1) g)
    (hn : IsUni (D.sdeg (-1)) g) : g = 1 := by
  refine ext_single fun a => ?_
  rw [Module.End.one_apply, ← sub_eq_zero]
  refine Finsupp.ext fun b => ?_
  have h1 := hp _ _ (single_mem_filt (dg := D.sdeg 1) (a := a) le_rfl)
  have h2 := hn _ _ (single_mem_filt (dg := D.sdeg (-1)) (a := a) le_rfl)
  rw [Finsupp.zero_apply]
  rcases lt_or_ge (D.sdeg 1 b) (D.sdeg 1 a + 1) with h | h
  · exact apply_eq_zero_of_mem_filt h1 h
  · refine apply_eq_zero_of_mem_filt h2 ?_
    simp only [sdeg] at h ⊢
    omega

theorem posPart_inf_negPart :
    (⨆ γ ∈ {γ | IsRoot τ γ ∧ 0 < ht γ}, hV.rootGroup k γ) ⊓
      (⨆ γ ∈ {γ | IsRoot τ γ ∧ ht γ < 0}, hV.rootGroup k γ) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_inf] at hg
  have hp' := hV.isUni_of_mem k (η := 1) (by simpa only [one_mul] using hg.1)
  have hn' := hV.isUni_of_mem k (η := -1) (by
    simpa only [neg_one_mul, Left.neg_pos_iff] using hg.2)
  rw [Subgroup.mem_bot]
  exact hV.endo_injective k (eq_one_of_isUni k hp' hn')

theorem torus_commute (i j : Fin τ.rank) {h h' : hV.minGroup k} (hh : h ∈ hV.torus k i)
    (hh' : h' ∈ hV.torus k j) : Commute h h' := by
  obtain ⟨t, rfl⟩ := (hV.mem_torus k).1 hh
  obtain ⟨t', rfl⟩ := (hV.mem_torus k).1 hh'
  exact hV.endo_injective k (by rw [endo_mul, endo_mul, endo_hm, endo_hm, hDiag, hDiag,
    diagOp_comm])

theorem exists_diagOp_of_mem_iSup_torus {g : hV.minGroup k} (hg : g ∈ ⨆ i, hV.torus k i) :
    ∃ μ : Fin D.d → k, hV.endo k g = diagOp μ := by
  refine Subgroup.iSup_induction _ (C := fun x => ∃ μ : Fin D.d → k, hV.endo k x = diagOp μ) hg
    (fun i x hx => ?_) ⟨1, diagOp_one.symm⟩ (fun x y hx hy => ?_)
  · obtain ⟨t, rfl⟩ := (hV.mem_torus k).1 hx
    exact ⟨_, hV.endo_hm k i t⟩
  · obtain ⟨μ, hμ⟩ := hx
    obtain ⟨ν, hν⟩ := hy
    exact ⟨μ * ν, by rw [endo_mul, hμ, hν, diagOp_mul]⟩

theorem torus_inf_posPart :
    (⨆ i, hV.torus k i) ⊓ (⨆ γ ∈ {γ | IsRoot τ γ ∧ 0 < ht γ}, hV.rootGroup k γ) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨μ, hμ⟩ := hV.exists_diagOp_of_mem_iSup_torus k hg.1
  have hp' := hV.isUni_of_mem k (η := 1) (by simpa only [one_mul] using hg.2)
  rw [Subgroup.mem_bot]
  refine hV.endo_injective k ?_
  rw [hμ, endo_one, ← diagOp_one]
  congr 1
  funext a
  have h1 := hp' _ _ (single_mem_filt (dg := D.sdeg 1) (a := a) le_rfl)
  rw [hμ, diagOp_single] at h1
  have := apply_eq_zero_of_mem_filt h1 (b := a) (lt_add_one _)
  simp only [Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul,
    mul_one, sub_eq_zero] at this
  exact this

@[expose] def charHom (u : Fin τ.rank → kˣ) : (Fin τ.rank → ℤ) →+ Additive kˣ where
  toFun n := Additive.ofMul (∏ j, u j ^ n j)
  map_zero' := by simp
  map_add' n n' := by
    rw [← ofMul_mul, ← Finset.prod_mul_distrib]
    simp [zpow_add]

omit hV in
theorem charHom_apply (u : Fin τ.rank → kˣ) (n : Fin τ.rank → ℤ) :
    Additive.toMul (charHom k u n) = ∏ j, u j ^ n j := rfl

omit hV in
theorem charHom_single (u : Fin τ.rank → kˣ) (i : Fin τ.rank) :
    Additive.toMul (charHom k u (Pi.single i 1)) = u i := by
  rw [charHom_apply, Finset.prod_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj])
    (by simp)]
  simp

theorem charHom_eq_of_wt {u u' : Fin τ.rank → kˣ}
    (h : ∀ a : Fin D.d, charHom k u (D.wt a) = charHom k u' (D.wt a))
    (i : Fin τ.rank) : u i = u' i := by
  have hsum := hV.pgen_sum i
  have key : charHom k u (Pi.single i 1) = charHom k u' (Pi.single i 1) := by
    rw [← hsum, map_list_sum, map_list_sum, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun p hp => ?_
    simp only [Function.comp_apply, map_zsmul]
    rw [h ⟨p.1, hV.pgen_lt i p hp⟩]
  have := congrArg Additive.toMul key
  rwa [charHom_single, charHom_single] at this

theorem exists_char_of_mem {i : Fin τ.rank} {g : hV.minGroup k}
    (hg : g ∈ ⨆ (j) (_ : j ≠ i), hV.torus k j) :
    ∃ u : Fin τ.rank → kˣ, u i = 1 ∧
      hV.endo k g = diagOp fun a => ((Additive.toMul (charHom k u (D.wt a)) : kˣ) : k) := by
  have hone : ∃ u : Fin τ.rank → kˣ, u i = 1 ∧
      hV.endo k 1 = diagOp fun a => ((Additive.toMul (charHom k u (D.wt a)) : kˣ) : k) :=
    ⟨1, rfl, by rw [endo_one, ← diagOp_one]; congr 1; funext a; simp [charHom_apply]⟩
  have hmul : ∀ x y : hV.minGroup k,
      (∃ u : Fin τ.rank → kˣ, u i = 1 ∧
        hV.endo k x = diagOp fun a => ((Additive.toMul (charHom k u (D.wt a)) : kˣ) : k)) →
      (∃ u : Fin τ.rank → kˣ, u i = 1 ∧
        hV.endo k y = diagOp fun a => ((Additive.toMul (charHom k u (D.wt a)) : kˣ) : k)) →
      ∃ u : Fin τ.rank → kˣ, u i = 1 ∧
        hV.endo k (x * y) = diagOp fun a => ((Additive.toMul (charHom k u (D.wt a)) : kˣ) : k) := by
    rintro x y ⟨u, hu, hux⟩ ⟨u', hu', huy⟩
    refine ⟨u * u', by rw [Pi.mul_apply, hu, hu', mul_one], ?_⟩
    rw [endo_mul, hux, huy, diagOp_mul]
    congr 1
    funext a
    simp [charHom_apply, mul_zpow, Finset.prod_mul_distrib]
  refine Subgroup.iSup_induction _ (C := fun x => ∃ u : Fin τ.rank → kˣ, u i = 1 ∧
    hV.endo k x = diagOp fun a => ((Additive.toMul (charHom k u (D.wt a)) : kˣ) : k)) hg
    (fun j x hx => ?_) hone hmul
  refine Subgroup.iSup_induction _ (C := fun x => ∃ u : Fin τ.rank → kˣ, u i = 1 ∧
    hV.endo k x = diagOp fun a => ((Additive.toMul (charHom k u (D.wt a)) : kˣ) : k)) hx
    (fun hj y hy => ?_) hone hmul
  obtain ⟨t, rfl⟩ := (hV.mem_torus k).1 hy
  refine ⟨Pi.mulSingle j t, by rw [Pi.mulSingle_eq_of_ne (Ne.symm hj)], ?_⟩
  rw [endo_hm, hDiag]
  congr 1
  funext a
  rw [charHom_apply, Finset.prod_eq_single j (fun l _ hl => by simp [Pi.mulSingle_eq_of_ne hl])
    (by simp)]
  simp

theorem torus_iSupIndep : iSupIndep (hV.torus k) := by
  intro i
  rw [Subgroup.disjoint_def]
  intro g hg hg'
  obtain ⟨t, rfl⟩ := (hV.mem_torus k).1 hg
  obtain ⟨u, hu, hgu⟩ := hV.exists_char_of_mem k hg'
  have hdiag := hgu
  rw [endo_hm, hDiag] at hdiag
  have hval : ∀ a : Fin D.d, charHom k (Pi.mulSingle i t) (D.wt a) =
      charHom k u (D.wt a) := by
    intro a
    have := congrFun (diagOp_injective hdiag) a
    apply Additive.toMul.injective
    rw [Units.ext_iff.2 this.symm, charHom_apply,
      Finset.prod_eq_single i (fun l _ hl => by simp [Pi.mulSingle_eq_of_ne hl]) (by simp)]
    simp
  have := hV.charHom_eq_of_wt k hval i
  rw [Pi.mulSingle_eq_same, hu] at this
  rw [this, hm_one]

end Valid

end MinData

end CFSG.LieType.Steinberg.Minuscule
