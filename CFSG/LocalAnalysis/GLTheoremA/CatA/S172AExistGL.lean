module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreTransfer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172A.GL

open CFSG.Open
open scoped commutatorElement

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem add_self_V (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v]
  have : (2 : ZMod 2) = 0 := by decide
  rw [this, zero_smul]

theorem neg_V (v : V) : -v = v := neg_eq_of_add_eq_zero_right (add_self_V v)

theorem sub_V (v w : V) : v - w = v + w := by rw [sub_eq_add_neg, neg_V]

@[expose] def ds (e : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V := (e : V →ₗ[ZMod 2] V) - LinearMap.id

theorem ds_apply (e : V ≃ₗ[ZMod 2] V) (v : V) : ds e v = e v - v := by
  simp [ds]

@[expose] def fixSp (e : V ≃ₗ[ZMod 2] V) : Submodule (ZMod 2) V := LinearMap.ker (ds e)

@[expose] def comSp (e : V ≃ₗ[ZMod 2] V) : Submodule (ZMod 2) V := LinearMap.range (ds e)

theorem mem_fixSp {e : V ≃ₗ[ZMod 2] V} {v : V} : v ∈ fixSp e ↔ e v = v := by
  simp [fixSp, LinearMap.mem_ker, ds_apply, sub_eq_zero]

theorem mem_comSp {e : V ≃ₗ[ZMod 2] V} {a : V} : a ∈ comSp e ↔ ∃ v, e v - v = a := by
  simp [comSp, LinearMap.mem_range, ds_apply]

theorem cube {e : V ≃ₗ[ZMod 2] V} (h3 : e ^ 3 = 1) (v : V) : e (e (e v)) = v := by
  have : (e ^ 3) v = v := by rw [h3]; rfl
  simpa [pow_succ, LinearEquiv.mul_apply] using this

theorem eq_zero_of_mem_comSp_fixed {e : V ≃ₗ[ZMod 2] V} (h3 : e ^ 3 = 1) {x : V}
    (hx : x ∈ comSp e) (hf : e x = x) : x = 0 := by
  obtain ⟨y, hy⟩ := mem_comSp.1 hx
  have h2 : e (e y) + e y = e y + y := by
    have := hf
    rw [← hy] at this
    simpa [map_sub, sub_V] using this
  have hc : e (e y) = y := by
    have h2' : e (e y) + e y = y + e y := by rw [h2, add_comm]
    exact add_right_cancel h2'
  have hey : e y = y := by
    have := congrArg e hc
    rw [cube h3] at this
    exact this.symm
  rw [← hy, hey, sub_self]

theorem quad_of_mem_comSp {e : V ≃ₗ[ZMod 2] V} (h3 : e ^ 3 = 1) {a : V} (ha : a ∈ comSp e) :
    e (e a) + e a + a = 0 := by
  obtain ⟨y, rfl⟩ := mem_comSp.1 ha
  have h := cube h3 y
  simp only [map_sub, sub_V, map_add]
  have : e (e (e y)) + e (e y) + (e (e y) + e y) + (e y + y) = y + y + (e (e y) + e (e y)) + (e y + e y) := by
    rw [h]; abel
  rw [this]; simp only [add_self_V, add_zero, zero_add]

theorem isCompl_fixSp_comSp {e : V ≃ₗ[ZMod 2] V} (h3 : e ^ 3 = 1) :
    IsCompl (fixSp e) (comSp e) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    exact eq_zero_of_mem_comSp_fixed h3 hx' (mem_fixSp.1 hx)
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    rw [Submodule.mem_sup]
    refine ⟨v + e v + e (e v), ?_, e v + e (e v), ?_, ?_⟩
    · rw [mem_fixSp]
      simp only [map_add]
      rw [cube h3]; abel
    · rw [mem_comSp]
      refine ⟨e v, ?_⟩
      rw [sub_V]; abel
    ·
      have : v + e v + e (e v) + (e v + e (e v)) = v + (e v + e v) + (e (e v) + e (e v)) := by abel
      rw [this]; simp only [add_self_V, add_zero, zero_add]


section Glue

variable {U Uc : Submodule (ZMod 2) V} (hc : IsCompl U Uc)

@[expose] noncomputable def glue (g : U ≃ₗ[ZMod 2] U) : V ≃ₗ[ZMod 2] V :=
  ((Submodule.prodEquivOfIsCompl U Uc hc).symm.trans
    (g.prodCongr (LinearEquiv.refl (ZMod 2) Uc))).trans (Submodule.prodEquivOfIsCompl U Uc hc)

theorem glue_apply_left (g : U ≃ₗ[ZMod 2] U) (u : U) : glue hc g (u : V) = ((g u : U) : V) := by
  simp only [glue, LinearEquiv.trans_apply, Submodule.prodEquivOfIsCompl_symm_apply_left,
    LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply, Submodule.coe_prodEquivOfIsCompl',
    ZeroMemClass.coe_zero, add_zero]

theorem glue_apply_right (g : U ≃ₗ[ZMod 2] U) (u : Uc) : glue hc g (u : V) = (u : V) := by
  simp only [glue, LinearEquiv.trans_apply, Submodule.prodEquivOfIsCompl_symm_apply_right,
    LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply, map_zero, Submodule.coe_prodEquivOfIsCompl',
    ZeroMemClass.coe_zero, zero_add]

theorem exists_decomp (hc : IsCompl U Uc) (x : V) : ∃ (u : U) (u' : Uc), x = (u : V) + (u' : V) := by
  have hx : x ∈ U ⊔ Uc := by rw [hc.sup_eq_top]; trivial
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hx
  exact ⟨⟨y, hy⟩, ⟨z, hz⟩, hyz.symm⟩

theorem glue_mul (g h : U ≃ₗ[ZMod 2] U) : glue hc (g * h) = glue hc g * glue hc h := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨u, u', rfl⟩ := exists_decomp hc x
  simp only [LinearEquiv.mul_apply, map_add, glue_apply_left, glue_apply_right]

theorem glue_one : glue hc (1 : U ≃ₗ[ZMod 2] U) = 1 := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨u, u', rfl⟩ := exists_decomp hc x
  simp only [map_add, glue_apply_left, glue_apply_right]
  rfl

@[expose] noncomputable def glueHom : (U ≃ₗ[ZMod 2] U) →* (V ≃ₗ[ZMod 2] V) :=
  MonoidHom.mk' (glue hc) (fun g h => glue_mul hc g h)

theorem glueHom_injective : Function.Injective (glueHom hc) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply LinearEquiv.ext
  intro u
  have h1 : glue hc g (u : V) = (u : V) := by
    have : glueHom hc g = 1 := hg
    exact congrArg (fun f : V ≃ₗ[ZMod 2] V => f (u : V)) this
  rw [glue_apply_left] at h1
  exact Subtype.ext h1

end Glue


section One

variable [FiniteDimensional (ZMod 2) V] {e : V ≃ₗ[ZMod 2] V}

theorem e_mem_comSp {a : V} (ha : a ∈ comSp e) : e a ∈ comSp e := by
  obtain ⟨y, rfl⟩ := mem_comSp.1 ha
  exact mem_comSp.2 ⟨e y, by simp [map_sub]⟩

theorem e_fix {w : V} (hw : w ∈ fixSp e) : e w = w := mem_fixSp.1 hw

@[expose] noncomputable def Nsub (h3 : e ^ 3 = 1) : Subgroup (V ≃ₗ[ZMod 2] V) :=
  (glueHom (isCompl_fixSp_comSp h3)).range

theorem mem_Nsub {h3 : e ^ 3 = 1} {h : V ≃ₗ[ZMod 2] V} :
    h ∈ Nsub h3 ↔ (∀ a ∈ comSp e, h a = a) ∧ (∀ w ∈ fixSp e, h w ∈ fixSp e) := by
  have hc := isCompl_fixSp_comSp h3
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨fun a ha => ?_, fun w hw => ?_⟩
    · exact glue_apply_right hc g ⟨a, ha⟩
    · have := glue_apply_left hc g ⟨w, hw⟩
      show glue hc g w ∈ fixSp e
      rw [show w = ((⟨w, hw⟩ : fixSp e) : V) from rfl, this]
      exact (g ⟨w, hw⟩).2
  · rintro ⟨hA, hW⟩
    let f : fixSp e →ₗ[ZMod 2] fixSp e := (h : V →ₗ[ZMod 2] V).restrict hW
    have hinj : Function.Injective f := by
      intro u u' huu
      apply Subtype.ext
      have : h (u : V) = h (u' : V) := congrArg Subtype.val huu
      exact h.injective this
    refine ⟨LinearEquiv.ofInjectiveEndo f hinj, ?_⟩
    show glue hc (LinearEquiv.ofInjectiveEndo f hinj) = h
    apply LinearEquiv.ext
    intro x
    obtain ⟨u, u', rfl⟩ := exists_decomp hc x
    rw [map_add, map_add, glue_apply_left, glue_apply_right, hA u' u'.2]
    congr 1


theorem cent_fix {g : V ≃ₗ[ZMod 2] V} (hg : g * e = e * g) {w : V} (hw : w ∈ fixSp e) :
    g w ∈ fixSp e := by
  rw [mem_fixSp]
  have h1 : (e * g) w = (g * e) w := by rw [hg]
  simp only [LinearEquiv.mul_apply] at h1
  rw [h1, e_fix hw]

theorem cent_com {g : V ≃ₗ[ZMod 2] V} (hg : g * e = e * g) {a : V} (ha : a ∈ comSp e) :
    g a ∈ comSp e := by
  obtain ⟨y, rfl⟩ := mem_comSp.1 ha
  refine mem_comSp.2 ⟨g y, ?_⟩
  have h1 : (e * g) y = (g * e) y := by rw [hg]
  simp only [LinearEquiv.mul_apply] at h1
  rw [map_sub, ← h1]

theorem Nsub_le_cent (h3 : e ^ 3 = 1) :
    Nsub h3 ≤ Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V)) := by
  intro h hh
  rw [mem_Nsub] at hh
  obtain ⟨hA, hW⟩ := hh
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hc := isCompl_fixSp_comSp h3
  apply LinearEquiv.ext
  intro x
  obtain ⟨u, u', rfl⟩ := exists_decomp hc x
  simp only [LinearEquiv.mul_apply, map_add]
  rw [e_fix u.2, hA _ (e_mem_comSp u'.2), hA _ u'.2, e_fix (hW _ u.2)]

theorem exists_pow_of_cent (h3 : e ^ 3 = 1) (hfr : Module.finrank (ZMod 2) (comSp e) = 2)
    {g : V ≃ₗ[ZMod 2] V} (hg : g * e = e * g) : ∃ k : ℕ, ∀ a ∈ comSp e, g a = (e ^ k) a := by
  have hne : comSp e ≠ ⊥ := by
    intro h
    rw [h] at hfr
    simp at hfr
  obtain ⟨a₀, ha₀, ha₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hea₀ : e a₀ ∈ comSp e := e_mem_comSp ha₀
  have hZ : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hef : e a₀ ≠ a₀ := fun h => ha₀ne (eq_zero_of_mem_comSp_fixed h3 ha₀ h)
  have hli : LinearIndependent (ZMod 2) ![a₀, e a₀] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rcases hZ s with rfl | rfl <;> rcases hZ t with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · exfalso
      simp only [zero_smul, one_smul, zero_add] at hst
      exact ha₀ne (e.injective (by rw [hst, map_zero]))
    · exfalso
      simp only [one_smul, zero_smul, add_zero] at hst
      exact ha₀ne hst
    · exfalso
      simp only [one_smul] at hst
      apply hef
      have : e a₀ = -a₀ := eq_neg_of_add_eq_zero_right hst
      rw [this, neg_V]
  have hli' : LinearIndependent (ZMod 2) (![⟨a₀, ha₀⟩, ⟨e a₀, hea₀⟩] : Fin 2 → comSp e) := by
    refine LinearIndependent.of_comp (comSp e).subtype ?_
    convert hli using 1
    ext i
    fin_cases i <;> rfl
  have hspan : Submodule.span (ZMod 2)
      (Set.range (![⟨a₀, ha₀⟩, ⟨e a₀, hea₀⟩] : Fin 2 → comSp e)) = ⊤ :=
    hli'.span_eq_top_of_card_eq_finrank (by simp [hfr])
  have hdecomp : ∀ a ∈ comSp e, ∃ s t : ZMod 2, a = s • a₀ + t • e a₀ := by
    intro a ha
    have : (⟨a, ha⟩ : comSp e) ∈ Submodule.span (ZMod 2)
        (Set.range (![⟨a₀, ha₀⟩, ⟨e a₀, hea₀⟩] : Fin 2 → comSp e)) := by rw [hspan]; trivial
    rw [Submodule.mem_span_range_iff_exists_fun] at this
    obtain ⟨c, hc⟩ := this
    refine ⟨c 0, c 1, ?_⟩
    have := congrArg Subtype.val hc
    simpa [Fin.sum_univ_two] using this.symm
  have hquad : e (e a₀) = a₀ + e a₀ := by
    have h := quad_of_mem_comSp h3 ha₀
    rw [add_assoc] at h
    have : e (e a₀) = -(e a₀ + a₀) := eq_neg_of_add_eq_zero_left h
    rw [this, neg_V, add_comm]
  have hga : g a₀ ∈ comSp e := cent_com hg ha₀
  have hgne : g a₀ ≠ 0 := fun h => ha₀ne (g.injective (by rw [h, map_zero]))
  obtain ⟨s, t, hst⟩ := hdecomp _ hga
  have hgea : g (e a₀) = e (g a₀) := by
    have h1 : (g * e) a₀ = (e * g) a₀ := by rw [hg]
    simpa using h1
  have key : ∃ k : ℕ, g a₀ = (e ^ k) a₀ := by
    rcases hZ s with rfl | rfl <;> rcases hZ t with rfl | rfl
    · exfalso
      apply hgne
      rw [hst]; simp
    · refine ⟨1, ?_⟩
      rw [hst]; simp
    · refine ⟨0, ?_⟩
      rw [hst]; simp
    · refine ⟨2, ?_⟩
      rw [hst]
      simp only [one_smul, pow_two, LinearEquiv.mul_apply]
      rw [hquad]
  obtain ⟨k, hk⟩ := key
  refine ⟨k, fun a ha => ?_⟩
  obtain ⟨s', t', rfl⟩ := hdecomp a ha
  have hcomm : ∀ m : ℕ, ∀ v : V, (e ^ k) (e v) = e ((e ^ k) v) := by
    intro m v
    rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← pow_succ', pow_succ]
  rw [map_add, map_add, map_smul, map_smul, map_smul, map_smul, hgea, hk]
  have : e ((e ^ k) a₀) = (e ^ k) (e a₀) := (hcomm 0 a₀).symm
  rw [this]


theorem Nsub_normal (h3 : e ^ 3 = 1) :
    ((Nsub h3).subgroupOf (Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V)))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (Nsub_le_cent h3)]
  intro h g hh hg
  rw [mem_Nsub] at hh ⊢
  have hg' : g * e = e * g := Subgroup.mem_centralizer_singleton_iff.1 hg
  have hginv : g⁻¹ * e = e * g⁻¹ :=
    Subgroup.mem_centralizer_singleton_iff.1 ((Subgroup.centralizer _).inv_mem hg)
  refine ⟨fun a ha => ?_, fun w hw => ?_⟩
  · have h1 := cent_com hginv ha
    simp only [LinearEquiv.mul_apply]
    rw [hh.1 _ h1]
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  · have h1 := cent_fix hginv hw
    have h2 := hh.2 _ h1
    simp only [LinearEquiv.mul_apply]
    exact cent_fix hg' h2

theorem comm_le_Nsub (h3 : e ^ 3 = 1) (hfr : Module.finrank (ZMod 2) (comSp e) = 2) :
    ⁅Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V)),
      Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V))⁆ ≤ Nsub h3 := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  rw [mem_Nsub]
  have hmem : ∀ x ∈ Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V)), x * e = e * x :=
    fun x hx => Subgroup.mem_centralizer_singleton_iff.1 hx
  have hcomm : ∀ x ∈ Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V)),
      ∀ y ∈ Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V)),
      ∀ a ∈ comSp e, x (y a) = y (x a) := by
    intro x hx y hy a ha
    obtain ⟨k₁, hk₁⟩ := exists_pow_of_cent h3 hfr (hmem x hx)
    obtain ⟨k₂, hk₂⟩ := exists_pow_of_cent h3 hfr (hmem y hy)
    rw [hk₁ _ (cent_com (hmem y hy) ha), hk₂ _ ha, hk₂ _ (cent_com (hmem x hx) ha), hk₁ _ ha,
      ← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← pow_add, ← pow_add, add_comm]
  have hi₁ := (Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V))).inv_mem hg₁
  have hi₂ := (Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V))).inv_mem hg₂
  refine ⟨fun a ha => ?_, fun w hw => ?_⟩
  · have hb : g₂⁻¹ a ∈ comSp e := cent_com (hmem _ hi₂) ha
    have h1 := hcomm g₂ hg₂ g₁⁻¹ hi₁ (g₂⁻¹ a) hb
    simp only [commutatorElement_def, LinearEquiv.mul_apply]
    have e2 : g₂ (g₂⁻¹ a) = a := by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
    have e1 : g₁ (g₁⁻¹ a) = a := by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
    rw [h1, e2, e1]
  · have := cent_fix (hmem _ hi₂) hw
    have := cent_fix (hmem _ hi₁) this
    have := cent_fix (hmem _ hg₂) this
    have := cent_fix (hmem _ hg₁) this
    simpa [commutatorElement_def, LinearEquiv.mul_apply] using this

theorem finrank_fixSp (h3 : e ^ 3 = 1) :
    Module.finrank (ZMod 2) (fixSp e) + Module.finrank (ZMod 2) (comSp e) =
      Module.finrank (ZMod 2) V :=
  Submodule.finrank_add_eq_of_isCompl (isCompl_fixSp_comSp h3)

end One

section GLfacts

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer (VecAut projEquiv)

@[expose] noncomputable def conjEquiv {W W' : Type} [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup W']
    [Module (ZMod 2) W'] (e : W ≃ₗ[ZMod 2] W') :
    (W ≃ₗ[ZMod 2] W) ≃* (W' ≃ₗ[ZMod 2] W') where
  toFun g := e.symm.trans (g.trans e)
  invFun h := e.trans (h.trans e.symm)
  left_inv g := by ext w; simp
  right_inv h := by ext w; simp
  map_mul' g h := by ext w; simp

theorem center_eq_bot_of_simple_nonab {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hnab : ∃ a b : Q, a * b ≠ b * a) : Subgroup.center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center Q := by rw [h]; exact Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.1 ha) b).symm

theorem isQuasisimple_of_simple_nonab {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hnab : ∃ a b : Q, a * b ≠ b * a) : CFSG.Open.IsQuasisimple Q := by
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have : ⁅a, b⁆ ∈ commutator Q := by
        rw [_root_.commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      rw [h, Subgroup.mem_bot] at this
      exact commutatorElement_eq_one_iff_mul_comm.1 this
    · exact h
  · have hc := center_eq_bot_of_simple_nonab hnab
    exact (MulEquiv.isSimpleGroup_congr ((QuotientGroup.quotientMulEquivOfEq hc).trans
      QuotientGroup.quotientBot)).2 inferInstance

theorem vecAut_simple_nonab {k : ℕ} (hk : 3 ≤ k) :
    IsSimpleGroup (VecAut k) ∧ ∃ a b : VecAut k, a * b ≠ b * a := by
  let σ : ZMod 2 ≃+* ZMod 2 := RingEquiv.refl _
  let Φ := projEquiv (K := ZMod 2) k σ
  haveI : IsSimpleGroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL k (ZMod 2)) :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.isSimpleGroup_projectiveSL hk
  refine ⟨Φ.isSimpleGroup_congr.1 inferInstance, ?_⟩
  obtain ⟨a, b, hab⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.exists_noncomm_projectiveSL
    (K := ZMod 2) hk
  exact ⟨Φ a, Φ b, fun h => hab (Φ.injective (by simpa using h))⟩

end GLfacts

theorem simple_nonab_of_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsSimpleGroup Y ∧ ∃ a b : Y, a * b ≠ b * a) :
    IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  refine ⟨e.isSimpleGroup_congr.2 h.1, ?_⟩
  obtain ⟨a, b, hab⟩ := h.2
  exact ⟨e.symm a, e.symm b, fun h' => hab (e.symm.injective (by simpa using h'))⟩

section OneBlock

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer (VecAut)

variable [FiniteDimensional (ZMod 2) V] {e : V ≃ₗ[ZMod 2] V}

@[expose] noncomputable def NsubEquiv {r : ℕ} (hV : Module.finrank (ZMod 2) V = 2 * r + 1)
    (h3 : e ^ 3 = 1) (hfr : Module.finrank (ZMod 2) (comSp e) = 2) :
    Nsub h3 ≃* VecAut (2 * r - 1) :=
  (MonoidHom.ofInjective (glueHom_injective (isCompl_fixSp_comSp h3))).symm.trans
    (conjEquiv (LinearEquiv.ofFinrankEq (fixSp e) (Fin (2 * r - 1) → ZMod 2) (by
      have := finrank_fixSp h3
      rw [Module.finrank_fin_fun]
      omega)))

theorem Nsub_simple_nonab {r : ℕ} (hV : Module.finrank (ZMod 2) V = 2 * r + 1) (hr : 3 ≤ r)
    (h3 : e ^ 3 = 1) (hfr : Module.finrank (ZMod 2) (comSp e) = 2) :
    IsSimpleGroup (Nsub h3) ∧ ∃ a b : Nsub h3, a * b ≠ b * a :=
  simple_nonab_of_equiv (NsubEquiv hV h3 hfr) (vecAut_simple_nonab (by omega))

theorem Nsub_isQuasisimple {r : ℕ} (hV : Module.finrank (ZMod 2) V = 2 * r + 1) (hr : 3 ≤ r)
    (h3 : e ^ 3 = 1) (hfr : Module.finrank (ZMod 2) (comSp e) = 2) :
    CFSG.Open.IsQuasisimple (Nsub h3) := by
  obtain ⟨hs, hn⟩ := Nsub_simple_nonab hV hr h3 hfr
  haveI := hs
  exact isQuasisimple_of_simple_nonab hn

theorem Nsub_center {r : ℕ} (hV : Module.finrank (ZMod 2) V = 2 * r + 1) (hr : 3 ≤ r)
    (h3 : e ^ 3 = 1) (hfr : Module.finrank (ZMod 2) (comSp e) = 2) :
    Subgroup.center (Nsub h3) = ⊥ := by
  obtain ⟨hs, hn⟩ := Nsub_simple_nonab hV hr h3 hfr
  haveI := hs
  exact center_eq_bot_of_simple_nonab hn


theorem cent_Nsub_le_zpowers {r : ℕ} (hV : Module.finrank (ZMod 2) V = 2 * r + 1) (hr : 3 ≤ r)
    (h3 : e ^ 3 = 1) (hfr : Module.finrank (ZMod 2) (comSp e) = 2)
    {g : V ≃ₗ[ZMod 2] V} (hgC : g ∈ Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V)))
    (hgN : ∀ h ∈ Nsub h3, g * h = h * g) : g ∈ Subgroup.zpowers e := by
  have hg : g * e = e * g := Subgroup.mem_centralizer_singleton_iff.1 hgC
  obtain ⟨k, hk⟩ := exists_pow_of_cent h3 hfr hg
  have hek : e ^ k * e = e * e ^ k := (Commute.refl e).pow_left k |>.eq
  have hekC : (e ^ k)⁻¹ ∈ Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V)) := by
    apply (Subgroup.centralizer _).inv_mem
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hek
  have hekC' : (e ^ k)⁻¹ * e = e * (e ^ k)⁻¹ := Subgroup.mem_centralizer_singleton_iff.1 hekC
  have hg'N : g * (e ^ k)⁻¹ ∈ Nsub h3 := by
    rw [mem_Nsub]
    refine ⟨fun a ha => ?_, fun w hw => ?_⟩
    · have hb : (e ^ k)⁻¹ a ∈ comSp e := cent_com hekC' ha
      simp only [LinearEquiv.mul_apply]
      rw [hk _ hb, ← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    · simp only [LinearEquiv.mul_apply]
      exact cent_fix hg (cent_fix hekC' hw)
  have hcomm : ∀ h ∈ Nsub h3, (g * (e ^ k)⁻¹) * h = h * (g * (e ^ k)⁻¹) := by
    intro h hh
    have hhC := Nsub_le_cent h3 hh
    have h1 : h * e = e * h := Subgroup.mem_centralizer_singleton_iff.1 hhC
    have h2 : Commute h ((e ^ k)⁻¹) := (Commute.pow_right h1 k).inv_right
    rw [mul_assoc, h2.symm.eq, ← mul_assoc, hgN h hh, mul_assoc]
  have hcen : (⟨g * (e ^ k)⁻¹, hg'N⟩ : Nsub h3) ∈ Subgroup.center (Nsub h3) := by
    rw [Subgroup.mem_center_iff]
    intro h
    exact Subtype.ext (hcomm h h.2).symm
  rw [Nsub_center hV hr h3 hfr, Subgroup.mem_bot] at hcen
  have h1 : g * (e ^ k)⁻¹ = 1 := congrArg Subtype.val hcen
  have : g = e ^ k := mul_inv_eq_one.1 h1
  rw [this]
  exact Subgroup.npow_mem_zpowers e k

end OneBlock

section Frame

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore

variable [FiniteDimensional (ZMod 2) V]

theorem exists_oneBlock {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hE : IsElemAbelian 3 E) {r : ℕ}
    (hV : Module.finrank (ZMod 2) V = 2 * r + 1) (hr : 1 ≤ r) (hge : 3 ^ r ≤ Nat.card E) :
    ∃ e ∈ E, e ^ 3 = 1 ∧ Module.finrank (ZMod 2) (comSp e) = 2 := by
  classical
  haveI : Fintype E := Fintype.ofFinite E
  have hge' : 3 ^ (Module.finrank (ZMod 2) V / 2) ≤ Fintype.card E := by
    have h2 : (2 * r + 1) / 2 = r := by omega
    rw [hV, h2, ← Nat.card_eq_fintype_card]
    exact hge
  obtain ⟨k, X, ρf, hXprop, hind, hsup, hρf, hPcard, hpe⟩ := exists_struct E hE hge'
  have hPpos : 0 < Fintype.card {i // Module.finrank (ZMod 2) (X i) = 2} := by
    rw [hPcard, hV]; omega
  obtain ⟨p⟩ := Fintype.card_pos_iff.1 hPpos
  obtain ⟨e, heE, hexp⟩ := hpe p
  have hplane : ∀ i, Module.finrank (ZMod 2) (X i) = 2 →
      (∀ x ∈ X i, ρf i x = x → x = 0) ∧ (∀ g ∈ E, ∃ k : Fin 3, ∀ x ∈ X i, g x = (ρf i ^ (k : ℕ)) x) := by
    intro i hi
    rcases (hρf i).2 with ⟨h1, -⟩ | ⟨-, hfix, -, hpow⟩
    · omega
    · exact ⟨hfix, hpow⟩
  have hline : ∀ i, Module.finrank (ZMod 2) (X i) ≠ 2 → ∀ g ∈ E, ∀ x ∈ X i, g x = x := by
    intro i hi
    rcases (hρf i).2 with ⟨-, h⟩ | ⟨h2, -⟩
    · exact h
    · exact absurd h2 hi
  have hA : ∀ x ∈ X p.1, e x = ρf p.1 x := by
    intro x hx
    have h := expo_spec ((hplane p.1 p.2).2 e heE) x hx
    rw [h, hexp p]
    simp
  have hB : ∀ j, j ≠ p.1 → ∀ x ∈ X j, e x = x := by
    intro j hj x hx
    by_cases hjp : Module.finrank (ZMod 2) (X j) = 2
    · have h := expo_spec ((hplane j hjp).2 e heE) x hx
      have hne : (⟨j, hjp⟩ : {i // Module.finrank (ZMod 2) (X i) = 2}) ≠ p := fun h' =>
        hj (congrArg Subtype.val h')
      rw [h, hexp ⟨j, hjp⟩, if_neg hne]
      simp
    · exact hline j hjp e heE x hx
  have hinv : ∀ x ∈ X p.1, ρf p.1 x ∈ X p.1 := fun x hx =>
    (hXprop p.1).1 (ρf p.1) (hρf p.1).1 x hx
  have hcom : comSp e = X p.1 := by
    apply le_antisymm
    · rintro a ha
      obtain ⟨v, rfl⟩ := mem_comSp.1 ha
      refine Planes.sub_mem_of_pieces hsup e (X p.1) (fun j x hx => ?_) v
      by_cases hj : j = p.1
      · subst hj
        rw [hA x hx]
        exact (X p.1).sub_mem (hinv x hx) hx
      · rw [hB j hj x hx, sub_self]
        exact (X p.1).zero_mem
    · intro a ha
      obtain ⟨y, hy, hya⟩ := Planes.surj_of_plane p.2 hinv (hplane p.1 p.2).1 a ha
      exact mem_comSp.2 ⟨y, by rw [hA y hy]; exact hya⟩
  exact ⟨e, heE, hE.2 e heE, by rw [hcom]; exact p.2⟩

end Frame

section Rank

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Std
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Model (F4)

variable [FiniteDimensional (ZMod 2) V]

theorem exists_torus_fixed {r : ℕ} (hV : Module.finrank (ZMod 2) V = 2 * r + 1) :
    ∃ T : Subgroup (V ≃ₗ[ZMod 2] V), IsElemAbelian 3 T ∧ Nat.card T = 3 ^ r ∧
      ∃ v₀ : V, v₀ ≠ 0 ∧ ∀ g ∈ T, g v₀ = v₀ := by
  have hfin : Module.finrank (ZMod 2) V =
      Module.finrank (ZMod 2) ((Fin r → F4) × (Fin 1 → ZMod 2)) := by
    rw [finrank_block, hV]
  let e : V ≃ₗ[ZMod 2] ((Fin r → F4) × (Fin 1 → ZMod 2)) := LinearEquiv.ofFinrankEq V _ hfin
  refine ⟨(blockHom r 1).range.map (conjHom e),
    isElemAbelian_map' _ (isElemAbelian_range_blockHom _ _), ?_,
    e.symm ((0 : Fin r → F4), (fun _ => (1 : ZMod 2))), ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (conjHom_injective e), card_range_blockHom]
  · intro h
    have h1 := e.symm.injective (h.trans (map_zero e.symm).symm)
    have h2 := congrArg Prod.snd h1
    have h3 := congrFun h2 0
    simp at h3
  · rintro g ⟨_, ⟨u, rfl⟩, rfl⟩
    simp [conjHom, blockHom, blockAct, LinearEquiv.prodCongr_apply]

theorem inv_apply_of_fix {g : V ≃ₗ[ZMod 2] V} {v : V} (hg : g v = v) : g⁻¹ v = v := by
  calc g⁻¹ v = g⁻¹ (g v) := by rw [hg]
    _ = v := by rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl

theorem apply_inv_apply (g : V ≃ₗ[ZMod 2] V) (v : V) : g (g⁻¹ v) = v := by
  rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl

@[expose] noncomputable def tv (v₀ : V) (f : V →ₗ[ZMod 2] ZMod 2) (hf : f v₀ = 0) : V ≃ₗ[ZMod 2] V where
  toFun v := v + f v • v₀
  map_add' x y := by
    simp only [map_add, add_smul]
    abel
  map_smul' c x := by
    simp only [map_smul, smul_add, smul_eq_mul, RingHom.id_apply, smul_smul]
  invFun v := v + f v • v₀
  left_inv v := by
    show (v + f v • v₀) + f (v + f v • v₀) • v₀ = v
    rw [map_add, map_smul, hf, smul_zero, add_zero, add_assoc, add_self_V, add_zero]
  right_inv v := by
    show (v + f v • v₀) + f (v + f v • v₀) • v₀ = v
    rw [map_add, map_smul, hf, smul_zero, add_zero, add_assoc, add_self_V, add_zero]

theorem tv_apply (v₀ : V) (f : V →ₗ[ZMod 2] ZMod 2) (hf : f v₀ = 0) (v : V) :
    tv v₀ f hf v = v + f v • v₀ := rfl

theorem exists_twoGroup (hn : 2 ≤ Module.finrank (ZMod 2) V) {v₀ : V} (hv₀ : v₀ ≠ 0) :
    ∃ P : Subgroup (V ≃ₗ[ZMod 2] V), P ≠ ⊥ ∧ IsPGroup 2 P ∧
      ∀ g : V ≃ₗ[ZMod 2] V, g v₀ = v₀ → g ∈ Subgroup.normalizer (P : Set (V ≃ₗ[ZMod 2] V)) := by
  have hsq0 : ∀ (a : V ≃ₗ[ZMod 2] V) (f : V →ₗ[ZMod 2] ZMod 2), f v₀ = 0 →
      (∀ v, a v = v + f v • v₀) → a * a = 1 := by
    intro a f hf h
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.mul_apply, h v, map_add, map_smul, h v, h v₀, hf, zero_smul, add_zero,
      add_assoc, add_self_V, add_zero]
    rfl
  let P : Subgroup (V ≃ₗ[ZMod 2] V) :=
    { carrier := {g | ∃ f : V →ₗ[ZMod 2] ZMod 2, f v₀ = 0 ∧ ∀ v, g v = v + f v • v₀}
      mul_mem' := by
        rintro a b ⟨f₁, hf₁, h₁⟩ ⟨f₂, hf₂, h₂⟩
        refine ⟨f₁ + f₂, by simp [hf₁, hf₂], fun v => ?_⟩
        rw [LinearEquiv.mul_apply, h₂ v, map_add, map_smul, h₁ v, h₁ v₀, hf₁, zero_smul, add_zero]
        simp only [LinearMap.add_apply, add_smul]
        abel
      one_mem' := ⟨0, by simp, fun v => by simp⟩
      inv_mem' := by
        rintro a ⟨f, hf, h⟩
        have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq0 a f hf h)
        rw [hinv]
        exact ⟨f, hf, h⟩ }
  have hsq : ∀ a ∈ P, a * a = 1 := by
    rintro a ⟨f, hf, h⟩
    exact hsq0 a f hf h
  refine ⟨P, ?_, ?_, ?_⟩
  ·
    have hspan : v₀ ∈ (ZMod 2 ∙ v₀) := Submodule.mem_span_singleton_self v₀
    have hne : (ZMod 2 ∙ v₀) ≠ ⊤ := by
      intro htop
      have h1 := finrank_span_singleton (K := ZMod 2) hv₀
      have h2 : Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) V) = Module.finrank (ZMod 2) V :=
        finrank_top (ZMod 2) V
      rw [htop] at h1
      omega
    obtain ⟨w, hw⟩ : ∃ w, w ∉ (ZMod 2 ∙ v₀) := by
      by_contra hcon
      push Not at hcon
      exact hne (eq_top_iff.2 fun w _ => hcon w)
    obtain ⟨f, hfw, hfker⟩ := Submodule.exists_le_ker_of_notMem hw
    have hf0 : f v₀ = 0 := hfker hspan
    intro hbot
    have hmem : tv v₀ f hf0 ∈ P := ⟨f, hf0, fun v => rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hfw
    have := congrArg (fun g : V ≃ₗ[ZMod 2] V => g w) hmem
    simp only [tv_apply] at this
    have h2 : f w • v₀ = 0 := by
      have h3 : w + f w • v₀ = w := this
      simpa using h3
    rcases (smul_eq_zero.1 h2) with h | h
    · exact h
    · exact absurd h hv₀
  · intro a
    refine ⟨1, ?_⟩
    rw [pow_one]
    apply Subtype.ext
    simpa [pow_two] using hsq a.1 a.2
  · intro g hg
    have key : ∀ g' : V ≃ₗ[ZMod 2] V, g' v₀ = v₀ → ∀ a ∈ P, g' * a * g'⁻¹ ∈ P := by
      intro g' hg' a ⟨f, hf, h⟩
      have hgi := inv_apply_of_fix hg'
      refine ⟨f.comp (g'.symm : V ≃ₗ[ZMod 2] V).toLinearMap, ?_, fun v => ?_⟩
      · have hgi' : g'.symm v₀ = v₀ := hgi
        simp [hgi', hf]
      · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, h, map_add, map_smul, hg',
          apply_inv_apply]
        rfl
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · exact key g hg a
    · intro ha
      have := key g⁻¹ (inv_apply_of_fix hg) _ ha
      have e : g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a := by group
      rwa [e] at this

end Rank

section ThreeDvd

variable [FiniteDimensional (ZMod 2) V] {e : V ≃ₗ[ZMod 2] V}

theorem three_dvd_card_Nsub {r : ℕ} (hV : Module.finrank (ZMod 2) V = 2 * r + 1) (hr : 3 ≤ r)
    (h3 : e ^ 3 = 1) (hfr : Module.finrank (ZMod 2) (comSp e) = 2) :
    3 ∣ Nat.card (Nsub h3) := by
  have hW : Module.finrank (ZMod 2) (fixSp e) = 2 * (r - 1) + 1 := by
    have := finrank_fixSp h3
    omega
  obtain ⟨T, hTel, hTcard, -⟩ := exists_torus_fixed (V := fixSp e) hW
  have h1 : Nat.card T ∣ Nat.card (fixSp e ≃ₗ[ZMod 2] fixSp e) := Subgroup.card_subgroup_dvd_card T
  have h2 : Nat.card (Nsub h3) = Nat.card (fixSp e ≃ₗ[ZMod 2] fixSp e) :=
    Nat.card_congr (MonoidHom.ofInjective (glueHom_injective (isCompl_fixSp_comSp h3))).symm.toEquiv
  rw [h2]
  refine dvd_trans ?_ h1
  rw [hTcard]
  exact dvd_pow_self 3 (by omega)

end ThreeDvd

end CFSG.LocalAnalysis.GLTheoremA.S172A.GL

end
