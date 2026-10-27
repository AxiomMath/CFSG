module

public import CFSG.ClassicalInvolution.SmallOrth.OrthSmall
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Orth

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V]

@[expose] def elemOn (Q : QuadraticForm F V) (S : Submodule F V) : Subgroup (V ≃ₗ[F] V) :=
  Subgroup.closure {g | ∃ u w, u ∈ S ∧ w ∈ S ∧ Q u = 0 ∧ polar Q u w = 0 ∧ eichler Q u w = g}

variable {Q : QuadraticForm F V} {S : Submodule F V}

theorem eichler_mem_elemOn {u w : V} (hu : u ∈ S) (hw : w ∈ S) : eichler Q u w ∈ elemOn Q S := by
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · exact Subgroup.subset_closure ⟨u, w, hu, hw, h.1, h.2, rfl⟩
  · rw [eichler_of_not h]
    exact Subgroup.one_mem _

theorem elemOn_le_elementaryGroup : elemOn Q S ≤ elementaryGroup Q := by
  rw [elemOn, Subgroup.closure_le]
  rintro _ ⟨u, w, -, -, hu, hw, rfl⟩
  exact Subgroup.subset_closure ⟨u, w, hu, hw, rfl⟩

theorem support_of_mem_elemOn {g : V ≃ₗ[F] V} (hg : g ∈ elemOn Q S) :
    (∀ x, x ∈ S ↔ g x ∈ S) ∧ ∀ z, (∀ x ∈ S, polar Q z x = 0) → g z = z := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨u, w, hu, hw, -, -, rfl⟩ := hg
    refine ⟨fun x => ?_, fun z hz => eichler_apply_of_polar_eq_zero (hz u hu) (hz w hw)⟩
    obtain ⟨a, b, hab⟩ := eichler_apply_eq_add (Q := Q) u w x
    have hd : eichler Q u w x - x ∈ S := by
      have e : eichler Q u w x - x = a • w + b • u := by rw [hab]; abel
      rw [e]
      exact S.add_mem (S.smul_mem a hw) (S.smul_mem b hu)
    constructor
    · intro hx
      have := S.add_mem hd hx
      rwa [sub_add_cancel] at this
    · intro hx
      have := S.sub_mem hx hd
      rwa [sub_sub_cancel] at this
  | one => exact ⟨fun x => Iff.rfl, fun z _ => rfl⟩
  | mul a b _ _ iha ihb =>
    refine ⟨fun x => ?_, fun z hz => ?_⟩
    · rw [LinearEquiv.mul_apply, ← iha.1 (b x), ← ihb.1 x]
    · rw [LinearEquiv.mul_apply, ihb.2 z hz, iha.2 z hz]
  | inv a _ iha =>
    refine ⟨fun x => ?_, fun z hz => ?_⟩
    · rw [iha.1 (a⁻¹ x), LinearEquiv.apply_inv_apply']
    · apply a.injective
      rw [LinearEquiv.apply_inv_apply', iha.2 z hz]

theorem conj_mem_elemOn {g : V ≃ₗ[F] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgS : ∀ x, x ∈ S ↔ g x ∈ S) {h : V ≃ₗ[F] V} (hh : h ∈ elemOn Q S) :
    g * h * g⁻¹ ∈ elemOn Q S := by
  have hle : elemOn Q S ≤ (elemOn Q S).comap (MulAut.conj g).toMonoidHom := by
    rw [elemOn, Subgroup.closure_le]
    rintro _ ⟨u, w, hu, hw, -, -, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      eichler_conj hg]
    exact eichler_mem_elemOn ((hgS u).mp hu) ((hgS w).mp hw)
  exact hle hh

theorem comm_of_scalar_elemOn {s : V ≃ₗ[F] V} (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {ε : F} (hε : ε * ε = 1) (hsS : ∀ x ∈ S, s x = ε • x) {h : V ≃ₗ[F] V}
    (hh : h ∈ elemOn Q S) : s * h = h * s := by
  have hc : elemOn Q S ≤ Subgroup.centralizer ({s} : Set (V ≃ₗ[F] V)) := by
    rw [elemOn, Subgroup.closure_le]
    rintro _ ⟨u, w, hu, hw, -, -, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have := eichler_conj hs u w
    rw [hsS u hu, hsS w hw, eichler_smul_left, smul_smul, hε, one_smul] at this
    exact (mul_inv_eq_iff_eq_mul.mp this).symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hc hh)).symm

section Restrict

theorem isCompl_perp [FiniteDimensional F V] (hS : (polarBilin (Q.restrict S)).Nondegenerate) :
    IsCompl S (LinearMap.BilinForm.orthogonal (polarBilin Q) S) := by
  have h : polarBilin (Q.comp S.subtype) = LinearMap.BilinForm.restrict (polarBilin Q) S := by
    refine LinearMap.ext₂ fun x y => ?_
    simp [polarBilin_apply_apply, polar]
  exact LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
    (isSymm_polarBilin Q).isRefl (by rw [← h]; exact hS)

theorem mem_perp_iff {z : V} :
    z ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) S ↔ ∀ x ∈ S, polar Q z x = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h x hx
    have := h x hx
    rw [polarBilin_apply_apply] at this
    rw [polar_comm]
    exact this
  · intro h x hx
    show polarBilin Q x z = 0
    rw [polarBilin_apply_apply, polar_comm]
    exact h x hx

theorem eq_of_agree_on [FiniteDimensional F V] (hS : (polarBilin (Q.restrict S)).Nondegenerate)
    {g h : V ≃ₗ[F] V} (hgh : ∀ x ∈ S, g x = h x)
    (hg : ∀ z, (∀ x ∈ S, polar Q z x = 0) → g z = z)
    (hh : ∀ z, (∀ x ∈ S, polar Q z x = 0) → h z = z) : g = h := by
  refine LinearEquiv.ext fun v => ?_
  have hv : v ∈ S ⊔ LinearMap.BilinForm.orthogonal (polarBilin Q) S := by
    rw [(isCompl_perp hS).sup_eq_top]
    trivial
  obtain ⟨x, hx, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, map_add, hgh x hx, hg z (mem_perp_iff.mp hz), hh z (mem_perp_iff.mp hz)]

@[expose] def resAux (g : V ≃ₗ[F] V) (hg : ∀ x, x ∈ S ↔ g x ∈ S) : S ≃ₗ[F] S where
  toFun r := ⟨g r, (hg r).mp r.2⟩
  map_add' x y := Subtype.ext (map_add g (x : V) (y : V))
  map_smul' c x := Subtype.ext (map_smul g c (x : V))
  invFun r := ⟨g⁻¹ r, (hg (g⁻¹ r)).mpr (by rw [LinearEquiv.apply_inv_apply']; exact r.2)⟩
  left_inv r := Subtype.ext (LinearEquiv.inv_apply_apply' g (r : V))
  right_inv r := Subtype.ext (LinearEquiv.apply_inv_apply' g (r : V))

theorem coe_resAux (g : V ≃ₗ[F] V) (hg : ∀ x, x ∈ S ↔ g x ∈ S) (r : S) :
    ((resAux g hg r : S) : V) = g r := rfl

@[expose] noncomputable def resHom (Q : QuadraticForm F V) (S : Submodule F V) :
    elemOn Q S →* (S ≃ₗ[F] S) where
  toFun g := resAux g.1 (support_of_mem_elemOn g.2).1
  map_one' := LinearEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => Subtype.ext rfl

theorem coe_resHom (g : elemOn Q S) (r : S) : ((resHom Q S g r : S) : V) = g.1 r := rfl

theorem resAux_eichler {u w : V} (hu : u ∈ S) (hw : w ∈ S) :
    resAux (eichler Q u w) (support_of_mem_elemOn (eichler_mem_elemOn hu hw)).1 =
      eichler (Q.restrict S) ⟨u, hu⟩ ⟨w, hw⟩ := by
  refine LinearEquiv.ext fun r => Subtype.ext ?_
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · have h' : Q.restrict S ⟨u, hu⟩ = 0 ∧ polar (Q.restrict S) ⟨u, hu⟩ ⟨w, hw⟩ = 0 := by
      refine ⟨h.1, ?_⟩
      rw [polar_restrict]
      exact h.2
    rw [coe_resAux, eichler_apply h.1 h.2, eichler_apply h'.1 h'.2]
    simp [polar_restrict]
  · have h' : ¬(Q.restrict S ⟨u, hu⟩ = 0 ∧ polar (Q.restrict S) ⟨u, hu⟩ ⟨w, hw⟩ = 0) := by
      rwa [polar_restrict]
    rw [coe_resAux, eichler_of_not h, eichler_of_not h']
    rfl

theorem resAux_mem_elementaryGroup {g : V ≃ₗ[F] V} (hg : g ∈ elemOn Q S) :
    ∀ hgS : (∀ x, x ∈ S ↔ g x ∈ S), resAux g hgS ∈ elementaryGroup (Q.restrict S) := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨u, w, hu, hw, hQu, hQw, rfl⟩ := hg
    intro hgS
    have : resAux (eichler Q u w) hgS = eichler (Q.restrict S) ⟨u, hu⟩ ⟨w, hw⟩ :=
      resAux_eichler hu hw
    rw [this]
    exact eichler_mem_elementaryGroup _ _ _
  | one =>
    intro hgS
    have : resAux (1 : V ≃ₗ[F] V) hgS = 1 := LinearEquiv.ext fun r => Subtype.ext rfl
    rw [this]
    exact Subgroup.one_mem _
  | mul a b ha hb iha ihb =>
    intro hgS
    have : resAux (a * b) hgS =
        resAux a (support_of_mem_elemOn ha).1 * resAux b (support_of_mem_elemOn hb).1 :=
      LinearEquiv.ext fun r => Subtype.ext rfl
    rw [this]
    exact Subgroup.mul_mem _ (iha _) (ihb _)
  | inv a ha iha =>
    intro hgS
    have : resAux a⁻¹ hgS = (resAux a (support_of_mem_elemOn ha).1)⁻¹ :=
      LinearEquiv.ext fun r => Subtype.ext (by
        change a⁻¹ r = ((resAux a (support_of_mem_elemOn ha).1)⁻¹ r : S)
        apply a.injective
        rw [LinearEquiv.apply_inv_apply']
        have := LinearEquiv.apply_symm_apply (resAux a (support_of_mem_elemOn ha).1) r
        exact (congrArg Subtype.val this).symm)
    rw [this]
    exact Subgroup.inv_mem _ (iha _)

theorem resHom_mem_elementaryGroup (g : elemOn Q S) :
    resHom Q S g ∈ elementaryGroup (Q.restrict S) :=
  resAux_mem_elementaryGroup g.2 (support_of_mem_elemOn g.2).1

theorem elementaryGroup_le_range_resHom :
    elementaryGroup (Q.restrict S) ≤ (resHom Q S).range := by
  rw [elementaryGroup, Subgroup.closure_le]
  rintro _ ⟨u, w, hu, hw, rfl⟩
  have hu' : (u : V) ∈ S := u.2
  have hw' : (w : V) ∈ S := w.2
  exact ⟨⟨eichler Q u w, eichler_mem_elemOn hu' hw'⟩, resAux_eichler hu' hw'⟩

theorem range_resHom : (resHom Q S).range = elementaryGroup (Q.restrict S) :=
  le_antisymm (by rintro _ ⟨g, rfl⟩; exact resHom_mem_elementaryGroup g)
    elementaryGroup_le_range_resHom

theorem resHom_injective [FiniteDimensional F V] (hS : (polarBilin (Q.restrict S)).Nondegenerate) :
    Function.Injective (resHom Q S) := by
  intro g h hgh
  apply Subtype.ext
  refine eq_of_agree_on hS (fun x hx => ?_) (support_of_mem_elemOn g.2).2
    (support_of_mem_elemOn h.2).2
  have := congrArg (fun e : S ≃ₗ[F] S => ((e ⟨x, hx⟩ : S) : V)) hgh
  exact this

end Restrict

section Small

theorem exists_smul_of_finrank_le_two [FiniteDimensional F V] (hS : PolarNondegOn Q S)
    (h2 : Module.finrank F S ≤ 2) {u w : V} (hu : u ∈ S) (hw : w ∈ S) (hQu : Q u = 0)
    (hu0 : u ≠ 0) (huw : polar Q u w = 0) : ∃ c : F, w = c • u := by
  obtain ⟨y, hy, hyu⟩ := hS.exists_polar_ne_zero hu hu0
  by_contra hno
  push Not at hno
  have hli : LinearIndependent F ![u, y, w] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
    have h1 : g 1 = 0 := by
      have := congrArg (polar Q u) hg
      rw [polar_add_right, polar_add_right, polar_smul_right_eq, polar_smul_right_eq,
        polar_smul_right_eq, polar_self_eq_zero hQu, huw, polar_zero_right] at this
      simp only [mul_zero, zero_add, add_zero] at this
      exact (mul_eq_zero.mp this).resolve_right hyu
    rw [h1, zero_smul, add_zero] at hg
    have h2' : g 2 = 0 := by
      by_contra h2'
      apply hno (-((g 2)⁻¹ * g 0))
      have : g 2 • w = -(g 0 • u) := eq_neg_of_add_eq_zero_right hg
      calc w = (g 2)⁻¹ • (g 2 • w) := by rw [smul_smul, inv_mul_cancel₀ h2', one_smul]
        _ = (-((g 2)⁻¹ * g 0)) • u := by rw [this, smul_neg, smul_smul, neg_smul]
    rw [h2', zero_smul, add_zero] at hg
    have h0 : g 0 = 0 := (smul_eq_zero.mp hg).resolve_right hu0
    intro i
    fin_cases i <;> simp [h0, h1, h2']
  have hspan : Submodule.span F (Set.range ![u, y, w]) ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hu
    · exact hy
    · exact hw
  have := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hli, Fintype.card_fin] at this
  omega

theorem elemOn_eq_bot_of_finrank_le_two [FiniteDimensional F V] (hS : PolarNondegOn Q S)
    (h2 : Module.finrank F S ≤ 2) : elemOn Q S = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [elemOn, Subgroup.closure_le]
  rintro _ ⟨u, w, hu, hw, hQu, huw, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_bot]
  by_cases hu0 : u = 0
  · rw [hu0, eichler_zero_left]
  obtain ⟨c, rfl⟩ := exists_smul_of_finrank_le_two hS h2 hu hw hQu hu0 huw
  have := eichler_add_smul_self hQu 0 c
  rw [zero_add, eichler_zero_right] at this
  exact this

end Small

section Layer

theorem isQuasisimple_of_mulEquiv_open {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B :=
  hA.of_mulEquiv e.symm

@[expose] def LayerGenOn (Q : QuadraticForm F V) (S : Submodule F V) : Prop :=
  ∃ 𝓗 : Set (Subgroup (V ≃ₗ[F] V)),
    (∀ H ∈ 𝓗, H ≤ elemOn Q S ∧ CFSG.Open.IsQuasisimple ↥H ∧
      ∀ g ∈ elemOn Q S, ∀ h ∈ H, g * h * g⁻¹ ∈ H) ∧
    elemOn Q S ≤ ⨆ H ∈ 𝓗, H

@[expose] noncomputable def resEquiv [FiniteDimensional F V]
    (hS : (polarBilin (Q.restrict S)).Nondegenerate) :
    elemOn Q S ≃* elementaryGroup (Q.restrict S) :=
  MulEquiv.ofBijective ((resHom Q S).codRestrict (elementaryGroup (Q.restrict S))
    resHom_mem_elementaryGroup) ⟨fun g h hgh => resHom_injective hS (Subtype.ext_iff.mp hgh), by
      rintro ⟨x, hx⟩
      obtain ⟨g, hg⟩ := elementaryGroup_le_range_resHom hx
      exact ⟨g, Subtype.ext hg⟩⟩

theorem coe_resEquiv [FiniteDimensional F V] (hS : (polarBilin (Q.restrict S)).Nondegenerate)
    (g : elemOn Q S) : ((resEquiv hS g : elementaryGroup (Q.restrict S)) : S ≃ₗ[F] S) =
      resHom Q S g := rfl

theorem layerGenOn_of_generatedBy [FiniteDimensional F V]
    (hS : (polarBilin (Q.restrict S)).Nondegenerate) (h : GeneratedByQuasisimple (Q.restrict S)) :
    LayerGenOn Q S := by
  obtain ⟨𝓗₀, h𝓗₀, hcover⟩ := h
  set E : Subgroup (S ≃ₗ[F] S) := elementaryGroup (Q.restrict S) with hE
  set e : elemOn Q S ≃* E := resEquiv hS with he
  set ι : E →* (V ≃ₗ[F] V) := (elemOn Q S).subtype.comp e.symm.toMonoidHom with hι
  have hιinj : Function.Injective ι := fun x y hxy =>
    e.symm.injective (Subtype.ext hxy)
  have hιe : ∀ g : elemOn Q S, ι (e g) = g.1 := fun g => by simp [hι]
  refine ⟨(fun H₀ => (H₀.subgroupOf E).map ι) '' 𝓗₀, ?_, ?_⟩
  · rintro _ ⟨H₀, hH₀, rfl⟩
    obtain ⟨hle, hq, hnorm⟩ := h𝓗₀ H₀ hH₀
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨y, -, rfl⟩
      exact (e.symm y).2
    · exact isQuasisimple_of_mulEquiv_open
        ((Subgroup.subgroupOfEquivOfLe hle).symm.trans
          (Subgroup.equivMapOfInjective _ ι hιinj)) hq
    · rintro g hg _ ⟨y, hy, rfl⟩
      have hgg : ι (e ⟨g, hg⟩) = g := hιe ⟨g, hg⟩
      refine ⟨e ⟨g, hg⟩ * y * (e ⟨g, hg⟩)⁻¹, ?_, ?_⟩
      · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy ⊢
        exact hnorm _ (e ⟨g, hg⟩).2 _ hy
      · rw [map_mul, map_mul, map_inv, hgg]
  · intro g hg
    have hmap : (⨆ H₀ ∈ 𝓗₀, H₀.subgroupOf E).map E.subtype = ⨆ H₀ ∈ 𝓗₀, H₀ := by
      rw [Subgroup.map_iSup]
      refine iSup_congr fun H₀ => ?_
      rw [Subgroup.map_iSup]
      refine iSup_congr fun hH₀ => ?_
      exact Subgroup.map_subgroupOf_eq_of_le (h𝓗₀ H₀ hH₀).1
    have htop : (⊤ : Subgroup E) ≤ ⨆ H₀ ∈ 𝓗₀, H₀.subgroupOf E := by
      rw [← Subgroup.map_le_map_iff_of_injective E.subtype_injective, hmap,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact hcover
    have hmem : e ⟨g, hg⟩ ∈ ⨆ H₀ ∈ 𝓗₀, H₀.subgroupOf E := htop (Subgroup.mem_top _)
    have h2 := Subgroup.mem_map_of_mem ι hmem
    rw [hιe ⟨g, hg⟩] at h2
    refine (Subgroup.map_le_iff_le_comap.mpr ?_ : (⨆ H₀ ∈ 𝓗₀, H₀.subgroupOf E).map ι ≤
      ⨆ H ∈ (fun H₀ => (H₀.subgroupOf E).map ι) '' 𝓗₀, H) h2
    refine iSup₂_le fun H₀ hH₀ => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_iSup₂_of_le ((H₀.subgroupOf E).map ι) ⟨H₀, hH₀, rfl⟩ le_rfl

theorem generatedByQuasisimple_of_regular {W : Type} [AddCommGroup W] [Module F W]
    [Finite F] [FiniteDimensional F W] (Q' : QuadraticForm F W) (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) (hQ : (polarBilin Q').Nondegenerate) (h3 : 3 ≤ Module.finrank F W) :
    GeneratedByQuasisimple Q' := by
  by_cases hd : 5 ≤ Module.finrank F W
  · refine ⟨{elementaryGroup Q'}, ?_, ?_⟩
    · rintro H rfl
      exact ⟨le_rfl,
        CFSG.ClassicalGroups.Orthogonal.Small.isQuasisimple_elementaryGroup_of_five_le_finrank
          hodd h5 hQ hd, fun g hg x hx => mul_mem (mul_mem hg hx) (inv_mem hg)⟩
    · exact le_iSup₂_of_le (elementaryGroup Q') (by simp) le_rfl
  · exact orthSmallLayer F W Q' hQ hodd h5 h3 (by omega)

theorem layerGenOn [Finite F] [FiniteDimensional F V]
    (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hS : (polarBilin (Q.restrict S)).Nondegenerate) (h3 : 3 ≤ Module.finrank F S) :
    LayerGenOn Q S :=
  layerGenOn_of_generatedBy hS (generatedByQuasisimple_of_regular _ hodd h5 hS h3)

end Layer

end CFSG.ClassicalInvolution.Balance.StrongBalance.Orth
