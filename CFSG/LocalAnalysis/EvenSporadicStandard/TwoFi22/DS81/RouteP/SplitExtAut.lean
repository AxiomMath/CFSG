module

public import Mathlib.GroupTheory.Complement
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

variable {B : Type*} [Group B]

@[expose] def IsCrossedHom (K E : Subgroup B) (f : ↥K → ↥E) : Prop :=
  ∀ k₁ k₂ : ↥K, ((f (k₁ * k₂) : ↥E) : B) = (f k₁ : B) * ((k₁ : B) * (f k₂ : B) * (k₁ : B)⁻¹)

@[expose] def IsPrincipalCrossedHom (K E : Subgroup B) (f : ↥K → ↥E) : Prop :=
  ∃ e : ↥E, ∀ k : ↥K, ((f k : ↥E) : B) = (e : B) * ((k : B) * (e : B)⁻¹ * (k : B)⁻¹)

@[expose] def H1TrivialMod (K E : Subgroup B) : Prop :=
  ∀ f : ↥K → ↥E, IsCrossedHom K E f → (∀ k : ↥K, (k : B) ∈ E → f k = 1) →
    IsPrincipalCrossedHom K E f

@[expose] def EquivAutTrivial (K E : Subgroup B) [E.Normal] : Prop :=
  ∀ φ : ↥E ≃* ↥E,
    (∀ k : ↥K, ∀ x : ↥E, φ (MulAut.conjNormal (k : B) x) = MulAut.conjNormal (k : B) (φ x)) →
      φ = MulEquiv.refl ↥E

@[expose] def TrivialModInner (E : Subgroup B) : Prop :=
  ∀ α : B ≃* B, (∀ b : B, α b * b⁻¹ ∈ E) → ∃ e ∈ E, ∀ b : B, α b = e * b * e⁻¹

section CrossedHom

variable {K E : Subgroup B} {f : ↥K → ↥E}

theorem IsCrossedHom.map_one (hf : IsCrossedHom K E f) : f 1 = 1 := by
  have h := hf 1 1
  simp only [mul_one, OneMemClass.coe_one, inv_one, one_mul] at h
  exact Subtype.ext (by simpa using h)

theorem IsCrossedHom.coe_map_inv (hf : IsCrossedHom K E f) (k : ↥K) :
    ((f k⁻¹ : ↥E) : B) = (k : B)⁻¹ * ((f k : ↥E) : B)⁻¹ * (k : B) := by
  have h := hf k⁻¹ k
  rw [inv_mul_cancel, hf.map_one] at h
  have h2 : ((f k⁻¹ : ↥E) : B) = ((k : B)⁻¹ * (f k : B) * (k : B))⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    simpa using h.symm
  rw [h2]
  group

@[expose] def IsCrossedHom.graph (hf : IsCrossedHom K E f) : Subgroup B where
  carrier := {x | ∃ k : ↥K, x = (f k : B) * (k : B)}
  one_mem' := ⟨1, by simp [hf.map_one]⟩
  mul_mem' := by
    rintro _ _ ⟨k₁, rfl⟩ ⟨k₂, rfl⟩
    refine ⟨k₁ * k₂, ?_⟩
    rw [hf k₁ k₂]
    simp only [Subgroup.coe_mul]
    group
  inv_mem' := by
    rintro _ ⟨k, rfl⟩
    refine ⟨k⁻¹, ?_⟩
    rw [hf.coe_map_inv k]
    simp only [Subgroup.coe_inv]
    group

theorem IsCrossedHom.mem_graph (hf : IsCrossedHom K E f) {x : B} :
    x ∈ hf.graph ↔ ∃ k : ↥K, x = (f k : B) * (k : B) :=
  Iff.rfl

theorem IsCrossedHom.inf_graph_eq_bot (hf : IsCrossedHom K E f) (hinf : E ⊓ K = ⊥) :
    E ⊓ hf.graph = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro x ⟨hxE, k, rfl⟩
  have hkE : (k : B) ∈ E := by
    simpa using E.mul_mem (E.inv_mem (f k).2) hxE
  have hk1 : (k : B) = 1 := by
    have hk : (k : B) ∈ E ⊓ K := ⟨hkE, k.2⟩
    rwa [hinf, Subgroup.mem_bot] at hk
  have hk : k = 1 := Subtype.ext hk1
  subst hk
  simp [hf.map_one]

theorem IsCrossedHom.sup_graph_eq_top [E.Normal] (hf : IsCrossedHom K E f)
    (hsup : E ⊔ K = ⊤) : E ⊔ hf.graph = ⊤ := by
  rw [eq_top_iff]
  intro b _
  have hb : b ∈ (E ⊔ K : Subgroup B) := by rw [hsup]; trivial
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hb
  obtain ⟨x, hx, k, hk, rfl⟩ := hb
  have h1 : x * ((f ⟨k, hk⟩ : ↥E) : B)⁻¹ ∈ E := E.mul_mem hx (E.inv_mem (f ⟨k, hk⟩).2)
  have h2 : ((f ⟨k, hk⟩ : ↥E) : B) * k ∈ hf.graph := ⟨⟨k, hk⟩, rfl⟩
  simpa [mul_assoc] using Subgroup.mul_mem_sup h1 h2

theorem isComplement'_iff_inf_eq_bot_and_sup_eq_top [E.Normal] :
    E.IsComplement' K ↔ E ⊓ K = ⊥ ∧ E ⊔ K = ⊤ := by
  constructor
  · intro h
    exact ⟨disjoint_iff.1 h.disjoint, h.sup_eq_top⟩
  · rintro ⟨hinf, hsup⟩
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.2 hinf) ?_
    rw [← Subgroup.normal_mul, hsup]
    simp

theorem IsCrossedHom.isComplement'_graph [E.Normal] (hf : IsCrossedHom K E f) (hinf : E ⊓ K = ⊥)
    (hsup : E ⊔ K = ⊤) : E.IsComplement' hf.graph :=
  isComplement'_iff_inf_eq_bot_and_sup_eq_top.2 ⟨hf.inf_graph_eq_bot hinf, hf.sup_graph_eq_top hsup⟩

theorem existsUnique_isCrossedHom_of_isComplement [E.Normal] (hsup : E ⊔ K = ⊤)
    {K' : Subgroup B} (hinf' : E ⊓ K' = ⊥) (hsup' : E ⊔ K' = ⊤) :
    ∃! f : ↥K → ↥E, IsCrossedHom K E f ∧ ∀ x : B, x ∈ K' ↔ ∃ k : ↥K, x = (f k : B) * (k : B) := by
  have hex : ∀ b : B, ∃ e : ↥E, (e : B) * b ∈ K' := by
    intro b
    have hb : b ∈ (↑(E ⊔ K') : Set B) := by rw [hsup']; simp
    rw [Subgroup.normal_mul E K'] at hb
    obtain ⟨x, hxE, y, hyK', hxy⟩ := hb
    refine ⟨⟨x⁻¹, E.inv_mem hxE⟩, ?_⟩
    show x⁻¹ * b ∈ K'
    rw [← hxy, inv_mul_cancel_left]
    exact hyK'
  have huniq : ∀ (b : B) (e₁ e₂ : ↥E), (e₁ : B) * b ∈ K' → (e₂ : B) * b ∈ K' → e₁ = e₂ := by
    intro b e₁ e₂ h₁ h₂
    have hmem : (e₁ : B) * (e₂ : B)⁻¹ ∈ E ⊓ K' := by
      refine ⟨E.mul_mem e₁.2 (E.inv_mem e₂.2), ?_⟩
      have h : (e₁ : B) * (e₂ : B)⁻¹ = ((e₁ : B) * b) * ((e₂ : B) * b)⁻¹ := by group
      rw [h]
      exact K'.mul_mem h₁ (K'.inv_mem h₂)
    have h1 : (e₁ : B) * (e₂ : B)⁻¹ = 1 := by
      have hmem' := Subgroup.mem_bot.mp (by rw [← hinf']; exact hmem)
      simpa using hmem'
    exact Subtype.ext (mul_inv_eq_one.mp h1)
  let f : ↥K → ↥E := fun k => Classical.choose (hex k)
  have hf_mem : ∀ k : ↥K, (f k : B) * (k : B) ∈ K' := fun k => Classical.choose_spec (hex k)
  have hcross : IsCrossedHom K E f := by
    intro k₁ k₂
    have hwE : (f k₁ : B) * ((k₁ : B) * (f k₂ : B) * (k₁ : B)⁻¹) ∈ E :=
      E.mul_mem (f k₁).2 ((inferInstance : E.Normal).conj_mem (f k₂ : B) (f k₂).2 (k₁ : B))
    have hwK' : ((f k₁ : B) * ((k₁ : B) * (f k₂ : B) * (k₁ : B)⁻¹)) *
        ((k₁ * k₂ : ↥K) : B) ∈ K' := by
      have h : ((f k₁ : B) * ((k₁ : B) * (f k₂ : B) * (k₁ : B)⁻¹)) *
            ((k₁ * k₂ : ↥K) : B)
          = ((f k₁ : B) * (k₁ : B)) * ((f k₂ : B) * (k₂ : B)) := by
        simp only [Subgroup.coe_mul]
        group
      rw [h]
      exact K'.mul_mem (hf_mem k₁) (hf_mem k₂)
    have heq := huniq ((k₁ * k₂ : ↥K) : B) ⟨_, hwE⟩ (f (k₁ * k₂)) hwK' (hf_mem (k₁ * k₂))
    exact (congrArg Subtype.val heq).symm
  have hgraph : ∀ x : B, x ∈ K' ↔ ∃ k : ↥K, x = (f k : B) * (k : B) := by
    intro x
    refine ⟨?_, ?_⟩
    · intro hx
      have hxsup : x ∈ (↑(E ⊔ K) : Set B) := by rw [hsup]; simp
      rw [Subgroup.normal_mul E K] at hxsup
      obtain ⟨e, heE, k, hkK, hxek⟩ := hxsup
      let kk : ↥K := ⟨k, hkK⟩
      refine ⟨kk, ?_⟩
      have hmem : e * (f kk : B)⁻¹ ∈ E ⊓ K' := by
        refine ⟨E.mul_mem heE (E.inv_mem (f kk).2), ?_⟩
        have h : e * (f kk : B)⁻¹ = x * ((f kk : B) * (kk : B))⁻¹ := by
          rw [← hxek]
          simp only [kk]
          group
        rw [h]
        exact K'.mul_mem hx (K'.inv_mem (hf_mem kk))
      have h1 : e * (f kk : B)⁻¹ = 1 := by
        have hmem' := Subgroup.mem_bot.mp (by rw [← hinf']; exact hmem)
        simpa using hmem'
      have hef : e = (f kk : B) := mul_inv_eq_one.mp h1
      rw [← hef]
      exact hxek.symm
    · rintro ⟨k, rfl⟩
      exact hf_mem k
  refine ⟨f, ⟨hcross, hgraph⟩, ?_⟩
  intro g hg
  obtain ⟨hgc, hgg⟩ := hg
  funext k
  exact huniq (k : B) (g k) (f k)
    ((hgg ((g k : B) * (k : B))).mpr ⟨k, rfl⟩) (hf_mem k)

theorem existsUnique_isCrossedHom_of_isComplement' [E.Normal] (hsup : E ⊔ K = ⊤) {K' : Subgroup B}
    (hK' : E.IsComplement' K') :
    ∃! f : ↥K → ↥E, IsCrossedHom K E f ∧ ∀ x : B, x ∈ K' ↔ ∃ k : ↥K, x = (f k : B) * (k : B) :=
  existsUnique_isCrossedHom_of_isComplement hsup
    (isComplement'_iff_inf_eq_bot_and_sup_eq_top.1 hK').1
    (isComplement'_iff_inf_eq_bot_and_sup_eq_top.1 hK').2

end CrossedHom

section Rigidity

variable {K E : Subgroup B}

theorem h1TrivialMod_top_iff (E : Subgroup B) :
    H1TrivialMod ⊤ E ↔ ∀ F : B → ↥E,
      (∀ b₁ b₂ : B, ((F (b₁ * b₂) : ↥E) : B) = (F b₁ : B) * (b₁ * (F b₂ : B) * b₁⁻¹)) →
      (∀ b ∈ E, F b = 1) →
      ∃ e : ↥E, ∀ b : B, ((F b : ↥E) : B) = (e : B) * (b * (e : B)⁻¹ * b⁻¹) := by
  constructor
  · intro h F hF hFE
    obtain ⟨e, he⟩ := h (fun k : ↥(⊤ : Subgroup B) => F k) (fun k₁ k₂ => hF k₁ k₂)
      (fun k hk => hFE k hk)
    exact ⟨e, fun b => he ⟨b, Subgroup.mem_top b⟩⟩
  · intro h f hf hfE
    obtain ⟨e, he⟩ := h (fun b => f ⟨b, Subgroup.mem_top b⟩)
      (fun b₁ b₂ => hf ⟨b₁, Subgroup.mem_top b₁⟩ ⟨b₂, Subgroup.mem_top b₂⟩)
      (fun b hb => hfE ⟨b, Subgroup.mem_top b⟩ hb)
    exact ⟨e, fun k => he k⟩

theorem isCrossedHom_of_trivialMod (K : Subgroup B) {E : Subgroup B} (α : B ≃* B)
    (hα : ∀ b : B, α b * b⁻¹ ∈ E) :
    IsCrossedHom K E (fun k : ↥K => (⟨α k * (k : B)⁻¹, hα k⟩ : ↥E)) := by
  intro k₁ k₂
  simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
  group

theorem equivAutTrivial_top_iff (E : Subgroup B) [E.Normal] :
    EquivAutTrivial ⊤ E ↔ ∀ φ : ↥E ≃* ↥E,
      (∀ (b : B) (x : ↥E), φ (MulAut.conjNormal b x) = MulAut.conjNormal b (φ x)) →
        φ = MulEquiv.refl ↥E :=
  ⟨fun h φ hφ => h φ fun k x => hφ k x, fun h φ hφ => h φ fun b x => hφ ⟨b, Subgroup.mem_top b⟩ x⟩

@[expose] def autOfTrivialMod {E : Subgroup B} (β : B ≃* B) (hβ : ∀ b : B, β b * b⁻¹ ∈ E) :
    ↥E ≃* ↥E where
  toFun x := ⟨β x, by
    have h := E.mul_mem (hβ x) x.2
    rwa [inv_mul_cancel_right] at h⟩
  invFun x := ⟨β.symm x, by
    have h := E.mul_mem (E.inv_mem (hβ (β.symm x))) x.2
    rwa [β.apply_symm_apply, mul_inv_rev, inv_inv, inv_mul_cancel_right] at h⟩
  left_inv x := Subtype.ext (β.symm_apply_apply x)
  right_inv x := Subtype.ext (β.apply_symm_apply x)
  map_mul' x y := Subtype.ext (map_mul β (x : B) (y : B))

theorem coe_autOfTrivialMod {E : Subgroup B} (β : B ≃* B) (hβ : ∀ b : B, β b * b⁻¹ ∈ E)
    (x : ↥E) : ((autOfTrivialMod β hβ x : ↥E) : B) = β x :=
  rfl

theorem eq_refl_of_fixes_sup (hsup : E ⊔ K = ⊤) (γ : B ≃* B) (hE : ∀ x ∈ E, γ x = x)
    (hK : ∀ k ∈ K, γ k = k) : γ = MulEquiv.refl B := by
  have hle : E ⊔ K ≤ MonoidHom.eqLocus γ.toMonoidHom (MonoidHom.id B) := by
    refine sup_le (fun x hx => ?_) (fun k hk => ?_)
    · exact hE x hx
    · exact hK k hk
  have htop : MonoidHom.eqLocus γ.toMonoidHom (MonoidHom.id B) = ⊤ :=
    le_antisymm le_top (hsup.ge.trans hle)
  refine MulEquiv.ext fun b => ?_
  have hb : γ b = b := by
    have : b ∈ MonoidHom.eqLocus γ.toMonoidHom (MonoidHom.id B) := by
      rw [htop]; trivial
    exact this
  simpa using hb

theorem forall_eq_conj_of_eq_conj_on [E.Normal] (hsup : E ⊔ K = ⊤) (hEnd : EquivAutTrivial K E)
    (α : B ≃* B) (hα : ∀ b : B, α b * b⁻¹ ∈ E) (e : ↥E)
    (h : ∀ k : ↥K, α k = (e : B) * k * (e : B)⁻¹) : ∀ b : B, α b = (e : B) * b * (e : B)⁻¹ := by
  let γ : B ≃* B := α.trans (MulAut.conj ((e : B)⁻¹))
  have hγb : ∀ b : B, γ b = (e : B)⁻¹ * α b * (e : B) := by
    intro b
    simp [γ, MulAut.conj_apply]
  have hγ : ∀ b : B, γ b * b⁻¹ ∈ E := by
    intro b
    have hconj : b * (e : B) * b⁻¹ ∈ E := (inferInstance : E.Normal).conj_mem (e : B) e.2 b
    have heq : γ b * b⁻¹ = (e : B)⁻¹ * (α b * b⁻¹) * (b * (e : B) * b⁻¹) := by
      rw [hγb b]; group
    rw [heq]
    exact E.mul_mem (E.mul_mem (E.inv_mem e.2) (hα b)) hconj
  have hγK : ∀ k : ↥K, γ (k : B) = (k : B) := by
    intro k
    rw [hγb (k : B), h k]
    group
  have hcomm : ∀ k : ↥K, ∀ x : ↥E,
      autOfTrivialMod γ hγ (MulAut.conjNormal (k : B) x) =
        MulAut.conjNormal (k : B) (autOfTrivialMod γ hγ x) := by
    intro k x
    apply Subtype.ext
    simp only [coe_autOfTrivialMod, MulAut.conjNormal_apply, map_mul, map_inv, hγK k]
  have hreflE : autOfTrivialMod γ hγ = MulEquiv.refl ↥E := hEnd _ hcomm
  have hfixE : ∀ x : ↥E, γ (x : B) = (x : B) := by
    intro x
    have := congrArg (fun f : ↥E ≃* ↥E => (f x : B)) hreflE
    simpa [coe_autOfTrivialMod] using this
  have hfixK : ∀ k ∈ K, γ k = k := fun k hk => hγK ⟨k, hk⟩
  have hfixE' : ∀ x ∈ E, γ x = x := fun x hx => hfixE ⟨x, hx⟩
  have hγrefl : γ = MulEquiv.refl B := eq_refl_of_fixes_sup hsup γ hfixE' hfixK
  intro b
  have hb : γ b = b := by
    have := congrArg (fun f : B ≃* B => f b) hγrefl
    simpa using this
  rw [hγb b] at hb
  calc α b = (e : B) * ((e : B)⁻¹ * α b * (e : B)) * (e : B)⁻¹ := by group
    _ = (e : B) * b * (e : B)⁻¹ := by rw [hb]

theorem trivialModInner_of_h1TrivialMod [E.Normal] (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hsup : E ⊔ K = ⊤) (hH1 : H1TrivialMod K E) (hEnd : EquivAutTrivial K E) :
    TrivialModInner E := by
  intro α hα
  have hcomm : ∀ k : ↥K, ∀ x : ↥E,
      autOfTrivialMod α hα (MulAut.conjNormal (k : B) x) =
        MulAut.conjNormal (k : B) (autOfTrivialMod α hα x) := by
    intro k x
    apply Subtype.ext
    simp only [coe_autOfTrivialMod, MulAut.conjNormal_apply]
    have hy : (k : B) * α x * (k : B)⁻¹ ∈ E := by
      have hαx : α x ∈ E := (autOfTrivialMod α hα x).2
      exact (inferInstance : E.Normal).conj_mem _ hαx _
    have hd : α k * (k : B)⁻¹ ∈ E := hα k
    have h1 : α ((k : B) * (x : B) * (k : B)⁻¹) = (α k * (k : B)⁻¹) * ((k : B) * α x * (k : B)⁻¹) *
        (α k * (k : B)⁻¹)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      group
    rw [h1, hE _ hd _ hy]
    group
  have hfixE : ∀ x : ↥E, α (x : B) = (x : B) := fun x => by
    have := congrArg (fun f : ↥E ≃* ↥E => (f x : B)) (hEnd _ hcomm)
    simpa [coe_autOfTrivialMod] using this
  obtain ⟨e, he⟩ := hH1 _ (isCrossedHom_of_trivialMod K α hα)
    fun k hk => Subtype.ext (by simp [hfixE ⟨k, hk⟩])
  have hconj : ∀ k : ↥K, α k = (e : B) * k * (e : B)⁻¹ := fun k => by
    have h : α k * (k : B)⁻¹ = (e : B) * ((k : B) * (e : B)⁻¹ * (k : B)⁻¹) := he k
    calc α k = (α k * (k : B)⁻¹) * k := by group
      _ = _ := by rw [h]; group
  exact ⟨e, e.2, forall_eq_conj_of_eq_conj_on hsup hEnd α hα e hconj⟩

theorem trivialModInner_of_forall_crossedHom [E.Normal] (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hH1 : ∀ F : B → ↥E,
      (∀ b₁ b₂ : B, ((F (b₁ * b₂) : ↥E) : B) = (F b₁ : B) * (b₁ * (F b₂ : B) * b₁⁻¹)) →
      (∀ b ∈ E, F b = 1) →
      ∃ e : ↥E, ∀ b : B, ((F b : ↥E) : B) = (e : B) * (b * (e : B)⁻¹ * b⁻¹))
    (hEnd : ∀ φ : ↥E ≃* ↥E,
      (∀ (b : B) (x : ↥E), φ (MulAut.conjNormal b x) = MulAut.conjNormal b (φ x)) →
        φ = MulEquiv.refl ↥E) :
    TrivialModInner E :=
  trivialModInner_of_h1TrivialMod hE (sup_top_eq E) ((h1TrivialMod_top_iff E).2 hH1)
    ((equivAutTrivial_top_iff E).2 hEnd)

end Rigidity

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
