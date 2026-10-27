module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.AGL81I542

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.AutImageStar

open CFSG.Open
open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

section Transport

@[expose] def mulAutTransport {A B : Type} [Group A] [Group B] (φ : A ≃* B) :
    MulAut A ≃* MulAut B where
  toFun f := φ.symm.trans (f.trans φ)
  invFun g := φ.trans (g.trans φ.symm)
  left_inv f := by ext a; simp
  right_inv g := by ext b; simp
  map_mul' f g := by ext b; simp [MulAut.mul_apply]

theorem mulAutTransport_apply {A B : Type} [Group A] [Group B] (φ : A ≃* B) (f : MulAut A)
    (b : B) : mulAutTransport φ f b = φ (f (φ.symm b)) :=
  rfl

theorem mulAutTransport_conj {A B : Type} [Group A] [Group B] (φ : A ≃* B) (a : A) :
    mulAutTransport φ (MulAut.conj a) = MulAut.conj (φ a) := by
  ext b
  simp [mulAutTransport_apply, MulAut.conj_apply]

theorem innSub_map_transport {A B : Type} [Group A] [Group B] (φ : A ≃* B) :
    (innSub A).map (mulAutTransport φ).toMonoidHom = innSub B := by
  unfold innSub
  rw [MonoidHom.map_range]
  ext x
  simp only [MonoidHom.mem_range, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨φ a, (mulAutTransport_conj φ a).symm⟩
  · rintro ⟨b, rfl⟩
    exact ⟨φ.symm b, by rw [mulAutTransport_conj, MulEquiv.apply_symm_apply]⟩

@[expose] noncomputable def subgroupEquivOfMap {G G' : Type} [Group G] [Group G']
    (ψ : G ≃* G') (H : Subgroup G) (K : Subgroup G') (h : H.map ψ.toMonoidHom = K) :
    ↥H ≃* ↥K :=
  (Subgroup.equivMapOfInjective H ψ.toMonoidHom ψ.injective).trans (MulEquiv.subgroupCongr h)

theorem statedPSL_of_equiv {G G' : Type} [Group G] [Group G'] {n p f : ℕ} (e : G ≃* G')
    (h : StatedClassicalModel G .PSL n p f) : StatedClassicalModel G' .PSL n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e h

end Transport

section Quotient

variable {H : Type} [Group H]

@[expose] def quotMapHom (N₁ N₂ : Subgroup H) [N₁.Normal] [N₂.Normal] (h12 : N₁ ≤ N₂) :
    H ⧸ N₁ →* H ⧸ N₂ :=
  QuotientGroup.map N₁ N₂ (MonoidHom.id H) (fun _ hx => h12 hx)

theorem mem_map_quotMapHom (K N₁ N₂ : Subgroup H) [N₁.Normal] [N₂.Normal] (h12 : N₁ ≤ N₂)
    {z : H ⧸ N₁} (hz : z ∈ K.map (QuotientGroup.mk' N₁)) :
    quotMapHom N₁ N₂ h12 z ∈ K.map (QuotientGroup.mk' N₂) := by
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hz
  exact Subgroup.mem_map.mpr ⟨k, hk, rfl⟩

@[expose] noncomputable def quotMapEquiv (K N₁ N₂ : Subgroup H) [N₁.Normal] [N₂.Normal]
    (h12 : N₁ ≤ N₂) (hKN : K ⊓ N₂ = N₁) :
    ↥(K.map (QuotientGroup.mk' N₁)) ≃* ↥(K.map (QuotientGroup.mk' N₂)) := by
  let f : ↥(K.map (QuotientGroup.mk' N₁)) →* ↥(K.map (QuotientGroup.mk' N₂)) :=
    { toFun := fun z => ⟨quotMapHom N₁ N₂ h12 z.1, mem_map_quotMapHom K N₁ N₂ h12 z.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · intro a b h
    obtain ⟨z, hz⟩ := a
    obtain ⟨w, hw⟩ := b
    have h' : quotMapHom N₁ N₂ h12 z = quotMapHom N₁ N₂ h12 w := congrArg Subtype.val h
    obtain ⟨k1, hk1, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨k2, hk2, rfl⟩ := Subgroup.mem_map.mp hw
    have h'' : QuotientGroup.mk' N₂ k1 = QuotientGroup.mk' N₂ k2 := h'
    have hmem : k1⁻¹ * k2 ∈ K ⊓ N₂ :=
      ⟨K.mul_mem (K.inv_mem hk1) hk2, QuotientGroup.eq.mp h''⟩
    rw [hKN] at hmem
    apply Subtype.ext
    exact QuotientGroup.eq.mpr hmem
  · intro y
    obtain ⟨y, hy⟩ := y
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
    refine ⟨⟨QuotientGroup.mk' N₁ k, Subgroup.mem_map.mpr ⟨k, hk, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    rfl

end Quotient

section Aut

variable {X W : Type} [Group X] [Group W]

theorem map_autImage_eq_autIn (N : Subgroup X) [N.Normal] (Y : Subgroup W) [Y.Normal]
    (π : X →* W) (hπ : Function.Surjective π) (φ : ↥N ≃* ↥Y)
    (hφ : ∀ n : ↥N, (φ n : W) = π (n : X)) :
    (autImage N).map (mulAutTransport φ).toMonoidHom = autIn Y := by
  have hmem : ∀ x : X, π x ∈ Subgroup.normalizer (Y : Set W) := fun x => by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top _
  have hz : ∀ y : ↥Y, π ((φ.symm y : ↥N) : X) = (y : W) := fun y => by
    rw [← hφ]
    simp
  have happ : ∀ (n : W) (hn : n ∈ Subgroup.normalizer (Y : Set W)) (y : ↥Y),
      ((Y.normalizerMonoidHom ⟨n, hn⟩ y : ↥Y) : W) = n * y * n⁻¹ :=
    fun _ _ _ => rfl
  have key : ∀ x : X, mulAutTransport φ (MulAut.conjNormal x) =
      Y.normalizerMonoidHom ⟨π x, hmem x⟩ := by
    intro x
    ext y
    simp only [mulAutTransport_apply, happ]
    rw [← hz y]
    simp [hφ, map_mul, map_inv]
  unfold autImage autIn
  rw [MonoidHom.map_range]
  ext w
  simp only [MonoidHom.mem_range, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨π x, hmem x⟩, (key x).symm⟩
  · rintro ⟨⟨n, hn⟩, rfl⟩
    obtain ⟨x, rfl⟩ := hπ n
    exact ⟨x, key x⟩

end Aut

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.AutImageStar
