module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverCore

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open Subgroup BinarySymplecticSix
open scoped commutatorElement Pointwise

theorem ker_le_of_sylow_le_map {E G : Type*} [Group E] [Group G] [Finite E]
    [Group.IsPerfect E] (η : E →* G) (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E)
    (h2 : IsPGroup 2 η.ker) (S : Sylow 2 G) (P₀ : Subgroup E)
    (hS : (S : Subgroup G) ≤ P₀.map η) : η.ker ≤ P₀ := by
  have hker : ∀ z, η z = 1 → z ∈ center E := fun z hz => hC hz
  have comm_eq : ∀ {a a' b b' : E}, η a = η a' → η b = η b' → ⁅a, b⁆ = ⁅a', b'⁆ :=
    fun ha hb => LinearCover.HeisenbergRoots.commutatorElement_eq_of_map_eq η hker ha hb
  obtain ⟨P, hP, hzP⟩ := LinearCover.exists_sylow_map_eq_twoPart_le η hη hC S
  have hlift : ∀ g ∈ (P : Subgroup E), ∃ p ∈ P₀, η p = η g := fun g hg => by
    have h1 : η g ∈ (P : Subgroup E).map η := mem_map_of_mem η hg
    rw [hP] at h1
    obtain ⟨p, hp, hpg⟩ := mem_map.mp (hS h1)
    exact ⟨p, hp, hpg⟩
  have hPP : ⁅(P : Subgroup E), (P : Subgroup E)⁆ ≤ P₀ := by
    rw [commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨p₁, hp₁, h₁⟩ := hlift g₁ hg₁
    obtain ⟨p₂, hp₂, h₂⟩ := hlift g₂ hg₂
    rw [comm_eq h₁.symm h₂.symm, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hp₁ hp₂) (inv_mem hp₁)) (inv_mem hp₂)
  intro z hz
  obtain ⟨k, hk⟩ := h2 ⟨z, hz⟩
  have hk' : z ^ 2 ^ k = 1 := congrArg Subtype.val hk
  exact hPP (hzP z hz ⟨k, hk'⟩)

theorem ker_le_of_lifts {E X : Type*} [Group E] [Group X] [Finite E] [Group.IsPerfect E]
    {θ : E →* X} (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)
    (h2 : IsPGroup 2 θ.ker) (C₀ : Subgroup E) (V UR : Subgroup X) (S : Sylow 2 X)
    (hS : ∀ g ∈ (S : Subgroup X), ∃ a ∈ UR, ∃ b ∈ V, g = a * b) (hVUR : UR ⊓ V = ⊥)
    (V' Ũ : Subgroup E) (hŨN : Ũ ≤ Subgroup.normalizer (V' : Set E)) (hV' : ∀ v ∈ V', θ v ∈ V)
    (hŨ : ∀ u ∈ Ũ, θ u ∈ UR) (hV'surj : ∀ b ∈ V, ∃ v ∈ V', θ v = b)
    (hŨsurj : ∀ a ∈ UR, ∃ u ∈ Ũ, θ u = a) (hV'ker : ∀ v ∈ V', θ v = 1 → v ∈ C₀)
    (hŨker : ∀ u ∈ Ũ, θ u = 1 → u ∈ C₀) : θ.ker ≤ C₀ := by
  have hP₀ : ((Ũ ⊔ V' : Subgroup E) : Set E) = (Ũ : Set E) * (V' : Set E) :=
    Subgroup.coe_mul_of_left_le_normalizer_right Ũ V' hŨN
  have hSle : (S : Subgroup X) ≤ (Ũ ⊔ V').map θ := by
    intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := hS g hg
    obtain ⟨u, hu, rfl⟩ := hŨsurj a ha
    obtain ⟨v, hv, rfl⟩ := hV'surj b hb
    exact ⟨u * v, Subgroup.mul_mem _ (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hv),
      map_mul θ u v⟩
  intro z hz
  have hzP := ker_le_of_sylow_le_map θ hθ hC h2 S _ hSle hz
  rw [← SetLike.mem_coe, hP₀, Set.mem_mul] at hzP
  obtain ⟨u, hu, v, hv, rfl⟩ := hzP
  have huv : θ u * θ v = 1 := by rw [← map_mul]; exact hz
  have hθu : θ u = (θ v)⁻¹ := eq_inv_of_mul_eq_one_left huv
  have hbot : θ u ∈ UR ⊓ V :=
    Subgroup.mem_inf.mpr ⟨hŨ u hu, by rw [hθu]; exact inv_mem (hV' v hv)⟩
  rw [hVUR, Subgroup.mem_bot] at hbot
  have hθv : θ v = 1 := by rw [hbot, eq_comm, inv_eq_one] at hθu; exact hθu
  exact mul_mem (hŨker u hu hbot) (hV'ker v hv hθv)

section LeviLift

variable {E X : Type*} [Group E] [Group X] (θ : E →* X) (R : Subgroup X)

@[expose] def leviLift : Subgroup E :=
  ⁅R.comap θ, R.comap θ⁆

theorem leviLift_le_comap : leviLift θ R ≤ R.comap θ :=
  Subgroup.commutator_le_self _

theorem map_leviLift (hθ : Function.Surjective θ) [Group.IsPerfect R] :
    (leviLift θ R).map θ = R := by
  rw [leviLift, Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hθ,
    Subgroup.commutator_eq_self]

theorem comap_le_leviLift_sup_ker (hθ : Function.Surjective θ) [Group.IsPerfect R] :
    R.comap θ ≤ leviLift θ R ⊔ θ.ker := by
  intro x hx
  have hxR : θ x ∈ (leviLift θ R).map θ := by rw [map_leviLift θ R hθ]; exact hx
  obtain ⟨y, hy, hyx⟩ := hxR
  have hk : y⁻¹ * x ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
  have := Subgroup.mul_mem_sup hy hk
  rwa [mul_inv_cancel_left] at this

theorem isPerfect_leviLift (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)
    [Group.IsPerfect R] : Group.IsPerfect (leviLift θ R) := by
  have h := comap_le_leviLift_sup_ker θ R hθ
  exact Subgroup.isPerfect_iff.mpr (le_antisymm (Subgroup.commutator_le_self _)
    ((Subgroup.commutator_mono h h).trans (commutator_sup_le hC)))

@[expose] def leviLiftHom : leviLift θ R →* R :=
  (θ.comp (leviLift θ R).subtype).codRestrict R fun f => leviLift_le_comap θ R f.2

theorem coe_leviLiftHom (f : leviLift θ R) : (leviLiftHom θ R f : X) = θ f :=
  rfl

theorem leviLiftHom_surjective (hθ : Function.Surjective θ) [Group.IsPerfect R] :
    Function.Surjective (leviLiftHom θ R) := by
  rintro ⟨r, hr⟩
  rw [← map_leviLift θ R hθ] at hr
  obtain ⟨f, hf, hfr⟩ := hr
  exact ⟨⟨f, hf⟩, Subtype.ext hfr⟩

theorem leviLiftHom_eq_one_iff (f : leviLift θ R) : leviLiftHom θ R f = 1 ↔ θ f = 1 :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem leviLiftHom_ker_le_center (hC : θ.ker ≤ Subgroup.center E) :
    (leviLiftHom θ R).ker ≤ Subgroup.center (leviLift θ R) := fun f hf =>
  Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hC ((leviLiftHom_eq_one_iff θ R f).mp hf)) g)

theorem isPGroup_leviLiftHom_ker (h2 : IsPGroup 2 θ.ker) : IsPGroup 2 (leviLiftHom θ R).ker := by
  intro k
  obtain ⟨n, hn⟩ := h2 ⟨((k : leviLift θ R) : E), (leviLiftHom_eq_one_iff θ R k).mp k.2⟩
  refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg Subtype.val hn
  simpa using this

end LeviLift

section Radical

variable {E X Γ A : Type*} [Group E] [Group X] [Group Γ] [AddGroup A] {θ : E →* X}
  (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E) (ρ : Γ →* X)
  {τ : Multiplicative A →* X} (hτ : Function.Injective τ) {f : Γ → A → A}
  (hf : ∀ g a, ρ g * τ (Multiplicative.ofAdd a) * (ρ g)⁻¹ = τ (Multiplicative.ofAdd (f g a)))

@[expose] def preRad (θ : E →* X) (τ : Multiplicative A →* X) : Subgroup E :=
  τ.range.comap θ

@[expose] noncomputable def piRad (θ : E →* X) (hτ : Function.Injective τ) :
    preRad θ τ →* Multiplicative A :=
  (MonoidHom.ofInjective hτ).symm.toMonoidHom.comp
    ((θ.comp (preRad θ τ).subtype).codRestrict _ fun x => x.2)

theorem tau_piRad (x : preRad θ τ) : τ (piRad θ hτ x) = θ x := by
  have h := (MonoidHom.ofInjective hτ).apply_symm_apply ⟨θ x, x.2⟩
  exact congrArg Subtype.val h

theorem piRad_eq_one_iff (x : preRad θ τ) : piRad θ hτ x = 1 ↔ θ x = 1 := by
  rw [← tau_piRad hτ x]
  exact ⟨fun h => by rw [h, map_one], fun h => hτ (by rw [h, map_one])⟩

include hθ in
theorem piRad_surjective : Function.Surjective (piRad θ hτ) := by
  intro a
  obtain ⟨y, hy⟩ := hθ (τ a)
  exact ⟨⟨y, ⟨a, hy.symm⟩⟩, hτ (by rw [tau_piRad]; exact hy)⟩

include hC in
theorem piRad_ker_le_center : (piRad θ hτ).ker ≤ Subgroup.center (preRad θ τ) := fun c hc =>
  Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hC ((piRad_eq_one_iff hτ c).mp hc)) g)

include hf in
theorem liftConj_mem_preRad (g : Γ) {y : E} (hy : y ∈ preRad θ τ) :
    liftConj hθ hC (ρ g) y ∈ preRad θ τ := by
  obtain ⟨a, ha⟩ := hy
  refine ⟨Multiplicative.ofAdd (f g a.toAdd), ?_⟩
  rw [← hf, map_liftConj_apply hθ hC (ρ g) y, ← ha, ofAdd_toAdd]

@[expose] noncomputable def actRad : Γ →* MulAut (preRad θ τ) :=
  restrictAct ((liftConj hθ hC).comp ρ) (preRad θ τ) fun g _ hy =>
    liftConj_mem_preRad hθ hC ρ hf g hy

theorem coe_actRad_of_map_eq {g : Γ} {u : E} (hu : θ u = ρ g) (x : preRad θ τ) :
    ((actRad hθ hC ρ hf g x : preRad θ τ) : E) = u * x * u⁻¹ := by
  change liftConj hθ hC (ρ g) x = u * x * u⁻¹
  rw [← hu, liftConj_apply, MulAut.conj_apply]

theorem piRad_actRad (g : Γ) (x : preRad θ τ) :
    (piRad θ hτ (actRad hθ hC ρ hf g x)).toAdd = f g (piRad θ hτ x).toAdd := by
  have h : τ (piRad θ hτ (actRad hθ hC ρ hf g x)) =
      τ (Multiplicative.ofAdd (f g (piRad θ hτ x).toAdd)) := by
    rw [tau_piRad, ← hf, ofAdd_toAdd, tau_piRad]
    exact map_liftConj_apply hθ hC (ρ g) x
  exact congrArg Multiplicative.toAdd (hτ h)

theorem actRad_apply_of_mem_ker (g : Γ) {c : preRad θ τ} (hc : c ∈ (piRad θ hτ).ker) :
    actRad hθ hC ρ hf g c = c :=
  Subtype.ext (liftConj_apply_of_mem_ker hθ hC (ρ g) ((piRad_eq_one_iff hτ c).mp hc))

theorem mem_normalizer_of_actRad_mem {V' : Subgroup E} (hV' : V' ≤ preRad θ τ)
    (hinv : ∀ (g : Γ) (x : preRad θ τ), (x : E) ∈ V' →
      ((actRad hθ hC ρ hf g x : preRad θ τ) : E) ∈ V') {g : Γ} {u : E} (hu : θ u = ρ g) :
    u ∈ Subgroup.normalizer (V' : Set E) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have := hinv g ⟨y, hV' hy⟩ hy
    rwa [coe_actRad_of_map_eq hθ hC ρ hf hu] at this
  · intro hy
    have hu' : θ u⁻¹ = ρ g⁻¹ := by rw [map_inv, map_inv, hu]
    have := hinv g⁻¹ ⟨u * y * u⁻¹, hV' hy⟩ hy
    rwa [coe_actRad_of_map_eq hθ hC ρ hf hu', show u⁻¹ * (u * y * u⁻¹) * u⁻¹⁻¹ = y by group]
      at this

end Radical

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
