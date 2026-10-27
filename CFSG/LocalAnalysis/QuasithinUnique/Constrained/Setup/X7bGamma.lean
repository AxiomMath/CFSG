module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bDiagram

public section

namespace CFSG.QuasithinUnique.Setup.X7b

open scoped MonoidAlgebra
open CFSG.Semidihedral.Principal Representation

section Perfect

variable {k : Type} [Field k] {H Γ : Type} [Group H] [Group Γ]

theorem trivial_of_sub_quot (hH : Group.IsPerfect H) (ι : H →* Γ) {V : Type} [AddCommGroup V]
    [Module k V] (ρ : Representation k Γ V) (W : Subrepresentation ρ)
    (hW : ∀ h, W.toRepresentation (ι h) = 1) (hQ : ∀ h, W.quotient (ι h) = 1) :
    ∀ h, ρ (ι h) = 1 := by
  have hmem : ∀ h v, ρ (ι h) v - v ∈ W.toSubmodule := fun h v => by
    have h1 : W.quotient (ι h) (W.toSubmodule.mkQ v) = W.toSubmodule.mkQ v := by
      rw [hQ h]
      rfl
    have h2 : W.toSubmodule.mkQ (ρ (ι h) v) = W.toSubmodule.mkQ v := h1
    exact (Submodule.Quotient.eq W.toSubmodule).mp h2
  have hfix : ∀ h, ∀ w ∈ W.toSubmodule, ρ (ι h) w = w := fun h w hw => by
    have := congrArg (fun T : W.toSubmodule →ₗ[k] W.toSubmodule => (T ⟨w, hw⟩ : V)) (hW h)
    exact this
  have hprod : ∀ g h : H, (ρ (ι g) - 1) * (ρ (ι h) - 1) = 0 := fun g h => by
    refine LinearMap.ext fun v => ?_
    have h1 : ρ (ι g) (ρ (ι h) v - v) = ρ (ι h) v - v := hfix g _ (hmem h v)
    show (ρ (ι g) - 1) ((ρ (ι h) - 1) v) = 0
    simp only [LinearMap.sub_apply, Module.End.one_apply] at h1 ⊢
    rw [h1, sub_self]
  have hmul : ∀ g h : H, ρ (ι (g * h)) - 1 = (ρ (ι g) - 1) + (ρ (ι h) - 1) := fun g h => by
    have e : ρ (ι g) * ρ (ι h) - 1 - ((ρ (ι g) - 1) + (ρ (ι h) - 1)) =
        (ρ (ι g) - 1) * (ρ (ι h) - 1) := by
      simp only [mul_sub, sub_mul, mul_one, one_mul]
      abel
    rw [hprod g h] at e
    rw [map_mul, map_mul]
    exact sub_eq_zero.mp e
  let Φ : H →* Multiplicative (V →ₗ[k] V) :=
    { toFun := fun g => Multiplicative.ofAdd (ρ (ι g) - 1)
      map_one' := by simp
      map_mul' := fun g h => by
        show Multiplicative.ofAdd (ρ (ι (g * h)) - 1) =
          Multiplicative.ofAdd (ρ (ι g) - 1) * Multiplicative.ofAdd (ρ (ι h) - 1)
        rw [hmul g h]
        rfl }
  have hker : (⊤ : Subgroup H) ≤ Φ.ker := by
    rw [← hH.commutator_eq_top, commutator_def]
    refine Subgroup.commutator_le.mpr fun g _ h _ => ?_
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_inv, map_inv]
    simp
  intro g
  have := hker (Subgroup.mem_top g)
  rw [MonoidHom.mem_ker] at this
  have h0 : ρ (ι g) - 1 = 0 := by
    have := congrArg Multiplicative.toAdd this
    simpa [Φ] using this
  exact sub_eq_zero.mp h0

end Perfect

section Codim

variable {k Γ : Type} [Field k] [Group Γ] {V : Type} [AddCommGroup V] [Module k V]

theorem finrank_repFixedSpace_le [Module.Finite k V] (ρ : Representation k Γ V)
    (W : Subrepresentation ρ) (A : Set Γ) :
    Module.finrank k (repFixedSpace ρ A) ≤
      Module.finrank k (repFixedSpace W.toRepresentation A) +
        Module.finrank k (repFixedSpace W.quotient A) := by
  have hres : ∀ m ∈ repFixedSpace ρ A, W.toSubmodule.mkQ m ∈ repFixedSpace W.quotient A := by
    intro m hm a ha
    have h : W.quotient a (W.toSubmodule.mkQ m) = W.toSubmodule.mkQ (ρ a m) := rfl
    show W.quotient a (W.toSubmodule.mkQ m) = W.toSubmodule.mkQ m
    rw [h, hm a ha]
  let L := W.toSubmodule.mkQ.restrict hres
  have hi : ∀ n ∈ repFixedSpace W.toRepresentation A, W.toSubmodule.subtype n ∈
      repFixedSpace ρ A := by
    intro n hn a ha
    have := congrArg Subtype.val (hn a ha)
    exact this
  let i := W.toSubmodule.subtype.restrict hi
  have hinj : Function.Injective i := by
    intro a b hab
    exact Subtype.ext (Subtype.ext
      (congrArg (fun x : repFixedSpace ρ A => (x : V)) hab))
  have hrange : LinearMap.range i = LinearMap.ker L := by
    ext ⟨m, hm⟩
    simp only [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨⟨n, hn⟩, h⟩
      apply Subtype.ext
      have : (n : V) = m := congrArg (fun x : repFixedSpace ρ A => (x : V)) h
      show W.toSubmodule.mkQ m = 0
      rw [← this]
      exact (Submodule.Quotient.mk_eq_zero _).mpr n.2
    · intro h
      have h0 : W.toSubmodule.mkQ m = 0 := congrArg Subtype.val h
      have hmN : m ∈ W.toSubmodule := (Submodule.Quotient.mk_eq_zero _).mp h0
      refine ⟨⟨⟨m, hmN⟩, fun a ha => ?_⟩, rfl⟩
      apply Subtype.ext
      exact hm a ha
  have h1 := LinearMap.finrank_range_add_finrank_ker L
  have h2 : Module.finrank k (LinearMap.range i) =
      Module.finrank k (repFixedSpace W.toRepresentation A) :=
    LinearMap.finrank_range_of_inj hinj
  have h3 : Module.finrank k (LinearMap.range L) ≤
      Module.finrank k (repFixedSpace W.quotient A) := Submodule.finrank_le _
  rw [hrange] at h2
  omega

theorem codim_sub_quot [Module.Finite k V] (ρ : Representation k Γ V) (W : Subrepresentation ρ)
    (A : Set Γ) :
    (Module.finrank k W.toSubmodule - Module.finrank k (repFixedSpace W.toRepresentation A)) +
        (Module.finrank k (V ⧸ W.toSubmodule) -
          Module.finrank k (repFixedSpace W.quotient A)) ≤
      Module.finrank k V - Module.finrank k (repFixedSpace ρ A) := by
  have h1 := finrank_repFixedSpace_le ρ W A
  have h2 := Submodule.finrank_quotient_add_finrank W.toSubmodule
  have h3 : Module.finrank k (repFixedSpace W.toRepresentation A) ≤
      Module.finrank k W.toSubmodule := Submodule.finrank_le _
  have h4 : Module.finrank k (repFixedSpace W.quotient A) ≤
      Module.finrank k (V ⧸ W.toSubmodule) := Submodule.finrank_le _
  omega

end Codim

section Gamma

variable {F : Type} [Field F] {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module F V]

theorem repLinEquiv_one (ρ : Representation F G V) : repLinEquiv ρ 1 = 1 :=
  LinearEquiv.ext fun v => by simp [repLinEquiv_apply]

theorem repLinEquiv_mul (ρ : Representation F G V) (g h : G) :
    repLinEquiv ρ (g * h) = repLinEquiv ρ g * repLinEquiv ρ h :=
  LinearEquiv.ext fun v => by simp [repLinEquiv_apply]

theorem repLinEquiv_inv (ρ : Representation F G V) (g : G) :
    repLinEquiv ρ g⁻¹ = (repLinEquiv ρ g)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← repLinEquiv_mul, inv_mul_cancel, repLinEquiv_one])

@[expose] def sPow (s : V ≃ₗ[F] V) : Bool → (V ≃ₗ[F] V)
  | true => s
  | false => 1

@[expose] def gammaGroup (ρ : Representation F G V) (s : V ≃ₗ[F] V) (τ : G ≃* G)
    (hss : s * s = 1) (hs : ∀ g, s * repLinEquiv ρ g = repLinEquiv ρ (τ g) * s) :
    Subgroup (V ≃ₗ[F] V) where
  carrier := {γ | ∃ (g : G) (e : Bool), γ = repLinEquiv ρ g * sPow s e}
  one_mem' := ⟨1, false, by simp [sPow, repLinEquiv_one]⟩
  mul_mem' := by
    rintro _ _ ⟨g, e, rfl⟩ ⟨g', e', rfl⟩
    cases e <;> cases e'
    · exact ⟨g * g', false, by simp [sPow, repLinEquiv_mul]⟩
    · exact ⟨g * g', true, by simp [sPow, repLinEquiv_mul, mul_assoc]⟩
    · refine ⟨g * τ g', true, ?_⟩
      calc repLinEquiv ρ g * sPow s true * (repLinEquiv ρ g' * sPow s false)
          = repLinEquiv ρ g * (s * repLinEquiv ρ g') := by simp [sPow, mul_assoc]
        _ = repLinEquiv ρ g * (repLinEquiv ρ (τ g') * s) := by rw [hs g']
        _ = repLinEquiv ρ (g * τ g') * sPow s true := by simp [sPow, repLinEquiv_mul, mul_assoc]
    · refine ⟨g * τ g', false, ?_⟩
      calc repLinEquiv ρ g * sPow s true * (repLinEquiv ρ g' * sPow s true)
          = repLinEquiv ρ g * (s * repLinEquiv ρ g') * s := by simp [sPow, mul_assoc]
        _ = repLinEquiv ρ g * (repLinEquiv ρ (τ g') * s) * s := by rw [hs g']
        _ = repLinEquiv ρ g * repLinEquiv ρ (τ g') * (s * s) := by simp only [mul_assoc]
        _ = repLinEquiv ρ (g * τ g') * sPow s false := by
          rw [hss, mul_one, repLinEquiv_mul]
          simp [sPow]
  inv_mem' := by
    rintro _ ⟨g, e, rfl⟩
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    cases e
    · exact ⟨g⁻¹, false, by simp [sPow, repLinEquiv_inv]⟩
    · refine ⟨τ g⁻¹, true, ?_⟩
      calc (repLinEquiv ρ g * sPow s true)⁻¹ = s * repLinEquiv ρ g⁻¹ := by
            simp [sPow, hsinv, repLinEquiv_inv]
        _ = repLinEquiv ρ (τ g⁻¹) * sPow s true := by rw [hs]; rfl

end Gamma

section Reduction

variable {F : Type} [Field F] {G : Type} [Group G]

@[expose] def GSIrreducible {V : Type} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    (s : V ≃ₗ[F] V) : Prop :=
  ∀ U : Submodule F V, (∀ g, ∀ u ∈ U, ρ g u ∈ U) → (∀ u ∈ U, s u ∈ U) → U = ⊥ ∨ U = ⊤

theorem gamma_reduction (hG : Group.IsPerfect G) (τ : G ≃* G) (n : ℕ)
    (hirr : ∀ {W : Type} [AddCommGroup W] [Module F W] [Module.Finite F W]
      (ρ' : Representation F G W) (s' : W ≃ₗ[F] W), (∀ w, s' (s' w) = w) →
      (∀ g w, s' (ρ' g w) = ρ' (τ g) (s' w)) → GSIrreducible ρ' s' → Nontrivial W →
      (∃ g, ρ' g ≠ 1) →
      n ≤ Module.finrank F W - Module.finrank F (LinearMap.ker (s'.toLinearMap - 1)))
    {V : Type} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (s : V ≃ₗ[F] V) (hss : ∀ v, s (s v) = v)
    (hs : ∀ g v, s (ρ g v) = ρ (τ g) (s v)) (hnt : ∃ g, ρ g ≠ 1) :
    n ≤ Module.finrank F V - Module.finrank F (LinearMap.ker (s.toLinearMap - 1)) := by
  have hss' : s * s = 1 := LinearEquiv.ext hss
  have hs' : ∀ g, s * repLinEquiv ρ g = repLinEquiv ρ (τ g) * s := fun g =>
    LinearEquiv.ext fun v => hs g v
  let Γ := gammaGroup ρ s τ hss' hs'
  let ι : G →* ↥Γ :=
    { toFun := fun g => ⟨repLinEquiv ρ g, g, false, by simp [sPow]⟩
      map_one' := Subtype.ext (repLinEquiv_one ρ)
      map_mul' := fun g h => Subtype.ext (repLinEquiv_mul ρ g h) }
  let t : ↥Γ := ⟨s, 1, true, by simp [sPow, repLinEquiv_one]⟩
  have htt : t * t = 1 := Subtype.ext hss'
  have htι : ∀ g, t * ι g = ι (τ g) * t := fun g => Subtype.ext (hs' g)
  have hdec : ∀ γ : ↥Γ, (∃ g, γ = ι g) ∨ (∃ g, γ = ι g * t) := by
    rintro ⟨γ, g, e, hγ⟩
    cases e
    · left
      refine ⟨g, Subtype.ext ?_⟩
      show γ = repLinEquiv ρ g
      rw [hγ]
      simp [sPow]
    · right
      refine ⟨g, Subtype.ext ?_⟩
      show γ = repLinEquiv ρ g * s
      rw [hγ]
      rfl
  let ρΓ : Representation F ↥Γ V :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := F) (M := V)).comp Γ.subtype
  have hρΓι : ∀ g, ρΓ (ι g) = ρ g := fun g => LinearMap.ext fun v => rfl
  have hρΓt : ρΓ t = s.toLinearMap := rfl
  have hfixker : ∀ {W : Type} [AddCommGroup W] [Module F W] (ρ' : Representation F ↥Γ W),
      repFixedSpace ρ' {t} = LinearMap.ker ((repLinEquiv ρ' t).toLinearMap - 1) := by
    intro W _ _ ρ'
    ext v
    simp only [mem_repFixedSpace, Set.mem_singleton_iff, forall_eq, LinearMap.mem_ker,
      LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, repLinEquiv_apply, sub_eq_zero]
  have key := rep_induction (k := F) (G := ↥Γ)
    (fun {W} _ _ _ ρ' => (∃ g, ρ' (ι g) ≠ 1) →
      n ≤ Module.finrank F W - Module.finrank F (repFixedSpace ρ' {t}))
    (fun {W} _ _ _ ρ' hsub hex => by
      obtain ⟨g, hg⟩ := hex
      exact absurd (LinearMap.ext fun v => Subsingleton.elim _ _) hg)
    (fun {W} _ _ _ ρ' hirrΓ hex => by
      let s' : W ≃ₗ[F] W := repLinEquiv ρ' t
      have hs's' : ∀ w, s' (s' w) = w := fun w => by
        show ρ' t (ρ' t w) = w
        rw [← Module.End.mul_apply, ← map_mul, htt, map_one]
        rfl
      have hs'G : ∀ g w, s' ((ρ'.comp ι) g w) = (ρ'.comp ι) (τ g) (s' w) := fun g w => by
        show ρ' t (ρ' (ι g) w) = ρ' (ι (τ g)) (ρ' t w)
        rw [← Module.End.mul_apply, ← map_mul, htι, map_mul]
        rfl
      have hGS : GSIrreducible (ρ'.comp ι) s' := by
        intro U hUG hUs
        let Ux : Subrepresentation ρ' := ⟨U, fun γ w hw => by
          rcases hdec γ with ⟨g, rfl⟩ | ⟨g, rfl⟩
          · exact hUG g w hw
          · show ρ' (ι g * t) w ∈ U
            rw [map_mul]
            exact hUG g _ (hUs w hw)⟩
        rcases hirrΓ.eq_bot_or_eq_top Ux with h | h
        · left
          exact congrArg Subrepresentation.toSubmodule h
        · right
          exact congrArg Subrepresentation.toSubmodule h
      have hNT : Nontrivial W := by
        by_contra hW
        have hsub : Subsingleton W := not_nontrivial_iff_subsingleton.mp hW
        have hbt : (⊥ : Submodule F W) = ⊤ := (Submodule.eq_bot_of_subsingleton (p := (⊤ : Submodule F W))).symm
        exact bot_ne_top (Subrepresentation.toSubmodule_injective (ρ := ρ') hbt)
      have := hirr (ρ'.comp ι) s' hs's' hs'G hGS hNT hex
      rwa [hfixker ρ'])
    (fun {W} _ _ _ ρ' U hU1 hU2 hex => by
      by_cases hUt : ∃ g, U.toRepresentation (ι g) ≠ 1
      · have h1 := hU1 hUt
        have hcod := codim_sub_quot ρ' U {t}
        omega
      · by_cases hQt : ∃ g, U.quotient (ι g) ≠ 1
        · have h2 := hU2 hQt
          have hcod := codim_sub_quot ρ' U {t}
          omega
        · exfalso
          push Not at hUt hQt
          have := trivial_of_sub_quot hG ι ρ' U (fun g => hUt g) (fun g => hQt g)
          obtain ⟨g, hg⟩ := hex
          exact hg (this g))
    (Module.finrank F V) ρΓ rfl
  have hex : ∃ g, ρΓ (ι g) ≠ 1 := by
    obtain ⟨g, hg⟩ := hnt
    exact ⟨g, by rw [hρΓι]; exact hg⟩
  have := key hex
  have hker : repFixedSpace ρΓ {t} = LinearMap.ker (s.toLinearMap - 1) := by
    rw [hfixker]
    rfl
  rwa [hker] at this

end Reduction

end CFSG.QuasithinUnique.Setup.X7b
