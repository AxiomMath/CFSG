module

public import CFSG.ClassicalInvolution.Q3.Q3NMAlpha

public section

namespace CFSG.ClassicalInvolution.Q3.Q3NM

open CFSG.Open CFSG.ClassicalInvolution.Balance CFSG.Assembly.Dichotomy
  CFSG.ClassicalInvolution.Asc77 CFSG.ComponentClassification

@[expose] def AutOddFreeOn (X : Type) [Group X] (P : MulAut X → Prop) : Prop :=
  ∀ 𝒳 : Subgroup (MulAut X), innSubgroup X ≤ 𝒳 → ∀ f : 𝒳, P (f : MulAut X) → orderOf f = 2 →
    involutionOddCore f = ⊥

theorem AutOddFree.on {X : Type} [Group X] (h : AutOddFree X) (P : MulAut X → Prop) :
    AutOddFreeOn X P :=
  fun 𝒳 hinn f _ hf => h 𝒳 hinn f hf

theorem AutOddFreeInner.toOn {X : Type} [Group X] (h : AutOddFreeInner X) :
    AutOddFreeOn X (fun τ => τ ∈ innSubgroup X) :=
  fun 𝒳 hinn f hf hf2 => h 𝒳 hinn f hf hf2

theorem AutOddFreeOn.mono {X : Type} [Group X] {P Q : MulAut X → Prop}
    (h : AutOddFreeOn X Q) (hPQ : ∀ f, P f → Q f) : AutOddFreeOn X P :=
  fun 𝒳 hinn f hf hf2 => h 𝒳 hinn f (hPQ _ hf) hf2

theorem AutOddFreeOn.or {X : Type} [Group X] {P Q : MulAut X → Prop} (hP : AutOddFreeOn X P)
    (hQ : AutOddFreeOn X Q) : AutOddFreeOn X (fun f => P f ∨ Q f) :=
  fun 𝒳 hinn f hf hf2 => hf.elim (fun h => hP 𝒳 hinn f h hf2) (fun h => hQ 𝒳 hinn f h hf2)

section Fixed

variable {X : Type} [Group X] [Finite X]

theorem autOddFreeOn_of_fixed (P : MulAut X → Prop) (hZ : Subgroup.center X = ⊥)
    (hodd : ∀ α : MulAut X, Odd (orderOf α) → α ∈ innSubgroup X)
    (hfix : ∀ σ : MulAut X, P σ → σ * σ = 1 → oddCoreIn (fixedSubgroup σ) = ⊥) :
    AutOddFreeOn X P := by
  intro 𝒳 hinn f hP hf
  have hf2 := mul_self_eq_one_of_orderOf_eq_two' hf
  exact involutionOddCore_eq_bot_of_fixed hZ hodd 𝒳 hinn f hf2
    (hfix _ hP (congrArg Subtype.val hf2))

end Fixed

section Transport

variable {A B : Type} [Group A] [Group B]

theorem oddCoreIn_map_eq_bot (Φ : A →* B) (hΦ : Function.Injective Φ) {U : Subgroup A}
    (h : oddCoreIn U = ⊥) : oddCoreIn (U.map Φ) = ⊥ := by
  have h1 : componentClassificationOddCore ↥U = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ U.subtype_injective).mp h
  have := oddCoreIn_range_eq_bot_of_injective (Φ.comp U.subtype) (hΦ.comp U.subtype_injective) h1
  rwa [MonoidHom.range_comp, Subgroup.range_subtype] at this

theorem fixedSubgroup_congr_aut (e : A ≃* B) (ρ : MulAut A) :
    fixedSubgroup (MulAut.congr e ρ) = (fixedSubgroup ρ).map e.toMonoidHom := by
  ext b
  obtain ⟨a, rfl⟩ := e.surjective b
  constructor
  · intro hb
    refine ⟨a, ?_, rfl⟩
    have hb' : e (ρ (e.symm (e a))) = e a := hb
    rw [MulEquiv.symm_apply_apply] at hb'
    exact e.injective hb'
  · rintro ⟨a', ha', hab⟩
    have : a' = a := e.injective hab
    subst this
    show e (ρ (e.symm (e a'))) = e a'
    rw [MulEquiv.symm_apply_apply, mem_fixedSubgroup_iff.mp ha']

theorem oddCoreIn_fixed_congr_eq_bot' (e : A ≃* B) (ρ : MulAut A)
    (h : oddCoreIn (fixedSubgroup ρ) = ⊥) :
    oddCoreIn (fixedSubgroup (MulAut.congr e ρ)) = ⊥ := by
  rw [fixedSubgroup_congr_aut]
  exact oddCoreIn_map_eq_bot _ e.injective h

end Transport


section CentralIso

variable {K X : Type} [Group K] [Group X]

@[expose] def centralQuotientMap (ψ : K →* X) (hψ : Function.Surjective ψ) :
    K ⧸ Subgroup.center K →* X ⧸ Subgroup.center X :=
  QuotientGroup.map _ _ ψ (fun z hz => Subgroup.map_center_le_center hψ ⟨z, hz, rfl⟩)

theorem centralQuotientMap_mk (ψ : K →* X) (hψ : Function.Surjective ψ) (k : K) :
    centralQuotientMap ψ hψ (QuotientGroup.mk k) = QuotientGroup.mk (ψ k) :=
  rfl

theorem centralQuotientMap_bijective [Group.IsPerfect K] (ψ : K →* X)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center K) :
    Function.Bijective (centralQuotientMap ψ hψ) := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective a
    rw [centralQuotientMap_mk, QuotientGroup.eq_one_iff] at ha
    obtain ⟨z, hz, hzk⟩ := center_le_map_center_of_perfect ψ hψ hker ha
    have h1 : z⁻¹ * k ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hzk, inv_mul_cancel]
    have hk : k = z * (z⁻¹ * k) := by group
    rw [QuotientGroup.eq_one_iff, hk]
    exact mul_mem hz (hker h1)
  · intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, rfl⟩ := hψ y
    exact ⟨QuotientGroup.mk k, rfl⟩

@[expose] noncomputable def centralQuotientIso [Group.IsPerfect K] (ψ : K →* X)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center K) :
    K ⧸ Subgroup.center K ≃* X ⧸ Subgroup.center X :=
  MulEquiv.ofBijective (centralQuotientMap ψ hψ) (centralQuotientMap_bijective ψ hψ hker)

theorem oddCoreIn_fixed_eq_bot_of_lift [Group.IsPerfect K] (ψ : K →* X)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center K) {σ : MulAut K}
    {τ : MulAut X} (hlift : ∀ x, τ (ψ x) = ψ (σ x))
    (h : oddCoreIn (fixedSubgroup (autToCentralQuotient K σ)) = ⊥) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient X τ)) = ⊥ := by
  have hbij := centralQuotientMap_bijective ψ hψ hker
  have hcompat : ∀ a, autToCentralQuotient X τ (centralQuotientMap ψ hψ a) =
      centralQuotientMap ψ hψ (autToCentralQuotient K σ a) := by
    intro a
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective a
    show QuotientGroup.mk (τ (ψ k)) = QuotientGroup.mk (ψ (σ k))
    rw [hlift]
  have hfix : fixedSubgroup (autToCentralQuotient X τ) =
      (fixedSubgroup (autToCentralQuotient K σ)).map (centralQuotientMap ψ hψ) := by
    ext b
    constructor
    · intro hb
      obtain ⟨a, rfl⟩ := hbij.2 b
      refine ⟨a, ?_, rfl⟩
      show autToCentralQuotient K σ a = a
      apply hbij.1
      rw [← hcompat]
      exact mem_fixedSubgroup_iff.mp hb
    · rintro ⟨a, ha, rfl⟩
      rw [mem_fixedSubgroup_iff, hcompat, mem_fixedSubgroup_iff.mp ha]
  rw [hfix]
  exact oddCoreIn_map_eq_bot _ hbij.1 h

end CentralIso

section CongrTransport

variable {K K' : Type} [Group K] [Group K']

theorem oddCoreIn_fixed_congr_eq_bot (e : K ≃* K') (σ : MulAut K)
    (h : oddCoreIn (fixedSubgroup (autToCentralQuotient K σ)) = ⊥) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient K' (MulAut.congr e σ))) = ⊥ := by
  set Ψ : K ⧸ Subgroup.center K ≃* K' ⧸ Subgroup.center K' :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e) with hΨdef
  have hΨ := Ψ.injective
  have hΨmk : ∀ k : K, Ψ (QuotientGroup.mk k) = QuotientGroup.mk (e k) := fun k => rfl
  have hcompat : ∀ a : K ⧸ Subgroup.center K,
      autToCentralQuotient K' (MulAut.congr e σ) (Ψ a) = Ψ (autToCentralQuotient K σ a) := by
    intro a
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective a
    show QuotientGroup.mk (e (σ (e.symm (e k)))) = QuotientGroup.mk (e (σ k))
    rw [MulEquiv.symm_apply_apply]
  have hfix : fixedSubgroup (autToCentralQuotient K' (MulAut.congr e σ)) =
      (fixedSubgroup (autToCentralQuotient K σ)).map Ψ.toMonoidHom := by
    ext b
    obtain ⟨a, rfl⟩ := Ψ.surjective b
    constructor
    · intro hb
      refine ⟨a, ?_, rfl⟩
      show autToCentralQuotient K σ a = a
      apply hΨ
      rw [← hcompat]
      exact hb
    · rintro ⟨a', ha', hab⟩
      have : a' = a := hΨ hab
      subst this
      show autToCentralQuotient K' (MulAut.congr e σ) (Ψ a') = Ψ a'
      rw [hcompat, mem_fixedSubgroup_iff.mp ha']
  rw [hfix]
  exact oddCoreIn_map_eq_bot _ hΨ h

end CongrTransport

section Lifts

variable {K X : Type} [Group K] [Group X]

theorem isPerfect_of_surjective [Group.IsPerfect K] (ψ : K →* X) (hψ : Function.Surjective ψ) :
    Group.IsPerfect X := by
  refine ⟨?_⟩
  have hK : commutator K = ⊤ := Group.IsPerfect.commutator_eq_top
  have h1 : (commutator K).map ψ = commutator X := by
    rw [commutator, commutator, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr hψ]
  rw [← h1, hK, Subgroup.map_top, MonoidHom.range_eq_top.mpr hψ]

theorem center_quotient_eq_bot_of_perfect [Group.IsPerfect X] :
    Subgroup.center (X ⧸ Subgroup.center X) = ⊥ := by
  rw [eq_bot_iff]
  intro s hs
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
  refine CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.mem_center_of_commutator_mem_center
    fun y => ?_
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
    QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hs _).symm

variable [Finite X]

theorem autOddFreeOn_of_fixed_quotient [Group.IsPerfect X] (Q : MulAut X → Prop)
    (hodd : ∀ α : MulAut (X ⧸ Subgroup.center X), Odd (orderOf α) →
      α ∈ innSubgroup (X ⧸ Subgroup.center X))
    (hfix : ∀ τ : MulAut X, Q τ → τ ≠ 1 → τ * τ = 1 →
      oddCoreIn (fixedSubgroup (autToCentralQuotient X τ)) = ⊥) :
    AutOddFreeOn X Q := by
  intro 𝒳 hinn f hQ hf
  have hf2 := mul_self_eq_one_of_orderOf_eq_two' hf
  have hτ2 : (f : MulAut X) * (f : MulAut X) = 1 := congrArg Subtype.val hf2
  have hτ1 : (f : MulAut X) ≠ 1 := by
    intro h
    have hf1 : f = 1 := Subtype.ext h
    rw [hf1, orderOf_one] at hf
    omega
  have hfix' := hfix _ hQ hτ1 hτ2
  have hΦ := autToCentralQuotient_injective (X := X)
  set 𝒳' := 𝒳.map (autToCentralQuotient X) with h𝒳'
  have hinn' : innSubgroup (X ⧸ Subgroup.center X) ≤ 𝒳' := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    refine ⟨MulAut.conj x, hinn ⟨x, rfl⟩, ?_⟩
    ext y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rfl
  let ε : ↥𝒳 ≃* ↥𝒳' := 𝒳.equivMapOfInjective (autToCentralQuotient X) hΦ
  have hf' : orderOf (ε f) = 2 := by rw [MulEquiv.orderOf_eq]; exact hf
  have hε : ((ε f : ↥𝒳') : MulAut (X ⧸ Subgroup.center X)) =
      autToCentralQuotient X (f : MulAut X) := rfl
  have h1 := involutionOddCore_eq_bot_of_fixed center_quotient_eq_bot_of_perfect hodd 𝒳' hinn'
    (ε f) (mul_self_eq_one_of_orderOf_eq_two' hf') (by rw [hε]; exact hfix')
  exact oddCoreIn_centralizer_eq_bot_of_mulEquiv ε f h1

theorem autOddFreeOn_of_lifts [Group.IsPerfect K] (ψ : K →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center K) (P : MulAut K → Prop)
    (hodd : ∀ α : MulAut (X ⧸ Subgroup.center X), Odd (orderOf α) →
      α ∈ innSubgroup (X ⧸ Subgroup.center X))
    (hfix : ∀ σ : MulAut K, P σ → σ ≠ 1 → σ * σ = 1 →
      oddCoreIn (fixedSubgroup (autToCentralQuotient K σ)) = ⊥) :
    AutOddFreeOn X (fun τ => ∃ σ : MulAut K, P σ ∧ ∀ x, τ (ψ x) = ψ (σ x)) := by
  have : Group.IsPerfect X := isPerfect_of_surjective ψ hψ
  refine autOddFreeOn_of_fixed_quotient _ hodd ?_
  rintro τ ⟨σ, hPσ, hlift⟩ hτ1 hτ2
  have hσ2 : σ * σ = 1 := by
    apply autToCentralQuotient_injective (X := K)
    rw [map_mul, map_one]
    ext a
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective a
    show (QuotientGroup.mk (σ (σ k)) : K ⧸ Subgroup.center K) = QuotientGroup.mk k
    rw [QuotientGroup.eq]
    apply hker
    have hτ2' : ∀ y : X, τ (τ y) = y := fun y => by
      have := congrArg (fun g : MulAut X => g y) hτ2
      simpa using this
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hlift, ← hlift, hτ2', inv_mul_cancel]
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    apply hτ1
    refine MulEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := hψ y
    rw [hlift]
    rfl
  exact oddCoreIn_fixed_eq_bot_of_lift ψ hψ hker hlift (hfix σ hPσ hσ1 hσ2)

theorem autOddFreeOn_of_quotientIso [Group.IsPerfect X] {S : Type} [Group S]
    (ε : X ⧸ Subgroup.center X ≃* S) (P : MulAut S → Prop)
    (hodd : ∀ α : MulAut (X ⧸ Subgroup.center X), Odd (orderOf α) →
      α ∈ innSubgroup (X ⧸ Subgroup.center X))
    (hfix : ∀ ρ : MulAut S, P ρ → ρ ≠ 1 → ρ * ρ = 1 → oddCoreIn (fixedSubgroup ρ) = ⊥) :
    AutOddFreeOn X (fun τ => P (MulAut.congr ε (autToCentralQuotient X τ))) := by
  refine autOddFreeOn_of_fixed_quotient _ hodd ?_
  intro τ hP hτ1 hτ2
  have hρ1 : MulAut.congr ε (autToCentralQuotient X τ) ≠ 1 := by
    intro h
    apply hτ1
    apply autToCentralQuotient_injective (X := X)
    rw [map_one]
    exact (MulAut.congr ε).injective (h.trans (map_one _).symm)
  have hρ2 : MulAut.congr ε (autToCentralQuotient X τ) *
      MulAut.congr ε (autToCentralQuotient X τ) = 1 := by
    rw [← map_mul, ← map_mul, hτ2, map_one, map_one]
  have h := hfix _ hP hρ1 hρ2
  have hτ' : autToCentralQuotient X τ = MulAut.congr ε.symm (MulAut.congr ε
      (autToCentralQuotient X τ)) := by
    refine MulEquiv.ext fun y => ?_
    show _ = ε.symm (ε (autToCentralQuotient X τ (ε.symm (ε y))))
    simp
  rw [hτ']
  have h2 := oddCoreIn_fixed_congr_eq_bot' ε.symm _ h
  exact h2

end Lifts


section Link

variable {H : Type} [Group H]

theorem alphaOf_eq_bot_of_on (L : Subgroup H) (P : MulAut ↥L → Prop) (hL : AutOddFreeOn ↥L P)
    (A : Subgroup ↥(inducedAutOn L)) (h2 : ∀ x ∈ A, x * x = 1) (hne : ∃ x ∈ A, x ≠ 1)
    (hP : ∀ x ∈ A, x ≠ 1 → P ((x : ↥(inducedAutOn L)) : MulAut ↥L)) : alphaOf A = ⊥ := by
  refine alphaOf_eq_bot_of_oddCore hne fun a ha ha1 => ?_
  have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact h2 a ha) ha1
  exact hL (inducedAutOn L) (innSubgroup_le_inducedAutOn L) a (hP a ha ha1) ha2

theorem alphaOf_inducedImage_eq_bot_of_on (L B : Subgroup H) (P : MulAut ↥L → Prop)
    (hL : AutOddFreeOn ↥L P) (h2 : ∀ x ∈ inducedImage L B, x * x = 1)
    (hne : ∃ x ∈ inducedImage L B, x ≠ 1)
    (hP : ∀ x ∈ inducedImage L B, P ((x : ↥(inducedAutOn L)) : MulAut ↥L)) :
    alphaOf (inducedImage L B) = ⊥ :=
  alphaOf_eq_bot_of_on L P hL _ h2 hne fun x hx _ => hP x hx

end Link

end CFSG.ClassicalInvolution.Q3.Q3NM
