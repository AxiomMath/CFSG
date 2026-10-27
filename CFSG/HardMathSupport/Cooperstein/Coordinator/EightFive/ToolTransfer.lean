module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Perfect
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Bookkeeping

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin CFSG.RankThree.PartTwo Equiv Equiv.Perm

theorem natShape_of_natShape_subgroup {V : Type*} [CommGroup V] {W : Subgroup V} {G : Type*}
    [Group G] (hG : commutator G = ⊤) {k : ℕ} (ρ : G →* MulAut V) (ρW : G →* MulAut ↥W)
    (hres : ∀ g (w : ↥W), ((ρW g w : ↥W) : V) = ρ g w) (hVW : ∀ g v, ρ g v * v⁻¹ ∈ W)
    {α : G →* Perm (Fin k)} (h : NatShape ρW α) : NatShape ρ α := by
  obtain ⟨M₀, M₁, hM, h₀, h₁, π, hπ, hker, heq⟩ := h
  set e := Subgroup.equivMapOfInjective M₁ W.subtype W.subtype_injective with he_def
  have he : ∀ u : ↥(M₁.map W.subtype), (((e.symm u : ↥M₁) : ↥W) : V) = u := fun u => by
    have := Subgroup.coe_equivMapOfInjective_apply M₁ W.subtype W.subtype_injective (e.symm u)
    rw [← he_def, MulEquiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨M₀.map W.subtype, M₁.map W.subtype, Subgroup.map_mono hM, ?_, ?_,
    π.comp e.symm.toMonoidHom, hπ.comp e.symm.surjective, ?_, ?_⟩
  · rintro g _ ⟨w, hw, rfl⟩
    rw [Subgroup.coe_subtype, ← hres, h₀ g w hw]
  ·
    intro g v
    have key := sub_mem_of_perfect hG (autToEnd.comp ρ) Set.univ {x | Additive.toMul x ∈ W}
      (Subgroup.toAddSubgroup (M₁.map W.subtype))
      (fun g w _ => by
        change ρ g (Additive.toMul w) / Additive.toMul w ∈ W
        rw [div_eq_mul_inv]
        exact hVW g _)
      (fun g t ht => by
        change ρ g (Additive.toMul t) / Additive.toMul t ∈ M₁.map W.subtype
        rw [div_eq_mul_inv]
        refine ⟨ρW g ⟨Additive.toMul t, ht⟩ * (⟨Additive.toMul t, ht⟩ : ↥W)⁻¹,
          h₁ g ⟨Additive.toMul t, ht⟩, ?_⟩
        rw [map_mul, map_inv]
        change ((ρW g ⟨Additive.toMul t, ht⟩ : ↥W) : V) * (Additive.toMul t)⁻¹ = _
        rw [hres])
      g (Additive.ofMul v) (Set.mem_univ _)
    change ρ g v / v ∈ M₁.map W.subtype at key
    rwa [div_eq_mul_inv] at key
  · ext u
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · intro hu
      exact ⟨_, hu, he u⟩
    · rintro ⟨w, hw, hwu⟩
      have : ((e.symm u : ↥M₁) : ↥W) = w :=
        W.subtype_injective ((he u).trans hwu.symm)
      change ((e.symm u : ↥M₁) : ↥W) ∈ M₀
      rw [this]
      exact hw
  · intro g u v huv
    have h1 : ((e.symm v : ↥M₁) : ↥W) = ρW g ((e.symm u : ↥M₁) : ↥W) := by
      apply Subtype.ext
      rw [he, hres, he]
      exact huv
    exact heq g (e.symm u) (e.symm v) h1

section Restrict

variable {X : Type} [CommGroup X] {K : Subgroup (MulAut X)} {m : ℕ} {κ : ↥K →* Perm (Fin m)}
  {π : ↥(commV K) →* Multiplicative (altHeart m)}

theorem range_subtype_comp_le (r : alternatingGroup (Fin m) →* ↥K) :
    (K.subtype.comp r).range ≤ K := by
  rintro _ ⟨σ, rfl⟩
  exact (r σ).2

theorem surjective_comp_inclusion_commV (hm : 4 ≤ m) (hπ : Function.Surjective π)
    (heq : ∀ (h : ↥K) (u v : ↥(commV K)), (v : X) = (h : MulAut X) (u : X) →
      Multiplicative.toAdd (π v) = altAct (κ h) (Multiplicative.toAdd (π u)))
    (r : alternatingGroup (Fin m) →* ↥K) (hr : ∀ σ, κ (r σ) = σ) :
    Function.Surjective (π.comp (Subgroup.inclusion (commV_mono (range_subtype_comp_le r)))) := by
  set E := (K.subtype.comp r).range with hE
  set hle := commV_mono (range_subtype_comp_le r) with hhle
  have hrE : ∀ σ, ((r σ : ↥K) : MulAut X) ∈ E := fun σ => ⟨σ, rfl⟩
  have hinvE : ∀ σ (u : X), u ∈ commV E → (r σ : MulAut X) u ∈ commV E := fun σ u hu => by
    have h2 := (commV E).mul_mem (mul_inv_mem_commV (hrE σ) u) hu
    rwa [inv_mul_cancel_right] at h2
  have hinvK : ∀ (g : ↥K) (u : X), u ∈ commV K → (g : MulAut X) u ∈ commV K := fun g u hu => by
    have h2 := (commV K).mul_mem (mul_inv_mem_commV g.2 u) hu
    rwa [inv_mul_cancel_right] at h2
  let Y : AddSubgroup (altHeart m) :=
    { carrier := {z | ∃ u : ↥(commV E), Multiplicative.toAdd (π (Subgroup.inclusion hle u)) = z}
      add_mem' := by
        rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
        exact ⟨u * v, by rw [map_mul, map_mul]; rfl⟩
      zero_mem' := ⟨1, by rw [map_one, map_one]; rfl⟩
      neg_mem' := by
        rintro _ ⟨u, rfl⟩
        exact ⟨u⁻¹, by rw [map_inv, map_inv]; rfl⟩ }
  have hY : ∀ σ ∈ alternatingGroup (Fin m), ∀ z ∈ Y, altAct σ z ∈ Y := by
    rintro σ hσ _ ⟨u, rfl⟩
    refine ⟨⟨(r ⟨σ, hσ⟩ : MulAut X) u, hinvE _ u u.2⟩, ?_⟩
    rw [heq (r ⟨σ, hσ⟩) (Subgroup.inclusion hle u) _ rfl, hr]
  have hne : ∃ z ∈ Y, z ≠ 0 := by
    obtain ⟨σ, hσ, z, hz⟩ := exists_altAct_ne hm
    obtain ⟨u, hu⟩ := hπ (Multiplicative.ofAdd z)
    set g := r ⟨σ, hσ⟩ with hg
    have hgu : (g : MulAut X) u ∈ commV K := hinvK g u u.2
    have hmem : (g : MulAut X) u * (u : X)⁻¹ ∈ commV E := mul_inv_mem_commV (hrE _) u
    refine ⟨_, ⟨⟨_, hmem⟩, rfl⟩, ?_⟩
    have hval : Subgroup.inclusion hle ⟨_, hmem⟩ = ⟨(g : MulAut X) u, hgu⟩ * u⁻¹ :=
      Subtype.ext rfl
    rw [hval, map_mul, map_inv, toAdd_mul, toAdd_inv, heq g u ⟨_, hgu⟩ rfl, hu, toAdd_ofAdd, hg,
      hr]
    intro h
    apply hz
    have h2 := congrArg (· + z) h
    simp only [neg_add_cancel_right, zero_add] at h2
    exact h2
  have htop := altHeart_eq_top_of_moved hm Y hY hne
  intro w
  obtain ⟨u, hu⟩ := (show Multiplicative.toAdd w ∈ Y from htop ▸ AddSubgroup.mem_top _)
  exact ⟨u, Multiplicative.toAdd.injective hu⟩

theorem ker_comp_inclusion_commV
    (hker : π.ker = (commV K ⊓ fixV (altPre κ)).subgroupOf (commV K))
    {E : Subgroup (MulAut X)} (hle : commV E ≤ commV K) :
    (π.comp (Subgroup.inclusion hle)).ker = (commV E ⊓ fixV (altPre κ)).subgroupOf (commV E) := by
  ext u
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker,
    Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact ⟨fun h => ⟨u.2, h.2⟩, fun h => ⟨hle u.2, h.2⟩⟩

end Restrict

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
