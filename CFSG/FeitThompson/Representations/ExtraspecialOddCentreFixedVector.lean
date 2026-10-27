module

public import CFSG.FeitThompson.Representations.ExtraspecialExtensionComplementFixedVector
import CFSG.FeitThompson.Representations.QuadraticPrimeElementsPrimePowerImage

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Module SemidirectProduct

universe u v w

variable {k : Type v} [Field k] {V : Type w} [AddCommGroup V] [Module k V]

section Aux

variable {P H : Type u} [Group P] [Group H] {α : H →* MulAut P}

theorem inl_mem_center_of_forall_apply_eq {z : P} (hz : z ∈ Subgroup.center P)
    (hα : ∀ a : H, α a z = z) :
    (SemidirectProduct.inl z : P ⋊[α] H) ∈ Subgroup.center (P ⋊[α] H) := by
  rw [Subgroup.mem_center_iff]
  intro g
  refine SemidirectProduct.ext ?_ ?_
  · rw [mul_left, mul_left, left_inl, right_inl, map_one, MulAut.one_apply, hα g.right,
      Subgroup.mem_center_iff.1 hz g.left]
  · rw [mul_right, mul_right, right_inl, one_mul, mul_one]

end Aux

theorem exists_ne_one_characterSpace_ne_bot {A : Type*} [CommGroup A] [Finite A]
    [FiniteDimensional k V] [IsAlgClosed k] (σ : Representation k A V)
    (hA : (Nat.card A : k) ≠ 0) (hnt : ∃ a : A, σ a ≠ 1) :
    ∃ χ : A →* kˣ, χ ≠ 1 ∧ Representation.characterSpace σ χ ≠ ⊥ := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have htop : Representation.characterSpace σ (1 : A →* kˣ) = ⊤ := by
    rw [← Representation.iSup_characterSpace_eq_top σ hA]
    refine le_antisymm (le_iSup _ 1) (iSup_le fun χ => ?_)
    rcases eq_or_ne χ 1 with rfl | hχ
    · exact le_rfl
    · rw [hcon χ hχ]; exact bot_le
  obtain ⟨a, ha⟩ := hnt
  refine ha (LinearMap.ext fun v => ?_)
  have hv : v ∈ Representation.characterSpace σ (1 : A →* kˣ) := by rw [htop]; exact trivial
  rw [Representation.mem_characterSpace_iff] at hv
  simpa using hv a

theorem exists_minimal_invariant_le {X : Type*} [Monoid X] (ρ : Representation k X V)
    [FiniteDimensional k V] {W : Submodule k V} (hW : ∀ g : X, ∀ v ∈ W, ρ g v ∈ W)
    (hW0 : W ≠ ⊥) :
    ∃ S : Submodule k V, S ≠ ⊥ ∧ S ≤ W ∧ (∀ g : X, ∀ v ∈ S, ρ g v ∈ S) ∧
      ∀ T : Submodule k V, T ≤ S → (∀ g : X, ∀ v ∈ T, ρ g v ∈ T) → T = ⊥ ∨ T = S := by
  classical
  set 𝒮 : Set ℕ := {n | ∃ S : Submodule k V, S ≠ ⊥ ∧ S ≤ W ∧
      (∀ g : X, ∀ v ∈ S, ρ g v ∈ S) ∧ finrank k S = n} with h𝒮
  have hne : finrank k W ∈ 𝒮 := ⟨W, hW0, le_rfl, hW, rfl⟩
  obtain ⟨S, hS0, hSle, hSinv, hSrank⟩ := Nat.sInf_mem ⟨_, hne⟩
  refine ⟨S, hS0, hSle, hSinv, fun T hTle hTinv => ?_⟩
  rcases eq_or_ne T ⊥ with hb | hb
  · exact Or.inl hb
  · refine Or.inr (Submodule.eq_of_le_of_finrank_le hTle ?_)
    rw [hSrank]
    exact Nat.sInf_le ⟨T, hb, hTle.trans hSle, hTinv, rfl⟩

theorem isIrreducible_subrepresentation_of_minimal {X : Type*} [Group X]
    (ρ : Representation k X V) [FiniteDimensional k V]
    {S : Submodule k V} (hS0 : S ≠ ⊥) (hSinv : ∀ g : X, ∀ v ∈ S, ρ g v ∈ S)
    (hmin : ∀ T : Submodule k V, T ≤ S → (∀ g : X, ∀ v ∈ T, ρ g v ∈ T) → T = ⊥ ∨ T = S) :
    (ρ.subrepresentation S (fun g v hv => hSinv g v hv)).IsIrreducible := by
  have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hS0
  refine isIrreducible_of_forall_eq_bot_or_eq_top _ fun U hU => ?_
  have hmap : ∀ g : X, ∀ v ∈ U.map S.subtype, ρ g v ∈ U.map S.subtype := by
    rintro g v ⟨w, hw, rfl⟩
    exact ⟨_, hU g w hw, by
      simp [Representation.subrepresentation_apply, LinearMap.coe_restrict_apply]⟩
  rcases hmin _ (Submodule.map_subtype_le _ _) hmap with hb | ht
  · left
    have hiff := Submodule.map_le_map_iff_of_injective (Submodule.injective_subtype S) U ⊥
    simp only [Submodule.map_bot] at hiff
    exact le_bot_iff.1 (hiff.1 (by rw [hb]))
  · right
    refine top_unique fun x _ => ?_
    obtain ⟨y, hy, hxy⟩ : (x : V) ∈ U.map S.subtype := by rw [ht]; exact x.2
    exact (Subtype.ext hxy : y = x) ▸ hy

section Main

variable {p r : ℕ} {P H : Type u} [Group P] [Group H] {α : H →* MulAut P} {h : H}
  {ρ : Representation k (P ⋊[α] H) V}

theorem resInl_comp_center_subtype_apply (ρ : Representation k (P ⋊[α] H) V)
    (z : ↥(Subgroup.center P)) :
    ((resInl ρ).comp (Subgroup.center P).subtype) z = ρ (SemidirectProduct.inl (z : P)) := by
  rw [MonoidHom.comp_apply, Subgroup.coe_subtype, resInl_apply]

theorem exists_ne_zero_mem_invariants_resInr_of_center_nontrivial (hP : IsExtraspecial p P)
    [IsAlgClosed k] [FiniteDimensional k V] (hp : (p : k) ≠ 0) (hpodd : Odd p)
    (hα : ∀ (a : H) (z : P), z ∈ Subgroup.center P → α a z = z)
    (hr : r.Prime) (hrodd : Odd r) (hrk : (r : k) ≠ 0) (hho : orderOf h = r)
    (hgen : Subgroup.zpowers h = ⊤)
    (hfix : ∀ q : P ⧸ Subgroup.center P, (∀ a : H, centerQuotAut α a q = q) → q = 1)
    (hnt : ∃ z ∈ Subgroup.center P, ρ (SemidirectProduct.inl z) ≠ 1) :
    ∃ x : V, x ≠ 0 ∧ x ∈ (resInr ρ).invariants := by
  have : Finite P := hP.finite
  let _ : CommGroup ↥(Subgroup.center P) := IsMulCommutative.instCommGroup
  set σ : Representation k ↥(Subgroup.center P) V :=
    (resInl ρ).comp (Subgroup.center P).subtype with hσ
  have hσapply : ∀ z : ↥(Subgroup.center P), σ z = ρ (SemidirectProduct.inl (z : P)) := fun z => by
    rw [hσ, resInl_comp_center_subtype_apply]
  have hcard : (Nat.card ↥(Subgroup.center P) : k) ≠ 0 := by rw [hP.card_center]; exact hp
  obtain ⟨zeta, hzeta, hW0⟩ := exists_ne_one_characterSpace_ne_bot σ hcard
    (by obtain ⟨z, hz, hne⟩ := hnt; exact ⟨⟨z, hz⟩, by rw [hσapply]; exact hne⟩)
  set W : Submodule k V := Representation.characterSpace σ zeta with hWdef
  have hWmem : ∀ w ∈ W, ∀ z : ↥(Subgroup.center P),
      ρ (SemidirectProduct.inl (z : P)) w = (zeta z : k) • w := by
    intro w hw z
    rw [hWdef, Representation.mem_characterSpace_iff] at hw
    rw [← hσapply]; exact hw z
  have hWinv : ∀ g : P ⋊[α] H, ∀ w ∈ W, ρ g w ∈ W := by
    intro g w hw
    rw [hWdef, Representation.mem_characterSpace_iff]
    intro z
    have hcen : (SemidirectProduct.inl (z : P) : P ⋊[α] H) ∈ Subgroup.center (P ⋊[α] H) :=
      inl_mem_center_of_forall_apply_eq z.2 fun a => hα a z z.2
    have hcomm : ρ (SemidirectProduct.inl (z : P)) * ρ g
        = ρ g * ρ (SemidirectProduct.inl (z : P)) := by
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hcen g]
    have hcw := congrArg (fun T : Module.End k V => T w) hcomm
    simp only [Module.End.mul_apply] at hcw
    rw [hσapply, hcw, hWmem w hw z, map_smul]
  obtain ⟨S, hS0, hSW, hSinv, hSmin⟩ := exists_minimal_invariant_le ρ hWinv hW0
  set ρS : Representation k (P ⋊[α] H) ↥S := ρ.subrepresentation S (fun g v hv => hSinv g v hv)
    with hρS
  have hρSapply : ∀ (g : P ⋊[α] H) (x : ↥S), ((ρS g x : ↥S) : V) = ρ g (x : V) := fun g x => by
    rw [hρS, Representation.subrepresentation_apply, LinearMap.coe_restrict_apply]
  have hirrS : ρS.IsIrreducible :=
    isIrreducible_subrepresentation_of_minimal ρ hS0 hSinv hSmin
  have hzS : ∀ (z : ↥(Subgroup.center P)) (x : ↥S),
      resInl ρS (z : P) x = (zeta z : k) • x := fun z x =>
    Subtype.ext <| by rw [resInl_apply, hρSapply]; simpa using hWmem (x : V) (hSW x.2) z
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_mem_invariants_resInr (ρ := ρS) (zeta := zeta)
    hP hp hpodd hirrS hzeta hzS hr hrodd hrk hho hgen hfix
  refine ⟨(x : V), fun hc => hx0 (Subtype.ext hc), ?_⟩
  rw [mem_invariants_resInr]
  intro a
  rw [← hρSapply, mem_invariants_resInr.1 hx a]

theorem invariants_resInr_ne_bot_of_center_nontrivial (hP : IsExtraspecial p P)
    [IsAlgClosed k] [FiniteDimensional k V] (hp : (p : k) ≠ 0) (hpodd : Odd p)
    (hα : ∀ (a : H) (z : P), z ∈ Subgroup.center P → α a z = z)
    (hr : r.Prime) (hrodd : Odd r) (hrk : (r : k) ≠ 0) (hho : orderOf h = r)
    (hgen : Subgroup.zpowers h = ⊤)
    (hfix : ∀ q : P ⧸ Subgroup.center P, (∀ a : H, centerQuotAut α a q = q) → q = 1)
    (hnt : ∃ z ∈ Subgroup.center P, ρ (SemidirectProduct.inl z) ≠ 1) :
    (resInr ρ).invariants ≠ ⊥ := by
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_mem_invariants_resInr_of_center_nontrivial hP hp hpodd hα
    hr hrodd hrk hho hgen hfix hnt
  exact fun hbot => hx0 (Submodule.mem_bot k |>.1 (hbot ▸ hx))

theorem exists_ne_zero_mem_invariants_resInr_of_faithful (hP : IsExtraspecial p P)
    [IsAlgClosed k] [FiniteDimensional k V] (hp : (p : k) ≠ 0) (hpodd : Odd p)
    (hα : ∀ (a : H) (z : P), z ∈ Subgroup.center P → α a z = z)
    (hr : r.Prime) (hrodd : Odd r) (hrk : (r : k) ≠ 0) (hho : orderOf h = r)
    (hgen : Subgroup.zpowers h = ⊤)
    (hfix : ∀ q : P ⧸ Subgroup.center P, (∀ a : H, centerQuotAut α a q = q) → q = 1)
    (hfaithful : ∀ g : P ⋊[α] H, ρ g = 1 → g = 1) :
    ∃ x : V, x ≠ 0 ∧ x ∈ (resInr ρ).invariants := by
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ Subgroup.center P, z ≠ 1 := by
    have hne := hP.center_ne_bot
    rw [Ne, Subgroup.eq_bot_iff_forall] at hne
    push Not at hne
    exact hne
  refine exists_ne_zero_mem_invariants_resInr_of_center_nontrivial hP hp hpodd hα hr hrodd hrk
    hho hgen hfix ⟨z, hz, fun hc => hz1 ?_⟩
  simpa using congrArg SemidirectProduct.left (hfaithful _ hc)

end Main

end

end CFSG.FeitThompson
