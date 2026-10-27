module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2Generation
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2Binary
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Sub
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LinearGroups

section Displacement

variable {G E : Type*} [Group G] [AddCommGroup E] [Module (ZMod 2) E]

@[expose] def disp (ρ : G →* (E ≃ₗ[ZMod 2] E)) (a : G) : E →ₗ[ZMod 2] E :=
  (ρ a : E →ₗ[ZMod 2] E) - LinearMap.id

theorem disp_apply (ρ : G →* (E ≃ₗ[ZMod 2] E)) (a : G) (v : E) : disp ρ a v = ρ a v - v := rfl

@[expose] def commSub (ρ : G →* (E ≃ₗ[ZMod 2] E)) (A : Subgroup G) : Submodule (ZMod 2) E :=
  Submodule.span (ZMod 2) {x | ∃ a ∈ A, ∃ e : E, x = ρ a e - e}

theorem range_disp_conj (ρ : G →* (E ≃ₗ[ZMod 2] E)) (a g : G) :
    LinearMap.range (disp ρ (g * a * g⁻¹)) =
      (LinearMap.range (disp ρ a)).map (ρ g : E →ₗ[ZMod 2] E) := by
  have hg : ∀ v : E, ρ g (ρ g⁻¹ v) = v := fun v => by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hg' : ∀ v : E, ρ g⁻¹ (ρ g v) = v := fun v => by
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  ext x
  simp only [Submodule.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨disp ρ a (ρ g⁻¹ v), ⟨_, rfl⟩, ?_⟩
    simp only [disp_apply, LinearEquiv.coe_coe, map_sub, hg, map_mul, LinearEquiv.mul_apply]
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    refine ⟨ρ g w, ?_⟩
    simp only [disp_apply, LinearEquiv.coe_coe, map_sub, hg', map_mul, LinearEquiv.mul_apply]

theorem finrank_range_disp_conj (ρ : G →* (E ≃ₗ[ZMod 2] E)) (a g : G) :
    Module.finrank (ZMod 2) (LinearMap.range (disp ρ (g * a * g⁻¹))) =
      Module.finrank (ZMod 2) (LinearMap.range (disp ρ a)) := by
  rw [range_disp_conj]
  exact LinearEquiv.finrank_map_eq (ρ g) _

theorem range_disp_mul_le (ρ : G →* (E ≃ₗ[ZMod 2] E)) (g h : G) :
    LinearMap.range (disp ρ (g * h)) ≤
      LinearMap.range (disp ρ g) ⊔ LinearMap.range (disp ρ h) := by
  rintro _ ⟨v, rfl⟩
  have : disp ρ (g * h) v = disp ρ g (ρ h v) + disp ρ h v := by
    rw [disp_apply, disp_apply, disp_apply, map_mul, LinearEquiv.mul_apply, sub_add_sub_cancel]
  rw [this]
  exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩

theorem finrank_range_disp_mul_le [Module.Finite (ZMod 2) E] (ρ : G →* (E ≃ₗ[ZMod 2] E))
    (g h : G) :
    Module.finrank (ZMod 2) (LinearMap.range (disp ρ (g * h))) ≤
      Module.finrank (ZMod 2) (LinearMap.range (disp ρ g)) +
        Module.finrank (ZMod 2) (LinearMap.range (disp ρ h)) :=
  (Submodule.finrank_mono (range_disp_mul_le ρ g h)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem fixedSub_le_ker_disp (ρ : G →* (E ≃ₗ[ZMod 2] E)) {A : Subgroup G} {a : G} (ha : a ∈ A) :
    fixedSub ρ A ≤ LinearMap.ker (disp ρ a) := fun x hx => by
  rw [LinearMap.mem_ker, disp_apply, mem_fixedSub.1 hx a ha, sub_self]

theorem finrank_range_disp_le_of_offender [Module.Finite (ZMod 2) E]
    (ρ : G →* (E ≃ₗ[ZMod 2] E)) {B : Subgroup G} {a : G} (ha : a ∈ B) {L : ℕ}
    (hoff : Module.finrank (ZMod 2) E - Module.finrank (ZMod 2) (fixedSub ρ B) ≤ L) :
    Module.finrank (ZMod 2) (LinearMap.range (disp ρ a)) ≤ L := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (disp ρ a)
  have h2 : Module.finrank (ZMod 2) (fixedSub ρ B) ≤
      Module.finrank (ZMod 2) (LinearMap.ker (disp ρ a)) :=
    Submodule.finrank_mono (fixedSub_le_ker_disp ρ ha)
  omega

theorem commSub_le_of_closure (ρ : G →* (E ≃ₗ[ZMod 2] E)) (D : Submodule (ZMod 2) E) {X : Set G}
    (hX : ∀ g ∈ X, ∀ v, ρ g v - v ∈ D) {A : Subgroup G} (hA : A ≤ Subgroup.closure X) :
    commSub ρ A ≤ D := by
  let Stab : Subgroup G :=
    { carrier := {s | ∀ v, ρ s v - v ∈ D}
      one_mem' := fun v => by simp
      mul_mem' := fun {s t} hs ht v => by
        have : ρ (s * t) v - v = (ρ s (ρ t v) - ρ t v) + (ρ t v - v) := by
          rw [map_mul, LinearEquiv.mul_apply]
          abel
        rw [this]
        exact D.add_mem (hs _) (ht v)
      inv_mem' := fun {s} hs v => by
        have h1 : ρ s (ρ s⁻¹ v) = v := by
          rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
          rfl
        have := D.neg_mem (hs (ρ s⁻¹ v))
        rwa [h1, neg_sub] at this }
  have hcl : Subgroup.closure X ≤ Stab := (Subgroup.closure_le Stab).2 fun g hg v => hX g hg v
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, ha, e, rfl⟩
  exact hcl (hA ha) e

end Displacement

section LowRank

variable {p : ℕ} [hpf : Fact p.Prime] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

theorem p2_isSimpleGroup (hp5 : 5 ≤ p) : IsSimpleGroup (projectiveSL 2 (ZMod p)) := by
  have hcard : ∃ s : Finset (ZMod p), s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (ZMod p)))
      (n := 4) (by rw [Finset.card_univ, ZMod.card]; omega)
    exact ⟨s, hs⟩
  have := (linear_projective_simple (n := 2) (K := ZMod p) le_rfl (Or.inr hcard)).2.1
  exact (p2Equiv (ZMod p)).isSimpleGroup

theorem p2_actor_of_low_rank_involution (hp5 : 5 ≤ p) [Module.Finite (ZMod 2) E] [Nontrivial E]
    (ρ : projectiveSL 2 (ZMod p) →* (E ≃ₗ[ZMod 2] E)) (hE : commSub ρ ⊤ = ⊤)
    {a : projectiveSL 2 (ZMod p)} (ha1 : a ≠ 1) (ha2 : a * a = 1)
    (hrk : Module.finrank (ZMod 2) (LinearMap.range (disp ρ a)) ≤ 2) :
    Function.Injective ρ ∧ Module.finrank (ZMod 2) E ≤ 6 ∧ (p = 5 ∨ p = 7) := by
  obtain ⟨a₁, a₂, a₃, h1, h2, h3, hgen⟩ := p2_three_involution_generation hp5 ha1 ha2
  obtain ⟨g₁, rfl⟩ := isConj_iff.1 h1
  obtain ⟨g₂, rfl⟩ := isConj_iff.1 h2
  obtain ⟨g₃, rfl⟩ := isConj_iff.1 h3
  set D := LinearMap.range (disp ρ (g₁ * a * g₁⁻¹)) ⊔ LinearMap.range (disp ρ (g₂ * a * g₂⁻¹)) ⊔
    LinearMap.range (disp ρ (g₃ * a * g₃⁻¹)) with hD
  have hgens : ∀ g ∈ ({g₁ * a * g₁⁻¹, g₂ * a * g₂⁻¹, g₃ * a * g₃⁻¹} :
      Set (projectiveSL 2 (ZMod p))), ∀ v, ρ g v - v ∈ D := by
    intro g hg v
    have hv : ρ g v - v = disp ρ g v := rfl
    rw [hv]
    rcases hg with rfl | rfl | rfl
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left ⟨v, rfl⟩)
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨v, rfl⟩)
    · exact Submodule.mem_sup_right ⟨v, rfl⟩
  have hDtop : D = ⊤ := by
    have hle : commSub ρ ⊤ ≤ D := commSub_le_of_closure ρ D hgens (by rw [hgen])
    rw [hE] at hle
    exact top_le_iff.1 hle
  have hdim : Module.finrank (ZMod 2) E ≤ 6 := by
    have hD1 : Module.finrank (ZMod 2) D ≤
        Module.finrank (ZMod 2) (LinearMap.range (disp ρ (g₁ * a * g₁⁻¹))) +
          Module.finrank (ZMod 2) (LinearMap.range (disp ρ (g₂ * a * g₂⁻¹))) +
          Module.finrank (ZMod 2) (LinearMap.range (disp ρ (g₃ * a * g₃⁻¹))) :=
      ((Submodule.finrank_add_le_finrank_add_finrank _ _).trans
        (Nat.add_le_add_right (Submodule.finrank_add_le_finrank_add_finrank _ _) _))
    rw [finrank_range_disp_conj, finrank_range_disp_conj, finrank_range_disp_conj] at hD1
    have hDE : Module.finrank (ZMod 2) D = Module.finrank (ZMod 2) E := by
      rw [hDtop]
      exact finrank_top (ZMod 2) E
    omega
  have hinj : Function.Injective ρ := by
    have := p2_isSimpleGroup hp5 (p := p)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff ρ).1 h
    · exfalso
      obtain ⟨x, hx⟩ := exists_ne (0 : E)
      have hxm : x ∈ commSub ρ ⊤ := by rw [hE]; trivial
      have hle : commSub ρ ⊤ ≤ ⊥ := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨s, -, e, rfl⟩
        have hs : s ∈ ρ.ker := by rw [h]; trivial
        rw [MonoidHom.mem_ker] at hs
        rw [hs]
        simp
      exact hx (Submodule.mem_bot _ |>.1 (hle hxm))
  exact ⟨hinj, hdim, p2_binary_six_space hp5 hdim ρ hinj⟩

theorem p2_internal_offender_actor (hp5 : 5 ≤ p) [Module.Finite (ZMod 2) E] [Nontrivial E]
    (ρ : projectiveSL 2 (ZMod p) →* (E ≃ₗ[ZMod 2] E)) (hE : commSub ρ ⊤ = ⊤)
    {B : Subgroup (projectiveSL 2 (ZMod p))} (hB1 : B ≠ ⊥)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB2 : ∀ a ∈ B, a * a = 1)
    (hoff : Module.finrank (ZMod 2) E - Module.finrank (ZMod 2) (fixedSub ρ B) ≤
      Nat.log 2 (Nat.card B)) :
    Function.Injective ρ ∧ Module.finrank (ZMod 2) E ≤ 6 ∧ (p = 5 ∨ p = 7) := by
  obtain ⟨-, hcard⟩ := p2_involution_structure hp5
  have h4 : Nat.card B ≤ 4 := hcard B hBc hB2
  have hlog : Nat.log 2 (Nat.card B) ≤ 2 :=
    (Nat.log_mono_right h4).trans (by norm_num)
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB1
  have ha1 : (a : projectiveSL 2 (ZMod p)) ≠ 1 := fun h => ha (Subtype.ext h)
  refine p2_actor_of_low_rank_involution hp5 ρ hE ha1 (hB2 a a.2) ?_
  exact finrank_range_disp_le_of_offender ρ a.2 (hoff.trans hlog)

end LowRank

end CFSG.QuasithinUnique.Setup.Family
