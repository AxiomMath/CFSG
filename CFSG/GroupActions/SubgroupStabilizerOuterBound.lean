module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.GroupActions

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {G : Type*} [Group G] (H : Subgroup G)

@[expose] def subgroupStabAut : Subgroup (MulAut G) where
  carrier := {α | H.map α.toMonoidHom = H}
  mul_mem' {α β} hα hβ := by
    change H.map (α.toMonoidHom.comp β.toMonoidHom) = H
    rw [← Subgroup.map_map]
    change H.map β.toMonoidHom = H at hβ
    rw [hβ]
    exact hα
  one_mem' := Subgroup.map_id H
  inv_mem' {α} hα := by
    change H.map α.toMonoidHom = H at hα
    change H.map α.symm.toMonoidHom = H
    ext x
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, ← hα, Subgroup.mem_map_equiv,
      MulEquiv.symm_apply_apply, hα]

variable {H}

theorem apply_mem_of_mem_subgroupStabAut {α : MulAut G} (hα : α ∈ subgroupStabAut H)
    {x : G} (hx : x ∈ H) : α x ∈ H := by
  rw [← (hα : H.map α.toMonoidHom = H)]
  exact Subgroup.mem_map_of_mem _ hx

variable (H)

@[expose] noncomputable def subgroupStabRestrict : subgroupStabAut H →* MulAut H where
  toFun α :=
    { toFun := fun x => ⟨α.1 x, apply_mem_of_mem_subgroupStabAut α.2 x.2⟩
      invFun := fun x => ⟨α.1⁻¹ x, apply_mem_of_mem_subgroupStabAut (inv_mem α.2) x.2⟩
      left_inv := fun x => Subtype.ext (α.1.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (α.1.apply_symm_apply x)
      map_mul' := fun x y => Subtype.ext (map_mul α.1 (x : G) (y : G)) }
  map_one' := MulEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := MulEquiv.ext fun _ => Subtype.ext rfl

theorem subgroupStabRestrict_apply (α : subgroupStabAut H) (x : H) :
    ((subgroupStabRestrict H α x : H) : G) = (α : MulAut G) (x : G) :=
  rfl

theorem subgroup_stabilizer_outer_restriction_bound [Finite G]
    (hfix : ∀ α : MulAut G, (∀ h ∈ H, α h = h) → α = 1) :
    let ρ : subgroupStabAut H →* Outer H :=
      (QuotientGroup.mk' (inner H)).comp (subgroupStabRestrict H)
    (∀ h ∈ H, MulAut.conj h ∈ subgroupStabAut H) ∧
    (∀ α : subgroupStabAut H, α ∈ ρ.ker ↔ ∃ h ∈ H, (α : MulAut G) = MulAut.conj h) ∧
    ρ.ker.Normal ∧
    (∃ f : subgroupStabAut H ⧸ ρ.ker →* Outer H, Function.Injective f ∧
      ∀ α : subgroupStabAut H, f (QuotientGroup.mk α) =
        ((subgroupStabRestrict H α : MulAut H) : Outer H)) ∧
    Nat.card ((subgroupStabAut H).map (QuotientGroup.mk' (inner G))) ∣ Nat.card (Outer H) ∧
    ((∀ α : MulAut G, ∃ g : G, H.map α.toMonoidHom = H.map (MulAut.conj g).toMonoidHom) →
      Nat.card (Outer G) ∣ Nat.card (Outer H)) := by
  intro ρ
  have hconjN : ∀ h ∈ H, MulAut.conj h ∈ subgroupStabAut H := by
    intro h hh
    change H.map (MulAut.conj h).toMonoidHom = H
    ext x
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    constructor
    · intro hx
      have := mul_mem (mul_mem hh hx) (inv_mem hh)
      simpa [mul_assoc] using this
    · intro hx
      exact mul_mem (mul_mem (inv_mem hh) hx) hh
  have hker : ∀ α : subgroupStabAut H, α ∈ ρ.ker ↔ ∃ h ∈ H, (α : MulAut G) = MulAut.conj h := by
    intro α
    rw [MonoidHom.mem_ker]
    change ((subgroupStabRestrict H α : MulAut H) : Outer H) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨h, hh⟩
      refine ⟨h, h.2, ?_⟩
      have hpt : ∀ x ∈ H, ((MulAut.conj (h : G))⁻¹ * (α : MulAut G)) x = x := by
        intro x hx
        have h1 := congrArg (fun φ : MulAut H => ((φ ⟨x, hx⟩ : H) : G)) hh
        simp only [MulAut.conj_apply, subgroupStabRestrict_apply] at h1
        rw [MulAut.mul_apply, ← h1, MulAut.conj_inv_apply, Subgroup.coe_mul, Subgroup.coe_mul,
          Subgroup.coe_inv]
        group
      have h2 := hfix _ hpt
      rw [inv_mul_eq_one] at h2
      exact h2.symm
    · rintro ⟨h, hh, hα⟩
      refine ⟨⟨h, hh⟩, MulEquiv.ext fun x => Subtype.ext ?_⟩
      rw [subgroupStabRestrict_apply, hα]
      rfl
  have hnorm : ρ.ker.Normal := MonoidHom.normal_ker ρ
  have hdiv : Nat.card ((subgroupStabAut H).map (QuotientGroup.mk' (inner G))) ∣
      Nat.card (Outer H) := by
    set π := (QuotientGroup.mk' (inner G)).comp (subgroupStabAut H).subtype with hπ
    have hle : ρ.ker ≤ π.ker := by
      intro α hα
      obtain ⟨h, -, hα'⟩ := (hker α).1 hα
      rw [MonoidHom.mem_ker]
      change ((α : MulAut G) : Outer G) = 1
      rw [QuotientGroup.eq_one_iff, hα']
      exact ⟨h, rfl⟩
    let q : subgroupStabAut H ⧸ ρ.ker →* (subgroupStabAut H).map (QuotientGroup.mk' (inner G)) :=
      QuotientGroup.lift ρ.ker
        ((π.codRestrict _ fun α => ⟨α, α.2, rfl⟩)) (fun α hα => by
          apply Subtype.ext
          exact hle hα)
    have hq : Function.Surjective q := by
      rintro ⟨_, ⟨α, hα, rfl⟩⟩
      exact ⟨((⟨α, hα⟩ : subgroupStabAut H) : subgroupStabAut H ⧸ ρ.ker), rfl⟩
    exact (Subgroup.card_dvd_of_surjective hq).trans
      (Subgroup.card_dvd_of_injective _ (QuotientGroup.kerLift_injective ρ))
  refine ⟨hconjN, hker, hnorm, ⟨QuotientGroup.kerLift ρ, QuotientGroup.kerLift_injective ρ,
    fun α => rfl⟩, hdiv, fun hconj => ?_⟩
  have htop : (subgroupStabAut H).map (QuotientGroup.mk' (inner G)) = ⊤ := by
    refine eq_top_iff.2 fun q _ => ?_
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner G) q
    obtain ⟨g, hg⟩ := hconj α
    refine ⟨(MulAut.conj g)⁻¹ * α, ?_, ?_⟩
    · change H.map ((MulAut.conj g)⁻¹ * α).toMonoidHom = H
      rw [show ((MulAut.conj g)⁻¹ * α).toMonoidHom =
        ((MulAut.conj g)⁻¹).toMonoidHom.comp α.toMonoidHom from rfl, ← Subgroup.map_map, hg,
        Subgroup.map_map]
      have hid : ((MulAut.conj g)⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
          MonoidHom.id G := MonoidHom.ext fun x => MulAut.inv_apply_self G (MulAut.conj g) x
      rw [hid, Subgroup.map_id]
    · change (((MulAut.conj g)⁻¹ * α : MulAut G) : Outer G) = (α : Outer G)
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (N := inner G)
        ((MulAut.conj g)⁻¹)).2 ⟨g⁻¹, by rw [map_inv]⟩, one_mul]
  rw [htop, Subgroup.card_top] at hdiv
  exact hdiv

end CFSG.GroupActions
