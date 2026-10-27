module

public import CFSG.LieType.ChevTwo.OppCl.Defs

public section

namespace CFSG.LieType.ChevTwo.OppCl.TK

open CFSG.Open CFSG.LieType.BorelTits

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {H K : Type} [Group H] [Group K]

theorem induces_one (π : H →* K) (ρ : H →* Module.End F V) : Induces π ρ 1 1 := by
  refine ⟨fun h => ⟨h, fun v => ?_, ?_⟩, fun h => ⟨h, fun v => ?_, ?_⟩⟩ <;> simp

theorem induces_mul {π : H →* K} {ρ : H →* Module.End F V} {r s : Equiv.Perm V} {α β : MulAut K}
    (hr : Induces π ρ r α) (hs : Induces π ρ s β) : Induces π ρ (r * s) (α * β) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨h₁, hs₁, hβ⟩ := hs.1 h
    obtain ⟨h₂, hr₂, hα⟩ := hr.1 h₁
    refine ⟨h₂, fun v => ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hs₁ v, hr₂ (s v)]
    · rw [MulAut.mul_apply, hβ, hα]
  · obtain ⟨h₁, hr₁, hα⟩ := hr.2 h
    obtain ⟨h₂, hs₂, hβ⟩ := hs.2 h₁
    refine ⟨h₂, fun v => ?_, ?_⟩
    · rw [mul_inv_rev, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hr₁ v, hs₂ (r⁻¹ v)]
    · rw [mul_inv_rev, MulAut.mul_apply, hα, hβ]

theorem induces_inv {π : H →* K} {ρ : H →* Module.End F V} {r : Equiv.Perm V} {α : MulAut K}
    (hr : Induces π ρ r α) : Induces π ρ r⁻¹ α⁻¹ := by
  refine ⟨hr.2, fun h => ?_⟩
  simpa only [inv_inv] using hr.1 h

theorem normH_of_induces {π : H →* K} {ρ : H →* Module.End F V} {r : Equiv.Perm V} {α : MulAut K}
    (hr : Induces π ρ r α) : NormH ρ r := by
  intro h
  obtain ⟨h', hh', -⟩ := hr.1 h
  exact ⟨h', hh'⟩

theorem autLift_of_induced [Finite V] [Finite K] {π : H →* K} {ρ : H →* Module.End F V}
    (P : Equiv.Perm V → Prop) (hP1 : P 1) (hPm : ∀ r s, P r → P s → P (r * s))
    (hPi : ∀ r, P r → P r⁻¹) (p : ℕ) [Fact p.Prime] (R : Subgroup (MulAut K))
    (hR : IsPGroup p R)
    (hind : ∀ α ∈ R, ∃ r : Equiv.Perm V, r ∈ semilinGroup F V ∧ P r ∧ Induces π ρ r α) :
    ∃ Rh : Subgroup (Equiv.Perm V), Rh ≤ semilinGroup F V ∧ (∀ r ∈ Rh, P r) ∧ IsPGroup p Rh ∧
      (∀ r ∈ Rh, NormH ρ r) ∧ (∀ α ∈ R, ∃ r ∈ Rh, Induces π ρ r α) ∧
      (∀ r ∈ Rh, ∃ α ∈ R, Induces π ρ r α) := by
  let Γ : Subgroup (Equiv.Perm V × MulAut K) :=
    { carrier := {x | x.1 ∈ semilinGroup F V ∧ P x.1 ∧ Induces π ρ x.1 x.2 ∧ x.2 ∈ R}
      one_mem' := ⟨one_mem _, hP1, induces_one π ρ, one_mem _⟩
      mul_mem' := fun {x y} hx hy =>
        ⟨mul_mem hx.1 hy.1, hPm _ _ hx.2.1 hy.2.1, induces_mul hx.2.2.1 hy.2.2.1,
          mul_mem hx.2.2.2 hy.2.2.2⟩
      inv_mem' := fun {x} hx =>
        ⟨inv_mem hx.1, hPi _ hx.2.1, induces_inv hx.2.2.1, inv_mem hx.2.2.2⟩ }
  have hmem : ∀ x : Equiv.Perm V × MulAut K, x ∈ Γ ↔
      (x.1 ∈ semilinGroup F V ∧ P x.1 ∧ Induces π ρ x.1 x.2 ∧ x.2 ∈ R) := fun x => Iff.rfl
  haveI : Finite Γ := inferInstance
  let f : Γ →* R := ((MonoidHom.snd (Equiv.Perm V) (MulAut K)).comp Γ.subtype).codRestrict R
    (fun x => ((hmem _).mp x.2).2.2.2)
  have hf : Function.Surjective f := by
    rintro ⟨α, hα⟩
    obtain ⟨r, hr, hPr, hind'⟩ := hind α hα
    exact ⟨⟨(r, α), (hmem _).mpr ⟨hr, hPr, hind', hα⟩⟩, rfl⟩
  obtain ⟨S⟩ : Nonempty (Sylow p Γ) := inferInstance
  have htop : (S : Subgroup Γ).map f = ⊤ := by
    have h := (Sylow.mapSurjective hf S).is_maximal' (hR.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective] at h
    exact h.symm
  let g : Γ →* Equiv.Perm V := (MonoidHom.fst (Equiv.Perm V) (MulAut K)).comp Γ.subtype
  refine ⟨(S : Subgroup Γ).map g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact ((hmem _).mp x.2).1
  · rintro _ ⟨x, -, rfl⟩
    exact ((hmem _).mp x.2).2.1
  · exact S.isPGroup'.map g
  · rintro _ ⟨x, -, rfl⟩
    exact normH_of_induces ((hmem _).mp x.2).2.2.1
  · intro α hα
    have hmem' : (⟨α, hα⟩ : ↥R) ∈ (S : Subgroup Γ).map f := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨x, hx, hxα⟩ := Subgroup.mem_map.mp hmem'
    have hxα' : (x : Equiv.Perm V × MulAut K).2 = α := congrArg Subtype.val hxα
    refine ⟨g x, Subgroup.mem_map_of_mem g hx, ?_⟩
    have hi := ((hmem _).mp x.2).2.2.1
    rw [hxα'] at hi
    exact hi
  · rintro _ ⟨x, -, rfl⟩
    exact ⟨(x : Equiv.Perm V × MulAut K).2, ((hmem _).mp x.2).2.2.2, ((hmem _).mp x.2).2.2.1⟩

end CFSG.LieType.ChevTwo.OppCl.TK
