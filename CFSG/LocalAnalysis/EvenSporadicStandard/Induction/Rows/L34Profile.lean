module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.L34Q8Sound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverFixInduced

public section

namespace CFSG.EvenSporadicStandard.L34Q8

open CFSG.ComponentClassification.PSL3Four CFSG.EvenSporadicStandard.Induction.CoverFix Subgroup


theorem exists_fixed_hom {β : MulAut ↥S} {ρ : Equiv.Perm (Fin 42)}
    (hβρ : ∀ s : ↥S, (β s : Equiv.Perm (Fin 42)) = ρ * s * ρ⁻¹) {c r₀ : Equiv.Perm (Fin 42)}
    (hc : c ∈ R) (hρ : ρ = c * r₀ * c⁻¹) :
    ∃ ψ : ↥(centralizer {r₀} ⊓ S) →* ↥(fixed β), Function.Injective ψ ∧
      ∀ s, ((ψ s : ↥S) : Equiv.Perm (Fin 42)) = c * s * c⁻¹ := by
  have hmem : ∀ s : ↥(centralizer ({r₀} : Set (Equiv.Perm (Fin 42))) ⊓ S),
      c * (s : Equiv.Perm (Fin 42)) * c⁻¹ ∈ S := fun s => conj_mem_S hc (mem_inf.1 s.2).2
  have hfix : ∀ s : ↥(centralizer ({r₀} : Set (Equiv.Perm (Fin 42))) ⊓ S),
      β ⟨c * (s : Equiv.Perm (Fin 42)) * c⁻¹, hmem s⟩ =
        ⟨c * (s : Equiv.Perm (Fin 42)) * c⁻¹, hmem s⟩ := by
    intro s
    have hs : (s : Equiv.Perm (Fin 42)) * r₀ = r₀ * s :=
      mem_centralizer_singleton_iff.1 (mem_inf.1 s.2).1
    apply Subtype.ext
    rw [hβρ, hρ]
    calc c * r₀ * c⁻¹ * (c * (s : Equiv.Perm (Fin 42)) * c⁻¹) * (c * r₀ * c⁻¹)⁻¹
        = c * (r₀ * s * r₀⁻¹) * c⁻¹ := by group
      _ = c * (s * r₀ * r₀⁻¹) * c⁻¹ := by rw [hs]
      _ = c * s * c⁻¹ := by group
  let ψ : ↥(centralizer ({r₀} : Set (Equiv.Perm (Fin 42))) ⊓ S) →* ↥(fixed β) :=
    { toFun := fun s => ⟨⟨c * (s : Equiv.Perm (Fin 42)) * c⁻¹, hmem s⟩, hfix s⟩
      map_one' := Subtype.ext (Subtype.ext (by simp))
      map_mul' := fun a b => Subtype.ext (Subtype.ext (by
        show c * ((a : Equiv.Perm (Fin 42)) * b) * c⁻¹ = _
        simp only [Subgroup.coe_mul]
        group)) }
  refine ⟨ψ, fun a b hab => ?_, fun s => rfl⟩
  have h1 : c * (a : Equiv.Perm (Fin 42)) * c⁻¹ = c * (b : Equiv.Perm (Fin 42)) * c⁻¹ :=
    congrArg (fun z : ↥(fixed β) => ((z : ↥S) : Equiv.Perm (Fin 42))) hab
  apply Subtype.ext
  have h2 : (a : Equiv.Perm (Fin 42)) = b := by
    have := congrArg (fun z => c⁻¹ * z * c) h1
    simpa [mul_assoc] using this
  exact h2

theorem q8Rel_subtype {a b : ↥S} (h : Q8Rel (a : Equiv.Perm (Fin 42)) (b : Equiv.Perm (Fin 42))) :
    Q8Rel a b :=
  Q8Rel.of_map S.subtype S.subtype_injective h

theorem l34_profile (β : MulAut ↥S) (h1 : β ≠ 1)
    (h2 : β * β = 1) :
    ¬ Group.IsSolvable ↥(fixed β) ∨
      (∃ x y : ↥S, Q8Rel x y ∧ β x = x ∧ β y = y ∧ ∀ t : ↥S, β ≠ MulAut.conj t) ∨
      (∃ t x y : ↥S, β = MulAut.conj t ∧ Q8Rel x y ∧ x * x = t) := by
  obtain ⟨e, he, -⟩ := full_automorphism_action
  obtain ⟨r, hr⟩ := e.surjective β
  have hr2 : r * r = 1 := e.injective (by rw [map_mul, hr, h2, map_one])
  have hr1 : r ≠ 1 := fun h => h1 (by rw [← hr, h, map_one])
  have hord : orderOf r = 2 := orderOf_eq_prime (by rwa [pow_two]) hr1
  have hβ : ∀ s : ↥S, (β s : Equiv.Perm (Fin 42)) =
      (r : Equiv.Perm (Fin 42)) * s * (r : Equiv.Perm (Fin 42))⁻¹ := fun s => by
    rw [← hr]
    exact he r s
  obtain ⟨x₁, y₁, x₄, y₄, hx₁, hy₁, hx₄, hy₄, hq1, hsq1, hq4, hc4x, hc4y⟩ := q8_data
  rcases (orderOf_eq_two_iff r).1 hord with hc | hc | hc | hc
  ·
    obtain ⟨c, hcR, hrc⟩ := eq_conj_of_isConj hc
    have hrS : (r : Equiv.Perm (Fin 42)) ∈ S := mem_S_of_isConj₁ hc
    refine Or.inr (Or.inr ⟨⟨r, hrS⟩, ⟨c * x₁ * c⁻¹, conj_mem_S hcR hx₁⟩,
      ⟨c * y₁ * c⁻¹, conj_mem_S hcR hy₁⟩, ?_, ?_, ?_⟩)
    · refine MulEquiv.ext fun s => Subtype.ext ?_
      rw [hβ]
      simp [MulAut.conj_apply]
    · refine q8Rel_subtype ?_
      have := hq1.map (MulAut.conj c).toMonoidHom (MulAut.conj c).injective
      simpa [MulAut.conj_apply] using this
    · apply Subtype.ext
      show c * x₁ * c⁻¹ * (c * x₁ * c⁻¹) = r
      rw [hrc]
      show _ = c * r₁ * c⁻¹
      rw [← hsq1]
      group
  ·
    obtain ⟨c, hcR, hrc⟩ := eq_conj_of_isConj hc
    have hrc' : (r : Equiv.Perm (Fin 42)) = c * r₂ * c⁻¹ := hrc
    left
    obtain ⟨ψ, hψ, -⟩ := exists_fixed_hom (β := β) (ρ := (r : Equiv.Perm (Fin 42))) hβ hcR hrc'
    intro hsolv
    have hsC : Group.IsSolvable ↥C₂ := Group.isSolvable_of_isSolvable_injective hψ
    have : IsSimpleGroup ↥C₂ := isSimpleGroup_C₂
    obtain ⟨a, b, hab⟩ := exists_mul_ne_C₂
    exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := ↥C₂)).2 hsC a b)
  ·
    obtain ⟨c, hcR, hrc⟩ := eq_conj_of_isConj hc
    have hrc' : (r : Equiv.Perm (Fin 42)) = c * r₃ * c⁻¹ := hrc
    left
    obtain ⟨ψ, hψ, -⟩ := exists_fixed_hom (β := β) (ρ := (r : Equiv.Perm (Fin 42))) hβ hcR hrc'
    intro hsolv
    have hsC : Group.IsSolvable ↥C₃ := Group.isSolvable_of_isSolvable_injective hψ
    have : IsSimpleGroup ↥C₃ := isSimpleGroup_C₃
    obtain ⟨a, b, hab⟩ := exists_mul_ne_C₃
    exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := ↥C₃)).2 hsC a b)
  ·
    obtain ⟨c, hcR, hrc⟩ := eq_conj_of_isConj hc
    have hrc' : (r : Equiv.Perm (Fin 42)) = c * r₄ * c⁻¹ := hrc
    have hx : c * x₄ * c⁻¹ ∈ S := conj_mem_S hcR hx₄
    have hy : c * y₄ * c⁻¹ ∈ S := conj_mem_S hcR hy₄
    have hfixed : ∀ z : Equiv.Perm (Fin 42), z * r₄ = r₄ * z →
        (r : Equiv.Perm (Fin 42)) * (c * z * c⁻¹) * (r : Equiv.Perm (Fin 42))⁻¹ =
          c * z * c⁻¹ := by
      intro z hz
      rw [hrc']
      calc c * r₄ * c⁻¹ * (c * z * c⁻¹) * (c * r₄ * c⁻¹)⁻¹ = c * (r₄ * z * r₄⁻¹) * c⁻¹ := by
            group
        _ = c * (z * r₄ * r₄⁻¹) * c⁻¹ := by rw [hz]
        _ = c * z * c⁻¹ := by group
    refine Or.inr (Or.inl ⟨⟨c * x₄ * c⁻¹, hx⟩, ⟨c * y₄ * c⁻¹, hy⟩, ?_, ?_, ?_, ?_⟩)
    · refine q8Rel_subtype ?_
      have := hq4.map (MulAut.conj c).toMonoidHom (MulAut.conj c).injective
      simpa [MulAut.conj_apply] using this
    · exact Subtype.ext (by rw [hβ]; exact hfixed x₄ hc4x)
    · exact Subtype.ext (by rw [hβ]; exact hfixed y₄ hc4y)
    · intro t ht
      have hnS : (r : Equiv.Perm (Fin 42)) ∉ S := not_mem_S_of_isConj hc not_mem_S_r₄
      apply hnS
      have hcomm : ((t : Equiv.Perm (Fin 42))⁻¹ * (r : Equiv.Perm (Fin 42))) ∈
          Subgroup.centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R := by
        refine ⟨Subgroup.mem_centralizer_iff.2 ?_, R.mul_mem (R.inv_mem (S_le_R t.2)) r.2⟩
        intro s hs
        have h3 := congrArg (fun α : MulAut ↥S => ((α ⟨s, hs⟩ : ↥S) : Equiv.Perm (Fin 42))) ht
        simp only [hβ, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h3
        have h4 : ((t : Equiv.Perm (Fin 42))⁻¹ * (r : Equiv.Perm (Fin 42))) * s *
            ((t : Equiv.Perm (Fin 42))⁻¹ * (r : Equiv.Perm (Fin 42)))⁻¹ = s := by
          calc ((t : Equiv.Perm (Fin 42))⁻¹ * (r : Equiv.Perm (Fin 42))) * s *
              ((t : Equiv.Perm (Fin 42))⁻¹ * (r : Equiv.Perm (Fin 42)))⁻¹
              = (t : Equiv.Perm (Fin 42))⁻¹ * ((r : Equiv.Perm (Fin 42)) * s *
                  (r : Equiv.Perm (Fin 42))⁻¹) * t := by group
            _ = (t : Equiv.Perm (Fin 42))⁻¹ * ((t : Equiv.Perm (Fin 42)) * s *
                  (t : Equiv.Perm (Fin 42))⁻¹) * t := by rw [h3]
            _ = s := by group
        exact (mul_inv_eq_iff_eq_mul.1 h4).symm
      rw [centralizer_S_inf_R, Subgroup.mem_bot] at hcomm
      have : (r : Equiv.Perm (Fin 42)) = t := by
        calc (r : Equiv.Perm (Fin 42)) = t * ((t : Equiv.Perm (Fin 42))⁻¹ * r) := by group
          _ = t := by rw [hcomm, mul_one]
      rw [this]
      exact t.2

end CFSG.EvenSporadicStandard.L34Q8
