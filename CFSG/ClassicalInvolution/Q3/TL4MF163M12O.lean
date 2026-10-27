module

public import CFSG.ClassicalInvolution.Q3.TL4MF163M12
public import CFSG.ClassicalInvolution.Q3.TL4MF163L2
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverExternalOuter

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.M12Cover CFSG.ComponentClassification.OuterAutomorphisms

namespace MF163

theorem orderOf_ne_four_prod
    (p : Multiplicative (ZMod 2) × alternatingGroup (Fin 5)) : orderOf p ≠ 4 := by
  intro h4
  have hp4 : p ^ 4 = 1 := h4 ▸ pow_orderOf_eq_one p
  have hp2 : p ^ 2 ≠ 1 := fun h => by
    have := orderOf_dvd_of_pow_eq_one h
    rw [h4] at this
    norm_num at this
  have h2 : ∀ ε : Multiplicative (ZMod 2), ε ^ 2 = 1 := by decide
  obtain ⟨ε, a⟩ := p
  have hε : ε ^ 2 = 1 := h2 ε
  have ha4 : a ^ 4 = 1 := by simpa using congrArg Prod.snd hp4
  have ha2 : a ^ 2 ≠ 1 := fun ha => hp2 (by ext <;> simp [hε, ha])
  refine ha2 (Certificates.certificate2 a (a ^ 2) (fun h => ha2 (by rw [h, one_pow]))
    (by rwa [← sq]) (by rw [← pow_add]; exact ha4) (by rw [← pow_succ, ← pow_succ']))

theorem not_fix_of_outer
    {α : MulAut NativeSporadic.M12} (h2 : orderOf α = 2) (hα : α ∉ inner NativeSporadic.M12)
    {w : NativeSporadic.M12} (hw : orderOf w = 4) : α w ≠ w := by
  intro hfix
  obtain ⟨g, rfl⟩ := exists_conj_beta_of_outer h2 hα
  have hmem : w ∈ fixSub (MulAut.conj g * beta * (MulAut.conj g)⁻¹) := mem_fixSub.2 hfix
  rw [fixSub_conj_beta] at hmem
  obtain ⟨y, hy, hyw⟩ := hmem
  have hy4 : orderOf y = 4 := by
    rw [← hw, ← hyw, MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
  apply orderOf_ne_four_prod (fixedAltEquiv ⟨y, hy⟩)
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy4]

theorem eq_one_or_conj_of_quat_m12
    (ι : QuaternionGroup 2 →* NativeSporadic.M12)
    (hι : Function.Injective ι) (β : MulAut NativeSporadic.M12) (hβ2 : β * β = 1)
    (hβι : ∀ g, β (ι g) = ι g) : β = 1 ∨ β = MulAut.conj (ι (QuaternionGroup.a 2)) := by
  by_cases hin : β ∈ inner NativeSporadic.M12
  · obtain ⟨m, rfl⟩ := hin
    have hcomm : ∀ q, m * ι q = ι q * m := fun q => by
      have h := hβι q
      rw [MulAut.conj_apply] at h
      calc m * ι q = m * ι q * m⁻¹ * m := by group
        _ = ι q * m := by rw [h]
    have hm2 : m * m = 1 := by
      have h1 : MulAut.conj (m * m) = 1 := by rw [map_mul]; exact hβ2
      have h2 : m * m ∈ Subgroup.center NativeSporadic.M12 := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h3 := congrArg (fun φ : MulAut NativeSporadic.M12 => φ g) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at h3
        calc g * (m * m) = m * m * g * (m * m)⁻¹ * (m * m) := by rw [h3]
          _ = m * m * g := by group
      rw [m12_center_eq_bot', Subgroup.mem_bot] at h2
      exact h2
    rcases eq_of_comm_quat ι hι hcomm (Or.inl hm2) with rfl | h
    · exact Or.inl (map_one _)
    · exact Or.inr (by rw [h])
  · exfalso
    have hβ1 : β ≠ 1 := fun h => hin (h ▸ (inner NativeSporadic.M12).one_mem)
    have hord : orderOf β = 2 := orderOf_eq_prime (by rw [sq]; exact hβ2) hβ1
    exact not_fix_of_outer hord hin
      (by rw [orderOf_injective ι hι, QuaternionGroup.orderOf_xa]) (hβι (QuaternionGroup.xa 0))

end MF163

theorem model163M12_proved :
    Model163M12 := by
  intro X _ _ R S z hm hX β hβ2 hβK
  obtain ⟨e⟩ := hX
  obtain ⟨ι, hι, hιK, hιz⟩ := MF163.exists_quat_of_member hm
  let e' : X ≃* NativeSporadic.M12 := e
  have hfix : ∀ g, MulAut.congr e' β ((e'.toMonoidHom.comp ι) g) = (e'.toMonoidHom.comp ι) g :=
    fun g => by simp [MulAut.congr_apply, hβK _ (hιK g)]
  rcases MF163.eq_one_or_conj_of_quat_m12 (e'.toMonoidHom.comp ι) (e'.injective.comp hι)
    (MulAut.congr e' β) (by rw [← map_mul, hβ2, map_one]) hfix with h | h
  · exact Or.inl ((MulAut.congr e').injective (h.trans (map_one _).symm))
  · right
    apply (MulAut.congr e').injective
    rw [h, congr_conj]
    simp [hιz]

end CFSG.ClassicalInvolution.Q3.TL4
