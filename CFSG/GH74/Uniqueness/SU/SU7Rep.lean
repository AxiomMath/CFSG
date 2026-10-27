module

public import CFSG.GH74.Uniqueness.SU.SU7Gen3
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GH74.Uniqueness.SU.SU7Gen2

public section

namespace CFSG.GH74.Uniqueness.SU.SU7.Rep

open Subgroup

theorem rep_A5 {H : Type} [Group H] [Finite H]
    (hOH : ∀ N : Subgroup H, N.Normal → Odd (Nat.card N) → N = ⊥)
    {Sq Rq : Subgroup H} {X₀ : Set H}
    (hSqp : IsPGroup 2 Sq) (hSqidx : ¬ 2 ∣ Sq.index) (hRS : Rq ≤ Sq)
    (hRab : ∀ a ∈ Rq, ∀ b ∈ Rq, a * b = b * a) (hR16 : Nat.card Rq = 16)
    (hX₀R : X₀ ⊆ (Rq : Set H)) (hX₀5 : X₀.ncard = 5) (hX₀gen : Subgroup.closure X₀ = Rq)
    (hX₀cl : ∀ x ∈ X₀, ∀ h : H, h * x * h⁻¹ ∈ X₀)
    (hX₀conj : ∀ x ∈ X₀, ∀ y ∈ X₀, ∃ h : H, h * x * h⁻¹ = y)
    (hfaith : ∀ s ∈ Sq, (∀ r ∈ Rq, s * r = r * s) → s ∈ Rq)
    (hSq64 : Nat.card Sq = 64) (hsq : ∀ s ∈ Sq, s * s ∈ Rq) :
    ∃ ρ : H →* Equiv.Perm ↥X₀, (∀ (h : H) (x : ↥X₀), ((ρ h x : ↥X₀) : H) = h * x * h⁻¹) ∧
      ρ.ker = Rq ∧ Nonempty (ρ.range ≃* alternatingGroup (Fin 5)) := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let perm : H → Equiv.Perm ↥X₀ := fun h =>
    { toFun := fun x => ⟨h * x * h⁻¹, hX₀cl x x.2 h⟩
      invFun := fun x => ⟨h⁻¹ * x * h, by simpa using hX₀cl x x.2 h⁻¹⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc]) }
  let ρ : H →* Equiv.Perm ↥X₀ :=
    { toFun := perm
      map_one' := by ext x; simp [perm]
      map_mul' := fun h h' => by
        ext x
        simp only [perm, Equiv.coe_fn_mk, Equiv.Perm.coe_mul, Function.comp_apply, mul_inv_rev]
        group }
  have hρ : ∀ h : H, ∀ x : ↥X₀, ((ρ h x : ↥X₀) : H) = h * x * h⁻¹ := fun h x => rfl
  have hker_le : ∀ h : H, h ∈ ρ.ker → ∀ r ∈ Rq, h * r = r * h := by
    intro h hh r hr
    have hcent : h ∈ Subgroup.centralizer (X₀ : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have := congrArg (fun p : Equiv.Perm ↥X₀ => ((p ⟨x, hx⟩ : ↥X₀) : H)) (MonoidHom.mem_ker.1 hh)
      simp only [hρ, Equiv.Perm.coe_one, id_eq] at this
      calc x * h = (h * x * h⁻¹) * h := by rw [this]
        _ = h * x := by group
    rw [← Subgroup.centralizer_closure, hX₀gen] at hcent
    have := Subgroup.mem_centralizer_iff.1 hcent r hr
    exact this.symm
  have hRker : Rq ≤ ρ.ker := by
    intro r hr
    rw [MonoidHom.mem_ker]
    ext x
    rw [hρ]
    have := hRab r hr x (hX₀R x.2)
    simp only [Equiv.Perm.coe_one, id_eq]
    calc r * x * r⁻¹ = x * r * r⁻¹ := by rw [this]
      _ = x := by group
  have hSqD : Sq ⊓ ρ.ker = Rq := by
    apply le_antisymm
    · rintro s ⟨hsS, hsD⟩
      exact hfaith s hsS (hker_le s hsD)
    · exact le_inf hRS hRker
  have hSyl : ABGLocalTools.IsSylowOf 2 Sq ⊤ := by
    rw [ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, hSqp, by rw [Subgroup.relIndex_top_right]; exact hSqidx⟩
  have hD : ABGLocalTools.IsSylowOf 2 (Sq ⊓ ρ.ker) ρ.ker :=
    hSyl.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top])
  rw [hSqD] at hD
  have hD' := ABGLocalTools.isSylowOf_iff.1 hD
  have hker : ρ.ker = Rq := by
    apply le_antisymm _ hRker
    refine Gen.normal_le_of_central_sylow (fun h d hd => ?_) hRker (fun a ha d hd => ?_)
      (hSqp.to_le hRS) hD'.2.2 hOH
    · exact ρ.normal_ker.conj_mem d hd h
    · exact (hker_le d hd a ha).symm
  refine ⟨ρ, hρ, hker, ?_⟩
  have hΩ : Nat.card ↥X₀ = 5 := by rw [Nat.card_coe_set_eq]; exact hX₀5
  have hpre : MulAction.IsPretransitive ↥ρ.range ↥X₀ := ⟨fun x y => by
    obtain ⟨h, hh⟩ := hX₀conj x x.2 y y.2
    exact ⟨⟨ρ h, ⟨h, rfl⟩⟩, Subtype.ext (by
      show ((ρ h x : ↥X₀) : H) = y
      rw [hρ]; exact hh)⟩⟩
  have hρ'surj : Function.Surjective ρ.rangeRestrict := ρ.rangeRestrict_surjective
  have hker' : ρ.rangeRestrict.ker = Rq := by
    rw [MonoidHom.ker_rangeRestrict]; exact hker
  have hP4 : Nat.card (Sq.map ρ.rangeRestrict) = 4 := by
    have := Gen.card_map_mul_card_inf_ker ρ.rangeRestrict Sq
    rw [hker', inf_eq_right.2 hRS, hR16, hSq64] at this
    omega
  have hPidx : ¬ 2 ∣ (Sq.map ρ.rangeRestrict).index := fun hd =>
    hSqidx (hd.trans (Subgroup.index_map_dvd Sq hρ'surj))
  have hPe : ∀ g ∈ Sq.map ρ.rangeRestrict, g * g = 1 := by
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul]
    exact MonoidHom.mem_ker.1 (hker' ▸ hsq s hs)
  exact Gen.nonempty_mulEquiv_alternatingGroup_five hΩ hP4 hPidx hPe

end CFSG.GH74.Uniqueness.SU.SU7.Rep
