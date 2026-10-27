module

public import CFSG.GH74.Generic.S45.LSporCommon
public import CFSG.GH74.Generic.S45.LLift

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.GH74.GLS Subgroup

theorem spor_j1_false {K : Type} [Group K] [Finite K] {y : MulAut K}
    {L : Subgroup K} (hyp : Hyp1310 K y L)
    (e : K ⧸ Subgroup.center K ≃* CFSG.Open.walterJ1) : False := by
  have hb2 := hyp.2.2.2.2.2.2.2
  obtain ⟨hKp, -, hy, hLfix, -, -, -, -, q, hq5, hqodd, hqcard, hmodel⟩ := hyp.data
  let π : K →* CFSG.Open.walterJ1 := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hπsurj : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπker : π.ker = Subgroup.center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hker : π.ker = ⊥ := noCentralCover_walterJ1 K hKp π hπsurj hπker.le
  have hZ : Subgroup.center K = ⊥ := hπker ▸ hker
  have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 hker
  let φ : K ≃* CFSG.Open.walterJ1 := MulEquiv.ofBijective π ⟨hinj, hπsurj⟩
  obtain ⟨g, hg⟩ := CFSG.Walter.J1Props.J3_aut (φ.symm.trans (y.trans φ))
  have hyk : ∀ x : K, y x = φ.symm g * x * (φ.symm g)⁻¹ := by
    intro x
    have h1 := congrArg (fun a : MulAut CFSG.Open.walterJ1 => a (φ x)) hg
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
    apply φ.injective
    rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hkorder : orderOf g = 2 := by
    have hy2 : y * y = 1 := by
      have := pow_orderOf_eq_one y
      rw [hy, pow_two] at this
      exact this
    have hg2 : g * g = 1 := by
      have hc : (φ.symm g * φ.symm g) ∈ Subgroup.center K := by
        rw [Subgroup.mem_center_iff]
        intro x
        have h1 := congrArg (fun a : MulAut K => a x) hy2
        simp only [MulAut.mul_apply, MulAut.one_apply, hyk] at h1
        have h2 : φ.symm g * (φ.symm g * x * (φ.symm g)⁻¹) * (φ.symm g)⁻¹ = x := h1
        calc x * (φ.symm g * φ.symm g) = (φ.symm g * (φ.symm g * x * (φ.symm g)⁻¹) *
              (φ.symm g)⁻¹) * (φ.symm g * φ.symm g) := by rw [h2]
          _ = φ.symm g * φ.symm g * x := by group
      rw [hZ, Subgroup.mem_bot] at hc
      have := congrArg φ hc
      rwa [map_mul, MulEquiv.apply_symm_apply, map_one] at this
    have hg1 : g ≠ 1 := by
      rintro rfl
      have hyone : y = 1 := by
        refine MulEquiv.ext fun x => ?_
        rw [hyk x, map_one, inv_one]
        simp
      rw [hyone, orderOf_one] at hy
      omega
    exact orderOf_eq_prime (by rw [pow_two]; exact hg2) hg1
  have hcard : Nat.card (Subgroup.centralizer ({g} : Set CFSG.Open.walterJ1)) = 120 :=
    CFSG.Walter.J1Props.card_centralizer_of_orderOf_eq_two hkorder
  have hLle : L.map φ.toMonoidHom ≤ Subgroup.centralizer ({g} : Set CFSG.Open.walterJ1) := by
    rintro _ ⟨l, hl, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hLfix l hl
    rw [hyk l] at h1
    show φ l * g = g * φ l
    have h2 : φ (φ.symm g * l * (φ.symm g)⁻¹) = φ l := congrArg φ h1
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h2
    calc φ l * g = (g * φ l * g⁻¹) * g := by rw [h2]
      _ = g * φ l := by group
  have hdvd : Nat.card ↥L ∣ 120 := by
    have h1 := Subgroup.card_dvd_of_le hLle
    rw [hcard, Subgroup.card_map_of_injective φ.injective] at h1
    exact h1
  have hq : q = 5 := eq_five_of_card_dvd_120 hdvd hq5 hqodd hqcard
  have hL5 : HasL2Model ↥L (fun q => q = 5) := hmodel _ hq
  exact hb2 hL5 ⟨φ.trans CFSG.Walter.walterJ1EquivNative⟩

end CFSG.GH74.Generic.S45
