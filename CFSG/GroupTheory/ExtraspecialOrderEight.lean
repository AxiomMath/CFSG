module

public import CFSG.LargeExtraspecial.Timmesfeld.FStar
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutOrder8
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut
public import CFSG.CharacterTheory.Wreathed.QuaternionCharacteristic

public section

namespace CFSG

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem card_eight_cases {E : Subgroup G}
    (hE : LargeExtraspecial.Timmesfeld.IsExtraspecial2 E) (hcard : Nat.card E = 8) :
    Nonempty (↥E ≃* QuaternionGroup 2) ∨ Nonempty (↥E ≃* DihedralGroup 4) := by
  have hnab : ∃ a b : ↥E, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have hcommE : IsMulCommutative ↥E := IsMulCommutative.of_comm h
    have hbot : ⁅E, E⁆ = ⊥ := Subgroup.commutator_self_eq_bot_iff.mpr hcommE
    have h2 : Nat.card (⊥ : Subgroup G) = 2 := by
      rw [← hbot]
      exact hE.2.2
    rw [Subgroup.card_bot] at h2
    omega
  rcases OddStandard.SmallF3.HarrisU33.Outside.order8_nonabelian (G := ↥E) hcard hnab with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem extraspecial_eight_automorphism_three {E : Subgroup G}
    (hE : LargeExtraspecial.Timmesfeld.IsExtraspecial2 E) (hcard : Nat.card E = 8)
    (hne : ¬ Nonempty (↥E ≃* QuaternionGroup 2)) :
    ¬ ∃ φ : MulAut ↥E, orderOf φ = 3 := by
  rintro ⟨φ, hφ⟩
  have he : Nonempty (↥E ≃* DihedralGroup 4) := by
    rcases card_eight_cases hE hcard with h | h
    · exact absurd h hne
    · exact h
  obtain ⟨e⟩ := he
  have hAut : IsPGroup 2 (MulAut ↥E) :=
    (GorensteinWalter.dihedral_mulAut_is_twoGroup (m := 2) le_rfl).of_equiv
      (MulAut.congr e).symm
  obtain ⟨k, hk⟩ := hAut.exists_orderOf_dvd_pow φ
  rw [hφ] at hk
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hk) (by norm_num)

theorem quaternion_orderOf_eq_four_of_not_mem_center (q : QuaternionGroup 2)
    (hq : q ∉ Subgroup.center (QuaternionGroup 2)) : orderOf q = 4 := by
  have ha2_center :
      (QuaternionGroup.a 2 : QuaternionGroup 2) ∈ Subgroup.center (QuaternionGroup 2) := by
    rw [Subgroup.mem_center_iff]
    decide
  exact Wreathed.quaternionEight_noncentral_order q
    ⟨fun h => hq (h ▸ Subgroup.one_mem _), fun h => hq (h ▸ ha2_center)⟩

theorem centralizer_is_quaternion_of_three_action {H : Type} [Group H] [Finite H]
    {E : Subgroup H} (hE : LargeExtraspecial.Timmesfeld.IsExtraspecial2 E)
    (hcard : Nat.card E = 8) {σ : H} (hσ : orderOf σ = 3)
    (hN : σ ∈ Subgroup.normalizer (E : Set H))
    (hact : ∃ e ∈ E, σ * e * σ⁻¹ ≠ e) :
    Nonempty (↥E ≃* QuaternionGroup 2) ∧
      ∀ r : ↥E, r ∉ Subgroup.center ↥E → orderOf r = 4 := by
  classical
  let x : ↥(Subgroup.normalizer (E : Set H)) := ⟨σ, hN⟩
  let c : MulAut ↥E := E.normalizerMonoidHom x
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    simpa [x] using hσ3
  have hc3 : c ^ 3 = 1 := by
    change (E.normalizerMonoidHom x) ^ 3 = 1
    rw [← map_pow, hx3, map_one]
  have hcne : c ≠ 1 := by
    intro hc1
    obtain ⟨e, he, hne⟩ := hact
    apply hne
    have h : c ⟨e, he⟩ = ⟨e, he⟩ := by rw [hc1]; rfl
    have h' := congrArg Subtype.val h
    simpa [c, Subgroup.normalizerMonoidHom_apply_apply_coe] using h'
  have hcord : orderOf c = 3 := by
    have hdvd : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hcne
    · exact h3
  have hQ8 : Nonempty (↥E ≃* QuaternionGroup 2) := by
    by_contra hneQ
    exact (extraspecial_eight_automorphism_three hE hcard hneQ) ⟨c, hcord⟩
  refine ⟨hQ8, ?_⟩
  obtain ⟨eQ⟩ := hQ8
  intro r hr
  have hnotmem : eQ r ∉ Subgroup.center (QuaternionGroup 2) := by
    intro hmem
    apply hr
    have hmap : Subgroup.map eQ.toMonoidHom (Subgroup.center ↥E) =
        Subgroup.center (QuaternionGroup 2) := by
      simp
    have hmem' : eQ r ∈ Subgroup.map eQ.toMonoidHom (Subgroup.center ↥E) := by
      rw [hmap]
      exact hmem
    obtain ⟨z, hz, hze⟩ := hmem'
    rw [← eQ.injective hze]
    exact hz
  have h4 : orderOf (eQ r) = 4 :=
    quaternion_orderOf_eq_four_of_not_mem_center (eQ r) hnotmem
  rwa [MulEquiv.orderOf_eq] at h4

end CFSG
