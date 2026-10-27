module

public import CFSG.LargeExtraspecial.S45QOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4C1

open Module QuadraticMap CFSG.LargeExtraspecial
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_conj eichler_mul eichler_zero_right
  eichler_add_smul_self eichler_mem_orthogonalGroup)

section Siegel

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem pointRadical_conj_le (hQ : Q.polarBilin.Nondegenerate)
    {M : Subgroup (V ≃ₗ[ZMod 2] V)} (hMO : M ≤ orthogonalGroup Q) {a : V} (ha0 : a ≠ 0)
    (haq : Q a = 0) (hA : pointRadical Q a ≤ M) {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ M) :
    pointRadical Q (g a) ≤ M := by
  intro t ht
  have hga0 : g a ≠ 0 := fun h => ha0 (g.injective (by rw [h, map_zero]))
  have hgaq : Q (g a) = 0 := by
    rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (hMO hg)]
    exact haq
  obtain ⟨u, hu, rfl⟩ := (mem_pointRadical_iff hQ hga0 hgaq).mp ht
  have hu' : polar Q a (g.symm u) = 0 := by
    have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hMO hg) a (g.symm u)
    rw [LinearEquiv.apply_symm_apply] at h1
    rw [← h1, hu]
  have h2 : eichler Q a (g.symm u) ∈ M := hA (eichler_mem_pointRadical haq hu')
  have h3 := eichler_conj (hMO hg) a (g.symm u)
  rw [LinearEquiv.apply_symm_apply] at h3
  rw [← h3]
  exact M.mul_mem (M.mul_mem hg h2) (M.inv_mem hg)

theorem exists_singular_perp_pair (hQ : Q.polarBilin.Nondegenerate) (hV : finrank (ZMod 2) V = 8)
    (x b : V) : ∃ w : V, w ≠ 0 ∧ Q w = 0 ∧ polar Q x w = 0 ∧ polar Q b w = 0 := by
  classical
  set W := LinearMap.BilinForm.orthogonal Q.polarBilin (Submodule.span (ZMod 2) {x, b}) with hW
  have h1 : finrank (ZMod 2) W = finrank (ZMod 2) V -
      finrank (ZMod 2) (Submodule.span (ZMod 2) {x, b}) :=
    LinearMap.BilinForm.finrank_orthogonal hQ (Submodule.span (ZMod 2) {x, b})
  have h2 : finrank (ZMod 2) (Submodule.span (ZMod 2) {x, b}) ≤ 2 := by
    have := finrank_span_finset_le_card (R := ZMod 2) ({x, b} : Finset V)
    rw [Finset.coe_insert, Finset.coe_singleton] at this
    exact this.trans ((Finset.card_insert_le _ _).trans (by simp))
  have h3 : 3 ≤ finrank (ZMod 2) W := by omega
  obtain ⟨w, hwW, hw0, hwq⟩ := CFSG.LargeExtraspecial.S45Q.exists_singular_mem (Q := Q) h3
  rw [hW, OrthoF2.mem_orthogonal_span_pair_iff] at hwW
  exact ⟨w, hw0, hwq, hwW.1, hwW.2⟩

theorem eichler_apply_pair {x b w : V} (hbq : Q b = 0) (hbw : polar Q b w = 0)
    (hxb : polar Q x b = 1) (hxw : polar Q x w = 0) (hwq : Q w = 0) :
    eichler Q b w x = x + w := by
  rw [eichler_apply_zmod2 hbq hbw, hxb, hxw, hwq]
  simp

open CFSG.RankThree.Literature.FSmith (zmod2_eq_zero_or_eq_one zmod2_eq_one_of_ne_zero)
open CFSG.RankThree.OrthogonalInvolutions (polar_self_eq_zero)

theorem card_stabilizer_pointRadical (hQ : Q.polarBilin.Nondegenerate)
    (hV : finrank (ZMod 2) V = 8) {x c : V} (hc0 : c ≠ 0) (hcq : Q c = 0)
    (hxc : polar Q x c = 0) (hx0 : x ≠ 0) (hxc' : x ≠ c) :
    Nat.card (MulAction.stabilizer (pointRadical Q c) x) = 2 ^ 5 := by
  have horb : MulAction.orbit (pointRadical Q c) x = {x, x + c} := by
    ext y
    simp only [MulAction.mem_orbit_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨t, ht⟩, rfl⟩
      obtain ⟨u, hu, rfl, -⟩ := pointRadical_apply_of_polar_eq_zero hQ hc0 hcq ht
      have e1 : (⟨eichler Q c u, ht⟩ : pointRadical Q c) • x = eichler Q c u x := rfl
      rw [e1, eichler_apply_zmod2 hcq hu, hxc]
      rcases zmod2_eq_zero_or_eq_one (polar Q x u) with h | h
      · left
        simp [h]
      · right
        simp [h]
    · rintro (rfl | rfl)
      · exact ⟨1, one_smul _ _⟩
      · obtain ⟨u, hu, hxu⟩ : ∃ u, polar Q c u = 0 ∧ polar Q x u = 1 := by
          by_contra hcon
          push Not at hcon
          have hx_mem : x ∈ LinearMap.BilinForm.orthogonal Q.polarBilin
              (LinearMap.BilinForm.orthogonal Q.polarBilin ((ZMod 2) ∙ c)) := by
            rw [LinearMap.BilinForm.mem_orthogonal_iff]
            intro u hu
            have hu' := OrthoF2.mem_orthogonal_span_singleton_iff.mp hu
            have h5 : polar Q x u = 0 := by
              by_contra h6
              exact hcon u hu' (zmod2_eq_one_of_ne_zero h6)
            rw [polarBilin_apply_apply, polar_comm, h5]
          rw [LinearMap.BilinForm.orthogonal_orthogonal hQ
            (QuadraticMap.isSymm_polarBilin Q).isRefl] at hx_mem
          obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.mp hx_mem
          rcases zmod2_eq_zero_or_eq_one α with rfl | rfl
          · exact hx0 (by rw [← hα, zero_smul])
          · exact hxc' (by rw [← hα, one_smul])
        refine ⟨⟨eichler Q c u, eichler_mem_pointRadical hcq hu⟩, ?_⟩
        show eichler Q c u x = x + c
        rw [eichler_apply_zmod2 hcq hu, hxc, hxu]
        simp
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer (pointRadical Q c) x)
  rw [MulAction.index_stabilizer, horb, card_pointRadical hQ hc0 hcq, hV] at h1
  have h2 : ({x, x + c} : Set V).ncard = 2 := by
    rw [Set.ncard_pair]
    intro h
    exact hc0 (by simpa using h)
  rw [h2] at h1
  have h3 : (2 : ℕ) ^ (8 - 2) = 2 ^ 5 * 2 := by norm_num
  rw [h3] at h1
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1

theorem eq_one_or_eichler_of_mem_pointRadical (hQ : Q.polarBilin.Nondegenerate) {x c : V}
    (hx0 : x ≠ 0) (hxq : Q x = 0) (hxc' : x ≠ c) {t : V ≃ₗ[ZMod 2] V}
    (htx : t ∈ pointRadical Q x) (htc : t ∈ pointRadical Q c) :
    t = 1 ∨ t = eichler Q x c := by
  obtain ⟨u, hu, rfl, happ⟩ := pointRadical_apply_of_polar_eq_zero hQ hx0 hxq htx
  have hu' : u ∈ Submodule.span (ZMod 2) {x, c} := by
    rw [← LinearMap.BilinForm.orthogonal_orthogonal hQ (QuadraticMap.isSymm_polarBilin Q).isRefl
      (Submodule.span (ZMod 2) {x, c}), LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    rw [OrthoF2.mem_orthogonal_span_pair_iff] at hy
    have h3 := htc.2.2.1 y hy.2
    rw [happ y hy.1, add_sub_cancel_left] at h3
    rw [polarBilin_apply_apply]
    by_contra h4
    have h5 : polar Q y u = 1 := zmod2_eq_one_of_ne_zero h4
    rw [h5, one_smul] at h3
    obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.mp h3
    rcases zmod2_eq_zero_or_eq_one α with rfl | rfl
    · exact hx0 (by rw [← hα, zero_smul])
    · exact hxc' (by rw [← hα, one_smul])
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hu'
  have h6 : eichler Q x (α • x + β • c) = eichler Q x (β • c) := by
    rw [add_comm, eichler_add_smul_self hxq]
  rw [h6]
  rcases zmod2_eq_zero_or_eq_one β with rfl | rfl
  · left
    rw [zero_smul, eichler_zero_right]
  · right
    rw [one_smul]

theorem two_pow_ten_dvd_card (hQ : Q.polarBilin.Nondegenerate) (hV : finrank (ZMod 2) V = 8)
    {M : Subgroup (V ≃ₗ[ZMod 2] V)} (hMO : M ≤ orthogonalGroup Q) {x : V} (hx0 : x ≠ 0)
    (hxq : Q x = 0) (hA : pointRadical Q x ≤ M) (horb : ∃ m ∈ M, polar Q x (m x) ≠ 0) :
    2 ^ 10 ∣ Nat.card M := by
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  haveI : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V))
      (fun _ _ h => LinearEquiv.ext (congrFun h))
  obtain ⟨m₀, hm₀, hpol⟩ := horb
  have hxb : polar Q x (m₀ x) = 1 := zmod2_eq_one_of_ne_zero hpol
  set b := m₀ x with hb
  have hb0 : b ≠ 0 := fun h => hx0 (m₀.injective (by rw [← hb, h, map_zero]))
  have hbq : Q b = 0 := by
    rw [hb, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (hMO hm₀)]
    exact hxq
  have hB : pointRadical Q b ≤ M := pointRadical_conj_le hQ hMO hx0 hxq hA hm₀
  obtain ⟨w, hw0, hwq, hxw, hbw'⟩ := exists_singular_perp_pair hQ hV x b
  have hbw : polar Q b w = 0 := hbw'
  have hrB : eichler Q b w ∈ pointRadical Q b := eichler_mem_pointRadical hbq hbw
  have hrM : eichler Q b w ∈ M := hB hrB
  set c := eichler Q b w x with hc
  have hcx : c = x + w := eichler_apply_pair hbq hbw hxb hxw hwq
  have hxne : x ≠ w := by
    intro h
    rw [← h] at hbw
    rw [polar_comm, hbw] at hxb
    exact zero_ne_one hxb
  have hc0 : c ≠ 0 := by
    rw [hcx]
    intro h
    exact hxne (by simpa [eq_comm, add_eq_zero_iff_eq_neg, ZModModule.neg_eq_self] using h)
  have hcq : Q c = 0 := by
    rw [hc, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (eichler_mem_orthogonalGroup Q b w)]
    exact hxq
  have hxc : polar Q x c = 0 := by
    rw [hcx, polar_add_right, polar_self_eq_zero Q x, hxw, add_zero]
  have hxc' : x ≠ c := by
    rw [hcx]
    intro h
    exact hw0 (by simpa using h)
  have hC : pointRadical Q c ≤ M := pointRadical_conj_le hQ hMO hx0 hxq hA hrM
  set A : Subgroup (V ≃ₗ[ZMod 2] V) := pointRadical Q x with hAdef
  set Nc : Subgroup (V ≃ₗ[ZMod 2] V) := pointRadical Q c with hNc
  set Bs : Subgroup Nc := MulAction.stabilizer Nc x with hBs
  set B : Subgroup (V ≃ₗ[ZMod 2] V) := Bs.map Nc.subtype with hBdef
  have hBcard : Nat.card B = 2 ^ 5 :=
    (Subgroup.card_map_of_injective Nc.subtype_injective).trans
      (card_stabilizer_pointRadical hQ hV hc0 hcq hxc hx0 hxc')
  have hBle : B ≤ Nc := Subgroup.map_subtype_le _
  have hBfix : ∀ y ∈ B, y x = x := by
    rintro _ ⟨⟨t, ht⟩, hts, rfl⟩
    exact hts
  set P : Subgroup (V ≃ₗ[ZMod 2] V) := M ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) x with hP
  have hAfix : ∀ t ∈ A, t x = x := fun t ht => ((mem_pointRadical).mp ht).2.1
  have hAP : A ≤ P := fun t ht => ⟨hA ht, hAfix t ht⟩
  have hBP : B ≤ P := fun t ht => ⟨(hBle.trans hC) ht, hBfix t ht⟩
  have hAnorm : ∀ p ∈ P, ∀ t ∈ A, p * t * p⁻¹ ∈ A := by
    intro p hp t ht
    obtain ⟨u, hu, rfl⟩ := (mem_pointRadical_iff hQ hx0 hxq).mp ht
    have hpO : p ∈ orthogonalGroup Q := hMO hp.1
    have hpx : p x = x := hp.2
    rw [eichler_conj hpO, hpx]
    refine eichler_mem_pointRadical hxq ?_
    have h5 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hpO x u
    rw [hpx] at h5
    rw [h5, hu]
  set A' : Subgroup P := A.subgroupOf P with hA'
  haveI : A'.Normal :=
    ⟨fun n hn g => by
      rw [hA', Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hAnorm g g.2 n hn⟩
  set B' : Subgroup P := B.subgroupOf P with hB'
  set ψ : B' →* P ⧸ A' := (QuotientGroup.mk' A').comp B'.subtype with hψ
  have hA'card : Nat.card A' = 2 ^ 6 := by
    rw [hA', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv, hAdef,
      card_pointRadical hQ hx0 hxq, hV]
  have hB'card : Nat.card B' = 2 ^ 5 := by
    rw [hB', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP).toEquiv, hBcard]
  have hker : Nat.card ψ.ker ≤ 2 := by
    let φ : ψ.ker → (V ≃ₗ[ZMod 2] V) := fun k => (((k : B') : P) : V ≃ₗ[ZMod 2] V)
    have hφ : Function.Injective φ := fun k₁ k₂ h => Subtype.ext (Subtype.ext (Subtype.ext h))
    have hrange : Set.range φ ⊆ {1, eichler Q x c} := by
      rintro _ ⟨k, rfl⟩
      have hk : ψ k = 1 := k.2
      have hkA : (((k : B') : P) : V ≃ₗ[ZMod 2] V) ∈ A := by
        have h7 : ((k : B') : P) ∈ A' := (QuotientGroup.eq_one_iff _).mp hk
        exact Subgroup.mem_subgroupOf.mp h7
      have hkN : (((k : B') : P) : V ≃ₗ[ZMod 2] V) ∈ Nc :=
        hBle (Subgroup.mem_subgroupOf.mp (k : B').2)
      rcases eq_one_or_eichler_of_mem_pointRadical hQ hx0 hxq hxc' hkA hkN with h | h
      · exact Or.inl h
      · exact Or.inr h
    calc Nat.card ψ.ker = Nat.card (Set.range φ) := (Nat.card_range_of_injective hφ).symm
      _ = (Set.range φ).ncard := Nat.card_coe_set_eq _
      _ ≤ ({1, eichler Q x c} : Set (V ≃ₗ[ZMod 2] V)).ncard :=
          Set.ncard_le_ncard hrange (Set.toFinite _)
      _ ≤ 2 := by
          refine (Set.ncard_insert_le _ _).trans ?_
          rw [Set.ncard_singleton]
  have c1 := Subgroup.card_ker_mul_card_range ψ
  have hkpos : 0 < Nat.card ψ.ker := Nat.card_pos
  have h16 : 16 ∣ Nat.card ψ.range := by
    rw [hB'card] at c1
    rcases (by omega : Nat.card ψ.ker = 1 ∨ Nat.card ψ.ker = 2) with h | h
    · rw [h] at c1
      exact ⟨2, by omega⟩
    · rw [h] at c1
      exact ⟨1, by omega⟩
  have h2 : Nat.card ψ.range ∣ Nat.card (P ⧸ A') := Subgroup.card_subgroup_dvd_card _
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup A'
  obtain ⟨k, hk⟩ := h16.trans h2
  have h4 : 2 ^ 10 ∣ Nat.card P := by
    rw [h3, hA'card, hk]
    exact ⟨k, by ring⟩
  exact h4.trans (Subgroup.card_dvd_of_le inf_le_left)

end Siegel

end CFSG.GF2Type.Smith1979.W4C1
