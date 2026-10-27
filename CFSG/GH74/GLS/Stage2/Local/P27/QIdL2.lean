module

public import CFSG.GH74.GLS.IVK.L2.ExistNotation
public import CFSG.GH74.GLS.IVK.L2.Lemma12hc
public import CFSG.GH74.GLS.IVK.L2.Fixed14a
public import CFSG.GH74.GLS.IVK.L2.Lemma13
public import CFSG.GH74.GLS.IVK.Lifted.SolvAut
public import CFSG.CharacterTheory.Burnside
public import CFSG.Assembly.GL83LieDefs
public import CFSG.GH74.GLS.IVK.Lifted.OuterStruct

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.QId

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Lifted CFSG.GorensteinWalter
open scoped commutatorElement

section Aux

variable {K : Type} [Group K]

theorem mem_fixedSubgroup_iff' (φ : MulAut K) (g : K) : g ∈ fixedSubgroup K φ ↔ φ g = g :=
  Iff.rfl

theorem fixedSubgroup_equiv_of_conj (c f : MulAut K) :
    Nonempty (↥(fixedSubgroup K (c⁻¹ * f * c)) ≃* ↥(fixedSubgroup K f)) := by
  have hmap : (fixedSubgroup K (c⁻¹ * f * c)).map c.toMonoidHom = fixedSubgroup K f := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hg' : (c⁻¹ * f * c) g = g := hg
      have h1 : c⁻¹ (f (c g)) = g := hg'
      have h2 : f (c g) = c g := by
        have := congrArg c h1
        simpa using this
      exact h2
    · intro hy
      refine ⟨c⁻¹ y, ?_, by simp⟩
      have hy' : f y = y := hy
      show (c⁻¹ * f * c) (c⁻¹ y) = c⁻¹ y
      simp [hy']
  exact ⟨(Subgroup.equivMapOfInjective _ c.toMonoidHom c.injective).trans
    (MulEquiv.subgroupCongr hmap)⟩

theorem commutator_eq_map_commutator (C : Subgroup K) :
    ⁅C, C⁆ = (commutator ↥C).map C.subtype := by
  have h1 := Subgroup.map_commutator (⊤ : Subgroup ↥C) ⊤ C.subtype
  have h2 : (⊤ : Subgroup ↥C).map C.subtype = C := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [h2] at h1
  exact h1.symm

end Aux

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem l2_fixed_dichotomy (hF : L2Field F) (e : K ≃* L2 F) (α : MulAut K) (hα : α * α = 1)
    (hne : α ≠ 1) :
    Group.IsSolvable ↥(fixedSubgroup K α) ∨
      ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ ^ 2 = Nat.card F ∧
        Odd (Nat.card F₀) ∧ 3 < Nat.card F₀ ∧
        Nonempty (↥⁅fixedSubgroup K α, fixedSubgroup K α⁆ ≃* L2 F₀) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N⟩ := exists_notation hF e
  have hD : (innDiagSub e).Normal := innDiagSub_normal e
  have hFD := innDiagSub_inf_fieldAutSub e
  have hDF := innDiagSub_sup_fieldAutSub e
  have hαord : orderOf α = 2 := orderOf_eq_prime (by rw [pow_two]; exact hα) hne
  obtain ⟨d, hd, f, hf, hdf⟩ := Subgroup.mem_sup_of_normal_left.1
    (show α ∈ innDiagSub e ⊔ fieldAutSub e by rw [hDF]; exact Subgroup.mem_top _)
  have hff : f * f = 1 := by
    have h1 : f * f ∈ innDiagSub e := by
      have e1 : f * f = d⁻¹ * (α * α) * (f⁻¹ * d⁻¹ * f) := by rw [← hdf]; group
      rw [e1, hα, mul_one]
      have := hD.conj_mem d⁻¹ (inv_mem hd) f⁻¹
      simp only [inv_inv] at this
      exact mul_mem (inv_mem hd) this
    have h2 : f * f ∈ innDiagSub e ⊓ fieldAutSub e := ⟨h1, mul_mem hf hf⟩
    rw [hFD] at h2
    exact h2
  by_cases hf1 : f = 1
  ·
    left
    have hαD : α ∈ innDiagSub e := by rw [← hdf, hf1, mul_one]; exact hd
    obtain ⟨ε, hε1, hε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (Nat.card F : ℤ) ≡ ε [ZMOD 4] := by
      have hodd := hF.1
      have h4 : Nat.card F % 4 = 1 ∨ Nat.card F % 4 = 3 := by
        obtain ⟨m, hm⟩ := hodd
        omega
      rcases h4 with h4 | h4
      · exact ⟨1, Or.inl rfl, by unfold Int.ModEq; omega⟩
      · exact ⟨-1, Or.inr rfl, by unfold Int.ModEq; omega⟩
    by_cases hαI : α ∈ innAut K
    · obtain ⟨u, hu⟩ := hαI
      have huu : u * u = 1 := by
        have h1 : MulAut.conj (u * u) = MulAut.conj (1 : K) := by
          rw [map_mul, hu, hα, map_one]
        exact conj_injective_of_L2 e h1
      have hu1 : u ≠ 1 := by
        intro h
        apply hne
        rw [← hu, h, map_one]
      have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact huu) hu1
      have hdd : ∃ dd : ℕ, (dd : ℤ) = Nat.card F - ε := by
        refine ⟨(Nat.card F - ε).toNat, ?_⟩
        have : (0 : ℤ) ≤ Nat.card F - ε := by
          have := hF.2
          rcases hε1 with rfl | rfl <;> omega
        exact Int.toNat_of_nonneg this
      obtain ⟨dd, hdd⟩ := hdd
      have hdih := (ivk_1_3a F hF K e ε hε1 hε dd hdd u hu2).2.1
      have hfix : fixedSubgroup K α = centralizer ({u} : Set K) := by
        ext g
        rw [mem_fixedSubgroup_iff', Subgroup.mem_centralizer_singleton_iff, ← hu]
        simp only [MulAut.conj_apply]
        constructor
        · intro h
          calc g * u = (u * g * u⁻¹) * u := by rw [h]
            _ = u * g := by group
        · intro h
          calc u * g * u⁻¹ = (g * u) * u⁻¹ := by rw [h]
            _ = g := by group
      rw [hfix]
      exact isSolvable_of_isDihedralOrder hdih
    · have hdd : ∃ dd : ℕ, (dd : ℤ) = Nat.card F + ε := by
        refine ⟨(Nat.card F + ε).toNat, ?_⟩
        have : (0 : ℤ) ≤ Nat.card F + ε := by
          have := hF.2
          rcases hε1 with rfl | rfl <;> omega
        exact Int.toNat_of_nonneg this
      obtain ⟨dd, hdd⟩ := hdd
      have hdih := (ivk_1_3b_dihedral hF e ε hε1 hε dd hdd α hαD hαI hαord).2
      exact isSolvable_of_isDihedralOrder hdih
  ·
    have hford : orderOf f = 2 := orderOf_eq_prime (by rw [pow_two]; exact hff) hf1
    have hfT : f ∈ (N.T : Subgroup (MulAut K)) := by
      have hp : IsPGroup 2 ↥(Subgroup.zpowers f) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hford]; norm_num)
      have hs := hp.inf_normalizer_sylow N.T
      have hmem : f ∈ Subgroup.zpowers f ⊓ Subgroup.normalizer (N.T : Set (MulAut K)) :=
        ⟨Subgroup.mem_zpowers f, N.T_inv hf⟩
      rw [hs] at hmem
      exact hmem.2
    obtain ⟨c, hc, hcf⟩ := ivk_1_2h_c F hF K e N f ⟨hfT, hf⟩ hford d hd
      (by rw [hdf]; exact hαord)
    have hαc : α = c⁻¹ * f * c := by
      calc α = c⁻¹ * (c * (d * f) * c⁻¹) * c := by rw [hdf]; group
        _ = c⁻¹ * f * c := by rw [hcf]
    obtain ⟨σ, hσ⟩ := (hf : f ∈ (fieldAutHom e).range)
    have hσ2 : orderOf σ = 2 := by
      rw [← hford, ← hσ]
      exact (orderOf_injective (fieldAutHom e) (fieldAutHom_injective e) σ).symm
    obtain ⟨F₀, _, _, hF₀, ⟨φ₀⟩⟩ := (ivk_1_4a F hF K e σ).2.2 (by rw [hσ2]; exact even_two)
    rw [hσ2] at hF₀
    rw [hσ] at φ₀
    obtain ⟨ψ⟩ := fixedSubgroup_equiv_of_conj c f
    rw [← hαc] at ψ
    have hodd₀ : Odd (Nat.card F₀) := by
      have h1 : Odd (Nat.card F) := hF.1
      rw [← hF₀, pow_two] at h1
      exact (Nat.odd_mul.1 h1).1
    have hge : 2 ≤ Nat.card F₀ := by
      have : 1 < Nat.card F₀ := Finite.one_lt_card
      omega
    have hge3 : 3 ≤ Nat.card F₀ := by
      obtain ⟨m, hm⟩ := hodd₀
      omega
    let Q := fixedSubgroup K α
    let eQ : ↥Q ≃* PGL2 F₀ := ψ.trans φ₀
    rcases Nat.lt_or_ge 3 (Nat.card F₀) with h3 | h3
    · right
      have hL2 : L2Field F₀ := ⟨hodd₀, h3⟩
      obtain ⟨eC⟩ := commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three
        (Q := ↥Q) F₀ (isOddPrimePower_of_L2Field hL2) h3 eQ
      refine ⟨F₀, inferInstance, inferInstance, hF₀, hodd₀, h3, ⟨?_⟩⟩
      rw [commutator_eq_map_commutator]
      exact (Subgroup.equivMapOfInjective _ Q.subtype Q.subtype_injective).symm.trans
        (eC.trans (L2.equivPSL F₀).symm)
    · left
      have h33 : Nat.card F₀ = 3 := by omega
      have hc24 : Nat.card ↥Q = 2 ^ 3 * 3 ^ 1 := by
        rw [Nat.card_congr eQ.toEquiv, pgl2_card_formula, h33]
        norm_num
      have := Fintype.ofFinite ↥Q
      exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
        Nat.prime_two Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hc24])

end CFSG.GH74.GLS.Stage2.Local.P27.QId
