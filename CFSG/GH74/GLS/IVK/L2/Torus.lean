module

public import CFSG.GH74.GLS.IVK.Statements.Sec1
public import CFSG.GH74.GLS.IVK.L2.TorusMatrices
public import CFSG.GH74.GLS.IVK.L2.TorusCentralizer

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG.Assembly.LowTwoRank

theorem ivk_1_3abc : IVK_1_3abc := by
  intro F _ _ hF D hD hc
  exact L2Torus.exists_inverting_normalizer (specialLinearGroupEquivStatedSL 2 F).symm hF.1 hF.2
    D hD hc

theorem sl2_centralizer_order_four {F : Type} [Field F] [Finite F] (hF : L2Field F) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hq : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) (d : ℕ)
    (hd : (d : ℤ) = Nat.card F - ε) (û : SL2 F) (hû : orderOf û = 4) :
    IsCyclic ↥(centralizer ({û} : Set (SL2 F))) ∧
      Nat.card ↥(centralizer ({û} : Set (SL2 F))) = d := by
  have h2 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hF.1
  let e := specialLinearGroupEquivStatedSL 2 F
  set x := e.symm û with hxdef
  have hxo : orderOf x = 4 := by rw [hxdef, MulEquiv.orderOf_eq]; exact hû
  have hx2 : x * x = CFSG.Semidihedral.OddFieldSL2.minusIdentity F := by
    have : orderOf (x ^ 2) = 2 := by
      rw [orderOf_pow_of_dvd (by norm_num) (by rw [hxo]; norm_num), hxo]
    rw [CFSG.Semidihedral.OddFieldSL2.orderOf_eq_two_iff F h2] at this
    rwa [← pow_two]
  have hcent : centralizer ({û} : Set (SL2 F)) =
      (centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F))).map e.toMonoidHom := by
    ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply, hxdef] at h ⊢
      exact h
    · intro h
      have := congrArg e h
      simpa [hxdef] using this
  obtain ⟨hcyc, hsq, hnsq⟩ := L2Torus.centralizer_cyclic_card hF.1 x hx2
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hcard : Nat.card ↥(centralizer ({û} : Set (SL2 F))) =
      Nat.card ↥(centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) := by
    rw [hcent]
    exact Subgroup.card_map_of_injective hinj
  have hcyc' : IsCyclic ↥(centralizer ({û} : Set (SL2 F))) := by
    rw [hcent]
    exact (Subgroup.equivMapOfInjective _ e.toMonoidHom hinj).isCyclic.1 hcyc
  refine ⟨hcyc', ?_⟩
  rw [hcard]
  have hsqiff : IsSquare (-1 : F) ↔ Nat.card F % 4 ≠ 3 := by
    have := Fintype.ofFinite F
    rw [FiniteField.isSquare_neg_one_iff, Nat.card_eq_fintype_card]
  have hq4 : (Nat.card F : ℤ) % 4 = ε % 4 := hq
  have hqpos : 0 < Nat.card F := Nat.card_pos
  rcases hε with rfl | rfl
  · have : Nat.card F % 4 = 1 := by omega
    rw [hsq (hsqiff.2 (by omega))]
    omega
  · have : Nat.card F % 4 = 3 := by omega
    rw [hnsq (fun h => (hsqiff.1 h) this)]
    omega

theorem orderOf_lift_involution {F : Type} [Field F] [Finite F] (hF : L2Field F) {G : Type*}
    [Group G] (φ : SL2 F →* G)
    (hker : ∀ y : SL2 F, φ y = 1 ↔ y ∈ (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F))
    (û : SL2 F) (h : orderOf (φ û) = 2) : orderOf û = 4 := by
  have h2 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hF.1
  let e := specialLinearGroupEquivStatedSL 2 F
  have hker' : ∀ y : SL2 F, φ y = 1 ↔ e.symm y ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    intro y
    rw [hker, ← map_center_eq_statedScalars 2 F, Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      show e.symm (e z) ∈ _
      rw [e.symm_apply_apply]
      exact hz
    · intro hy
      exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
  set x := e.symm û with hx
  have hxo : orderOf û = orderOf x := by rw [hx, MulEquiv.orderOf_eq]
  have hmk : ∀ n : ℕ, (φ û) ^ n = 1 ↔ x ^ n ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    intro n
    rw [← map_pow, hker', hx, ← map_pow]
  have hx2 : x ^ 2 ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    apply (hmk 2).1
    have := pow_orderOf_eq_one (φ û)
    rwa [h] at this
  have hx1 : x ∉ center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    intro hc
    have := (hmk 1).2 (by simpa using hc)
    rw [pow_one] at this
    have h1 : orderOf (φ û) = 1 := orderOf_eq_one_iff.2 this
    omega
  obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hx2
  rw [Fintype.card_fin] at hr
  have hr' : (r - 1) * (r + 1) = 0 := by linear_combination hr
  rcases mul_eq_zero.1 hr' with hr1 | hr1
  · exfalso
    have hr1' : r = 1 := sub_eq_zero.1 hr1
    have hx2' : x ^ 2 = 1 := by
      apply Subtype.ext
      rw [← hrx, hr1']
      simp
    apply hx1
    have hinv : x⁻¹ = x := by
      rw [inv_eq_iff_mul_eq_one, ← pow_two, hx2']
    rcases CFSG.Semidihedral.OddFieldSL2.eq_one_or_minusIdentity_of_inv_eq_self F h2 x hinv with
      h1 | h1
    · rw [h1]
      exact Subgroup.one_mem _
    · rw [h1]
      exact CFSG.Semidihedral.OddFieldSL2.minusIdentity_mem_center F
  · have hr1' : r = -1 := eq_neg_of_add_eq_zero_left hr1
    have hx2' : x ^ 2 = CFSG.Semidihedral.OddFieldSL2.minusIdentity F := by
      apply Subtype.ext
      rw [← hrx, hr1', CFSG.Semidihedral.OddFieldSL2.minusIdentity_matrix]
    rw [hxo]
    have h4 : orderOf x = 2 ^ (1 + 1) :=
      orderOf_eq_prime_pow (p := 2) (n := 1)
        (by
          rw [pow_one, hx2']
          exact CFSG.Semidihedral.OddFieldSL2.minusIdentity_ne_one F h2)
        (by
          rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hx2']
          exact CFSG.Semidihedral.OddFieldSL2.minusIdentity_square F)
    simpa using h4

theorem sl2_centralizer_lift_involution {F : Type} [Field F] [Finite F] (hF : L2Field F) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hq : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) (d : ℕ)
    (hd : (d : ℤ) = Nat.card F - ε) {G : Type*} [Group G] (φ : SL2 F →* G)
    (hker : ∀ y : SL2 F, φ y = 1 ↔ y ∈ (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F))
    {K : Type*} [Group K] (e : K ≃* G) (u : K) (hu : orderOf u = 2) (û : SL2 F)
    (hû : φ û = e u) :
    IsCyclic ↥(centralizer ({û} : Set (SL2 F))) ∧
      Nat.card ↥(centralizer ({û} : Set (SL2 F))) = d := by
  apply sl2_centralizer_order_four hF ε hε hq d hd û
  apply orderOf_lift_involution hF φ hker û
  rw [hû, MulEquiv.orderOf_eq, hu]

end CFSG.GH74.GLS.IVK
