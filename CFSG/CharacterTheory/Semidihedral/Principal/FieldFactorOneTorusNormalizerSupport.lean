module

public import CFSG.CharacterTheory.Semidihedral.ActualFourGroupNormalizer

public section

open scoped Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open
open CFSG.Semidihedral.MatrixCoverData

theorem mem_torus_of_commute_of_ne {F : Type*} [Field F] (a : Fˣ) {X : SL F}
    (hX : X ∈ MatrixTorus.Torus F a) (h1 : X ≠ 1) (hm1 : X ≠ OddFieldSL2.minusIdentity F)
    {Y : SL F} (hXY : Y * X = X * Y) : Y ∈ MatrixTorus.Torus F a := by
  obtain ⟨x, y, hXm, hdet⟩ := (MatrixTorus.torus_coordinates F a X).mp hX
  have hy : y ≠ 0 := by
    intro hy0
    rw [hy0] at hdet hXm
    have hx : x = 1 ∨ x = -1 := sq_eq_one_iff.mp (by simpa using hdet)
    rcases hx with hx | hx
    · apply h1
      ext i j
      rw [hXm, hx]
      fin_cases i <;> fin_cases j <;> simp [MatrixTorus.torusMatrix]
    · apply hm1
      ext i j
      rw [hXm, hx, OddFieldSL2.minusIdentity_matrix]
      fin_cases i <;> fin_cases j <;> simp [MatrixTorus.torusMatrix]
  have hm := congrArg (fun Z : SL F => (Z : Matrix (Fin 2) (Fin 2) F)) hXY
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hm
  rw [hXm] at hm
  have h00 := congrArg (fun Z : Matrix (Fin 2) (Fin 2) F => Z 0 0) hm
  have h10 := congrArg (fun Z : Matrix (Fin 2) (Fin 2) F => Z 1 0) hm
  simp [Matrix.mul_apply, Fin.sum_univ_two, MatrixTorus.torusMatrix] at h00 h10
  rw [MatrixTorus.mem_torus_iff]
  constructor
  · apply mul_right_cancel₀ hy
    linear_combination h00
  · apply mul_right_cancel₀ hy
    linear_combination h10

theorem originalH_commute_u_of_commute {F : Type*} [Field F] (A : Subgroup (F ≃+* F))
    (hA : ∀ σ : A, σ = 1) (a : Fˣ) (hfix : ∀ σ : A, (σ : F ≃+* F) (a : F) = a)
    {X : MatrixCoverData.SL F} (hX : X ∈ MatrixTorus.Torus F a) (h1 : X ≠ 1)
    (hm1 : X ≠ OddFieldSL2.minusIdentity F) (g : MatrixTorus.OriginalH F a A hfix)
    (hg : g * MatrixTorus.originalSlInH F a A hfix X =
      MatrixTorus.originalSlInH F a A hfix X * g) :
    g * MatrixTorus.originalU F a A hfix = MatrixTorus.originalU F a A hfix * g := by
  have hgeq : g = SemidirectProduct.inl g.left := by
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right g]
    rw [hA g.right, map_one, mul_one]
  rw [hgeq] at hg ⊢
  change SemidirectProduct.inl g.left * SemidirectProduct.inl (MatrixCoverData.inclusion F a X) =
    SemidirectProduct.inl (MatrixCoverData.inclusion F a X) * SemidirectProduct.inl g.left at hg
  rw [← map_mul, ← map_mul] at hg
  have hg' := SemidirectProduct.inl_injective hg
  have hl := congrArg (fun m : MatrixCoverData.M F a => m.left) hg'
  change g.left.left * MatrixCoverData.action F a g.left.right X =
    X * MatrixCoverData.action F a (Multiplicative.ofAdd (0 : ZMod 2)) g.left.left at hl
  rw [MatrixCoverData.action_zero, MulAut.one_apply,
    MatrixTorus.action_torus_trivial F a g.left.right ⟨X, hX⟩] at hl
  have hY := mem_torus_of_commute_of_ne a hX h1 hm1 hl
  have hu := (MatrixTorus.matrix_centralizer_u_iff F a g.left).mpr hY
  rw [Subgroup.mem_centralizer_singleton_iff] at hu
  change SemidirectProduct.inl g.left * SemidirectProduct.inl (MatrixCoverData.u F a) =
    SemidirectProduct.inl (MatrixCoverData.u F a) * SemidirectProduct.inl g.left
  rw [← map_mul, ← map_mul, hu]

theorem field_factor_one_trivial_core_four_group_data {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hN : N t = ⊥) (hC : Nat.card (C t) = 2 * p ^ f * ((p ^ f) ^ 2 - 1))
    (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t) :
    Nat.card (ActualFourGroupCentralizer.D s) = 2 * MatrixTorus.torusSize (p ^ f) ∧
      Nat.card (ActualFourGroupCentralizer.R s) = MatrixTorus.torusSize (p ^ f) / 2 ∧
      IsCyclic (ActualFourGroupCentralizer.R s) ∧
      Nat.card (ActualFourGroupNormalizer.K s) = 4 * MatrixTorus.torusSize (p ^ f) ∧
      (ActualFourGroupCentralizer.D s).map (C t).subtype =
        C t ⊓ Subgroup.centralizer {(s : G)} ∧
      (ActualFourGroupCentralizer.V s).map (C t).subtype =
        Subgroup.zpowers t ⊔ Subgroup.zpowers (s : G) ∧
      (∀ x : ActualFourGroupCentralizer.R s, x ≠ 1 → ∀ c : C t,
        c * ((x : ActualFourGroupCentralizer.D s) : C t) =
          ((x : ActualFourGroupCentralizer.D s) : C t) * c → c * s = s * c) ∧
      ∃ d : ActualFourGroupNormalizer.K s, orderOf d = 4 ∧
        d ^ 2 = ActualFourGroupNormalizer.tInK s ∧
        (d : C t) * s * (d : C t)⁻¹ = tInC t * s ∧
        ∀ x : ActualFourGroupCentralizer.R s,
          (d : C t) * ((x : ActualFourGroupCentralizer.D s) : C t) * (d : C t)⁻¹ =
            ((x : ActualFourGroupCentralizer.D s) : C t)⁻¹ := by
  obtain ⟨⟨-, F, hF, hFfin, A, a, hcard, hAodd, hAf, -, -, -, -, haF, -, -, -, hdata⟩, hnorm⟩ :=
    ActualFourGroupNormalizer.actual_simple_layer_four_group_normalizer_action n hn S fS hG t ht
      hnonab hcentral hnc p f hp hpodd hf hmodel
  obtain ⟨Psi, hz, hu, hcent, -, hDmap, hVmap, -⟩ := hdata s hs hst
  obtain ⟨⟨x, y, hxy⟩, hND⟩ := hnorm F A _ _ s hs hst Psi hz hu hcard hAodd haF
  have hdat := hND x y hxy
  have hodd : Odd (Nat.card F) := hcard ▸ hpodd.pow
  have hNcard : Nat.card (N t) = 1 := by rw [hN, Subgroup.card_bot]
  have hN0 : Nat.card (ActualFourGroupCentralizer.N0 s) = 1 :=
    Nat.eq_one_of_dvd_one (hNcard ▸ Subgroup.card_subgroup_dvd_card _)
  have hN0i : (ActualFourGroupCentralizer.N0 s).index = 1 :=
    Nat.eq_one_of_dvd_one (hNcard ▸ Subgroup.index_dvd_card _)
  have hq1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
  have hA1 : Nat.card A = 1 := by
    have h := hcent.C_card
    rw [hN0, hN0i, hC] at h
    have hpos : 0 < 2 * p ^ f * ((p ^ f) ^ 2 - 1) := by
      have : 1 < (p ^ f) ^ 2 := by nlinarith
      have : 0 < (p ^ f) ^ 2 - 1 := by omega
      positivity
    have h' : (2 * p ^ f * ((p ^ f) ^ 2 - 1)) * Nat.card A =
        (2 * p ^ f * ((p ^ f) ^ 2 - 1)) * 1 := by
      rw [mul_one]
      calc 2 * p ^ f * ((p ^ f) ^ 2 - 1) * Nat.card A
          = 2 * 1 * 1 * Nat.card A * p ^ f * ((p ^ f) ^ 2 - 1) := by ring
        _ = 2 * p ^ f * ((p ^ f) ^ 2 - 1) := h.symm
    exact Nat.eq_of_mul_eq_mul_left hpos h'
  have hAtriv : ∀ σ : A, σ = 1 := fun σ => by
    have : Subsingleton A := (Nat.card_eq_one_iff_unique.mp hA1).1
    exact Subsingleton.elim _ _
  have hT' : MatrixTorus.torusSize (Nat.card F) = MatrixTorus.torusSize (p ^ f) := by rw [hcard]
  have hN0R : ActualFourGroupCentralizer.N0InR s = ⊥ := by
    have h := hcent.kernel_original
    rw [hN, bot_inf_eq] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _
      (fun a b hab => Subtype.ext (Subtype.ext hab))).mp h
  have hnu : Function.Injective (nu t) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hN]
  obtain ⟨e, he⟩ := hcent.original_quotient
  have : IsCyclic (MatrixTorus.W F (MatrixCover.fixedUnit F A a)) :=
    MatrixTorus.W_cyclic F _ hodd haF
  have hRcyc : IsCyclic (ActualFourGroupCentralizer.R s) := by
    have : IsCyclic (ActualFourGroupCentralizer.R s ⧸ ActualFourGroupCentralizer.N0InR s) := by
      apply isCyclic_of_surjective (e.symm.toMonoidHom.comp SemidirectProduct.inl)
      intro q
      refine ⟨(e q).left, ?_⟩
      have h : SemidirectProduct.inl (e q).left = e q := by
        conv_rhs => rw [← SemidirectProduct.inl_left_mul_inr_right (e q)]
        rw [hAtriv (e q).right, map_one, mul_one]
      rw [MonoidHom.comp_apply, h, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    apply isCyclic_of_injective (QuotientGroup.mk' (ActualFourGroupCentralizer.N0InR s))
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hN0R]
  refine ⟨?_, ?_, hRcyc, ?_, hDmap, hVmap, ?_, ?_⟩
  · rw [hcent.D_card, hN0, hA1, mul_one, mul_one]
  · rw [hcent.R_card, hN0, hA1, one_mul, one_mul]
  · rw [hdat.K_card, hN0, hA1, hT', mul_one, mul_one]
  ·
    intro r hr c hc
    have hw := he r
    set w' := e (QuotientGroup.mk' (ActualFourGroupCentralizer.N0InR s) r) with hw'def
    have hright : w'.right = 1 := hAtriv _
    have hincl : ActualFourGroupCentralizer.originalOddInclusion F A _ _ w' =
        MatrixTorus.originalSlInH F _ A _ w'.left.val.val := by
      rw [ActualFourGroupCentralizer.originalOddInclusion_coordinates, hright]
      rfl
    have hX : w'.left.val.val ∈ MatrixTorus.Torus F (MatrixCover.fixedUnit F A a) :=
      w'.left.val.property
    have hX1 : w'.left.val.val ≠ 1 := by
      intro h
      apply hr
      have hl : w'.left = 1 := Subtype.ext (Subtype.ext h)
      have hw1 : w' = 1 := SemidirectProduct.ext hl hright
      have hmk : QuotientGroup.mk' (ActualFourGroupCentralizer.N0InR s) r = 1 := by
        apply e.injective
        rw [map_one]
        exact hw1
      have hmem : r ∈ (QuotientGroup.mk' (ActualFourGroupCentralizer.N0InR s)).ker := hmk
      rw [QuotientGroup.ker_mk', hN0R] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hXm1 : w'.left.val.val ≠ OddFieldSL2.minusIdentity F := by
      intro h
      have hzz : w'.left.val = MatrixTorus.z F (MatrixCover.fixedUnit F A a) := Subtype.ext h
      have hoddord := (MatrixTorus.mem_W_iff_odd_order F _ hodd haF w'.left.val).mp
        w'.left.property
      rw [hzz, MatrixTorus.z_orderOf F _ hodd] at hoddord
      exact absurd hoddord (by decide)
    have hcomm : Psi.symm (nu t c) * MatrixTorus.originalSlInH F _ A _ w'.left.val.val =
        MatrixTorus.originalSlInH F _ A _ w'.left.val.val * Psi.symm (nu t c) := by
      have h1 : nu t c * nu t ((r : ActualFourGroupCentralizer.D s) : C t) =
          nu t ((r : ActualFourGroupCentralizer.D s) : C t) * nu t c := by
        rw [← map_mul, ← map_mul, hc]
      rw [← hw, hincl] at h1
      apply Psi.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact h1
    have hcu := originalH_commute_u_of_commute A hAtriv _ _ hX hX1 hXm1 _ hcomm
    have h2 : nu t c * nu t s = nu t s * nu t c := by
      have h3 := congrArg Psi hcu
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hu] at h3
      exact h3
    apply hnu
    rw [map_mul, map_mul]
    exact h2
  obtain ⟨d, hd4, hd2, hds, -, -, -, -, e', -, -, hinv, -⟩ := hdat.actual_lift_and_action
  refine ⟨d, hd4, hd2, hds, fun r => ?_⟩
  set q : ActualFourGroupCentralizer.R s ⧸ ActualFourGroupCentralizer.N0InR s :=
    QuotientGroup.mk' (ActualFourGroupCentralizer.N0InR s) r with hq_def
  have heq : e' q = SemidirectProduct.inl (e' q).left := by
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right (e' q)]
    rw [hAtriv (e' q).right, map_one, mul_one]
  have hconj : ActualFourGroupNormalizer.conjugationOnOddQuotient s d q = q⁻¹ := by
    apply e'.injective
    have h := hinv (e' q).left
    rw [← heq, MulEquiv.symm_apply_apply] at h
    calc e' (ActualFourGroupNormalizer.conjugationOnOddQuotient s d q)
        = SemidirectProduct.inl (e' q).left⁻¹ := h
      _ = (SemidirectProduct.inl (e' q).left)⁻¹ := map_inv _ _
      _ = (e' q)⁻¹ := by rw [← heq]
      _ = e' q⁻¹ := (map_inv e' q).symm
  have h2 : ActualFourGroupNormalizer.conjugationOnR s d r = r⁻¹ := by
    have h1 : QuotientGroup.mk (s := ActualFourGroupCentralizer.N0InR s)
        (show KleinFourOddKernel.oddKernel s from ActualFourGroupNormalizer.conjugationOnR s d r) =
        QuotientGroup.mk (s := ActualFourGroupCentralizer.N0InR s)
          (show KleinFourOddKernel.oddKernel s from r⁻¹) := hconj
    rw [QuotientGroup.eq, hN0R, Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact h1
  rw [← ActualFourGroupNormalizer.conjugationOnR_value, h2]
  rfl

theorem sup_eq_of_card_eq_mul {G : Type*} [Group G] [Finite G] {V W D : Subgroup G}
    (hVD : V ≤ D) (hWD : W ≤ D) (hdisj : Disjoint V W)
    (hcard : Nat.card D = Nat.card V * Nat.card W) : V ⊔ W = D := by
  apply Subgroup.eq_of_le_of_card_ge (sup_le hVD hWD)
  rw [hcard]
  let f : V × W → (V ⊔ W : Subgroup G) := fun p =>
    ⟨(p.1 : G) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hf : Function.Injective f := by
    rintro ⟨v, w⟩ ⟨v', w'⟩ h
    have h' : (v : G) * w = v' * w' := congrArg Subtype.val h
    have hvv : (v' : G)⁻¹ * v = w' * (w : G)⁻¹ := by
      calc (v' : G)⁻¹ * v = (v' : G)⁻¹ * (v * w) * (w : G)⁻¹ := by group
        _ = (v' : G)⁻¹ * (v' * w') * (w : G)⁻¹ := by rw [h']
        _ = w' * (w : G)⁻¹ := by group
    have h1 : (v' : G)⁻¹ * v = 1 := Subgroup.disjoint_def.mp hdisj
      (V.mul_mem (V.inv_mem v'.2) v.2) (hvv ▸ W.mul_mem w'.2 (W.inv_mem w.2))
    have hveq : (v : G) = v' := by
      rw [inv_mul_eq_one] at h1
      exact h1.symm
    have hweq : (w : G) = w' := by
      rw [hveq] at h'
      exact mul_left_cancel h'
    exact Prod.ext (Subtype.ext hveq) (Subtype.ext hweq)
  have h := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod] at h

theorem card_centralizer_of_layer_preimage_index_two {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hN : N t = ⊥)
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2) :
    Nat.card (C t) = 2 * p ^ f * ((p ^ f) ^ 2 - 1) := by
  obtain ⟨F₁, hF₁, hF₁fin, A₁, rho, data⟩ :=
    actual_simple_layer_matrix_data n hn S fS hG t ht hnonab hcentral hnc p f hp hpodd hf hmodel
  obtain ⟨eta, -, -, -⟩ := data.compatible_layer
  have hL : Nat.card ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) =
      p ^ f * ((p ^ f) ^ 2 - 1) := by
    rw [Nat.card_congr eta.toEquiv, CFSG.GorensteinWalter.sl2_card_formula, data.field_card]
  have hnu : Function.Injective (nu t) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hN]
  have hYcard : Nat.card (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap
      (nu t)) = p ^ f * ((p ^ f) ^ 2 - 1) := by
    rw [← hL, ← Subgroup.card_map_of_injective hnu,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  have h := Subgroup.card_mul_index
    (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t))
  rw [hYcard, hY] at h
  rw [← h]
  ring

end CFSG.Semidihedral.Principal
