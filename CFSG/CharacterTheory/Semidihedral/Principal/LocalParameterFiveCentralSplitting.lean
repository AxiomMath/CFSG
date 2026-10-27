module

public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveCentralSplittingSupport
public import CFSG.CharacterTheory.Semidihedral.Local.SplitActualLayer
public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveSylowSeven

public section

open scoped Classical Pointwise

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open
  LocalParameterFiveCentralSplitting

theorem simple_local_parameter_five_central_odd_core_and_actual_centralizer_splitting
    {G : Type} [Group G] [Fintype G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 5 1) :
    let T₀ : Subgroup (H t) := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    let Y : Subgroup (C t) := T₀.comap (nu t)
    let CY : Subgroup (C t) := Y ⊓ Subgroup.centralizer (N t : Set (C t))
    let J₀ : Subgroup (C t) := (CFSG.perfectResidual CY).map CY.subtype
    N t ≤ Subgroup.center (C t) ∧ IsCyclic (N t) ∧
      (Nat.card (N t) = 1 ∨ Nat.card (N t) = 3) ∧
      J₀.Normal ∧ (∃ φ : J₀ ≃* T₀, ∀ x : J₀, (φ x : H t) = nu t x) ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 5 ∧
        Nonempty (T₀ ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∧
      tInC t ∈ J₀ ∧ J₀ ⊓ N t = ⊥ ∧
      (∃ μ : J₀ × N t ≃* Y, ∀ x : J₀ × N t, (μ x : C t) = x.1 * x.2) ∧
      Nat.card (C t) = 240 * Nat.card (N t) ∧
      (Nat.card (C t) = 240 ∨ Nat.card (C t) = 720) ∧
      Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) = 12 * Nat.card (N t) ∧
      (Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) = 12 ∨
        Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) = 36) ∧
      Nat.card G = 126000 * Nat.card (N t) ∧
      (Nat.card G = 126000 ∨ Nat.card G = 378000) ∧ (C t).index = 525 ∧
      ∀ sC : C t, (sC : G) = fS (s n) →
        let Hs : Subgroup (C t) := J₀ ⊔ Subgroup.zpowers sC
        (∃ μ : Hs × N t ≃* C t, ∀ x : Hs × N t, μ x = (x.1 : C t) * x.2) ∧
        (∃ φ : Hs ≃* H t, ∀ x : Hs, φ x = nu t x) ∧
        ∃ (F : Type) (_ : Field F) (_ : Finite F) (a : Fˣ), Nat.card F = 5 ∧ ¬ IsSquare a ∧
          ∃ Ψ : MatrixCoverData.M F a ≃* H t,
            Ψ (MatrixCoverData.inclusion F a (-1)) = nu t (tInC t) ∧
            Ψ (MatrixCoverData.u F a) = nu t sC ∧
            ∃ Θ : MatrixCoverData.M F a ≃* Hs, (∀ x, nu t (Θ x) = Ψ x) ∧
              (Θ (MatrixCoverData.inclusion F a (-1)) : C t) = tInC t ∧
              (Θ (MatrixCoverData.u F a) : C t) = sC := by
  intro T₀ Y CY J₀
  have : Group.IsPerfect G := isPerfect_of_isSimpleGroup hGnonab
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := supplied_t_s_facts hn fS ht
  set s₀ : C t := ⟨(fS (s n) : G), hsC⟩ with hs₀def
  have hs₀2 : orderOf s₀ = 2 := by rw [← Subgroup.orderOf_coe]; exact hs2
  have hs₀t : s₀ ≠ tInC t := fun h => hst (congrArg Subtype.val h)
  obtain ⟨hN13, c, -, hJN, hJT, hYJN, -⟩ :=
    simple_local_parameter_five_odd_core_has_order_one_or_three hGnonab n hn S fS t ht hnonab
      hcentral hnc hmodel
  set CN : Subgroup (N t) :=
    ((Subgroup.centralizer {(fS (s n) : G)}).comap (C t).subtype).subgroupOf (N t) with hCNdef
  obtain ⟨-, hCcard, hDcard, hGcard, hidx, -, -⟩ :=
    simple_local_parameter_five_is_regular_with_exact_order hGnonab n hn S fS t ht hnonab hcentral
      hnc hmodel
  have hCcard : Nat.card (C t) = 240 * Nat.card CN * CN.index := hCcard
  have hDcard : Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) = 12 * Nat.card CN :=
    hDcard
  have hGcard : Nat.card G = 126000 * Nat.card CN * CN.index ^ 3 := hGcard
  have hidx : (C t).index = 525 * CN.index ^ 2 := hidx
  obtain ⟨-, -, hP7, -⟩ := simple_local_parameter_five_seven_centralizer_normalizer_congruence
    hGnonab n hn S fS t ht hnonab hcentral hnc hmodel
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 7 G) := inferInstance
  obtain ⟨A, -, hA13, -, -, -, -, hcong, -⟩ := hP7 P
  have hcong : Nat.card CN * CN.index ^ 3 ≡ Nat.card A [MOD 7] := hcong
  have hab : Nat.card CN * CN.index = Nat.card (N t) := Subgroup.card_mul_index CN
  have hN13' : Nat.card (N t) = 1 ∨ Nat.card (N t) = 3 := by
    rcases hN13 with hN1 | ⟨-, hN3⟩
    · left
      rw [hN1, Subgroup.card_bot]
    · exact Or.inr hN3
  have hNcyc : IsCyclic (N t) := by
    rcases hN13 with hN1 | ⟨hcyc, -⟩
    · rw [hN1]
      infer_instance
    · exact hcyc
  have hb1 : CN.index = 1 := by
    rcases hN13' with hN1 | hN3
    · rw [hN1] at hab
      exact Nat.eq_one_of_mul_eq_one_left hab
    · rw [hN3] at hab
      have ha : Nat.card CN ∣ 3 := ⟨CN.index, hab.symm⟩
      rcases (Nat.dvd_prime Nat.prime_three).mp ha with h1 | h3
      · exfalso
        rw [h1, one_mul] at hab
        rw [h1, hab] at hcong
        rcases hA13 with hA | hA <;> rw [hA] at hcong <;> revert hcong <;> decide
      · rw [h3] at hab
        omega
  have hCNtop : CN = ⊤ := Subgroup.index_eq_one.mp hb1
  have hs₀N : ∀ x ∈ N t, x * s₀ = s₀ * x := by
    intro x hx
    have hxCN : (⟨x, hx⟩ : N t) ∈ CN := hCNtop ▸ Subgroup.mem_top _
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hxCN
    exact Subtype.ext hxCN
  have hLJ := generalizedFitting_eq_J_of_field_group_trivial n hn S fS hG t ht2 hnonab hcentral
    hnc 5 1 (by norm_num) (by decide) le_rfl hmodel (fun a _ ha => Nat.dvd_one.mp ha)
  obtain ⟨hNZK, hJindex, -, -, -, -, -⟩ := actual_quotient_inputs n hn S fS hG t ht2
  have hKcomap : K t = (J t).comap (kappa t) := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    exact (sup_eq_left.mpr hNZK).symm
  have hYK : Y = K t := by
    change ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t) = K t
    rw [Subgroup.comap_comap, barKappa_comp_nu, hLJ, ← hKcomap]
  have hYidx : Y.index = 2 := by
    rw [hYK, hKcomap, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _),
      hJindex]
  have hs₀Y : s₀ ∉ Y := by
    rw [hYK]
    exact actual_noncentral_involution_not_mem_K n hn S fS hG t ht2 s₀ hs₀2 hs₀t
  have hCY : Y ⊔ Subgroup.zpowers s₀ = ⊤ := sup_zpowers_eq_top_of_index_eq_two hYidx hs₀Y
  have hNcomm : ∀ a ∈ N t, ∀ b ∈ N t, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := N t)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hYJN' : Y = Subgroup.normalClosure {c} ⊔ N t := hYJN
  have hYcent : Y ≤ Subgroup.centralizer (N t : Set (C t)) := by
    rw [hYJN']
    refine sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJN) fun x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact hNcomm h hh x hx
  have hs₀cent : s₀ ∈ Subgroup.centralizer (N t : Set (C t)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact hs₀N h hh
  have hNcent : Subgroup.centralizer (N t : Set (C t)) = ⊤ := by
    rw [eq_top_iff, ← hCY]
    exact sup_le hYcent (Subgroup.zpowers_le.mpr hs₀cent)
  have hNZ : N t ≤ Subgroup.center (C t) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer (N t : Set (C t)) := hNcent ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.mp hg x hx).symm
  have hcov : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ Nat.card (N t) → ∃ P : Sylow ℓ (N t),
      (Subgroup.centralizer (((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t)) :
        Set (C t)) ⊓ Y).map (nu t) = T₀ := by
    intro ℓ _ _
    obtain ⟨P⟩ : Nonempty (Sylow ℓ (N t)) := inferInstance
    refine ⟨P, ?_⟩
    have htop : Subgroup.centralizer (((P : Subgroup (N t)).map (N t).subtype :
        Subgroup (C t)) : Set (C t)) = ⊤ := by
      rw [eq_top_iff]
      intro g _
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hhN : h ∈ N t := Subgroup.map_subtype_le _ hh
      exact (Subgroup.mem_center_iff.mp (hNZ hhN) g).symm
    rw [htop, top_inf_eq]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) T₀
  obtain ⟨⟨-, hJ₀Y, -, hJ₀T, -⟩, hJ₀normal, htJ₀, -, hsplit, -⟩ :=
    Local.all_local_prime_covers_split_actual_layer_except_central_three_at_nine n hn S fS hG t
      ht2 hnonab hcentral hnc 5 1 (by norm_num) (by decide) le_rfl (by norm_num) hmodel
      (Or.inl hcov)
  obtain ⟨hE, ⟨φ, hφ⟩, hFSL, ⟨μ, hμ⟩⟩ := hsplit (by norm_num)
  have hJ₀T : J₀.map (nu t) = T₀ := hJ₀T
  have hJ₀Y : J₀ ≤ Y := hJ₀Y
  have ha₀ : Nat.card CN = Nat.card (N t) := by rw [← hab, hb1, mul_one]
  have hC240 : Nat.card (C t) = 240 * Nat.card (N t) := by rw [hCcard, hb1, ha₀, mul_one]
  have hD12 : Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) = 12 * Nat.card (N t) := by
    rw [hDcard, ha₀]
  have hG126 : Nat.card G = 126000 * Nat.card (N t) := by
    rw [hGcard, hb1, ha₀, one_pow, mul_one]
  have hidx525 : (C t).index = 525 := by rw [hidx, hb1, one_pow, mul_one]
  refine ⟨hNZ, hNcyc, hN13', hJ₀normal, ⟨φ, hφ⟩, hFSL, htJ₀, hE, ⟨μ, hμ⟩, hC240, ?_, hD12, ?_,
    hG126, ?_, hidx525, ?_⟩
  · rcases hN13' with h | h <;> rw [hC240, h] <;> norm_num
  · rcases hN13' with h | h <;> rw [hD12, h] <;> norm_num
  · rcases hN13' with h | h <;> rw [hG126, h] <;> norm_num
  intro sC hsC' Hs
  obtain rfl : sC = s₀ := Subtype.ext hsC'
  have hs₀sq : s₀ ^ 2 = 1 := by rw [← hs₀2]; exact pow_orderOf_eq_one s₀
  have hHsN : Hs ⊓ N t = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxH, hxN⟩
    obtain ⟨j, hj, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxH
    rcases eq_one_or_eq_of_mem_zpowers hs₀sq hz with rfl | rfl
    · rw [mul_one] at hxN ⊢
      have hjE : j ∈ J₀ ⊓ N t := ⟨hj, hxN⟩
      rw [hE] at hjE
      exact hjE
    · exfalso
      apply hs₀Y
      have h1 : nu t (j * s₀) = 1 := (QuotientGroup.eq_one_iff _).mpr hxN
      have hjY : j ∈ Y := hJ₀Y hj
      have hjs : j * s₀ ∈ Y := by
        change nu t (j * s₀) ∈ T₀
        rw [h1]
        exact T₀.one_mem
      have heq : s₀ = j⁻¹ * (j * s₀) := by group
      rw [heq]
      exact Y.mul_mem (Y.inv_mem hjY) hjs
  have hT₀idx : T₀.index = 2 := by
    rw [← Subgroup.index_comap_of_surjective T₀ (QuotientGroup.mk'_surjective (N t))]
    exact hYidx
  have hνH : Hs.map (nu t) = ⊤ := by
    have hT₀le : T₀ ≤ Hs.map (nu t) := by
      rw [← hJ₀T]
      exact Subgroup.map_mono le_sup_left
    have htop := sup_zpowers_eq_top_of_index_eq_two hT₀idx (hs₀Y : nu t s₀ ∉ T₀)
    rw [eq_top_iff, ← htop]
    exact sup_le hT₀le (Subgroup.zpowers_le.mpr
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers s₀))))
  have hinj : Function.Injective ((nu t).comp Hs.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxN : (x : C t) ∈ N t := (QuotientGroup.eq_one_iff _).mp hx
    have hxHN : (x : C t) ∈ Hs ⊓ N t := ⟨x.2, hxN⟩
    rw [hHsN] at hxHN
    exact Subtype.ext hxHN
  have hsurj : Function.Surjective ((nu t).comp Hs.subtype) := by
    intro y
    have hy : y ∈ Hs.map (nu t) := hνH ▸ Subgroup.mem_top y
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  let φH : Hs ≃* H t := MulEquiv.ofBijective ((nu t).comp Hs.subtype) ⟨hinj, hsurj⟩
  have hφH : ∀ x : Hs, φH x = nu t x := fun x => rfl
  have hcommHN : ∀ (x : Hs) (y : N t), Commute (Hs.subtype x) ((N t).subtype y) := fun x y =>
    (Subgroup.mem_center_iff.mp (hNZ y.2) x)
  let mH : Hs × N t →* C t := MonoidHom.noncommCoprod Hs.subtype (N t).subtype hcommHN
  have hmH : ∀ x : Hs × N t, mH x = (x.1 : C t) * x.2 := fun x => rfl
  have hmH_inj : Function.Injective mH := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ hxy
    rw [hmH] at hxy
    have hx : (x : C t) = (y : C t)⁻¹ := eq_inv_of_mul_eq_one_left hxy
    have hxN : (x : C t) ∈ N t := by rw [hx]; exact (N t).inv_mem y.2
    have hxHN : (x : C t) ∈ Hs ⊓ N t := ⟨x.2, hxN⟩
    rw [hHsN, Subgroup.mem_bot] at hxHN
    have hy : (y : C t) = 1 := by
      rw [hxHN, eq_comm, inv_eq_one] at hx
      exact hx
    exact Prod.ext (Subtype.ext hxHN) (Subtype.ext hy)
  have hmH_surj : Function.Surjective mH := by
    intro g
    obtain ⟨h, hh⟩ := hsurj (nu t g)
    have hN' : (h : C t)⁻¹ * g ∈ N t := by
      rw [← QuotientGroup.eq_one_iff]
      change nu t ((h : C t)⁻¹ * g) = 1
      rw [map_mul, map_inv]
      change ((nu t).comp Hs.subtype h)⁻¹ * nu t g = 1
      rw [hh, inv_mul_cancel]
    refine ⟨(h, ⟨(h : C t)⁻¹ * g, hN'⟩), ?_⟩
    rw [hmH]
    change (h : C t) * ((h : C t)⁻¹ * g) = g
    group
  let μH : Hs × N t ≃* C t := MulEquiv.ofBijective mH ⟨hmH_inj, hmH_surj⟩
  obtain ⟨⟨-, F, hF, hFfin, A, a, hFcard, -, hAdvd, -, -, -, -, ha', -, -, -, hPsi⟩, -⟩ :=
    ActualFourGroupNormalizer.actual_simple_layer_four_group_normalizer_action.{0} n hn S fS hG t
      ht2 hnonab hcentral hnc 5 1 (by norm_num) (by decide) le_rfl hmodel
  obtain ⟨Psi, hPsiZ, hPsiU, -⟩ := hPsi s₀ hs₀2 hs₀t
  have hA1 : Nat.card A = 1 := Nat.dvd_one.mp hAdvd
  have : Subsingleton A := (Nat.card_eq_one_iff_unique.mp hA1).1
  let ι : MatrixCoverData.M F (MatrixCover.fixedUnit F A a) ≃*
      MatrixTorus.OriginalH F (MatrixCover.fixedUnit F A a) A
        (ActualFourGroupCentralizer.fixed_coefficient_action F A a) :=
    MulEquiv.ofBijective SemidirectProduct.inl (semidirectProduct_inl_bijective _)
  let Ψ : MatrixCoverData.M F (MatrixCover.fixedUnit F A a) ≃* H t := ι.trans Psi
  have hΨz : Ψ (MatrixCoverData.inclusion F (MatrixCover.fixedUnit F A a) (-1)) =
      nu t (tInC t) := hPsiZ
  have hΨu : Ψ (MatrixCoverData.u F (MatrixCover.fixedUnit F A a)) = nu t s₀ := hPsiU
  let Θ : MatrixCoverData.M F (MatrixCover.fixedUnit F A a) ≃* Hs := Ψ.trans φH.symm
  have hΘ : ∀ x, nu t (Θ x) = Ψ x := fun x => by
    rw [← hφH]
    exact φH.apply_symm_apply (Ψ x)
  have htHs : tInC t ∈ Hs := Subgroup.mem_sup_left htJ₀
  have hs₀Hs : s₀ ∈ Hs := Subgroup.mem_sup_right (Subgroup.mem_zpowers s₀)
  have hΘz : (Θ (MatrixCoverData.inclusion F (MatrixCover.fixedUnit F A a) (-1)) : C t) =
      tInC t := by
    have h : Θ (MatrixCoverData.inclusion F (MatrixCover.fixedUnit F A a) (-1)) =
        ⟨tInC t, htHs⟩ := by
      apply φH.injective
      rw [hφH, hφH, hΘ, hΨz]
    rw [h]
  have hΘu : (Θ (MatrixCoverData.u F (MatrixCover.fixedUnit F A a)) : C t) = s₀ := by
    have h : Θ (MatrixCoverData.u F (MatrixCover.fixedUnit F A a)) = ⟨s₀, hs₀Hs⟩ := by
      apply φH.injective
      rw [hφH, hφH, hΘ, hΨu]
    rw [h]
  exact ⟨⟨μH, hmH⟩, ⟨φH, hφH⟩, F, hF, hFfin, MatrixCover.fixedUnit F A a,
    by rw [hFcard, pow_one], ha', Ψ, hΨz, hΨu, Θ, hΘ, hΘz, hΘu⟩

end CFSG.Semidihedral.Principal
