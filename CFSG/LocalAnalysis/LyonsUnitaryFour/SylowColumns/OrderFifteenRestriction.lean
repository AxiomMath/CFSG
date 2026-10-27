module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.SylowColumns.Congruences

public section

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers CFSG.RankTwoShapes
open scoped BigOperators Classical

variable {G : Type} [Group G]

section Free

theorem normalizerConj_pow_apply (S : Subgroup G) {m : G}
    (hm : m ∈ Subgroup.normalizer (S : Set G)) (k : ℕ) (x : S) :
    (((normalizerConj S hm) ^ k) x : G) = (m ^ k)⁻¹ * x * m ^ k := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, ih, normalizerConj_apply, pow_succ']
    group

theorem mem_center_of_outer_order_five {S : Type} [Group S] {K : Type} [Field K]
    {hK : Nat.card K = 16} (e : S ≃* unitaryFourW K hK) (α : MulAut S)
    (h5 : α ^ 5 ∈ (MulAut.conj : S →* MulAut S).range)
    (h1 : α ∉ (MulAut.conj : S →* MulAut S).range) {x : S}
    (hx : α x * x⁻¹ ∈ Subgroup.center S) : x ∈ Subgroup.center S := by
  have := charP_two_of_natCard_eq_sixteen hK
  have hc : ∀ w : S, w ∈ Subgroup.center S ↔ UnitaryFourW.fst (e w) = 0 := by
    intro w
    rw [← mem_center_iff_of_mulEquiv e w, UnitaryFourW.center_eq_ker_firstCoord,
      UnitaryFourW.mem_ker_firstCoord]
  rw [hc] at hx ⊢
  apply fst_eq_zero_of_outer_order_five e α h5 h1 x
  rw [map_mul, map_inv, UnitaryFourW.fst_mul, UnitaryFourW.fst_inv] at hx
  rw [eq_neg_of_add_eq_zero_left hx, CharTwo.neg_eq]

theorem UnitaryFourSylowShape.linear_comp_ne_of_quotient {S : Type} [Group S] [Finite S]
    (h : UnitaryFourSylowShape S) (φ : S ≃* S)
    (hφ : ∀ x : S, φ x * x⁻¹ ∈ Subgroup.center S → x ∈ Subgroup.center S) {θ : S → ℂ}
    (hθ : θ ∈ CFSG.BlocksIrr S) (h1 : θ 1 = 1) (hne : θ ≠ 1) : θ ∘ φ ≠ θ := by
  obtain ⟨l, rfl⟩ := h.exists_sign_of_linear hθ h1
  intro hfix
  apply hne
  have hcen : Subgroup.center S ≤ (Subgroup.center S).comap φ.toMonoidHom :=
    fun z hz => mulEquiv_mem_center φ hz
  let β : S ⧸ Subgroup.center S →* S ⧸ Subgroup.center S :=
    QuotientGroup.map _ _ φ.toMonoidHom hcen
  have hβ : ∀ q, β q = q → q = 1 := by
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hq' : ((φ x : S) : S ⧸ Subgroup.center S) = (x : S ⧸ Subgroup.center S) := hq
    rw [QuotientGroup.eq] at hq'
    rw [QuotientGroup.eq_one_iff]
    apply hφ x
    have h2 := Subgroup.inv_mem _ hq'
    rw [mul_inv_rev, inv_inv] at h2
    have h3 : φ x * x⁻¹ = x * (x⁻¹ * φ x) * x⁻¹ := by group
    rw [h3]
    exact (inferInstance : (Subgroup.center S).Normal).conj_mem _ h2 x
  have htriv := monoidHom_eq_one_of_fixedPointFree β hβ l (fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have := congrFun hfix x
    simp only [Function.comp_apply] at this
    exact_mod_cast this)
  funext s
  rw [htriv]
  simp

end Free

section Freeness

theorem exists_mem_map_center_ne_one [Finite G] {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T))) :
    ∃ z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype, z ≠ 1 := by
  have hshape := unitaryFourSylowShape_of_mulEquiv hT S U hSU
  have : Nontrivial (Subgroup.center (S : Subgroup G)) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hshape.card_center]
    norm_num
  obtain ⟨w, hw⟩ := exists_ne (1 : Subgroup.center (S : Subgroup G))
  refine ⟨((w : (S : Subgroup G)) : G), ⟨w, w.property, rfl⟩, fun h => hw ?_⟩
  exact Subtype.ext (Subtype.ext h)

theorem order_fifteen_linear_free [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    (hd : (((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup G) : Set G))).index = 15)
    {m : G} (hm : m ∈ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hmR : m ∉ (S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G))
    {θ : ↥(S : Subgroup G) → ℂ} (hθ : θ ∈ nonprincipalLinearCharacters (S : Subgroup G)) :
    conjugateCharacter (S : Subgroup G) m θ ≠ θ := by
  classical
  obtain ⟨hRn, -, -, hloc⟩ := lyons_unitary_four_normalizer_odd_quotient hnonab hT S U hSU
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hcent⟩ :=
    lyons_unitary_four_fusion_and_centralizers hnonab hT S U hSU
  have hshape := unitaryFourSylowShape_of_mulEquiv hT S U hSU
  have hθ' := mem_nonprincipalLinearCharacters.mp hθ
  rw [conjugateCharacter_eq_comp hm]
  by_cases hmZ : m ∈ Subgroup.centralizer
      (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) : Set G)
  ·
    obtain ⟨z, hz, hz1⟩ := exists_mem_map_center_ne_one hT S U hSU
    obtain ⟨-, -, -, hMeq, -, hidx, -⟩ := hloc z hz hz1
    have hmM : m ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) ⊓
        Subgroup.centralizer ({z} : Set G) := by
      rw [hMeq]
      exact Subgroup.mem_inf.mpr ⟨hm, hmZ⟩
    have hidx5 : (((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
        (Subgroup.normalizer ((S : Subgroup G) : Set G) ⊓
          Subgroup.centralizer ({z} : Set G))).index = 5 := by rw [hidx, hd]
    have hRMnormal : (((S : Subgroup G) ⊔
        Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
        (Subgroup.normalizer ((S : Subgroup G) : Set G) ⊓
          Subgroup.centralizer ({z} : Set G))).Normal := by
      constructor
      intro a ha b
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      have haN : (a : G) ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) :=
        (Subgroup.mem_inf.mp a.property).1
      have hbN : (b : G) ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) :=
        (Subgroup.mem_inf.mp b.property).1
      have h := hRn.conj_mem ⟨a, haN⟩ (by rw [Subgroup.mem_subgroupOf]; exact ha) ⟨b, hbN⟩
      rw [Subgroup.mem_subgroupOf] at h
      simpa using h
    have h5 : m ^ 5 ∈ (S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
      have h := pow_card_eq_one' (x := ((⟨m, hmM⟩ : (Subgroup.normalizer
        ((S : Subgroup G) : Set G) ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G)) :
          (Subgroup.normalizer ((S : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ({z} : Set G) : Subgroup G) ⧸
          ((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
            (Subgroup.normalizer ((S : Subgroup G) : Set G) ⊓
              Subgroup.centralizer ({z} : Set G))))
      rw [← Subgroup.index_eq_card, hidx5, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf] at h
      simpa using h
    have hK : Nat.card (GaloisField 2 4) = 16 := by
      rw [GaloisField.card 2 4 (by norm_num)]
      norm_num
    obtain ⟨φ⟩ := nonempty_sylow_equiv_unitaryFourW hT U (GaloisField 2 4) hK
    obtain ⟨e₀⟩ := hSU
    have hα5 : normalizerConj (S : Subgroup G) hm ^ 5 ∈
        (MulAut.conj : (S : Subgroup G) →* MulAut (S : Subgroup G)).range := by
      obtain ⟨s, hs, hsn⟩ := sup_centralizer_le_innerActing (S : Subgroup G) h5
      refine ⟨⟨s, hs⟩⁻¹, ?_⟩
      ext x
      rw [normalizerConj_pow_apply, hsn x x.property]
      simp
    have hα1 : normalizerConj (S : Subgroup G) hm ∉
        (MulAut.conj : (S : Subgroup G) →* MulAut (S : Subgroup G)).range := by
      rintro ⟨s', hs'⟩
      apply hmR
      have hcomm : m * s' ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have h1 := congrArg Subtype.val (DFunLike.congr_fun hs' ⟨x, hx⟩)
        rw [normalizerConj_apply] at h1
        simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
        calc x * (m * s') = m * (m⁻¹ * x * m) * s' := by group
          _ = m * (s' * x * (s' : G)⁻¹) * s' := by rw [h1]
          _ = m * s' * x := by group
      have heq : m = (m * s') * (s' : G)⁻¹ := by group
      rw [heq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hcomm)
        (Subgroup.mem_sup_left ((S : Subgroup G).inv_mem s'.property))
    exact hshape.linear_comp_ne_of_quotient (normalizerConj (S : Subgroup G) hm)
      (fun x hx => mem_center_of_outer_order_five (e₀.trans φ) _ hα5 hα1 hx)
      hθ'.1 hθ'.2.1 hθ'.2.2
  · have hfix : ∀ z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype,
        z ≠ 1 → m * z * m⁻¹ ≠ z := by
      intro z hz hz1 hmz
      apply hmZ
      have hC : m ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) ⊓
          Subgroup.centralizer ({z} : Set G) := by
        refine Subgroup.mem_inf.mpr ⟨hm, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc m * z = m * z * m⁻¹ * m := by group
          _ = z * m := by rw [hmz]
      rw [(hcent z hz hz1).1] at hC
      exact (Subgroup.mem_inf.mp hC).2
    exact hshape.linear_comp_ne (normalizerConj (S : Subgroup G) hm)
      (normalizerConj_fixedPointFree hm hfix) hθ'.1 hθ'.2.1 hθ'.2.2

end Freeness

section Multiplicities

theorem degreeFour_multiplicity_const [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    (m : (↥(S : Subgroup G) → ℂ) → ℕ)
    (hminv : ∀ θ ∈ CFSG.BlocksIrr (S : Subgroup G),
      ∀ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G),
        m (conjugateCharacter (S : Subgroup G) n θ) = m θ) :
    ∃ c : ℕ, ∀ θ ∈ degreeFourCharacters (S : Subgroup G), m θ = c := by
  classical
  have hshape := unitaryFourSylowShape_of_mulEquiv hT S U hSU
  obtain ⟨n, hn, h3, hfix⟩ := exists_normalizer_element_order_three hnonab hT S U hSU
  have hφ := normalizerConj_fixedPointFree hn hfix
  have hPD : ∀ k ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), ∀ θ,
      θ ∈ degreeFourCharacters (S : Subgroup G) →
      conjugateCharacter (S : Subgroup G) k θ ∈ degreeFourCharacters (S : Subgroup G) := by
    intro k hk θ hθ
    rw [mem_degreeFourCharacters] at hθ ⊢
    exact ⟨conjugateCharacter_mem_blocksIrr hk hθ.1,
      by rw [conjugateCharacter_apply_one hk, hθ.2]⟩
  let σD := conjugatePerm hn (fun θ => θ ∈ degreeFourCharacters (S : Subgroup G))
    (hPD n hn) (hPD n⁻¹ (inv_mem hn))
  have hσD3 : σD ^ 3 = 1 := by
    ext θ : 1
    apply Subtype.ext
    rw [conjugatePerm_pow_val, conjugateCharacter_innerActing h3 _
      (blocksIrr_conj (mem_degreeFourCharacters.mp θ.property).1)]
    rfl
  have hσDfix : ∀ θ, σD θ ≠ θ := by
    intro θ h
    have h' := congrArg Subtype.val h
    change conjugateCharacter (S : Subgroup G) n θ.val = θ.val at h'
    rw [conjugateCharacter_eq_comp hn] at h'
    have hθ := mem_degreeFourCharacters.mp θ.property
    exact hshape.degree_four_comp_ne (normalizerConj (S : Subgroup G) hn) hφ hθ.1 hθ.2 h'
  obtain ⟨kD, repD, hbijD⟩ := exists_orbit_representatives_three σD hσD3 hσDfix
  have hkD : kD = 1 := by
    have h := Nat.card_eq_of_bijective _ hbijD
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin,
      Fintype.card_fin, Nat.card_eq_fintype_card, Fintype.card_coe,
      hshape.card_degreeFourCharacters] at h
    omega
  subst hkD
  refine ⟨m (repD 0).val, fun θ hθ => ?_⟩
  obtain ⟨⟨i, a⟩, hia⟩ := hbijD.2 ⟨θ, hθ⟩
  have h := congrArg Subtype.val hia
  simp only at h
  rw [conjugatePerm_pow_val] at h
  rw [← h, Subsingleton.elim i 0, hminv _ (mem_degreeFourCharacters.mp (repD 0).property).1 _
    (Subgroup.pow_mem _ hn _)]

theorem linear_multiplicity_const_of_order_fifteen [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    (hd : (((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup G) : Set G))).index = 15)
    (m : (↥(S : Subgroup G) → ℂ) → ℕ)
    (hminv : ∀ θ ∈ CFSG.BlocksIrr (S : Subgroup G),
      ∀ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G),
        m (conjugateCharacter (S : Subgroup G) n θ) = m θ) :
    ∃ b : ℕ, ∀ θ ∈ nonprincipalLinearCharacters (S : Subgroup G), m θ = b := by
  classical
  have hshape := unitaryFourSylowShape_of_mulEquiv hT S U hSU
  obtain ⟨-, hcyc, -, -⟩ := lyons_unitary_four_normalizer_odd_quotient hnonab hT S U hSU
  obtain ⟨q, hq⟩ := IsCyclic.exists_generator (α := Subgroup.normalizer
    ((S : Subgroup G) : Set G) ⧸ ((S : Subgroup G) ⊔
      Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
        (Subgroup.normalizer ((S : Subgroup G) : Set G)))
  have hord : orderOf q = 15 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hq, ← Subgroup.index_eq_card, hd]
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective q
  set g : G := (g' : G) with hg
  have hgN : g ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) := g'.property
  have hgpow : ∀ k : ℕ, 0 < k → k < 15 →
      g ^ k ∉ (S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
    intro k hk0 hk15 hk
    have h1 := pow_ne_one_of_lt_orderOf (x := (g' : Subgroup.normalizer
      ((S : Subgroup G) : Set G) ⧸ ((S : Subgroup G) ⊔
        Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
          (Subgroup.normalizer ((S : Subgroup G) : Set G)))) (n := k) (by omega)
      (by rw [hord]; exact hk15)
    apply h1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa [hg] using hk
  have hne : (nonprincipalLinearCharacters (S : Subgroup G)).Nonempty := by
    rw [← Finset.card_pos, hshape.card_nonprincipalLinearCharacters]
    norm_num
  obtain ⟨θ₀, hθ₀⟩ := hne
  have hθ₀' := mem_nonprincipalLinearCharacters.mp hθ₀
  have hPL : ∀ k ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), ∀ θ,
      θ ∈ nonprincipalLinearCharacters (S : Subgroup G) →
      conjugateCharacter (S : Subgroup G) k θ ∈ nonprincipalLinearCharacters (S : Subgroup G) := by
    intro k hk θ hθ
    rw [mem_nonprincipalLinearCharacters] at hθ ⊢
    exact ⟨conjugateCharacter_mem_blocksIrr hk hθ.1,
      by rw [conjugateCharacter_apply_one hk, hθ.2.1], conjugateCharacter_ne_one hk hθ.2.2⟩
  let f : Fin 15 → {θ : ↥(S : Subgroup G) → ℂ //
      θ ∈ nonprincipalLinearCharacters (S : Subgroup G)} :=
    fun k => ⟨conjugateCharacter (S : Subgroup G) (g ^ (k : ℕ)) θ₀,
      hPL _ (Subgroup.pow_mem _ hgN _) θ₀ hθ₀⟩
  have hinj : Function.Injective f := by
    have key : ∀ i j : Fin 15, (i : ℕ) < j → f i ≠ f j := by
      intro i j hij hfij
      have h := congrArg Subtype.val hfij
      change conjugateCharacter (S : Subgroup G) (g ^ (i : ℕ)) θ₀ =
        conjugateCharacter (S : Subgroup G) (g ^ (j : ℕ)) θ₀ at h
      have h' := congrArg (conjugateCharacter (S : Subgroup G) (g ^ (i : ℕ))⁻¹) h
      rw [conjugateCharacter_mul (inv_mem (Subgroup.pow_mem _ hgN _))
          (Subgroup.pow_mem _ hgN _), inv_mul_cancel, conjugateCharacter_one,
        conjugateCharacter_mul (inv_mem (Subgroup.pow_mem _ hgN _))
          (Subgroup.pow_mem _ hgN _)] at h'
      have hpow : (g ^ (i : ℕ))⁻¹ * g ^ (j : ℕ) = g ^ ((j : ℕ) - i) := by
        rw [← pow_sub_mul_pow g (Nat.le_of_lt hij)]
        group
      rw [hpow] at h'
      exact order_fifteen_linear_free hnonab hT S U hSU hd (Subgroup.pow_mem _ hgN _)
        (hgpow _ (by omega) (by omega)) hθ₀ h'.symm
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · exact key i j h hij
    · exact key j i h hij.symm
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [Fintype.card_fin, Fintype.card_coe, hshape.card_nonprincipalLinearCharacters]
  refine ⟨m θ₀, fun θ hθ => ?_⟩
  obtain ⟨k, hk⟩ := hbij.2 ⟨θ, hθ⟩
  have h := congrArg Subtype.val hk
  change conjugateCharacter (S : Subgroup G) (g ^ (k : ℕ)) θ₀ = θ at h
  rw [← h, hminv _ hθ₀'.1 _ (Subgroup.pow_mem _ hgN _)]

end Multiplicities

section Node

theorem lyons_order_fifteen_sylow_restriction_multiplicities [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    (hd : (((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup G) : Set G))).index = 15) :
    (nonprincipalLinearCharacters (S : Subgroup G)).card = 15 ∧
    (degreeFourCharacters (S : Subgroup G)).card = 3 ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ G V), ∃ a b c : ℕ,
        (∀ x : (S : Subgroup G), ρ.character x =
          a + b * ∑ θ ∈ nonprincipalLinearCharacters (S : Subgroup G), θ x +
            c * ∑ θ ∈ degreeFourCharacters (S : Subgroup G), θ x) ∧
        (∀ a' b' c' : ℕ, (∀ x : (S : Subgroup G), ρ.character x =
          a' + b' * ∑ θ ∈ nonprincipalLinearCharacters (S : Subgroup G), θ x +
            c' * ∑ θ ∈ degreeFourCharacters (S : Subgroup G), θ x) →
          a' = a ∧ b' = b ∧ c' = c) ∧
        (∀ z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype, z ≠ 1 →
          ∀ t ∈ (S : Subgroup G), orderOf t = 4 →
            ρ.character 1 = a + 15 * b + 12 * c ∧ ρ.character z = a + 15 * b - 4 * c ∧
            ρ.character t = a - b ∧
            (c : ℂ) = (ρ.character 1 - ρ.character z) / 16 ∧
            (b : ℂ) = (ρ.character 1 + 3 * ρ.character z - 4 * ρ.character t) / 64 ∧
            (a : ℂ) = (ρ.character 1 + 3 * ρ.character z + 60 * ρ.character t) / 64 ∧
            ρ.character 1 + 3 * ρ.character z + 60 * ρ.character t = 64 * a) ∧
        (ρ.IsIrreducible → ρ.character ≠ 1 → 1 ≤ c ∧ 12 ≤ Module.finrank ℂ V) := by
  classical
  obtain ⟨-, -, hsq, hZcard, -, -, -, -, -, -, -, -⟩ :=
    lyons_unitary_four_fusion_and_centralizers hnonab hT S U hSU
  have hshape := unitaryFourSylowShape_of_mulEquiv hT S U hSU
  refine ⟨hshape.card_nonprincipalLinearCharacters, hshape.card_degreeFourCharacters,
    fun V _ _ _ ρ => ?_⟩
  obtain ⟨m, hm, hminv⟩ := restriction_multiplicities (S : Subgroup G) ρ
  obtain ⟨b, hb⟩ := linear_multiplicity_const_of_order_fifteen hnonab hT S U hSU hd m hminv
  obtain ⟨c, hc⟩ := degreeFour_multiplicity_const hnonab hT S U hSU m hminv
  set a := m 1 with ha
  have hformula : ∀ x : (S : Subgroup G), ρ.character x =
      a + b * ∑ θ ∈ nonprincipalLinearCharacters (S : Subgroup G), θ x +
        c * ∑ θ ∈ degreeFourCharacters (S : Subgroup G), θ x := by
    intro x
    have hL : ∑ θ ∈ nonprincipalLinearCharacters (S : Subgroup G), (m θ : ℂ) * θ x =
        ∑ θ ∈ nonprincipalLinearCharacters (S : Subgroup G), (b : ℂ) * θ x :=
      Finset.sum_congr rfl fun θ hθ => by rw [hb θ hθ]
    have hP : ∑ θ ∈ degreeFourCharacters (S : Subgroup G), (m θ : ℂ) * θ x =
        ∑ θ ∈ degreeFourCharacters (S : Subgroup G), (c : ℂ) * θ x :=
      Finset.sum_congr rfl fun θ hθ => by rw [hc θ hθ]
    rw [hm x, hshape.irreducibleCharacters_eq,
      Finset.sum_insert one_not_mem_linear_union_degreeFour,
      Finset.sum_union disjoint_linear_degreeFour, hL, hP, ← Finset.mul_sum, ← Finset.mul_sum]
    simp only [Pi.one_apply, mul_one]
    rw [ha]
    ring
  obtain ⟨z₀, hz₀, hz₀1⟩ := exists_mem_map_center_ne_one hT S U hSU
  obtain ⟨w₀, hw₀, rfl⟩ := hz₀
  have hw₀1 : w₀ ≠ 1 := fun h => hz₀1 (by rw [h]; rfl)
  have hw₀' : w₀ ∈ Subgroup.center (S : Subgroup G) := hw₀
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : (S : Subgroup G), t₀ ∉ Subgroup.center (S : Subgroup G) := by
    by_contra hall
    push Not at hall
    have htop : Subgroup.center (S : Subgroup G) = ⊤ := eq_top_iff.mpr fun x _ => hall x
    have h1 := hshape.card_center
    rw [htop, Subgroup.card_top, hshape.card] at h1
    norm_num at h1
  have ht₀1 : t₀ ≠ 1 := fun h => ht₀ (h ▸ Subgroup.one_mem _)
  have hval : ∀ (a' b' c' : ℕ), (∀ x : (S : Subgroup G), ρ.character x =
      a' + b' * ∑ θ ∈ nonprincipalLinearCharacters (S : Subgroup G), θ x +
        c' * ∑ θ ∈ degreeFourCharacters (S : Subgroup G), θ x) →
      ρ.character 1 = a' + 15 * b' + 12 * c' ∧
        ρ.character ((w₀ : (S : Subgroup G)) : G) = a' + 15 * b' - 4 * c' ∧
        ρ.character (t₀ : G) = a' - b' := by
    intro a' b' c' h
    refine ⟨?_, ?_, ?_⟩
    · have h1 := h 1
      rw [hshape.sum_linear, ite_eq_left (Subgroup.one_mem _), hshape.sum_degreeFour,
        ite_eq_left rfl] at h1
      rw [show (1 : G) = ((1 : (S : Subgroup G)) : G) from rfl, h1]
      ring
    · have h1 := h w₀
      rw [hshape.sum_linear, ite_eq_left hw₀', hshape.sum_degreeFour, ite_eq_right hw₀1,
        ite_eq_left hw₀'] at h1
      rw [h1]
      ring
    · have h1 := h t₀
      rw [hshape.sum_linear, ite_eq_right ht₀, hshape.sum_degreeFour, ite_eq_right ht₀1,
        ite_eq_right ht₀] at h1
      rw [h1]
      ring
  refine ⟨a, b, c, hformula, fun a' b' c' h' => ?_, fun z hz hz1 t ht ht4 => ?_, ?_⟩
  · obtain ⟨e1, e2, e3⟩ := hval a b c hformula
    obtain ⟨e1', e2', e3'⟩ := hval a' b' c' h'
    have hc' : (c' : ℂ) = c := by linear_combination (e1 - e2 - e1' + e2') / 16
    have hb' : (b' : ℂ) = b := by
      linear_combination (e1 + 3 * e2 - 4 * e3 - e1' - 3 * e2' + 4 * e3') / 64
    have ha' : (a' : ℂ) = a := by
      linear_combination (e1 + 3 * e2 + 60 * e3 - e1' - 3 * e2' - 60 * e3') / 64
    exact ⟨by exact_mod_cast ha', by exact_mod_cast hb', by exact_mod_cast hc'⟩
  · obtain ⟨w, hw, rfl⟩ := hz
    have hw1 : w ≠ 1 := fun h => hz1 (by rw [h]; rfl)
    have hw' : w ∈ Subgroup.center (S : Subgroup G) := hw
    set t' : (S : Subgroup G) := ⟨t, ht⟩ with ht'
    have ht'Z : t' ∉ Subgroup.center (S : Subgroup G) := by
      intro h
      have h2 := congrArg Subtype.val ((hshape.sq_eq_one_iff t').mpr h)
      rw [Subgroup.coe_pow] at h2
      have h3 := orderOf_dvd_of_pow_eq_one h2
      rw [ht4] at h3
      norm_num at h3
    have ht'1 : t' ≠ 1 := fun h => ht'Z (h ▸ Subgroup.one_mem _)
    have e1 : ρ.character 1 = a + 15 * b + 12 * c := by
      have h1 := hformula 1
      rw [hshape.sum_linear, ite_eq_left (Subgroup.one_mem _), hshape.sum_degreeFour,
        ite_eq_left rfl] at h1
      rw [show (1 : G) = ((1 : (S : Subgroup G)) : G) from rfl, h1]
      ring
    have e2 : ρ.character (w : G) = a + 15 * b - 4 * c := by
      have h1 := hformula w
      rw [hshape.sum_linear, ite_eq_left hw', hshape.sum_degreeFour, ite_eq_right hw1,
        ite_eq_left hw'] at h1
      rw [h1]
      ring
    have e3 : ρ.character t = a - b := by
      have h1 := hformula t'
      rw [hshape.sum_linear, ite_eq_right ht'Z, hshape.sum_degreeFour, ite_eq_right ht'1,
        ite_eq_right ht'Z] at h1
      rw [show t = (t' : G) from rfl, h1]
      ring
    simp only [Subgroup.coe_subtype]
    refine ⟨e1, e2, e3, ?_, ?_, ?_, ?_⟩
    · rw [e1, e2]
      ring
    · rw [e1, e2, e3]
      ring
    · rw [e1, e2, e3]
      ring
    · rw [e1, e2, e3]
      ring
  · intro hirr hne
    obtain ⟨e1, -, -⟩ := hval a b c hformula
    have hdeg : (Module.finrank ℂ V : ℂ) = a + 15 * b + 12 * c :=
      (Representation.char_one ρ).symm.trans e1
    have hdegN : Module.finrank ℂ V = a + 15 * b + 12 * c := by exact_mod_cast hdeg
    have hc1 : 1 ≤ c := by
      by_contra hlt
      push Not at hlt
      have hc0 : c = 0 := by omega
      set Z := (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype with hZ
      have hZker : Z ≤ MonoidHom.ker ρ := by
        apply le_ker_of_character_eq_degree ρ Z
        rintro _ ⟨w, hw, rfl⟩
        have hw' : w ∈ Subgroup.center (S : Subgroup G) := hw
        have h1 := hformula w
        change ρ.character (w : G) = ρ.character 1
        rw [h1, e1, hc0, hshape.sum_linear, ite_eq_left hw']
        push_cast
        ring
      have hZbot : Z ≠ ⊥ := by
        intro h
        have hcard : Nat.card Z = 4 := by
          rw [hZ, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hZcard]
        rw [h, Subgroup.card_bot] at hcard
        norm_num at hcard
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.ker ρ) with hk | hk
      · exact hZbot (le_bot_iff.mp (hk ▸ hZker))
      · apply hne
        have htriv : ∀ g : G, ρ g = 1 := by
          intro g
          have : g ∈ MonoidHom.ker ρ := by rw [hk]; exact Subgroup.mem_top g
          exact this
        let data : FiniteComplexRepresentation.{0, 0} G :=
          { vector := V, representation := ρ }
        have hone : Module.finrank ℂ V = 1 :=
          finrank_eq_one_of_commutator_trivial data hirr (fun g h => by
            change ρ g * ρ h = ρ h * ρ g
            rw [htriv g, htriv h])
        funext g
        change LinearMap.trace ℂ V (ρ g) = 1
        rw [htriv g, LinearMap.trace_one, hone]
        norm_num
    exact ⟨hc1, by omega⟩

end Node

end CFSG.LyonsUnitaryFour
