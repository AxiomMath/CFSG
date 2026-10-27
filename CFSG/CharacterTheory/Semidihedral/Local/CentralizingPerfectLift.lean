module

public import CFSG.CharacterTheory.Semidihedral.Local.LayerCoveringCentralizer
public import CFSG.CharacterTheory.Wreathed.PrimewisePerfectLift

public section

open scoped Pointwise

namespace CFSG.Semidihedral.Local

open CFSG.Open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
  CFSG.Wreathed.PrimewisePerfectLift

theorem mul_pow_orderOf_eq_of_involution {X : Type*} [Group X] {t a : X} (ht : t ^ 2 = 1)
    (hta : Commute t a) (hd : Odd (orderOf a)) : (t * a) ^ orderOf a = t := by
  rw [hta.mul_pow, pow_orderOf_eq_one, mul_one]
  obtain ⟨m, hm⟩ := hd
  rw [hm, pow_succ, pow_mul, ht, one_pow, one_mul]

theorem all_local_prime_centralizer_covers_produce_actual_centralizing_perfect_lift {G : Type}
    [Group G] [Finite G] (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    let L := CFSG.generalizedFitting (Gamma t)
    let T₀ := L.comap (barKappa t)
    let Y := T₀.comap (nu t)
    let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
    let J := (CFSG.perfectResidual H₀).map H₀.subtype
    let E := J ⊓ N t
    let Concl : Prop :=
      Group.IsPerfect J ∧ J.Normal ∧ tInC t ∈ J ∧ J.map (nu t) = T₀ ∧ ⁅J, N t⁆ = ⊥ ∧
      Y = J ⊔ N t ∧ Odd (Nat.card E) ∧
      (Subgroup.center J).map J.subtype = E ⊔ Subgroup.zpowers (tInC t) ∧
      E ⊓ Subgroup.zpowers (tInC t) = ⊥ ∧ ⁅E, Subgroup.zpowers (tInC t)⁆ = ⊥ ∧
      (∃ φ : J ⧸ E.subgroupOf J ≃* T₀,
        ∀ x : J, (φ (x : J ⧸ E.subgroupOf J) : H t) = nu t x) ∧
      (∃ ψ : J ⧸ Subgroup.center J ≃* L,
        ∀ x : J, (ψ (x : J ⧸ Subgroup.center J) : Gamma t) = kappa t x) ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F)
          (eta : T₀ ≃* Matrix.SpecialLinearGroup (Fin 2) F)
          (π : J →* Matrix.SpecialLinearGroup (Fin 2) F),
        Nat.card F = p ^ f ∧ (∀ h : nu t (tInC t) ∈ T₀, eta ⟨nu t (tInC t), h⟩ = -1) ∧
        (∀ (x : J) (h : nu t x ∈ T₀), π x = eta ⟨nu t x, h⟩) ∧ Function.Surjective π ∧
        π.ker = E.subgroupOf J) ∧
      H₀ = J ⊔ (Subgroup.center (N t)).map (N t).subtype ∧ ⁅H₀, H₀⁆ = J ∧
      ∀ J₁ : Subgroup (C t), J₁ ≤ Y → Group.IsPerfect J₁ → ⁅J₁, N t⁆ = ⊥ →
        J₁.map (nu t) = T₀ → J₁ = J
    ((∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ Nat.card (N t) → ∃ P : Sylow ℓ (N t),
        (Subgroup.centralizer (((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t)) :
          Set (C t)) ⊓ Y).map (nu t) = T₀) → Concl) ∧
    ((∃ s : C t, orderOf s = 2 ∧ s ≠ tInC t ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ Nat.card (N t) →
        ∃ P : Sylow ℓ (N t), s ∈ Subgroup.normalizer
          (((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t)) : Set (C t)) ∧
          ((∀ x : N t, x ∈ P → s * (x : C t) * s⁻¹ = x) ∨
            (∀ x : N t, x ∈ P → s * (x : C t) * s⁻¹ = (x : C t)⁻¹))) → Concl) := by
  intro L T₀ Y H₀ J E Concl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, hF, hFfin, A, rho, data⟩ := actual_simple_layer_matrix_data n hn S0 f0 hG t ht
    hnonab hcentral hnc p f hp hpodd hf hmodel
  obtain ⟨eta, hetat, -, -⟩ := data.compatible_layer
  obtain ⟨-, -, -, hzcenter, -, -, -⟩ := actual_quotient_inputs n hn S0 f0 hG t ht
  have hT₀perf : Group.IsPerfect T₀ := by
    have : Fintype F := Fintype.ofFinite F
    have h4 : ∃ s : Finset F, s.card = 4 := by
      obtain ⟨u, -, hu⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
        (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, data.field_card]; omega)
      exact ⟨u, hu⟩
    have := CFSG.LinearGroups.special_linear_dimension_two_perfect h4
    exact Group.IsPerfect.ofSurjective (f := eta.symm.toMonoidHom) eta.symm.surjective
  have hLnormal : L.Normal := (CFSG.LocalCores.generalized_fitting_characteristic).2
  have hT₀normal : T₀.Normal := hLnormal.comap _
  have hNodd : Odd (Nat.card (N t)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))
  let κ₀ : T₀ →* L := ((barKappa t).comp T₀.subtype).codRestrict L fun x => x.2
  have hκ₀ : ∀ x : T₀, (κ₀ x : Gamma t) = barKappa t x := fun x => rfl
  have hκ₀surj : Function.Surjective κ₀ := by
    intro l
    obtain ⟨x, hx⟩ := barKappa_surjective t (l : Gamma t)
    have hxT : x ∈ T₀ := by
      change barKappa t x ∈ L
      rw [hx]
      exact l.2
    exact ⟨⟨x, hxT⟩, Subtype.ext hx⟩
  have hkerκ : ∀ x : H t, barKappa t x = 1 ↔ x ∈ Subgroup.zpowers (nu t (tInC t)) := by
    intro x
    rw [← barKappa_kernel t]
    exact Iff.rfl
  have hcentΓ : ∀ g : Gamma t, g ∈ L → (∀ l ∈ L, l * g = g * l) → g = 1 := by
    intro g _ hg
    have hmem : g ∈ Subgroup.centralizer (L : Set (Gamma t)) :=
      Subgroup.mem_centralizer_iff.mpr hg
    rw [hcentral] at hmem
    exact (Subgroup.mem_bot).mp hmem
  have hcenterT₀ : Subgroup.center T₀ = κ₀.ker := by
    ext z
    rw [MonoidHom.mem_ker]
    constructor
    · intro hz
      apply Subtype.ext
      rw [hκ₀]
      apply hcentΓ _ (κ₀ z).2
      intro l hl
      obtain ⟨w, hw⟩ := hκ₀surj ⟨l, hl⟩
      have hzw := (Subgroup.mem_center_iff.mp hz) w
      have h := congrArg (fun y : T₀ => barKappa t y) hzw
      simp only [Subgroup.coe_mul, map_mul] at h
      rw [← hκ₀ w, hw] at h
      exact h
    · intro hz
      have hz' : barKappa t z = 1 := congrArg Subtype.val hz
      rw [hkerκ] at hz'
      have hzc : (z : H t) ∈ Subgroup.center (H t) :=
        (Subgroup.zpowers_le.mpr hzcenter) hz'
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext ((Subgroup.mem_center_iff.mp hzc) w)
  let eL : T₀ ⧸ Subgroup.center T₀ ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hcenterT₀).trans
      (QuotientGroup.quotientKerEquivOfSurjective κ₀ hκ₀surj)
  have hquasi : CFSG.IsQuasisimple T₀ := by
    refine ⟨hT₀perf, eL.isSimpleGroup, ?_⟩
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨eL.symm a, eL.symm b, fun h => hab ?_⟩
    have := congrArg eL h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this
  have hLeven : Even (Nat.card L) := by
    obtain ⟨U⟩ := (inferInstance : Nonempty (Sylow 2 L))
    have hU1 : Nat.card (U : Subgroup L) ≠ 1 := by
      intro h1
      apply hnc U
      rw [Subgroup.card_eq_one] at h1
      rw [h1]
      exact isCyclic_of_subsingleton
    obtain ⟨k, hk⟩ := U.isPGroup'.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hU1 (by rw [hk, pow_zero])
    exact even_iff_two_dvd.mpr ((dvd_pow_self 2 hk0).trans
      (hk ▸ Subgroup.card_subgroup_dvd_card (U : Subgroup L)))
  have heven : Even (Nat.card (T₀ ⧸ Subgroup.center T₀)) := by
    rw [Nat.card_congr eL.toEquiv]
    exact hLeven
  have htcent : ∀ x : C t, tInC t * x = x * tInC t := fun x =>
    ((Subgroup.mem_center_iff.mp (tInC_central t)) x).symm
  have ht2 : tInC t ^ 2 = 1 := by
    apply Subtype.ext
    simp only [tInC, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← ht, pow_orderOf_eq_one]
  have htY : tInC t ∈ Y := by
    change barKappa t (nu t (tInC t)) ∈ L
    rw [(hkerκ _).mpr (Subgroup.mem_zpowers _)]
    exact L.one_mem
  have core : (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ Nat.card (N t) → ∃ P : Sylow ℓ (N t),
      (Subgroup.centralizer (((P : Subgroup (N t)).map (N t).subtype : Subgroup (C t)) :
        Set (C t)) ⊓ Y).map (nu t) = T₀) → Concl := by
    intro hcov
    obtain ⟨hJperf, hJnormal, hJY, hJimage, hJR, hJN, hJRY, -, hEodd, hEJ, -, hH₀, -, hH₀',
        huniq, e, he⟩ :=
      primewise_Sylow_centralizer_coverage_gives_canonical_perfect_lift
        (N t) hNodd T₀ hquasi heven fun ℓ hℓ hdiv => by
          have : Fact ℓ.Prime := ⟨hℓ⟩
          exact hcov ℓ hdiv
    have hnu1 : ∀ y : C t, y ∈ N t → nu t y = 1 := fun y hy => (QuotientGroup.eq_one_iff y).mpr hy
    have htord : orderOf (tInC t) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact ht
    have hNord : ∀ x : C t, x ∈ N t → Odd (orderOf x) := by
      intro x hxN
      have h : orderOf x ∣ Nat.card (N t) := by
        rw [show orderOf x = orderOf (⟨x, hxN⟩ : N t) from Subgroup.orderOf_coe (⟨x, hxN⟩ : N t)]
        exact orderOf_dvd_natCard _
      exact hNodd.of_dvd_nat h
    have hmapJ : ∀ u ∈ T₀, ∃ j ∈ J, nu t j = u := by
      intro u hu
      have huJ : u ∈ J.map (nu t) := by rw [hJimage]; exact hu
      obtain ⟨j, hj, hjeq⟩ := Subgroup.mem_map.mp huJ
      exact ⟨j, hj, hjeq⟩
    have htJ : tInC t ∈ J := by
      obtain ⟨j, hjJ, hj⟩ := hmapJ _ htY
      obtain ⟨a, haN, hja⟩ := (QuotientGroup.mk'_eq_mk' (N t)).mp hj.symm
      have h := mul_pow_orderOf_eq_of_involution ht2 (htcent a) (hNord a haN)
      rw [hja] at h
      rw [← h]
      exact J.pow_mem hjJ _
    have hzJ : Subgroup.zpowers (tInC t) ≤ J := Subgroup.zpowers_le.mpr htJ
    have hkey : ∀ x : C t, x ∈ J → barKappa t (nu t x) = 1 →
        x ∈ E ⊔ Subgroup.zpowers (tInC t) := by
      intro x hxJ hx
      rw [hkerκ, ← MonoidHom.map_zpowers] at hx
      obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp hx
      obtain ⟨z, hzN, hz⟩ := (QuotientGroup.mk'_eq_mk' (N t)).mp hwx
      have hzJ' : z ∈ J := by
        have hz' : z = w⁻¹ * x := by rw [← hz, inv_mul_cancel_left]
        rw [hz']
        exact J.mul_mem (J.inv_mem (hzJ hw)) hxJ
      rw [← hz]
      exact (E ⊔ Subgroup.zpowers (tInC t)).mul_mem (Subgroup.mem_sup_right hw)
        (Subgroup.mem_sup_left ⟨hzJ', hzN⟩)
    have hcenterJ : (Subgroup.center J).map J.subtype = E ⊔ Subgroup.zpowers (tInC t) := by
      apply le_antisymm
      · rintro _ ⟨z, hz, rfl⟩
        apply hkey z z.2
        apply hcentΓ _ (hJY z.2)
        intro l hl
        obtain ⟨u, hu⟩ := hκ₀surj ⟨l, hl⟩
        obtain ⟨j, hjJ, hjeq⟩ := hmapJ u u.2
        have hzj := (Subgroup.mem_center_iff.mp hz) ⟨j, hjJ⟩
        have h := congrArg (fun y : J => barKappa t (nu t y)) hzj
        simp only [Subgroup.coe_mul, map_mul] at h
        have hl' : l = barKappa t (nu t j) := by
          have h2 : barKappa t (u : H t) = l := congrArg Subtype.val hu
          rw [← h2, ← hjeq]
        rw [hl']
        exact h
      · apply sup_le
        · rintro x ⟨hxJ, hxN⟩
          exact ⟨⟨x, hxJ⟩, hEJ (show (⟨x, hxJ⟩ : J) ∈ E.subgroupOf J from ⟨hxJ, hxN⟩), rfl⟩
        · rw [Subgroup.zpowers_le]
          exact ⟨⟨tInC t, htJ⟩,
            Subgroup.mem_center_iff.mpr fun w => Subtype.ext (htcent w).symm, rfl⟩
    have hEt : E ⊓ Subgroup.zpowers (tInC t) = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨⟨-, hxN⟩, hxt⟩
      rw [Subgroup.mem_bot, ← orderOf_eq_one_iff]
      have h1 : orderOf x ∣ 2 := htord ▸ orderOf_dvd_of_mem_zpowers hxt
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
      · exact h
      · have h2 := hNord x hxN
        rw [h] at h2
        exact absurd h2 (by decide)
    have hEtcomm : ⁅E, Subgroup.zpowers (tInC t)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact Commute.zpow_left (htcent x) k
    let κJ : J →* L := ((barKappa t).comp ((nu t).comp J.subtype)).codRestrict L
      fun j => hJY j.2
    have hκJsurj : Function.Surjective κJ := by
      intro l
      obtain ⟨u, hu⟩ := hκ₀surj l
      obtain ⟨j, hjJ, hjeq⟩ := hmapJ u u.2
      refine ⟨⟨j, hjJ⟩, Subtype.ext ?_⟩
      change barKappa t (nu t j) = (l : Gamma t)
      rw [hjeq, ← hu]
      rfl
    have hκJker : Subgroup.center J = κJ.ker := by
      ext x
      rw [MonoidHom.mem_ker]
      constructor
      · intro hx
        have hmem : (x : C t) ∈ E ⊔ Subgroup.zpowers (tInC t) := by
          rw [← hcenterJ]
          exact ⟨x, hx, rfl⟩
        have hle : E ⊔ Subgroup.zpowers (tInC t) ≤ ((barKappa t).comp (nu t)).ker := by
          apply sup_le
          · rintro y ⟨-, hyN⟩
            rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hnu1 y hyN, map_one]
          · rw [Subgroup.zpowers_le, MonoidHom.mem_ker, MonoidHom.comp_apply]
            exact (hkerκ _).mpr (Subgroup.mem_zpowers _)
        exact Subtype.ext (hle hmem)
      · intro hx
        have hx' : barKappa t (nu t x) = 1 := congrArg Subtype.val hx
        have hmem := hkey x x.2 hx'
        rw [← hcenterJ] at hmem
        obtain ⟨y, hy, hyx⟩ := hmem
        have hyx' : y = x := Subtype.ext hyx
        rw [← hyx']
        exact hy
    let ψ : J ⧸ Subgroup.center J ≃* L :=
      (QuotientGroup.quotientMulEquivOfEq hκJker).trans
        (QuotientGroup.quotientKerEquivOfSurjective κJ hκJsurj)
    let νJ : J →* T₀ := ((nu t).comp J.subtype).codRestrict T₀ fun j => hJY j.2
    have hνJsurj : Function.Surjective νJ := by
      intro u
      obtain ⟨j, hjJ, hjeq⟩ := hmapJ u u.2
      exact ⟨⟨j, hjJ⟩, Subtype.ext hjeq⟩
    let π : J →* Matrix.SpecialLinearGroup (Fin 2) F := eta.toMonoidHom.comp νJ
    have hπker : π.ker = E.subgroupOf J := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        have hx1 : νJ x = 1 := by
          apply eta.injective
          rw [map_one]
          exact hx
        have hx' : nu t x = 1 := congrArg Subtype.val hx1
        exact ⟨x.2, (QuotientGroup.eq_one_iff (x : C t)).mp hx'⟩
      · rintro ⟨-, hxN⟩
        have hx1 : νJ x = 1 := Subtype.ext (hnu1 _ hxN)
        change eta (νJ x) = 1
        rw [hx1, map_one]
    exact ⟨hJperf, hJnormal, htJ, hJimage, hJN, hJRY.symm, hEodd, hcenterJ, hEt, hEtcomm,
      ⟨e, he⟩, ⟨ψ, fun x => rfl⟩,
      ⟨F, hF, hFfin, eta, π, data.field_card, fun _ => hetat, fun _ _ => rfl,
        eta.surjective.comp hνJsurj, hπker⟩, hH₀, hH₀',
      fun J₁ hJ₁Y hJ₁perf hJ₁N hJ₁img => huniq J₁ hJ₁perf hJ₁Y hJ₁img
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJ₁N)⟩
  refine ⟨core, fun ⟨s, hs, hst, halt⟩ => core fun ℓ _ hℓ => ?_⟩
  obtain ⟨P, hsP, hact⟩ := halt ℓ hℓ
  exact ⟨P, centralized_or_inverted_local_sylow_prime_has_layer_covering_centralizer n hn S0 f0
    hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel s hs hst ℓ hℓ P hsP hact⟩

end CFSG.Semidihedral.Local
