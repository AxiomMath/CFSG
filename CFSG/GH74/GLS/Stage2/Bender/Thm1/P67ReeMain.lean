module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67ReeAut
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67ReePlane
public import CFSG.GH74.GLS.Stage2.OddAut.FixedCore
public import CFSG.GH74.GLS.Stage2.OddAut.OutCyc
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FRee
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Mult
public import CFSG.RankThree.Chevalley.SteinbergCFSmallReeComponentCores
public import CFSG.LieType.Steinberg.CentralExt.SmallReeMultiplier

public section

open CFSG.ComponentClassification.LiteratureLocal.SmallRee CFSG.LieType.Ree
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Walter.Ree.Model
  CFSG.GH74.GLS.Stage2.OddAut CFSG.LieType.BorelTits CFSG.GH74.GLS.Stage2.Signalizer.Odd87

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

section ReeMain

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem ree_holds : Holds (ReeTag.G2.reeGamma K a) 3 := by
  have h := holds_reeFixedGroup (t := ReeTag.G2) (K := K) (a := a)
  rw [← ReeTag.reeGamma_eq_reeFixedGroup] at h
  exact h

theorem ree_false_of_rp (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1))
    {V Z : Subgroup (MulAut (ReeTag.G2.reeGamma K a))}
    (h2 : N2Cfg (ReeTag.G2.reeGamma K a) 3 V Z) (h3 : N3Full (ReeTag.G2.reeGamma K a) V Z) :
    False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (ReeTag.G2.reeGamma K a) := finite_reeGamma
  obtain ⟨-, -, hVe, hVc, -⟩ := id h2
  have := hVe
  have hcen : Subgroup.center (ReeTag.G2.reeGamma K a) = ⊥ := ReeTag.center_reeGamma_G2_eq_bot hK
  obtain ⟨hcyc, -⟩ := outer_reeGamma_cyclic ha hK
  have : IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (ReeTag.G2.reeGamma K a)) := hcyc
  obtain ⟨v, hvV, hv1, hΘ⟩ := exists_mem_ker_of_isCyclic (r := 3)
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (ReeTag.G2.reeGamma K a))) hVc
  have hvinn : v ∈ (MulAut.conj : ReeTag.G2.reeGamma K a →*
      MulAut (ReeTag.G2.reeGamma K a)).range := (QuotientGroup.eq_one_iff v).1 hΘ
  exact false_of_rp_data ree_holds hcen (ree_pCharData ha hK) (fun x _ => Subgroup.mem_top _)
    le_top le_top h2 h3 ⟨v, hvV, hv1, hvinn⟩

theorem reeGammaFieldAut_uIn (hK : Nat.card K = 3 ^ (2 * a + 1)) (σ : K ≃+* K) (t b c : K) :
    ReeTag.G2.reeGammaFieldAut K a σ (uIn hK t b c) = uIn hK (σ t) (σ b) (σ c) := by
  apply Subtype.ext
  rw [ReeTag.coe_reeGammaFieldAut, uIn_val, uIn_val]
  exact entrywise_smallReeCoord σ.toRingHom t b c

theorem reeGammaFieldAut_longestIn (σ : K ≃+* K) {w₀ : WeylGroup ReeTag.G2.tag}
    (hw₀ : ∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤
      (coxeterSystem ReeTag.G2.tag).length w₀) :
    ReeTag.G2.reeGammaFieldAut K a σ (longestIn a K hw₀) = longestIn a K hw₀ := by
  apply Subtype.ext
  rw [ReeTag.coe_reeGammaFieldAut]
  exact entrywise_canonicalRep σ w₀

theorem ree_false_of_large (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1)) {r : ℕ}
    (hr3 : 3 < r) {V Z : Subgroup (MulAut (ReeTag.G2.reeGamma K a))}
    (h2 : N2Cfg (ReeTag.G2.reeGamma K a) r V Z) (h3 : N3Full (ReeTag.G2.reeGamma K a) V Z) :
    False := by
  classical
  have : Finite (ReeTag.G2.reeGamma K a) := finite_reeGamma
  have hcen : Subgroup.center (ReeTag.G2.reeGamma K a) = ⊥ := ReeTag.center_reeGamma_G2_eq_bot hK
  obtain ⟨hr, hrodd, hVe, hVc, -⟩ := id h2
  have := hVe
  have : Fact r.Prime := ⟨hr⟩
  have hinj : Function.Injective
      (MulAut.conj : ReeTag.G2.reeGamma K a →* MulAut (ReeTag.G2.reeGamma K a)) :=
    mulAut_conj_injective_of_center_bot hcen
  by_cases hVinn : ∀ v ∈ V, v ∈
      (MulAut.conj : ReeTag.G2.reeGamma K a →* MulAut (ReeTag.G2.reeGamma K a)).range
  ·
    set E : Subgroup (ReeTag.G2.reeGamma K a) :=
      V.comap (MulAut.conj : ReeTag.G2.reeGamma K a →* MulAut (ReeTag.G2.reeGamma K a)) with hE
    have hEmap : E.map (MulAut.conj : ReeTag.G2.reeGamma K a →*
        MulAut (ReeTag.G2.reeGamma K a)) = V := by
      rw [hE, Subgroup.map_comap_eq]
      exact inf_eq_right.2 (fun v hv => hVinn v hv)
    let e : E ≃* V := (Subgroup.equivMapOfInjective E (MulAut.conj : ReeTag.G2.reeGamma K a →*
      MulAut (ReeTag.G2.reeGamma K a)) hinj).trans (MulEquiv.subgroupCongr hEmap)
    refine ree_no_plane ha hK hr hr3 E ?_ ?_
    · exact CFSG.RankThree.Chevalley.isElementaryAbelian_of_injective (p := r)
        e.toMonoidHom e.injective
    · rw [Nat.card_congr e.toEquiv]
      exact hVc
  · push Not at hVinn
    obtain ⟨φ, hφV, hφinn⟩ := hVinn
    have hφ1 : φ ≠ 1 := fun h => hφinn (h ▸ one_mem _)
    have hφr : φ ^ r = 1 := elemPow_eq_one_of_isElementaryAbelian φ hφV
    have hφord : orderOf φ = r := orderOf_eq_prime hφr hφ1
    obtain ⟨hrf, δ, σ, -, hδ, hkc, -⟩ := CFSG.RankThree.small_Ree_large_prime_field_coset_descent
      a ha K hK hr hr3 φ hφord hφinn
    obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
    refine false_of_fixed_core hcen h2 h3 hφV hφ1 ?_ ?_
    · intro F₀ hF₀n hF₀c
      have hsolv : Group.IsSolvable F₀ := by
        have : IsMulCommutative F₀ := ⟨⟨hF₀c⟩⟩
        infer_instance
      exact CFSG.RankThree.Chevalley.smallRee_fixed_radical_of_not_inner ha hK hr hr3 φ hφord
        hφinn F₀ hF₀n hsolv
    · intro ζ hζodd hζcop hζφ hζfix
      have hfixσ : ∀ x : ReeTag.G2.reeGamma K a, ReeTag.G2.reeGammaFieldAut K a σ x = x →
          (δ * ζ * δ⁻¹) x = x := by
        intro x hx
        have hδx : φ (δ⁻¹ x) = δ⁻¹ x := by
          have h1 : (δ * φ * δ⁻¹) x = x := by rw [hδ]; exact hx
          simp only [MulAut.mul_apply] at h1
          have h2 : δ⁻¹ (δ (φ (δ⁻¹ x))) = δ⁻¹ x := by rw [h1]
          rwa [MulAut.inv_apply_self] at h2
        have hζx := hζfix (δ⁻¹ x) hδx
        simp only [MulAut.mul_apply]
        rw [hζx, MulAut.apply_inv_self]
      have hord : orderOf (δ * ζ * δ⁻¹) = orderOf ζ := by
        have := (MulEquiv.orderOf_eq (MulAut.conj δ) ζ)
        rwa [MulAut.conj_apply] at this
      have h1 : δ * ζ * δ⁻¹ = 1 := by
        refine ree_aut_trivial_of_fix_subfield hK ha hrf hkc hw₀ (fun t ht => ?_)
          (hfixσ _ (reeGammaFieldAut_longestIn σ hw₀)) (by rw [hord]; exact hζcop)
        exact hfixσ _ (by rw [reeGammaFieldAut_uIn hK, ht, map_zero])
      have h2 : ζ = δ⁻¹ * (δ * ζ * δ⁻¹) * δ := by group
      rw [h2, h1]
      group

end ReeMain

theorem cf67CoreFull_Ree (Y : Type) [Group Y] [Finite Y] (hY : FRee Y) : CF67CoreFull Y := by
  obtain ⟨f, hRee⟩ := reeTitsModel_of_FRee hY
  obtain ⟨a, K, _, _, _, ha, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.Chevalley.exists_mulEquiv_reeGamma_G2_of_reeTitsModel hRee
  refine CF67CoreFull.of_mulEquiv e ?_
  intro hs hn r V Z h2 h3
  obtain ⟨hr, hrodd, -⟩ := id h2
  by_cases hr3 : r = 3
  · subst hr3
    exact ree_false_of_rp ha hK h2 h3
  · have h2r := hr.two_le
    have : r ≠ 2 := by
      rintro rfl
      exact absurd hrodd (by decide)
    exact ree_false_of_large ha hK (by omega) h2 h3

theorem ree_card_center_eq_one {J : Type} [Group J] [Finite J] (hJ : CFSG.IsQuasisimple J)
    (hY : FRee (J ⧸ Subgroup.center J)) : Nat.card (Subgroup.center J) = 1 := by
  obtain ⟨f, hRee⟩ := reeTitsModel_of_FRee hY
  obtain ⟨a, K, _, _, _, ha, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.Chevalley.exists_mulEquiv_reeGamma_G2_of_reeTitsModel hRee
  have hZ : Subgroup.center (ReeTag.G2.reeGamma K a) = ⊥ := ReeTag.center_reeGamma_G2_eq_bot hK
  let e' : (J ⧸ Subgroup.center J) ≃* (ReeTag.G2.reeGamma K a ⧸
      Subgroup.center (ReeTag.G2.reeGamma K a)) :=
    e.trans ((QuotientGroup.quotientBot (G := ReeTag.G2.reeGamma K a)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ.symm))
  obtain ⟨-, hsub⟩ := CFSG.LieType.Steinberg.CentralExt.SmallReeClosed.smallRee_hopfMultiplier
    hK ha
  have : Finite (CFSG.Open.griessHopfMultiplier (ReeTag.G2.reeGamma K a ⧸
      Subgroup.center (ReeTag.G2.reeGamma K a))) := Finite.of_subsingleton
  have h1 := card_center_dvd_hopf hJ e'
  have := hsub
  have hcard : Nat.card (CFSG.Open.griessHopfMultiplier (ReeTag.G2.reeGamma K a ⧸
      Subgroup.center (ReeTag.G2.reeGamma K a))) = 1 := Nat.card_of_subsingleton 1
  rw [hcard] at h1
  exact Nat.dvd_one.1 h1

theorem cf67Ree_thm : CF67Ree :=
  cf67Fam_of_core (fun Y _ _ hY => cf67CoreFull_Ree Y hY)
    (fun _ _ _ hJ hY r hr _ hd => by
      have h1 := ree_card_center_eq_one hJ hY
      rw [h1] at hd
      exact absurd (Nat.le_of_dvd one_pos hd) (by have := hr.two_le; omega))

end CFSG.GH74.GLS.Stage2.Bender.Thm1
