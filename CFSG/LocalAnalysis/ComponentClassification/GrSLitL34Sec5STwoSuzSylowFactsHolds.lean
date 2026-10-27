module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SSuzSylowFactsHolds
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.SylowFactsModel

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.EvenSporadicStandard

theorem twoSuzSylowFacts_of_model
    (hmodel : IsElemTwo (zGammaThree TwoSuz.Ssub) ∧
      Nat.card (zGammaThree TwoSuz.Ssub) = 32 ∧
      ∃ Q : Subgroup TwoSuz.GL12, Q ≤ TwoSuz.Ssub ∧ IsElemTwo Q ∧ Nat.card Q = 8 ∧
        (TwoSuz.Lhat : Subgroup TwoSuz.GL12) ≤ TwoSuz.Ssub ⊔
          ((TwoSuz.Lhat : Subgroup TwoSuz.GL12) ⊓
            Subgroup.centralizer (Q : Set TwoSuz.GL12))) :
    TwoSuzSylowFacts := by
  intro X _ _ hperf hZ hX R
  haveI : Group.IsPerfect X := hperf
  obtain ⟨e⟩ := CFSG.EvenSporadicStandard.Solomon78.suz_equiv_of_isSporadic hX
  let q : X →* CFSG.Sporadic.SuzOddCore.suzM :=
    e.toMonoidHom.comp (QuotientGroup.mk' (center X))
  have hq : Function.Surjective q :=
    e.surjective.comp (QuotientGroup.mk'_surjective (center X))
  have hker : q.ker = center X := by
    ext x
    rw [MonoidHom.mem_ker]
    show e (QuotientGroup.mk x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  obtain ⟨x, y, hxy, -⟩ := Nat.card_eq_two_iff.mp hZ
  have ht_exists : ∃ t : center X, t ≠ 1 := by
    by_cases hx : x = 1
    · exact ⟨y, fun hy => hxy (hx.trans hy.symm)⟩
    · exact ⟨x, hx⟩
  obtain ⟨t, ht_ne⟩ := ht_exists
  let tX : X := (t : center X)
  have htX_mem : tX ∈ center X := t.2
  have htX_ne : tX ≠ 1 := fun h => ht_ne (Subtype.ext h)
  have ht2 : orderOf tX = 2 := by
    have hdvd := Subgroup.orderOf_dvd_natCard (center X) htX_mem
    rw [hZ] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h (fun h1 => htX_ne (orderOf_eq_one_iff.mp h1))
    · exact h
  have hzpow : Subgroup.zpowers tX = center X := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr htX_mem) ?_
    rw [Nat.card_zpowers, ht2, hZ]
  have hkerT : q.ker = Subgroup.zpowers tX := by
    rw [hker, hzpow]
  obtain ⟨φ, ψ, hφ, hψ, -, hψφ, -⟩ :=
    TwoSuz.exists_embedding q hq ht2 hkerT (Subgroup.zpowers_le.mpr htX_mem)
  have hψrange : ψ.range = (TwoSuz.Lhat : Subgroup TwoSuz.GL12) := by
    have h1 : (ψ.comp φ).range = (TwoSuz.Lhat : Subgroup TwoSuz.GL12) := by
      rw [hψφ]
    rwa [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hφ, Subgroup.map_top] at h1
  let eX : X ≃* ↥(TwoSuz.Lhat : Subgroup TwoSuz.GL12) :=
    (MonoidHom.ofInjective hψ).trans (MulEquiv.subgroupCongr hψrange)
  have hcardX : Nat.card X = 2 * 448345497600 := by
    have hquot : Nat.card (X ⧸ center X) = 448345497600 := by
      rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.SuzOddCore.suzM_card]
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center X), hZ, hquot, Nat.mul_comm]
  have hcardLhat : Nat.card ↥(TwoSuz.Lhat : Subgroup TwoSuz.GL12) = Nat.card X :=
    (Nat.card_congr eX.toEquiv).symm
  have hfac : (Nat.card ↥(TwoSuz.Lhat : Subgroup TwoSuz.GL12)).factorization 2 = 14 := by
    rw [hcardLhat, hcardX]
    show (2 * 448345497600 : ℕ).factorization 2 = 14
    rw [show (2 * 448345497600 : ℕ) = 2 ^ 14 * 54729675 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  let R₀' : Subgroup ↥(TwoSuz.Lhat : Subgroup TwoSuz.GL12) :=
    TwoSuz.Ssub.subgroupOf (TwoSuz.Lhat : Subgroup TwoSuz.GL12)
  have hR₀'card : Nat.card R₀' = 2 ^ 14 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe TwoSuz.Ssub_le_Lhat).toEquiv,
      TwoSuz.Ssub_card]
  have hcardSyl : Nat.card R₀' =
      2 ^ (Nat.card ↥(TwoSuz.Lhat : Subgroup TwoSuz.GL12)).factorization 2 := by
    rw [hR₀'card, hfac]
  let R₀s : Sylow 2 ↥(TwoSuz.Lhat : Subgroup TwoSuz.GL12) := Sylow.ofCard R₀' hcardSyl
  have hR₀scoe : (R₀s : Subgroup ↥(TwoSuz.Lhat : Subgroup TwoSuz.GL12)) = R₀' :=
    Sylow.coe_ofCard R₀' hcardSyl
  obtain ⟨hzel, hzcard, Q₀, hQ₀le, hQ₀el, hQ₀card, hQ₀sup⟩ := hmodel
  have hR₀'map : R₀'.map (TwoSuz.Lhat : Subgroup TwoSuz.GL12).subtype = TwoSuz.Ssub := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr TwoSuz.Ssub_le_Lhat]
  have hzmap : (zGammaThree R₀').map (TwoSuz.Lhat : Subgroup TwoSuz.GL12).subtype =
      zGammaThree TwoSuz.Ssub := by
    rw [map_zGammaThree_of_injOn (TwoSuz.Lhat : Subgroup TwoSuz.GL12).subtype
      (Set.injOn_of_injective (f := (TwoSuz.Lhat : Subgroup TwoSuz.GL12).subtype)
        (TwoSuz.Lhat : Subgroup TwoSuz.GL12).subtype_injective), hR₀'map]
  have hzel' : IsElemTwo (zGammaThree R₀') := by
    have h : IsElemTwo ((zGammaThree R₀').map
        (TwoSuz.Lhat : Subgroup TwoSuz.GL12).subtype) := by
      rw [hzmap]
      exact hzel
    have h2 := isElemTwo_comap_of_injective (TwoSuz.Lhat : Subgroup TwoSuz.GL12).subtype
      (TwoSuz.Lhat : Subgroup TwoSuz.GL12).subtype_injective h
    rwa [Subgroup.comap_map_eq,
      (MonoidHom.ker_eq_bot_iff (TwoSuz.Lhat : Subgroup TwoSuz.GL12).subtype).mpr
        (TwoSuz.Lhat : Subgroup TwoSuz.GL12).subtype_injective, sup_bot_eq] at h2
  have hzcard' : Nat.card (zGammaThree R₀') = 32 := by
    calc Nat.card (zGammaThree R₀') = Nat.card ((zGammaThree R₀').map
          (TwoSuz.Lhat : Subgroup TwoSuz.GL12).subtype) :=
          (Subgroup.card_map_of_injective (K := zGammaThree R₀')
            (TwoSuz.Lhat : Subgroup TwoSuz.GL12).subtype_injective).symm
      _ = Nat.card (zGammaThree TwoSuz.Ssub) := by rw [hzmap]
      _ = 32 := hzcard
  let Q' : Subgroup ↥(TwoSuz.Lhat : Subgroup TwoSuz.GL12) :=
    Q₀.subgroupOf (TwoSuz.Lhat : Subgroup TwoSuz.GL12)
  have hQ'map : Q'.map (TwoSuz.Lhat : Subgroup TwoSuz.GL12).subtype = Q₀ := by
    rw [Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (hQ₀le.trans TwoSuz.Ssub_le_Lhat)]
  have hQ'le : Q' ≤ (R₀s : Subgroup ↥(TwoSuz.Lhat : Subgroup TwoSuz.GL12)) := by
    rw [hR₀scoe]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hQ₀le (Subgroup.mem_subgroupOf.mp hx))
  have hQ'el : IsElemTwo Q' := by
    have h : IsElemTwo (Q'.map (TwoSuz.Lhat : Subgroup TwoSuz.GL12).subtype) := by
      rw [hQ'map]
      exact hQ₀el
    have h2 := isElemTwo_comap_of_injective (TwoSuz.Lhat : Subgroup TwoSuz.GL12).subtype
      (TwoSuz.Lhat : Subgroup TwoSuz.GL12).subtype_injective h
    rwa [Subgroup.comap_map_eq,
      (MonoidHom.ker_eq_bot_iff (TwoSuz.Lhat : Subgroup TwoSuz.GL12).subtype).mpr
        (TwoSuz.Lhat : Subgroup TwoSuz.GL12).subtype_injective, sup_bot_eq] at h2
  have hQ'card : Nat.card Q' = 8 := by
    calc Nat.card Q' = Nat.card (Q'.map (TwoSuz.Lhat : Subgroup TwoSuz.GL12).subtype) :=
          (Subgroup.card_map_of_injective (K := Q')
            (TwoSuz.Lhat : Subgroup TwoSuz.GL12).subtype_injective).symm
      _ = Nat.card Q₀ := by rw [hQ'map]
      _ = 8 := hQ₀card
  have hcentmap : (Subgroup.centralizer (Q' : Set ↥(TwoSuz.Lhat : Subgroup TwoSuz.GL12))).map
      (TwoSuz.Lhat : Subgroup TwoSuz.GL12).subtype =
      (TwoSuz.Lhat : Subgroup TwoSuz.GL12) ⊓
        Subgroup.centralizer (Q₀ : Set TwoSuz.GL12) :=
    map_subtype_centralizer_of_subgroupOf (hQ₀le.trans TwoSuz.Ssub_le_Lhat)
  have hsup' : (R₀s : Subgroup ↥(TwoSuz.Lhat : Subgroup TwoSuz.GL12)) ⊔
      Subgroup.centralizer (Q' : Set ↥(TwoSuz.Lhat : Subgroup TwoSuz.GL12)) = ⊤ := by
    apply Subgroup.map_injective (f := (TwoSuz.Lhat : Subgroup TwoSuz.GL12).subtype)
      (TwoSuz.Lhat : Subgroup TwoSuz.GL12).subtype_injective
    rw [Subgroup.map_sup, hR₀scoe, hR₀'map, hcentmap, Subgroup.map_top,
      Subgroup.range_subtype]
    exact le_antisymm (sup_le TwoSuz.Ssub_le_Lhat inf_le_left) hQ₀sup
  exact sylowFacts_of_mulEquiv eX 32 R₀s
    ⟨hzel', hzcard', Q', hQ'le, hQ'el, hQ'card, hsup'⟩ R

theorem twoSuzSylowFacts_holds :
    TwoSuzSylowFacts :=
  twoSuzSylowFacts_of_model TwoSuz.twoSuz_sylow_model

end CFSG.ComponentClassification.GrSLit.L34Sec5S
