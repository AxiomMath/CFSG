module

public import CFSG.CharacterTheory.Semidihedral.LocalCoverFactorization

public noncomputable section

namespace CFSG.Semidihedral.TwoCoverOddCore

open CFSG.Open
open CFSG.Semidihedral.ProperSubgroupRegularity
open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.LocalCoverFactorization
open CFSG.Semidihedral.QuaternionFocalFactorization
open CFSG.Wreathed.OriginalSylowNormalizerWitness

universe u

variable {H : Type u} [Group H]

theorem quotient_injective_on_every_two_subgroup
    (R : Subgroup H) [R.Normal] (hR : Odd (Nat.card R))
    (P : Subgroup H) (hP : IsPGroup 2 P) :
    Function.Injective ((QuotientGroup.mk' R).comp P.subtype) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let phi := (QuotientGroup.mk' R).comp P.subtype
  apply phi.ker_eq_bot_iff.mp
  apply phi.ker.eq_bot_iff_forall.mpr
  intro x hx
  by_contra hne
  have hxR : (x : H) ∈ R := (QuotientGroup.eq_one_iff _).mp hx
  have hdiv : 2 ∣ orderOf (x : H) := by
    rw [Subgroup.orderOf_coe]
    exact hP.dvd_orderOf hne
  exact hR.not_two_dvd_nat (hdiv.trans (R.orderOf_dvd_natCard hxR))

theorem original_four_group_members (t s x : H)
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hcomm : Commute t s) :
    x ∈ Subgroup.closure ({t, s} : Set H) ↔
      x = 1 ∨ x = t ∨ x = s ∨ x = t * s := by
  have ht2 : t * t = 1 := by
    simpa only [ht, pow_two] using pow_orderOf_eq_one t
  have hs2 : s * s = 1 := by
    simpa only [hs, pow_two] using pow_orderOf_eq_one s
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  let E : Subgroup H :=
    { carrier := {y | y = 1 ∨ y = t ∨ y = s ∨ y = t * s}
      one_mem' := Or.inl rfl
      mul_mem' := by
        rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl)
        all_goals simp only [Set.mem_ofPred_eq]
        all_goals grind only [mul_assoc, hcomm.eq]
      inv_mem' := by
        rintro a (rfl | rfl | rfl | rfl)
        all_goals simp only [Set.mem_ofPred_eq, inv_one, hti, hsi, mul_inv_rev,
          ← hcomm.eq]
        all_goals tauto }
  have hVE : Subgroup.closure ({t, s} : Set H) ≤ E := by
    apply (Subgroup.closure_le E).mpr
    rintro y (rfl | rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  constructor
  · intro hx
    exact hVE hx
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))

theorem original_four_group_isKleinFour (t s : H)
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hcomm : Commute t s) (hne : t ≠ s) :
    IsKleinFour (Subgroup.closure ({t, s} : Set H)) := by
  classical
  let V := Subgroup.closure ({t, s} : Set H)
  have ht1 : t ≠ 1 := by intro h; simp [h] at ht
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hprod := mul_notMem_of_orderOf_eq_two ht hs hne
  have heq : (V : Set H) = {t * s, t, s, 1} := by
    ext x
    simp only [V, SetLike.mem_coe, original_four_group_members t s x ht hs hcomm,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hcard : Nat.card V = 4 := by
    change Nat.card (V : Set H) = 4
    rw [heq, Nat.card_coe_set_eq]
    simp [Set.ncard_insert_of_notMem, hprod, ht1, hs1, hne]
  have hsquare : ∀ x : V, x ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    change (x : H) ^ 2 = 1
    have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
    have hs2 : s ^ 2 = 1 := hs ▸ pow_orderOf_eq_one s
    rcases (original_four_group_members t s x ht hs hcomm).mp x.property with
      h | h | h | h
    · simp [h]
    · simpa only [h] using ht2
    · simpa only [h] using hs2
    · simp [h, hcomm.mul_pow, ht2, hs2]
  refine ⟨hcard, Nat.dvd_antisymm
    (Monoid.exponent_dvd_of_forall_pow_eq_one hsquare) ?_⟩
  let a : V := ⟨t, Subgroup.subset_closure (by simp)⟩
  have ha : orderOf a = 2 := (Subgroup.orderOf_coe a).symm.trans ht
  rw [← ha]
  exact Monoid.order_dvd_exponent a

theorem quotient_identifies_every_original_two_subgroup
    (R : Subgroup H) [R.Normal] (hR : Odd (Nat.card R))
    (P : Subgroup H) (hP : IsPGroup 2 P) :
    ∃ e : P ≃* P.map (QuotientGroup.mk' R),
      ∀ x : P, (e x : H ⧸ R) = QuotientGroup.mk' R (x : H) := by
  let phi := (QuotientGroup.mk' R).comp P.subtype
  let j : P →* P.map (QuotientGroup.mk' R) := phi.codRestrict _ (fun x =>
    Subgroup.mem_map.mpr ⟨x, x.property, rfl⟩)
  have hinj : Function.Injective j := by
    intro x y hxy
    exact quotient_injective_on_every_two_subgroup R hR P hP (congrArg Subtype.val hxy)
  have hsurj : Function.Surjective j := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact ⟨MulEquiv.ofBijective j ⟨hinj, hsurj⟩, fun _ => rfl⟩

theorem quotient_centrality_in_original_two_subgroup
    (R : Subgroup H) [R.Normal] (hR : Odd (Nat.card R))
    (P : Subgroup H) (hP : IsPGroup 2 P) (t : H) (htP : t ∈ P)
    (hcentral : QuotientGroup.mk' R t ∈ Subgroup.center (H ⧸ R)) :
    (⟨t, htP⟩ : P) ∈ Subgroup.center P := by
  apply Subgroup.mem_center_iff.mpr
  intro x
  apply quotient_injective_on_every_two_subgroup R hR P hP
  change QuotientGroup.mk' R ((x : H) * t) = QuotientGroup.mk' R (t * (x : H))
  simpa only [map_mul] using Subgroup.mem_center_iff.mp hcentral
    (QuotientGroup.mk' R (x : H))

theorem every_original_semidihedral_sylow_center_card [Finite H]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 H) (f0 : SemidihedralGroup n ≃* S0)
    (S : Sylow 2 H) : Nat.card (Subgroup.center S) = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : SemidihedralGroup n ≃* S := f0.trans (S0.equiv S)
  rw [← Subgroup.map_center_eq f]
  exact (Subgroup.card_map_of_injective f.injective).trans (center_card n hn)

theorem original_two_involution_quotient_center_obstruction [Finite H]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 H) (f0 : SemidihedralGroup n ≃* S0)
    (R : Subgroup H) [R.Normal] (hR : Odd (Nat.card R))
    (t s : H) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hcomm : Commute t s) (hne : t ≠ s)
    (htcentral : QuotientGroup.mk' R t ∈ Subgroup.center (H ⧸ R))
    (hscentral : QuotientGroup.mk' R s ∈ Subgroup.center (H ⧸ R)) : False := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let V := Subgroup.closure ({t, s} : Set H)
  have hV : IsKleinFour V := original_four_group_isKleinFour t s ht hs hcomm hne
  have hVcard : Nat.card V = 4 := hV.card_four
  have hVtwo : IsPGroup 2 V := IsPGroup.of_card (n := 2) hVcard
  obtain ⟨S, hVS⟩ := hVtwo.exists_le_sylow
  have htS : t ∈ S := hVS (Subgroup.subset_closure (by simp))
  have hsS : s ∈ S := hVS (Subgroup.subset_closure (by simp))
  have htZ := quotient_centrality_in_original_two_subgroup R hR
    (S : Subgroup H) S.isPGroup' t htS htcentral
  have hsZ := quotient_centrality_in_original_two_subgroup R hR
    (S : Subgroup H) S.isPGroup' s hsS hscentral
  have hVZ : V.subgroupOf (S : Subgroup H) ≤ Subgroup.center S := by
    intro x hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Subtype.ext
    change (y : H) * (x : H) = (x : H) * (y : H)
    rcases (original_four_group_members t s (x : H) ht hs hcomm).mp hx with
      h | h | h | h
    · simp [h]
    · simpa only [Subgroup.coe_mul, Subtype.coe_mk, h] using
        congrArg Subtype.val (Subgroup.mem_center_iff.mp htZ y)
    · simpa only [Subgroup.coe_mul, Subtype.coe_mk, h] using
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hsZ y)
    · have htcomm : (y : H) * t = t * (y : H) :=
        congrArg Subtype.val (Subgroup.mem_center_iff.mp htZ y)
      have hscomm : (y : H) * s = s * (y : H) :=
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hsZ y)
      rw [h, ← mul_assoc, htcomm, mul_assoc, hscomm, ← mul_assoc]
  have hcard : Nat.card (V.subgroupOf (S : Subgroup H)) = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVS).toEquiv).trans hVcard
  have hle := Nat.card_le_card_of_injective (Subgroup.inclusion hVZ)
    (Subgroup.inclusion_injective hVZ)
  rw [hcard, every_original_semidihedral_sylow_center_card n hn S0 f0 S] at hle
  omega

theorem quotient_centrality_of_original_centralizer_factorization
    {H : Type*} [Group H] (R : Subgroup H) [R.Normal] (t : H)
    (hfactor : R ⊔ Subgroup.centralizer {t} = ⊤) :
    QuotientGroup.mk' R t ∈ Subgroup.center (H ⧸ R) := by
  apply Subgroup.mem_center_iff.mpr
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R y
  have hx : x ∈ R ⊔ Subgroup.centralizer {t} := by rw [hfactor]; trivial
  obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  have haq : QuotientGroup.mk' R a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
  simp only [map_mul, haq, one_mul]
  exact congrArg (QuotientGroup.mk' R) (Subgroup.mem_centralizer_singleton_iff.mp hc)

theorem intrinsic_factorization_of_literal_ambient_factorization
    {G : Type*} [Group G] (H : Subgroup G) (R : Subgroup H) (t : H)
    (hfactor : R.map H.subtype ⊔ (H ⊓ Subgroup.centralizer {(t : G)}) = H) :
    R ⊔ Subgroup.centralizer {t} = ⊤ := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_sup, Subgroup.map_top, H.range_subtype]
  have hC : (Subgroup.centralizer {t}).map H.subtype =
      H ⊓ Subgroup.centralizer {(t : G)} := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c.property, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc))⟩
    · rintro ⟨hxH, hxC⟩
      exact ⟨⟨x, hxH⟩, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxC)), rfl⟩
  rw [hC]
  exact hfactor


theorem two_commuting_involution_local_layer_covers_force_trivial_subgroup_odd_core
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : SmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (htnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (htcentral : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (htnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (pt ft : ℕ) (hpt : pt.Prime) (hptodd : Odd pt) (hft : 1 ≤ ft) (hqt : 5 ≤ pt ^ ft)
    (htmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 pt ft)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma s))]
    (hsnonab : ∃ a b : CFSG.generalizedFitting (Gamma s), a * b ≠ b * a)
    (hscentral : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma s) : Set (Gamma s)) = ⊥)
    (hsnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma s)), ¬ IsCyclic P)
    (ps fs : ℕ) (hps : ps.Prime) (hpsodd : Odd ps) (hfs : 1 ≤ fs) (hqs : 5 ≤ ps ^ fs)
    (hsmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma s)) .PSL 2 ps fs)
    (H : Subgroup G) (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (htcover : (H.subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t))
    (hscover : (H.subgroupOf (C s) ⊓
      ((CFSG.generalizedFitting (Gamma s)).comap (barKappa s)).comap (nu s)).map (nu s) =
        (CFSG.generalizedFitting (Gamma s)).comap (barKappa s)) :
    CFSG.pPrimeCore 2 H = ⊥ := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hR
  have htH : t ∈ H := hVH (Subgroup.subset_closure (by simp))
  have hsH : s ∈ H := hVH (Subgroup.subset_closure (by simp))
  let tH : H := ⟨t, htH⟩
  let sH : H := ⟨s, hsH⟩
  have htC : t ∈ C s := Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_singleton_iff.mp hsC).symm
  have hVHswap : Subgroup.closure ({s, t} : Set G) ≤ H := by
    simpa only [Set.pair_comm] using hVH
  have htdata := original_layer_cover_produces_focal_and_factorization
    G hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts htnonab htcentral htnc
      pt ft hpt hptodd hft hqt htmodel H hVH hR htcover
  have hsdata := original_layer_cover_produces_focal_and_factorization
    G hGnonab hrecognition n hn S0 f0 s t hs ht htC hts.symm hsnonab hscentral hsnc
      ps fs hps hpsodd hfs hqs hsmodel H hVHswap hR hscover
  obtain ⟨-, -, -, hall, -, -, -, htFactor, -⟩ := htdata
  obtain ⟨-, -, -, -, -, -, -, hsFactor, -⟩ := hsdata
  have htFactor' : (CFSG.pPrimeCore 2 H).map H.subtype ⊔
      (H ⊓ Subgroup.centralizer {(tH : G)}) = H := by
    simpa only [ambientOddCore, oddCore_eq_twoPrimeCore] using htFactor
  have hsFactor' : (CFSG.pPrimeCore 2 H).map H.subtype ⊔
      (H ⊓ Subgroup.centralizer {(sH : G)}) = H := by
    simpa only [ambientOddCore, oddCore_eq_twoPrimeCore] using hsFactor
  have htquot := quotient_centrality_of_original_centralizer_factorization
    (CFSG.pPrimeCore 2 H) tH
      (intrinsic_factorization_of_literal_ambient_factorization
        H (CFSG.pPrimeCore 2 H) tH htFactor')
  have hsquot := quotient_centrality_of_original_centralizer_factorization
    (CFSG.pPrimeCore 2 H) sH
      (intrinsic_factorization_of_literal_ambient_factorization
        H (CFSG.pPrimeCore 2 H) sH hsFactor')
  let SB : Sylow 2 (H.subgroupOf (C t)) := default
  obtain ⟨⟨fB⟩, SH, SG, -, -, -, hpresent⟩ := hall SB
  obtain ⟨-, -, fH, -, -, -, -, -⟩ := hpresent fB
  have htHorder : orderOf tH = 2 := (Subgroup.orderOf_coe tH).symm.trans ht
  have hsHorder : orderOf sH = 2 := (Subgroup.orderOf_coe sH).symm.trans hs
  have hcommH : Commute tH sH := by
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_singleton_iff.mp hsC).symm
  have hneH : tH ≠ sH := fun h => hts (congrArg Subtype.val h)
  have hodd : Odd (Nat.card (CFSG.pPrimeCore 2 H)) :=
    Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  exact original_two_involution_quotient_center_obstruction n hn SH fH
    (CFSG.pPrimeCore 2 H) hodd tH sH htHorder hsHorder hcommH hneH htquot hsquot

end CFSG.Semidihedral.TwoCoverOddCore

end
