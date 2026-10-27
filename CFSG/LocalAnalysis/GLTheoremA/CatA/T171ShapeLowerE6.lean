module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeLowerBase
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.E6BadTorus
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6Lift
public import CFSG.RankThree.CentralCover.SteinbergBNCoverPairingCore
public import CFSG.LieType.SeitzGeneration.ExcPlaneModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AGrp
public import CFSG.RankThree.PartOne.K159.CoverLift
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Dickson.Sec6.I1431 CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Isogeny
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.RankThree.CentralCover
open CFSG.RankThree.PartOne.K159 (closure_range_ofAdd_single)
open scoped commutatorElement


theorem three_pow_five_mul_card_inf_le {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {Q : Type} [Group Q] {π : ↥L →* Q} (hker : π.ker = Subgroup.center ↥L)
    {R : Subgroup ↥L} (hR : 3 ^ 5 ≤ Nat.card (R.map π)) :
    3 ^ 5 * Nat.card ↥((R.map L.subtype) ⊓ Subgroup.centralizer (L : Set G)) ≤
      Nat.card (R.map L.subtype) := by
  have hcardE : Nat.card (R.map L.subtype) = Nat.card R :=
    Subgroup.card_map_of_injective L.subtype_injective
  have hcardI : Nat.card ↥((R.map L.subtype) ⊓ Subgroup.centralizer (L : Set G)) =
      Nat.card ↥(R ⊓ Subgroup.center ↥L) := (card_inf_center_map_eq (L := L) (E := R)).2
  have hcardR : Nat.card ↥(R ⊓ π.ker) * Nat.card (R.map π) = Nat.card R :=
    card_inf_ker_mul_card_map π R
  rw [hcardE, hcardI, ← hker]
  calc 3 ^ 5 * Nat.card ↥(R ⊓ π.ker)
      ≤ Nat.card (R.map π) * Nat.card ↥(R ⊓ π.ker) := Nat.mul_le_mul_right _ hR
    _ = Nat.card R := by rw [mul_comm]; exact hcardR

theorem closure_range_hm_eq_map_torus {F : Type} [Field F] [Finite F] (ζ : Fˣ)
    (hζ : orderOf ζ = 3) :
    Subgroup.closure (Set.range fun i : Fin Tag.E6.rank =>
        e6Isogeny F (e6Data_valid.hm F i ζ)) =
      (((minTorus e6Data_valid F).comp (zeta3Pi ζ hζ)).range).map (e6Isogeny F) := by
  have hpi : ∀ i : Fin Tag.E6.rank,
      zeta3Pi ζ hζ (Multiplicative.ofAdd (Pi.single i (1 : ZMod 3))) = Pi.mulSingle i ζ := by
    intro i
    ext k
    rw [zeta3Pi_apply, toAdd_ofAdd, Pi.single_apply, Pi.mulSingle_apply]
    by_cases hk : k = i
    · rw [if_pos hk, if_pos hk, show (1 : ZMod 3).val = 1 from rfl, pow_one]
    · rw [if_neg hk, if_neg hk, show (0 : ZMod 3).val = 0 from rfl, pow_zero]
  have hgen : (fun i : Fin Tag.E6.rank =>
        ((e6Isogeny F).comp ((minTorus e6Data_valid F).comp (zeta3Pi ζ hζ)))
          (Multiplicative.ofAdd (Pi.single i (1 : ZMod 3)))) =
      (fun i => e6Isogeny F (e6Data_valid.hm F i ζ)) := by
    funext i
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hpi, minTorus_mulSingle]
  have h1 : (((minTorus e6Data_valid F).comp (zeta3Pi ζ hζ)).range).map (e6Isogeny F) =
      ((e6Isogeny F).comp ((minTorus e6Data_valid F).comp (zeta3Pi ζ hζ))).range :=
    (MonoidHom.range_comp _ _).symm
  rw [h1, MonoidHom.range_eq_map,
    ← closure_range_ofAdd_single (p := 3) (m := Tag.E6.rank), MonoidHom.map_closure]
  have h2 : ((⇑((e6Isogeny F).comp ((minTorus e6Data_valid F).comp (zeta3Pi ζ hζ)))) ''
      Set.range (fun j => Multiplicative.ofAdd (Pi.single j (1 : ZMod 3)))) =
      Set.range (fun i => e6Isogeny F (e6Data_valid.hm F i ζ)) := by
    rw [← Set.range_comp]
    exact congrArg Set.range hgen
  rw [h2]

theorem exists_elemAbelian_lift_E6 {F : Type} [Field F] [Finite F] (h2 : (2 : F) = 0)
    (h3 : 3 ∣ Nat.card F - 1) {L : Type} [Group L] (π : L →* adjointGroup Tag.E6 F)
    (hπ : Function.Surjective π) (hc : ∀ x, π x = 1 → x ∈ Subgroup.center L) :
    ∃ (R : Subgroup L) (U : Subgroup (adjointGroup Tag.E6 F)),
      (∀ x ∈ R, x ^ 3 = 1) ∧ (∀ x ∈ R, ∀ y ∈ R, x * y = y * x) ∧
        3 ^ 5 ≤ Nat.card (R.map π) ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
          R.map π ≤ Subgroup.normalizer (U : Set (adjointGroup Tag.E6 F)) := by
  classical
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Fˣ, orderOf ζ = 3 := by
    have h : 3 ∣ Nat.card Fˣ := by rw [Nat.card_units]; exact h3
    exact exists_prime_orderOf_dvd_card' 3 h
  obtain ⟨U, hU1, hU2, hUN⟩ := e6_even_witness (F := F) h2 ζ hζ
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hD : 3 ^ 5 ≤
      Nat.card (((minTorus e6Data_valid F).comp (zeta3Pi ζ hζ)).range.map (e6Isogeny F)) :=
    three_pow_five_le_card_image ζ hζ
  let e : Fin Tag.E6.rank → adjointGroup Tag.E6 F :=
    fun i => e6Isogeny F (e6Data_valid.hm F i ζ)
  let n : Fin Tag.E6.rank → adjointGroup Tag.E6 F :=
    fun i => e6Isogeny F (e6Data_valid.nm F i)
  have hcomm : ∀ i j, e i * e j = e j * e i := by
    intro i j
    have h := (e6Data_valid.torus_commute (k := F) i j (e6Data_valid.hm_mem_torus F i ζ)
      (e6Data_valid.hm_mem_torus F j ζ)).eq
    show e6Isogeny F (e6Data_valid.hm F i ζ) * e6Isogeny F (e6Data_valid.hm F j ζ) =
      e6Isogeny F (e6Data_valid.hm F j ζ) * e6Isogeny F (e6Data_valid.hm F i ζ)
    rw [← map_mul, ← map_mul, h]
  have he : ∀ i, e i ^ 3 = 1 := by
    intro i
    show e6Isogeny F ((e6Data_valid.hHom F i) ζ) ^ 3 = 1
    rw [← map_pow, ← map_pow (e6Data_valid.hHom F i), hζ3, map_one, map_one]
  have hinv : ∀ i, n i * e i * (n i)⁻¹ = (e i)⁻¹ := by
    intro i
    show e6Isogeny F (e6Data_valid.nm F i) * e6Isogeny F (e6Data_valid.hm F i ζ) *
      (e6Isogeny F (e6Data_valid.nm F i))⁻¹ = (e6Isogeny F (e6Data_valid.hm F i ζ))⁻¹
    have h := congrArg (e6Isogeny F)
      (e6Data_valid.nm_conj_hm (k := F) (j := i) (l := i) ζ)
    simp only [map_mul, map_inv] at h
    have hz : e6Data_valid.hm F i (ζ ^ (-(Tag.E6.cartan i i : ℤ))) =
        (e6Data_valid.hm F i ζ) ^ (-(Tag.E6.cartan i i : ℤ)) :=
      map_zpow (e6Data_valid.hHom F i) ζ _
    rw [h, hz, map_zpow, Tag.cartan_self]
    rw [zpow_neg, zpow_ofNat, pow_two, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
  have hrel : ∀ i j, ∃ k : ℤ, n i * e j * (n i)⁻¹ = e j * e i ^ k := by
    intro i j
    refine ⟨-(Tag.E6.cartan j i : ℤ), ?_⟩
    show e6Isogeny F (e6Data_valid.nm F i) * e6Isogeny F (e6Data_valid.hm F j ζ) *
      (e6Isogeny F (e6Data_valid.nm F i))⁻¹ =
        e6Isogeny F (e6Data_valid.hm F j ζ) * (e6Isogeny F (e6Data_valid.hm F i ζ)) ^
          (-(Tag.E6.cartan j i : ℤ))
    have h := congrArg (e6Isogeny F)
      (e6Data_valid.nm_conj_hm (k := F) (j := i) (l := j) ζ)
    simp only [map_mul, map_inv] at h
    have hz : e6Data_valid.hm F i (ζ ^ (-(Tag.E6.cartan j i : ℤ))) =
        (e6Data_valid.hm F i ζ) ^ (-(Tag.E6.cartan j i : ℤ)) :=
      map_zpow (e6Data_valid.hHom F i) ζ _
    rw [h, hz, map_zpow]
  obtain ⟨R, hR3, hRc, hRmap⟩ := exists_elemAbelian_of_reflection_lifts π hπ hc e n hcomm he
    hinv hrel
  have hEq : Subgroup.closure (Set.range e) =
      (((minTorus e6Data_valid F).comp (zeta3Pi ζ hζ)).range).map (e6Isogeny F) :=
    closure_range_hm_eq_map_torus ζ hζ
  refine ⟨R, U, hR3, hRc, ?_, hU1, hU2, ?_⟩
  · rw [hRmap, hEq]; exact hD
  · rw [hRmap, hEq]; exact hUN

theorem lowerE6_holds : LowerE6 := by
  intro G _ _ L hq hcat
  classical
  obtain ⟨i, hQi, ⟨eCat⟩⟩ := hcat
  rcases i with ⟨pr, hpr⟩ | ⟨deg, hdeg⟩ | d | s
  · exact hQi.elim
  · exact hQi.elim
  · obtain ⟨idx, hv⟩ := d
    obtain ⟨q, hidx, hq2, h3q⟩ := hQi
    subst hidx
    obtain ⟨F, hFld, hFfin, hFcard, hFchar, ⟨eAd⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
        (CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6) q hv
    letI := hFld
    letI := hFfin
    haveI : CharP F 2 := by rw [← hq2]; exact hFchar
    let e : PSimple 3 L ≃* adjointGroup Tag.E6 F := eCat.trans eAd
    have h3F : 3 ∣ Nat.card F - 1 := by rw [hFcard]; exact h3q
    have h2F : (2 : F) = 0 := CharP.cast_eq_zero F 2
    obtain ⟨ζ, hζ⟩ : ∃ ζ : Fˣ, orderOf ζ = 3 := by
      have h : 3 ∣ Nat.card Fˣ := by rw [Nat.card_units]; exact h3F
      exact exists_prime_orderOf_dvd_card' 3 h
    have h3adj : 3 ∣ Nat.card (adjointGroup Tag.E6 F) := by
      have h1 : 3 ^ 5 ≤ Nat.card (((e6Isogeny F).comp ((minTorus e6Data_valid F).comp
          (zeta3Pi ζ hζ))).range) := by
        rw [MonoidHom.range_comp]
        exact three_pow_five_le_card_image ζ hζ
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hEab : IsElemAbelian 3 (((e6Isogeny F).comp ((minTorus e6Data_valid F).comp
          (zeta3Pi ζ hζ))).range) :=
        isElemAbelian_range_of_pow_three _ (fun a => pow_three_multiplicative_pi _ a)
      have hE3 : IsPGroup 3 (((e6Isogeny F).comp ((minTorus e6Data_valid F).comp
          (zeta3Pi ζ hζ))).range) := hEab.isPGroup
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hE3
      have hk5 : 5 ≤ k := by
        rw [hk] at h1
        exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h1
      have hk0 : k ≠ 0 := by omega
      have hdvd : 3 ∣ 3 ^ k := dvd_pow_self 3 hk0
      rw [← hk] at hdvd
      have htop := Subgroup.card_dvd_of_le
        (le_top : (((e6Isogeny F).comp ((minTorus e6Data_valid F).comp (zeta3Pi ζ hζ))).range)
          ≤ ⊤)
      rw [Subgroup.card_top] at htop
      exact hdvd.trans htop
    have h3L : 3 ∣ Nat.card ↥L := by
      have h1 : 3 ∣ Nat.card (PSimple 3 L) := by
        rw [Nat.card_congr e.toEquiv]; exact h3adj
      exact h1.trans ((Subgroup.card_quotient_dvd_card (Subgroup.center (PQuot 3 L))).trans
        (Subgroup.card_quotient_dvd_card (GLAPPrimeCore 3 ↥L)))
    have hO : GLAPPrimeCore 3 ↥L ≠ ⊤ := by
      intro htop
      have hc : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥L)) :=
        CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥L)
      rw [htop, Subgroup.card_top] at hc
      exact Nat.prime_three.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc h3L)
    have hOZ : GLAPPrimeCore 3 ↥L ≤ Subgroup.center ↥L :=
      CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hq inferInstance hO
    haveI : Group.IsPerfect ↥L := ⟨hq.1⟩
    let eP := CFSG.LocalAnalysis.GLTheoremA.S172A.pSimpleEquivCenterQuot 3 hOZ
    let eAll : (↥L ⧸ Subgroup.center ↥L) ≃* adjointGroup Tag.E6 F := eP.trans e
    let π : ↥L →* adjointGroup Tag.E6 F :=
      eAll.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
    have hπ : Function.Surjective π :=
      eAll.surjective.comp (QuotientGroup.mk'_surjective _)
    have hπker : π.ker = Subgroup.center ↥L := by
      ext x
      show eAll ((QuotientGroup.mk' (Subgroup.center ↥L)) x) = 1 ↔
        x ∈ Subgroup.center ↥L
      constructor
      · intro hx
        have h1 : (QuotientGroup.mk' (Subgroup.center ↥L)) x = 1 := by
          apply eAll.injective
          rw [map_one]
          exact hx
        exact (QuotientGroup.eq_one_iff _).1 h1
      · intro hx
        rw [show (QuotientGroup.mk' (Subgroup.center ↥L)) x = 1 from
          (QuotientGroup.eq_one_iff _).2 hx]
        exact map_one _
    obtain ⟨R, U, hR3, hRc, hRcard, hU1, hU2, hRUN⟩ :=
      exists_elemAbelian_lift_E6 h2F h3F π hπ (fun x hx => hπker ▸ hx)
    obtain ⟨R₂, hR₂1, hR₂2, hR₂N⟩ :=
      exists_two_subgroup_normalized_of_cover hπ hπker.le hU1 hU2 (S := R) (fun x hx u hu =>
        (Subgroup.mem_normalizer_iff.1 (hRUN (Subgroup.mem_map_of_mem π hx)) u).1 hu)
    have hRel : IsElemAbelian 3 R :=
      ⟨⟨⟨fun a b => Subtype.ext (hRc a a.2 b b.2)⟩⟩, fun x hx => hR3 x hx⟩
    refine ⟨R.map L.subtype, R₂.map L.subtype, Subgroup.map_subtype_le R,
      Subgroup.map_subtype_le R₂, hRel.map L.subtype, hR₂2.map L.subtype, ?_, ?_, ?_⟩
    · intro hbot
      exact hR₂1 ((Subgroup.map_eq_bot_iff_of_injective R₂ (Subgroup.subtype_injective L)).1
        hbot)
    · exact map_le_normalizer_map L.subtype hR₂N
    · exact three_pow_five_mul_card_inf_le (π := π) (R := R) hπker hRcard
  · exact hQi.elim

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
