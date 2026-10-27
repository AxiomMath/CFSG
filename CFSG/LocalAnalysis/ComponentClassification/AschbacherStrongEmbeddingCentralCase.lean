module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingCentralBender
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingCentralQuotient

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {X : Type*} [Group X]

theorem commutator_dichotomy {x : X} (hx : orderOf x = 2) (hhull : involutionPointHull x = ⊤) :
    (∀ g : X, g ∈ commutator X ∨ x⁻¹ * g ∈ commutator X) ∧
      ∀ t ∈ involutionPointClass x, x⁻¹ * t ∈ commutator X := by
  have hcls : ∀ t ∈ involutionPointClass x, Abelianization.of t = Abelianization.of x := by
    rintro t ⟨g, rfl⟩
    change Abelianization.of (g⁻¹ * x * g) = _
    rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  have hxsq : (Abelianization.of x) ^ 2 = 1 := by
    rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have hmem : ∀ g : X, Abelianization.of g ∈ Subgroup.zpowers (Abelianization.of x) := by
    intro g
    have hg : g ∈ involutionPointHull x := hhull ▸ Subgroup.mem_top g
    have hle : involutionPointHull x ≤
        (Subgroup.zpowers (Abelianization.of x)).comap Abelianization.of := by
      refine (Subgroup.closure_le _).mpr fun t ht => ?_
      change Abelianization.of t ∈ Subgroup.zpowers (Abelianization.of x)
      rw [hcls t ht]
      exact Subgroup.mem_zpowers _
    exact hle hg
  have hker : ∀ g : X, Abelianization.of g = 1 → g ∈ commutator X := by
    intro g hg
    rw [← Abelianization.ker_of]
    exact hg
  have hdich : ∀ a ∈ Subgroup.zpowers (Abelianization.of x),
      a = 1 ∨ a = Abelianization.of x := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul, zpow_two, ← pow_two, hxsq, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul, zpow_two, ← pow_two, hxsq, one_zpow, one_mul]
  refine ⟨fun g => ?_, fun t ht => hker _ (by rw [map_mul, map_inv, hcls t ht, inv_mul_cancel])⟩
  rcases hdich _ (hmem g) with h | h
  · exact Or.inl (hker g h)
  · exact Or.inr (hker _ (by rw [map_mul, map_inv, h, inv_mul_cancel]))

theorem commutator_map_quotient (Z : Subgroup X) [Z.Normal] :
    (commutator X).map (QuotientGroup.mk' Z) = commutator (X ⧸ Z) := by
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective Z), commutator_def]

theorem normSplit_of_central_not_mem [Finite X] {M : Subgroup X} {x u : X}
    (hx : orderOf x = 2) (hhull : involutionPointHull x = ⊤)
    (hu : u ∈ Subgroup.center X) (hu2 : orderOf u = 2) (Z : Subgroup X) [Z.Normal]
    (hZ : Z = Subgroup.zpowers u) (hZM : Z ≤ M)
    (hse : fusionStronglyEmbedded
      ((M.map (QuotientGroup.mk' Z)).subgroupOf (commutator (X ⧸ Z))))
    (huD : u ∉ commutator X) : NormSplit X M x := by
  let D := commutator X
  let q := QuotientGroup.mk' Z
  obtain ⟨hdich, hcls⟩ := commutator_dichotomy hx hhull
  have huD' : x⁻¹ * u ∈ D := (hdich u).resolve_left huD
  have hmemZ : ∀ w : X, w ∈ Z ↔ w = 1 ∨ w = u := by
    intro w
    rw [hZ, mem_zpowers_of_orderOf_two hu2]
  refine Or.inr ⟨u, hu2 ▸ pow_orderOf_eq_one u, hu, ?_, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro w ⟨hwu, hwD⟩
    rcases (mem_zpowers_of_orderOf_two hu2).mp hwu with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd hwD huD
  · rw [eq_top_iff]
    intro g _
    rcases hdich g with hg | hg
    · exact Subgroup.mem_sup_right hg
    · have hmem : u⁻¹ * g ∈ D := by
        have h := D.mul_mem (D.inv_mem huD') hg
        simpa only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] using h
      have h := Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers u) :
        u ∈ Subgroup.zpowers u ⊔ D) (Subgroup.mem_sup_right hmem)
      rwa [mul_inv_cancel_left] at h
  · have hDmap := commutator_map_quotient (X := X) Z
    let ψ : D →* commutator (X ⧸ Z) := (q.comp D.subtype).codRestrict _
      (fun d => hDmap ▸ ⟨d, d.property, rfl⟩)
    have hψ : Function.Surjective ψ := by
      rintro ⟨y, hy⟩
      rw [← hDmap] at hy
      obtain ⟨d, hd, rfl⟩ := hy
      exact ⟨⟨d, hd⟩, rfl⟩
    have hker : ψ.ker = ⊥ := by
      rw [eq_bot_iff]
      intro d hd
      have h1 : q d = 1 := congrArg Subtype.val hd
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hmemZ] at h1
      rcases h1 with h1 | h1
      · exact Subgroup.mem_bot.mpr (Subtype.ext h1)
      · exact absurd (h1 ▸ d.property) huD
    have hodd : Odd (Nat.card ψ.ker) := by rw [hker, Subgroup.card_bot]; exact odd_one
    have hmap : (M.subgroupOf D).map ψ = (M.map q).subgroupOf (commutator (X ⧸ Z)) := by
      ext y
      constructor
      · rintro ⟨d, hd, rfl⟩
        exact ⟨d, hd, rfl⟩
      · intro hy
        obtain ⟨d, rfl⟩ := hψ y
        have hker' : q.ker ≤ M := by rw [QuotientGroup.ker_mk']; exact hZM
        exact ⟨d, (mem_map_iff_of_ker_le q hker' d).mp hy, rfl⟩
    exact stronglyEmbedded_of_map_odd_kernel ψ hψ hodd (hker ▸ bot_le) (hmap ▸ hse)
  · intro t ht
    have h := D.mul_mem (D.inv_mem huD') (hcls t ht)
    simpa only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] using h

theorem isMulCommutative_of_sq_eq_one {K : Subgroup X} (hK : ∀ k ∈ K, k ^ 2 = 1) :
    IsMulCommutative K := by
  have hinv : ∀ k ∈ K, k⁻¹ = k := fun k hk =>
    inv_eq_of_mul_eq_one_left (by rw [← pow_two]; exact hK k hk)
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have hab := hinv _ (K.mul_mem a.property b.property)
  rw [mul_inv_rev, hinv _ b.property, hinv _ a.property] at hab
  exact hab.symm

theorem false_of_central_mem_commutator (hcov : BenderDoubleCoverRigidity)
    {X : Type} [Group X] [Finite X] {M : Subgroup X} {x u : X}
    (hx : orderOf x = 2) (hM : M ≠ ⊤) (huniq : ∀ g : X, x ∈ rightConjugate M g ↔ g ∈ M)
    (hcentral : InvolutionPointCentralSylow x) (hhull : involutionPointHull x = ⊤)
    (hu : u ∈ Subgroup.center X) (hu2 : orderOf u = 2) (Z : Subgroup X) [Z.Normal]
    (hZ : Z = Subgroup.zpowers u) (hB : fusionIsBenderGroup (commutator (X ⧸ Z)))
    (hperf : commutator (commutator (X ⧸ Z)) = ⊤) (huD : u ∈ commutator X) : False := by
  let D := commutator X
  let q := QuotientGroup.mk' Z
  obtain ⟨hdich, -⟩ := commutator_dichotomy hx hhull
  have hmemZ : ∀ w : X, w ∈ Z ↔ w = 1 ∨ w = u := by
    intro w
    rw [hZ, mem_zpowers_of_orderOf_two hu2]
  have hZD : Z ≤ D := hZ ▸ Subgroup.zpowers_le.mpr huD
  have hDmap := commutator_map_quotient (X := X) Z
  have hxx : x * x = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hx).1
  have huu : u * u = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hu2).1
  have hxu : Commute x u := Subgroup.mem_center_iff.mp hu x
  have hKK : ⁅commutator (X ⧸ Z), commutator (X ⧸ Z)⁆ = commutator (X ⧸ Z) := by
    have h := Subgroup.map_subtype_commutator (commutator (X ⧸ Z))
    rw [hperf, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
    exact h.symm
  have hEmap : (⁅D, D⁆).map q = commutator (X ⧸ Z) := by
    rw [Subgroup.map_commutator]
    change ⁅(commutator X).map q, (commutator X).map q⁆ = _
    rw [hDmap, hKK]
  have hDEZ : D ≤ ⁅D, D⁆ ⊔ Z := by
    intro d hd
    have hqd : q d ∈ (⁅D, D⁆).map q := by
      rw [hEmap, ← hDmap]
      exact ⟨d, hd, rfl⟩
    obtain ⟨e, he, hed⟩ := hqd
    have hz : e⁻¹ * d ∈ Z := by
      rw [← QuotientGroup.eq]
      exact hed
    have h := Subgroup.mul_mem _ (Subgroup.mem_sup_left he : e ∈ ⁅D, D⁆ ⊔ Z)
      (Subgroup.mem_sup_right hz)
    rwa [mul_inv_cancel_left] at h
  let H₀ := commutingPairSubgroup x u hxx huu hxu
  have hZH₀ : Z ≤ H₀ := hZ ▸ Subgroup.zpowers_le.mpr
    (mem_commutingPairSubgroup.mpr (Or.inr (Or.inr (Or.inl rfl))))
  have hxH₀ : x ∈ H₀ := mem_commutingPairSubgroup.mpr (Or.inr (Or.inl rfl))
  have hsup : ⁅D, D⁆ ⊔ H₀ = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hle : D ≤ ⁅D, D⁆ ⊔ H₀ := hDEZ.trans (sup_le_sup_left hZH₀ _)
    rcases hdich g with hg | hg
    · exact hle hg
    · have h := Subgroup.mul_mem _ (Subgroup.mem_sup_right hxH₀ : x ∈ ⁅D, D⁆ ⊔ H₀) (hle hg)
      rwa [mul_inv_cancel_left] at h
  have hH₀ : IsMulCommutative H₀ :=
    isMulCommutative_of_sq_eq_one fun k hk => commutingPairSubgroup_sq hk
  have hDE : D ≤ ⁅D, D⁆ :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup hH₀
  have hDperf : commutator D = ⊤ := by
    apply Subgroup.map_injective D.subtype_injective
    rw [Subgroup.map_subtype_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact le_antisymm (Subgroup.commutator_le_self D) hDE
  let ZD : Subgroup D := Z.subgroupOf D
  have hZDnormal : ZD.Normal := Subgroup.normal_subgroupOf
  have hZDc : ZD ≤ Subgroup.center D := by
    intro w hw
    refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
    have hwu : (w : X) ∈ Z := hw
    rcases (hmemZ _).mp hwu with h | h
    · simp only [Subgroup.coe_mul, h, mul_one, one_mul]
    · simp only [Subgroup.coe_mul, h]
      exact (Subgroup.mem_center_iff.mp hu (g : X))
  have hZD2 : Nat.card ZD = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZD).toEquiv, hZ, Nat.card_zpowers, hu2]
  let ψ : D →* commutator (X ⧸ Z) := (q.comp D.subtype).codRestrict _
    (fun d => hDmap ▸ ⟨d, d.property, rfl⟩)
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    rw [← hDmap] at hy
    obtain ⟨d, hd, rfl⟩ := hy
    exact ⟨⟨d, hd⟩, rfl⟩
  have hψker : ψ.ker = ZD := by
    ext d
    change ψ d = 1 ↔ (d : X) ∈ Z
    rw [Subtype.ext_iff]
    change q d = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hBD : fusionIsBenderGroup (D ⧸ ZD) :=
    CFSG.QuasithinUnique.RankOneRecog.fusionIsBenderGroup_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)).symm hB
  let φ : MulAut D := MulAut.conjNormal x
  have hφ2 : φ * φ = 1 := by
    change MulAut.conjNormal x * MulAut.conjNormal x = 1
    rw [← map_mul, hxx, map_one]
  obtain ⟨S, hxS, hxc⟩ := hcentral
  have hxcomm := commute_of_mem_center hxS hxc
  obtain ⟨R, hR⟩ := CFSG.Glauberman.sylow_inf_normal S (N := D)
  have hfix : ∀ r ∈ (R : Subgroup D), φ r = r := by
    intro r hr
    apply Subtype.ext
    rw [hR] at hr
    have hrS : (r : X) ∈ (S : Subgroup X) := hr.1
    change x * (r : X) * x⁻¹ = r
    rw [(hxcomm _ hrS).eq, mul_inv_cancel_right]
  have hφ1 := hcov D ZD hZDc hZD2 hDperf hBD φ hφ2 ⟨R, hfix⟩
  have hxD : ∀ d ∈ D, Commute x d := by
    intro d hd
    have h := congrArg (fun ψ : MulAut D => ((ψ ⟨d, hd⟩ : D) : X)) hφ1
    change x * d * x⁻¹ = d at h
    change x * d = d * x
    calc x * d = x * d * x⁻¹ * x := by group
      _ = d * x := by rw [h]
  apply hM
  refine eq_top_iff.mpr fun g _ => centralizer_le_of_unique huniq ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  rcases hdich g with hg | hg
  · exact (hxD g hg).eq.symm
  · have h := (hxD _ hg).eq
    calc g * x = x * ((x⁻¹ * g) * x) := by group
      _ = x * (x * (x⁻¹ * g)) := by rw [← h]
      _ = x * g := by group

theorem normSplit_of_central_involution (hcov : BenderDoubleCoverRigidity)
    {X : Type} [Group X] [Finite X] {M : Subgroup X} {x u : X}
    (hx : orderOf x = 2) (hM : M ≠ ⊤) (huniq : ∀ g : X, x ∈ rightConjugate M g ↔ g ∈ M)
    (h2 : CentralProductCentralizer M x) (hhull : involutionPointHull x = ⊤)
    (hO : CFSG.oddCore X = ⊥) (hu : u ∈ Subgroup.center X) (hu2 : orderOf u = 2)
    (Z : Subgroup X) [Z.Normal] (hZ : Z = Subgroup.zpowers u)
    (hN : NormSplit (X ⧸ Z) (M.map (QuotientGroup.mk' Z)) (QuotientGroup.mk' Z x)) :
    NormSplit X M x := by
  set q := QuotientGroup.mk' Z with hqdef
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective Z
  have hxx : x * x = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hx).1
  have huc : ∀ g : X, g * u = u * g := fun g => Subgroup.mem_center_iff.mp hu g
  have hmemZ : ∀ w : X, w ∈ Z ↔ w = 1 ∨ w = u := by
    intro w
    rw [hZ, mem_zpowers_of_orderOf_two hu2]
  have huM : u ∈ M := centralizer_le_of_unique huniq
    (Subgroup.mem_centralizer_singleton_iff.mpr (huc x).symm)
  have hZM : Z ≤ M := hZ ▸ Subgroup.zpowers_le.mpr huM
  have hZc : Z ≤ Subgroup.center X := hZ ▸ Subgroup.zpowers_le.mpr hu
  have hZ2 : Nat.card Z = 2 := by rw [hZ, Nat.card_zpowers, hu2]
  have hxt2 := orderOf_central_quotient hx huniq hM hu hu2 Z hZ
  have hOt := oddCore_central_quotient_eq_bot hO Z hZc hZ2
  have hhullt := hull_map_eq_top q hq hhull
  have h2t := centralProduct_central_quotient hx huniq hM h2 hu hu2 Z hZ
  have hux : u * x ∉ involutionPointClass x := by
    intro hux
    have hcomm : Commute x (u * x) := by
      change x * (u * x) = u * x * x
      rw [← mul_assoc, huc x]
    have hne : u * x ≠ x := by
      intro h
      apply (orderOf_eq_prime_iff.mp hu2).2
      have h' := congrArg (· * x) h
      simpa only [mul_assoc, hxx, mul_one] using h'
    have hC := h2.2 (u * x) hux hcomm hne
    apply hM
    refine eq_top_iff.mpr fun g _ => hC ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxux : x * (u * x) = u := by rw [← mul_assoc, huc x, mul_assoc, hxx, mul_one]
    rw [hxux]
    exact huc g
  have hxtnc : q x ∉ Subgroup.center (X ⧸ Z) := by
    intro hc
    apply hM
    refine eq_top_iff.mpr fun g _ => centralizer_le_of_unique huniq ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hqg : q (g⁻¹ * x * g) = q x := by
      rw [map_mul, map_mul, map_inv, mul_assoc, ← (Subgroup.mem_center_iff.mp hc (q g)),
        inv_mul_cancel_left]
    obtain ⟨w, hw, hwx⟩ := (QuotientGroup.mk'_eq_mk' Z).mp hqg.symm
    rcases (hmemZ w).mp hw with rfl | rfl
    · rw [mul_one] at hwx
      calc g * x = g * (g⁻¹ * x * g) := by rw [← hwx]
        _ = x * g := by group
    · exfalso
      apply hux
      rw [← huc x, hwx]
      exact class_conj_mem (distinguished_mem_pointClass x) g
  obtain ⟨tt, htt, hxtt, hne⟩ : ∃ tt ∈ involutionPointClass (q x), Commute (q x) tt ∧ tt ≠ q x := by
    by_contra h
    apply hxtnc
    apply mem_center_of_isolated hOt hxt2 h2t.1
    intro t ht hxt
    by_contra hne
    exact h ⟨t, ht, hxt, hne⟩
  rcases hN with hrank | ⟨ut, hut2, hutc, -, -, hse, hcls⟩
  · exfalso
    exact hne (CFSG.TwoRankLowerBound.Helpers.commuting_involutions_eq_of_twoRank_le_one _ hrank
      (q x) tt hxt2 (class_orderOf hxt2 htt) hxtt).symm
  obtain ⟨hB, hperf⟩ := bender_derived_of_split hxt2 hOt hhullt hxtnc htt hxtt hne hutc hut2
    hse hcls
  by_cases huD : u ∈ commutator X
  · exact (false_of_central_mem_commutator hcov hx hM huniq h2.1 hhull hu hu2 Z hZ hB hperf
      huD).elim
  · exact normSplit_of_central_not_mem hx hhull hu hu2 Z hZ hZM hse huD

end CFSG.ComponentClassification.AschbacherStrongEmbedding
