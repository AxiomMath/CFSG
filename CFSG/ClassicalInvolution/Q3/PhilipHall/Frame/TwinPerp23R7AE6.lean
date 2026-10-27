module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R56Zstar
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7E7

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section Model

theorem permQ_eq_one_of_normal {Q : Type*} [Group Q] (ψ : Q →* AE.AEQ 6)
    (hψ : ψ.range = (AE.aeSub 6).map (AE.mkQ 6)) {N : Subgroup Q} (hN : N.Normal)
    (h2 : IsPGroup 2 N) {x : Q} (hx : x ∈ N) : TC.Thin.permQ 6 (ψ x) = 1 := by
  classical
  set M : Subgroup (Equiv.Perm (Fin 6)) := (N.map ψ).map (TC.Thin.permQ 6) with hM
  have hMA : M ≤ alternatingGroup (Fin 6) := by
    rintro _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
    have hy : ψ y ∈ ψ.range := ⟨y, rfl⟩
    rw [hψ] at hy
    obtain ⟨a, ha, hay⟩ := hy
    rw [← hay, TC.Thin.permQ_mkQ]
    exact Equiv.Perm.mem_alternatingGroup.mpr (AE.mem_aeSub.mp ha).2
  have hM2 : IsPGroup 2 M := (h2.map ψ).map _
  haveI hnorm : (M.subgroupOf (alternatingGroup (Fin 6))).Normal := by
    constructor
    intro m hm σ
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    have hσ : (⟨0, (σ : Equiv.Perm (Fin 6))⟩ : AE.Wr 6) ∈ AE.aeSub 6 := by
      refine AE.mem_aeSub.mpr ⟨?_, Equiv.Perm.mem_alternatingGroup.mp σ.2⟩
      unfold AE.Wr.wsum
      simp
    have hr : AE.mkQ 6 ⟨0, (σ : Equiv.Perm (Fin 6))⟩ ∈ ψ.range := by
      rw [hψ]; exact ⟨_, hσ, rfl⟩
    obtain ⟨q, hq⟩ := hr
    obtain ⟨_, ⟨y, hy, rfl⟩, hmy⟩ := hm
    refine ⟨ψ (q * y * q⁻¹), ⟨q * y * q⁻¹, hN.conj_mem y hy q, rfl⟩, ?_⟩
    have hqσ : TC.Thin.permQ 6 (ψ q) = (σ : Equiv.Perm (Fin 6)) := by
      rw [hq, TC.Thin.permQ_mkQ]
    simp only [map_mul, map_inv, hqσ, hmy, Subgroup.coe_mul, Subgroup.coe_inv]
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hxM : TC.Thin.permQ 6 (ψ x) ∈ M := ⟨ψ x, ⟨x, hx, rfl⟩, rfl⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf (alternatingGroup (Fin 6))) with h | h
  · have hmem : (⟨_, hMA hxM⟩ : alternatingGroup (Fin 6)) ∈ M.subgroupOf (alternatingGroup (Fin 6)) :=
      Subgroup.mem_subgroupOf.mpr hxM
    rw [h, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    set c : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2 with hc
    have hcA : c ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup, hc]; decide
    have hcM : c ∈ M := by
      have : (⟨c, hcA⟩ : alternatingGroup (Fin 6)) ∈ M.subgroupOf (alternatingGroup (Fin 6)) := by
        rw [h]; trivial
      exact Subgroup.mem_subgroupOf.mp this
    obtain ⟨k, hk⟩ := hM2 ⟨c, hcM⟩
    have hck : c ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hc3 : c ^ 3 = 1 := by rw [hc]; decide
    have h1 : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2))
      (orderOf_dvd_of_pow_eq_one hc3) (orderOf_dvd_of_pow_eq_one hck)
    have hc1 : c = 1 := orderOf_eq_one_iff.mp h1
    revert hc1
    rw [hc]
    decide

end Model

section E7AE6

variable {n : ℕ}

theorem p23E7AE6_proved : P23E7AE6 n := by
  intro Y _ _ R S t K' W u e g hc _ hE ⟨I⟩
  classical
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hc2 : IsPGroup 2 (Subgroup.zpowers e) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.he2
  obtain ⟨R₁, -, -, -, hR₁, -, hRD, -, -, -, -, -, -, -, -⟩ := e_decomp hc
  obtain ⟨b, hbRW, hb4⟩ := Q3T8.Asc77.Thompson.exists_orderOf_four hΩ hc.std.hW hRD
  have hbK : b ∈ tightCore R := hR₁.1 hbRW.1
  have hbb : b * b = t := TwinPerp.sq_eq_of_orderOf_four hz hbK hb4
  have hR₁e : R₁ ≤ Subgroup.centralizer ({e} : Set Y) :=
    hRD.2.trans (normalizer_le_centralizer_e hd)
  have hKtq : tightCore R ∈ tqMembers3 (Om R) e :=
    ⟨hK, TwinADescent3.mem_tq_of_sylCent hΩ h2 hK ⟨R₁, hR₁, hR₁e⟩⟩
  have hR₁s : IsSylow2In R₁ (TwinADescent.coreAt e (tightCore R)) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hKtq.2).mpr ⟨hR₁, hR₁e⟩
  have h8 : Nat.card R₁ = 8 := (CFSG.ClassicalInvolution.Q8P.ascStand_of_twinCore hC).card8 _ hK R₁ hR₁
  have hgen : TC.Thin.pSpan (TwinDisc.secFam (Om R) e) = ⊤ := (p23_q8Section hc.std.perp hd.he2).gen
  have hmap := TwinPerpV3.coreHull_map_eq_rLayer hΩ hc2 h2
  set C := Subgroup.centralizer ({e} : Set Y) with hCdef
  set H := coreHull (Om R) e with hH
  set O := classicalInvolutionOddCore ↥H with hO
  let ι0 : ↥H ⧸ O →* ↥(TC.Thin.pSpan (TwinDisc.secFam (Om R) e)) :=
    { toFun := fun x => ⟨x, TwinDisc.mem_pSpan_of_top hgen x⟩, map_one' := rfl,
      map_mul' := fun _ _ => rfl }
  let ψ : ↥H ⧸ O →* AE.AEQ 6 := I.φ.comp ι0
  have hψ : ψ.range = (AE.aeSub 6).map (AE.mkQ 6) := by
    rw [← I.range_eq]
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩; exact ⟨ι0 x, rfl⟩
    · rintro _ ⟨y, rfl⟩; exact ⟨(y : ↥H ⧸ O), congrArg I.φ (Subtype.ext rfl)⟩
  let ι : ↥H →* Y := C.subtype.comp H.subtype
  have hιinj : Function.Injective ι :=
    (Subgroup.subtype_injective C).comp (Subgroup.subtype_injective H)
  have hιr : ι.range = rLayer (Om R) e := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hmap]
  set N : Subgroup (↥H ⧸ O) := (W.comap ι).map (QuotientGroup.mk' O) with hN
  have hW2 : IsPGroup 2 W := by
    obtain ⟨η, ⟨S₀, hη, -⟩, hWη⟩ := hc.std.hW
    exact S₀.isPGroup'.to_le (hWη ▸ iSup₂_le fun U hU => (hη.1 hU).2)
  have hN2 : IsPGroup 2 N := (hW2.comap_of_injective ι hιinj).map _
  have hconj : ∀ x : ↥H, ι x ∈ Subgroup.normalizer (W : Set Y) → ∀ m ∈ N,
      QuotientGroup.mk' O x * m * (QuotientGroup.mk' O x)⁻¹ ∈ N := by
    rintro x hx _ ⟨w, hw, rfl⟩
    refine ⟨x * w * x⁻¹, ?_, by simp⟩
    show ι (x * w * x⁻¹) ∈ W
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hx _).mp hw
  have hNn : N.Normal := by
    have hsub : ∀ x : ↥H, ι x ∈ oddCoreOf (rLayer (Om R) e) ⊔
        (rLayer (Om R) e ⊓ Subgroup.normalizer (W : Set Y)) := fun x =>
      hE (hιr ▸ ⟨x, rfl⟩)
    have htop : (⊤ : Subgroup ↥H) ≤ (oddCoreOf (rLayer (Om R) e)).comap ι ⊔
        (rLayer (Om R) e ⊓ Subgroup.normalizer (W : Set Y)).comap ι := by
      rw [Subgroup.comap_sup_eq_of_le_range]
      · exact fun x _ => hsub x
      · rw [hιr]; exact Subgroup.map_subtype_le _
      · rw [hιr]; exact inf_le_left
    have hnorm : (⊤ : Subgroup (↥H ⧸ O)) ≤ Subgroup.normalizer (N : Set (↥H ⧸ O)) := by
      intro q _
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective O q
      have hx := htop (Subgroup.mem_top x)
      have hle : ((oddCoreOf (rLayer (Om R) e)).comap ι ⊔
          (rLayer (Om R) e ⊓ Subgroup.normalizer (W : Set Y)).comap ι).map (QuotientGroup.mk' O) ≤
            Subgroup.normalizer (N : Set (↥H ⧸ O)) := by
        rw [Subgroup.map_sup]
        refine sup_le ?_ ?_
        · rintro _ ⟨y, hy, rfl⟩
          have hyO : y ∈ O := by
            apply R56.mem_oddCore_coreHull_of_mem_oddCoreOf_coreLayer
            show ι y ∈ oddCoreOf (coreLayer (Om R) e)
            unfold coreLayer
            rw [hmap]
            exact hy
          rw [show QuotientGroup.mk' O y = 1 from (QuotientGroup.eq_one_iff y).mpr hyO]
          exact Subgroup.one_mem _
        · rintro _ ⟨y, hy, rfl⟩
          rw [Subgroup.mem_normalizer_iff]
          intro m
          refine ⟨hconj y hy.2 m, fun hm => ?_⟩
          have hy' : ι y⁻¹ ∈ Subgroup.normalizer (W : Set Y) := by
            rw [map_inv]; exact Subgroup.inv_mem _ hy.2
          have := hconj y⁻¹ hy' _ hm
          simpa [mul_assoc] using this
      exact hle ⟨x, hx, rfl⟩
    exact Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr hnorm)
  have hbC : b ∈ C := hR₁e hbRW.1
  have hbcore : b ∈ TwinADescent.coreAt e (tightCore R) := hR₁s.1 hbRW.1
  have hbH : (⟨b, hbC⟩ : ↥C) ∈ H :=
    le_coreHull hKtq (Subgroup.mem_subgroupOf.mpr hbcore)
  set bH : ↥H := ⟨⟨b, hbC⟩, hbH⟩ with hbHdef
  have hbN : QuotientGroup.mk' O bH ∈ N := ⟨bH, hbRW.2, rfl⟩
  have hperm := permQ_eq_one_of_normal ψ hψ hNn hN2 hbN
  have hsq : ψ (QuotientGroup.mk' O (bH * bH)) = 1 := by
    rw [map_mul, map_mul]
    exact TC.Thin.mul_self_of_mem_ker_permQ hperm
  obtain ⟨α, hα, bb, hlab⟩ := I.label _ (TwinDisc.secImg_mem_secFam hKtq)
  have hTt := (hR₁s.subgroupOf (TwinADescent.coreAt_le_centralizer e (tightCore R))).subgroupOf
    (le_coreHull hKtq)
  set A := ((TwinADescent.coreAt e (tightCore R)).subgroupOf C).subgroupOf H with hA
  have hgA : ∀ a : ↥A, ψ (QuotientGroup.mk' O (a : ↥H)) ∈ AE.memBar α hα bb := by
    intro a
    rw [← hlab]
    exact ⟨ι0 (QuotientGroup.mk' O (a : ↥H)), Subgroup.mem_subgroupOf.mpr ⟨a, a.2, rfl⟩, rfl⟩
  let gA : ↥A →* ↥(AE.memBar α hα bb) :=
    ((ψ.comp (QuotientGroup.mk' O)).comp A.subtype).codRestrict _ hgA
  have hgs : Function.Surjective gA := by
    rintro ⟨y, hy⟩
    rw [← hlab] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    obtain ⟨a, ha, hae⟩ := Subgroup.mem_subgroupOf.mp hy'
    refine ⟨⟨a, ha⟩, Subtype.ext ?_⟩
    show ψ (QuotientGroup.mk' O a) = I.φ y'
    exact congrArg I.φ (Subtype.ext hae)
  have hB2 : IsPGroup 2 ↥(AE.memBar α hα bb) :=
    IsPGroup.of_card (n := 3) (by rw [AE.natCard_memBar (by norm_num)]; norm_num)
  have hmapS := map_sylow_eq_of_isPGroup gA hgs hB2 (Uniform.sylowOfIsSylow2In hTt)
  have hrH : ∀ r : ↥R₁, (⟨(r : Y), hR₁e r.2⟩ : ↥C) ∈ H := fun r =>
    le_coreHull hKtq (Subgroup.mem_subgroupOf.mpr (hR₁s.1 r.2))
  let F : ↥R₁ → ↥(AE.memBar α hα bb) := fun r =>
    ⟨ψ (QuotientGroup.mk' O ⟨⟨(r : Y), hR₁e r.2⟩, hrH r⟩), by
      have hrA : (⟨⟨(r : Y), hR₁e r.2⟩, hrH r⟩ : ↥H) ∈ A :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr (hR₁s.1 r.2))
      exact hgA ⟨_, hrA⟩⟩
  have hFs : Function.Surjective F := by
    intro y
    have hy : y ∈ (Uniform.sylowOfIsSylow2In hTt : Subgroup ↥A).map gA := by rw [hmapS]; trivial
    obtain ⟨s, hs0, hsy⟩ := hy
    have hs := hs0
    rw [Uniform.coe_sylowOfIsSylow2In hTt] at hs
    refine ⟨⟨s.1.1.1, hs⟩, ?_⟩
    rw [← hsy]
    rfl
  have hcard : Nat.card ↥R₁ ≤ Nat.card ↥(AE.memBar α hα bb) := by
    rw [h8, AE.natCard_memBar (by norm_num)]
  have hFi := (hFs.bijective_of_nat_card_le hcard).1
  have htR : t ∈ R₁ := hbb ▸ R₁.mul_mem hbRW.1 hbRW.1
  have hF : F ⟨t, htR⟩ = F 1 := by
    apply Subtype.ext
    show ψ (QuotientGroup.mk' O ⟨⟨t, _⟩, _⟩) = ψ (QuotientGroup.mk' O ⟨⟨1, _⟩, _⟩)
    have e1 : (⟨⟨t, hR₁e htR⟩, hrH ⟨t, htR⟩⟩ : ↥H) = bH * bH :=
      Subtype.ext (Subtype.ext hbb.symm)
    have e2 : (⟨⟨(1 : Y), hR₁e (1 : ↥R₁).2⟩, hrH 1⟩ : ↥H) = 1 := rfl
    rw [e1, e2, hsq, map_one, map_one]
  exact hz.ne_one (congrArg Subtype.val (hFi hF))

end E7AE6

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
