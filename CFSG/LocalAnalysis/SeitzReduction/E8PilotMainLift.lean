module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotMainFinal
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotBLiftF4
public import CFSG.LieType.Steinberg.CentralExt.MinusculeCentrallyClosed
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotSwapBLiftSchur
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormalCore
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParamLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (QuadraticFrobenius centralizerPerfectCore)
open CFSG.ComponentClassification.M12Cover.CyclicKernel
  (eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two)
open CFSG.LieType.Steinberg.Minuscule (e7Data_valid)


section Center

variable {K : Type} [Field K] {G : Type} [Group G] {L : Subgroup G}

theorem exists_mem_inv_mul_mem_zpowers_E8 [Finite G] {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* adjointGroup .E8 K) {X : Subgroup G} {Y : Subgroup (adjointGroup .E8 K)}
    (hXc : centralizer (((X.subgroupOf L).map e.toMonoidHom : Subgroup (adjointGroup .E8 K)) :
      Set (adjointGroup .E8 K)) ≤ Y ⊔ e7Levi K)
    (hYD : Y ≤ centralizer (e7Levi K : Set (adjointGroup .E8 K)))
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype) {c : G}
    (hcX : c ∈ centralizer (X : Set G)) (hct : c * t = t * c)
    (hcD : c ∈ centralizer (D : Set G)) :
    ∃ y ∈ (Y.map e.symm.toMonoidHom).map L.subtype, y⁻¹ * c ∈ zpowers t := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hKc
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hKc
  set XC : Subgroup (adjointGroup .E8 K) := (X.subgroupOf L).map e.toMonoidHom with hXCdef
  have hcN : c ∈ normalizer (L : Set G) :=
    CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hL htC ht
      (mem_centralizer_singleton_iff.2 hct)
  set β := L.normalizerMonoidHom ⟨c, hcN⟩ with hβ
  have hβapp : ∀ a : L, ((β a : L) : G) = c * a * c⁻¹ := fun a => by
    simp [hβ, normalizerMonoidHom_apply_apply_coe]
  have hβ'app : ∀ x, MulAut.congr e β x = e (β (e.symm x)) := fun x => by
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  have hfixD : ∀ x ∈ e7Levi K, MulAut.congr e β x = x := by
    intro x hxD
    have hmem : ((e.symm x : L) : G) ∈ D := by
      rw [hDe]
      exact ⟨e.symm x, ⟨x, hxD, rfl⟩, rfl⟩
    have h1 : β (e.symm x) = e.symm x := by
      apply Subtype.ext
      rw [hβapp, ← mem_centralizer_iff.1 hcD _ hmem, mul_inv_cancel_right]
    rw [hβ'app, h1, MulEquiv.apply_symm_apply]
  obtain ⟨g, hg, hgD'⟩ := exists_eq_conj_of_fix_e7Levi _ hfixD
  have hgX : g ∈ centralizer (XC : Set (adjointGroup .E8 K)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    have h1 : β a = a := by
      apply Subtype.ext
      rw [hβapp, ← mem_centralizer_iff.1 hcX _ (mem_subgroupOf.1 ha), mul_inv_cancel_right]
    have h2 : MulAut.congr e β (e a) = e a := by
      rw [hβ'app, MulEquiv.symm_apply_apply, h1]
    rw [hg, MulAut.conj_apply] at h2
    calc e.toMonoidHom a * g = g * e a * g⁻¹ * g := by rw [h2]; rfl
      _ = g * e.toMonoidHom a := by simp
  have hgY : g ∈ Y :=
    F4Pilot.mem_of_mem_sup_of_mem_centralizer hYD center_e7Levi_eq_bot (hXc hgX) hgD'
  set a₀ : L := e.symm g with ha₀
  have hga₀ : e a₀ = g := by rw [ha₀, MulEquiv.apply_symm_apply]
  have hβa : ∀ l : L, β l = a₀ * l * a₀⁻¹ := by
    intro l
    have h1 : MulAut.congr e β (e l) = g * e l * g⁻¹ := by rw [hg, MulAut.conj_apply]
    rw [hβ'app, MulEquiv.symm_apply_apply, ← hga₀] at h1
    apply e.injective
    rw [h1]
    simp
  have hcen : (a₀ : G)⁻¹ * c ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := by
    refine mem_inf.2 ⟨mem_centralizer_iff.2 fun l hl => ?_, ?_⟩
    · have h1 := congrArg Subtype.val (hβa ⟨l, hl⟩)
      rw [hβapp] at h1
      simp only [coe_mul, coe_inv] at h1
      calc l * ((a₀ : G)⁻¹ * c) = (a₀ : G)⁻¹ * ((a₀ : G) * l * (a₀ : G)⁻¹) * c := by group
        _ = (a₀ : G)⁻¹ * (c * l * c⁻¹) * c := by rw [h1]
        _ = (a₀ : G)⁻¹ * c * l := by group
    · rw [mem_centralizer_singleton_iff]
      have hta : (a₀ : G) * t = t * a₀ := mem_centralizer_iff.1 htC _ a₀.2
      have hta' : (a₀ : G)⁻¹ * t = t * (a₀ : G)⁻¹ := by
        calc (a₀ : G)⁻¹ * t = (a₀ : G)⁻¹ * (t * a₀) * (a₀ : G)⁻¹ := by group
          _ = (a₀ : G)⁻¹ * ((a₀ : G) * t) * (a₀ : G)⁻¹ := by rw [hta]
          _ = t * (a₀ : G)⁻¹ := by group
      calc (a₀ : G)⁻¹ * c * t = (a₀ : G)⁻¹ * (c * t) := by group
        _ = (a₀ : G)⁻¹ * (t * c) := by rw [hct]
        _ = ((a₀ : G)⁻¹ * t) * c := by group
        _ = (t * (a₀ : G)⁻¹) * c := by rw [hta']
        _ = t * ((a₀ : G)⁻¹ * c) := by group
  rw [hK] at hcen
  exact ⟨a₀, ⟨a₀, ⟨g, hgY, rfl⟩, rfl⟩, hcen⟩

theorem mem_map_of_mem_oddCore_of_commute_E8 [Finite G] {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* adjointGroup .E8 K) {X : Subgroup G} {Y : Subgroup (adjointGroup .E8 K)}
    (hXc : centralizer (((X.subgroupOf L).map e.toMonoidHom : Subgroup (adjointGroup .E8 K)) :
      Set (adjointGroup .E8 K)) ≤ Y ⊔ e7Levi K)
    (hYD : Y ≤ centralizer (e7Levi K : Set (adjointGroup .E8 K))) (hYodd : Odd (Nat.card Y))
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype)
    (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G)))
    {c : centralizer (X : Set G)} (hc : c ∈ oddCore (centralizer (X : Set G)))
    (hct : c * ⟨t, htX⟩ = ⟨t, htX⟩ * c) : (c : G) ∈ (Y.map e.symm.toMonoidHom).map L.subtype := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hKc
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hKc
  have hOodd : Odd (Nat.card (oddCore (centralizer (X : Set G)))) :=
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  have hLt : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hL htC ht
  have hDLX : D ≤ L ⊓ centralizer (X : Set G) := hD ▸ map_subtype_le _
  have hcD : (c : G) ∈ centralizer (D : Set G) := by
    refine F4Pilot.mem_centralizer_of_mem_oddCore_of_commute htX (hDLX.trans inf_le_right)
      (fun d hd => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (hDLX hd).1))
      (hDe ▸ isQuasisimple_map_e7Levi e) (fun m hm d hd => ?_) hc hct
    have hd' : d ∈ inSubgroup layer (L ⊓ centralizer (X : Set G)) := hD ▸ hd
    have := layer_centralizer_normalized hLt hm hd'
    rwa [← hD] at this
  obtain ⟨y, hy, hyc⟩ := exists_mem_inv_mul_mem_zpowers_E8 hKc hL htC ht hK e hXc hYD hDe c.2
    (congrArg Subtype.val hct) hcD
  set Y' : Subgroup G := (Y.map e.symm.toMonoidHom).map L.subtype with hY'
  have hY'L : Y' ≤ L := map_subtype_le _
  have hY'odd : Odd (Nat.card Y') := by
    rw [hY', card_map_of_injective L.subtype_injective,
      card_map_of_injective e.symm.injective]
    exact hYodd
  rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two ht hyc with h1 | h1
  · have hcy : (c : G) = y := by
      calc (c : G) = y * (y⁻¹ * c) := by group
        _ = y := by rw [h1, mul_one]
    rw [hcy]
    exact hy
  · exfalso
    have hcodd : Odd (orderOf (c : G)) := by
      rw [orderOf_submonoid]
      exact hOodd.of_dvd_nat ((oddCore (centralizer (X : Set G))).orderOf_dvd_natCard hc)
    have hyt : y * t = t * y := mem_centralizer_iff.1 htC y (hY'L hy)
    have hcy : (c : G) = y * t := by
      calc (c : G) = y * (y⁻¹ * c) := by group
        _ = y * t := by rw [h1]
    obtain ⟨j, hj⟩ := hcodd
    have hpow : (c : G) ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one _
    have htt : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
    rw [hcy, (show Commute y t from hyt).mul_pow, pow_succ t, pow_mul, htt, one_pow,
      one_mul] at hpow
    have htY : t ∈ Y' := by
      have : t = (y ^ (2 * j + 1))⁻¹ := eq_inv_of_mul_eq_one_right hpow
      rw [this]
      exact Y'.inv_mem (Y'.pow_mem hy _)
    have h2 := Y'.orderOf_dvd_natCard htY
    rw [ht] at h2
    exact (Nat.not_even_iff_odd.2 hY'odd) (even_iff_two_dvd.2 h2)

theorem mem_center_of_mem_oddCore_of_commute_highTorusLine_E8 [Finite G] {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* adjointGroup .E8 K) (htX : t ∈ centralizer (rootTorusG e : Set G)) :
    ∀ c ∈ oddCore (centralizer (rootTorusG e : Set G)), c * ⟨t, htX⟩ = ⟨t, htX⟩ * c →
      c ∈ center (centralizer (rootTorusG e : Set G)) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hKc
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hKc
  have hq : 4 ≤ Nat.card K := by
    rw [hKc]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  set A : Subgroup (adjointGroup .E8 K) :=
    (EPilot.highTorusLine .E8 K).subgroupOf (adjointGroup .E8 K) with hAdef
  have hX : rootTorusG e = (A.map e.symm.toMonoidHom).map L.subtype := rfl
  obtain ⟨c₀, hc₀⟩ := F4Pilot.exists_three_le_orderOf hq
  have hA : centralizer (A : Set (adjointGroup .E8 K)) = A ⊔ e7Levi K :=
    E6Pilot.centralizer_eq_highTorusLine_sup_of_le (τ := .E8) (Or.inr (Or.inr rfl)) hc₀ le_rfl
      (Subgroup.mem_subgroupOf.2 (EPilot.rootDiagUnit_highDiag_mem_highTorusLine c₀))
  have hYD : A ≤ centralizer (e7Levi K : Set (adjointGroup .E8 K)) :=
    E6Pilot.highTorusLine_subgroupOf_le_centralizer_perpLevi
  have hYodd : Odd (Nat.card A) := by
    rw [hAdef, Nat.card_congr (subgroupOfEquivOfLe
      (E6Pilot.highTorusLine_le_adjointGroup (Or.inr (Or.inr rfl)))).toEquiv]
    exact E6Pilot.odd_card_highTorusLine (F4Pilot.one_le_of_natCard_eq_two_pow hKc) hKc
  have hXc : centralizer ((((rootTorusG e).subgroupOf L).map e.toMonoidHom :
      Subgroup (adjointGroup .E8 K)) : Set (adjointGroup .E8 K)) ≤ A ⊔ e7Levi K := by
    rw [hX, F4Pilot.map_subgroupOf_map_symm]
    exact hA.le
  have hD : rootLeviG e = inSubgroup layer (L ⊓ centralizer (rootTorusG e : Set G)) :=
    (inSubgroup_layer_inf_centralizer_highTorusLine_E8 e hq).symm
  intro c hc hct
  have hcY := mem_map_of_mem_oddCore_of_commute_E8 hKc hL htC ht hK e hXc hYD hYodd htX rfl hD hc
    hct
  have hcX : (c : G) ∈ rootTorusG e := hcY
  rw [mem_center_iff]
  intro h
  exact Subtype.ext (mem_centralizer_iff.1 h.2 _ hcX).symm

end Center

section Closure

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem injective_of_surjective_of_le_center_E7 (hF : 5 ≤ Nat.card F) {P : Type*} [Group P]
    [Group.IsPerfect P] (π : P →* adjointGroup .E7 F) (hπ : Function.Surjective π)
    (hker : π.ker ≤ center P) : Function.Injective π := by
  set ε : e7Data_valid.minGroup F ≃* adjointGroup .E7 F := e7MinEquivAdjoint F with hε
  set π' : P →* e7Data_valid.minGroup F := ε.symm.toMonoidHom.comp π with hπ'def
  have hπ' : Function.Surjective π' := ε.symm.surjective.comp hπ
  have hker' : π'.ker = π.ker := by
    ext x
    simp only [hπ'def, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  obtain ⟨σ, hσ⟩ :=
    CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.e7_exists_section_of_central hF hπ'
      (hker' ▸ hker)
  have hinj := F4Pilot.injective_of_section_of_perfect π' (hker' ▸ hker) σ hσ
  intro a b hab
  apply hinj
  simp only [hπ'def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hab]

end Closure

section Transport

theorem baseChangeGL_mem_adjointGroup_E7 {K K' : Type} [Field K] [Field K'] (ε : K →+* K')
    (g : adjointGroup .E7 K) : baseChangeGL ε (g : ModGL .E7 K) ∈ adjointGroup .E7 K' :=
  map_baseChangeGL_adjointGroup_le ε ⟨g, g.2, rfl⟩

@[expose] noncomputable def adjointGroupE7RingEquiv {K K' : Type} [Field K] [Field K']
    (ε : K ≃+* K') : adjointGroup .E7 K ≃* adjointGroup .E7 K' where
  toFun g := ⟨baseChangeGL (ε : K →+* K') g, baseChangeGL_mem_adjointGroup_E7 _ g⟩
  invFun g := ⟨baseChangeGL (ε.symm : K' →+* K) g, baseChangeGL_mem_adjointGroup_E7 _ g⟩
  left_inv g := by
    apply Subtype.ext
    change baseChangeGL (ε.symm : K' →+* K) (baseChangeGL (ε : K →+* K') (g : ModGL .E7 K)) = g
    rw [baseChangeGL_baseChangeGL]
    have h : ((ε.symm : K' →+* K).comp (ε : K →+* K')) = RingHom.id K := by
      ext c
      simp
    rw [h, baseChangeGL_id]
  right_inv g := by
    apply Subtype.ext
    change baseChangeGL (ε : K →+* K') (baseChangeGL (ε.symm : K' →+* K) (g : ModGL .E7 K')) = g
    rw [baseChangeGL_baseChangeGL]
    have h : ((ε : K →+* K').comp (ε.symm : K' →+* K)) = RingHom.id K' := by
      ext c
      simp
    rw [h, baseChangeGL_id]
  map_mul' g h := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, map_mul]

end Transport

section Lift

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem nonempty_adjointGroupE7_mulEquiv_neighbourCore_high {t : G} {f : ℕ}
    (hw : E8Work L K t f) (hf : 2 ≤ f) (e : L ≃* adjointGroup .E8 K) (hX : HR8FieldE8 e t f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ (2 * f) ∧
      Nonempty (adjointGroup .E7 F ≃* neighbourCore e .high) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hw.card_eq
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hw.card_eq
  have htC := hw.mem_centralizer
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have hKt := hw.inf_eq e
  set X : Subgroup G := rootTorusG e with hXdef
  set H : Subgroup G := centralizer (X : Set G) with hHdef
  set D : Subgroup G := rootLeviG e with hDdef
  obtain ⟨htX, Kb, hKb, -, -, hlt, hsK, hsN, hov⟩ := hX
  set π := QuotientGroup.mk' (oddCore H) with hπ
  set Db : Subgroup (H ⧸ oddCore H) := (D.subgroupOf H).map π with hDbdef
  set t' : H := ⟨t, htX⟩ with ht'def
  set s : H ⧸ oddCore H := π t' with hsdef
  have ht't' : t' * t' = 1 := Subtype.ext htt
  have hss : s * s = 1 := by rw [hsdef, ← map_mul, ht't', map_one]
  have hsC : s ∉ centralizer (Kb : Set (H ⧸ oddCore H)) := by
    intro hc
    refine hov.1 ⟨1, MulEquiv.ext fun k => Subtype.ext ?_⟩
    rw [map_one, MulAut.one_apply, F4Pilot.coe_normalizerMonoidHom_mk_apply Kb hsN,
      ← mem_centralizer_iff.1 hc k k.2, mul_inv_cancel_right]
  have hs1 : s ≠ 1 := fun h => hsK (h ▸ one_mem Kb)
  have hs2 : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hss) hs1
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (map_subtype_le _ hd))
  have hsD : s ∈ centralizer (Db : Set (H ⧸ oddCore H)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [hsdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_E8_highTorusLine hw.standard.standard htC
    hw.orderOf_eq hKt hf hw.card_eq e (X := X) rfl htX (D := D) rfl
  obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ :=
    exists_mulEquiv_adjointQuotient_of_lieModel (.inr (.inr (.inl rfl))) hov.2.2.1
  have : CharP F 2 := F4Pilot.charP_two_of_natCard_eq_two_pow hF
  have hF5 : 5 ≤ Nat.card F := by
    rw [hF]
    calc 5 ≤ 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  set ε : Kb ⧸ center Kb ≃* adjointGroup .E7 F :=
    eF.trans (CFSG.RankThree.Chevalley.adjointQuotientEquiv .E7 F) with hε
  have hKbP : Group.IsPerfect Kb := hKb.1.1
  set η : Kb →* adjointGroup .E7 F := ε.toMonoidHom.comp (QuotientGroup.mk' (center Kb)) with hη
  have hηs : Function.Surjective η := ε.surjective.comp (QuotientGroup.mk'_surjective _)
  have hηker : η.ker = center Kb := by
    ext x
    rw [MonoidHom.mem_ker, hη, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hηinj := injective_of_surjective_of_le_center_E7 hF5 η hηs hηker.le
  set eK : Kb ≃* adjointGroup .E7 F := MulEquiv.ofBijective η ⟨hηinj, hηs⟩ with heK
  have hOut : Group.IsSolvable (Outer Kb) :=
    (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism eK).2.mpr
      ⟨⟨2, (exceptional_E_pinned_model_Schreier F).2.1⟩⟩
  have hcore := LinearPilot.perfectCore_top_eq_of_isComponent
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot H) hKb hlt.le hs2 hsD hsN hsC hsyl hOut
  have hC := mem_center_of_mem_oddCore_of_commute_highTorusLine_E8 hw.card_eq hf
    hw.standard.standard htC hw.orderOf_eq hKt e htX
  have hB : F4Pilot.HasBLift Kb := F4Pilot.hasBLift_of_le_center ht't' (isPerfect_iff.mp hKbP)
    hsN (F4Pilot.le_commutator_zpowers_of_isQuasisimple hKb.1 hsN hsC) hC
  obtain ⟨qh, hqs, hqker, -⟩ :=
    LinearPilot.exists_surjective_centralizerPerfectCore_of_perfectCore_eq hcore hB
  set η' : centralizerPerfectCore X →* adjointGroup .E7 F := eK.toMonoidHom.comp qh with hη'
  have hη's : Function.Surjective η' := eK.surjective.comp hqs
  have hη'ker : η'.ker = qh.ker := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hη', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hEperf : Group.IsPerfect (centralizerPerfectCore X) :=
    isPerfect_iff.mpr (F4Pilot.commutator_centralizerPerfectCore X)
  have hinj := injective_of_surjective_of_le_center_E7 hF5 η' hη's (hη'ker ▸ hqker)
  have hE : neighbourCore e .high = centralizerPerfectCore X := by
    rw [neighbourCore_high]
    rfl
  exact ⟨F, inferInstance, inferInstance, inferInstance, hF,
    ⟨(MulEquiv.ofBijective η' ⟨hinj, hη's⟩).symm.trans (MulEquiv.subgroupCongr hE.symm)⟩⟩

end Lift

theorem e8FieldNeighbourIsoInput_holds : E8FieldNeighbourIsoInput := by
  intro G _ _ L K₂ _ _ _ σ f hq hf e t hw hX
  obtain ⟨F, _, _, _, hF, ⟨Ψ⟩⟩ := nonempty_adjointGroupE7_mulEquiv_neighbourCore_high hw hf e hX
  let := Fintype.ofFinite F
  let := Fintype.ofFinite K₂
  have hc : Fintype.card K₂ = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hq.card_eq, hF]
  exact ⟨((MulEquiv.subgroupCongr (E8Neighbour.levi_high K₂)).trans (e7LeviEquiv K₂)).trans
    ((adjointGroupE7RingEquiv (FiniteField.ringEquivOfCardEq hc)).trans Ψ)⟩

section Main


open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)

theorem seitzExclusion_highE8_of_inputs'' (hGLS : GLS3OddLieAutComponentsInput)
    (hE7Odd : E7NotOddLieInput) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hSCT : E8SwapRowCTInput)
    (hSU : E8SwapRowUniqueInput) (h2 : E8TwoInput) :
    SeitzExclusion (HighExceptional .E8) :=
  seitzExclusion_highE8_of_inputs' hGLS hE7Odd hMinn hMcomp e8FieldNeighbourIsoInput_holds hSCT
    hSU h2

end Main

end CFSG.SeitzReduction.E8Pilot
