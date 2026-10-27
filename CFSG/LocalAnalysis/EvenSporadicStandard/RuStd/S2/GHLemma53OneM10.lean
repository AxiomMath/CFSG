module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeM10
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6M10
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21GenA6
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinA6

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup CFSG.Open CFSG.QuasithinUnique

private theorem eq_ofAdd_one_of_ne_one :
    ∀ g : Multiplicative (ZMod 2), g ≠ 1 → g = Multiplicative.ofAdd 1 := by decide

private theorem ofAdd_one_ne_one : (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) ≠ 1 := by
  decide

private theorem ofAdd_one_mul_self :
    (Multiplicative.ofAdd 1 * Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) = 1 := by
  decide

theorem exists_index_two_alt6_of_M10 :
    ∃ A : Subgroup M10, Nonempty (↥A ≃* A6) ∧ A.index = 2 ∧
      ∀ m : M10, m * m = 1 → m ∈ A := by
  obtain ⟨φ⟩ := CFSG.QuasithinUnique.Unc25G2.nonempty_stabilizer_zero_equiv_m10
  obtain ⟨ψ⟩ := CFSG.QuasithinUnique.Out21.A6.exists_psl29_equiv
  let B : Subgroup ↥A6Models.m10 := A6Models.psl29.subgroupOf A6Models.m10
  let A : Subgroup M10 := B.map φ.symm.toMonoidHom
  have hle : A6Models.psl29 ≤ A6Models.m10 := CFSG.QuasithinUnique.Out21.A6.psl29_le_m10
  have hcardB : Nat.card ↥B = 360 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      CFSG.QuasithinUnique.A6Facts.card_psl29]
  refine ⟨A, ?_, ?_, ?_⟩
  · exact ⟨(Subgroup.equivMapOfInjective B φ.symm.toMonoidHom φ.symm.injective).symm.trans
      ((Subgroup.subgroupOfEquivOfLe hle).trans ψ)⟩
  · rw [Subgroup.index_map_of_bijective φ.symm.bijective]
    have hcm := Subgroup.card_mul_index B
    rw [hcardB, CFSG.QuasithinUnique.Out21.A6.card_m10] at hcm
    omega
  · intro m hm
    have hm2 : (φ m : ↥A6Models.m10) * (φ m : ↥A6Models.m10) = 1 := by
      rw [← map_mul, hm, map_one]
    have hval : ((φ m : ↥A6Models.m10) : Equiv.Perm (Fin 10)) *
        ((φ m : ↥A6Models.m10) : Equiv.Perm (Fin 10)) = 1 := by
      simpa using congrArg Subtype.val hm2
    have hmem : (φ m : ↥A6Models.m10) ∈ B := by
      rw [Subgroup.mem_subgroupOf]
      exact CFSG.QuasithinUnique.Out21.A6.m10_involution_mem_psl29 (φ m).2 hval
    rw [Subgroup.mem_map]
    exact ⟨φ m, hmem, φ.symm_apply_apply m⟩

theorem snd_eq_one_of_mem_center_prod_M10
    {a : Multiplicative (ZMod 2) × M10} (ha : a ∈ center (Multiplicative (ZMod 2) × M10)) :
    a.2 = 1 := by
  have h : a.2 ∈ Subgroup.center M10 := by
    rw [Subgroup.mem_center_iff]
    intro m
    have hm := Subgroup.mem_center_iff.1 ha (1, m)
    have h2 := congrArg Prod.snd hm
    simpa using h2
  rw [center_M10_eq_bot, Subgroup.mem_bot] at h
  exact h

theorem mulEquiv_central_involution_prod_M10 {Q : Type*} [Group Q]
    (φ : Q ≃* Multiplicative (ZMod 2) × M10) {z : Q} (hz : z ∈ center Q) (hz1 : z ≠ 1) :
    φ z = (Multiplicative.ofAdd 1, 1) := by
  have hcenter : φ z ∈ Subgroup.center (Multiplicative (ZMod 2) × M10) := by
    rw [Subgroup.mem_center_iff]
    intro a
    calc a * φ z = φ (φ.symm a) * φ z := by rw [φ.apply_symm_apply]
      _ = φ (φ.symm a * z) := by rw [map_mul]
      _ = φ (z * φ.symm a) := by rw [Subgroup.mem_center_iff.1 hz (φ.symm a)]
      _ = φ z * φ (φ.symm a) := by rw [map_mul]
      _ = φ z * a := by rw [φ.apply_symm_apply]
  have h2 : (φ z).2 = 1 := snd_eq_one_of_mem_center_prod_M10 hcenter
  have h1 : (φ z).1 ≠ 1 := by
    intro h
    apply hz1
    apply φ.injective
    have hz1' : φ z = 1 := Prod.ext h h2
    rw [hz1', map_one]
  exact Prod.ext (eq_ofAdd_one_of_ne_one _ h1) h2

theorem exists_alt6_subgroup_of_mulEquiv_prod_M10 {Q : Type*}
    [Group Q] (φ : Q ≃* Multiplicative (ZMod 2) × M10) {z : Q}
    (hz : φ z = (Multiplicative.ofAdd 1, 1)) :
    ∃ Ab : Subgroup Q, Nonempty (↥Ab ≃* A6) ∧ z ∉ Ab ∧ (Ab ⊔ zpowers z).index = 2 ∧
      ∀ h : Q, h * h ∈ zpowers z → h ∈ Ab ⊔ zpowers z := by
  obtain ⟨A, ⟨eA⟩, hAidx, hAinv⟩ := exists_index_two_alt6_of_M10
  have hz' : φ.toMonoidHom z = (Multiplicative.ofAdd 1, 1) := hz
  set A' : Subgroup (Multiplicative (ZMod 2) × M10) :=
    A.map (MonoidHom.inr (Multiplicative (ZMod 2)) M10) with hA'def
  set B' : Subgroup (Multiplicative (ZMod 2) × M10) :=
    (⊤ : Subgroup (Multiplicative (ZMod 2))).prod A with hB'def
  set Ab : Subgroup Q := A'.comap φ.toMonoidHom with hAbdef
  have hA'leB' : A' ≤ B' := by
    intro x hx
    rw [hA'def] at hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    rw [hB'def]
    exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, ha⟩
  have hmap : Ab.map φ.toMonoidHom = A' := by
    rw [hAbdef, Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr φ.surjective, top_inf_eq]
  have hA'equiv : ↥A' ≃* A6 := by
    rw [hA'def]
    exact (Subgroup.equivMapOfInjective A (MonoidHom.inr (Multiplicative (ZMod 2)) M10)
      (fun a b h => congrArg Prod.snd h)).symm.trans eA
  have hsup : Ab ⊔ zpowers z = B'.comap φ.toMonoidHom := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · intro x hx
        rw [Subgroup.mem_comap]
        rw [hAbdef, Subgroup.mem_comap] at hx
        exact hA'leB' hx
      · rw [Subgroup.zpowers_le, Subgroup.mem_comap, hz', hB'def]
        exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.one_mem A⟩
    · intro x hx
      rw [Subgroup.mem_comap] at hx
      rw [hB'def] at hx
      obtain ⟨-, ha⟩ := Subgroup.mem_prod.mp hx
      have hx1 : φ.symm (1, (φ x).2) ∈ Ab := by
        rw [hAbdef, Subgroup.mem_comap]
        change φ (φ.symm (1, (φ x).2)) ∈ A'
        rw [φ.apply_symm_apply, hA'def]
        exact Subgroup.mem_map.mpr ⟨(φ x).2, ha, rfl⟩
      have hx2 : φ.symm ((φ x).1, 1) ∈ zpowers z := by
        rcases eq_or_ne (φ x).1 1 with hg | hg
        · rw [hg]
          change φ.symm (1 : Multiplicative (ZMod 2) × M10) ∈ zpowers z
          rw [map_one]
          exact Subgroup.one_mem _
        · have hgw : ((φ x).1, (1 : M10)) = φ z := by
            rw [hz, eq_ofAdd_one_of_ne_one _ hg]
          rw [hgw, φ.symm_apply_apply]
          exact Subgroup.mem_zpowers z
      have hxeq : φ.symm (1, (φ x).2) * φ.symm ((φ x).1, 1) = x := by
        apply φ.injective
        rw [map_mul, φ.apply_symm_apply, φ.apply_symm_apply]
        exact Prod.ext (one_mul _) (mul_one _)
      rw [← hxeq]
      exact Subgroup.mul_mem_sup hx1 hx2
  have hB'index : B'.index = 2 := by
    have hb := Subgroup.index_prod (⊤ : Subgroup (Multiplicative (ZMod 2))) A
    rw [Subgroup.index_top, hAidx, one_mul] at hb
    rw [hB'def]
    exact hb
  have hAbEquiv : ↥Ab ≃* A6 :=
    (Subgroup.equivMapOfInjective Ab φ.toMonoidHom φ.injective).trans
      ((MulEquiv.subgroupCongr hmap).trans hA'equiv)
  refine ⟨Ab, ⟨⟨hAbEquiv⟩, ?_, ?_, ?_⟩⟩
  · intro hzAb
    rw [hAbdef, Subgroup.mem_comap, hz', hA'def] at hzAb
    obtain ⟨a, -, haeq⟩ := Subgroup.mem_map.mp hzAb
    have h1 : (1 : Multiplicative (ZMod 2)) = Multiplicative.ofAdd 1 := by
      have := congrArg Prod.fst haeq
      simpa using this
    exact ofAdd_one_ne_one h1.symm
  · rw [hsup, Subgroup.index_comap_of_surjective B' φ.surjective]
    exact hB'index
  · intro h hh
    rw [hsup, Subgroup.mem_comap, hB'def]
    have hle : Subgroup.zpowers (Multiplicative.ofAdd 1, (1 : M10)) ≤
        (⊤ : Subgroup (Multiplicative (ZMod 2))).prod (⊥ : Subgroup M10) :=
      Subgroup.zpowers_le.mpr
        (Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr rfl⟩)
    have hmem : φ h * φ h ∈ Subgroup.zpowers (Multiplicative.ofAdd 1, (1 : M10)) := by
      have hφ : φ (h * h) ∈ Subgroup.map φ.toMonoidHom (Subgroup.zpowers z) :=
        Subgroup.mem_map.mpr ⟨h * h, hh, rfl⟩
      rwa [MonoidHom.map_zpowers, hz', map_mul] at hφ
    have hsnd : (φ h * φ h).2 = 1 := by
      have hker := hle hmem
      rw [Subgroup.mem_prod, Subgroup.mem_bot] at hker
      exact hker.2
    have hm2 : (φ h).2 * (φ h).2 = 1 := by simpa using hsnd
    exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, hAinv (φ h).2 hm2⟩

theorem fusionOddCore_eq_bot_of_mulEquiv_prod_M10 {C : Type*}
    [Group C] (e : C ≃* Multiplicative (ZMod 2) × M10) : fusionOddCore C = ⊥ := by
  unfold CFSG.Open.fusionOddCore
  apply le_antisymm
  · rw [sSup_le_iff]
    intro N hN
    obtain ⟨hNnormal, hNodd⟩ := hN
    intro n hn
    rw [Subgroup.mem_bot]
    set N' : Subgroup (Multiplicative (ZMod 2) × M10) :=
      N.map e.toMonoidHom with hN'def
    set K : Subgroup M10 := N'.map (MonoidHom.snd (Multiplicative (ZMod 2)) M10) with hKdef
    have hN'normal : N'.Normal := by
      rw [hN'def]
      exact Subgroup.Normal.map hNnormal e.toMonoidHom e.surjective
    have hN'card : Nat.card ↥N' = Nat.card ↥N := by
      rw [hN'def]
      exact Subgroup.card_map_of_injective e.injective
    have hN'odd : Odd (Nat.card ↥N') := by rw [hN'card]; exact hNodd
    have hKnormal : K.Normal := by
      rw [hKdef]
      exact Subgroup.Normal.map hN'normal (MonoidHom.snd (Multiplicative (ZMod 2)) M10)
        (fun y => ⟨(1, y), rfl⟩)
    have hKodd : Odd (Nat.card ↥K) := by
      rw [hKdef]
      exact Odd.of_dvd_nat hN'odd (Subgroup.card_map_dvd N' (MonoidHom.snd _ _))
    haveI : K.Normal := hKnormal
    have hKbot : K = ⊥ := M10_no_odd_normal K hKodd
    have hn' : e n ∈ N' := by
      rw [hN'def]
      exact Subgroup.mem_map.mpr ⟨n, hn, rfl⟩
    have hsndK : (e n).2 ∈ K := by
      rw [hKdef]
      exact Subgroup.mem_map.mpr ⟨e n, hn', rfl⟩
    rw [hKbot, Subgroup.mem_bot] at hsndK
    have hfst : (e n).1 = 1 := by
      by_contra h1
      have hw : e n = (Multiplicative.ofAdd 1, 1) :=
        Prod.ext (eq_ofAdd_one_of_ne_one _ h1) hsndK
      have hx2 : ((Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)), (1 : M10)) ^ 2 = 1 := by
        rw [pow_two, Prod.mk_mul_mk, ofAdd_one_mul_self, one_mul]
        rfl
      have hxne : ((Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)), (1 : M10)) ≠ 1 := by
        intro h
        exact ofAdd_one_ne_one (by simpa using congrArg Prod.fst h)
      have horder : orderOf (e n) = 2 := by
        rw [hw]
        exact orderOf_eq_prime hx2 hxne
      have hdvd : orderOf (e n) ∣ Nat.card ↥N' := Subgroup.orderOf_dvd_natCard N' hn'
      rw [horder] at hdvd
      obtain ⟨k, hk⟩ := hN'odd
      rcases hdvd with ⟨c, hc⟩
      omega
    have hpair : e n = 1 := Prod.ext hfst hsndK
    apply e.injective
    rw [hpair, map_one]
  · exact bot_le

end CFSG.EvenSporadicStandard.RuStd.S2
