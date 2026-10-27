module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Lift
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Borel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator

section Core

variable {Kg : Type} [Group Kg] [Finite Kg] {M : Type} [Group M]

theorem not_three_dvd_card_comap (π : Kg →* M) (hk3 : ¬ 3 ∣ Nat.card π.ker) {Wb : Subgroup M}
    (hW2 : IsPGroup 2 Wb) : ¬ 3 ∣ Nat.card (Wb.comap π) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P : Subgroup Kg := Wb.comap π with hP
  set g : ↥P →* M := π.comp P.subtype with hg
  have hrange : g.range ≤ Wb := by
    rintro _ ⟨x, rfl⟩
    exact x.2
  have hgr : IsPGroup 2 g.range := hW2.to_le hrange
  haveI : Finite g.range := Finite.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  have hcard : Nat.card ↥P = Nat.card g.range * Nat.card g.ker := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv] at h1
    rw [h1]
  intro h3
  rw [hcard] at h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h | h
  · obtain ⟨k, hk⟩ := hgr.exists_card_eq
    rw [hk] at h
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
    omega
  · exact hk3 (h.trans (card_ker_comp_subtype_dvd π P))

theorem exists_two_local_lift (π : Kg →* M) (hπ : Function.Surjective π)
    (hk3 : ¬ 3 ∣ Nat.card π.ker) {Eb Wb : Subgroup M} (hE : IsElemAbelian 3 Eb)
    (hW2 : IsPGroup 2 Wb) (hW1 : Wb ≠ ⊥) (hEW : Eb ≤ Subgroup.normalizer (Wb : Set M)) :
    ∃ W T : Subgroup Kg, IsElemAbelian 3 W ∧ W.map π = Eb ∧
      Function.Injective (π.comp W.subtype) ∧ IsPGroup 2 T ∧
      W ≤ Subgroup.normalizer (T : Set Kg) ∧ ∃ t ∈ T, π t ≠ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨W, hW3, hWmap, hWinj⟩ := exists_pSubgroup_lift Nat.prime_three π hk3 hE.isPGroup
    (by rw [MonoidHom.range_eq_top.2 hπ]; exact le_top)
  have hWe : IsElemAbelian 3 W := isElemAbelian_of_injective_comp_subtype π hWinj (hWmap ▸ hE)
  set P : Subgroup Kg := Wb.comap π with hP
  have hWN : W ≤ Subgroup.normalizer (P : Set Kg) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hπw : π w ∈ Subgroup.normalizer (Wb : Set M) :=
      hEW (hWmap ▸ Subgroup.mem_map_of_mem π hw)
    have := Subgroup.mem_normalizer_iff.1 hπw (π x)
    simpa [hP, Subgroup.mem_comap] using this
  have hPcop : ¬ 3 ∣ Nat.card P := not_three_dvd_card_comap π hk3 hW2
  let φ : ↥W →* MulAut ↥P := P.normalizerMonoidHom.comp (Subgroup.inclusion hWN)
  let _inst : MulDistribMulAction ↥W ↥P := MulDistribMulAction.compHom ↥P φ
  obtain ⟨S, hS⟩ := c25_exists_invariant_sylow (A := ↥W) (P := ↥P) hW3 hPcop
  set T : Subgroup Kg := (S : Subgroup ↥P).map P.subtype with hT
  have hT2 : IsPGroup 2 ↥T :=
    (S.isPGroup').of_equiv ((S : Subgroup ↥P).equivMapOfInjective P.subtype P.subtype_injective)
  have hWT : W ≤ Subgroup.normalizer (T : Set Kg) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    have hφ : ∀ (w' : ↥W) (x : ↥P), (((φ w') x : ↥P) : Kg) = (w' : Kg) * (x : Kg) * (w' : Kg)⁻¹ :=
      fun _ _ => rfl
    intro g
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := hS ⟨w, hw⟩ x hx
      exact ⟨φ ⟨w, hw⟩ • x, this, hφ ⟨w, hw⟩ x⟩
    · rintro ⟨y, hy, hyg⟩
      have hg : g ∈ P := by
        have h1 : w * g * w⁻¹ ∈ P := hyg ▸ y.2
        have h2 := (Subgroup.mem_normalizer_iff.1 (hWN hw) g).2 h1
        exact h2
      have := hS ⟨w, hw⟩⁻¹ y hy
      refine ⟨_, this, ?_⟩
      show (((⟨w, hw⟩⁻¹ : ↥W) : Kg)) * (y : Kg) * (((⟨w, hw⟩⁻¹ : ↥W) : Kg))⁻¹ = g
      have hyg' : (y : Kg) = w * g * w⁻¹ := hyg
      rw [hyg']
      show w⁻¹ * (w * g * w⁻¹) * w⁻¹⁻¹ = g
      group
  refine ⟨W, T, hWe, hWmap, hWinj, hT2, hWT, ?_⟩
  let f : ↥P →* ↥Wb := π.subgroupComap Wb
  have hf : Function.Surjective f := by
    intro w
    obtain ⟨x, hx⟩ := hπ (w : M)
    exact ⟨⟨x, by simp [hP, Subgroup.mem_comap, hx]⟩, Subtype.ext hx⟩
  haveI : Finite Wb := Finite.of_surjective f hf
  have htop : IsPGroup 2 (⊤ : Subgroup ↥Wb) := hW2.of_equiv Subgroup.topEquiv.symm
  have hmap : (S : Subgroup ↥P).map f = ⊤ := by
    have h1 : ((Sylow.mapSurjective hf S : Sylow 2 ↥Wb) : Subgroup ↥Wb) = ⊤ :=
      ((Sylow.mapSurjective hf S).3 htop le_top).symm
    simpa [Sylow.coe_mapSurjective] using h1
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hW1
  have hmem : a ∈ (S : Subgroup ↥P).map f := by rw [hmap]; trivial
  obtain ⟨x, hxS, hxa⟩ := hmem
  refine ⟨(x : Kg), ⟨x, hxS, rfl⟩, fun h1 => ha ?_⟩
  apply Subtype.ext
  have : π (x : Kg) = (a : M) := congrArg Subtype.val hxa
  rw [← this, h1]
  rfl

end Core

section Sub

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {M : Type} [Group M]

theorem exists_two_local_lift_subgroup (π : ↥K →* M) (hπ : Function.Surjective π)
    (hk3 : ¬ 3 ∣ Nat.card π.ker) {Eb Wb : Subgroup M} (hE : IsElemAbelian 3 Eb)
    (hW2 : IsPGroup 2 Wb) (hW1 : Wb ≠ ⊥) (hEW : Eb ≤ Subgroup.normalizer (Wb : Set M)) :
    ∃ (E T : Subgroup G) (W : Subgroup ↥K), E = W.map K.subtype ∧ E ≤ K ∧ IsElemAbelian 3 E ∧
      Nat.card E = Nat.card Eb ∧ W.map π = Eb ∧ Function.Injective (π.comp W.subtype) ∧ T ≤ K ∧
      IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set G) ∧ ∃ t : ↥K, (t : G) ∈ T ∧ π t ≠ 1 := by
  obtain ⟨W, T, hWe, hWmap, hWinj, hT2, hWT, t, htT, hπt⟩ :=
    exists_two_local_lift π hπ hk3 hE hW2 hW1 hEW
  refine ⟨W.map K.subtype, T.map K.subtype, W, rfl, Subgroup.map_subtype_le W, hWe.map K.subtype, ?_,
    hWmap, hWinj, Subgroup.map_subtype_le T, hT2.map K.subtype, ?_, t, ⟨t, htT, rfl⟩, hπt⟩
  · rw [Subgroup.card_map_of_injective K.subtype_injective,
      card_eq_of_injective_comp_subtype π hWinj, hWmap]
  · rintro _ ⟨w, hw, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    have hwn := Subgroup.mem_normalizer_iff.1 (hWT hw)
    have hwn' := Subgroup.mem_normalizer_iff.1 (hWT (W.inv_mem hw))
    intro g
    constructor
    · rintro ⟨t', ht', rfl⟩
      exact ⟨w * t' * w⁻¹, (hwn t').1 ht', by simp⟩
    · rintro ⟨t', ht', hg⟩
      refine ⟨w⁻¹ * t' * w, ?_, ?_⟩
      · have := (hwn' t').1 ht'
        simpa using this
      · have hg' : (t' : G) = (w : G) * g * (w : G)⁻¹ := hg
        show (((w⁻¹ * t' * w : ↥K)) : G) = g
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hg']
        group

theorem exists_E_T_pQuot_of_sub (K : Subgroup G) {Eb Wb : Subgroup (PQuot 3 K)}
    (hE : IsElemAbelian 3 Eb) (hW2 : IsPGroup 2 Wb) (hW1 : Wb ≠ ⊥)
    (hEW : Eb ≤ Subgroup.normalizer (Wb : Set (PQuot 3 K))) :
    ∃ (E T : Subgroup G) (W : Subgroup ↥K), E = W.map K.subtype ∧ E ≤ K ∧ IsElemAbelian 3 E ∧
      Nat.card E = Nat.card Eb ∧ W.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)) = Eb ∧
      Function.Injective ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)).comp W.subtype) ∧
      T ≤ K ∧ IsPGroup 2 T ∧ ¬ T ≤ GLAPPrimeCoreOf 3 K ∧ E ≤ Subgroup.normalizer (T : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π : ↥K →* PQuot 3 K := QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) with hπ
  have hk3 : ¬ 3 ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card
  obtain ⟨E, T, W, hEW', hEK, hEe, hEc, hWmap, hWinj, hTK, hT2, hEN, t, htT, hπt⟩ :=
    exists_two_local_lift_subgroup π (QuotientGroup.mk'_surjective _) hk3 hE hW2 hW1 hEW
  refine ⟨E, T, W, hEW', hEK, hEe, hEc, hWmap, hWinj, hTK, hT2, fun hT => hπt ?_, hEN⟩
  obtain ⟨u, hu, hut⟩ := hT htT
  have hut' : u = t := Subtype.ext hut
  rw [hut'] at hu
  exact (QuotientGroup.eq_one_iff _).2 hu

theorem exists_E_T_pQuot (K : Subgroup G) {Eb : Subgroup (PQuot 3 K)} {s : PQuot 3 K}
    (hE : IsElemAbelian 3 Eb) (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) (hc : ∀ e ∈ Eb, e * s = s * e) :
    ∃ (E T : Subgroup G) (W : Subgroup ↥K), E = W.map K.subtype ∧ E ≤ K ∧ IsElemAbelian 3 E ∧
      Nat.card E = Nat.card Eb ∧ W.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)) = Eb ∧
      Function.Injective ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)).comp W.subtype) ∧
      T ≤ K ∧ IsPGroup 2 T ∧ ¬ T ≤ GLAPPrimeCoreOf 3 K ∧ E ≤ Subgroup.normalizer (T : Set G) :=
  exists_E_T_pQuot_of_sub K hE (isPGroup_zpowers_of_pow_eq_one hs2)
    (by rwa [Ne, Subgroup.zpowers_eq_bot])
    (fun e he => mem_normalizer_zpowers_of_commute (hc e he))

end Sub

end CFSG.LocalAnalysis.GLTheoremA.CatB
