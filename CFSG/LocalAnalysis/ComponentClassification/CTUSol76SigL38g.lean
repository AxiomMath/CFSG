module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigL310

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {N K K' : Subgroup G}

theorem commutator_oddTwoCoreIn_le_of_normalizes {C S Y : Subgroup G} (hSC : S ≤ C)
    (hS2 : IsPGroup 2 S) (hYC : Y ≤ C) (hYodd : Odd (Nat.card Y))
    (hYS : Y ≤ centralizer (S : Set G))
    (hN : C ⊓ centralizer (S : Set G) ≤ normalizer (Y : Set G)) :
    ⁅oddTwoCoreIn C, Y⁆ ≤ oddCoreIn C := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : ↥C →* ↥C ⧸ pPrimeCore 2 ↥C := QuotientGroup.mk' (pPrimeCore 2 ↥C)
  set S' : Subgroup (↥C ⧸ pPrimeCore 2 ↥C) := (S.subgroupOf C).map π
  set Y' : Subgroup (↥C ⧸ pPrimeCore 2 ↥C) := (Y.subgroupOf C).map π
  have hSC2 : IsPGroup 2 (S.subgroupOf C) := hS2.comap_of_injective C.subtype C.subtype_injective
  have hY'odd : Odd (Nat.card Y') := by
    refine hYodd.of_dvd_nat ((card_map_dvd _ _).trans ?_)
    rw [← card_map_of_injective C.subtype_injective, subgroupOf_map_subtype]
    exact card_dvd_of_le inf_le_left
  have hlift : ∀ h : ↥C ⧸ pPrimeCore 2 ↥C, h ∈ centralizer (S' : Set _) →
      ∃ c : ↥C, (c : G) ∈ centralizer (S : Set G) ∧ π c = h := by
    intro h hh
    obtain ⟨c₀, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥C) h
    have hNd : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥C) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card
    have hPN : S.subgroupOf C ≤ normalizer (pPrimeCore 2 ↥C : Set ↥C) := by
      rw [normalizer_eq_top]
      exact le_top
    obtain ⟨n, hn, hcn⟩ := FooteLit.exists_mul_mem_centralizer hSC2 hNd hPN (y := c₀)
      (fun u hu => by
      have hc : π u * π c₀ = π c₀ * π u :=
        (mem_centralizer_iff.mp hh) (π u) (mem_map_of_mem _ hu)
      rw [← QuotientGroup.eq_one_iff]
      change π (c₀⁻¹ * (u * c₀ * u⁻¹)) = 1
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, hc]
      group)
    refine ⟨c₀ * n, mem_centralizer_iff.mpr fun s hs => ?_, ?_⟩
    · have := (mem_centralizer_iff.mp hcn) ⟨s, hSC hs⟩ (mem_subgroupOf.mpr hs)
      exact congrArg Subtype.val this
    · have h1 : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      rw [map_mul, h1, mul_one]
  have hBn : (pCore 2 (↥C ⧸ pPrimeCore 2 ↥C)).Normal := pCore_normal
  have hkey : ⁅pCore 2 (↥C ⧸ pPrimeCore 2 ↥C), Y'⁆ = ⊥ := by
    refine GorensteinWalter.ThompsonPQ.thompson_p_times_q (p := 2) S' Y'
      (pCore 2 (↥C ⧸ pPrimeCore 2 ↥C)) (hSC2.map π) pCore_isPGroup
      (Nat.coprime_two_left.mpr hY'odd) ?_ ?_ ?_ ?_
    · rw [normalizer_eq_top]; exact le_top
    · rw [normalizer_eq_top]; exact le_top
    · rw [commutator_eq_bot_iff_le_centralizer]
      rintro _ ⟨s, hs, rfl⟩
      refine mem_centralizer_iff.mpr ?_
      rintro _ ⟨d, hd, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext ((mem_centralizer_iff.mp (hYS (mem_subgroupOf.mp hd))) s
        (mem_subgroupOf.mp hs)).symm
    · intro b hb
      obtain ⟨hbB, hbS⟩ := mem_inf.mp hb
      obtain ⟨c, hcS, rfl⟩ := hlift b hbS
      rw [mem_centralizer_iff]
      rintro _ ⟨d, hd, rfl⟩
      have hcN : (c : G) ∈ normalizer (Y : Set G) := hN ⟨c.2, hcS⟩
      have hz : c⁻¹ * d⁻¹ * c * d ∈ Y.subgroupOf C := by
        rw [mem_subgroupOf]
        have h1 : (c : G)⁻¹ * (d : G)⁻¹ * (c : G) ∈ Y := by
          have := (mem_normalizer_iff.mp (inv_mem hcN) ((d : G)⁻¹)).mp
            (inv_mem (mem_subgroupOf.mp hd))
          rwa [inv_inv] at this
        simpa using Y.mul_mem h1 (mem_subgroupOf.mp hd)
      have hzB : π (c⁻¹ * d⁻¹ * c * d) ∈ pCore 2 (↥C ⧸ pPrimeCore 2 ↥C) := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        have e : (π c)⁻¹ * (π d)⁻¹ * π c * π d = (π c)⁻¹ * ((π d)⁻¹ * π c * ((π d)⁻¹)⁻¹) := by
          group
        rw [e]
        exact mul_mem (inv_mem hbB) (hBn.conj_mem _ hbB _)
      obtain ⟨n, hn⟩ := pCore_isPGroup (p := 2) (G := ↥C ⧸ pPrimeCore 2 ↥C) ⟨_, hzB⟩
      have h1 : π (c⁻¹ * d⁻¹ * c * d) = 1 :=
        GrSLit.Sol25.eq_one_of_mem_odd_of_pow hY'odd (mem_map_of_mem _ hz) (n := n)
          (congrArg Subtype.val hn)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      calc π d * π c = π d * π c * ((π c)⁻¹ * (π d)⁻¹ * π c * π d) := by rw [h1, mul_one]
        _ = π c * π d := by group
  rw [commutator_le]
  rintro _ ⟨y, hy, rfl⟩ d hd
  have hdC : d ∈ C := hYC hd
  have hmem : π ⁅y, ⟨d, hdC⟩⁆ = 1 := by
    rw [map_commutatorElement]
    have h := commutator_mem_commutator (mem_comap.mp hy)
      (mem_map_of_mem π (mem_subgroupOf.mpr (show ((⟨d, hdC⟩ : ↥C) : G) ∈ Y from hd)))
    rw [hkey, mem_bot] at h
    exact h
  exact ⟨_, (QuotientGroup.eq_one_iff _).mp hmem, rfl⟩

omit [Finite G] in
theorem exists_subgroup_commutator_mem {C A O : Subgroup G} (hOC : C ≤ normalizer (O : Set G)) :
    ∃ Kc : Subgroup G, ∀ x : G, x ∈ Kc ↔ x ∈ C ∧ ∀ a ∈ A, ⁅a, x⁆ ∈ O := by
  refine ⟨{ carrier := {x | x ∈ C ∧ ∀ a ∈ A, ⁅a, x⁆ ∈ O}
            one_mem' := ⟨C.one_mem, fun a _ => by simp [commutatorElement_def]⟩
            mul_mem' := ?_
            inv_mem' := ?_ }, fun x => Iff.rfl⟩
  · rintro x y ⟨hxC, hx⟩ ⟨hyC, hy⟩
    refine ⟨C.mul_mem hxC hyC, fun a ha => ?_⟩
    have e : ⁅a, x * y⁆ = ⁅a, x⁆ * (x * ⁅a, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact O.mul_mem (hx a ha) ((mem_normalizer_iff.mp (hOC hxC) _).mp (hy a ha))
  · rintro x ⟨hxC, hx⟩
    refine ⟨C.inv_mem hxC, fun a ha => ?_⟩
    have e : ⁅a, x⁻¹⁆ = x⁻¹ * ⁅a, x⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (mem_normalizer_iff.mp (hOC (C.inv_mem hxC)) _).mp (O.inv_mem (hx a ha))

theorem twoLayerIn_centralizer_le_of_forall_or {V X : Subgroup G} (hV : IsKleinFour V) {v : G}
    (hvV : v ∈ V) (hv1 : v ≠ 1) (hLv : twoLayerIn (centralizer ({v} : Set G)) ≤ X) {s : G}
    (hs2 : orderOf s = 2) (hVs : V ≤ centralizer ({s} : Set G))
    (hOX : oddCoreIn (centralizer ({s} : Set G)) ≤ X)
    (h : ∀ J : Subgroup G, IsTwoComponentIn J (centralizer ({s} : Set G)) →
      v ∈ coreActionKernel J ∨ J ≤ X) :
    twoLayerIn (centralizer ({s} : Set G)) ≤ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv2 : orderOf v = 2 := orderOf_eq_two_of_isKleinFour hV hvV hv1
  have hsv : s ∈ centralizer ({v} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hVs hvV)).symm
  have hbal : twoLayerIn (centralizer ({v} : Set G) ⊓ centralizer ({s} : Set G)) ≤
      twoLayerIn (centralizer ({v} : Set G)) := by
    have h := GrSLit.pLayer_inf_centralizer_le (Y := centralizer ({v} : Set G))
      (A := zpowers s) (zpowers_le.mpr hsv)
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs2, pow_one]))
    rw [centralizer_zpowers_eq] at h
    exact h
  refine twoLayerIn_le_of_forall fun J hJ => ?_
  rcases h J hJ with hvJ | hJX
  swap
  · exact hJX
  have hJq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J) :=
    isQuasisimple_quotient_of_isPComponent hJ.1 hJ.2
  have hsupY : (J ⊓ centralizer ({v} : Set G)) ⊔ oddCoreIn J = J := by
    have h := inf_centralizer_sup_oddCoreIn_eq
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv2, pow_one])) (zpowers_le.mpr hvJ)
    rwa [centralizer_zpowers_eq] at h
  obtain ⟨hR2, -, hRsup, -⟩ := cover_facts hJq inf_le_left hsupY
  have hYC : J ⊓ centralizer ({v} : Set G) ≤
      centralizer ({v} : Set G) ⊓ centralizer ({s} : Set G) :=
    le_inf inf_le_right (inf_le_left.trans hJ.1)
  have hsub : ((J ⊓ centralizer ({v} : Set G)).subgroupOf
      (centralizer ({v} : Set G) ⊓ centralizer ({s} : Set G))).IsSubnormal := by
    have h0 : (J.subgroupOf (centralizer ({s} : Set G))).IsSubnormal :=
      ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ hJ.1).mp hJ.2).1
    have h1 := isSubnormal_subgroupOf_of_le
      (inf_le_right : centralizer ({v} : Set G) ⊓ centralizer ({s} : Set G) ≤ _) h0
    convert h1 using 1
    ext x
    simp only [mem_subgroupOf, mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, (mem_inf.mp x.2).1⟩⟩
  have hRC : IsTwoComponentIn (oddResidualIn (J ⊓ centralizer ({v} : Set G)))
      (centralizer ({v} : Set G) ⊓ centralizer ({s} : Set G)) :=
    ⟨hR2.1.trans hYC, GrSLit.isPComponent_subgroupOf_of_isSubnormal hR2.1 hYC hsub hR2.2⟩
  calc J = oddResidualIn (J ⊓ centralizer ({v} : Set G)) ⊔ oddCoreIn J := hRsup.symm
    _ ≤ X := sup_le ((le_twoLayerIn_of_isTwoComponentIn hRC).trans (hbal.trans hLv))
        ((oddCoreIn_le_of_isTwoComponentIn hJ).trans hOX)

theorem twoLayerIn_centralizer_le_of_mem_B (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K) (hKW : K ≤ normalizer (wGroup B V : Set G))
    (hK'W : K' ≤ normalizer (wGroup B V : Set G)) {b : G} (hbB : b ∈ B) (hb1 : b ≠ 1) :
    twoLayerIn (centralizer ({b} : Set G)) ≤ normalizer (wGroup B V : Set G) := by
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.is_comm.comm (⟨x, hx⟩ : B) ⟨y, hy⟩)
  have hb2 : orderOf b = 2 := orderOf_eq_prime (hB.2 b hbB) hb1
  have hbQ : b ∈ coreActionKernel K' := hBQ hbB
  have hBb : B ≤ centralizer ({b} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hBc x hx b hbB)
  have hVb : V ≤ centralizer ({b} : Set G) := le_centralizer_singleton_of_mem hBV hbB
  have hOX := oddCoreIn_centralizer_le_normalizer_wGroup hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB
    hB8 hE hEB hEK hBb hVb
  have hP := conjClosure_le_of_isKleinFour hq hR1 hG hN hK' hK hne.symm hbQ hb2 hE hEK
    (hEB.trans hBb)
  have hVY := le_pump_of_isPGroup hK' hbQ hb2 (isPGroup_of_isKleinFour hV) (le_inf hVK' hVb)
  obtain ⟨v, hvV, hv1⟩ := exists_mem_ne_one_of_isKleinFour hV
  refine twoLayerIn_centralizer_le_of_forall_or hV hvV hv1
    (twoLayerIn_centralizer_le_of_mem_V hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE hEB hEK
      hKW hvV hv1) hb2 hVb hOX fun J hJ => ?_
  rcases pump_moves_of_le hK' hbQ hb2 hP hJ with h | h
  · exact Or.inl ((hVY.trans h) hvV)
  · refine Or.inr (h.trans (sup_le (le_trans ?_ hOX) (((map_subtype_le _).trans
      inf_le_left).trans hK'W)))
    exact oddCoreIn_le_of_le_normalizer (map_subtype_le _) (le_normalizer_twoLayerIn _)

theorem twoLayerIn_centralizer_V_le (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K) (hKW : K ≤ normalizer (wGroup B V : Set G)) :
    twoLayerIn (centralizer (V : Set G)) ≤ normalizer (wGroup B V : Set G) := by
  obtain ⟨v, hvV, hv1⟩ := exists_mem_ne_one_of_isKleinFour hV
  have hVc := comm_of_isKleinFour hV
  have hVv : V ≤ centralizer ({v} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.mpr (hVc w hw v hvV)
  have h := GrSLit.pLayer_inf_centralizer_le (Y := centralizer ({v} : Set G)) (A := V) hVv
    (isPGroup_of_isKleinFour hV)
  have hCV : centralizer ({v} : Set G) ⊓ centralizer (V : Set G) = centralizer (V : Set G) :=
    inf_eq_right.mpr (centralizer_le (Set.singleton_subset_iff.mpr hvV))
  rw [hCV] at h
  exact h.trans (twoLayerIn_centralizer_le_of_mem_V hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8
    hE hEB hEK hKW hvV hv1)

theorem commutator_le_oddCoreIn_of_twoLayerIn_le {C H M X : Subgroup G}
    (hLH : twoLayerIn C ≤ H) (hM : IsTwoComponentIn M C) (hXH : X ≤ oddCoreIn H) (hXC : X ≤ C) :
    ⁅M, X⁆ ≤ oddCoreIn C := by
  have hHO : H ≤ normalizer (oddCoreIn H : Set G) := le_normalizer_oddCoreIn H
  have hML : M ≤ twoLayerIn C := le_twoLayerIn_of_isTwoComponentIn hM
  have hXL : X ≤ normalizer (twoLayerIn C : Set G) := hXC.trans (le_normalizer_twoLayerIn C)
  have h1 : ⁅M, X⁆ ≤ oddCoreIn H ⊓ twoLayerIn C := by
    rw [commutator_le]
    intro m hm x hx
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact (oddCoreIn H).mul_mem ((mem_normalizer_iff.mp (hHO (hLH (hML hm))) x).mp (hXH hx))
        ((oddCoreIn H).inv_mem (hXH hx))
    · rw [commutatorElement_def, mul_assoc, mul_assoc]
      refine (twoLayerIn C).mul_mem (hML hm) ?_
      have := (mem_normalizer_iff.mp (hXL hx) (m⁻¹)).mp ((twoLayerIn C).inv_mem (hML hm))
      simpa [mul_assoc] using this
  refine h1.trans ((inf_le_oddCoreIn (coprime_card_oddCoreIn H)
    ((hLH.trans hHO))).trans ?_)
  exact oddCoreIn_le_of_le_normalizer (map_subtype_le _) (le_normalizer_twoLayerIn C)

theorem inf_centralizer_le_oddCoreIn_of_mem_B (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K) (hKW : K ≤ normalizer (wGroup B V : Set G))
    (hK'W : K' ≤ normalizer (wGroup B V : Set G)) {b : G} (hbB : b ∈ B) (hb1 : b ≠ 1) :
    oddCoreIn (normalizer (wGroup B V : Set G)) ⊓ centralizer ({b} : Set G) ≤
      oddCoreIn (centralizer ({b} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (wGroup B V : Set G)
  set Cb := centralizer ({b} : Set G)
  set X := oddCoreIn H ⊓ Cb with hX
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.is_comm.comm (⟨x, hx⟩ : B) ⟨y, hy⟩)
  have hBb : B ≤ Cb := fun x hx => mem_centralizer_singleton_iff.mpr (hBc x hx b hbB)
  have hVb : V ≤ Cb := le_centralizer_singleton_of_mem hBV hbB
  have hBH : B ≤ H := fun x hx =>
    le_normalizer_wGroup (le_normalizer hx) (Subgroup.centralizer_le_normalizer _ (hBV hx))
  have hVH : V ≤ H := hVK'.trans hK'W
  have hXcop : Nat.Coprime 2 (Nat.card X) :=
    Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_left) (coprime_card_oddCoreIn H)
  have hXodd : Odd (Nat.card X) := Nat.coprime_two_left.mp hXcop
  have hBX : B ≤ normalizer (X : Set G) := fun x hx =>
    mem_normalizer_inf (le_normalizer_oddCoreIn H (hBH hx)) (le_normalizer (hBb hx))
  have hLb := twoLayerIn_centralizer_le_of_mem_B hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8
    hE hEB hEK hKW hK'W hbB hb1
  refine le_oddCoreIn_of_commutator_le inf_le_right hXodd ?_ fun M hM =>
    commutator_le_oddCoreIn_of_twoLayerIn_le hLb hM inf_le_left inf_le_right
  obtain ⟨Kc, hKc⟩ := exists_subgroup_commutator_mem (A := oddTwoCoreIn Cb)
    (le_normalizer_oddCoreIn Cb)
  suffices hXK : X ≤ Kc by
    rw [commutator_le]
    intro a ha x hx
    exact ((hKc x).mp (hXK hx)).2 a ha
  rw [← CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two B X hB (by rw [hB8]; norm_num) hBX hXcop]
  refine iSup₂_le fun S hS => ?_
  obtain ⟨hSB, hScard⟩ := hS
  have hSK : IsKleinFour S :=
    isKleinFour_of_card_eq_four (by rw [hScard]; norm_num) fun x hx => hB.2 x (hSB hx)
  have hVS : V ≤ centralizer (S : Set G) := fun v hv => mem_centralizer_iff.mpr fun s hs =>
    ((mem_centralizer_iff.mp (hBV (hSB hs))) v hv).symm
  have hVY : V ≤ normalizer ((X ⊓ centralizer (S : Set G) : Subgroup G) : Set G) := fun v hv =>
    mem_normalizer_inf (mem_normalizer_inf (le_normalizer_oddCoreIn H (hVH hv))
      (le_normalizer (hVb hv))) (le_normalizer (hVS hv))
  have hYcop : Nat.Coprime 2 (Nat.card (X ⊓ centralizer (S : Set G) : Subgroup G)) :=
    Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_left) hXcop
  rw [← CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 1
    Nat.prime_two V _ (isElemAbelian_of_isKleinFour hV) (by rw [hV.card_four]; norm_num) hVY
    hYcop]
  refine iSup₂_le fun T hT => ?_
  obtain ⟨hTV, hTcard⟩ := hT
  have : Nontrivial T := Finite.one_lt_card_iff_nontrivial.mp (by rw [hTcard]; norm_num)
  obtain ⟨t, ht⟩ := exists_ne (1 : ↥T)
  have ht1 : (t : G) ≠ 1 := fun h => ht (Subtype.ext h)
  have hT2 : IsPGroup 2 T := (isPGroup_of_isKleinFour hV).to_le hTV
  have hST : S ≤ centralizer (T : Set G) := fun x hx =>
    centralizer_le (show (T : Set G) ⊆ V from hTV) (hBV (hSB hx))
  have hSTC : S ⊔ T ≤ Cb := sup_le (hSB.trans hBb) (hTV.trans hVb)
  have hST2 := isPGroup_sup_of_le_centralizer (isPGroup_of_isKleinFour hSK) hT2 hST
  set Z := X ⊓ centralizer (S : Set G) ⊓ centralizer (T : Set G) with hZ
  have hZodd : Odd (Nat.card Z) := Nat.coprime_two_left.mp
    (Nat.Coprime.coprime_dvd_right (card_dvd_of_le (inf_le_left.trans inf_le_left)) hXcop)
  have hZS : Z ≤ centralizer ((S ⊔ T : Subgroup G) : Set G) :=
    le_centralizer_iff.mp (sup_le (le_centralizer_iff.mp fun z hz => hz.1.2)
      (le_centralizer_iff.mp fun z hz => hz.2))
  have hNZ : Cb ⊓ centralizer ((S ⊔ T : Subgroup G) : Set G) ≤ normalizer (Z : Set G) := by
    intro g hg
    obtain ⟨hgb, hgST⟩ := mem_inf.mp hg
    have hgS : g ∈ centralizer (S : Set G) :=
      centralizer_le (by exact_mod_cast le_sup_left) hgST
    have hgT : g ∈ centralizer (T : Set G) :=
      centralizer_le (by exact_mod_cast le_sup_right) hgST
    have hgH : g ∈ H := le_normalizer_wGroup_of_mem_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ
      hBV hB hE hEB hEK hSK hSB (hTV t.2) ht1 (Subgroup.centralizer_le_normalizer _ hgS)
      (centralizer_le (Set.singleton_subset_iff.mpr t.2) hgT)
    exact mem_normalizer_inf (mem_normalizer_inf (mem_normalizer_inf
      (le_normalizer_oddCoreIn H hgH) (le_normalizer hgb)) (le_normalizer hgS)) (le_normalizer hgT)
  have hPQ := commutator_oddTwoCoreIn_le_of_normalizes hSTC hST2
    ((inf_le_left.trans inf_le_left).trans inf_le_right) hZodd hZS hNZ
  intro z hz
  exact (hKc z).mpr ⟨hz.1.1.2, fun a ha => hPQ (commutator_mem_commutator ha hz)⟩

theorem inf_centralizer_V_le_oddCoreIn (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K) (hKW : K ≤ normalizer (wGroup B V : Set G)) :
    oddCoreIn (normalizer (wGroup B V : Set G)) ⊓ centralizer (V : Set G) ≤
      oddCoreIn (centralizer (V : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (wGroup B V : Set G)
  set CV := centralizer (V : Set G)
  set X := oddCoreIn H ⊓ CV with hX
  obtain ⟨v, hvV, hv1⟩ := exists_mem_ne_one_of_isKleinFour hV
  have hBH : B ≤ H := fun x hx =>
    le_normalizer_wGroup (le_normalizer hx) (Subgroup.centralizer_le_normalizer _ (hBV hx))
  have hXcop : Nat.Coprime 2 (Nat.card X) :=
    Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_left) (coprime_card_oddCoreIn H)
  have hXodd : Odd (Nat.card X) := Nat.coprime_two_left.mp hXcop
  have hBX : B ≤ normalizer (X : Set G) := fun x hx =>
    mem_normalizer_inf (le_normalizer_oddCoreIn H (hBH hx)) (le_normalizer (hBV hx))
  have hLV := twoLayerIn_centralizer_V_le hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE hEB
    hEK hKW
  refine le_oddCoreIn_of_commutator_le inf_le_right hXodd ?_ fun M hM =>
    commutator_le_oddCoreIn_of_twoLayerIn_le hLV hM inf_le_left inf_le_right
  obtain ⟨Kc, hKc⟩ := exists_subgroup_commutator_mem (A := oddTwoCoreIn CV)
    (le_normalizer_oddCoreIn CV)
  suffices hXK : X ≤ Kc by
    rw [commutator_le]
    intro a ha x hx
    exact ((hKc x).mp (hXK hx)).2 a ha
  rw [← CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two B X hB (by rw [hB8]; norm_num) hBX hXcop]
  refine iSup₂_le fun S hS => ?_
  obtain ⟨hSB, hScard⟩ := hS
  have hSK : IsKleinFour S :=
    isKleinFour_of_card_eq_four (by rw [hScard]; norm_num) fun x hx => hB.2 x (hSB hx)
  set Z := X ⊓ centralizer (S : Set G) with hZ
  have hZodd : Odd (Nat.card Z) := Nat.coprime_two_left.mp
    (Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_left) hXcop)
  have hNZ : CV ⊓ centralizer (S : Set G) ≤ normalizer (Z : Set G) := by
    intro g hg
    obtain ⟨hgV, hgS⟩ := mem_inf.mp hg
    have hgH : g ∈ H := le_normalizer_wGroup_of_mem_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ
      hBV hB hE hEB hEK hSK hSB hvV hv1 (Subgroup.centralizer_le_normalizer _ hgS)
      (centralizer_le (Set.singleton_subset_iff.mpr hvV) hgV)
    exact mem_normalizer_inf (mem_normalizer_inf (le_normalizer_oddCoreIn H hgH)
      (le_normalizer hgV)) (le_normalizer hgS)
  have hPQ := commutator_oddTwoCoreIn_le_of_normalizes (hSB.trans hBV)
    (isPGroup_of_isKleinFour hSK) (inf_le_left.trans inf_le_right) hZodd (fun z hz => hz.2) hNZ
  intro z hz
  exact (hKc z).mpr ⟨hz.1.2, fun a ha => hPQ (commutator_mem_commutator ha hz)⟩

theorem wGroup_le_oddCoreIn_normalizer (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K) :
    wGroup B V ≤ oddCoreIn (normalizer (wGroup B V : Set G)) := by
  have hcop := (wGroup_spec_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK
    (by rw [hB8]; norm_num)).1
  have h := inf_le_oddCoreIn hcop (le_refl (normalizer (wGroup B V : Set G)))
  rwa [inf_eq_left.mpr le_normalizer] at h

theorem oddCoreIn_inf_centralizer_eq_theta (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K) (hKW : K ≤ normalizer (wGroup B V : Set G))
    (hK'W : K' ≤ normalizer (wGroup B V : Set G)) {b : G} (hbB : b ∈ B) (hb1 : b ≠ 1) :
    oddCoreIn (normalizer (wGroup B V : Set G)) ⊓ centralizer ({b} : Set G) = theta V b := by
  set H := normalizer (wGroup B V : Set G)
  set X := oddCoreIn H ⊓ centralizer ({b} : Set G) with hX
  have hVb : V ≤ centralizer ({b} : Set G) := le_centralizer_singleton_of_mem hBV hbB
  refine le_antisymm ?_ (le_inf ((theta_le_wGroup hbB hb1).trans
    (wGroup_le_oddCoreIn_normalizer hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE hEB hEK))
    ((theta_le_oddCoreIn hVb).trans (map_subtype_le _)))
  have hXO := inf_centralizer_le_oddCoreIn_of_mem_B hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8
    hE hEB hEK hKW hK'W hbB hb1
  have hVO := inf_centralizer_V_le_oddCoreIn hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE hEB
    hEK hKW
  have hVH : V ≤ H := hVK'.trans hK'W
  have hVX : V ≤ normalizer (X : Set G) := fun v hv =>
    mem_normalizer_inf (le_normalizer_oddCoreIn H (hVH hv)) (le_normalizer (hVb hv))
  have hXcop : Nat.Coprime 2 (Nat.card X) :=
    Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_left) (coprime_card_oddCoreIn H)
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2
    Nat.prime_two V X (isPGroup_of_isKleinFour hV) hVX hXcop
  rw [← hfac]
  refine sup_le (le_sup_of_le_left (Subgroup.commutator_mono hXO le_rfl))
    (le_sup_of_le_right (le_inf (inf_le_left.trans hXO) ?_))
  exact (inf_le_inf_right _ inf_le_left).trans hVO

theorem oddCoreIn_normalizer_wGroup_eq (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K) (hKW : K ≤ normalizer (wGroup B V : Set G))
    (hK'W : K' ≤ normalizer (wGroup B V : Set G)) :
    oddCoreIn (normalizer (wGroup B V : Set G)) = wGroup B V := by
  set H := normalizer (wGroup B V : Set G)
  refine le_antisymm ?_ (wGroup_le_oddCoreIn_normalizer hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB
    hB8 hE hEB hEK)
  have hEH : E ≤ normalizer (oddCoreIn H : Set G) := fun x hx => le_normalizer_oddCoreIn H
    (le_normalizer_wGroup (le_normalizer (hEB hx))
      (Subgroup.centralizer_le_normalizer _ (hBV (hEB hx))))
  refine (le_iSup_inf_centralizer_of_isKleinFour hE hEH (coprime_card_oddCoreIn H)).trans
    (iSup₂_le fun e he => iSup_le fun he1 => ?_)
  rw [oddCoreIn_inf_centralizer_eq_theta hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE hEB hEK
    hKW hK'W (hEB he) he1]
  exact theta_le_wGroup (hEB he) he1

end CFSG.ComponentClassification.Sol76.Sig
