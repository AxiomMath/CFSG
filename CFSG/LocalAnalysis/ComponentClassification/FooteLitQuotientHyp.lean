module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitQuotientChain

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

section General

variable {X : Type} [Group X] [Finite X] {N : Subgroup X} [N.Normal]

omit [Finite X] in
theorem not_two_dvd_card_ker_mk'_of_odd (hN : Odd (Nat.card N)) :
    ¬ 2 ∣ Nat.card (QuotientGroup.mk' N).ker := by
  rw [QuotientGroup.ker_mk']
  exact fun h => (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h)

omit [Finite X] in
theorem map_centralizer_mk'_of_odd (hN : Odd (Nat.card N)) {x : X} (hx : orderOf x = 2) :
    (centralizer ({x} : Set X)).map (QuotientGroup.mk' N) =
      centralizer ({QuotientGroup.mk' N x} : Set (X ⧸ N)) := by
  have h := GSThmB.OddQuot.map_inf_centralizer (QuotientGroup.mk' N) (Y := ⊤)
    (isPGroup_zpowers_of_orderOf hx) (by rw [normalizer_eq_top]; exact le_top)
    (GSThmB.OddQuot.not_two_dvd_card_ker_domRestrict _ (not_two_dvd_card_ker_mk'_of_odd hN) ⊤)
  rw [top_inf_eq, map_top_of_surjective _ (QuotientGroup.mk'_surjective N), top_inf_eq,
    centralizer_zpowers_eq, MonoidHom.map_zpowers, centralizer_zpowers_eq] at h
  exact h

theorem exists_involution_mem_zpowers_of_map (hN : Odd (Nat.card N)) {d : X} {cq : X ⧸ N}
    (hd : QuotientGroup.mk' N d = cq) (hc : orderOf cq = 2) :
    ∃ c ∈ zpowers d, orderOf c = 2 ∧ QuotientGroup.mk' N c = cq := by
  obtain ⟨i, m, hm, hdm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos d).ne'
  have hm0 : m ≠ 0 := fun h => by simp [h] at hm
  have hc2 : cq ^ 2 = 1 := by
    have h := pow_orderOf_eq_one cq
    rwa [hc] at h
  have hπc : QuotientGroup.mk' N (d ^ m) = cq := by
    rw [map_pow, hd]
    obtain ⟨r, rfl⟩ := hm
    rw [pow_succ, pow_mul, hc2, one_pow, one_mul]
  have hord : orderOf (d ^ m) = 2 ^ i := by
    rw [orderOf_pow' d hm0, hdm, Nat.gcd_mul_left_left,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  have hsq : (d ^ m) ^ 2 = 1 := by
    have h1 : (d ^ m) ^ 2 ∈ N := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow, hπc, hc2]
    have h2 : ∃ k : ℕ, orderOf ((d ^ m) ^ 2) = 2 ^ k := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
        (hord ▸ orderOf_pow_dvd (x := d ^ m) 2)
      exact ⟨j, hj⟩
    exact eq_one_of_two_element_of_odd hN h1 h2
  have hne : d ^ m ≠ 1 := by
    intro h
    rw [h, map_one] at hπc
    rw [← hπc, orderOf_one] at hc
    exact absurd hc (by decide)
  exact ⟨d ^ m, ⟨m, zpow_natCast d m⟩, orderOf_eq_prime hsq hne, hπc⟩

theorem exists_involution_lift_commute_of_odd (hN : Odd (Nat.card N)) {a : X}
    (ha : orderOf a = 2) {cq : X ⧸ N} (hc : orderOf cq = 2)
    (hac : QuotientGroup.mk' N a * cq = cq * QuotientGroup.mk' N a) :
    ∃ c : X, orderOf c = 2 ∧ QuotientGroup.mk' N c = cq ∧ a * c = c * a := by
  have hmem : cq ∈ (centralizer ({a} : Set X)).map (QuotientGroup.mk' N) := by
    rw [map_centralizer_mk'_of_odd hN ha, mem_centralizer_singleton_iff]
    exact hac.symm
  obtain ⟨d, hdC, hd⟩ := mem_map.mp hmem
  obtain ⟨c, hcd, hc2, hcq⟩ := exists_involution_mem_zpowers_of_map hN hd hc
  have hcC : c ∈ centralizer ({a} : Set X) :=
    (zpowers_le.mpr hdC) hcd
  exact ⟨c, hc2, hcq, (mem_centralizer_singleton_iff.mp hcC).symm⟩

theorem footeCoreAt_quotient (hN : Odd (Nat.card N)) (h : FooteCoreAt X) :
    FooteCoreAt (X ⧸ N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := QuotientGroup.mk' N with hφ
  have hker := not_two_dvd_card_ker_mk'_of_odd hN
  intro aq bq haq hbq habq Yq hYqC hYqpc
  obtain ⟨d, hd⟩ := QuotientGroup.mk'_surjective N aq
  obtain ⟨a, -, ha, rfl⟩ := exists_involution_mem_zpowers_of_map hN hd haq
  obtain ⟨b, hb, rfl, hab⟩ := exists_involution_lift_commute_of_odd hN ha hbq habq
  set C := centralizer ({b} : Set X) with hC
  have hCmap : C.map φ = centralizer ({φ b} : Set (X ⧸ N)) := map_centralizer_mk'_of_odd hN hb
  obtain ⟨hbij, -, -⟩ := CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
    (MonoidHom.subgroupMap φ C) (MonoidHom.subgroupMap_surjective φ C)
    (GSThmB.OddQuot.not_two_dvd_card_ker_subgroupMap φ hker C)
  have hYqC' : Yq ≤ C.map φ := hCmap ▸ hYqC
  have hpc' : IsPComponent 2 (Yq.subgroupOf (C.map φ)) := by rw [hCmap]; exact hYqpc
  obtain ⟨Y', hY', hY'map⟩ := hbij.surjOn hpc'
  have hY'map' : Y'.map (MonoidHom.subgroupMap φ C) = Yq.subgroupOf (C.map φ) := hY'map
  set Y := Y'.map C.subtype with hYdef
  have hYC : Y ≤ C := map_subtype_le _
  have hYpc : IsPComponent 2 (Y.subgroupOf C) := by
    have h1 : Y.subgroupOf C = Y' := comap_map_eq_self_of_injective C.subtype_injective Y'
    rw [h1]
    exact hY'
  have hYmap : Y.map φ = Yq := by
    have h1 : (Y'.map (MonoidHom.subgroupMap φ C)).map (C.map φ).subtype = Yq := by
      rw [hY'map']
      exact map_subgroupOf_eq_of_le hYqC'
    rw [← h1, hYdef, Subgroup.map_map, Subgroup.map_map]
    rfl
  rcases h a b ha hb hab Y hYC hYpc with ⟨p, f, hp, hp2, hf, hL⟩ | hcomm
  · left
    obtain ⟨eZ⟩ := GSThmB.OddQuot.nonempty_quotient_fusionZStar_equiv φ hker Y
    rw [hYmap] at eZ
    exact ⟨p, f, hp, hp2, hf, LieType.CurtisTits.lieModel_of_mulEquiv eZ hL⟩
  · right
    have haC : b ∈ centralizer ({a} : Set X) := mem_centralizer_singleton_iff.mpr hab.symm
    have hOa : (oddCoreOfCentralizer a).map φ = oddCoreOfCentralizer (φ a) := by
      have h1 := GSThmB.OddQuot.map_oddCoreIn φ hker (centralizer ({a} : Set X))
      rw [map_centralizer_mk'_of_odd hN ha] at h1
      exact h1
    have hOb : (oddCoreOfCentralizer b).map φ = oddCoreOfCentralizer (φ b) := by
      have h1 := GSThmB.OddQuot.map_oddCoreIn φ hker (centralizer ({b} : Set X))
      rw [map_centralizer_mk'_of_odd hN hb] at h1
      exact h1
    have hX0 : (oddCoreOfCentralizer a ⊓ centralizer ({b} : Set X)).map φ =
        oddCoreOfCentralizer (φ a) ⊓ centralizer ({φ b} : Set (X ⧸ N)) := by
      have h1 := GSThmB.OddQuot.map_inf_centralizer φ (Y := oddCoreOfCentralizer a)
        (isPGroup_zpowers_of_orderOf hb)
        ((zpowers_le).mpr (mem_normalizer_oddCoreOfCentralizer haC))
        (GSThmB.OddQuot.not_two_dvd_card_ker_domRestrict φ hker _)
      rw [centralizer_zpowers_eq, MonoidHom.map_zpowers, centralizer_zpowers_eq, hOa] at h1
      exact h1
    have h1 := map_mono (f := φ) hcomm
    rw [map_commutator, map_commutator, hX0, hYmap, hOb] at h1
    exact h1

end General

theorem footeCoreHypothesis_quotient {G : Type} [Group G] [Finite G] {N : Subgroup G}
    [N.Normal] (hN : Odd (Nat.card N)) (h : FooteCoreHypothesis G) :
    FooteCoreHypothesis (G ⧸ N) := by
  intro Hq
  set H := Hq.comap (QuotientGroup.mk' N) with hH
  let f : H →* Hq := ((QuotientGroup.mk' N).comp H.subtype).codRestrict Hq fun x => x.2
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact ⟨⟨g, hy⟩, rfl⟩
  have hkerodd : Odd (Nat.card f.ker) := by
    let ι : f.ker →* N :=
      { toFun := fun x => ⟨((x : H) : G), by
          have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
          exact (QuotientGroup.eq_one_iff _).mp h1⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : Function.Injective ι := fun x y hxy => by
      have h2 : ((x : H) : G) = ((y : H) : G) := congrArg (fun z : N => (z : G)) hxy
      exact Subtype.ext (Subtype.ext h2)
    exact Odd.of_dvd_nat hN (Subgroup.card_dvd_of_injective ι hι)
  have h1 : FooteCoreAt (H ⧸ f.ker) := footeCoreAt_quotient hkerodd (h H)
  exact footeCoreAt_of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective f hf).symm h1

end CFSG.ComponentClassification.FooteLit
