module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeDL
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotTools
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalCorrespondenceTools
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrNestedNormalClosure
public import CFSG.GH74.Generic.S45.LDiagCore

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

variable {G : Type} [Group G] [Finite G]

theorem exists_kleinFour_perfect_of_layer {P : Subgroup G} (hperf : ⁅P, P⁆ = P)
    (hsimp : IsSimpleGroup (↥P ⧸ pPrimeCore 2 ↥P)) {E₀ H₀ : Subgroup (↥P ⧸ pPrimeCore 2 ↥P)}
    (hE₀ : IsKleinFour E₀) (hH₀ : ⁅H₀, H₀⁆ = H₀) (hH₀1 : H₀ ≠ ⊥)
    (hCE : ⁅centralizer (E₀ : Set (↥P ⧸ pPrimeCore 2 ↥P)),
      centralizer (E₀ : Set (↥P ⧸ pPrimeCore 2 ↥P))⁆ = H₀)
    (hlayer : ∀ e ∈ E₀, e ≠ 1 →
      H₀ ≤ (pLayer ↥(centralizer ({e} : Set (↥P ⧸ pPrimeCore 2 ↥P))) 2).map
        (centralizer ({e} : Set (↥P ⧸ pPrimeCore 2 ↥P))).subtype) :
    ∃ E H : Subgroup G, E ≤ P ∧ IsKleinFour E ∧ H ≤ P ∧ ⁅H, H⁆ = H ∧
      (∀ f ∈ E, f ≠ 1 → H ≤ gsFixedLayer P f) ∧
      ∀ N : Subgroup G, N ≤ P → (N.subgroupOf P).Normal → H ≤ N → N = P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : IsKleinFour ↥E₀ := hE₀
  haveI : IsMulCommutative ↥E₀ := IsKleinFour.isMulCommutative
  let U : Subgroup ↥P := pPrimeCore 2 ↥P
  have hUnorm : U.Normal := pPrimeCore_normal
  haveI : U.Normal := hUnorm
  have hUodd : Odd (Nat.card U) := Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2))
  let π : ↥P →* (↥P ⧸ U) := QuotientGroup.mk' U
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective U
  have hπodd : ¬ 2 ∣ Nat.card π.ker := GSThmB.OddQuot.not_two_dvd_card_ker (H := ↥P)
  haveI : IsSimpleGroup (↥P ⧸ U) := hsimp
  have hE₀elem : IsElemTwo E₀ := by
    refine ⟨fun x hx y hy => Subgroup.mul_comm_of_mem_isMulCommutative (H := E₀) hx hy,
      fun x hx => ?_⟩
    have h := IsKleinFour.mul_self (⟨x, hx⟩ : ↥E₀)
    simpa only [Subgroup.coe_mul, Subgroup.coe_one] using congrArg Subtype.val h
  obtain ⟨E', -, hE'map, hE'elem, hE'card⟩ :=
    HeDL.exists_lift_le (H := ↥P) (R := ⊤) (E := E₀) hE₀elem
      (by rw [Subgroup.map_top_of_surjective π hπsurj]; exact le_top)
  have hE'card4 : Nat.card E' = 4 := hE'card.trans hE₀.card_four
  have hE'p : IsPGroup 2 E' :=
    IsPGroup.of_card (n := 2) (by rw [hE'card4]; norm_num)
  haveI hE'nontriv : Nontrivial ↥E' := by
    rw [← Finite.one_lt_card_iff_nontrivial, hE'card4]
    norm_num
  have hE'exp : Monoid.exponent ↥E' = 2 := by
    refine (Monoid.exponent_eq_prime_iff Nat.prime_two).2 (fun g hg => ?_)
    refine orderOf_eq_prime ?_ hg
    apply Subtype.ext
    simpa only [pow_two, Subgroup.coe_mul, Subgroup.coe_one] using hE'elem.2 (g : ↥P) g.2
  let eE : ↥E' ≃* ↥(E'.map P.subtype) :=
    Subgroup.equivMapOfInjective E' P.subtype P.subtype_injective
  have hEcard : Nat.card (E'.map P.subtype) = 4 := by
    rw [Subgroup.card_map_of_injective P.subtype_injective, hE'card4]
  have hEexp : Monoid.exponent ↥(E'.map P.subtype) = 2 :=
    (Monoid.exponent_eq_of_mulEquiv eE.symm).trans hE'exp
  have hEK4 : IsKleinFour (E'.map P.subtype) := ⟨hEcard, hEexp⟩
  let C : Subgroup ↥P := Subgroup.centralizer (E' : Set ↥P)
  have hCmap : C.map π = Subgroup.centralizer (E₀ : Set (↥P ⧸ U)) := by
    have h := GSThmB.OddQuot.map_inf_centralizer π hE'p
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
      (GSThmB.OddQuot.not_two_dvd_card_ker_domRestrict π hπodd ⊤)
    rw [top_inf_eq, Subgroup.map_top_of_surjective π hπsurj] at h
    rw [hE'map, top_inf_eq] at h
    simpa only [C] using h
  have hH₀leCbar : H₀ ≤ Subgroup.centralizer (E₀ : Set (↥P ⧸ U)) := by
    rw [← hCE]
    exact Subgroup.commutator_le_self _
  obtain ⟨Q, hQperf, hQmap⟩ :=
    CFSG.GH74.Generic.S45.exists_perfect_lift_hom (π.domRestrict C) hH₀ (by
      rw [MonoidHom.domRestrict_range, hCmap]
      exact hH₀leCbar)
  let H' : Subgroup ↥P := Q.map C.subtype
  have hH'leC : H' ≤ C := Subgroup.map_subtype_le Q
  have hH'perf : ⁅H', H'⁆ = H' := by
    have h := congrArg (Subgroup.map C.subtype) hQperf
    rw [Subgroup.map_commutator] at h
    exact h
  have hH'mapπ : H'.map π = H₀ := by
    rw [show H' = Q.map C.subtype from rfl, Subgroup.map_map]
    exact hQmap
  have hHlayer : ∀ f ∈ E'.map P.subtype, f ≠ 1 → H'.map P.subtype ≤ gsFixedLayer P f := by
    rintro f hf hf1
    obtain ⟨f', hf', rfl⟩ := Subgroup.mem_map.mp hf
    have hf'1 : f' ≠ 1 := fun h => hf1 (by rw [h]; rfl)
    have hf'2 : f' * f' = 1 := hE'elem.2 f' hf'
    have hord : orderOf f' = 2 := orderOf_eq_prime (by rwa [pow_two]) hf'1
    have hzp : IsPGroup 2 (Subgroup.zpowers f') := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hord]
      norm_num
    have hfbar_mem : π f' ∈ E₀ := by
      rw [← hE'map]
      exact Subgroup.mem_map_of_mem π hf'
    have hfbar1 : π f' ≠ 1 := by
      intro h
      have hinj : Set.InjOn π E' := GSThmB.OddQuot.injOn_of_isPGroup hE'p
      exact hf'1 (hinj hf' (one_mem E') (by rw [h, map_one]))
    have hH₀layer : H₀ ≤ (pLayer ↥(Subgroup.centralizer ({π f'} : Set (↥P ⧸ U))) 2).map
        (Subgroup.centralizer ({π f'} : Set (↥P ⧸ U))).subtype :=
      hlayer (π f') hfbar_mem hfbar1
    let D : Subgroup ↥P := (Subgroup.centralizer ({(f' : G)} : Set G)).subgroupOf P
    let Cbar : Subgroup (↥P ⧸ U) := Subgroup.centralizer ({π f'} : Set (↥P ⧸ U))
    have hD_eq : D = Subgroup.centralizer ({f'} : Set ↥P) := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
        Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h
        exact Subtype.ext h
      · intro h
        simpa using congrArg (fun z : ↥P => (z : G)) h
    have hDmap : D.map π = Cbar := by
      rw [hD_eq]
      have h := GSThmB.OddQuot.map_inf_centralizer π hzp
        (by rw [Subgroup.normalizer_eq_top]; exact le_top)
        (GSThmB.OddQuot.not_two_dvd_card_ker_domRestrict π hπodd ⊤)
      rw [top_inf_eq, Subgroup.map_top_of_surjective π hπsurj] at h
      rw [MonoidHom.map_zpowers] at h
      simp only [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, top_inf_eq] at h
      simpa only [Cbar] using h
    let g : ↥D →* ↥Cbar := (π.domRestrict D).codRestrict Cbar (by
      intro x
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hx : (x : ↥P) ∈ Subgroup.centralizer ({f'} : Set ↥P) := by
        rw [← hD_eq]
        exact x.2
      change π (x : ↥P) * π f' = π f' * π (x : ↥P)
      simpa only [map_mul] using congrArg π ((Subgroup.mem_centralizer_singleton_iff).mp hx))
    have hg : Function.Surjective g := by
      intro y
      have hy : (y : ↥P ⧸ U) ∈ D.map π := by
        rw [hDmap]
        exact y.2
      obtain ⟨x, hxD, hx⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hxD⟩, Subtype.ext hx⟩
    have hker : ¬ 2 ∣ Nat.card g.ker := by
      have hker_eq : g.ker = (π.domRestrict D).ker := by
        ext x
        simp only [g, MonoidHom.mem_ker, MonoidHom.codRestrict_apply, Subtype.ext_iff, Subgroup.coe_one, map_one]
      rw [hker_eq]
      exact GSThmB.OddQuot.not_two_dvd_card_ker_domRestrict π hπodd D
    have hLmap : (pLayer ↥D 2).map g = pLayer ↥Cbar 2 :=
      UnbalancingLocal.Correspondence.map_pLayer_of_coprime_kernel (p := 2) g hg hker
    have hH'leD : H' ≤ D := by
      rw [hD_eq]
      refine hH'leC.trans (Subgroup.centralizer_le ?_)
      intro x hx
      exact Set.mem_singleton_iff.mp hx ▸ hf'
    let Hc : Subgroup ↥D := H'.subgroupOf D
    have hHcperf : ⁅Hc, Hc⁆ = Hc := by
      apply Subgroup.map_injective D.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hH'leD, hH'perf]
    have hHcmap : (Hc.map g).map Cbar.subtype = H₀ := by
      rw [Subgroup.map_map, show Cbar.subtype.comp g = π.comp D.subtype from rfl,
        ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hH'leD, hH'mapπ]
    have hHcle : Hc.map g ≤ pLayer ↥Cbar 2 := by
      rw [← Subgroup.map_le_map_iff_of_injective Cbar.subtype_injective, hHcmap]
      exact hH₀layer
    have hHcle_sup : Hc ≤ pLayer ↥D 2 ⊔ g.ker :=
      (Subgroup.map_le_map_iff (f := g)).mp (by rw [hLmap]; exact hHcle)
    let q : ↥D →* (↥D ⧸ pLayer ↥D 2) := QuotientGroup.mk' (pLayer ↥D 2)
    have hLbot : (pLayer ↥D 2).map q = ⊥ := by
      have h := Subgroup.map_ker_self q
      rwa [QuotientGroup.ker_mk'] at h
    have hHcq : ⁅Hc.map q, Hc.map q⁆ = Hc.map q := by
      rw [← Subgroup.map_commutator, hHcperf]
    have hHcq_le : Hc.map q ≤ g.ker.map q := by
      calc Hc.map q ≤ (pLayer ↥D 2 ⊔ g.ker).map q := Subgroup.map_mono hHcle_sup
        _ = (pLayer ↥D 2).map q ⊔ (g.ker).map q := Subgroup.map_sup ..
        _ = g.ker.map q := by rw [hLbot, bot_sup_eq]
    have hKodd : Odd (Nat.card g.ker) :=
      Nat.not_even_iff_odd.mp (by
        rw [even_iff_two_dvd]
        exact hker)
    have hKqodd : Odd (Nat.card (g.ker.map q)) :=
      Odd.of_dvd_nat hKodd (Subgroup.card_map_dvd g.ker q)
    have hHcq_odd : Odd (Nat.card (Hc.map q)) :=
      Odd.of_dvd_nat hKqodd (Subgroup.card_dvd_of_le hHcq_le)
    have hHcq_bot : Hc.map q = ⊥ :=
      CFSG.GH74.Generic.S45.eq_bot_of_perfect_of_odd hHcq hHcq_odd
    have hHcle_layer : Hc ≤ pLayer ↥D 2 := by
      have h := (Subgroup.map_eq_bot_iff Hc (f := q)).mp hHcq_bot
      rwa [QuotientGroup.ker_mk'] at h
    have hH'le_layer : H' ≤ (pLayer ↥D 2).map D.subtype := by
      have h := Subgroup.map_mono (f := D.subtype) hHcle_layer
      rwa [Subgroup.map_subgroupOf_eq_of_le hH'leD] at h
    change H'.map P.subtype ≤ gsFixedLayer P (f' : G)
    calc H'.map P.subtype ≤ ((pLayer ↥D 2).map D.subtype).map P.subtype :=
          Subgroup.map_mono hH'le_layer
      _ = gsFixedLayer P (f' : G) :=
          CFSG.ComponentClassification.UnbalancedCorr.map_pLayer_subgroupOf_eq P
            (Subgroup.centralizer ({(f' : G)} : Set G))
  refine ⟨E'.map P.subtype, H'.map P.subtype, Subgroup.map_subtype_le E', hEK4,
    Subgroup.map_subtype_le H', ?_, hHlayer, ?_⟩
  · have h := congrArg (Subgroup.map P.subtype) hH'perf
    rw [Subgroup.map_commutator] at h
    exact h
  · intro N hNP hNnorm hHN
    set N₀ : Subgroup ↥P := N.subgroupOf P with hN₀
    have hN₀norm : N₀.Normal := by rw [hN₀]; exact hNnorm
    haveI : N₀.Normal := hN₀norm
    have hmapNnorm : (N₀.map π).Normal := hN₀norm.map π hπsurj
    have hH'leN₀ : H' ≤ N₀ := by
      intro x hx
      rw [hN₀]
      exact Subgroup.mem_subgroupOf.mpr (hHN (Subgroup.mem_map_of_mem P.subtype hx))
    have hH₀le : H₀ ≤ N₀.map π := by
      rw [← hH'mapπ]
      exact Subgroup.map_mono hH'leN₀
    have hNtop : N₀.map π = ⊤ := by
      rcases hmapNnorm.eq_bot_or_eq_top with h | h
      · rw [h] at hH₀le
        exact absurd (le_bot_iff.mp hH₀le) hH₀1
      · exact h
    have hNsup : N₀ ⊔ U = ⊤ := by
      rw [eq_top_iff]
      intro x hx
      have hx' : π x ∈ N₀.map π := by rw [hNtop]; exact mem_top _
      obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp hx'
      have hmemU : x * n⁻¹ ∈ U := by
        rw [← QuotientGroup.ker_mk' U]
        exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hnx, mul_inv_cancel])
      rw [show x = (x * n⁻¹) * n by group, sup_comm]
      exact Subgroup.mul_mem_sup hmemU hn
    let gU : ↥U →* (↥P ⧸ N₀) := (QuotientGroup.mk' N₀).comp U.subtype
    have hgU : Function.Surjective gU := by
      have hsurj : Function.Surjective (QuotientGroup.mk' N₀) := QuotientGroup.mk'_surjective N₀
      have hNbot : N₀.map (QuotientGroup.mk' N₀) = ⊥ := by
        apply le_antisymm _ bot_le
        intro y hy
        obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hy
        exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff n).mpr hn)
      have hUtop : U.map (QuotientGroup.mk' N₀) = ⊤ := by
        have h := Subgroup.map_sup (f := QuotientGroup.mk' N₀) N₀ U
        rw [hNsup, Subgroup.map_top_of_surjective _ hsurj, hNbot, bot_sup_eq] at h
        exact h.symm
      have hrange : gU.range = ⊤ := by
        rw [show gU = (QuotientGroup.mk' N₀).comp U.subtype from rfl,
          MonoidHom.range_comp, Subgroup.range_subtype]
        exact hUtop
      exact MonoidHom.range_eq_top.mp hrange
    have hqodd : Odd (Nat.card (↥P ⧸ N₀)) :=
      Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_surjective (f := gU) hgU)
    haveI : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hperf
    have hPperf : ⁅(⊤ : Subgroup ↥P), (⊤ : Subgroup ↥P)⁆ = ⊤ := Subgroup.commutator_eq_self
    have hqperf : ⁅(⊤ : Subgroup (↥P ⧸ N₀)), (⊤ : Subgroup (↥P ⧸ N₀))⁆ = ⊤ := by
      haveI : Group.IsPerfect (↥P ⧸ N₀) := Group.IsPerfect.instQuotientSubgroup
      exact Subgroup.commutator_eq_self
    have hqodd' : Odd (Nat.card (⊤ : Subgroup (↥P ⧸ N₀))) := by
      simpa only [Subgroup.card_top] using hqodd
    have hbot : (⊤ : Subgroup (↥P ⧸ N₀)) = ⊥ :=
      CFSG.GH74.Generic.S45.eq_bot_of_perfect_of_odd hqperf hqodd'
    have hN₀top : N₀ = ⊤ := by
      rw [eq_top_iff]
      intro x hx
      have hmem : QuotientGroup.mk' N₀ x ∈ (⊥ : Subgroup (↥P ⧸ N₀)) := hbot ▸ mem_top _
      exact (QuotientGroup.eq_one_iff x).mp (Subgroup.mem_bot.mp hmem)
    refine le_antisymm hNP ?_
    intro x hx
    exact Subgroup.mem_subgroupOf.mp (hN₀top ▸ mem_top (⟨x, hx⟩ : ↥P))

end CFSG.ComponentClassification.GrSLit.L34Sec5S
