module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

private theorem dszu_frattini_le {G : Type} [Group G] [Finite G] (Y K : Subgroup G)
    (hsq : ∀ x ∈ Y, x ^ 2 ∈ K) (hcomm : ∀ x ∈ Y, ∀ y ∈ Y, ⁅x, y⁆ ∈ K) :
    dsFrattini Y ≤ K := by
  have hnorm : (K.subgroupOf Y).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 : ⁅(g : G), (n : G)⁆ ∈ K := hcomm _ g.2 _ n.2
    have h2 : (g : G) * (n : G) * (g : G)⁻¹ = ⁅(g : G), (n : G)⁆ * (n : G) := by
      rw [commutatorElement_def]; group
    have h3 := K.mul_mem h1 hn
    rw [← h2] at h3
    simpa using h3
  have hcommQ : ∀ a b : ↥Y ⧸ K.subgroupOf Y, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h5 : (((x * y)⁻¹ * (y * x) : ↥Y) : G) = ⁅(y : G)⁻¹, (x : G)⁻¹⁆ := by
      rw [commutatorElement_def]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h5]
    exact hcomm _ (Y.inv_mem y.2) _ (Y.inv_mem x.2)
  have hpowQ : ∀ a : ↥Y ⧸ K.subgroupOf Y, a ^ 2 = 1 := by
    intro a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hsq (x : G) x.2
  haveI := hnorm
  have hfr := CFSG.SectionRank.Ccomm.frattini_le_of_quotient_elementary
    (p := 2) (K.subgroupOf Y) hcommQ hpowQ
  exact Subgroup.map_le_iff_le_comap.mpr hfr

private theorem dszu_comm_mul_z {G : Type} [Group G] {x y z : G} (hx : x * z = z * x)
    (hy : y * z = z * y) :
    ⁅x * z, y⁆ = ⁅x, y⁆ ∧ ⁅x, y * z⁆ = ⁅x, y⁆ ∧ ⁅x * z, y * z⁆ = ⁅x, y⁆ := by
  have hxi : z * x⁻¹ = x⁻¹ * z := by
    calc z * x⁻¹ = x⁻¹ * (x * z) * x⁻¹ := by group
      _ = x⁻¹ * (z * x) * x⁻¹ := by rw [hx]
      _ = x⁻¹ * z := by group
  refine ⟨?_, ?_, ?_⟩
  · rw [commutatorElement_def, commutatorElement_def]
    calc x * z * y * (x * z)⁻¹ * y⁻¹ = x * (z * y) * (z⁻¹ * x⁻¹) * y⁻¹ := by group
      _ = x * (y * z) * (z⁻¹ * x⁻¹) * y⁻¹ := by rw [hy]
      _ = x * y * (z * z⁻¹) * x⁻¹ * y⁻¹ := by group
      _ = x * y * x⁻¹ * y⁻¹ := by simp only [mul_inv_cancel, mul_one]
  · rw [commutatorElement_def, commutatorElement_def]
    calc x * (y * z) * x⁻¹ * (y * z)⁻¹ = x * y * (z * x⁻¹) * (z⁻¹ * y⁻¹) := by group
      _ = x * y * (x⁻¹ * z) * (z⁻¹ * y⁻¹) := by rw [hxi]
      _ = x * y * x⁻¹ * (z * z⁻¹) * y⁻¹ := by group
      _ = x * y * x⁻¹ * y⁻¹ := by simp only [mul_inv_cancel, mul_one]
  · rw [commutatorElement_def, commutatorElement_def]
    calc x * z * (y * z) * (x * z)⁻¹ * (y * z)⁻¹ = x * (z * y) * x⁻¹ * (z⁻¹ * y⁻¹) := by group
      _ = x * (y * z) * x⁻¹ * (z⁻¹ * y⁻¹) := by rw [hy]
      _ = x * y * (z * x⁻¹) * (z⁻¹ * y⁻¹) := by group
      _ = x * y * (x⁻¹ * z) * (z⁻¹ * y⁻¹) := by rw [hxi]
      _ = x * y * x⁻¹ * (z * z⁻¹) * y⁻¹ := by group
      _ = x * y * x⁻¹ * y⁻¹ := by simp only [mul_inv_cancel, mul_one]

private theorem dszu_comm_of_mul_mem {G : Type} [Group G] {R : Subgroup G} {z : G}
    (hzc : ∀ r ∈ R, r * z = z * r) (hz2 : z * z = 1) {x : G} (hx : x * z ∈ R) :
    x * z = z * x := by
  have hr := hzc (x * z) hx
  have hx' : x = z * (x * z) := by
    calc x = x * (z * z) := by rw [hz2, mul_one]
      _ = x * z * z := by group
      _ = z * (x * z) := hr
  have key : z * x = x * z := by
    calc z * x = z * (z * (x * z)) := by rw [← hx']
      _ = (z * z) * (x * z) := by group
      _ = x * z := by rw [hz2, one_mul]
  exact key.symm

private theorem dszu_exists_T {G : Type} [Group G] (R : Subgroup G) (z : G)
    (hzc : ∀ r ∈ R, r * z = z * r) (hz2 : z * z = 1) :
    ∃ T : Subgroup G, ∀ x, x ∈ T ↔ (x ∈ R ∨ x * z ∈ R) := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  refine ⟨{ carrier := {x | x ∈ R ∨ x * z ∈ R}
            one_mem' := by
              show (1 : G) ∈ R ∨ (1 : G) * z ∈ R
              exact Or.inl R.one_mem
            mul_mem' := ?_
            inv_mem' := ?_ }, fun x => Iff.rfl⟩
  · intro x y hx hy
    have hx' : x ∈ R ∨ x * z ∈ R := hx
    have hy' : y ∈ R ∨ y * z ∈ R := hy
    show x * y ∈ R ∨ x * y * z ∈ R
    rcases hx' with hx' | hx' <;> rcases hy' with hy' | hy'
    · exact Or.inl (R.mul_mem hx' hy')
    · refine Or.inr ?_
      rw [mul_assoc]
      exact R.mul_mem hx' hy'
    · refine Or.inr ?_
      rw [mul_assoc, hzc y hy', ← mul_assoc]
      exact R.mul_mem hx' hy'
    · refine Or.inl ?_
      have hxc := dszu_comm_of_mul_mem hzc hz2 hx'
      have hyc := dszu_comm_of_mul_mem hzc hz2 hy'
      have e : (x * z) * (y * z) = x * y := by
        calc (x * z) * (y * z) = x * (z * y) * z := by group
          _ = x * (y * z) * z := by rw [← hyc]
          _ = x * y * (z * z) := by group
          _ = x * y := by rw [hz2, mul_one]
      rw [← e]
      exact R.mul_mem hx' hy'
  · intro x hx
    have hx' : x ∈ R ∨ x * z ∈ R := hx
    show x⁻¹ ∈ R ∨ x⁻¹ * z ∈ R
    rcases hx' with hx' | hx'
    · exact Or.inl (R.inv_mem hx')
    · refine Or.inr ?_
      have hxc := dszu_comm_of_mul_mem hzc hz2 hx'
      have hinv : x⁻¹ * z = z * x⁻¹ := by
        calc x⁻¹ * z = x⁻¹ * (z * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * z) * x⁻¹ := by rw [hxc.symm]
          _ = z * x⁻¹ := by group
      have e : z * x⁻¹ = (x * z)⁻¹ := by rw [mul_inv_rev, hzinv]
      rw [hinv, e]
      exact R.inv_mem hx'

private theorem dszu_unique {G : Type} [Group G] {R : Subgroup G}
    (hc : Nat.card (Subgroup.center ↥R) = 2) {a b : G} (ha : a ∈ R) (hb : b ∈ R)
    (hac : ∀ r ∈ R, r * a = a * r) (hbc : ∀ r ∈ R, r * b = b * r) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    a = b := by
  have hA : (⟨a, ha⟩ : ↥R) ∈ Subgroup.center ↥R := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hac g.1 g.2)
  have hB : (⟨b, hb⟩ : ↥R) ∈ Subgroup.center ↥R := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hbc g.1 g.2)
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(Subgroup.center ↥R))).mp hc
  have hA1 : (⟨⟨a, ha⟩, hA⟩ : ↥(Subgroup.center ↥R)) ≠ 1 :=
    fun h => ha1 (congrArg (fun u : ↥(Subgroup.center ↥R) => ((u : ↥R) : G)) h)
  have hB1 : (⟨⟨b, hb⟩, hB⟩ : ↥(Subgroup.center ↥R)) ≠ 1 :=
    fun h => hb1 (congrArg (fun u : ↥(Subgroup.center ↥R) => ((u : ↥R) : G)) h)
  have e := (huniq _ hA1).trans (huniq _ hB1).symm
  exact congrArg (fun u : ↥(Subgroup.center ↥R) => ((u : ↥R) : G)) e

private theorem dszu_le_normalizer_zpowers {G : Type} [Group G] {g z : G} (hg : g * z = z * g) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hc : ∀ k : ℤ, Commute g (z ^ k) := fun k => Commute.zpow_right hg k
  have hc' : ∀ k : ℤ, Commute g⁻¹ (z ^ k) := fun k => (hc k).inv_left
  constructor
  · intro hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have e : g * z ^ k * g⁻¹ = z ^ k := by
      rw [(hc k).eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [e]
    exact hh
  · intro hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
    have e : h = z ^ k := by
      calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
        _ = g⁻¹ * z ^ k * g := by rw [← hk]
        _ = z ^ k := by rw [(hc' k).eq, mul_assoc, inv_mul_cancel, mul_one]
    rw [e]
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩

theorem leafDSBZSU [DSLeaf LeafSylowS] [DSLeaf LeafZiStructure] [DSLeaf LeafRankBounds] : LeafDSBZSU := by
  intro G _ _ L1 L2 S h _ hsp
  intro hZ
  have hRS : pCoreOf 2 L2 ≤ S :=
    (F1.pCoreOf_le_pCoreOf_parabolic h.symm).trans (sylow_s h.symm).2.2
  have hSpg : IsPGroup 2 ↥S := h.hyp.h1.pgroup
  obtain ⟨hspg, hcR, hcZ⟩ := hsp
  unfold IsSpecialPGroup at hspg
  obtain ⟨hpg, hcase⟩ := hspg
  set R : Subgroup G := pCoreOf 2 L2 with hRdef
  haveI : Fact (IsPGroup 2 ↥R) := ⟨hpg⟩
  obtain ⟨hF, hCom⟩ : frattini ↥R = Subgroup.center ↥R ∧
      _root_.commutator ↥R = Subgroup.center ↥R := by
    rcases hcase with ⟨hmc, -⟩ | ⟨hcomm_eq, hfr_eq, -⟩
    · exfalso
      haveI := hmc
      rw [Subgroup.center_eq_top, Subgroup.card_top, hcR] at hcZ
      norm_num at hcZ
    · exact ⟨hfr_eq, hcomm_eq⟩
  have hRcard : Nat.card ↥R = 32 := by rw [hcR]; norm_num
  have hZcard : Nat.card ↥(Subgroup.center ↥R) = 2 := hcZ
  have hrel : (dsFrattini R).relIndex R = 16 := by
    have h1 : (dsFrattini R).relIndex R = (frattini ↥R).index := by
      unfold dsFrattini
      rw [Subgroup.relIndex, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective R.subtype_injective]
    have h2 : Nat.card ↥(frattini ↥R) = 2 := by rw [hF]; exact hZcard
    have h3 := Subgroup.index_mul_card (frattini ↥R)
    rw [h2, hRcard] at h3
    omega
  have hFR_le : dsFrattini R ≤ R := Subgroup.map_subtype_le _
  have hsqR : ∀ a ∈ R, a ^ 2 ∈ dsFrattini R := by
    intro a ha
    have h1 : (⟨a, ha⟩ : ↥R) ^ 2 ∈ frattini ↥R :=
      CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) _
    have h2 := Subgroup.mem_map_of_mem R.subtype h1
    have e : R.subtype ((⟨a, ha⟩ : ↥R) ^ 2) = a ^ 2 := by simp
    rw [e] at h2
    exact h2
  have hRcomm : ∀ a ∈ R, ∀ b ∈ R, ⁅a, b⁆ ∈ dsFrattini R := by
    intro a ha b hb
    have h1 : ⁅(⟨a, ha⟩ : ↥R), (⟨b, hb⟩ : ↥R)⁆ ∈ frattini ↥R := by
      rw [hF, ← hCom, commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    have h2 := Subgroup.mem_map_of_mem R.subtype h1
    have e : R.subtype ⁅(⟨a, ha⟩ : ↥R), (⟨b, hb⟩ : ↥R)⁆ = ⁅a, b⁆ := by
      simp [commutatorElement_def]
    rw [e] at h2
    exact h2
  obtain ⟨z, hzS, hzc, hz2, hz1⟩ :
      ∃ z : G, z ∈ S ∧ (∀ s ∈ S, s * z = z * s) ∧ z ^ 2 = 1 ∧ z ≠ 1 := by
    haveI : Nontrivial ↥R := Finite.one_lt_card_iff_nontrivial.mp (by rw [hRcard]; norm_num)
    obtain ⟨a0, ha0⟩ := exists_ne (1 : ↥R)
    have h0 : (a0 : G) ≠ 1 := fun e' => ha0 (Subtype.ext e')
    haveI : Nontrivial ↥S :=
      ⟨⟨⟨(a0 : G), hRS a0.2⟩, 1, fun e => h0 (congrArg (fun u : ↥S => (u : G)) e)⟩⟩
    have hZnt : Nontrivial ↥(Subgroup.center ↥S) := hSpg.center_nontrivial
    obtain ⟨n, hn, hnc⟩ :=
      ((hSpg.to_subgroup (Subgroup.center ↥S))).nontrivial_iff_card.mp hZnt
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥S)) 2
      (by rw [hnc]; exact dvd_pow_self 2 hn.ne')
    have hw1 : w ≠ 1 := by
      intro e
      rw [e, orderOf_one] at hw
      norm_num at hw
    have hw2 : w ^ 2 = 1 := by
      have := pow_orderOf_eq_one w
      rwa [hw] at this
    refine ⟨((w : ↥S) : G), (w : ↥S).2, fun s hs => ?_, ?_, ?_⟩
    · have e := congrArg (fun u : ↥S => (u : G)) (Subgroup.mem_center_iff.mp w.2 ⟨s, hs⟩)
      simpa using e
    · have e := congrArg (fun u : ↥(Subgroup.center ↥S) => ((u : ↥S) : G)) hw2
      simpa using e
    · intro e
      apply hw1
      apply Subtype.ext
      apply Subtype.ext
      simpa using e
  have hzz : z * z = 1 := by rw [← pow_two]; exact hz2
  have hzRc : ∀ r ∈ R, r * z = z * r := fun r hr => hzc r (hRS hr)
  have hzL1 : ∀ l ∈ L1, l * z = z * l := by
    intro l hl
    have hzcent : z ∈ centerOf S :=
      Subgroup.mem_inf.mpr ⟨hzS, Subgroup.mem_centralizer_iff.mpr (fun s hs => hzc s hs)⟩
    exact Subgroup.mem_centralizer_iff.mp (hZ hzcent) l hl
  have hzR : z ∈ R := by
    by_contra hzR
    obtain ⟨T, hT⟩ := dszu_exists_T R z hzRc hzz
    have hRT : R ≤ T := fun x hx => (hT x).2 (Or.inl hx)
    have hzT : z ∈ T := (hT z).2 (Or.inr (by rw [hzz]; exact R.one_mem))
    have hTS : T ≤ S := by
      intro x hx
      rcases (hT x).1 hx with hx | hx
      · exact hRS hx
      · simpa using S.mul_mem (hRS hx) (S.inv_mem hzS)
    have hT2 : IsPGroup 2 ↥T :=
      IsPGroup.of_equiv (hSpg.to_subgroup (T.subgroupOf S)) (Subgroup.subgroupOfEquivOfLe hTS)
    have hrep : ∀ x ∈ T, ∃ r ∈ R, x = r ∨ x = r * z := by
      intro x hx
      rcases (hT x).1 hx with hxR | hxR
      · exact ⟨x, hxR, Or.inl rfl⟩
      · exact ⟨x * z, hxR, Or.inr (by rw [mul_assoc, hzz, mul_one])⟩
    have hsqT : ∀ x ∈ T, x ^ 2 ∈ dsFrattini R := by
      intro x hx
      obtain ⟨r, hr, hx'⟩ := hrep x hx
      rcases hx' with hx' | hx'
      · rw [hx']
        exact hsqR r hr
      · have e : (r * z) ^ 2 = r ^ 2 := by
          rw [pow_two, pow_two]
          calc r * z * (r * z) = r * (z * r) * z := by group
            _ = r * (r * z) * z := by rw [← hzRc r hr]
            _ = r * r * (z * z) := by group
            _ = r * r := by rw [hzz, mul_one]
        rw [hx', e]
        exact hsqR r hr
    have hcommT : ∀ x ∈ T, ∀ y ∈ T, ⁅x, y⁆ ∈ dsFrattini R := by
      intro x hx y hy
      obtain ⟨r, hr, hx'⟩ := hrep x hx
      obtain ⟨r', hr', hy'⟩ := hrep y hy
      rcases hx' with hx' | hx' <;> rcases hy' with hy' | hy'
      · rw [hx', hy']
        exact hRcomm r hr r' hr'
      · rw [hx', hy', (dszu_comm_mul_z (hzRc r hr) (hzRc r' hr')).2.1]
        exact hRcomm r hr r' hr'
      · rw [hx', hy', (dszu_comm_mul_z (hzRc r hr) (hzRc r' hr')).1]
        exact hRcomm r hr r' hr'
      · rw [hx', hy', (dszu_comm_mul_z (hzRc r hr) (hzRc r' hr')).2.2]
        exact hRcomm r hr r' hr'
    have hFT : dsFrattini T ≤ dsFrattini R := dszu_frattini_le T (dsFrattini R) hsqT hcommT
    have hne : R.subgroupOf T ≠ ⊤ := fun h' => hzR (Subgroup.subgroupOf_eq_top.mp h' hzT)
    have hRTidx : 1 < R.relIndex T := Subgroup.one_lt_index_of_ne_top hne
    have hmul : (dsFrattini R).relIndex R * R.relIndex T = (dsFrattini R).relIndex T :=
      Subgroup.relIndex_mul_relIndex _ _ _ hFR_le hRT
    have hle : (dsFrattini R).relIndex T ≤ (dsFrattini T).relIndex T :=
      Subgroup.relIndex_le_of_le_left hFT (by
        unfold Subgroup.relIndex
        exact Subgroup.index_ne_zero_of_finite)
    have hbound : (dsFrattini T).relIndex T ≤ 16 := (rank_bounds (G := G)).1 T hT2
    rw [hrel] at hmul
    omega
  have hzL2 : ∀ g ∈ L2, g * z = z * g := by
    intro g hg
    have hNg : g ∈ Subgroup.normalizer (R : Set G) :=
      CFSG.RankThree.PartOne.SectionalRank.le_normalizer_pCoreOf 2 L2 hg
    have hNg' : g⁻¹ ∈ Subgroup.normalizer (R : Set G) :=
      CFSG.RankThree.PartOne.SectionalRank.le_normalizer_pCoreOf 2 L2 (L2.inv_mem hg)
    have hzw : g⁻¹ * z * g ∈ R := by
      have e := (Subgroup.mem_normalizer_iff.mp hNg') z
      rw [inv_inv] at e
      exact e.mp hzR
    have hwc : ∀ r ∈ R, r * (g⁻¹ * z * g) = (g⁻¹ * z * g) * r := by
      intro r hr
      have hgr : g * r * g⁻¹ ∈ R := ((Subgroup.mem_normalizer_iff.mp hNg) r).mp hr
      calc r * (g⁻¹ * z * g) = g⁻¹ * ((g * r * g⁻¹) * z) * g := by group
        _ = g⁻¹ * (z * (g * r * g⁻¹)) * g := by rw [hzRc _ hgr]
        _ = (g⁻¹ * z * g) * r := by group
    have hw1 : g⁻¹ * z * g ≠ 1 := by
      intro e
      apply hz1
      calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
        _ = g * 1 * g⁻¹ := by rw [e]
        _ = 1 := by group
    have heq : g⁻¹ * z * g = z := dszu_unique hZcard hzw hzR hwc hzRc hw1 hz1
    calc g * z = g * (g⁻¹ * z * g) := by rw [heq]
      _ = z * g := by group
  have hXpg : IsPGroup 2 ↥(Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1]; norm_num)
  have hXle : Subgroup.zpowers z ≤ L1 ⊔ L2 ⊔ S :=
    Subgroup.zpowers_le.mpr ((le_sup_right : S ≤ L1 ⊔ L2 ⊔ S) hzS)
  have hX := coreFree h.hyp hXpg hXle
    (fun g hg => dszu_le_normalizer_zpowers (hzL1 g hg))
    (fun g hg => dszu_le_normalizer_zpowers (hzL2 g hg))
    (fun g hg => dszu_le_normalizer_zpowers (hzc g hg))
  exact hz1 (Subgroup.zpowers_eq_bot.mp hX)

end CFSG.GH74.QTGen4.DSGen4
