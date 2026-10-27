module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.SectionIH
public import CFSG.ClassicalInvolution.Q3.TL3C8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Transport217
public import CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.FStarNormal
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMaxOrb

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

set_option linter.unusedSectionVars false

namespace TwinSecXg

section Section

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

structure TwinSection (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' X' : Subgroup G) :
    Prop where
  le_left : K ≤ X'
  le_right : K' ≤ X'
  gen : (⨆ x : X', conjSub (x : G) K) = X'
  twin : K' ∈ twinSet {L | ∃ x : X', conjSub (x : G) K = L} K
  ne : K' ≠ K
  mem_right : K' ∈ Ω

variable (hs : OrbitStd Ω) {K : Subgroup G} {π : Set (Subgroup G)}

include hs

theorem conj_trans (hπ : π ∈ maxOrbs (nbrAdj Ω) K) {g : G} (hg : conjSub g K ∈ π) :
    ∀ J ∈ conjSub g '' π, ∃ a ∈ conjSub g (piGen π), conjSub a K = J := by
  intro J hJ
  have h := transitive_of_maxOrb hs.graph (isMaxOrb_conj hs.graph hπ g) K
    (hs.mem_conj_image_of_mem hπ hg) J hJ
  have e := piGen_conj π g
  rw [← e]
  exact h

theorem sec_gen (hπ : π ∈ maxOrbs (nbrAdj Ω) K) {g : G} (hg : conjSub g K ∈ π) :
    (⨆ x : ↥(conjSub g (piGen π)), conjSub (x : G) K) = conjSub g (piGen π) := by
  apply le_antisymm
  · refine iSup_le fun x => ?_
    have := conjSub_mono (n := (x : G)) (hs.le_conj_piGen hπ hg)
    rwa [conjSub_eq_self_of_mem x.2] at this
  · have h : piGen (conjSub g '' π) ≤
        ⨆ x : ↥(conjSub g (piGen π)), conjSub (x : G) K := by
      refine piGen_le fun J hJ => ?_
      obtain ⟨a, ha, rfl⟩ := conj_trans hs hπ hg J hJ
      exact le_iSup (fun x : ↥(conjSub g (piGen π)) => conjSub (x : G) K) ⟨a, ha⟩
    rwa [piGen_conj] at h

theorem twin_le (hK : K ∈ Ω) (hπ : π ∈ maxOrbs (nbrAdj Ω) K) (hH1 : NoCentralInv π)
    {g : G} (hg : conjSub g K ∈ π) {K' : Subgroup G} (hK' : K' ∈ twinSet Ω K) :
    K' ≤ conjSub g (piGen π) := by
  have h1 : K' ∈ conjSub g '' π :=
    hs.beta_subset_conj_image hK hπ hg (hs.twinSet_subset_beta hπ hH1 hK')
  rw [← piGen_conj]
  exact le_piGen h1

theorem twin_conj (hK : K ∈ Ω) (hπ : π ∈ maxOrbs (nbrAdj Ω) K) (hH1 : NoCentralInv π)
    {g : G} (hg : conjSub g K ∈ π) {K' : Subgroup G} (hK' : K' ∈ twinSet Ω K) :
    ∃ a ∈ conjSub g (piGen π), conjSub a K = K' :=
  conj_trans hs hπ hg K'
    (hs.beta_subset_conj_image hK hπ hg (hs.twinSet_subset_beta hπ hH1 hK'))

theorem twinSection_conj (hK : K ∈ Ω) (hπ : π ∈ maxOrbs (nbrAdj Ω) K) (hH1 : NoCentralInv π)
    {g : G} (hg : conjSub g K ∈ π) {K' : Subgroup G} (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) :
    TwinSection G Ω K K' (conjSub g (piGen π)) := by
  refine ⟨hs.le_conj_piGen hπ hg, twin_le hs hK hπ hH1 hg hK', sec_gen hs hπ hg, ?_, hne, hK'.1⟩
  obtain ⟨a, ha, hKa⟩ := twin_conj hs hK hπ hH1 hg hK'
  obtain ⟨-, z, hz, hz'⟩ := hK'
  exact ⟨⟨⟨a, ha⟩, hKa⟩, z, hz, hz'⟩

theorem card_conj_lt (hK : K ∈ Ω) (hπ : π ∈ maxOrbs (nbrAdj Ω) K) (hH1 : NoCentralInv π)
    (hZ : Subgroup.center G = ⊥) {z : G} (hz : IsUniqueInvolution K z) (g : G) :
    Nat.card (conjSub g (piGen π)) < Nat.card G := by
  have hle := (hs.conj_piGen_le_centralizer hK hπ hH1 hz g).1
  have hne : Subgroup.centralizer ({g * z * g⁻¹} : Set G) ≠ ⊤ := by
    intro h
    have hc : g * z * g⁻¹ ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro x
      have hx : x ∈ Subgroup.centralizer ({g * z * g⁻¹} : Set G) := by rw [h]; trivial
      exact Subgroup.mem_centralizer_singleton_iff.mp hx
    rw [hZ, Subgroup.mem_bot] at hc
    exact (hz.conj g).ne_one hc
  have hlt : conjSub g (piGen π) < ⊤ := lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hne)
  have := Subgroup.card_lt_of_lt hlt
  rwa [Subgroup.card_top] at this
theorem exists_conj_mem (hK : K ∈ Ω) (hπ : π ∈ maxOrbs (nbrAdj Ω) K) :
    ∃ g : G, conjSub g K ∈ π := by
  obtain ⟨⟨J, hKJ, hJ⟩, -⟩ := hπ
  have hJπ : J ∈ π := by rw [← hJ]; exact mem_orbOf_self K J
  have hJΩ : J ∈ Ω := hs.graph.mem (hs.graph.graph.symm hKJ)
  obtain ⟨g, -, hg⟩ := hs.graph.trans K hK J hJΩ
  exact ⟨g, by rw [hg]; exact hJπ⟩

end Section

section Hself

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def twinJoin (Ω : Set (Subgroup G)) (L : Subgroup G) : Subgroup G :=
  ⨆ J ∈ twinSet Ω L, J

theorem le_twinJoin {L J : Subgroup G} (hJ : J ∈ twinSet Ω L) : J ≤ twinJoin Ω L :=
  le_iSup₂_of_le J hJ le_rfl

theorem isUniqueInvolution_of_mem_twinSet {L J : Subgroup G} {u : G} (hu : IsUniqueInvolution L u)
    (hJ : J ∈ twinSet Ω L) : IsUniqueInvolution J u := by
  obtain ⟨-, z', hz'L, hz'J⟩ := hJ
  rwa [hu.eq hz'L]

theorem twinJoin_le_centralizer {L : Subgroup G} {u : G} (hu : IsUniqueInvolution L u) :
    twinJoin Ω L ≤ Subgroup.centralizer ({u} : Set G) :=
  iSup₂_le fun _ hJ => le_centralizer_of_unique (isUniqueInvolution_of_mem_twinSet hu hJ)

theorem twinJoin_normalized (hΩ : HypOmegaGen Ω) {L : Subgroup G} {u : G}
    (hu : IsUniqueInvolution L u) :
    ∀ c ∈ Subgroup.centralizer ({u} : Set G), ∀ p ∈ twinJoin Ω L, c * p * c⁻¹ ∈ twinJoin Ω L := by
  intro d hd x hx
  have hdz : d * u * d⁻¹ = u := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hd
    rw [hd, mul_inv_cancel_right]
  have hmapd : ∀ J ∈ twinSet Ω L, conjSub d J ∈ twinSet Ω L := by
    intro J hJ
    refine ⟨hΩ.conjInvariant d J hJ.1, u, hu, ?_⟩
    have := (isUniqueInvolution_of_mem_twinSet hu hJ).conj d
    rwa [hdz] at this
  have hsub : (twinJoin Ω L).map (MulAut.conj d).toMonoidHom ≤ twinJoin Ω L := by
    unfold twinJoin
    rw [Subgroup.map_iSup]
    refine iSup_le fun J => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hJ => le_iSup₂_of_le (conjSub d J) (hmapd J hJ) le_rfl
  exact hsub ⟨x, hx, rfl⟩

theorem twinJoin_isPGroup (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J) {L : Subgroup G}
    {u : G} (hu : IsUniqueInvolution L u) : IsPGroup 2 (twinJoin Ω L) := by
  have hT := fun J (hJ : J ∈ twinSet Ω L) => isUniqueInvolution_of_mem_twinSet hu hJ
  have key : ∀ s : Set (Subgroup G), s ⊆ twinSet Ω L → IsPGroup 2 (⨆ J ∈ s, J : Subgroup G) := by
    intro s
    refine Set.Finite.induction_on (motive := fun s _ => s ⊆ twinSet Ω L →
      IsPGroup 2 (⨆ J ∈ s, J : Subgroup G)) s (Set.toFinite s) ?_ ?_
    · intro _
      rw [iSup_emptyset]
      exact IsPGroup.of_card (n := 0) (by simp)
    · intro a s has _ ih hsub
      rw [Set.insert_subset_iff] at hsub
      rw [iSup_insert]
      refine (h2 a hsub.1.1).to_sup_of_normal_left' (ih hsub.2) ?_
      refine iSup₂_le fun J hJ => ?_
      by_cases hJa : J = a
      · rw [hJa]
        exact Subgroup.le_normalizer
      · exact Sec6Gen.le_normalizer_of_twin hΩ (hsub.2 hJ).1 hsub.1.1 hJa (hT J (hsub.2 hJ))
          (hT a hsub.1)
  exact key _ subset_rfl

theorem uAt_of_cyclic_index_two (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    {L : Subgroup G} (hL : L ∈ Ω) {u : G} (hu : IsUniqueInvolution L u)
    (hcyc : ∃ U : Subgroup G, U ≤ L ∧ IsCyclic ↥U ∧ U.relIndex L = 2) : UAt Ω u L := by
  obtain ⟨U, hUL, hUc, hUi⟩ := hcyc
  exact ⟨U, ⟨L, mem_RSet_of_isPGroup hL (h2 L hL), hUL, hUc, hUi⟩, hUL, twinJoin Ω L,
    ⟨twinJoin_le_centralizer hu, twinJoin_isPGroup hΩ h2 hu, twinJoin_normalized hΩ hu⟩,
    hUL.trans (le_twinJoin ⟨hL, u, hu, hu⟩)⟩

theorem exists_cyclic_index_two_of_card_eight (hΩ : HypOmegaGen Ω) {L : Subgroup G} (hL : L ∈ Ω)
    (h8 : Nat.card L = 8) :
    ∃ U : Subgroup G, U ≤ L ∧ IsCyclic ↥U ∧ U.relIndex L = 2 := by
  obtain ⟨-, P, hPL, hPnc⟩ := hΩ.omega1 L hL
  have hx : ∃ x ∈ L, x * x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hPnc
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have h1 := hcon (a * b : G) (L.mul_mem (hPL.1 a.2) (hPL.1 b.2))
    have ha := hcon (a : G) (hPL.1 a.2)
    have hb := hcon (b : G) (hPL.1 b.2)
    show (a : G) * b = b * a
    have e1 : (a : G)⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    have e2 : (b : G)⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    have e3 : ((a : G) * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h1
    rw [mul_inv_rev, e1, e2] at e3
    exact e3.symm
  obtain ⟨x, hxN, hx2⟩ := hx
  have hxord : orderOf x = 4 := by
    have hdvd : orderOf x ∣ 8 := by
      rw [← h8]
      exact Subgroup.orderOf_dvd_natCard L hxN
    have hx1 : x ≠ 1 := fun h => hx2 (by rw [h, one_mul])
    have hne2 : orderOf x ≠ 2 := fun h => hx2 (by rw [← pow_two, ← h, pow_orderOf_eq_one])
    have hne1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
    have hne8 : orderOf x ≠ 8 := by
      intro h
      have hzN : Subgroup.zpowers x = L := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxN) ?_
        rw [Nat.card_zpowers, h, h8]
      apply hPnc
      refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      have ha : (a : G) ∈ Subgroup.zpowers x := hzN ▸ hPL.1 a.2
      have hb : (b : G) ∈ Subgroup.zpowers x := hzN ▸ hPL.1 b.2
      obtain ⟨i, hi⟩ := ha
      obtain ⟨j, hj⟩ := hb
      show (a : G) * b = b * a
      rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
    have : orderOf x ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hdiv : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [hdiv] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  have hUcard : Nat.card ↥(Subgroup.zpowers x) = 4 := by rw [Nat.card_zpowers, hxord]
  refine ⟨Subgroup.zpowers x, Subgroup.zpowers_le.mpr hxN, inferInstance, ?_⟩
  have h1 := Subgroup.relIndex_mul_card (Subgroup.zpowers x) L
  rw [inf_eq_left.mpr (Subgroup.zpowers_le.mpr hxN), hUcard, h8] at h1
  omega

theorem hself_of_card_eight (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    (h8 : ∀ J ∈ Ω, Nat.card J = 8) :
    ∀ L ∈ Ω, ∀ u : G, IsUniqueInvolution L u → UAt Ω u L := fun L hL _ hu =>
  uAt_of_cyclic_index_two hΩ h2 hL hu (exists_cyclic_index_two_of_card_eight hΩ hL (h8 L hL))

end Hself

section Strong

variable {G : Type} [Group G] [Finite G]

theorem exists_normal_twoSub_of_tightInO2 {X : Subgroup G}
    (hO : classicalInvolutionOddCore ↥X = ⊥) {t : X} (h : TightInO2 (secInv X t)) :
    ∃ P : Subgroup G, P ≤ X ∧ IsPGroup 2 ↥P ∧ (∀ x ∈ X, ∀ p ∈ P, x * p * x⁻¹ ∈ P) ∧
      (t : G) ∈ P := by
  obtain ⟨Pb, hPn, hP2, htP⟩ := h
  set f := QuotientGroup.mk' (classicalInvolutionOddCore ↥X) with hf
  have hker : IsPGroup 2 ↥f.ker := by
    rw [hf, QuotientGroup.ker_mk', hO]
    exact IsPGroup.of_card (n := 0) (by simp)
  have hP0 : IsPGroup 2 ↥(Pb.comap f) := hP2.comap_of_ker_isPGroup f hker
  have hP0n : (Pb.comap f).Normal := hPn.comap f
  refine ⟨(Pb.comap f).map X.subtype, Subgroup.map_subtype_le _, hP0.map _, ?_, ⟨t, htP, rfl⟩⟩
  rintro x hx _ ⟨p, hp, rfl⟩
  exact ⟨⟨x, hx⟩ * p * ⟨x, hx⟩⁻¹, hP0n.conj_mem p hp ⟨x, hx⟩, rfl⟩

theorem twoIn_of_tightInO2 {X : Subgroup G} {w : G} (hXw : X ≤ Subgroup.centralizer ({w} : Set G))
    (hXn : (X.subgroupOf (Subgroup.centralizer ({w} : Set G))).Normal)
    (hO : classicalInvolutionOddCore ↥X = ⊥) {t : X} (h : TightInO2 (secInv X t)) :
    TwoIn w (t : G) := by
  obtain ⟨P, hPX, hP2, hPn, htP⟩ := exists_normal_twoSub_of_tightInO2 hO h
  have hPnorm : (P.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hPX]
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hPn x hx y hy, fun hy => ?_⟩
    have := hPn x⁻¹ (X.inv_mem hx) _ hy
    simpa [mul_assoc] using this
  have hPQ : P ≤ pCoreOf 2 X :=
    CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 P X hPX hPnorm hP2
  have hN := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_subgroupOf 2 X
    (Subgroup.centralizer ({w} : Set G)) hXw hXn
  have hQC : pCoreOf 2 X ≤ Subgroup.centralizer ({w} : Set G) :=
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 X).trans hXw
  refine ⟨pCoreOf 2 X, ⟨hQC, CFSG.RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 X, ?_⟩,
    hPQ htP⟩
  intro c hc p hp
  have := hN.conj_mem ⟨p, hQC hp⟩ (Subgroup.mem_subgroupOf.mpr hp) ⟨c, hc⟩
  exact Subgroup.mem_subgroupOf.mp this

theorem oddCore_eq_bot_of_normal {X : Subgroup G} {w : G}
    (hXn : (X.subgroupOf (Subgroup.centralizer ({w} : Set G))).Normal)
    (hXw : X ≤ Subgroup.centralizer ({w} : Set G))
    (hC : classicalInvolutionOddCore ↥(Subgroup.centralizer ({w} : Set G)) = ⊥) :
    classicalInvolutionOddCore ↥X = ⊥ := by
  have hsub : IsSubnormal X (Subgroup.centralizer ({w} : Set G)) :=
    IsSubnormal.step hXw hXn (IsSubnormal.refl _)
  have h1 := Balance.oddCoreIn_le_of_isSubnormal hsub
  have h2 : Balance.oddCoreIn (Subgroup.centralizer ({w} : Set G)) = ⊥ := by
    show (classicalInvolutionOddCore ↥(Subgroup.centralizer ({w} : Set G))).map _ = ⊥
    rw [hC, Subgroup.map_bot]
  rw [h2, le_bot_iff] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp h1

theorem maxAdj_conj_left {Ω : Set (Subgroup G)} (hs : OrbitStd Ω) {K : Subgroup G}
    {π : Set (Subgroup G)} (hπ : π ∈ maxOrbs (nbrAdj Ω) K) {g : G} (hg : conjSub g K ∈ π) :
    MaxAdj (nbrAdj Ω) (conjSub g K) K := by
  have hKJ : nbrAdj Ω K (conjSub g K) := adj_of_mem_isMaxOrb hs.graph hπ hg
  exact ⟨hs.graph.graph.symm hKJ, orbOf_mem_maxOrbs hs.graph hKJ
    (by rw [orbOf_eq_of_mem_isMaxOrb hπ hg]; exact hπ)⟩

theorem e2At_of_tightInO2 {Ω : Set (Subgroup G)} (hs : OrbitStd Ω) {K : Subgroup G}
    (hK : K ∈ Ω) {π : Set (Subgroup G)} (hπ : π ∈ maxOrbs (nbrAdj Ω) K) (hH1 : NoCentralInv π)
    {z : G} (hz : IsUniqueInvolution K z) {g : G} (hKX : K ≤ conjSub g (piGen π))
    (hO : classicalInvolutionOddCore ↥(conjSub g (piGen π)) = ⊥)
    (h : TightInO2 (secInv (conjSub g (piGen π)) ⟨z, hKX hz.mem⟩)) :
    E2At (conjSub g K) K := by
  intro z' u hz' hu
  have h1 : g * z * g⁻¹ = z' := (hz.conj g).eq hz'
  have h2 : z = u := hz.eq hu
  have := twoIn_of_tightInO2 (hs.conj_piGen_le_centralizer hK hπ hH1 hz g).1
    (hs.conj_piGen_normal hK hπ hH1 hz g) hO h
  subst h1 h2
  exact this

theorem card_eq_of_mem_conjClass {K₀ K J : Subgroup G} (hK : K ∈ CoreAssembly.conjClass K₀)
    (hJ : J ∈ CoreAssembly.conjClass K₀) : Nat.card J = Nat.card K := by
  obtain ⟨a, rfl⟩ := hK
  obtain ⟨b, rfl⟩ := hJ
  have : ∀ c : G, Nat.card (conjSub c K₀) = Nat.card K₀ := fun c =>
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  rw [this, this]

theorem conj_trans_of_mem_conjClass {K₀ K : Subgroup G} (hK : K ∈ CoreAssembly.conjClass K₀) :
    ∀ J ∈ CoreAssembly.conjClass K₀, ∃ g : G, conjSub g K = J := by
  rintro J ⟨b, rfl⟩
  obtain ⟨a, rfl⟩ := hK
  refine ⟨b * a⁻¹, ?_⟩
  ext x
  simp only [mem_conjSub_iff]
  rw [show a⁻¹ * ((b * a⁻¹)⁻¹ * x * (b * a⁻¹)) * a = b⁻¹ * x * b by group]

variable {K₀ : Subgroup G}

theorem twin_thin_of_tightInO2 (hs : TwinGraphStd K₀)
    (hO2 : ∀ P : Subgroup G, P.Normal → IsPGroup 2 ↥P → P = ⊥)
    {K : Subgroup G} (hK : K ∈ CoreAssembly.conjClass K₀)
    (hq8 : Nonempty (↥K ≃* QuaternionGroup 2)) {π : Set (Subgroup G)}
    (hπ : π ∈ maxOrbs (nbrAdj (CoreAssembly.conjClass K₀)) K) (hH1 : NoCentralInv π)
    {z : G} (hz : IsUniqueInvolution K z) {g : G} (hg : conjSub g K ∈ π)
    (hKX : K ≤ conjSub g (piGen π))
    (hO : classicalInvolutionOddCore ↥(conjSub g (piGen π)) = ⊥)
    (h : TightInO2 (secInv (conjSub g (piGen π)) ⟨z, hKX hz.mem⟩)) :
    ∀ M N : Subgroup G, MaxAdj (nbrAdj (CoreAssembly.conjClass K₀)) M N →
      ThinAt (CoreAssembly.conjClass K₀) M N := by
  have hos := hs.orbitStd
  have h8 : ∀ J ∈ CoreAssembly.conjClass K₀, Nat.card J = 8 := by
    intro J hJ
    rw [card_eq_of_mem_conjClass hK hJ, Nat.card_congr hq8.some.toEquiv]
    simp [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hself := hself_of_card_eight hs.hyp hs.two h8
  have hE := e2At_of_tightInO2 hos hK hπ hH1 hz hKX hO h
  have hmax := maxAdj_conj_left hos hπ hg
  rcases TC.inO2_or_thinAt hs.hyp hs.two hs.sep hK (conj_trans_of_mem_conjClass hK)
      (iSup_conjClass_eq_top hs.gen) hs.conn hself hmax hE hz with ⟨P, hPn, hP2, hzP⟩ | hthin
  · exfalso
    have := hO2 P hPn hP2
    rw [this, Subgroup.mem_bot] at hzP
    exact hz.ne_one hzP
  · exact hthin

theorem normalTwo_eq_bot_of_fstar_simple (hS : IsSimpleGroup ↥(genFittingFStar G))
    (hnab : ∃ a b : ↥(genFittingFStar G), a * b ≠ b * a) {P : Subgroup G} (hPn : P.Normal)
    (hP : IsPGroup 2 ↥P) : P = ⊥ := by
  rcases InductionBridge.normal_eq_bot_or_fstar_le hS hPn with h | hle
  · exact h
  · exfalso
    have h2 : IsPGroup 2 ↥(genFittingFStar G) := hP.to_le hle
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Nontrivial ↥(genFittingFStar G) := IsSimpleGroup.toNontrivial
    have hZ := h2.center_nontrivial
    have hZtop : Subgroup.center ↥(genFittingFStar G) = ⊤ := by
      rcases (Subgroup.center ↥(genFittingFStar G)).normal_of_characteristic.eq_bot_or_eq_top
        with h | h
      · exact absurd h ((Subgroup.nontrivial_iff_ne_bot _).mp hZ)
      · exact h
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center ↥(genFittingFStar G) := hZtop ▸ Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.mp ha b).symm)

end Strong

section Transport

variable {Y Y' : Type} [Group Y] [Group Y']

theorem isSubnormal_map_hom (φ : Y →* Y') {A B : Subgroup Y} (h : IsSubnormal A B) :
    IsSubnormal (A.map φ) (B.map φ) :=
  h.map φ

theorem map_centralizer_singleton_equiv (φ : Y ≃* Y') (t : Y) :
    (Subgroup.centralizer ({t} : Set Y)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ t} : Set Y') := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' := Subgroup.mem_centralizer_singleton_iff.mp (show x ∈ Subgroup.centralizer ({t} : Set Y) from hx)
    rw [Subgroup.mem_centralizer_singleton_iff]
    show φ x * φ t = φ t * φ x
    rw [← map_mul, ← map_mul, hx']
  · intro hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    refine ⟨φ.symm y, ?_, by simp⟩
    show φ.symm y ∈ Subgroup.centralizer ({t} : Set Y)
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hy

theorem isClassicalMember3_map_equiv (φ : Y ≃* Y') {L : Subgroup Y} {t : Y}
    (h : IsClassicalMember3 L t) : IsClassicalMember3 (L.map φ.toMonoidHom) (φ t) where
  orderOf_eq_two := by rw [MulEquiv.orderOf_eq]; exact h.orderOf_eq_two
  mem := Subgroup.mem_map_of_mem _ h.mem
  subnormal := by
    have := isSubnormal_map_hom φ.toMonoidHom h.subnormal
    rwa [map_centralizer_singleton_equiv] at this
  nonempty_equiv := by
    obtain ⟨e'⟩ := h.nonempty_equiv
    let e : L ≃* L.map φ.toMonoidHom := L.equivMapOfInjective φ.toMonoidHom φ.injective
    have hO : (classicalInvolutionOddCore L).map e.toMonoidHom =
        classicalInvolutionOddCore (L.map φ.toMonoidHom) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e
    exact ⟨(QuotientGroup.congr _ _ e hO).symm.trans e'⟩

end Transport

section TwinLift

variable {G : Type} [Group G] [Finite G]

@[expose] def IsClassicalMember3On (X L : Subgroup G) (z : G) : Prop :=
  ∃ hz : z ∈ X, IsClassicalMember3 (L.subgroupOf X) (⟨z, hz⟩ : X)

theorem twin_map_secImage {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 J) {K : Subgroup G} (hK : K ∈ Ω) {X : Subgroup G} (hKX : K ≤ X)
    {K' : Subgroup G} (hK' : K' ∈ twinSet {L | ∃ x : X, conjSub (x : G) K = L} K)
    (hne : K' ≠ K) :
    secImage X K' ∈ twinSet (CoreAssembly.conjClass (secImage X K)) (secImage X K) ∧
      secImage X K' ≠ secImage X K := by
  have hfam := restrictFamily_conjFamily hKX
  have hΔ := hypOmegaGen_conjClass_section hΩ hK hKX
  have hNodd := CFSG.ComponentClassification.OddCore.odd_card ↥X
  have hmem2 : ∀ M ∈ CoreAssembly.conjClass (K.subgroupOf X), IsPGroup 2 M := by
    rintro _ ⟨g, rfl⟩
    exact isPGroup_conjSub g (h2 K hK).comap_subtype
  have hqf : quotFamily (CoreAssembly.conjClass (K.subgroupOf X))
      (classicalInvolutionOddCore ↥X) = CoreAssembly.conjClass (secImage X K) :=
    QuaternionBridge.image_conjClass (N := classicalInvolutionOddCore ↥X) (K.subgroupOf X)
  have hmemJ := CoreAssembly.mem_conjClass_self (K.subgroupOf X)
  obtain ⟨hLP, z, hzJ, hzL⟩ := hK'
  have hLX : K' ≤ X := by
    obtain ⟨x, rfl⟩ := hLP
    have := conjSub_mono (n := (x : G)) hKX
    rwa [conjSub_eq_self_of_mem x.2] at this
  have hK'' : K'.subgroupOf X ∈ twinSet (CoreAssembly.conjClass (K.subgroupOf X))
      (K.subgroupOf X) := by
    refine ⟨?_, ⟨z, hKX hzJ.mem⟩, isUniqueInvolution_subgroupOf hzJ hKX,
      isUniqueInvolution_subgroupOf hzL hLX⟩
    rw [← hfam]
    exact ⟨K', hLP, hLX, rfl⟩
  obtain ⟨hm, hne'⟩ := OddQuot.twin_map hΔ hmem2 hNodd hmemJ hK''
    (subgroupOf_ne_of_ne hKX hLX hne)
  exact ⟨by rw [← hqf]; exact hm, hne'⟩

theorem subgroupOf_map_subtype_self {X : Subgroup G} (M : Subgroup X) :
    (M.map X.subtype).subgroupOf X = M := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem map_centralizer_subtype_singleton {X : Subgroup G} {a : G} (ha : a ∈ X) :
    (Subgroup.centralizer ({(⟨a, ha⟩ : ↥X)} : Set ↥X)).map X.subtype =
      X ⊓ Subgroup.centralizer ({a} : Set G) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_inf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy))⟩
  · rintro ⟨hxY, hxa⟩
    exact ⟨⟨x, hxY⟩, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxa)), rfl⟩

theorem sl2_pow_eight_imp_pow_four : ∀ g : SL(2, ZMod 3), g ^ 8 = 1 → g ^ 4 = 1 := by
  decide +kernel

theorem sl2_card_pow_four :
    (Finset.univ.filter (fun g : SL(2, ZMod 3) => g ^ 4 = 1)).card = 8 := by
  decide +kernel

theorem normal_of_card_eight_sl2 (S : Subgroup SL(2, ZMod 3)) (hS : Nat.card S = 8) :
    S.Normal := by
  classical
  have hsub : ∀ g ∈ S, g ^ 4 = 1 := by
    intro g hg
    have h1 : (⟨g, hg⟩ : S) ^ Nat.card S = 1 := pow_card_eq_one'
    rw [hS] at h1
    apply sl2_pow_eight_imp_pow_four
    simpa using congrArg Subtype.val h1
  have heq : ∀ g : SL(2, ZMod 3), g ^ 4 = 1 → g ∈ S := by
    intro g hg
    have hle : (Set.toFinset (S : Set SL(2, ZMod 3))) ⊆
        Finset.univ.filter (fun g : SL(2, ZMod 3) => g ^ 4 = 1) := by
      intro x hx
      simp only [Set.mem_toFinset, SetLike.mem_coe] at hx
      simp [hsub x hx]
    have hcard : (Finset.univ.filter (fun g : SL(2, ZMod 3) => g ^ 4 = 1)).card ≤
        (Set.toFinset (S : Set SL(2, ZMod 3))).card := by
      rw [sl2_card_pow_four, Set.toFinset_card, ← Nat.card_eq_fintype_card]
      exact hS.ge
    have := Finset.eq_of_subset_of_card_le hle hcard
    have hg' : g ∈ Finset.univ.filter (fun g : SL(2, ZMod 3) => g ^ 4 = 1) := by simp [hg]
    rw [← this] at hg'
    simpa using hg'
  refine ⟨fun n hn g => heq _ ?_⟩
  rw [conj_pow, hsub n hn]
  group

theorem IsClassicalMember3On.quotient {X L : Subgroup G} {z : G} (hLX : L ≤ X)
    (h : IsClassicalMember3On X L z) :
    Nonempty (↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, ZMod 3)) := by
  obtain ⟨_, hc⟩ := h
  obtain ⟨e'⟩ := hc.nonempty_equiv
  let e0 : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLX
  have hO : (classicalInvolutionOddCore ↥(L.subgroupOf X)).map e0.toMonoidHom =
      classicalInvolutionOddCore ↥L :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e0
  exact ⟨(QuotientGroup.congr _ _ e0 hO).symm.trans e'⟩

theorem lift217Side_of_exact {X K L : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    (hcent : K ≤ Subgroup.centralizer (X : Set G)) (hKL : K ≤ L) (hK8 : Nat.card K = 8)
    (hOL : classicalInvolutionOddCore ↥L = ⊥)
    (hq : Nonempty (↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, ZMod 3))) :
    ∃ A : Subgroup G, Lift217Side X K L A z := by
  obtain ⟨e0⟩ := hq
  let e : ↥L ≃* SL(2, ZMod 3) :=
    ((QuotientGroup.quotientMulEquivOfEq hOL).trans QuotientGroup.quotientBot).symm.trans e0
  have hL24 : Nat.card L = 24 := by
    rw [Nat.card_congr e.toEquiv, natCard_sl2Three]
  have hnorm : (K.subgroupOf L).Normal := by
    have hcard : Nat.card (K.subgroupOf L) = 8 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv]
      exact hK8
    have h1 : Nat.card ((K.subgroupOf L).map e.toMonoidHom) = 8 := by
      rw [← Nat.card_congr ((K.subgroupOf L).equivMapOfInjective e.toMonoidHom e.injective).toEquiv]
      exact hcard
    have h2 := (normal_of_card_eight_sl2 _ h1).comap e.toMonoidHom
    rwa [Subgroup.comap_map_eq_self_of_injective e.injective] at h2
  have h3 : 3 ∣ Nat.card L := by rw [hL24]; norm_num
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hA₀ : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, ha]
  set A : Subgroup G := (Subgroup.zpowers a).map L.subtype with hA
  have hAcard : Nat.card A = 3 := by
    rw [hA, Subgroup.card_map_of_injective L.subtype_injective, hA₀]
  have hA3 : IsPGroup 3 ↥A := IsPGroup.of_card (n := 1) (by rw [hAcard, pow_one])
  have hAL : A ≤ L := Subgroup.map_subtype_le _
  have hle : K ⊔ A ≤ L := sup_le hKL hAL
  have hd8 : 8 ∣ Nat.card ↥(K ⊔ A) := hK8 ▸ Subgroup.card_dvd_of_le le_sup_left
  have hd3 : 3 ∣ Nat.card ↥(K ⊔ A) := hAcard ▸ Subgroup.card_dvd_of_le le_sup_right
  have hd24 : 24 ∣ Nat.card ↥(K ⊔ A) :=
    (show Nat.Coprime 8 3 by norm_num).mul_dvd_of_dvd_of_dvd hd8 hd3
  have hpos : 0 < Nat.card ↥(K ⊔ A) := Nat.card_pos
  have hge : Nat.card L ≤ Nat.card ↥(K ⊔ A) := by
    rw [hL24]; exact Nat.le_of_dvd hpos hd24
  exact ⟨A, hz, hcent, hKL, hnorm, ⟨e0⟩, hAL, hA3,
    (Subgroup.eq_of_le_of_card_ge hle hge).symm⟩

end TwinLift

end TwinSecXg

variable {G : Type} [Group G] [Finite G] {K₀ : Subgroup G}

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
