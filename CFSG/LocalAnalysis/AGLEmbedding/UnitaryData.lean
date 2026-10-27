module

public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
public import CFSG.LocalAnalysis.AGLEmbedding.TorusData
import CFSG.LocalAnalysis.AGLEmbedding.TorusIrreducible
import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTransfer
import CFSG.LocalAnalysis.AGLEmbedding.SocleCompetitor
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section UnitaryData

variable {G : Type} [Group G] [Finite G]

theorem stmtUnitaryData_of (hB : StmtUnitaryBorel) : StmtUnitaryData := by
  intro G _ _ p _ d hd T _ _ hTe hTs P M H R U h hind
  have hp : p.Prime := Fact.out
  obtain ⟨K, hKn, ⟨eT⟩, hC, hUK⟩ := h.socle
  obtain ⟨eTd⟩ := hTe
  obtain ⟨Rbar, hRbar, hred⟩ := h.ext.reducedNongeneration
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  set X₀ := ((H ⊓ M).subgroupOf H).map π with hX₀
  set Ub : Subgroup (H ⧸ primeComplementCore (G := H) p) := (Rbar : Subgroup _) ⊓ K with hUbdef
  set Zb := Ub ⊓ Subgroup.centralizer (Ub : Set _) with hZbdef
  obtain ⟨hn2, hUcard, hcomm, hpow, hD1, hDp, hCU, ⟨ψ, hψ, hψZ, hc⟩, hppd, hsolv, hrank⟩ :=
    hB Rbar X₀ K Ub Zb d hd hred hKn ⟨eT.trans eTd⟩ hC rfl rfl
  have hn0 : d.1.fieldExponent ≠ 0 := by omega
  have hUH : U ≤ H := h.le_R.trans h.ext.le_H
  have hUp : IsPGroup p U := h.ext.isPGroup.to_le h.le_R
  set X := U ⊓ Subgroup.centralizer (U : Set G) with hXdef
  have hXU : X ≤ U := inf_le_left
  have hXH : X ≤ H := hXU.trans hUH
  have hXp : IsPGroup p X := hUp.to_le hXU
  have hUb : (U.subgroupOf H).map π = Ub := by rw [hUK, ← hRbar]
  have hXb : (X.subgroupOf H).map π = Zb := by
    rw [hXdef, map_inf_centralizer_eq hUH hUp, hUb]
  have hNHM : GLBPrimeCore p H ≤ H ⊓ M := h.ext.primeCore_le_inf'.1
  have hZbp : IsPGroup p Zb := Rbar.isPGroup'.to_le (inf_le_left.trans inf_le_left)
  have hZbcard := (isElemAbelian_range_galoisField hn0 ψ hψ).2
  rw [hψZ] at hZbcard
  have hZb1 : Zb ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hZbcard
    have := Nat.one_lt_pow hn0 hp.one_lt
    omega
  have hph3 : D1PhaseThree p P M H R := h.ext.toPhaseThreeU h.glob
    (h.ext.primeCore_inf_eq_iff.mpr (primeComplementCore_eq_bot_of_dichotomy hD1 hZbp hZb1))
  have hX1 : X ≠ ⊥ := by
    intro hX
    apply hZb1
    rw [← hXb, hX, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  have hUN : U ⊓ GLBPrimeCore p H = ⊥ := inf_eq_bot_of_isPGroup hp hUp (glbPrimeCore_coprime p H)
  have hinj : ∀ {A B : Subgroup G}, A ≤ U → B ≤ U →
      (A.subgroupOf H).map π ≤ (B.subgroupOf H).map π → A ≤ B := by
    intro A B hAU hBU hAB a ha
    obtain ⟨b, hb, hba⟩ := hAB (Subgroup.mem_map_of_mem _
      (Subgroup.mem_subgroupOf.mpr ha) : π ⟨a, hUH (hAU ha)⟩ ∈ _)
    have hbN : ((b⁻¹ * ⟨a, hUH (hAU ha)⟩ : H) : G) ∈ GLBPrimeCore p H := by
      rw [mem_glbPrimeCore_iff_mk_eq_one, map_mul, map_inv, hba, inv_mul_cancel]
    have hbU : ((b⁻¹ * ⟨a, hUH (hAU ha)⟩ : H) : G) ∈ U := by
      simpa using U.mul_mem (U.inv_mem (hBU (Subgroup.mem_subgroupOf.mp hb))) (hAU ha)
    have h1 : ((b⁻¹ * ⟨a, hUH (hAU ha)⟩ : H) : G) = 1 := by
      have hmem : ((b⁻¹ * ⟨a, hUH (hAU ha)⟩ : H) : G) ∈ U ⊓ GLBPrimeCore p H := ⟨hbU, hbN⟩
      rwa [hUN, Subgroup.mem_bot] at hmem
    have h2 : (a : G) = b := by
      have := congrArg (fun z => (b : G) * z) h1
      simpa using this
    rw [h2]
    exact Subgroup.mem_subgroupOf.mp hb
  have hcardU : Nat.card U = p ^ (3 * d.1.fieldExponent) := by
    have h1 : Nat.card ((U.subgroupOf H).map π) = Nat.card (U.subgroupOf H) :=
      card_map_mk_of_isPGroup hp _ (primeComplementCore_coprime p) hUp.comap_subtype
    rw [hUb, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUH).toEquiv] at h1
    rw [← h1, hUcard]
  have hcommU : ⁅U, U⁆ = X := by
    have hmap : ((⁅U, U⁆ : Subgroup G).subgroupOf H).map π = (X.subgroupOf H).map π := by
      rw [hXb, ← hcomm, ← hUb, ← Subgroup.map_commutator]
      congr 1
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hUH,
        Subgroup.map_subgroupOf_eq_of_le ((Subgroup.commutator_le_self U).trans hUH)]
    exact le_antisymm (hinj (Subgroup.commutator_le_self U) hXU hmap.le)
      (hinj hXU (Subgroup.commutator_le_self U) hmap.ge)
  have hpowU : ∀ u ∈ U, u ^ p = 1 := by
    intro u hu
    have h1 := hpow (π ⟨u, hUH hu⟩) (hUb ▸ Subgroup.mem_map_of_mem _
      (Subgroup.mem_subgroupOf.mpr hu))
    have h2 : ((⟨u, hUH hu⟩ ^ p : H) : G) ∈ GLBPrimeCore p H := by
      rw [mem_glbPrimeCore_iff_mk_eq_one, map_pow, h1]
    have h3 : ((⟨u, hUH hu⟩ ^ p : H) : G) ∈ U ⊓ GLBPrimeCore p H :=
      ⟨by simpa using U.pow_mem hu p, h2⟩
    rw [hUN, Subgroup.mem_bot] at h3
    simpa using h3
  have htorus := exists_torus_of_map_subgroupOf_eq' hXH hXp hNHM ψ hψ (hψZ.trans hXb.symm)
    fun μ => hc μ
  have hp3 : 3 ≤ p := by have := hp.two_le; have := h.ext.ne_two; omega
  obtain ⟨r, hr, hrdvd, hprim⟩ :=
    CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one hp3
      (show 3 ≤ 2 * d.1.fieldExponent by omega)
  obtain ⟨c, hcX₀, hcN, hcord, hcirr⟩ := hppd r hr hrdvd hprim
  have := Fact.mk hr
  have hpr : (p : ZMod r) ^ (2 * d.1.fieldExponent) = 1 :=
    (CFSG.SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff hp.pos _).mp hrdvd
  have hord : orderOf (p : ZMod r) = 2 * d.1.fieldExponent := by
    rw [orderOf_eq_iff (by omega)]
    exact ⟨hpr, fun k hk hk0 h => hprim k hk0 hk
      ((CFSG.SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff hp.pos k).mpr h)⟩
  have hp0 : (p : ZMod r) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hpr
    exact zero_ne_one hpr
  have hndvd : 2 * d.1.fieldExponent ∣ r - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hp0
  have hr2n : 2 * d.1.fieldExponent < r := by
    have h1 : 0 < r - 1 := by
      rcases Nat.lt_or_ge (r - 1) 1 with h | h
      · exfalso
        have : r = 2 := by have := hr.two_le; omega
        subst this
        obtain ⟨c', hc'⟩ := hndvd
        omega
      · omega
    have := Nat.le_of_dvd h1 hndvd
    omega
  have hrp : r ≠ p := by
    rintro rfl
    exact hp0 (ZMod.natCast_self r)
  have hrp1 : ¬ r ∣ p - 1 := by
    have h := hprim 1 one_pos (by omega)
    rwa [pow_one] at h
  obtain ⟨k, hk, hkc⟩ := hcX₀
  have hkN : k ∈ (Subgroup.normalizer (((U.subgroupOf H).map π : Subgroup _) :
      Set (H ⧸ primeComplementCore (G := H) p))).comap π := by
    rw [Subgroup.mem_comap, hkc, hUb]
    exact hcN
  obtain ⟨o, ho, t₀, ht₀, hot⟩ := Subgroup.mem_sup_of_normal_left.mp
    (comap_normalizer_map_le_sup hp (primeComplementCore (G := H) p)
      (primeComplementCore_coprime p) hUp.comap_subtype hkN)
  have hoN : ((o : H) : G) ∈ GLBPrimeCore p H :=
    (mem_glbPrimeCore_iff_mk_eq_one o).mpr ((QuotientGroup.eq_one_iff o).mpr ho)
  have ht₀K : (t₀ : G) ∈ H ⊓ M := by
    have : (t₀ : G) = ((o : H) : G)⁻¹ * (k : G) := by rw [← hot]; simp
    rw [this]
    exact (H ⊓ M).mul_mem ((H ⊓ M).inv_mem (hNHM hoN)) (Subgroup.mem_subgroupOf.mp hk)
  have ho1 : π o = 1 := by
    rw [hπ, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff o).mpr ho
  have hπt₀ : π t₀ = c := by
    rw [← hkc, ← hot, map_mul, ho1, one_mul]
  have ht₀U : (t₀ : G) ∈ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      have := (Subgroup.mem_normalizer_iff.mp ht₀ ⟨g, hUH hg⟩).mp
        (Subgroup.mem_subgroupOf.mpr hg)
      simpa using Subgroup.mem_subgroupOf.mp this
    · intro hg
      have hgH : g ∈ H := by
        have e : g = (t₀ : G)⁻¹ * ((t₀ : G) * g * (t₀ : G)⁻¹) * t₀ := by group
        rw [e]
        exact H.mul_mem (H.mul_mem (H.inv_mem t₀.2) (hUH hg)) t₀.2
      have := (Subgroup.mem_normalizer_iff.mp ht₀ ⟨g, hgH⟩).mpr
        (Subgroup.mem_subgroupOf.mpr (by simpa using hg))
      exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨e, m, hm, hom⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos t₀).ne' r hr.one_lt.ne'
  set t : G := (t₀ : G) ^ m with htdef
  have htK : t ∈ H ⊓ M := (H ⊓ M).pow_mem ht₀K m
  have htU : t ∈ Subgroup.normalizer (U : Set G) := Subgroup.pow_mem _ ht₀U m
  have htH : t ∈ H := htK.1
  have hπt : ∀ j : ℕ, π ⟨t ^ j, H.pow_mem htH j⟩ = c ^ (m * j) := by
    intro j
    have : (⟨t ^ j, H.pow_mem htH j⟩ : H) = t₀ ^ (m * j) := by
      apply Subtype.ext
      simp [htdef, pow_mul]
    rw [this, map_pow, hπt₀]
  have htr : IsPGroup r (Subgroup.zpowers t) := by
    have h1 : t ^ r ^ e = 1 := by
      rw [htdef, ← pow_mul, mul_comm, ← hom]
      have : (t₀ : G) ^ orderOf t₀ = 1 := by
        rw [← Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one]
      exact this
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hr).mp (orderOf_dvd_of_pow_eq_one h1)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  have hcm : ¬ r ∣ m := hm
  obtain ⟨⟨ub, hubU, hubZ⟩, hcV⟩ := hcirr m hcm
  have hπt1 : π ⟨t, htH⟩ = c ^ m := by
    have := hπt 1
    simpa using this
  have hcr : c ^ r = 1 := by rw [← hcord]; exact pow_orderOf_eq_one c
  have htrU : ∀ u ∈ U, t ^ r * u * (t ^ r)⁻¹ = u := by
    intro u hu
    have htrN : t ^ r ∈ GLBPrimeCore p H := by
      have h0 : π ⟨t ^ r, H.pow_mem htH r⟩ = 1 := by
        rw [hπt r, pow_mul', hcr, one_pow]
      exact (mem_glbPrimeCore_iff_mk_eq_one (p := p) ⟨t ^ r, H.pow_mem htH r⟩).mpr h0
    have h1 : t ^ r * u * (t ^ r)⁻¹ * u⁻¹ ∈ U :=
      U.mul_mem ((Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ htU r) u).mp hu)
        (U.inv_mem hu)
    have h2 : t ^ r * u * (t ^ r)⁻¹ * u⁻¹ ∈ GLBPrimeCore p H := by
      have hn := (le_normalizer_glbPrimeCore p H) (hUH hu)
      have h3 : u * (t ^ r)⁻¹ * u⁻¹ ∈ GLBPrimeCore p H :=
        (Subgroup.mem_normalizer_iff.mp hn _).mp ((GLBPrimeCore p H).inv_mem htrN)
      have e : t ^ r * u * (t ^ r)⁻¹ * u⁻¹ = t ^ r * (u * (t ^ r)⁻¹ * u⁻¹) := by group
      rw [e]
      exact (GLBPrimeCore p H).mul_mem htrN h3
    have h4 : t ^ r * u * (t ^ r)⁻¹ * u⁻¹ = 1 := by
      have hmem : t ^ r * u * (t ^ r)⁻¹ * u⁻¹ ∈ U ⊓ GLBPrimeCore p H := ⟨h1, h2⟩
      rwa [hUN, Subgroup.mem_bot] at hmem
    exact mul_inv_eq_one.mp h4
  have htnt : ∃ u ∈ U, t * u * t⁻¹ * u⁻¹ ∉ X := by
    rw [← hUb] at hubU
    obtain ⟨⟨u, huH⟩, hu, rfl⟩ := hubU
    refine ⟨u, Subgroup.mem_subgroupOf.mp hu, fun hXc => hubZ ?_⟩
    have hmem : π (⟨t, htH⟩ * ⟨u, huH⟩ * (⟨t, htH⟩)⁻¹ * (⟨u, huH⟩)⁻¹) ∈
        (X.subgroupOf H).map π :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (by simpa using hXc))
    rw [hXb, map_mul, map_mul, map_mul, map_inv, map_inv, hπt1] at hmem
    exact hmem
  have hirrU : ∀ V : Subgroup G, X ≤ V → V ≤ U → t ∈ Subgroup.normalizer (V : Set G) →
      V = X ∨ V = U := by
    intro V hXV hVU htV
    have hZV : Zb ≤ (V.subgroupOf H).map π :=
      hXb ▸ Subgroup.map_mono (Subgroup.subgroupOf_mono H hXV)
    have hVUb : (V.subgroupOf H).map π ≤ Ub :=
      hUb ▸ Subgroup.map_mono (Subgroup.subgroupOf_mono H hVU)
    have hcVb : c ^ m ∈ Subgroup.normalizer (((V.subgroupOf H).map π : Subgroup _) :
        Set (H ⧸ primeComplementCore (G := H) p)) := by
      rw [← hπt1]
      exact map_mk_le_normalizer_map_mk (A := Subgroup.zpowers t) (Y := V)
        ((Subgroup.zpowers_le).mpr htV)
        ⟨⟨t, htH⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers t), rfl⟩
    rcases hcV _ hZV hVUb hcVb with hVZ | hVU'
    · left
      exact le_antisymm (hinj hVU hXU (by rw [hXb]; exact hVZ.le)) hXV
    · right
      exact le_antisymm hVU (hinj le_rfl hVU (by rw [hUb]; exact hVU'.ge))
  exact ⟨hph3, hind, hn2, h.le_R, rfl, h.le_nclIn_of_le hTs hXU hX1, hcardU, hcommU, hpowU,
    htorus, fun Y hY hYN => le_glbPrimeCore_or_le_of_forall h.ext.primeCore_le hXH hXp
      (by rw [hXb]; exact hD1) hY hYN,
    fun Y hY hYN hYp => le_sup_glbPrimeCore_of_forall (by rw [hUb]; exact hDp) hY hYN hYp,
    pRank_inf_le_of_pRank_top_le hp hrank,
    fun L hL hLL => le_glbPrimeCore_of_perfect hsolv hL hLL,
    ⟨r, t, hr, hr2n, hrp, hrp1, htK, htU, htr, htrU, htnt, hirrU⟩⟩

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {P : Sylow p G} {M H R U X : Subgroup G}

theorem D1UnitaryData.toTorusData (h : D1UnitaryData p n P M H R U X) :
    D1TorusData p P M H R X := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := h.ph3.ne_two
  have hXU : X ≤ U := h.center_eq ▸ inf_le_left
  obtain ⟨φ, htor⟩ := h.torus
  have hn2 := h.two_le
  have hXel : IsElemAbelian p X := isElemAbelian_of_mulEquiv_galoisField φ
  have hXcard : Nat.card X = p ^ n := by
    rw [← Nat.card_congr φ.toEquiv, Nat.card_congr Multiplicative.toAdd,
      GaloisField.card p n (by omega)]
  refine ⟨h.ph3, h.ind, hXU.trans h.le_R, hXel, ?_, h.normal_dichotomy, h.perfect_le, ?_⟩
  · rw [hXcard]
    exact Nat.pow_le_pow_right hp.pos hn2
  · rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · have hn : n = 2 := by omega
      subst hn
      obtain ⟨t, htK, htX, hirr⟩ := exists_torus_element_two ⟨φ, htor⟩
      exact ⟨p + 1, t, by have := hp.two_le; omega, htK, htX, hirr⟩
    · have htor2 : ∃ φ : Multiplicative (GaloisField p n) ≃* X, ∀ μ : (GaloisField p n)ˣ,
          ∃ t ∈ H ⊓ M, ∀ a : Multiplicative (GaloisField p n),
            t * (φ a : G) * t⁻¹ = φ (Multiplicative.ofAdd
              ((μ : GaloisField p n) ^ 2 * Multiplicative.toAdd a)) := by
        refine ⟨φ, fun μ => ?_⟩
        obtain ⟨t, ht, hta⟩ := htor (μ ^ 2)
        exact ⟨t, ht, fun a => by rw [hta a, Units.val_pow_eq_pow_val]⟩
      obtain ⟨r, t, hr, -, hr2, hr3, -, -, htK, htX, -, -, -, hirr⟩ :=
        exists_ppd_torus_element hp2 hn3 htor2
      exact ⟨r, t, by have := hr.five_le_of_ne_two_of_ne_three hr2 hr3; omega, htK, htX, hirr⟩

end UnitaryData

end CFSG.AGLEmbedding
