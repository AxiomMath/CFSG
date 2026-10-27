module

public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
public import CFSG.LocalAnalysis.AGLEmbedding.BlockData
public import CFSG.LocalAnalysis.AGLEmbedding.SocleConfig
import CFSG.LocalAnalysis.AGLEmbedding.ReeArith
import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTransfer

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

@[expose] def StmtReeSocle : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) →
      ∀ d : TauCeti.ValidLieTypeIndex, IsReeGTwoIndex p d →
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        IsSimpleGroup K ∧ Nonempty (K ≃* CatGroup d) ∧ D1SocleConfig K p P M H R (d1LiftX p H R K)

theorem stmtReeSocle_of (hKR1 : KFactReeSchur) : StmtReeSocle := by
  intro G _ _ p _ P M H R Rbar hcfg K hK huniq hcent d hd e
  obtain ⟨e₁⟩ := e
  have hp3 : p = 3 := hd.1
  have hd3 : IsReeGTwoIndex 3 d := hp3 ▸ hd
  have hZp : IsPGroup 3 (Subgroup.center K) := hp3 ▸ hcfg.isPGroup_center hK
  have hZ : Subgroup.center K = ⊥ := hKR1 K d hd3 hK.2.2 hZp ⟨e₁⟩
  have eK : K ≃* K ⧸ Subgroup.center K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2.2.2
  refine ⟨eK.isSimpleGroup, ⟨eK.trans e₁⟩, hcfg.ext, hcfg.glob, d1LiftX_le p H R K,
    K, normal_of_forall_isComponentOf_eq hK huniq, ⟨MulEquiv.refl _⟩,
    hcfg.centralizer_eq_bot hK huniq hcent hZ, map_d1LiftX p H R K⟩

@[expose] def StmtReeBlockData : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : TauCeti.ValidLieTypeIndex}, IsReeGTwoIndex 3 d →
    ∀ {T : Type} [Group T] [Finite T], Nonempty (T ≃* CatGroup d) →
    ∀ {P : Sylow 3 G} {M H R U : Subgroup G}, D1SocleConfig T 3 P M H R U →
      D1BlockData 3 P M H R (U ⊓ Subgroup.centralizer (U : Set G))

theorem stmtReeBlockData_of (hRB : StmtReeBorel) : StmtReeBlockData := by
  intro G _ _ d hd T _ _ hTe P M H R U h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn3 : 3 ≤ d.1.fieldExponent := hd.three_le_fieldExponent
  have hodd : Odd d.1.fieldExponent := hd.odd_fieldExponent
  obtain ⟨K, hKn, ⟨eT⟩, hC, hUK⟩ := h.socle
  obtain ⟨eTd⟩ := hTe
  obtain ⟨Rbar, hRbar, hred⟩ := h.ext.reducedNongeneration
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3)
  set X₀ := ((H ⊓ M).subgroupOf H).map π
  obtain ⟨hD1, hCZ, ⟨ψ, hψ, hψZ, hc⟩, hsolv, hrank⟩ :=
    hRB Rbar X₀ K d hd hred hKn ⟨eT.trans eTd⟩ hC
  set Ub : Subgroup (H ⧸ primeComplementCore (G := H) 3) := (Rbar : Subgroup _) ⊓ K
  set Zb := Ub ⊓ Subgroup.centralizer (Ub : Set (H ⧸ primeComplementCore (G := H) 3))
  have hUH : U ≤ H := h.le_R.trans h.ext.le_H
  have hUp : IsPGroup 3 U := h.ext.isPGroup.to_le h.le_R
  set X := U ⊓ Subgroup.centralizer (U : Set G) with hXdef
  have hXH : X ≤ H := inf_le_left.trans hUH
  have hXp : IsPGroup 3 X := hUp.to_le inf_le_left
  have hUb : (U.subgroupOf H).map π = Ub := by rw [hUK, ← hRbar]
  have hXb : (X.subgroupOf H).map π = Zb := by
    rw [hXdef, map_inf_centralizer_eq hUH hUp, hUb]
  have hNHM : GLBPrimeCore 3 H ≤ H ⊓ M := h.ext.primeCore_le_inf'.1
  have hZbp : IsPGroup 3 Zb := Rbar.isPGroup'.to_le (inf_le_left.trans inf_le_left)
  have hn0 : d.1.fieldExponent ≠ 0 := by omega
  have hZbcard := (isElemAbelian_range_galoisField hn0 ψ hψ).2
  rw [hψZ] at hZbcard
  have hZb1 : Zb ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hZbcard
    have := Nat.one_lt_pow hn0 (by norm_num : 1 < 3)
    omega
  have hph3 : D1PhaseThree 3 P M H R := h.ext.toPhaseThreeU h.glob
    (h.ext.primeCore_inf_eq_iff.mpr (primeComplementCore_eq_bot_of_dichotomy hD1 hZbp hZb1))
  have htorus := exists_torus_of_map_subgroupOf_eq hXH hXp hNHM ψ hψ (hψZ.trans hXb.symm)
    fun μ => hc μ
  have hrankK : Open.pRank 3 (H ⊓ M) ≤ 2 * d.1.fieldExponent :=
    pRank_inf_le_of_pRank_top_le Nat.prime_three hrank
  obtain ⟨r, t, hr, hr2n, hr2, hr3, hrp, hrp1, htK, htX, htr, htr1, htnt, hirr⟩ :=
    exists_ppd_torus_element_odd (by norm_num) hn3 hodd htorus
  obtain ⟨φ, -⟩ := htorus
  refine ⟨⟨hph3, inf_le_left.trans h.le_R, ?_, ?_, ?_⟩, ?_, ?_,
    fun L hL hLL => le_glbPrimeCore_of_perfect hsolv hL hLL,
    ⟨r, t, hr, hr2, hr3, hrp, hrp1, by omega, htK, htX, htr, htr1, htnt, hirr⟩⟩
  ·
    intro hX
    apply hZb1
    rw [← hXb, hX, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  ·
    exact fun Y hY hYN => le_glbPrimeCore_or_le_of_forall h.ext.primeCore_le hXH hXp
      (by rw [hXb]; exact hD1) hY hYN
  ·
    intro k hk hkX
    have hkH : k ∈ H := hk.1
    have hk0 : π ⟨k, hkH⟩ ∈ X₀ := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hk)
    have hkC : π ⟨k, hkH⟩ ∈ Subgroup.centralizer (Zb : Set _) := by
      rw [← hXb, Subgroup.mem_centralizer_iff]
      rintro _ ⟨x, hx, rfl⟩
      have h1 := (mem_glbPrimeCore_iff_mk_eq_one (p := 3)
        (⟨k, hkH⟩ * x * (⟨k, hkH⟩)⁻¹ * x⁻¹ : H)).mp
        (by simpa using hkX x (Subgroup.mem_subgroupOf.mp hx))
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      have h2 := mul_inv_eq_one.mp h1
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    have hkU : π ⟨k, hkH⟩ ∈ (R.subgroupOf H).map π := by
      rw [← hRbar]
      exact (hCZ ⟨hk0, hkC⟩).1
    obtain ⟨r, hr, hrk⟩ := hkU
    have hrk' : ((r⁻¹ * ⟨k, hkH⟩ : H) : G) ∈ GLBPrimeCore 3 H := by
      rw [mem_glbPrimeCore_iff_mk_eq_one, map_mul, map_inv, hrk, inv_mul_cancel]
    have hk' : k = (r : G) * ((r⁻¹ * ⟨k, hkH⟩ : H) : G) := by simp
    rw [hk']
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hr) hrk'
  ·
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', rfl⟩ := φ.surjective a
      obtain ⟨b', rfl⟩ := φ.surjective b
      rw [← map_mul, ← map_mul, mul_comm]
    · obtain ⟨a, ha⟩ := φ.surjective ⟨x, hx⟩
      have hap : a ^ 3 = 1 := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
      have : (⟨x, hx⟩ : X) ^ 3 = 1 := by rw [← ha, ← map_pow, hap, map_one]
      simpa using congrArg Subtype.val this
  ·
    rw [← Nat.card_congr φ.toEquiv, Nat.card_congr Multiplicative.toAdd,
      GaloisField.card 3 _ hn0]
    exact Nat.pow_le_pow_right (by norm_num) hn3

end CFSG.AGLEmbedding
