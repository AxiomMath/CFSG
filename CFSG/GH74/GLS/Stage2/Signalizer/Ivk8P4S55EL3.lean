module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55FTGStmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55FTGLink
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrData
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55EL3Hbar
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55EL3Out
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55EL3Fin
public import CFSG.GroupTheory.SteinbergCBFTSCNRank

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

namespace EL3

open Subgroup CFSG CFSG.ABGLocalTools CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Bar

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_barIn {H X : Subgroup G} {y : HBar H} :
    y ∈ barIn H X ↔ ∃ h : ↥H, (h : G) ∈ X ∧ QuotientGroup.mk' (pPrimeCore 2 ↥H) h = y := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩

omit [Finite G] in
theorem isPGroup_barIn {p : ℕ} {H P : Subgroup G} (hP : IsPGroup p ↥P) :
    IsPGroup p ↥(barIn H P) :=
  (hP.comap_subtype : IsPGroup p ↥(P.subgroupOf H)).map _

omit [Finite G] in
theorem barIn_normalizes {H T P : Subgroup G} (hTP : T ≤ normalizer (P : Set G)) :
    ∀ s ∈ barIn H T, ∀ x ∈ barIn H P, s * x * s⁻¹ ∈ barIn H P := by
  intro s hs x hx
  obtain ⟨a, haT, rfl⟩ := mem_barIn.mp hs
  obtain ⟨b, hbP, rfl⟩ := mem_barIn.mp hx
  refine mem_barIn.mpr ⟨a * b * a⁻¹, ?_, by simp [map_mul, map_inv]⟩
  have := (Subgroup.mem_normalizer_iff.mp (hTP haT) (b : G)).mp hbP
  simpa using this

theorem isSylowOf_barIn {H T : Subgroup G} (hT : IsSylowOf 2 T ⊤) (hTH : T ≤ H) :
    IsSylowOf 2 (barIn H T) ⊤ := by
  have hTH' : IsSylowOf 2 T H := hT.of_le hTH le_top
  obtain ⟨Q, hQ⟩ := hTH'.exists_sylow_eq_subgroupOf
  let Q' : Sylow 2 (HBar H) :=
    Q.mapSurjective (f := QuotientGroup.mk' (pPrimeCore 2 ↥H)) (QuotientGroup.mk'_surjective _)
  have hQ' : (Q' : Subgroup (HBar H)) = barIn H T := by
    rw [Sylow.coe_mapSurjective, hQ]
    rfl
  rw [isSylowOf_iff]
  refine ⟨le_top, hQ' ▸ Q'.isPGroup', ?_⟩
  rw [Subgroup.relIndex_top_right, ← hQ']
  exact Q'.not_dvd_index

theorem injective_toBar {H T : Subgroup G} (hT2 : IsPGroup 2 ↥T) (hTH : T ≤ H) :
    Function.Injective
      ((QuotientGroup.mk' (pPrimeCore 2 ↥H)).comp (Subgroup.inclusion hTH)) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  have hmem : Subgroup.inclusion hTH s ∈ pPrimeCore 2 ↥H := (QuotientGroup.eq_one_iff _).mp hs
  obtain ⟨n, hn⟩ := hT2 s
  have hn' : (Subgroup.inclusion hTH s) ^ 2 ^ n = 1 := by
    rw [← map_pow, hn, map_one]
  set x : ↥(pPrimeCore 2 ↥H) := ⟨Subgroup.inclusion hTH s, hmem⟩ with hx
  have hxpow : x ^ 2 ^ n = 1 := Subtype.ext hn'
  have hcop : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 ↥H)) :=
    pPrimeCore_coprime_card (G := ↥H) (p := 2)
  have hco : Nat.Coprime (orderOf x) (2 ^ n) :=
    (Nat.Coprime.coprime_dvd_left (orderOf_dvd_natCard x) hcop.symm).pow_right n
  have h1 : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd hco (orderOf_dvd_of_pow_eq_one hxpow)
  have hx1 : x = 1 := orderOf_eq_one_iff.mp h1
  have h2 : Subgroup.inclusion hTH s = 1 := congrArg Subtype.val hx1
  have h3 : ((Subgroup.inclusion hTH s : ↥H) : G) = ((1 : ↥H) : G) := congrArg Subtype.val h2
  exact Subtype.ext h3

end Bar

section Rank

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem three_le_pRank_S (h : Stage2Ctx G z k S) : 3 ≤ CFSG.pRank 2 ↥S := by
  have hS := h.sylow_top
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hS
  obtain ⟨-, hP, hdvd⟩ := hS
  rw [Subgroup.relIndex_top_right] at hdvd
  let P : Sylow 2 G := hP.toSylow hdvd
  have hPS : (P : Subgroup G) = S := rfl
  have := (CFSG.SectionRank.pRank_sylow P).2
  rw [hPS] at this
  rw [this]
  exact h.std.rank.1

end Rank

section CaseB

variable {k : Kind} {p : ℕ} {Γ : Type} [Group Γ] [Finite Γ] {V : Type} [AddCommGroup V]
  [Module (ZMod p) V] [Module.Finite (ZMod p) V] {ρ : Γ →* (V →ₗ[ZMod p] V)ˣ} {K : Subgroup Γ}
  [K.Normal] {a : Γ} {P R : Subgroup Γ}

theorem false_of_innerPart_bot (hf : Frame55 k p ρ K a P R) (hU : innerPart (K := K) P = ⊥)
    (hOut : OuterFalse p (K ⧸ center ↥K)) : False := by
  have hnotinn : actYHom (K := K) a ∉
      (MulAut.conj : (K ⧸ center ↥K) →* MulAut (K ⧸ center ↥K)).range := by
    rintro ⟨y, hy⟩
    have hyU : y ∈ innerPart (K := K) P := mem_innerPart.mpr ⟨a, hf.a_mem, hy.symm⟩
    rw [hU, Subgroup.mem_bot] at hyU
    apply hf.actYHom_ne_one
    rw [← hy, hyU, map_one]
  exact hOut _ hnotinn hf.actYHom_pow (hf.exists_sylow_fixed hU)
    fun r hr hr2 hrp Q hQ hinv x hx => hf.actYHom_eq_of_invariant hr hr2 hrp hQ hinv hx

end CaseB

end EL3

open Subgroup CFSG CFSG.ABGLocalTools CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem endgameL3_thm (hInv : InvSec) : EndgameL3 := by
  intro G _ _ z k S T Tstar p H P g X Y hcfg Γ _ _ V _ _ _ ρ K a P' R hf hl hL
  have hKn : K.Normal := hf.normal
  obtain ⟨n, hn, hLie⟩ := hL
  have hp : p.Prime := hf.prime
  have hp2 : p ≠ 2 := hf.odd
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (p ^ n) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨F, _, _, hcard, ⟨eY⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hLie
  have : CharP F p := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  by_cases hU : innerPart (K := K) P' = ⊥
  · exact EL3.false_of_innerPart_bot hf hU
      (OuterFalse.of_mulEquiv eY (outerFalse_l3 hp hp2 hn hcard))
  obtain ⟨⟨y, hyU⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hU
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  obtain ⟨x, hxP', hxy⟩ := mem_innerPart.mp hyU
  obtain ⟨J, hJd⟩ := FTG.compData_of_link hf hl
  obtain ⟨eKJ⟩ := hJd.quot
  have hbad : ¬ KindFactorAll k (↥J ⧸ center ↥J) := fun h =>
    EL3.l3_not_kindFactorAll k hp hn hodd hLie (EL3.kindFactorAll_of_equiv eKJ.symm h)
  obtain ⟨hJn, hcent, -⟩ := EL3.hbarComp_of_bad hInv hcfg.ctx H hJd.comp hbad
  have : J.Normal := hJn
  have hZ : center ↥J = ⊥ := EL3.center_eq_bot_of_centralizer_eq_bot hcent
  let eJ : ↥J ≃* (↥K ⧸ center ↥K) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans eKJ.symm
  obtain ⟨h, hhP, j, hj, hcj, hnc⟩ := hJd.inner hJn x hxP' y hy1' hxy
  have hhJ : QuotientGroup.mk' (pPrimeCore 2 ↥H) h ∈ J := by
    rw [hcent, Subgroup.mem_bot] at hcj
    rw [← inv_mul_eq_one.mp hcj]
    exact hj
  have hh1 : QuotientGroup.mk' (pPrimeCore 2 ↥H) h ≠ 1 := fun h1 =>
    hnc (by rw [h1]; exact Subgroup.one_mem _)
  have hTH : T ≤ H := hcfg.T_le
  have hSb : IsSylowOf 2 (barIn H T) ⊤ := EL3.isSylowOf_barIn hcfg.T_sylow hTH
  have hPb : IsPGroup p ↥(barIn H P) := EL3.isPGroup_barIn hcfg.P_pgroup
  have hSP := EL3.barIn_normalizes (H := H) hcfg.T_norm
  have hPJ : ∃ x ∈ barIn H P, x ∈ J ∧ x ≠ 1 :=
    ⟨QuotientGroup.mk' (pPrimeCore 2 ↥H) h, EL3.mem_barIn.mpr ⟨h, hhP, rfl⟩, hhJ, hh1⟩
  have h3 : 3 ≤ CFSG.pRank 2 ↥T := by
    rw [hcfg.T_eq]
    exact EL3.three_le_pRank_S hcfg.ctx
  obtain ⟨E, hE, h8⟩ := CFSG.GroupTheory.FT63ChII.exists_isElementaryAbelian_of_three_le_pRank h3
  let ν : ↥T →* HBar H := (QuotientGroup.mk' (pPrimeCore 2 ↥H)).comp (Subgroup.inclusion hTH)
  have hν : Function.Injective ν := EL3.injective_toBar hcfg.T_sylow.isPGroup hTH
  have hE' : IsElementaryAbelian 2 ↥(E.map ν) := by
    have := hE
    exact IsElementaryAbelian.map ν
  have h8' : 8 ≤ Nat.card ↥(E.map ν) := by
    rw [Subgroup.card_map_of_injective hν]
    have : (2 : ℕ) ^ 3 = 8 := by norm_num
    omega
  obtain ⟨u, huE, -, B, σ, hu⟩ := EL3.exists_graph_involution hInv hcfg.ctx H hcent hp hn hp2
    hLie hcard eJ eY (E.map ν) hE' h8'
  have huSb : u ∈ barIn H T := by
    obtain ⟨s, -, rfl⟩ := huE
    exact EL3.mem_barIn.mpr ⟨Subgroup.inclusion hTH s, s.2, rfl⟩
  exact EL3.false_of_graph_normalized hp2 (eJ.trans eY) hSb hPb hSP hPJ huSb B σ hu

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
