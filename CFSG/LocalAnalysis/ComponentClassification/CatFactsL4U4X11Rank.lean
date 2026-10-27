module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4X11Conf
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4X11Sp4E8
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4L2Dih
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Rank
public import CFSG.RankThree.PartOne.LIT.RankProjective
public import CFSG.RankThree.PartOne.LIT.RankMatrix
public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.GH74.Orders.LieType

public section

namespace CFSG.ComponentClassification.GSThmB.X11

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.Assembly.LowTwoRank

theorem two_ne_zero_of_odd_card {F : Type} [Field F] [Finite F] (h : Odd (Nat.card F)) :
    (2 : F) ≠ 0 := by
  intro h2
  obtain ⟨k, hk⟩ := h
  have h0 : ((Nat.card F : ℕ) : F) = 0 := by
    have := card_nsmul_eq_zero' (G := F) (x := 1)
    rwa [nsmul_eq_mul, mul_one] at this
  rw [hk, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, h2, zero_mul, zero_add, Nat.cast_one] at h0
  exact one_ne_zero h0

theorem odd_pow_of_ne_two {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : Odd (p ^ f) :=
  (hp.odd_of_ne_two hp2).pow

theorem three_le_pRank_of_lieModel {K : Type} [Group K] [Finite K]
    (hK : Blueprint.LieModel (K ⧸ pPrimeCore 2 K) .PSp 2 3 1) : 3 ≤ CFSG.pRank 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := GH74.statedClassicalModel_of_lieModel (by norm_num) hK
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card (by rw [hF]; decide)
  have hN : ¬ 2 ∣ Nat.card (pPrimeCore 2 K) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card
  rw [← GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _ hN,
    SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_top_eq_of_mulEquiv one_lt_two e,
    ← SectionRank.pRank_eq_open_pRank_top]
  exact E8.three_le_pRank_statedProj_statedSp_two h2

theorem pRank_le_of_le {G : Type} [Group G] [Finite G] {K N : Subgroup G} (h : K ≤ N) :
    CFSG.pRank 2 K ≤ CFSG.pRank 2 N := by
  rw [SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_eq_open_pRank_top]
  exact SectionRank.pRank_top_le_of_injective one_lt_two (Subgroup.inclusion h)
    (Subgroup.inclusion_injective h)

theorem KConf.three_le_pRank {G : Type} [Group G] [Finite G] {N : Subgroup G}
    (h : KConf G N) : 3 ≤ CFSG.pRank 2 N := by
  obtain ⟨-, -, -, -, K, -, hKN, -, -, hKm⟩ := h
  exact (three_le_pRank_of_lieModel hKm).trans (pRank_le_of_le hKN)

theorem pRank_le_two_of_lieModel_psl_two {Y : Type} [Group Y] [Finite Y] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hL : Blueprint.LieModel Y .PSL 2 p f) :
    CFSG.pRank 2 Y ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [SectionRank.pRank_eq_open_pRank_top]
  refine SectionRank.pRank_le one_lt_two fun E _ hE => ?_
  have hE2 : IsPGroup 2 E := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 x x.2)⟩
  obtain ⟨T, hET⟩ := hE2.exists_le_sylow
  have hT2 : IsPGroup 2 (T : Subgroup Y) := T.isPGroup'
  by_cases h8 : 8 ≤ Nat.card T
  · obtain ⟨m, hm, ⟨φ⟩⟩ := CatFactsL4U4.L2Dih.dihedral_of_lieModel_psl_two Y p f hp hp2 hf hL T h8
    have h2m : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := QuasithinUnique.card_le_four_of_dihedral hT2 h2m φ hET fun x hx => hE.2 x hx
    simpa using this
  · obtain ⟨k, hk⟩ := hE2.exists_card_eq
    have hle : Nat.card E ≤ Nat.card T := Subgroup.card_le_of_le hET
    rw [hk] at hle ⊢
    have hk3 : k < 3 := by
      by_contra hk3
      have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem pRank_two_statedProj_le_of_det {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0)
    (H : Subgroup (GL (Fin 3) F))
    (hH : ∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) F).det = 1) :
    CFSG.pRank 2 (StatedProj H) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsc : ¬ 2 ∣ Nat.card ((StatedScalars (Fin 3) F).subgroupOf H) := by
    have h1 := RankThree.PartOne.LIT.not_dvd_card_scalars (m := 3) Nat.prime_two (by norm_num)
      H fun g hg hc => by
        simpa using RankThree.PartOne.LIT.pow_card_eq_one_of_det g hc (hH g hg)
    rwa [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar]
  rw [GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _ hsc,
    SectionRank.pRank_eq_open_pRank_top]
  exact RankThree.PartOne.LIT.pRank_le_of_card_gl one_lt_two H fun E hEH hc he =>
    RankThree.PartOne.LIT.card_le_sq_of_det_gl Nat.prime_two (by exact_mod_cast h2) (by simp)
      E hc he fun g hg => hH g (hEH hg)

theorem det_of_mem_statedSL {F : Type} [Field F] {g : GL (Fin 3) F} (hg : g ∈ StatedSL 3 F) :
    (g : Matrix (Fin 3) (Fin 3) F).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hg

theorem det_of_mem_statedSU {F : Type} [Field F] {q : ℕ} {g : GL (Fin 3) F}
    (hg : g ∈ StatedSU 3 q F) : (g : Matrix (Fin 3) (Fin 3) F).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSU hg

variable {G : Type} [Group G] [Finite G] {N : Subgroup G}

theorem KConf.not_psl_two (h : KConf G N) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    ¬ Blueprint.LieModel ↥N .PSL 2 p f := fun hL => by
  have := h.three_le_pRank.trans (pRank_le_two_of_lieModel_psl_two hp hp2 hf hL)
  omega

theorem KConf.not_psl_three (h : KConf G N) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ Blueprint.LieModel ↥N .PSL 3 p f := fun hL => by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := GH74.statedClassicalModel_of_lieModel (by norm_num) hL
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card (by rw [hF]; exact odd_pow_of_ne_two hp hp2)
  have hle := pRank_two_statedProj_le_of_det h2 (StatedSL 3 F) fun g hg => det_of_mem_statedSL hg
  rw [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_top_eq_of_mulEquiv one_lt_two e,
    ← SectionRank.pRank_eq_open_pRank_top] at hle
  have := h.three_le_pRank.trans hle
  omega

theorem KConf.not_psu_three (h : KConf G N) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ Blueprint.LieModel ↥N .PSU 3 p f := fun hL => by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := GH74.statedClassicalModel_of_lieModel (by norm_num) hL
  have h2 : (2 : F) ≠ 0 :=
    two_ne_zero_of_odd_card (by rw [hF]; exact (odd_pow_of_ne_two hp hp2).pow)
  have hle := pRank_two_statedProj_le_of_det h2 (StatedSU 3 (p ^ f) F)
    fun g hg => det_of_mem_statedSU hg
  rw [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_top_eq_of_mulEquiv one_lt_two e,
    ← SectionRank.pRank_eq_open_pRank_top] at hle
  have := h.three_le_pRank.trans hle
  omega

end CFSG.ComponentClassification.GSThmB.X11
