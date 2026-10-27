module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Statements2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12InputsF
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L126B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L127Alt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L127Cr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L127Dir
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L127Nm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10BData

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma127_of (hp : Asc82Pre11) (h120 : Asc82Lemma120) (h121 : Asc82Lemma121)
    (h123 : Asc82Lemma123) (h124 : Asc82Lemma124) (h125a : Asc82Lemma125a)
    (h125b : Asc82Lemma125b) (h126 : Asc82Lemma126) (hFus : Asc82StepFusionX) :
    Asc82Lemma127 := by
  intro G _ _ t L S z K1 K2 E X hctx hX y
  obtain ⟨hV8, -, -, hEN, hVsup, -, hVC⟩ := sec126_V_facts hp h120 h121 h124 hctx
  obtain ⟨-, hB16, -, -, -, -, -, -⟩ := sec10BData_of hp.basic hp.facts.b5 hctx.toSec10Z
  have hA5 := (h123 G t L S z K1 K2 E X hctx hX).1
  obtain ⟨hXN, hXt, hXL⟩ := sec127_X_le hp hctx hX hA5
  obtain ⟨V1, V2, hsup, hinf, φ1, φ2, hc1, hc2⟩ := sec127_alt1 hX hA5 hV8.1
  have h1V : V1 ≤ secV t S L E := le_trans le_sup_left hsup.le
  have hbot : X ⊓ centralizer (secV t S L E : Set G) = ⊥ := by
    refine eq_bot_iff.mpr ?_
    rw [← sec127_nat_cent_bot hc1 hA5]
    exact inf_le_inf_left X (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr h1V))
  have hVcard : Nat.card ↥(secV t S L E) = 256 := by
    rw [hV8.2]
    norm_num
  have htE : t ∈ E := by
    rw [← hVsup]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have htN : t ∈ normalizer (secV t S L E : Set G) := hEN htE
  have ht2 : t * t = 1 := sec126_mul_self_of_orderOf hctx.involution
  have ht1 : betaOf (secV t S L E) t ≠ 1 := sec127_betaOf_ne_one htN hVC hB16 hVcard
  have hrange : ∀ u ∈ X, u * u = 1 → u ≠ 1 → ∀ d ∈ secV t S L E, u * d = d * u →
      ∃ v ∈ secV t S L E, u * v * u⁻¹ * v⁻¹ = d := fun u hu hu2 hu1 d hd hdu =>
    sec127_comm_range hV8.1 hsup hinf hc1 hc2 hA5 hu hu2 hu1 hd hdu
  have hfus : ∀ u ∈ X, u * u = 1 → u ≠ 1 →
      ∃ n ∈ normalizer (secV t S L E : Set G), n⁻¹ * t * n = t * u := by
    intro u hu hu2 hu1
    obtain ⟨h, hh⟩ := hFus G t L S z K1 K2 E X hctx hX u hu hu2 hu1
    have htu : h⁻¹ * t * h ∈ secN (secV t S L E) := by
      rw [hh]
      exact (normalizer (secV t S L E : Set G)).mul_mem htN (hXN hu)
    obtain ⟨-, n, hn, hnt⟩ := h126 G t L S z K1 K2 E hctx h htu
    exact ⟨n, hn, hnt.trans hh⟩
  obtain ⟨hKeq, ⟨e⟩⟩ := h125b G t L S z K1 K2 E hctx
  have hKcard : Nat.card ↥(autIn (secN (secV t S L E) ⊓ centralizer ({t} : Set G))
      (secV t S L E)) = 120 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, sec127_card_alt5_type]
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card]
      rfl
    rw [h2]
  have hKX : autIn X (secV t S L E) ≤
      autIn (secN (secV t S L E) ⊓ centralizer ({t} : Set G)) (secV t S L E) :=
    sec127_autIn_mono (le_inf hXN hXt)
  have hKt : betaOf (secV t S L E) t ∈
      autIn (secN (secV t S L E) ⊓ centralizer ({t} : Set G)) (secV t S L E) :=
    sec127_mem_autIn_iff.mpr ⟨t,
      Subgroup.mem_inf.mpr ⟨htN, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩, htN, rfl⟩
  constructor
  · intro hy
    exact sec127_LR hA5 hXN hbot hXt hXL htN ht2 ht1 hKX hKcard hKt hKeq.symm hV8.1 hrange
      (h125a G t L S z K1 K2 E hctx) (hp.r10.l108 G t L S z K1 K2 hctx.toSec10Ctx) hy
  · intro hy
    exact sec127_RL hbot hXN hXt htN ht2 hfus hy

end CFSG.OddStandard.SmallF3.Omega
