module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Basic
import CFSG.Goldschmidt.Steps.AxB
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Plane
import CFSG.LocalAnalysis.RankThreeTheoremC.FusionControl
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (SmallRankPlane SmallRankSylowTwo smallRankR
  smallRankIsQ8D8)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}

private theorem p65g_exists_sylow_chain {f : ℕ} {F : Subgroup G} (hf : f.Prime)
    (hF : IsPGroup f F) (hFM : F ≤ M) :
    ∃ Fh : Subgroup G, F ≤ Fh ∧ Fh ≤ M ∧ IsPGroup f Fh ∧ Open.pRank f Fh = Open.pRank f M ∧
      ∃ F₀ : Sylow f G, Fh ≤ (F₀ : Subgroup G) := by
  obtain ⟨Fh, hFFh, hFhM, hFh, hidx⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.exists_sylow_le_of_isPGroup hf hFM hF
  haveI : Fact f.Prime := ⟨hf⟩
  obtain ⟨F₀, hle⟩ := hFh.exists_le_sylow
  exact ⟨Fh, hFFh, hFhM, hFh,
    CFSG.LocalAnalysis.RankThreeTheoremC.pRank_eq_of_sylow hf hFhM hFh hidx, F₀, hle⟩

private theorem p65g_core (hS : Situation G p P M) {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2)
    (h4 : 4 ≤ Open.pRank f M) {F : Subgroup G} (hF : IsPGroup f F) (hFM : F ≤ M) :
    ∃ F₀ : Sylow f G, F ≤ (F₀ : Subgroup G) ∧ 4 ≤ Open.pRank f (F₀ : Subgroup G) ∧
      CFSG.AGLEmbedding.D1Local f F₀ M ∧ GLBCore f 2 (F₀ : Subgroup G) ≤ M := by
  obtain ⟨Fh, hFFh, hFhM, hFh, hrk, F₀, hle⟩ := p65g_exists_sylow_chain hf hF hFM
  have h4' : 4 ≤ Open.pRank f Fh := hrk ▸ h4
  obtain ⟨hD, hcore⟩ := p65_d1Local_of_le hS hf hf2 h4 hFhM hFh (by omega) F₀ hle
  exact ⟨F₀, hFFh.trans hle, h4'.trans (CFSG.SectionRank.pRank_mono hf.one_lt hle), hD, hcore⟩

theorem p65_cyclic_of_not_le (hS : Situation G p P M) {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2)
    (h4 : 4 ≤ Open.pRank f M) {F : Subgroup G} (hF : IsPGroup f F) (hFM : F ≤ M)
    (hHM : ¬ normalizer (F : Set G) ≤ M) : IsCyclic F := by
  by_contra hnc
  obtain ⟨F₀, hFF₀, -, -, hcore⟩ := p65g_core hS hf hf2 h4 hF hFM
  have h2 : 2 ≤ Open.pRank f F :=
    CFSG.LocalAnalysis.RankThreeTheoremC.two_le_pRank_of_not_isCyclic hf hf2 hF hnc
  exact hHM ((CFSG.AGLEmbeddingD2.normalizer_le_glbCore f 2 hFF₀ h2).trans hcore)

private theorem p65g_isMulCommutative_of_sylow {f : ℕ} [Fact f.Prime] (F₀ P' : Sylow f G)
    (hP' : IsMulCommutative (P' : Subgroup G)) : IsMulCommutative (F₀ : Subgroup G) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P' F₀
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨s, hs, hsa⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 a.2
  obtain ⟨t, ht, htb⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 b.2
  apply Subtype.ext
  have hst : s * t = t * s := congrArg Subtype.val (mul_comm' (⟨s, hs⟩ : (P' : Subgroup G)) ⟨t, ht⟩)
  have hsa' : g * s * g⁻¹ = a := hsa
  have htb' : g * t * g⁻¹ = b := htb
  show (a : G) * b = b * a
  rw [← hsa', ← htb']
  calc g * s * g⁻¹ * (g * t * g⁻¹) = g * (s * t) * g⁻¹ := by group
    _ = g * (t * s) * g⁻¹ := by rw [hst]
    _ = g * t * g⁻¹ * (g * s * g⁻¹) := by group

set_option linter.unusedVariables false in
theorem p65_f_lt_p (hS : Situation G p P M) {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) (hfp : f ≠ p)
    (h4 : 4 ≤ Open.pRank f M) {F : Subgroup G} {y : G} (hF : IsPGroup f F) (hF1 : F ≠ ⊥)
    (hFM : F ≤ M) (hHM : ¬ normalizer (F : Set G) ≤ M) (hy : y ∈ F) (hyo : orderOf y = f)
    (hrk : Open.pRank f (centralizer ({y} : Set G)) ≤ 2) : f < p := by
  by_contra hlt
  have hpf : p < f := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hfp)
  obtain ⟨F₀, hFF₀, h4₀, hD, -⟩ := p65g_core hS hf hf2 h4 hF hFM
  obtain ⟨⟨-, hMtop, -, P', -, -, hcase⟩, -⟩ := hS.larger f F₀ M hpf hD
  rcases hcase with ⟨hdvd, hall⟩ | ⟨-, -, hcomm, -⟩
  · have hfF : f ∣ Nat.card F := hyo ▸ Subgroup.orderOf_dvd_natCard F hy
    exact hHM (CFSG.LocalAnalysis.RankFourTheoremC.normalizer_le_of_stronglyEmbedded
      ⟨hMtop, hdvd, hall⟩ hFM hfF)
  · haveI : Fact f.Prime := ⟨hf⟩
    haveI := p65g_isMulCommutative_of_sylow F₀ P' hcomm
    have hle : (F₀ : Subgroup G) ≤ centralizer ({y} : Set G) := by
      intro a ha
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : (F₀ : Subgroup G)) ⟨y, hFF₀ hy⟩)
    have := CFSG.SectionRank.pRank_mono hf.one_lt hle
    omega

private theorem p65g_mem_normalizer_centralizer {F : Subgroup G} {b : G}
    (hb : b ∈ normalizer (F : Set G)) :
    b ∈ normalizer ((centralizer (F : Set G) : Subgroup G) : Set G) := by
  have key : ∀ {w : G}, w ∈ normalizer (F : Set G) → ∀ c ∈ centralizer (F : Set G),
      w * c * w⁻¹ ∈ centralizer (F : Set G) := by
    intro w hw c hc
    rw [mem_centralizer_iff]
    intro a ha
    have h1 : w⁻¹ * a * w ∈ F := by
      simpa using (mem_normalizer_iff.mp (inv_mem hw) a).mp ha
    have h2 := mem_centralizer_iff.mp hc _ h1
    calc a * (w * c * w⁻¹) = w * ((w⁻¹ * a * w) * c) * w⁻¹ := by group
      _ = w * (c * (w⁻¹ * a * w)) * w⁻¹ := by rw [h2]
      _ = w * c * w⁻¹ * a := by group
  rw [mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    exact key hb c hc
  · intro hc
    simpa [mul_assoc] using key (inv_mem hb) _ hc

set_option linter.unusedVariables false in
theorem p65_final_contradiction (hKF : P65CoprimeRankTwo) {f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hf : f.Prime) (hf2 : f ≠ 2) (hfp : f < p)
    {B F Fs R : Subgroup G} {y : G}
    (hB : IsElemAbelian p B) (hBc : Nat.card B = p ^ 2) (hBR : B ≤ R) (hR : IsPGroup p R)
    (hF : IsPGroup f F) (hFs : IsPGroup f Fs) (hFFs : F ≤ Fs) (hcyc : IsCyclic F)
    (hy : y ∈ F) (hyo : orderOf y = f)
    (hBF : B ≤ normalizer (F : Set G)) (hBFs : B ≤ normalizer (Fs : Set G))
    (hRFs : R ≤ normalizer (Fs : Set G))
    (hrk : Open.pRank f (centralizer ({y} : Set G)) ≤ 2)
    (hcycR : IsCyclic (R ⊓ centralizer (Fs : Set G) : Subgroup G)) : False := by
  haveI : Fact f.Prime := ⟨hf⟩
  have hBp : IsPGroup p B := IsPGroup.of_card hBc
  have hF₀p : IsPGroup f (Fs ⊓ centralizer (F : Set G) : Subgroup G) := hFs.to_le inf_le_left
  have hBF₀ : B ≤ normalizer ((Fs ⊓ centralizer (F : Set G) : Subgroup G) : Set G) := by
    intro b hb
    exact inf_normalizer_le_normalizer_inf
      ⟨hBFs hb, p65g_mem_normalizer_centralizer (hBF hb)⟩
  have hF₀y : (Fs ⊓ centralizer (F : Set G) : Subgroup G) ≤ centralizer ({y} : Set G) := by
    intro c hc
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.mp hc.2 y hy).symm
  have hrk₀ : Open.pRank f (Fs ⊓ centralizer (F : Set G) : Subgroup G) ≤ 2 :=
    (CFSG.SectionRank.pRank_mono hf.one_lt hF₀y).trans hrk
  have hBC : B ≤ centralizer ((Fs ⊓ centralizer (F : Set G) : Subgroup G) : Set G) :=
    hKF G p f _ B hp hp5 hf hf2 hfp hF₀p hBp hBF₀ hrk₀
  have hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsCyclic.commGroup (α := F)).mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hFF₀ : F ≤ (Fs ⊓ centralizer (F : Set G) : Subgroup G) := fun a ha =>
    ⟨hFFs ha, mem_centralizer_iff.mpr fun b hb => hFab b hb a ha⟩
  have hBCF : B ≤ centralizer (F : Set G) := hBC.trans (Subgroup.centralizer_le hFF₀)
  have hcop : Nat.Coprime (Nat.card B) f := by
    rw [hBc]
    exact ((Nat.coprime_primes hp hf).mpr hfp.ne').pow_left 2
  have hfix : Fs ⊓ centralizer (F : Set G) ≤ centralizer (B : Set G) :=
    Subgroup.le_centralizer_iff.mp hBC
  have hFsB : Fs ≤ centralizer (B : Set G) :=
    CFSG.Goldschmidt.N10 G Fs B F hFs hcop hF hBFs (hFFs.trans le_normalizer)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hBCF) hfix
  have hBle : B ≤ R ⊓ centralizer (Fs : Set G) :=
    le_inf hBR (Subgroup.le_centralizer_iff.mpr hFsB)
  have h2 : 2 ≤ Open.pRank p (R ⊓ centralizer (Fs : Set G) : Subgroup G) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.le_pRank_of_isElemAbelian hp hBle hB hBc
  exact CFSG.LocalAnalysis.RankThreeTheoremC.not_isCyclic_of_two_le_pRank hp h2 hcycR

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
