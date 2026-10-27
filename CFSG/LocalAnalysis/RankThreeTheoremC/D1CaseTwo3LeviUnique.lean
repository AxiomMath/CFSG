module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3PlusCore
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.OneLieLambdaAux
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Config

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}

theorem D1CaseTwoData3.mem_normalizer_of_levi (hOut : KFactOutCyclic) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hSch : KFactCatalogSchreier)
    (hd : D1CaseTwoData3 3 P M H R Rbar)
    {Kb : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hKb : IsComponentOf Kb ⊤)
    (hKX : ¬ Kb ≤ d1X0 3 M H)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    {V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hVP : V ≤ blockPL M (pCoreOf 2 H) L)
    (hVp : ⁅V, V⁆ = V) (hV3 : 3 ∣ Nat.card V)
    (hVC : V ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥)
    {t : G} (htH : t ∈ H) (htM : t ∈ M) : t ∈ Subgroup.normalizer (L : Set G) := by
  by_contra hnot
  have h := hd.toPhaseThree hOut hS hKL
  have hp3 : Nat.Prime 3 := Nat.prime_three
  set L' : Subgroup G := L.map (MulAut.conj t).toMonoidHom with hL'def
  have hLc : IsTwoPrimeComponent M L := hL.toIsTwoPrimeComponent
  have hL'c : IsTwoPrimeComponent M L' := hLc.map_conj htM
  have hne : L ≠ L' := fun he => hnot (Subgroup.mem_normalizer_iff_map_conj_eq.mpr he.symm)
  set tb : ↥M ⧸ CFSG.pCore 2 ↥M := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, htM⟩ with htb
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  obtain ⟨d, hdo⟩ := exists_prime_orderOf_dvd_card' 3 hV3
  have hdV : (d : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ V := d.2
  have hdo' : orderOf (d : ↥M ⧸ CFSG.pCore 2 ↥M) = 3 := by rw [Subgroup.orderOf_coe]; exact hdo
  have hd3 : (d : ↥M ⧸ CFSG.pCore 2 ↥M) ^ 3 = 1 := by rw [← hdo']; exact pow_orderOf_eq_one _
  have hKeq := h.toD1Escape.inf_eq_inf_normalizer_twoCore
  have hNL : Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L ≤ H ⊓ M := by
    intro x hx
    rw [hKeq]
    exact ⟨hLc.le hx.2, hx.1⟩
  have hVHM : V ≤ barM M (H ⊓ M) := hVP.trans (barM_mono hNL)
  have hVL : V ≤ barM M L := hVP.trans (barM_mono inf_le_right)
  obtain ⟨V', hV'le, hV'p, hV'bar⟩ := exists_perfect_le_of_le_barM (inf_le_right : H ⊓ M ≤ M)
    hVHM hVp
  set A : Subgroup G := d1PlusCore 3 H Kb ⊓ M with hA
  have hAM : A ≤ M := inf_le_right
  have hV'A : V' ≤ A := fun x hx =>
    ⟨hd.perfect_le_plusCore hOut hS hKL hSch hKb hKX hV'le hV'p hx, (hV'le hx).2⟩
  have hVA : V ≤ barM M A := hV'bar ▸ barM_mono hV'A
  have hHM : t ∈ H ⊓ M := ⟨htH, htM⟩
  have hconjHM : ∀ x ∈ H ⊓ M, t * x * t⁻¹ ∈ H ⊓ M := fun x hx =>
    (H ⊓ M).mul_mem ((H ⊓ M).mul_mem hHM hx) ((H ⊓ M).inv_mem hHM)
  set V'' : Subgroup G := V'.map (MulAut.conj t).toMonoidHom with hV''def
  have hV''p : ⁅V'', V''⁆ = V'' := by rw [hV''def, ← Subgroup.map_commutator, hV'p]
  have hV''le : V'' ≤ H ⊓ M := by
    rintro _ ⟨x, hx, rfl⟩
    exact hconjHM x (hV'le hx)
  have hV''A : V'' ≤ A := fun x hx =>
    ⟨hd.perfect_le_plusCore hOut hS hKL hSch hKb hKX hV''le hV''p hx, (hV''le hx).2⟩
  have hV''bar : barM M V'' = V.map (MulAut.conj tb).toMonoidHom := by
    rw [hV''def, barM_map_conj htM, hV'bar]
  have hV''VA : V.map (MulAut.conj tb).toMonoidHom ≤ barM M A :=
    hV''bar ▸ barM_mono hV''A
  set y₁ : ↥M ⧸ CFSG.pCore 2 ↥M := (d : ↥M ⧸ CFSG.pCore 2 ↥M) with hy₁
  set y₂ : ↥M ⧸ CFSG.pCore 2 ↥M := tb * y₁ * tb⁻¹ with hy₂
  have hy₂V : y₂ ∈ V.map (MulAut.conj tb).toMonoidHom := ⟨y₁, hdV, rfl⟩
  have hy₁A : y₁ ∈ barM M A := hVA hdV
  have hy₂A : y₂ ∈ barM M A := hV''VA hy₂V
  have hy₁L : y₁ ∈ barM M L := hVL hdV
  have hy₂L : y₂ ∈ barM M L' := by
    rw [hL'def, barM_map_conj htM]
    exact ⟨y₁, hy₁L, rfl⟩
  have hy₁q : IsPGroup 3 (Subgroup.zpowers y₁) :=
    CFSG.AGLEmbedding.isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hd3)
  have hy₂3 : y₂ ^ 3 = 1 := by
    rw [hy₂, conj_pow, hd3, mul_one, mul_inv_cancel]
  have hy₂q : IsPGroup 3 (Subgroup.zpowers y₂) :=
    CFSG.AGLEmbedding.isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hy₂3)
  have hy₁ne : y₁ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hdo'
    omega
  have hnc₁ : ∃ l ∈ barM M L, y₁ * l ≠ l * y₁ := by
    by_contra hcon
    push Not at hcon
    have hC : y₁ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      Subgroup.mem_centralizer_iff.mpr fun l hl => (hcon l hl).symm
    have : y₁ ∈ V ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := ⟨hdV, hC⟩
    rw [hVC, Subgroup.mem_bot] at this
    exact hy₁ne this
  have hnc₂ : ∃ l ∈ barM M L', y₂ * l ≠ l * y₂ := by
    obtain ⟨l, hl, hne'⟩ := hnc₁
    refine ⟨tb * l * tb⁻¹, ?_, ?_⟩
    · rw [hL'def, barM_map_conj htM]
      exact ⟨l, hl, rfl⟩
    · intro heq
      apply hne'
      have : tb * (y₁ * l) * tb⁻¹ = tb * (l * y₁) * tb⁻¹ := by
        calc tb * (y₁ * l) * tb⁻¹ = (tb * y₁ * tb⁻¹) * (tb * l * tb⁻¹) := by group
          _ = (tb * l * tb⁻¹) * (tb * y₁ * tb⁻¹) := heq
          _ = tb * (l * y₁) * tb⁻¹ := by group
      simpa using this
  have h2 := two_blocks_pRank_ge hAM hp3 (by norm_num) hLc hL'c hne hy₁A hy₂A hy₁L hy₂L hy₁q hy₂q
    hnc₁ hnc₂
  have h1 : Open.pRank 3 A ≤ Open.pRank 3 (d1PlusCore 3 H Kb) :=
    pRank_mono 3 hp3 inf_le_left
  have h3 := hd.pRank_plusCore_le_one hKb hKX
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC
