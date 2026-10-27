module

public import CFSG.CGT.Foote82.Climb
public import CFSG.CGT.Foote82.EF1Bridge
public import CFSG.CGT.Foote82.Statements
import CFSG.CGT.Foote82.EF1Steps
import CFSG.CGT.Foote82.FPrime
import CFSG.LocalAnalysis.WeakClosure81.Eleven

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec19.SimsTheoremC

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_centralizerModTwoCore {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ Subgroup.normalizer (centralizerModTwoCore L : Set G) := by
  have hP := mem_normalizer_pCoreOf hg
  have key : ∀ c ∈ Subgroup.normalizer (L : Set G),
      c ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) →
      ∀ x ∈ centralizerModTwoCore L, c * x * c⁻¹ ∈ centralizerModTwoCore L := by
    intro c hcL hcP x hx
    obtain ⟨hxL, hx⟩ := mem_centralizerModTwoCore_iff.mp hx
    refine mem_centralizerModTwoCore_iff.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hcL hxL)
      (Subgroup.inv_mem _ hcL), fun y hy => ?_⟩
    have hy' : c⁻¹ * y * c ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcL) y).mp hy
      simpa using this
    have h1 := (Subgroup.mem_normalizer_iff.mp hcP _).mp (hx _ hy')
    have e : c * x * c⁻¹ * y * (c * x * c⁻¹)⁻¹ * y⁻¹ =
        c * (x * (c⁻¹ * y * c) * x⁻¹ * (c⁻¹ * y * c)⁻¹) * c⁻¹ := by group
    rw [e]
    exact h1
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg hP x, fun hx => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) (Subgroup.inv_mem _ hP) _ hx
  simpa [mul_assoc] using this

theorem pCoreOf_le_centralizerModTwoCore (L : Subgroup G) :
    pCoreOf 2 L ≤ centralizerModTwoCore L := by
  intro x hx
  have hxL : x ∈ L := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L hx
  refine mem_centralizerModTwoCore_iff.mpr ⟨Subgroup.le_normalizer hxL, fun y hy => ?_⟩
  have hN := CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L hy
  have h1 : y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 L :=
    (Subgroup.mem_normalizer_iff.mp hN _).mp (Subgroup.inv_mem _ hx)
  have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ hx h1

theorem le_normalizer_of_isSylowTwoOf {L N R : Subgroup G} (hLN : L ≤ N)
    (hR : IsSylowTwoOf R (centralizerModTwoCore L ⊓ N)) :
    L ≤ Subgroup.normalizer (R : Set G) := by
  have hPC : pCoreOf 2 L ≤ centralizerModTwoCore L ⊓ N :=
    le_inf (pCoreOf_le_centralizerModTwoCore L)
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L).trans hLN)
  have hPR : pCoreOf 2 L ≤ R := hR.le_of_normalizes hPC
    (fun c hc => mem_normalizer_pCoreOf (mem_centralizerModTwoCore_iff.mp hc.1).1)
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 L)
  have key : ∀ ℓ ∈ L, ∀ r ∈ R, ℓ * r * ℓ⁻¹ ∈ R := by
    intro ℓ hℓ r hr
    have h1 := (mem_centralizerModTwoCore_iff.mp (hR.le hr).1).2 ℓ hℓ
    have e : ℓ * r * ℓ⁻¹ = (r * ℓ * r⁻¹ * ℓ⁻¹)⁻¹ * r := by group
    rw [e]
    exact Subgroup.mul_mem _ (hPR (Subgroup.inv_mem _ h1)) hr
  intro ℓ hℓ
  rw [Subgroup.mem_normalizer_iff]
  intro r
  refine ⟨key ℓ hℓ r, fun hr => ?_⟩
  have := key ℓ⁻¹ (Subgroup.inv_mem _ hℓ) _ hr
  simpa [mul_assoc] using this

theorem ef1_climb (hG : IsCharTwoType G) (hKP : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G)
    (h66 : Thm66F) {K P N : Subgroup G} (hKB : InFooteB K) (hKF : IsFType K)
    (hKF' : IsFPrimeType K) (hP : EF1Class K P)
    (hPmax : ∀ P', EF1Class K P' → P ≤ P' → P' = P) (hN : GLBIsMaxTwoLocal N)
    (hKPN : K ⊔ P ≤ N) (hsub : ¬ IsSubnormal K N) :
    IsFooteBlock N (kClosure N K) ∧ K ≤ kClosure N K ∧
      P ≤ Subgroup.normalizer (kClosure N K : Set G) ∧
      kClosure N K = Subgroup.closure {g | ∃ ℓ ∈ kClosure N K, ∃ k ∈ K, g = ℓ * k * ℓ⁻¹} ∧
      kClosure N K ≠ K ∧ FooteArrow K (kClosure N K) := by
  have hch := ef1_chiefHyp hG hKB hKF hP hPmax hN hKPN hsub
  obtain ⟨hblock, hKD, hPD, hgen, hcase⟩ := hch.climb hKP h66 hKF'
  rcases hcase with heq | ⟨hne, harrow, -⟩
  · exfalso
    have := hblock.subnormal
    rw [heq] at this
    exact hsub this
  · exact ⟨hblock, hKD, hPD, hgen, hne, harrow⟩

theorem le_normalizer_centralizer_inf {L N P : Subgroup G} (hPN : P ≤ N)
    (hPL : P ≤ Subgroup.normalizer (L : Set G)) :
    P ≤ Subgroup.normalizer ((centralizerModTwoCore L ⊓ N : Subgroup G) : Set G) := by
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizerModTwoCore (hPL hp)) x
  have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hPN hp)) x
  exact ⟨fun hx => ⟨h1.mp hx.1, h2.mp hx.2⟩, fun hx => ⟨h1.mpr hx.1, h2.mpr hx.2⟩⟩

theorem ef1_of_thm66F (hG : IsCharTwoType G)
    (hKP : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G) (h66 : Thm66F) {K : Subgroup G}
    (hKB : InFooteBStar K) (hKF : IsFType K) (hKF' : IsFPrimeType K) :
    ∀ N : Subgroup G, GLBIsMaxTwoLocal N → K ≤ N → IsSubnormal K N := by
  intro N₀ hN₀ hKN₀
  by_contra hsub₀
  have hK : IsFooteBlock K K := by obtain ⟨S, -, hSK⟩ := hKB.1; exact IsFooteBlock.self hSK
  obtain ⟨P, hP, hPmax⟩ := exists_maximal_ef1Class hK hN₀ hKN₀ hsub₀
  have hcl := fun {N : Subgroup G} (hN : GLBIsMaxTwoLocal N) (hKPN : K ⊔ P ≤ N)
      (hsub : ¬ IsSubnormal K N) =>
    ef1_climb hG hKP h66 hKB.1 hKF hKF' hP hPmax hN hKPN hsub
  set 𝒮 : Set (Subgroup G × Subgroup G) := {p | GLBIsMaxTwoLocal p.1 ∧ K ⊔ P ≤ p.1 ∧
    ¬ IsSubnormal K p.1 ∧ IsSylowTwoOf p.2 (centralizerModTwoCore (kClosure p.1 K) ⊓ p.1) ∧
    P ≤ Subgroup.normalizer (p.2 : Set G)} with h𝒮
  have hex : ∀ {N : Subgroup G}, GLBIsMaxTwoLocal N → K ⊔ P ≤ N → ¬ IsSubnormal K N →
      ∃ R : Subgroup G, (N, R) ∈ 𝒮 := by
    intro N hN hKPN hsub
    obtain ⟨-, -, hPD, -, -, -⟩ := hcl hN hKPN hsub
    obtain ⟨R, hR, hPR⟩ := exists_isSylowTwoOf_normalized hP.1
      (le_normalizer_centralizer_inf (le_sup_right.trans hKPN) hPD)
    exact ⟨R, hN, hKPN, hsub, hR, hPR⟩
  obtain ⟨N₁, hN₁, hKPN₁, hsub₁⟩ := hP.2.2.2
  obtain ⟨R₁, hR₁⟩ := hex hN₁ hKPN₁ hsub₁
  obtain ⟨⟨N, R⟩, hNR, hmax⟩ := Set.exists_max_image 𝒮
    (fun p => toLex (Nat.card (kClosure p.1 K), Nat.card p.2)) (Set.toFinite 𝒮) ⟨_, hR₁⟩
  obtain ⟨hN, hKPN, hsub, hR, hPR⟩ := hNR
  obtain ⟨hblock, hKD, hPD, hgen, hne, harrow⟩ := hcl hN hKPN hsub
  set L := kClosure N K with hLdef
  have hLN : L ≤ N := hblock.le
  have hLR : L ≤ Subgroup.normalizer (R : Set G) := le_normalizer_of_isSylowTwoOf hLN hR
  have hR2 : IsPGroup 2 R := hR.isPGroup
  have hO₂R : pCoreOf 2 L ≤ R := hR.le_of_normalizes
    (le_inf (pCoreOf_le_centralizerModTwoCore L)
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L).trans hLN))
    (fun c hc => mem_normalizer_pCoreOf (mem_centralizerModTwoCore_iff.mp hc.1).1)
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 L)
  have hRne : R ≠ ⊥ := by
    intro hRb
    have hU : blockU L = ⊥ := by
      rw [blockU, show blockQ L = ⊥ from le_bot_iff.mp (hRb ▸ hO₂R),
        Subgroup.commutator_bot_left]
    have hlt := hblock.chief.1
    rw [hU] at hlt
    exact not_lt_bot hlt
  have h2l : IsTwoLocal (Subgroup.normalizer (R : Set G)) := ⟨R, hRne, hR2, rfl⟩
  obtain ⟨M, hM, hRM⟩ := CFSG.LocalAnalysis.WeakClosure81.exists_isMaxTwoLocalSubgroup_le h2l
  have hLM : L ≤ M := hLR.trans hRM
  have hKPM : K ⊔ P ≤ M := sup_le (hKD.trans hLM) (hPR.trans hRM)
  have hLq := hblock.quasisimple
  have hKperf := IsFooteBlock.commutator_eq hK
  have hK2 := not_isPGroup_of_block hK
  have hsubM : ¬ IsSubnormal K M := by
    intro hKM
    have hKMb : IsFooteBlock M K :=
      ⟨hKD.trans hLM, hKM, hK.residual, hK.quasisimple, hK.chief⟩
    have hLK := le_of_isFooteBlock_of_conj hKMb hLM hLq hKperf hK2 le_rfl hKD hgen.le
    exact hne (le_antisymm hLK hKD)
  obtain ⟨hblockM, hKDM, hPDM, -, -, -⟩ := hcl hM hKPM hsubM
  have hLLM : L ≤ kClosure M K :=
    le_of_isFooteBlock_of_conj hblockM hLM hLq hKperf hK2 hKDM hKD hgen.le
  obtain ⟨R', hR'⟩ := hex hM hKPM hsubM
  have hle := hmax _ hR'
  simp only [Prod.Lex.le_iff] at hle
  have hcardL : Nat.card L ≤ Nat.card (kClosure M K) := Subgroup.card_le_of_le hLLM
  have hLeq : kClosure M K = L ∧ Nat.card R' ≤ Nat.card R := by
    rcases hle with hlt | ⟨heq, hcard⟩
    · exact absurd hlt (not_lt.mpr hcardL)
    · exact ⟨(Subgroup.eq_of_le_of_card_ge hLLM heq.le).symm, hcard⟩
  obtain ⟨hLM_eq, hRR'⟩ := hLeq
  obtain ⟨-, -, -, hR'syl, -⟩ := hR'
  rw [hLM_eq] at hR'syl hblockM
  have hRCM : R ≤ centralizerModTwoCore L ⊓ M := le_inf (hR.le.trans inf_le_left)
    ((Subgroup.le_normalizer).trans hRM)
  have hRsylM : IsSylowTwoOf R (centralizerModTwoCore L ⊓ M) := by
    refine isSylowTwoOf_of_card_eq hRCM hR2 (le_antisymm (card_le_twoPart hRCM hR2) ?_)
    rw [← hR'syl.card_eq]
    exact hRR'
  have hRsyl : IsSylowTwoOf R (centralizerModTwoCore L) := by
    obtain ⟨T, hRT, hT⟩ := exists_isSylowTwoOf_of_le (hR.le.trans inf_le_left) hR2
    rcases eq_or_lt_of_le hRT with hRT' | hlt
    · rwa [← hRT'] at hT
    · exfalso
      have hlt' := lt_inf_normalizer hlt hT.isPGroup
      have hX : T ⊓ Subgroup.normalizer (R : Set G) ≤ centralizerModTwoCore L ⊓ M :=
        le_inf (inf_le_left.trans hT.le) (inf_le_right.trans hRM)
      have := hRsylM.eq_of_le hlt'.le hX (hT.isPGroup.to_le inf_le_left)
      exact hlt'.ne this.symm
  have hLsub : IsSubnormal L (Subgroup.normalizer (R : Set G)) := by
    have := CFSG.Open.IsSubnormal.inf_of_le hblockM.subnormal hRM
    rwa [inf_eq_left.mpr hLR] at this
  have hLB : InFooteB L :=
    ⟨R, hRsyl, ⟨hLR, hLsub, hblock.residual, hblock.quasisimple, hblock.chief⟩⟩
  exact hne (hKB.2 L hLB harrow)

theorem footeFiveF_of_thm66F (h66 : Thm66F) : FooteFiveF := by
  intro G _ _ _ _ hKP hG he J hJ hJF
  obtain ⟨S, -, hSJ⟩ := hJ.1
  exact ef2 hSJ (ef1_of_thm66F hG hKP h66 hJ hJF (isFPrimeType_of_isFooteBlock he hSJ hJF))

end CFSG.CGT.Foote82
