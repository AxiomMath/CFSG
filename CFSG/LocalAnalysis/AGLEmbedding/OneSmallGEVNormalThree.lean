module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormal
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeKFacts
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroAb
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeFusion
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeInner
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeMain
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosT
import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.ComponentInitial

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem isAltTwoP_of_isSmallLinTwo_three {L : Type} [Group L] (h : IsSmallLinTwo 3 L) :
    IsAltTwoP 3 L := by
  obtain ⟨d, hd, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e₁⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 3 2) = 9 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 3 2 (by norm_num)]
    norm_num
  obtain ⟨e₂⟩ :=
    unique_field_nine_projective_linear_alternating_six_isomorphism (GaloisField 3 2) hcard
  exact ⟨e.trans (e₁.trans e₂)⟩

theorem D1OneSmallData.exists_conj_eq_inv (hOrb : KFactSmallOrbits)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hdec : ∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i) (hp3 : p = 3)
    (hA6 : ¬ IsAltTwoP 3 K)
    (hcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup _) = p ^ 2) :
    ∀ t ∈ d1LiftX p H R K, t ≠ 1 → ∃ n ∈ M, n * z * n⁻¹ = z ∧ n * t * n⁻¹ = t⁻¹ := by
  intro t ht ht1
  set T := d1LiftX p H R K with hT
  set Orb : Set G := {s | s ∈ T ∧ s ≠ 1 ∧ ∃ n ∈ Subgroup.normalizer (R : Set G),
    n * z * n⁻¹ = z ∧ (∀ x ∈ T, n * x * n⁻¹ ∈ T) ∧ n * t * n⁻¹ = s} with hOrbDef
  have hinv : D1InvSubset p H R K z Orb := by
    refine ⟨fun s hs => ⟨hs.1, hs.2.1⟩, fun m hm hmz hmT s hs => ?_⟩
    obtain ⟨hsT, hs1, n, hn, hnz, hnT, hnt⟩ := hs
    refine ⟨hmT s hsT, fun h1 => hs1 ?_, m * n, Subgroup.mul_mem _ hm hn, ?_, ?_, ?_⟩
    · calc s = m⁻¹ * (m * s * m⁻¹) * m := by group
        _ = 1 := by rw [h1]; group
    · calc m * n * z * (m * n)⁻¹ = m * (n * z * n⁻¹) * m⁻¹ := by group
        _ = z := by rw [hnz, hmz]
    · intro x hx
      have := hmT _ (hnT x hx)
      have e : m * n * x * (m * n)⁻¹ = m * (n * x * n⁻¹) * m⁻¹ := by group
      rw [e]
      exact this
    · rw [← hnt]; group
  have htOrb : t ∈ Orb := ⟨ht, ht1, 1, Subgroup.one_mem _, by group, fun x hx => by simpa using hx,
    by group⟩
  have hT1 : ((T : Set G) \ {1}).ncard = p ^ 2 - 1 := by
    obtain ⟨-, hTc⟩ := hd.d1LiftX_facts hz
    rw [Set.ncard_sdiff_singleton_of_mem T.one_mem, ← Nat.card_coe_set_eq]
    exact congrArg (· - 1) (hTc.trans hcard)
  have hsize : Orb.ncard = p ^ 2 - 1 := by
    rcases hd.orbit_sizes hOrb hz hdec (fun h => by omega) hcard with h | ⟨-, h5, -⟩ | ⟨hA, -⟩
    · rcases h Orb hinv with h0 | h8
      · exact absurd ((Set.ncard_eq_zero (Set.toFinite _)).mp h0 ▸ htOrb) (Set.notMem_empty t)
      · exact h8
    · omega
    · exact absurd (hp3 ▸ hA) hA6
  have heq := Set.eq_of_subset_of_ncard_le hinv.1 (by rw [hsize, hT1])
  have hti : t⁻¹ ∈ Orb := heq ▸ ⟨T.inv_mem ht, fun h1 => ht1 (inv_eq_one.mp h1)⟩
  obtain ⟨-, -, n, hn, hnz, -, hnt⟩ := hti
  exact ⟨n, hd.cfg.ext.normalizer_le hn, hnz, hnt⟩

theorem d1SmallGEVNormalThree_of (hUP : KFactUPrimeSmall) (hSch : KFactCatalogSchreier)
    (hΓ : KFactSmallGammaSolvableSpor) (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp)
    (hOrb : KFactSmallOrbits) (hSh3 : KFactSmallSylowShapeThree) (hK : CitedBlockToralThree)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) : D1SmallGEVNormalThree := by
  intro G _ _ p P M H R Rbar K hd z hz hI hB0 _ _ hA6 hU3 hL _ _ _ hCz _ _ hp3
  subst hp3
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hF : ¬ (3 = 5 ∧ IsFi22 K) := fun h => absurd h.1 (by norm_num)
  have hA6' : ¬ IsAltTwoP 3 K := fun h => hA6 ⟨rfl, h⟩
  have hU3' : ¬ IsSmallUnitary 3 K := fun h => hU3 ⟨rfl, h⟩
  have hL34 : ¬ IsLinThreeFour K := fun h => hL ⟨rfl, h⟩
  have h3 := hd.toPhaseThree hUP hL hF
  obtain ⟨T₁, hT₁, hs, hn, hc, hTnc, hΓT, -⟩ := hd.exists_sylow
  have hUPK := hUP K hs hn hc 3 hp hp2 T₁ hTnc hΓT hd.small hL hF
  have hsolv := hΓ K hs hn hc 3 hp hp2 T₁ hTnc hΓT hd.small
    (fun h => hA6' (isAltTwoP_of_isSmallLinTwo_three h)) hU3' hA6' hL hF
  have hperf : ∀ Y : Subgroup G, Y ≤ H ⊓ M → ⁅Y, Y⁆ = Y → Nat.Coprime 3 (Nat.card Y) :=
    fun Y hY hYp => hd.coprime_card_of_perfect hI hT₁ hUPK (hSch K hs hn hc) hsolv hY hYp
  have hcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K :
      Subgroup _) = 3 ^ 2 := by
    rw [← hT₁, Subgroup.card_map_of_injective K.subtype_injective,
      hSh3 K hs hn hc T₁ hTnc hΓT hd.small hU3']
  have hfus := hd.mem_fusionSet_of_not_mem hOut hExp hOrb hz hB0 rfl hA6' hL34 hcard
  obtain ⟨hdec, hexpR⟩ := hd.decomp_exp_of_b0 hOut hExp hz hB0 hL
  have hinv := hd.exists_conj_eq_inv hOrb hz hdec rfl hA6' hcard
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := hd.le_centralizer_czElt hz
  have hRz : ∀ r ∈ R, z * r = r * z := fun r hr =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hRC hr)).symm
  have hsyl := exists_sylow_inf_of_sylow hB0 h3.le_M
  obtain ⟨E, hER, hEel, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 hp R
  rw [hd.pRank_R] at hEcard
  exact h3.false_of_toral_three rfl h84 h85 h86 h93 hD2 hK hperf hz.1 hz.2.1 hCz hsyl
    (hd.d1LiftX_facts hz).1 hRz hexpR hfus hinv ⟨E, hER, hEel, hEcard⟩

end CFSG.AGLEmbedding
