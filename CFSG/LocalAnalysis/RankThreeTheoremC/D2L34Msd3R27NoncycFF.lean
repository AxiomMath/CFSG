module

import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFH0Consumer
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.FFH0Final
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5Baum
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFConstrained
public import CFSG.Quasithin.Background.C118NoOuter

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsidePrelim

variable {G : Type} [Group G] [Finite G]

theorem exists_ffPairData_of_subgroup {N T : Subgroup G} (hF : CharTwo N)
    (hT : IsSylowTwoOf T N) (hs : Group.IsSolvable ↥N) (hT1 : T ≠ ⊥)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) N : Set G))
    (hX : ∀ Y : Subgroup G, Y ≤ N → IsSubnormal Y N → InClassXBlock Y → False) :
    ∃ (hU : IsElemAbelian 2 (conjClosure (quasithinOmegaOneCenter T) N))
      (I : Finset (Subgroup (MulAut (IntMod (conjClosure (quasithinOmegaOneCenter T) N) hU))))
      (C₁ C₂ : Subgroup G),
      N ≤ Subgroup.normalizer ((conjClosure (quasithinOmegaOneCenter T) N : Subgroup G) :
        Set G) ∧ S3Family I ∧ (∀ L ∈ I, Nat.card L = 6) ∧
      IsSylowTwoOf (autI hU (baum T)) (autI hU (thompsonJ N)) ∧
      autI hU (thompsonJ N) = ⨆ L ∈ I, L ∧ FFPairData N T hU I C₁ C₂ := by
  set V := conjClosure (quasithinOmegaOneCenter T) N with hV
  obtain ⟨hle, -, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)
  have hsAut : Group.IsSolvable ↥(autOn N V) :=
    Group.isSolvable_of_surjective (actOnAutOn_surjective hred.2.1)
  obtain ⟨hU, hMN, I, -, hcard, hJM, hSyl, hperm, hI⟩ :=
    exists_family_of_ffConclusion hT hJ (ffConclusion_of_solvable hF hsAut hT hV hJ)
  have hVT : V ≤ T := hle.trans (inf_le_left.trans (B6.pCoreOf_two_le_of_isSylowTwoOf hT))
  have hVN : V ≤ N := hle.trans (inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 N))
  have hBS : autI hU (baum T) ≤ autI hU (thompsonJ N) :=
    autI_baum_le_autI_thompsonJ hMN hT hVT hI hJM (thompsonJ_le_thompsonJ_of_isSylowTwoOf hT)
      hperm
  have hSylB : IsSylowTwoOf (autI hU (baum T)) (autI hU (thompsonJ N)) :=
    isSylowTwoOf_of_le_of_le hSyl (autI_mono hU (thompsonJ_le_baum T)) hBS
      (isPGroup_autI hU (hT.2.1.to_le (C1GN.baum_le T)))
  have hctx : FFCtx N T V hU hMN I := ⟨hVN, rfl, hT, hF, hcard, hJM, hSyl, hperm, hI, hBS⟩
  obtain ⟨C₁, C₂, h1, h1Z, h1char, h2, h2B, h2char, hall⟩ := theoremC118 G T hT.2.1 hT1
  have hZV : quasithinOmegaOneCenter T ≤ V := le_conjClosure _ N
  have hC₁T : C₁ ≤ T := h1Z.trans (C1GN.omegaOneCenterOf_le_self T)
  have hC₁B : C₁ ≤ baum T := h1Z.trans (C1GN.omegaOneCenterOf_le_baum T)
  refine ⟨hU, I, C₁, C₂, hMN, hI, hcard, hSylB, hJM, h1, hT.2.1.to_le hC₁T, h2,
    hT.2.1.to_le (h2B.trans (C1GN.baum_le T)), ?_, ?_, ?_, ?_, ?_⟩
  · exact normalizer_le_normalizer_of_characteristic_subgroupOf hC₁T h1char
  · exact (normalizer_le_normalizer_baum T).trans
      (normalizer_le_normalizer_of_characteristic_subgroupOf h2B h2char)
  · intro x hx
    have hxc : ∀ c ∈ C₁, c * x = x * c := fun c hc =>
      Subgroup.mem_centralizer_iff.1 hx.1 c (hZV (h1Z hc))
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 hxc)
  · exact fun x hx => normalizer_le_normalizer_of_characteristic_subgroupOf h2B h2char hx.2
  · intro L hL
    obtain ⟨H₀, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ :=
      FFH0Hyp.exists_H₀ invariantCyclicSupplement ⟨hF, hT, hle, hI, hcard, hJM, hSyl, hperm, hL⟩
        hMN
    obtain ⟨hHN, hHL, hH3, hGcl, hblock⟩ := FFH0Spec.conclusion hctx hL
      (⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ : FFH0Spec N T V hU L H₀)
    refine ⟨H₀, hHN, hHL, hH3, ?_⟩
    have hd := hall G H₀ (baum T).subtype (baum T).subtype_injective
      (by rwa [Subgroup.range_subtype])
    rw [Subgroup.map_subgroupOf_eq_of_le hC₁B, Subgroup.map_subgroupOf_eq_of_le h2B] at hd
    rcases hd with h | h | h
    · left
      intro x hx
      have hxc : ∀ c ∈ C₁, c * x = x * c := fun c hc =>
        ((Subgroup.mem_centralizer_iff.1 (h hc).2 x hx)).symm
      exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 hxc)
    · exact Or.inr h
    · obtain ⟨Y, hYN, hYs, hYX⟩ := hblock h
      exact (hX Y hYN hYs hYX).elim

theorem exists_factorization_of_pairData_of_bound {V N T : Subgroup G} {hU : IsElemAbelian 2 V}
    (hT : IsSylowTwoOf T N) (hNV : N ≤ Subgroup.normalizer (V : Set G))
    {I : Finset (Subgroup (MulAut (IntMod V hU)))} (hI : S3Family I)
    (hcard : ∀ L ∈ I, Nat.card L = 6)
    (hSylJ : IsSylowTwoOf (autI hU (baum T)) (autI hU (thompsonJ N)))
    (hJN : autI hU (thompsonJ N) = ⨆ L ∈ I, L) {C₁ C₂ : Subgroup G}
    (hdat : FFPairData N T hU I C₁ C₂) {D : Subgroup G}
    (hDC : D ≤ Subgroup.centralizer (V : Set G) ⊓ N) (hDp : IsPGroup 3 D) (hDc : ¬ IsCyclic D)
    (hbound : ∀ Q : Subgroup G, Q ≤ N ⊓ Subgroup.normalizer (C₁ : Set G) → IsPGroup 3 Q →
      D ≤ Q → Nat.card Q ≤ 9) :
    ∃ B : Subgroup G, B ≤ N ∧ B ≤ Subgroup.normalizer (C₂ : Set G) ∧
      ∀ n ∈ N, ∃ c ∈ Subgroup.centralizer (V : Set G) ⊓ N, ∃ b ∈ B, n = c * b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, -, -, -, -, hCN₁, hJ₂, hH⟩ := hdat
  set CN : Subgroup G := Subgroup.centralizer (V : Set G) ⊓ N with hCN
  choose! Hf hHN hHL hH3 hHcase using hH
  have hnoA : ∀ L ∈ I, ¬ Hf L ≤ Subgroup.normalizer (C₁ : Set G) := by
    intro L hL hLA
    set 𝒜 : Subgroup G := CN ⊔ Hf L with h𝒜
    have h𝒜N : 𝒜 ≤ N := sup_le inf_le_right (hHN L hL)
    have h𝒜C : 𝒜 ≤ Subgroup.normalizer (C₁ : Set G) := sup_le hCN₁ hLA
    have hcardA := card_eq_card_autI_mul (hU := hU) hNV (𝒜 := 𝒜) le_sup_left h𝒜N
    have h3 : 3 ∣ Nat.card (autI hU 𝒜) := by
      have hLle : L ≤ autI hU 𝒜 := (hHL L hL).trans (autI_mono hU le_sup_right)
      have := Subgroup.card_dvd_of_le hLle
      rw [hcard L hL] at this
      exact (show 3 ∣ 6 by norm_num).trans this
    have h9 : 9 ∣ Nat.card CN :=
      (nine_dvd_card_of_not_isCyclic hDp hDc).trans (Subgroup.card_dvd_of_le hDC)
    have h27 : 3 ^ 3 ∣ Nat.card 𝒜 := by
      rw [hcardA]
      exact (show 3 ^ 3 = 3 * 9 by norm_num) ▸ Nat.mul_dvd_mul h3 h9
    have hDA : D ≤ 𝒜 := hDC.trans le_sup_left
    have hDp' : IsPGroup 3 (D.subgroupOf 𝒜) :=
      hDp.of_equiv (Subgroup.subgroupOfEquivOfLe hDA).symm
    obtain ⟨Q', hDQ'⟩ := hDp'.exists_le_sylow
    set Q : Subgroup G := (Q' : Subgroup ↥𝒜).map 𝒜.subtype with hQ
    have hQp : IsPGroup 3 Q := Q'.isPGroup'.map 𝒜.subtype
    have hQ𝒜 : Q ≤ 𝒜 := Subgroup.map_subtype_le _
    have hDQ : D ≤ Q := fun x hx => ⟨⟨x, hDA hx⟩, hDQ' (Subgroup.mem_subgroupOf.2 hx), rfl⟩
    have hQcard : 3 ^ 3 ∣ Nat.card Q := by
      have := Sylow.pow_dvd_card_of_pow_dvd_card (n := 3) Q' h27
      rwa [Nat.card_congr (Subgroup.equivMapOfInjective _ 𝒜.subtype 𝒜.subtype_injective).toEquiv]
        at this
    have hQ9 := hbound Q (le_inf (hQ𝒜.trans h𝒜N) (hQ𝒜.trans h𝒜C)) hQp hDQ
    have := Nat.le_of_dvd Nat.card_pos hQcard
    omega
  have hB : ∀ L ∈ I, Hf L ≤ Subgroup.normalizer (C₂ : Set G) := fun L hL =>
    (hHcase L hL).resolve_left (hnoA L hL)
  set KB : Subgroup G := ⨆ L ∈ I, Hf L with hKB
  have hKBN : KB ≤ N := iSup₂_le fun L hL => hHN L hL
  have hKBC : KB ≤ Subgroup.normalizer (C₂ : Set G) := iSup₂_le fun L hL => hB L hL
  have hcov : ∀ L ∈ I, L ≤ autI hU (⊥ : Subgroup G) ∨ L ≤ autI hU KB := fun L hL =>
    Or.inr ((hHL L hL).trans (autI_mono hU (le_iSup₂ (f := fun L (_ : L ∈ I) => Hf L) L hL)))
  refine ⟨KB ⊔ (N ⊓ Subgroup.normalizer (baum T : Set G)), sup_le hKBN inf_le_left,
    sup_le hKBC hJ₂, fun m hm => ?_⟩
  obtain ⟨c, hc', a, ha, b, hb, n, hn, rfl⟩ := exists_factor_of_covering hNV hT (C1GN.baum_le T)
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T))
    (normalizer_inf_sup_le_normalizer_baum T _) hI hSylJ hJN
    (bot_le : (⊥ : Subgroup G) ≤ N) hKBN hcov m hm
  rw [Subgroup.mem_bot] at ha
  subst ha
  exact ⟨c, hc', b * n, Subgroup.mul_mem _ (Subgroup.mem_sup_left hb)
    (Subgroup.mem_sup_right hn), by group⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
