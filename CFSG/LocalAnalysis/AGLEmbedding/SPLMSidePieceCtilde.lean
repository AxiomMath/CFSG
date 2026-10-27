module

public import CFSG.LocalAnalysis.AGLEmbedding.SPLMSidePieces
public import CFSG.LocalAnalysis.AGLEmbedding.SPLMSidePieceCtildePpd
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSP
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLK0H1Omega
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPoszAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin

namespace SPLMSide

variable {p : ℕ} {X : Type} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

theorem exists_oneLieFacts_of_not_mem [Fact p.Prime] (h : ReducedNongeneration p X R X₀)
    (hR4 : 4 ≤ Open.pRank p (R : Subgroup X)) (hX : CatalogSimpleSections X) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hKn : K.Normal) (hzK : z ∉ K) (hβ : KFactBeta)
    (hK1 : KFactOneLie) (hTor : KFactOneLieTorus) :
    IsSimpleGroup K ∧ (K ⊓ Subgroup.normalizer (((R : Subgroup X) ⊓ K : Subgroup X) : Set X) ≤
      X₀) ∧ ¬ K ≤ X₀ ∧ ∃ T : Sylow p K, (T : Subgroup K).map K.subtype = (R : Subgroup X) ⊓ K ∧
      OneLieFacts p K T ∧ ∃ n e : ℕ, OneLieTorusFacts p K T n e := by
  obtain ⟨hsimple, hnonab, hcat, hAut, T', hT'nc, -⟩ :=
    h.exists_sylow_of_not_mem hR4 hX hz hzp hK hKn hzK hβ
  obtain ⟨T, hT⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal R hKn.isSubnormal
  have hTnc : ¬ IsCyclic (T : Subgroup K) := fun hc =>
    hT'nc (isCyclic_of_surjective (Sylow.equiv T T') (MulEquiv.surjective _))
  have hnc : ¬ IsCyclic ((R : Subgroup X) ⊓ K : Subgroup X) := fun hc => hTnc (by
    rw [← hT] at hc
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective _ _ K.subtype_injective).symm (MulEquiv.surjective _))
  obtain ⟨hN, hKX₀⟩ := (h.center_eq_bot_and_rankOne_of_not_mem hz hzp hK hzK).2 hnc
  have hΓ := h.glbCore_ne_top_of_rankOne hN hKX₀ hT
  have hbig : ¬ Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 := by omega
  exact ⟨hsimple, hN _ le_rfl (fun hbot => hnc (by rw [hbot]; exact isCyclic_of_subsingleton)),
    hKX₀, T, hT, hK1 K hsimple hnonab hcat p h.prime h.ne_two T hTnc hΓ hbig,
    hTor K hsimple hnonab hcat p h.ne_two T hTnc hΓ hbig⟩

theorem eq_two_one_of_card_centerOf [Fact p.Prime] {K : Subgroup X} {T : Sylow p K} {n e : ℕ}
    (hT : (T : Subgroup K).map K.subtype = (R : Subgroup X) ⊓ K)
    (hTF : OneLieTorusFacts p K T n e)
    (h2 : Nat.card (centerOf ((R : Subgroup X) ⊓ K)) = p ^ 2) : n = 2 ∧ e = 1 := by
  obtain ⟨ψ, hψ, hψr, -⟩ := hTF.torus
  have hcard : Nat.card ((T : Subgroup K) ⊓ Subgroup.centralizer ((T : Subgroup K) : Set K) :
      Subgroup K) = p ^ n := by
    rw [← hψr, ← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv,
      Nat.card_congr Multiplicative.toAdd, GaloisField.card p n (by have := hTF.two_le; omega)]
  have hcard' : Nat.card ((T : Subgroup K) ⊓ Subgroup.centralizer ((T : Subgroup K) : Set K) :
      Subgroup K) = Nat.card (centerOf ((R : Subgroup X) ⊓ K)) := by
    rw [← hT, ← map_inf_centralizer_eq_centerOf,
      Subgroup.card_map_of_injective K.subtype_injective]
  have hn : n = 2 := Nat.pow_right_injective (Fact.out : p.Prime).two_le
    (show p ^ n = p ^ 2 by rw [← hcard, hcard', h2])
  refine ⟨hn, ?_⟩
  rcases hTF.e_cases with he | ⟨-, h3⟩
  · exact he
  · omega

omit [Finite X] in
theorem eq_of_le_of_isSimpleGroup_of_conj {K : Subgroup X} (hK : IsSimpleGroup K)
    {N : Subgroup X} (hNK : N ≤ K) (hN : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N) (hN1 : N ≠ ⊥) :
    N = K := by
  have hn : (N.subgroupOf K).Normal := ⟨fun n hn k => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hN k k.2 n hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf K) with h | h
  · exact absurd ((Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le hNK) hN1
  · exact le_antisymm hNK (Subgroup.subgroupOf_eq_top.mp h)

end SPLMSide

theorem d1SPLPieceCtilde_of (hβ : KFactBeta) (hK1 : KFactOneLie) (hTor : KFactOneLieTorus) :
    D1SPLPieceCtilde := by
  intro G _ _ p P M H R Rbar K z D P' Pbar KC hRC hRP' hP'M
  have hred := hRC.red
  have : Fact p.Prime := ⟨hred.prime⟩
  obtain ⟨hzZ, hzp⟩ := hRC.center ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ rfl
  have hzK : d1CzElt p z ∉ KC := D.outside KC hRC.comp
  obtain ⟨-, hX⟩ := D.pair P' Pbar KC hRC hRP' hP'M
  have hXC : d1LiftX p H R K ≤ Subgroup.centralizer ({z} : Set G) :=
    (d1LiftX_le p H R K).trans (D.data.le_centralizer_czElt D.czElt)
  have h2 : Nat.card (centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC)) = p ^ 2 := by
    rw [← hX]
    exact D.data.card_map_liftX D.family hXC
  obtain ⟨hsimple, hN, hKX₀, T, hT, hF, n, e, hTF⟩ := SPLMSide.exists_oneLieFacts_of_not_mem
    hred hRC.four_le_pRank hRC.catalog hzZ hzp hRC.comp hRC.normal hzK hβ hK1 hTor
  obtain ⟨rfl, rfl⟩ := SPLMSide.eq_two_one_of_card_centerOf hT hTF h2
  obtain ⟨-, hcyc, -⟩ := hred.rankOneLieAutFacts_of_not_mem hRC.four_le_pRank hRC.catalog hzZ
    hzp hRC.comp hRC.normal hzK hβ
  have hCp := SPLMSide.isPGroup_centralizer_of_isCyclic_inf hred hzZ hzp hRC.normal hcyc
  have hCc := SPLMSide.isCyclic_centralizer_of_isCyclic_inf hred hzZ hzp hRC.normal hcyc
  have hnorm := SPLMSide.conj_mem_inf_of_coatom hRC.normal hT hTF.borel_coatom hN hKX₀
  obtain ⟨hexp, hcomm, hnonab⟩ := SPLMSide.sylow_facts_of_torus hT hTF h2
  exact
    { norm := hnorm
      cent_p := fun x _ hx => SPLMSide.exists_pow_eq_one_of_commute hRC.normal hCp hT
        (SPLMSide.exists_eq_conj_of_fix_sylow hT hF hTF h2) hx
      solv := SPLMSide.isSolvable_of_conj_mem hRC.normal hCp hT hTF.borel_solvable hnorm
      rank := fun A _ hA => SPLMSide.card_le_pow_five hRC.normal hCc
        (fun E hE => by simpa using hTF.autRank E hE) hA
      exp := hexp
      comm := hcomm
      nonab := hnonab
      simple := fun N hNK hN hN1 => SPLMSide.eq_of_le_of_isSimpleGroup_of_conj hsimple hNK hN hN1
      ppd := SPLMSide.exists_ppd_of_torus hred.ne_two hT hTF hN h2 }

end CFSG.AGLEmbedding
