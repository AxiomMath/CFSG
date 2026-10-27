module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Gen

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ABGLocalTools

section Orbit

variable {G : Type} [Group G] [Finite G]

theorem D1PhaseThree.isWeakSBlock_map_conj {p : ℕ} {P : Sylow p G} {M H R L : Subgroup G}
    (h3 : D1PhaseThree p P M H R) (hL : IsWeakSBlock M (pCoreOf 2 H) L) {k : G}
    (hk : k ∈ H ⊓ M) : IsWeakSBlock M (pCoreOf 2 H) (L.map (MulAut.conj k).toMonoidHom) := by
  have hkS : k ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    (h3.inf_eq_inf_normalizer_twoCore ▸ hk).2
  refine { toIsTwoPrimeComponent := hL.toIsTwoPrimeComponent.map_conj hk.2,
           not_le_normalizer := fun hle => hL.not_le_normalizer fun x hx => ?_ }
  have h1 : k * x * k⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hle ⟨x, hx, by simp [MulAut.conj_apply]⟩
  have e : x = k⁻¹ * (k * x * k⁻¹) * k := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hkS) h1) hkS

omit [Finite G] in
theorem blockParabolic_map_conj {M S L : Subgroup G} {k : G} (hkM : k ∈ M)
    (hkS : k ∈ Subgroup.normalizer (S : Set G)) :
    blockParabolic M S (L.map (MulAut.conj k).toMonoidHom) =
      (blockParabolic M S L).map
        (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨k, hkM⟩)).toMonoidHom := by
  have hN : (Subgroup.normalizer (S : Set G)).map (MulAut.conj k).toMonoidHom =
      Subgroup.normalizer (S : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hkS)
  have e : Subgroup.normalizer (S : Set G) ⊓ L.map (MulAut.conj k).toMonoidHom =
      (Subgroup.normalizer (S : Set G) ⊓ L).map (MulAut.conj k).toMonoidHom := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj k).injective, hN]
  show barM M _ = _
  rw [e, barM_map_conj hkM]

omit [Finite G] in
theorem barM_blockClosure_le {M K L : Subgroup G} (hKM : K ≤ M) (hL : IsTwoPrimeComponent M L)
    {T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hT : ∀ k ∈ K, barM M (L.map (MulAut.conj k).toMonoidHom) ≤ T) :
    barM M (blockClosure M K L) ≤ T := by
  refine barM_le_of_le_preimage (sup_le ?_ (iSup_le fun k => iSup_le fun hk => ?_))
  · intro q hq
    refine (mem_preM ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M) hq)).mpr ?_
    rw [(mk_eq_one_iff_coe_mem_pCoreOf _).mpr hq]
    exact T.one_mem
  · exact le_preM (hL.map_conj (hKM hk)).le (hT k hk)

theorem barM_blockClosure_le_sup_centralizer {M K L : Subgroup G} (hKM : K ≤ M)
    (hL : IsTwoPrimeComponent M L) {C : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hC : IsComponentOf C ⊤) :
    barM M (blockClosure M K L) ≤ C ⊔ Subgroup.centralizer (C : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  refine barM_blockClosure_le hKM hL fun k hk => ?_
  by_cases hCk : barM M (L.map (MulAut.conj k).toMonoidHom) = C
  · exact hCk.le.trans le_sup_left
  · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
        (hL.map_conj (hKM hk)).component hC hCk)).trans le_sup_right

theorem eq_one_of_centralizes_orbit {M K L : Subgroup G} (hKM : K ≤ M)
    (hL : IsTwoPrimeComponent M L) (hO : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥)
    {q : ↥M ⧸ CFSG.pCore 2 ↥M} (hq : q ∈ barM M (blockClosure M K L))
    (hq3 : IsPGroup 3 (Subgroup.zpowers q))
    (hqC : ∀ k ∈ K, q ∈ Subgroup.centralizer
      (barM M (L.map (MulAut.conj k).toMonoidHom) : Set (↥M ⧸ CFSG.pCore 2 ↥M))) : q = 1 := by
  have hbot := eq_bot_of_le_layer_of_centralizes hO hq3
    (Subgroup.zpowers_le.mpr (barM_blockClosure_le_layer hKM hL hq)) fun C hC => by
      rw [Subgroup.zpowers_le]
      by_cases hCo : ∃ k ∈ K, barM M (L.map (MulAut.conj k).toMonoidHom) = C
      · obtain ⟨k, hk, rfl⟩ := hCo
        exact hqC k hk
      · push Not at hCo
        refine barM_blockClosure_le hKM hL (fun k hk => ?_) hq
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
            (hL.map_conj (hKM hk)).component hC (hCo k hk))
  rw [Subgroup.zpowers_eq_bot] at hbot
  exact hbot

end Orbit

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ABGLocalTools

section Bounds

variable {G : Type} [Group G] [Finite G]

theorem D1PhaseThree.relIndex_centralizer_dvd {p : ℕ} {P : Sylow p G} {M H R L : Subgroup G}
    (h3 : D1PhaseThree p P M H R) (h84 : Asc81bEightFour) (h86 : Asc81bEightSix)
    (hD2 : D1NoXBlock) (hb : StmtBlockInnerNormalizer) (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    {I : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hI : I ≤ barM M ((H ⊓ M) ⊓ blockClosure M (H ⊓ M) L)) {k : G} (hk : k ∈ H ⊓ M) :
    (Subgroup.centralizer (barM M (L.map (MulAut.conj k).toMonoidHom) :
      Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex I ∣
      Nat.card (blockParabolic M (pCoreOf 2 H) L) := by
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  have hkS : k ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := (hKeq ▸ hk).2
  have hLk := h3.isWeakSBlock_map_conj hL hk
  set Lbk := barM M (L.map (MulAut.conj k).toMonoidHom) with hLbk
  have hLbkc : IsComponentOf Lbk ⊤ := hLk.component
  have hIE : I ≤ barM M (blockClosure M (H ⊓ M) L) :=
    hI.trans (Subgroup.map_mono (Subgroup.comap_mono inf_le_right))
  have hIN : I ≤ Subgroup.normalizer (Lbk : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    (hIE.trans (barM_blockClosure_le_layer inf_le_right hL.toIsTwoPrimeComponent)).trans
      (layer_le_normalizer_component hLbkc)
  have hJN : blockParabolic M (pCoreOf 2 H) (L.map (MulAut.conj k).toMonoidHom) ≤
      Subgroup.normalizer (Lbk : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    (blockParabolic_le_barM' _ _ _).trans Subgroup.le_normalizer
  have hPiS : (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L ≤
      Subgroup.normalizer (pCoreOf 2 H : Set G) := fun x hx => (hKeq ▸ hx.1).2
  have hdvd := relIndex_dvd_of_inner hIN hJN fun x hx =>
    h3.exists_mem_blockParabolic h84 h86 hD2 hb hLk
      (Subgroup.map_mono (Subgroup.comap_mono hPiS) (hI hx))
      (barM_blockClosure_le_sup_centralizer inf_le_right hL.toIsTwoPrimeComponent hLbkc
        (hIE hx))
  rw [blockParabolic_map_conj hk.2 hkS,
    Subgroup.card_map_of_injective (MulAut.conj _).injective] at hdvd
  exact hdvd

theorem relIndex_dvd_sylow {Y : Type*} [Group Y] [Finite Y] {I C J : Subgroup Y}
    (hI3 : IsPGroup 3 I) (hdvd : C.relIndex I ∣ Nat.card J) (Q : Sylow 3 J) :
    C.relIndex I ∣ Nat.card (Q : Subgroup J) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := hI3.exists_card_eq
  have h1 : C.relIndex I ∣ 3 ^ a := ha ▸ Subgroup.relIndex_dvd_card C I
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
  rw [hb] at hdvd ⊢
  exact Q.pow_dvd_card_of_pow_dvd_card hdvd

theorem card_sup_of_le_centralizer_component {Y : Type*} [Group Y] [Finite Y]
    (hO : CFSG.pCore 3 Y = ⊥) {C B B₂ : Subgroup Y} (hC : IsComponentOf C ⊤) (hB₂C : B₂ ≤ C)
    (hB₂3 : IsPGroup 3 B₂) (hBC : B ≤ Subgroup.centralizer (C : Set Y)) :
    Nat.card (B ⊔ B₂ : Subgroup Y) = Nat.card B * Nat.card B₂ := by
  refine card_sup_of_commute (hBC.trans (Subgroup.centralizer_le hB₂C)) ?_
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  exact eq_one_of_mem_center_component hO hC (hB₂C hx.2) (hBC hx.1)
    (hB₂3.to_le (Subgroup.zpowers_le.mpr hx.2))

end Bounds

end CFSG.AGLEmbedding
