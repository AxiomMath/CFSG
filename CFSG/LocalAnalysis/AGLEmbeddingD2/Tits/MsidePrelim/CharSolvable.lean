module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.EscapeCover

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsidePrelim

open CFSG.LocalAnalysis.RankThreeTheoremC (D2L34BetaConf3)
open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.D2L34BetaConf3.not_isSylowTwoOf_of_isSylowTwoOf_inf
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) {T : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M)) :
    ¬ IsSylowTwoOf T H := by
  intro hTH
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  set Tbar := (T.subgroupOf H).map π with hTbar
  have hAbar9 : Nat.card ((A.subgroupOf H).map π) = 9 := by
    have := hc.almostSimple.card_A
    rw [this]
    norm_num
  obtain ⟨-, -, h8⟩ := normalizer_inf_eq_sup_of_l34 hc.l34 hc.almostSimple.normal hc.iso hc.le_K
    hAbar9 (D2L34BetaConf3.isSylowTwoOf_map hc hT)
  have hsyl := isSylowTwoOf_map_range π hTH
  rw [MonoidHom.range_eq_top_of_surjective π (QuotientGroup.mk'_surjective _)] at hsyl
  have hKn := hc.almostSimple.normal
  have hTK : Tbar ≤ Subgroup.normalizer (K : Set _) := fun x _ =>
    Subgroup.mem_normalizer_iff.mpr fun k =>
      ⟨fun hk => hKn.conj_mem k hk x, fun hk => by simpa [mul_assoc] using hKn.conj_mem _ hk x⁻¹⟩
  have hodd := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.not_two_dvd_relIndex_inf_of_normalizes
    le_top le_top hTK hsyl.2.2
  have hL : IsLinThreeFour ↥K := isLinThreeFour_of_l34Index hc.l34 hc.iso
  have hK20 : Nat.card K = 20160 := (kFactSmallThreeOrders ↥K).2.1 hL
  have h := Subgroup.relIndex_mul_card (Tbar ⊓ K) K
  rw [inf_of_le_left inf_le_right, h8, hK20] at h
  have : (Tbar ⊓ K).relIndex K = 2520 := by omega
  rw [this] at hodd
  exact hodd (by norm_num)

omit [Finite G] in
theorem isPGroup_zpowers_sup {T : Subgroup G} {x : G} (hT : IsPGroup 2 T)
    (hxN : x ∈ Subgroup.normalizer (T : Set G)) {k : ℕ} (hk : x ^ 2 ^ k = 1) :
    IsPGroup 2 (Subgroup.zpowers x ⊔ T : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) := by
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  exact IsPGroup.to_sup_of_normal_right' hx2 hT ((Subgroup.zpowers_le).mpr hxN)

theorem not_isSylowTwoOf_of_mem_normalizer {T N : Subgroup G} {x : G} (hxN : x ∈ N)
    (hxT : x ∈ Subgroup.normalizer (T : Set G)) (hx : x ∉ T) {k : ℕ} (hk : x ^ 2 ^ k = 1) :
    ¬ IsSylowTwoOf T N := by
  intro hTN
  have hSN : Subgroup.zpowers x ⊔ T ≤ N := sup_le ((Subgroup.zpowers_le).mpr hxN) hTN.1
  have hST := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.eq_of_two_group_between le_sup_right hSN
    (isPGroup_zpowers_sup hTN.2.1 hxT hk) hTN.2.2
  exact hx (hST ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers x))

theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.D2L34BetaConf3.exists_two_element
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) {T : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M)) :
    ∃ x ∈ H, x ∈ Subgroup.normalizer (T : Set G) ∧ x ∉ M ∧ ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  have hTHM : T ≤ H ⊓ M := hT.1
  have h2 : 2 ∣ ((H ⊓ M).subgroupOf H).index := by
    by_contra h
    apply D2L34BetaConf3.not_isSylowTwoOf_of_isSylowTwoOf_inf hc hT
    refine ⟨hTHM.trans inf_le_left, hT.2.1, fun hd => ?_⟩
    have := Subgroup.relIndex_mul_relIndex T (H ⊓ M) H hTHM inf_le_left
    have hd' : 2 ∣ T.relIndex (H ⊓ M) * (H ⊓ M).relIndex H := this ▸ hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd' with h1 | h1
    · exact hT.2.2 h1
    · exact h h1
  obtain ⟨x, hxH, hxN, hxHM, k, hk⟩ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.exists_mem_normalizer_not_mem_of_two_dvd_index
      inf_le_left hT h2
  exact ⟨x, hxH, hxN, fun hxM => hxHM ⟨hxH, hxM⟩, k, hk⟩

theorem D2L34BetaConf.exists_two_element
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf d P M A H R Rbar K) {T : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M)) :
    ∃ x ∈ H, x ∈ Subgroup.normalizer (T : Set G) ∧ x ∉ M ∧ ∃ k : ℕ, x ^ 2 ^ k = 1 :=
  hc.toConf3.exists_two_element hT

theorem card_eq_of_isSylowTwoOf {S S' M : Subgroup G} (hS : IsSylowTwoOf S M)
    (hS' : IsSylowTwoOf S' M) : Nat.card S = Nat.card S' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : IsPGroup 2 (S.subgroupOf M) := hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  have h1' : IsPGroup 2 (S'.subgroupOf M) :=
    hS'.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS'.1).symm
  have e1 := Sylow.card_eq_multiplicity (h1.toSylow hS.2.2)
  have e2 := Sylow.card_eq_multiplicity (h1'.toSylow hS'.2.2)
  rw [IsPGroup.toSylow_coe] at e1 e2
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv,
    ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS'.1).toEquiv, e1, e2]

theorem not_isSylowTwoOf_of_card_lt {T S N : Subgroup G} (hT : IsPGroup 2 T) (hS : IsPGroup 2 S)
    (hlt : Nat.card T < Nat.card S) (hN : Subgroup.normalizer (T : Set G) ≤ N) :
    ¬ IsSylowTwoOf T N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hTQ⟩ := hT.exists_le_sylow
  have hQS : Nat.card S ≤ Nat.card (Q : Subgroup G) := card_le_card_sylow hS Q
  have hne : T ≠ (Q : Subgroup G) := fun h => by rw [h] at hlt; omega
  obtain ⟨y, -, hyN, hyT, k, hk⟩ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.exists_normalizer_not_mem_of_two_group
      Q.isPGroup' hTQ hne
  exact not_isSylowTwoOf_of_mem_normalizer (hN hyN) hyN hyT hk

end CFSG.AGLEmbeddingD2.Tits.MsidePrelim
