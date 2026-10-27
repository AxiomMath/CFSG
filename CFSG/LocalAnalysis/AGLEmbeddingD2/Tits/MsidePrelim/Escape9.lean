module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.SylowPermute
public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34BetaCoreFree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.NormalizerTransitive

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

variable {G : Type} [Group G] [Finite G] [D2Amb3 G]
variable {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D2L34BetaConf3.exists_escape_of_not_isCyclic (hc : D2L34BetaConf3 d P M A H R Rbar K)
    (hstr : GLBStronglyEmbedded 3 M) {N : Subgroup G} (hN : IsTwoLocal N) (hNM : ¬ N ≤ M)
    {X : Subgroup G} (hXN : X ≤ N) (hXM : X ≤ M) (hX : IsPGroup 3 X) (hXc : ¬ IsCyclic X) :
    ∃ N₁ E₀ : Subgroup G, N ≤ N₁ ∧ X ≤ E₀ ∧ D2Escape 3 P M E₀ N₁ E₀ ∧
      D2EscapeMax 3 P M E₀ ∧ Nat.card E₀ = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨N₁, hNN₁, hN₁⟩ := exists_maximal_twoLocal hN
  have hN₁M : ¬ N₁ ≤ M := fun h => hNM (hNN₁.trans h)
  have hXN₁ : X ≤ N₁ := hXN.trans hNN₁
  have hXp : IsPGroup 3 (X.subgroupOf N₁) := hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXN₁).symm
  obtain ⟨T, hXT⟩ := hXp.exists_le_sylow
  set E₀ : Subgroup G := (T : Subgroup N₁).map N₁.subtype with hE₀
  have hXE₀ : X ≤ E₀ := fun x hx => ⟨⟨x, hXN₁ hx⟩, hXT (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hE₀p : IsPGroup 3 E₀ := T.isPGroup'.map N₁.subtype
  have hXne : X ≠ ⊥ := fun h => hXc (h ▸ isCyclic_of_subsingleton ..)
  have hE₀M : E₀ ≤ M := le_of_stronglyEmbedded_of_inf_ne_bot Nat.prime_three hstr hE₀p
    fun h => hXne (le_bot_iff.mp (h ▸ le_inf hXE₀ hXM))
  have hE₀N₁ : E₀ ≤ N₁ := Subgroup.map_subtype_le _
  have hTc : ¬ IsCyclic (T : Subgroup N₁) := by
    intro hcyc
    apply hXc
    have hE₀c : IsCyclic E₀ :=
      isCyclic_of_surjective (Subgroup.equivMapOfInjective _ _ N₁.subtype_injective).toMonoidHom
        (Subgroup.equivMapOfInjective _ _ N₁.subtype_injective).surjective
    have hXsub : IsCyclic (X.subgroupOf E₀) := Subgroup.isCyclic _
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hXE₀).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hXE₀).surjective
  have : Fact (IsPGroup 3 (T : Subgroup N₁)) := ⟨T.isPGroup'⟩
  obtain ⟨E, -, hEc, hEel⟩ :=
    CFSG.lemma_4_5_a (R := (T : Subgroup N₁)) (p := 3) (by norm_num) hTc
  set E' : Subgroup G := (E.map (T : Subgroup N₁).subtype).map N₁.subtype with hE'
  have hE'el : IsElemAbelian 3 E' :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3
      (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3
        ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).mp hEel) _) _
  have hE'c : Nat.card E' = 3 ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective N₁.subtype_injective,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hEc]
  have hE'E₀ : E' ≤ E₀ := Subgroup.map_mono (Subgroup.map_subtype_le E)
  have hrank₀ : Open.pRank 3 (N₁ ⊓ M) ≤ 2 := by
    by_contra hlt
    exact hN₁M (D2Amb3.d1 (G := G) P M hc.esc.maxTwoLocal_M
      ((weakCore_le_fullCore 3 (P : Subgroup G)).trans hc.esc.core_le) N₁ hN₁.1 (by omega))
  have hE'rank : 2 ≤ Open.pRank 3 E' := le_pRank_of_isElemAbelian Nat.prime_three hE'el hE'c
  have hesc' : D2Escape 3 P M E' N₁ E₀ :=
    { prime := Nat.prime_three
      ne_two := by norm_num
      sylow_le := hc.esc.sylow_le
      core_le := hc.esc.core_le
      maxTwoLocal_M := hc.esc.maxTwoLocal_M
      maxTwoLocal_H := hN₁
      elem := hE'el
      card_A := hE'c
      core_A := glbCore_one_le_of_stronglyEmbedded Nat.prime_three hstr (hE₀p.to_le hE'E₀)
        (hE'E₀.trans hE₀M)
      A_le := hE'E₀
      le_H := hE₀N₁
      le_M := hE₀M
      isSylow := ⟨T, rfl⟩
      pRank_eq := le_antisymm
        ((pRank_mono 3 Nat.prime_three (le_inf hE₀N₁ hE₀M)).trans hrank₀)
        (hE'rank.trans (pRank_mono 3 Nat.prime_three hE'E₀))
      not_le := hN₁M }
  have hR9 := hc.card_R_eq_nine hstr
  have hE₀9 : Nat.card E₀ = 9 := by
    refine le_antisymm (hR9 ▸ hc.max E' N₁ E₀ hesc') ?_
    have := Subgroup.card_le_of_le hE'E₀
    rw [hE'c] at this
    omega
  have hE'eq : E' = E₀ := Subgroup.eq_of_le_of_card_ge hE'E₀ (by rw [hE₀9, hE'c]; norm_num)
  have hmax₀ : D2EscapeMax 3 P M E₀ := fun A' H' R' h' =>
    (hc.max A' H' R' h').trans (by rw [hR9, hE₀9])
  refine ⟨N₁, E₀, hNN₁, hXE₀, ?_, hmax₀, hE₀9⟩
  rw [← hE'eq] at hesc' ⊢
  exact hesc'

theorem D2L34BetaConf3.card_le_nine_of_not_isCyclic (hc : D2L34BetaConf3 d P M A H R Rbar K)
    (hstr : GLBStronglyEmbedded 3 M) {N : Subgroup G} (hN : IsTwoLocal N) (hNM : ¬ N ≤ M)
    {X : Subgroup G} (hXN : X ≤ N) (hXM : X ≤ M) (hX : IsPGroup 3 X) (hXc : ¬ IsCyclic X) :
    Nat.card X ≤ 9 := by
  obtain ⟨N₁, E₀, -, hXE₀, -, -, hE₀9⟩ :=
    D2L34BetaConf3.exists_escape_of_not_isCyclic hc hstr hN hNM hXN hXM hX hXc
  exact hE₀9 ▸ Subgroup.card_le_of_le hXE₀

theorem exists_conj_eq_of_escape (hOnly : D2OnlyL34At P M) {N X : Subgroup G}
    (hX : IsPGroup 3 X) (hXc : ¬ IsCyclic X)
    (hesc : ∃ N₁ E₀ : Subgroup G, N ≤ N₁ ∧ X ≤ E₀ ∧ D2Escape 3 P M E₀ N₁ E₀ ∧
      D2EscapeMax 3 P M E₀ ∧ Nat.card E₀ = 9)
    (hNX : Subgroup.normalizer (X : Set G) ≤ M) :
    IsElemAbelian 3 X ∧ Nat.card X = 9 ∧ ∀ x ∈ X, x ≠ 1 → ∀ y ∈ X, y ≠ 1 →
      ∃ n ∈ M ⊓ Subgroup.normalizer (X : Set G), n * x * n⁻¹ = y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨N₁, E₀, hNN₁, hXE₀, hesc₀, hmax₀, hE₀9⟩ := hesc
  have hXne : X ≠ ⊥ := fun h => hXc (h ▸ isCyclic_of_subsingleton ..)
  have hX9 : 9 ≤ Nat.card X := by
    obtain ⟨k, hk⟩ := hX.exists_card_eq
    rcases k with _ | _ | k
    · exact absurd (Subgroup.eq_bot_of_card_eq X (by simpa using hk)) hXne
    · exact absurd (isCyclic_of_prime_card (p := 3) (by simpa using hk)) hXc
    · rw [hk]
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hXeq : X = E₀ := Subgroup.eq_of_le_of_card_ge hXE₀ (by rw [hE₀9]; exact hX9)
  subst hXeq
  refine ⟨hesc₀.elem, hE₀9, ?_⟩
  obtain ⟨Rbar₀, K₀, hRbar₀, hK₀⟩ := hesc₀.almostSimple (D2Amb3.glob (G := G))
  obtain ⟨d₀, hd₀, hi⟩ := hOnly X N₁ X hesc₀ hmax₀ Rbar₀ K₀ hRbar₀ hK₀
  have := hK₀.normal
  have hK₀c : Nat.card K₀ = 20160 :=
    (kFactSmallThreeOrders K₀).2.1 (isLinThreeFour_of_l34Index hd₀ hi)
  have hXN₁ : X ≤ N₁ := hesc₀.le_H
  have hXp' : IsPGroup 3 (X.subgroupOf N₁) := hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXN₁).symm
  have hRb : Nat.card (Rbar₀ : Subgroup (N₁ ⧸ primeComplementCore (G := N₁) 3)) = 3 ^ 2 := by
    rw [hRbar₀, card_map_mk_of_isPGroup Nat.prime_three _ (primeComplementCore_coprime 3) hXp',
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXN₁).toEquiv, hE₀9]
    norm_num
  have hfac : (Nat.card (N₁ ⧸ primeComplementCore (G := N₁) 3)).factorization 3 = 2 := by
    have h1 := Rbar₀.card_eq_multiplicity
    rw [hRb] at h1
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1).symm
  have hidx3 : ¬ 3 ∣ K₀.index := by
    intro h3
    have hmul := K₀.index_mul_card
    rw [hK₀c] at hmul
    have hidx0 : K₀.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h2 : (K₀.index * 20160).factorization 3 = 2 := by rw [hmul, hfac]
    rw [Nat.factorization_mul hidx0 (by norm_num), Finsupp.add_apply,
      factorization_20160_three] at h2
    have h1 := (Nat.prime_three.dvd_iff_one_le_factorization hidx0).mp h3
    omega
  have hAK₀ : (X.subgroupOf N₁).map (QuotientGroup.mk' (primeComplementCore (G := N₁) 3)) ≤ K₀ := by
    rw [← hRbar₀]
    exact le_of_isPGroup_of_not_dvd_index Nat.prime_three hidx3 Rbar₀.isPGroup'
  have htr := hesc₀.exists_conj_eq_of_l34 hd₀ hi hAK₀
  obtain ⟨T, hT⟩ := hesc₀.isSylow
  have hidxX : ¬ 3 ∣ (X.subgroupOf N₁).index := by
    have : X.subgroupOf N₁ = (T : Subgroup N₁) := by
      rw [← hT, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective N₁.subtype_injective]
    rw [this]
    exact T.not_dvd_index
  intro x hx hx1 y hy hy1
  obtain ⟨g, hgN₁, hg⟩ := htr x hx hx1 y hy hy1
  set σ := N₁ ⊓ Subgroup.centralizer ({y} : Set G) with hσ
  have hXc' : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hesc₀.elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hXσ : X ≤ σ := fun a ha =>
    ⟨hXN₁ ha, Subgroup.mem_centralizer_singleton_iff.mpr (hXc' y hy a ha).symm⟩
  have hXgσ : X.map (MulAut.conj g).toMonoidHom ≤ σ := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨N₁.mul_mem (N₁.mul_mem hgN₁ (hXN₁ ha)) (N₁.inv_mem hgN₁), ?_⟩
    show g * a * g⁻¹ ∈ Subgroup.centralizer ({y} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [← hg]
    have hax := hXc' x hx a ha
    calc g * a * g⁻¹ * (g * x * g⁻¹) = g * (a * x) * g⁻¹ := by group
      _ = g * (x * a) * g⁻¹ := by rw [hax]
      _ = g * x * g⁻¹ * (g * a * g⁻¹) := by group
  have hσN₁ : σ ≤ N₁ := inf_le_left
  have hσc : Nat.card σ = 3 ^ 2 * X.relIndex σ := by
    have h := Subgroup.relIndex_mul_card X σ
    rw [inf_of_le_left hXσ, hE₀9] at h
    rw [← h]
    ring
  have hσ3 : ¬ 3 ∣ X.relIndex σ := by
    intro h3
    apply hidxX
    have := Subgroup.relIndex_mul_relIndex X σ N₁ hXσ hσN₁
    exact h3.trans ⟨_, this.symm⟩
  obtain ⟨c, hcσ, hcX⟩ := exists_conj_map_eq_of_card (p := 3) (n := 2) hXgσ hXσ
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hE₀9]; norm_num)
    (by rw [hE₀9]; norm_num) hσc hσ3
  refine ⟨c * g, ⟨?_, ?_⟩, ?_⟩
  ·
    have hn : c * g ∈ Subgroup.normalizer (X : Set G) := by
      apply mem_normalizer_of_map_conj_eq_self
      rw [map_conj_mul', hcX]
    exact hNX hn
  · apply mem_normalizer_of_map_conj_eq_self
    rw [map_conj_mul', hcX]
  · have hcy : c * y = y * c := Subgroup.mem_centralizer_singleton_iff.mp hcσ.2
    calc c * g * x * (c * g)⁻¹ = c * (g * x * g⁻¹) * c⁻¹ := by group
      _ = c * y * c⁻¹ := by rw [hg]
      _ = y := by rw [hcy]; group

theorem D2L34BetaConf3.exists_conj_eq_of_not_isCyclic (hc : D2L34BetaConf3 d P M A H R Rbar K)
    (hstr : GLBStronglyEmbedded 3 M) (hOnly : D2OnlyL34At P M) {N : Subgroup G}
    (hN : IsTwoLocal N) (hNM : ¬ N ≤ M) {X : Subgroup G} (hXN : X ≤ N) (hXM : X ≤ M)
    (hX : IsPGroup 3 X) (hXc : ¬ IsCyclic X) :
    IsElemAbelian 3 X ∧ Nat.card X = 9 ∧ ∀ x ∈ X, x ≠ 1 → ∀ y ∈ X, y ≠ 1 →
      ∃ n ∈ M ⊓ Subgroup.normalizer (X : Set G), n * x * n⁻¹ = y :=
  exists_conj_eq_of_escape hOnly hX hXc
    (D2L34BetaConf3.exists_escape_of_not_isCyclic hc hstr hN hNM hXN hXM hX hXc)
    (normalizer_le_of_stronglyEmbedded Nat.prime_three hstr hX hXM
      fun h => hXc (h ▸ isCyclic_of_subsingleton ..))

end CFSG.LocalAnalysis.RankThreeTheoremC

namespace CFSG.AGLEmbeddingD2.Tits.MsidePrelim

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

variable {G : Type} [Group G] [Finite G]
variable {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D2L34BetaConf.exists_escape_of_not_isCyclic (hc : D2L34BetaConf d P M A H R Rbar K)
    (hstr : GLBStronglyEmbedded 3 M) {N : Subgroup G} (hN : IsTwoLocal N) (hNM : ¬ N ≤ M)
    {X : Subgroup G} (hXN : X ≤ N) (hXM : X ≤ M) (hX : IsPGroup 3 X) (hXc : ¬ IsCyclic X) :
    ∃ N₁ E₀ : Subgroup G, N ≤ N₁ ∧ X ≤ E₀ ∧ D2Escape 3 P M E₀ N₁ E₀ ∧
      D2EscapeMax 3 P M E₀ ∧ Nat.card E₀ = 9 := by
  have := hc.amb3
  exact hc.toConf3.exists_escape_of_not_isCyclic hstr hN hNM hXN hXM hX hXc

theorem D2L34BetaConf.card_le_nine_of_not_isCyclic (hc : D2L34BetaConf d P M A H R Rbar K)
    (hstr : GLBStronglyEmbedded 3 M) {N : Subgroup G} (hN : IsTwoLocal N) (hNM : ¬ N ≤ M)
    {X : Subgroup G} (hXN : X ≤ N) (hXM : X ≤ M) (hX : IsPGroup 3 X) (hXc : ¬ IsCyclic X) :
    Nat.card X ≤ 9 := by
  have := hc.amb3
  exact hc.toConf3.card_le_nine_of_not_isCyclic hstr hN hNM hXN hXM hX hXc

theorem D2L34BetaConf.exists_conj_eq_of_not_isCyclic (hc : D2L34BetaConf d P M A H R Rbar K)
    (hstr : GLBStronglyEmbedded 3 M) (hOnly : D2OnlyL34At P M) {N : Subgroup G}
    (hN : IsTwoLocal N) (hNM : ¬ N ≤ M) {X : Subgroup G} (hXN : X ≤ N) (hXM : X ≤ M)
    (hX : IsPGroup 3 X) (hXc : ¬ IsCyclic X) :
    IsElemAbelian 3 X ∧ Nat.card X = 9 ∧ ∀ x ∈ X, x ≠ 1 → ∀ y ∈ X, y ≠ 1 →
      ∃ n ∈ M ⊓ Subgroup.normalizer (X : Set G), n * x * n⁻¹ = y := by
  have := hc.amb3
  exact hc.toConf3.exists_conj_eq_of_not_isCyclic hstr hOnly hN hNM hXN hXM hX hXc

end CFSG.AGLEmbeddingD2.Tits.MsidePrelim
