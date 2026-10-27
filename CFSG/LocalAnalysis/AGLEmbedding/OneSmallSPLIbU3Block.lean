module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbBlock

public section
namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R L : Subgroup G}

theorem D1PhaseThree.commutator_le_centralizer_block (h : D1PhaseThree p P M H R)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hSch : KFactCatalogSchreier)
    (hKF : KFactBlockCentCycIb) (hK2 : KFactAltSixSevenAutFive)
    (hK3 : CitedBlockTransvectionCyclic) (hK4 : CitedBlockAltNormalizerSq) (hp5 : 5 ≤ p)
    (hcyc : ∀ Y' : Subgroup G, Y' ≤ M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) →
      ⁅Y', Y'⁆ = Y' → ∀ A : Subgroup G, A ≤ Y' → IsPGroup p A → IsCyclic A)
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    {X : Subgroup G} (hXK : X ≤ H ⊓ M) (hXL : X ≤ Subgroup.normalizer (L : Set G))
    (hXexp : ∀ x ∈ X, x ^ p = 1) (hXcard : Nat.card X = p ^ 3)
    (hXnorm : ∀ N : Subgroup G, N ≤ X → X ≤ Subgroup.normalizer (N : Set G) → N ≠ ⊥ →
      ⁅X, X⁆ ≤ N)
    {D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hDp : ⁅D, D⁆ = D)
    (hDL : D ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hDS : D ≤ Subgroup.normalizer (barM M (pCoreOf 2 H) : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hDcyc : ∀ A : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), A ≤ D → IsPGroup p A → IsCyclic A)
    (hDpart : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      V ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) → ⁅V, V⁆ = V →
      ∀ k : ℕ, p ^ k ∣ Nat.card V → p ^ k ∣ Nat.card D)
    {zb : ↥M ⧸ CFSG.pCore 2 ↥M} (hzD : zb ∈ D) (hzp : zb ^ p = 1)
    (hzC : zb ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hZ : ∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅W, W⁆ = W →
      W ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → W = ⊥)
    (hXD : barM M X ≤ Subgroup.centralizer (D : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    barM M ⁅X, X⁆ ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  set S := pCoreOf 2 H with hS
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Lb := barM M L with hLb
  set Cb := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hCb
  have hKeq := h.inf_eq_inf_normalizer_twoCore
  have hXM : X ≤ M := hXK.trans inf_le_right
  have hXK' : X ≤ M ⊓ Subgroup.normalizer (S : Set G) := hKeq ▸ hXK
  have hXp : IsPGroup p X := IsPGroup.of_card hXcard
  have hpp : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  set C := X ⊓ blockCentralizer M L with hC
  have hXC : X ≤ Subgroup.normalizer (C : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx,
      mem_normalizer_blockCentralizer (hXM hx) (hXL hx)⟩
  by_cases hC0 : C = ⊥
  swap
  · have h1 := hXnorm C inf_le_left hXC hC0
    exact (barM_mono (h1.trans inf_le_right)).trans (barM_blockCentralizer_le M L)
  exfalso
  have hXbar : Nat.card (barM M X) = p ^ 3 := by
    rw [← hXcard, barM]
    have hO2 : p.Coprime (Nat.card (CFSG.pCore 2 ↥M)) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
      rw [hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    have hXsub : IsPGroup p (X.subgroupOf M) := hXp.comap_subtype
    rw [card_map_mk_of_isPGroup hp _ hO2 hXsub,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv]
  have hXbC : barM M X ⊓ Cb = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨⟨x, hxM⟩, hxX, rfl⟩, hxC⟩
    have hxC' : x ∈ C := ⟨Subgroup.mem_subgroupOf.mp hxX, ⟨x, hxM⟩, hxC, rfl⟩
    rw [hC0, Subgroup.mem_bot] at hxC'
    have : (⟨x, hxM⟩ : M) = 1 := Subtype.ext hxC'
    rw [this, map_one]
    exact Subgroup.one_mem _
  have hJ := perfectCyclicSylow_barM hL.le hp hcyc
  have hn1 := h.nineThree_not_one h85 hD2 hL
  rcases h.nineThree h93 hL with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact hn1.1 h1
  ·
    have hMtop : M ≠ ⊤ := fun hM => h.not_le (hM ▸ le_top)
    have hcat : CatalogSimpleSections (↥M ⧸ CFSG.pCore 2 ↥M) :=
      (catalogSimpleSections_of_isKProper h.glob.kProper M hMtop).quotient _
    have hOut := isSolvable_outer_of_component hSch hL.component
      (hcat.isCatalogGroup_center_quotient hL.component)
    have hDsup : D ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) ⊔ Cb := fun d hd =>
      h.mem_sup_barM_of_mem_sup h84 h86 hD2 hL
        (perfect_le_sup_centralizer_of_outer hOut hDp hDL hd) (hDS hd)
    have hKF' := hKF _ Lb (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) hL.component h2.1
      h2.2.1 (h.barM_ne_of_isWeakSBlock hL) (ne_inf_normalizer_of_nineThreeTwo h2 (hn1.2 h2)) p
      hp hp5 D hDp hDsup hDcyc hDpart zb hzD hzp hzC (fun W _ hWp hWz => hZ W hWp hWz)
    obtain ⟨⟨u, hu, hcov⟩, -⟩ := hKF' (barM M X) (barM_le_normalizer_barM hXL) (isPGroup_barM hXp)
    set E₂ := barM M X ⊓ (Lb ⊔ Cb) with hE₂
    have hE₂J : E₂ ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) ⊔ Cb := by
      rintro e ⟨⟨⟨x, hxM⟩, hxX, rfl⟩, hxQ⟩
      have hxS : x ∈ Subgroup.normalizer (S : Set G) :=
        (hXK' (Subgroup.mem_subgroupOf.mp hxX)).2
      exact h.mem_sup_barM_of_mem_sup h84 h86 hD2 hL hxQ (mem_normalizer_barM hxM hxS)
    have hE₂L : E₂ ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      inf_le_left.trans (barM_le_normalizer_barM hXL)
    obtain ⟨-, hb⟩ := hKF' E₂ hE₂L ((isPGroup_barM hXp).to_le inf_le_left)
    obtain ⟨v, hv, hcovv⟩ := hb hE₂J (inf_le_left.trans hXD)
    have hupow : u ^ p = 1 := by
      obtain ⟨⟨x, hxM⟩, hxX, rfl⟩ := hu
      have : (⟨x, hxM⟩ : M) ^ p = 1 :=
        Subtype.ext (by simpa using hXexp x (Subgroup.mem_subgroupOf.mp hxX))
      rw [← map_pow, this, map_one]
    have hvpow : v ^ p = 1 := by
      obtain ⟨⟨x, hxM⟩, hxX, rfl⟩ := hv.1
      have : (⟨x, hxM⟩ : M) ^ p = 1 :=
        Subtype.ext (by simpa using hXexp x (Subgroup.mem_subgroupOf.mp hxX))
      rw [← map_pow, this, map_one]
    have hE₂C : E₂ ⊓ Cb = ⊥ := by
      rw [eq_bot_iff]
      intro e he
      rw [← hXbC]
      exact ⟨he.1.1, he.2⟩
    have hE₂card := card_le_of_cov_of_inf_eq_bot hp.pos hv hvpow hcovv hE₂C
    have hXcard' := card_le_mul_card_inf_of_cov hp.pos hu hupow hcov
    have : Nat.card (barM M X) ≤ p * p := hXcard'.trans (Nat.mul_le_mul_left p hE₂card)
    rw [hXbar] at this
    have hpp' : p * p = p ^ 2 := by ring
    omega
  ·
    obtain ⟨u, hu, hcov⟩ := hK3 G M S L p h.isKGroup.1 h.asc81bHyp hL hn1.1
      (h.not_isSylowTwoOf_inf h85 hD2 hL) h3 hp hp2 hJ X hXK' hXL hXp
    have := card_le_of_cov_of_inf_eq_bot hp.pos hu (hXexp u hu) hcov hC0
    have : p < p ^ 3 := lt_of_le_of_lt (Nat.le_self_pow (by norm_num) p) hpp
    omega
  ·
    have hle := hK2 _ Lb (barM M X) p hL.component (Or.inl h4.2.2.1) hp hp5
      (barM_le_normalizer_barM hXL) (isPGroup_barM hXp)
    rw [← relIndex_blockCentralizer_eq hXM, ← hC, hC0, Subgroup.relIndex_bot_left, hXcard] at hle
    have : p < p ^ 3 := lt_of_le_of_lt (Nat.le_self_pow (by norm_num) p) hpp
    omega
  ·
    have hle := hK2 _ Lb (barM M X) p hL.component (Or.inr h5.2.1) hp hp5
      (barM_le_normalizer_barM hXL) (isPGroup_barM hXp)
    rw [← relIndex_blockCentralizer_eq hXM, ← hC, hC0, Subgroup.relIndex_bot_left, hXcard] at hle
    have : p < p ^ 3 := lt_of_le_of_lt (Nat.le_self_pow (by norm_num) p) hpp
    omega
  all_goals
    have h678 : NineThreeSix M S L ∨ NineThreeSeven M S L ∨ NineThreeEight M S L := by
      first
      | exact Or.inl ‹_›
      | exact Or.inr (Or.inl ‹_›)
      | exact Or.inr (Or.inr ‹_›)
    obtain ⟨U₁, U₂, hU₁, hU₂, hU12, hi₁, hi₂, -⟩ :=
      hK4 G M S L p h.isKGroup.1 h.asc81bHyp hL hn1.1 (h.not_isSylowTwoOf_inf h85 hD2 hL) h678
        hp hp2 hJ X hXK' hXL hXp
    have hU12C : U₁ ⊓ U₂ ≤ C := le_inf (inf_le_left.trans hU₁) hU12
    rw [hC0, le_bot_iff] at hU12C
    have hle := Subgroup.relIndex_inf_le (H := U₁) (K := U₂) (L := X)
    rw [hU12C, Subgroup.relIndex_bot_left, hXcard] at hle
    have : p ^ 3 ≤ p * p := hle.trans (Nat.mul_le_mul hi₁ hi₂)
    have hpp' : p * p = p ^ 2 := by ring
    omega

end CFSG.AGLEmbedding
