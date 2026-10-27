module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIV
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIVTypes
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZCompCloseDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactReduceBlocks
import CFSG.LocalAnalysis.AGLEmbedding.PrimeBlockTypes
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeSylowDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

section Groups

variable {X : Type*} [Group X] [Finite X]

theorem card_le_three_of_cyclic_of_pow_three {P : Subgroup X}
    (h : ∀ x ∈ P, (∃ k : ℕ, x ^ 3 ^ k = 1) → x ^ 3 = 1) (Q : Sylow 3 ↥P)
    (hQ : IsCyclic (Q : Subgroup ↥P)) : Nat.card (Q : Subgroup ↥P) ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥(Q : Subgroup ↥P))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp Q.isPGroup'
  have hox : orderOf ((g : ↥P) : X) = Nat.card (Q : Subgroup ↥P) := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hg]
  have h3 := h _ (g : ↥P).2 ⟨k, by rw [← hk, ← hox]; exact pow_orderOf_eq_one _⟩
  rw [← hox]
  exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h3)

theorem mul_comm_of_card_le_nine {V : Subgroup X} (hV3 : IsPGroup 3 V)
    (hV : Nat.card V ≤ 3 ^ 2) {x y : X} (hx : x ∈ V) (hy : y ∈ V) : x * y = y * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hV3
  have hm2 : m ≤ 2 := by
    by_contra h
    have h3 : 3 ^ 3 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hcomm : ∀ s t : ↥V, s * t = t * s := by
    interval_cases m
    · have : Subsingleton ↥V := (Nat.card_eq_one_iff_unique.mp (by simpa using hm)).1
      exact fun s t => Subsingleton.elim _ _
    · have : IsCyclic ↥V := isCyclic_of_prime_card (p := 3) (by simpa using hm)
      exact IsCyclic.isMulCommutative.is_comm.comm
    · exact (IsPGroup.isMulCommutative_of_card_eq_prime_sq hm).is_comm.comm
  exact congrArg Subtype.val (hcomm ⟨x, hx⟩ ⟨y, hy⟩)

theorem commutator_mem_centralizer_of_threeSub {Lb P U : Subgroup X} (hPL : P ≤ Lb)
    (hP : ∀ V : Subgroup X, V ≤ P → IsPGroup 3 V → ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hUP : U ≤ P) (hU : ∀ u ∈ U, ∃ e : ℕ, u ^ 3 ^ e ∈ Subgroup.centralizer (Lb : Set X))
    {a b : X} (ha : a ∈ U) (hb : b ∈ U) :
    a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (Lb : Set X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup ↥U := (Subgroup.centralizer (Lb : Set X)).subgroupOf U
  have hCc : ∀ c ∈ C, ∀ u : ↥U, (u : X) * c = c * u := fun c hc u =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hc) u (hPL (hUP u.2))
  have hCn : C.Normal := by
    refine ⟨fun c hc g => ?_⟩
    rw [show g * c * g⁻¹ = c from by
      rw [show g * c = c * g from Subtype.ext (hCc c hc g), mul_inv_cancel_right]]
    exact hc
  have hquot : IsPGroup 3 (↥U ⧸ C) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H u =>
      obtain ⟨e, he⟩ := hU u u.2
      exact ⟨e, by
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr (by simpa using he)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hquot
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 3 ↥U))
  have htop : (Q : Subgroup ↥U) ⊔ C = ⊤ := by
    have h1 : ((Q : Subgroup ↥U) ⊔ C).index ∣ (Q : Subgroup ↥U).index :=
      Subgroup.index_dvd_of_le le_sup_left
    have h2 : ((Q : Subgroup ↥U) ⊔ C).index ∣ 3 ^ n := by
      rw [← hn, ← Subgroup.index_eq_card]
      exact Subgroup.index_dvd_of_le le_sup_right
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h2
    rcases i with _ | i
    · exact Subgroup.index_eq_one.mp (by simpa using hi)
    · exact absurd ((dvd_pow_self 3 (Nat.succ_ne_zero i)).trans (hi ▸ h1)) Q.not_dvd_index
  have hmem : ∀ u : ↥U, ∃ q ∈ (Q : Subgroup ↥U), ∃ c ∈ C, q * c = u := by
    intro u
    have hu : u ∈ ((((Q : Subgroup ↥U) ⊔ C : Subgroup ↥U)) : Set ↥U) := by
      rw [htop]
      exact Subgroup.mem_top u
    rw [Subgroup.mul_normal] at hu
    exact Set.mem_mul.mp hu
  have hQ3 : IsPGroup 3 ((Q : Subgroup ↥U).map U.subtype) := Q.isPGroup'.map _
  have hQP : (Q : Subgroup ↥U).map U.subtype ≤ P := by
    rintro _ ⟨x, -, rfl⟩
    exact hUP x.2
  obtain ⟨q, hq, c, hc, hqc⟩ := hmem ⟨a, ha⟩
  obtain ⟨q', hq', c', hc', hqc'⟩ := hmem ⟨b, hb⟩
  have hqq' : Commute (q : X) q' := hP _ hQP hQ3 _ ⟨q, hq, rfl⟩ _ ⟨q', hq', rfl⟩
  have hqC : Commute (q : X) c' := hCc c' hc' q
  have hcQ : Commute (c : X) q' := (hCc c hc q').symm
  have hcC : Commute (c : X) c' := (hCc c hc c').symm
  have hab : Commute a b := by
    rw [show a = (q : X) * c from congrArg Subtype.val hqc.symm,
      show b = (q' : X) * c' from congrArg Subtype.val hqc'.symm]
    exact (hqq'.mul_right hqC).mul_left (hcQ.mul_right hcC)
  rw [hab.eq, mul_inv_cancel_right, mul_inv_cancel]
  exact Subgroup.one_mem _

end Groups

section Bar

variable {G : Type} [Group G] [Finite G]

theorem coprime_card_blockPL_of_perfect {M S L : Subgroup G} (hL : IsWeakSBlock M S L)
    (hperf : ∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (S : Set G) → ⁅Y, Y⁆ = Y →
      Nat.Coprime 3 (Nat.card Y))
    (W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) (hW : W ≤ blockPL M S L) (hWW : ⁅W, W⁆ = W) :
    Nat.Coprime 3 (Nat.card W) :=
  coprime_card_of_le_barM_of_perfect inf_le_left hperf
    (hW.trans (barM_mono fun _ hx => ⟨hL.le hx.2, hx.1⟩)) hWW

theorem coprime_card_blockPL_of_series {M S L N₀ B : Subgroup G} (hL : IsWeakSBlock M S L)
    (hN₀B : N₀ ≤ B) (hBK : B ≤ M ⊓ Subgroup.normalizer (S : Set G))
    (hNN₀ : M ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (N₀ : Set G))
    (hNB : M ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (B : Set G))
    (hcop : Nat.Coprime 3 (Nat.card N₀)) (h3 : ∀ b ∈ B, ∃ e : ℕ, b ^ 3 ^ e ∈ N₀)
    (h2 : ∀ k ∈ M ⊓ Subgroup.normalizer (S : Set G), ∃ e : ℕ, k ^ 2 ^ e ∈ B)
    (W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) (hW : W ≤ blockPL M S L) (hWW : ⁅W, W⁆ = W) :
    Nat.Coprime 3 (Nat.card W) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hWK : W ≤ barM M (M ⊓ Subgroup.normalizer (S : Set G)) :=
    hW.trans (barM_mono fun _ hx => ⟨hL.le hx.2, hx.1⟩)
  have hWB : W ≤ barM M B := by
    refine le_of_perfect_of_prime_pow_mem (q := 2) hWW
      (hWK.trans (barM_le_normalizer_barM hNB)) ?_
    intro w hw
    obtain ⟨k, hk, rfl⟩ := hWK hw
    obtain ⟨e, he⟩ := h2 k hk
    exact ⟨e, ⟨k ^ 2 ^ e, by simpa [Subgroup.mem_subgroupOf] using he, by simp⟩⟩
  have hWN₀ : W ≤ barM M N₀ := by
    refine le_of_perfect_of_prime_pow_mem (q := 3) hWW
      (hWK.trans (barM_le_normalizer_barM hNN₀)) ?_
    intro w hw
    obtain ⟨b, hb, rfl⟩ := hWB hw
    obtain ⟨e, he⟩ := h3 b hb
    exact ⟨e, ⟨b ^ 3 ^ e, by simpa [Subgroup.mem_subgroupOf] using he, by simp⟩⟩
  have hdvd : Nat.card W ∣ Nat.card N₀ := by
    refine (Subgroup.card_dvd_of_le hWN₀).trans ((Subgroup.card_map_dvd _ _).trans ?_)
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (hN₀B.trans (hBK.trans inf_le_left))).toEquiv).dvd
  exact Nat.Coprime.coprime_dvd_right hdvd hcop

theorem kFactBlockSylowThreeExp_of (hPS : KFactParabolicThreeSylowSmall)
    (hTPL : CitedBlockTransvectionPL) : KFactBlockSylowThreeExp := by
  intro G _ _ M S L hK hA hL h93 hX hS hperfK Q hQ
  have hperf := coprime_card_blockPL_of_perfect hL hperfK
  rcases h93 with h1 | h2 | hr
  · exact absurd h1 hX
  · obtain ⟨T₁, hT₁, hN, hne, hJ⟩ := exists_parabolic_three_of_nineThreeTwo hA hL h2 hS hperf
    obtain ⟨ha, -, -, -⟩ := hPS _ hL.component.2.2 h2.1 T₁ _ hT₁ hN hne hJ
    exact card_le_three_of_sylow_subgroupOf (barM_mono inf_le_right) ha Q hQ
  · exact card_le_three_of_cyclic_of_pow_three
      (fun x hx hx3 => pow_three_eq_one_of_blockPL_rest hTPL hK hA hL hX hS hr hperf hx hx3) Q hQ

theorem kFactBlockThreeOrderNine_of (hPS : KFactParabolicThreeSylowSmall)
    (hTPL : CitedBlockTransvectionPL) : KFactBlockThreeOrderNine := by
  intro G _ _ M S L hK hA hL h93 hX hS _ hperf
  have hPL : blockPL M S L ≤ barM M L := barM_mono inf_le_right
  rcases h93 with h1 | h2 | hr
  · exact absurd h1 hX
  · obtain ⟨T₁, hT₁, hN, hne, hJ⟩ := exists_parabolic_three_of_nineThreeTwo hA hL h2 hS hperf
    obtain ⟨ha, hb, -, -⟩ := hPS _ hL.component.2.2 h2.1 T₁ _ hT₁ hN hne hJ
    refine ⟨fun Q ⟨hQ, h9⟩ => ?_, fun u hu v hv hu9 hv9 huv =>
      not_zpowers_inf_eq_bot_of_subgroupOf hPL hb hu hv hu9 hv9 huv⟩
    exact absurd (h9.symm.trans_le (card_le_three_of_sylow_subgroupOf hPL ha Q hQ))
      (by norm_num)
  · have hpow : ∀ x ∈ blockPL M S L, (∃ k : ℕ, x ^ 3 ^ k = 1) → x ^ 3 = 1 :=
      fun x hx hx3 => pow_three_eq_one_of_blockPL_rest hTPL hK hA hL hX hS hr hperf hx hx3
    refine ⟨fun Q ⟨hQ, h9⟩ => ?_, fun u hu v _ hu9 _ _ => ?_⟩
    · exact absurd (h9.symm.trans_le (card_le_three_of_cyclic_of_pow_three hpow Q hQ))
        (by norm_num)
    · have h9 : u ^ 3 ^ 2 = 1 := by
        rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hu9]
        exact pow_orderOf_eq_one u
      have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hpow u hu ⟨2, h9⟩))
      omega

theorem kFactBlockThreeSolvableBeta_of (hPS : KFactParabolicThreeSylowSmall)
    (hTPL : CitedBlockTransvectionPL) (hA7PL : CitedBlockAltSevenPL) (h93 : Asc81bNineThree) :
    KFactBlockThreeSolvableBeta := by
  intro G _ _ M S L N₀ B hK hA hL hX hS hN₀B hBK hNN₀ hNB hcop h3 h2 U hU hU3 a ha b hb
  have hPL : blockPL M S L ≤ barM M L := barM_mono inf_le_right
  have hPK : blockPL M S L ≤ barM M (M ⊓ Subgroup.normalizer (S : Set G)) :=
    barM_mono fun _ hx => ⟨hL.le hx.2, hx.1⟩
  have hperf := coprime_card_blockPL_of_series hL hN₀B hBK hNN₀ hNB hcop h3 h2
  have hab : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ blockPL M S L → IsPGroup 3 V →
      ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
    rcases h93 G M S L hK hA hL with h1 | h2' | hr
    · exact absurd h1 hX
    · obtain ⟨T₁, hT₁, hN, hne, hJ⟩ :=
        exists_parabolic_three_of_nineThreeTwo hA hL h2' hS hperf
      obtain ⟨-, -, hc, -⟩ := hPS _ hL.component.2.2 h2'.1 T₁ _ hT₁ hN hne hJ
      have hinf : ∀ {A : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)},
          blockPL M S L ≤ Subgroup.normalizer (A : Set _) →
          blockPL M S L ≤ Subgroup.normalizer ((A ⊓ blockPL M S L : Subgroup _) : Set _) :=
        fun hA' z hz => Subgroup.mem_normalizer_iff.mpr fun n => by
          rw [Subgroup.mem_inf, Subgroup.mem_inf]
          exact and_congr (Subgroup.mem_normalizer_iff.mp (hA' hz) n)
            (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hz) n)
      intro V hV hV3 x hx y hy
      refine mul_comm_of_subgroupOf hPL hc (N := barM M N₀ ⊓ blockPL M S L)
        (B := barM M B ⊓ blockPL M S L) (inf_le_inf_right _ (barM_mono hN₀B)) inf_le_right
        (hinf (hPK.trans (barM_le_normalizer_barM hNN₀)))
        (hinf (hPK.trans (barM_le_normalizer_barM hNB))) ?_ ?_ ?_ hV hV3 hx hy
      · refine Nat.Coprime.coprime_dvd_right ((Subgroup.card_dvd_of_le inf_le_left).trans
          ((Subgroup.card_map_dvd _ _).trans ?_)) hcop
        exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (hN₀B.trans (hBK.trans inf_le_left))).toEquiv).dvd
      · rintro _ ⟨⟨k, hk, rfl⟩, hkP⟩
        obtain ⟨e, he⟩ := h3 k hk
        exact ⟨e, ⟨k ^ 3 ^ e, by simpa [Subgroup.mem_subgroupOf] using he, by simp⟩,
          (blockPL M S L).pow_mem hkP _⟩
      · intro j hj
        obtain ⟨k, hk, rfl⟩ := hPK hj
        obtain ⟨e, he⟩ := h2 k hk
        exact ⟨e, ⟨k ^ 2 ^ e, by simpa [Subgroup.mem_subgroupOf] using he, by simp⟩,
          (blockPL M S L).pow_mem hj _⟩
    · intro V hV hV3 x hx y hy
      exact mul_comm_of_card_le_nine hV3
        (card_le_nine_of_blockPL_rest hTPL hA7PL hK hA hL hX hS hr hperf hV hV3) hx hy
  exact commutator_mem_centralizer_of_threeSub hPL hab hU hU3 ha hb

theorem card_le_of_blockThreeOneOrbit (hPS : KFactParabolicThreeSylowSmall)
    (hTPL : CitedBlockTransvectionPL) (hA7PL : CitedBlockAltSevenPL) (h93 : Asc81bNineThree)
    {M S L : Subgroup G} (hK : Open.IsKGroup ↥M) (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hX : ¬ InClassXBlock L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L)
    (hperfK : ∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (S : Set G) → ⁅Y, Y⁆ = Y →
      Nat.Coprime 3 (Nat.card Y))
    (hrank : Open.pRank 3 (blockPL M S L) ≤ 3)
    (hO3 : IsMulCommutative ↥(CFSG.pCore 3
      (↥(blockPL M S L) ⧸ primeComplementCore (G := ↥(blockPL M S L)) 3)))
    {U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hU : U ≤ blockPL M S L) (hU3 : IsPGroup 3 U) :
    Nat.card U ≤ 3 ^ 3 := by
  have hperf := coprime_card_blockPL_of_perfect hL hperfK
  have hPL : blockPL M S L ≤ barM M L := barM_mono inf_le_right
  rcases h93 G M S L hK hA hL with h1 | h2 | hr
  · exact absurd h1 hX
  · obtain ⟨T₁, hT₁, hN, hne, hJ⟩ := exists_parabolic_three_of_nineThreeTwo hA hL h2 hS hperf
    obtain ⟨-, -, -, hd⟩ := hPS _ hL.component.2.2 h2.1 T₁ _ hT₁ hN hne hJ
    have hE := isElemAbelian_of_subgroupOf hPL (hd (isMulCommutative_pCore_subgroupOf hPL hO3))
      hU hU3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hU3
    rw [hm]
    exact Nat.pow_le_pow_right (by norm_num)
      ((le_pRank_of_elemAbelian_le (by norm_num) hU hE hm).trans hrank)
  · exact (card_le_nine_of_blockPL_rest hTPL hA7PL hK hA hL hX hS hr hperf hU hU3).trans
      (by norm_num)

end Bar

end CFSG.AGLEmbedding
