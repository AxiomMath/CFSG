module

public import CFSG.LocalAnalysis.AGLEmbedding.A9MSideOneAux
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.EscapeRankBar
public import CFSG.LocalAnalysis.AGLEmbedding.A9MSideBlocks

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section A9MSide

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R X : Subgroup G} {σ z : G}

theorem D1A9DataCore.false_of_two_blocks (h : D1A9DataCore P M H R X σ z) (hB3 : StmtBlockThree)
    (h84 : Asc81bEightFour) (h86 : Asc81bEightSix) (hD2 : D1NoXBlock)
    (hO : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥)
    (hσ : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      σ ∈ Subgroup.normalizer (L : Set G))
    {L L' : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hL' : IsWeakSBlock M (pCoreOf 2 H) L') (hne : L ≠ L') : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 := h.surv.ph3
  set S := pCoreOf 2 H with hS
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  obtain ⟨L₁, hL₁, hXL₁⟩ := h.exists_inf_blockCentralizer_eq_bot h84 hD2 hB3 hO hσ
  obtain ⟨E₁, hE₁P, hE₁, hE₁c⟩ := h.exists_isElemAbelian_le_barM h84 h86 hD2 hB3 hO hL₁ hXL₁
  obtain ⟨L₂, hL₂, h12⟩ : ∃ L₂ : Subgroup G, IsWeakSBlock M S L₂ ∧ L₁ ≠ L₂ := by
    by_cases he : L₁ = L
    · exact ⟨L', hL', he ▸ hne⟩
    · exact ⟨L, hL, he⟩
  obtain ⟨k, hk, hkL⟩ := h.exists_map_conj_eq h84 hD2 hB3 hO hL₁ hL₂
  have hkM : k ∈ M := hk.2
  have hkS : k ∈ Subgroup.normalizer (S : Set G) := (hKeq ▸ hk).2
  set g := mk ⟨k, hkM⟩ with hg
  set E₂ := E₁.map (MulAut.conj g).toMonoidHom with hE₂
  have hE₂P : E₂ ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L₂) := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨m, hm, rfl⟩ := hE₁P he
    have hm' := Subgroup.mem_subgroupOf.mp hm
    refine ⟨⟨k, hkM⟩ * m * (⟨k, hkM⟩)⁻¹, Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hkS hm'.1) (Subgroup.inv_mem _ hkS)
    · rw [← hkL]
      exact ⟨m, hm'.2, by simp⟩
    · simp only [map_mul, map_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hg, hmk]
  have hPK : ∀ {L₀ : Subgroup G}, IsWeakSBlock M S L₀ →
      barM M (Subgroup.normalizer (S : Set G) ⊓ L₀) ≤ barM M (H ⊓ M) := fun hL₀ =>
    barM_mono fun x hx => hKeq ▸ ⟨hL₀.le hx.2, hx.1⟩
  have hE₁L : E₁ ≤ barM M L₁ := hE₁P.trans (barM_mono inf_le_right)
  have hE₂L : E₂ ≤ barM M L₂ := hE₂P.trans (barM_mono inf_le_right)
  have hbar : barM M L₁ ≠ barM M L₂ := fun he =>
    h12 (hL₁.toIsTwoPrimeComponent.eq_of_barM_eq hL₂.toIsTwoPrimeComponent he)
  have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hL₁.component
    hL₂.component hbar
  have hL₁C : barM M L₁ ≤ Subgroup.centralizer (barM M L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hL₂C : barM M L₂ ≤ Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hcomm
  have hE₂e : IsElemAbelian 3 E₂ := elementary_abelian_map 3 hE₁ _
  have hJ : IsElemAbelian 3 (E₁ ⊔ E₂) := elementary_abelian_sup_of_commuting 3 hE₁ hE₂e
    (hE₁L.trans (hL₁C.trans (Subgroup.centralizer_le hE₂L)))
  have hJK : E₁ ⊔ E₂ ≤ barM M (H ⊓ M) := sup_le (hE₁P.trans (hPK hL₁)) (hE₂P.trans (hPK hL₂))
  have hrank : Open.pRank 3 (E₁ ⊔ E₂) ≤ 3 :=
    (pRank_mono 3 Nat.prime_three hJK).trans ((pRank_barM_le Nat.prime_three (by decide) M _
      inf_le_right).trans h.pRank_le)
  have heq := elementary_subgroup_eq_of_rank_bound 3 Nat.prime_three hJ le_sup_left 3 hE₁c hrank
  have hE₂Z : E₂ ≤ barM M L₁ ⊓ Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    le_inf ((le_sup_right.trans heq.symm.le).trans hE₁L) (hE₂L.trans hL₂C)
  have hcop := coprime_three_card_inf_centralizer hO hL₁.component.2.1
  have hE₂c : Nat.card E₂ = 3 ^ 3 := by
    rw [hE₂, Subgroup.card_map_of_injective (MulAut.conj g).injective, hE₁c]
  have hdvd := Subgroup.card_dvd_of_le hE₂Z
  rw [hE₂c] at hdvd
  exact absurd (Nat.Coprime.coprime_dvd_right hdvd hcop) (by decide)

theorem D1A9DataCore.false_of_one_block (h : D1A9DataCore P M H R X σ z) (hB3 : StmtBlockThree)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (hD2 : D1NoXBlock) (hi : KFactBlockThreeOneOrbit)
    (hO : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (huniq : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → L' = L) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 := h.surv.ph3
  set S := pCoreOf 2 H with hS
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Lb := barM M L with hLb
  set C := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hC
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  have hKL : H ⊓ M ≤ Subgroup.normalizer (L : Set G) := fun k hk =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (huniq _ (hL.map_conj hk.2 (hKeq ▸ hk).2))
  have hσK : σ ∈ H ⊓ M := h3.le_inf h.σ_mem
  have hσL : σ ∈ Subgroup.normalizer (L : Set G) := hKL hσK
  obtain ⟨L', hL', hzL'⟩ := h.exists_not_mem_blockCentralizer h84 hD2 hB3 hO
  rw [huniq L' hL'] at hzL'
  have hXL := h.inf_blockCentralizer_eq_bot hσL hzL'
  obtain ⟨E, hEP, hE, hEc⟩ := h.exists_isElemAbelian_le_barM h84 h86 hD2 hB3 hO hL hXL
  have hK := hi G M S L h3.isKGroup.1 h3.asc81bHyp hL (h3.nineThree_not_one h85 hD2 hL).1
    (h3.not_isSylowTwoOf_inf h85 hD2 hL) (fun Y hY hYp => h.coprime_card_of_perfect hY hYp)
    (coprime_three_card_center hO hL.component.2.1) (h.pRank_barM_le_three hL)
    (h.isMulCommutative_pCore_blockPL hL hKL)
  by_cases hσin : σ ∈ L ⊔ blockCentralizer M L
  ·
    have hRL : R ≤ L ⊔ blockCentralizer M L := by
      rw [← h.sup_zpowers_eq]
      exact sup_le (h.le_sup_blockCentralizer hB3 hL) ((Subgroup.zpowers_le).mpr hσin)
    have hRC : R ⊓ blockCentralizer M L = ⊥ := by
      rw [eq_bot_iff]
      rintro r ⟨hr, hrC⟩
      refine Subgroup.mem_bot.mpr (h.faithful h84 hD2 hB3 hO hr fun L₀ hL₀ => ?_)
      rw [huniq L₀ hL₀]
      exact hrC
    obtain ⟨U, hUP, hU3, hUc⟩ := h.exists_card_le_barM h84 h86 hD2 hO hL hRL hRC
    have hle := hK.1 U hUP hU3
    rw [hUc] at hle
    exact absurd hle (by norm_num)
  ·
    set s : M := ⟨σ, h3.le_M h.σ_mem⟩ with hs
    set t : M := ⟨z, h3.le_M (h.surv.le_R h.z_mem)⟩ with ht
    set u := mk s with hu
    set w := mk t with hw
    have huN : u ∈ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      Subgroup.le_normalizer_map _
        (Subgroup.mem_map_of_mem _ (Subgroup.le_normalizer_comap M.subtype hσL))
    have hs3 : s ^ 3 = 1 := Subtype.ext (by simpa using h.σ_pow)
    have hu3 : u ^ 3 = 1 := by rw [hu, ← map_pow, hs3, map_one]
    have hNC : Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
        Subgroup.normalizer (C : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _)
    have hLC : Lb ≤ Subgroup.normalizer (C : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      Subgroup.le_normalizer.trans hNC
    have huLC : u ∉ Lb ⊔ C := by
      intro hmem
      apply hσin
      have hmem' : u ∈ ((Lb ⊔ C : Subgroup _) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := hmem
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLC] at hmem'
      obtain ⟨_, ⟨l, hl, rfl⟩, c, hc, hlc⟩ := hmem'
      have hlσ : ((l⁻¹ * s : M) : G) ∈ blockCentralizer M L := by
        refine (mem_blockCentralizer_iff _).mpr ?_
        rw [map_mul, map_inv, ← hu, ← hlc]
        simpa using hc
      have he : σ = (l : G) * ((l⁻¹ * s : M) : G) := by simp [hs]
      rw [he]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hl))
        (Subgroup.mem_sup_right hlσ)
    have h2 := hK.2 ⟨E, hEP, hE, hEc⟩ u huN (by rw [hu3]; exact Subgroup.one_mem _) huLC
    set A := Subgroup.centralizer ({u} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓ (Lb ⊔ C) with hA
    have hA2 : 2 ≤ Open.pRank 3 A :=
      h2.trans (pRank_mono 3 Nat.prime_three (le_inf inf_le_right (inf_le_left.trans le_sup_left)))
    have hσz : σ * z = z * σ := (Subgroup.mem_centralizer_iff.mp h.z_center σ h.σ_mem)
    have hst : s * t = t * s := Subtype.ext hσz
    have huw : u * w = w * u := by rw [hu, hw, ← map_mul, hst, map_mul]
    have hwLC : w ∈ Lb ⊔ C := by
      have hLCpre : L ⊔ blockCentralizer M L ≤ ((Lb ⊔ C).comap mk).map M.subtype := by
        refine sup_le (fun l hl => ⟨⟨l, hL.le hl⟩, Subgroup.mem_sup_left
          (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl)), rfl⟩) ?_
        exact Subgroup.map_mono (Subgroup.comap_mono le_sup_right)
      exact barM_le_of_le_preimage hLCpre (Subgroup.mem_map_of_mem _
        (Subgroup.mem_subgroupOf.mpr (h.le_sup_blockCentralizer hB3 hL h.z_mem)))
    have hwA : w ∈ A := ⟨Subgroup.mem_centralizer_singleton_iff.mpr huw.symm, hwLC⟩
    have hw1 : w ≠ 1 := by
      intro hw1
      have hzQ : z ∈ X ⊓ pCoreOf 2 M := ⟨h.z_mem, coe_mem_pCoreOf_two_of_mk_eq_one t hw1⟩
      have hXQ : X ⊓ pCoreOf 2 M = ⊥ :=
        inf_eq_bot_of_isPGroup Nat.prime_three (h3.isPGroup_R.to_le h.surv.le_R) (by
          obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
            (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
          rw [hk]
          exact Nat.Coprime.pow_right k (by norm_num))
      rw [hXQ, Subgroup.mem_bot] at hzQ
      exact h.z_ne hzQ
    have hw3 : w ^ 3 = 1 := by
      have ht3 : t ^ 3 = 1 := Subtype.ext (by simpa using h.elem.2 z h.z_mem)
      rw [hw, ← map_pow, ht3, map_one]
    have hwo : orderOf w = 3 := orderOf_eq_prime hw3 hw1
    have hF2 := two_le_pRank_inf_centralizer_of_two_le Nat.prime_three (by decide) hA2 hwA hwo
    obtain ⟨F, hFA, hF, hFc⟩ := PreuniquenessRankFour.Helpers.pRank_attained 3 Nat.prime_three
      (A ⊓ Subgroup.centralizer ({w} : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    have huF : u ∉ F := fun huF' => huLC (hFA huF').1.2
    have huC : u ∈ Subgroup.centralizer (F : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      exact Subgroup.mem_centralizer_singleton_iff.mp (hFA hf).1.1
    have hFH : F ≤ Subgroup.centralizer ({u} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
        Subgroup.centralizer ({w} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      fun f hf => ⟨(hFA hf).1.1, (hFA hf).2⟩
    have huH : u ∈ Subgroup.centralizer ({u} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
        Subgroup.centralizer ({w} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl,
        Subgroup.mem_centralizer_singleton_iff.mpr huw⟩
    have hle := succ_le_pRank_of_isElemAbelian_of_mem_centralizer Nat.prime_three hF hFc hu3 huF
      huC hFH huH
    have hE2 : Open.pRank 3 (Subgroup.centralizer ({u} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
        Subgroup.centralizer ({w} : Set (↥M ⧸ CFSG.pCore 2 ↥M))) ≤ 2 :=
      h.pRank_inf_centralizer_le_two s t rfl rfl
    omega

theorem D1A9DataCore.exists_not_mem_normalizer (h : D1A9DataCore P M H R X σ z)
    (hB3 : StmtBlockThree) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (hD2 : D1NoXBlock) (hi : KFactBlockThreeOneOrbit)
    (hO : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥) :
    ∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧ σ ∉ Subgroup.normalizer (L : Set G) := by
  by_contra hno
  push Not at hno
  obtain ⟨L₀, hL₀⟩ := D1PhaseThree.exists_weakSBlock h.surv.ph3 h84 hD2
  by_cases h2 : ∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧ L ≠ L₀
  · obtain ⟨L, hL, hne⟩ := h2
    exact h.false_of_two_blocks hB3 h84 h86 hD2 hO hno hL hL₀ hne
  · push Not at h2
    exact h.false_of_one_block hB3 h84 h85 h86 hD2 hi hO hL₀ h2

end A9MSide

end CFSG.AGLEmbedding
