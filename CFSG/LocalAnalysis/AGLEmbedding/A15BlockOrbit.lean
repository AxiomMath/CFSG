module

public import CFSG.LocalAnalysis.AGLEmbedding.A15BlockOrbitAux
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA15Defs
import CFSG.LocalAnalysis.AGLEmbedding.A15OddCore
import CFSG.LocalAnalysis.AGLEmbedding.A9MSideBlocksAux
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeBlockRank
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section A15

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M H R : Subgroup G} {c : Fin 3 → G}
  {σ τ : G}

private theorem D1A15Data.pRank_three_le (h : D1A15Data P M H R c σ τ) :
    Open.pRank 3 (H ⊓ M) ≤ 3 := by
  by_contra hlt
  exact h.surv.ph3.false_of_four_le_pRank' h.ind Nat.prime_three (by decide) (by norm_num)
    (by omega)

private theorem D1A15Data.blockPL_le (h : D1A15Data P M H R c σ τ) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) : blockPL M (pCoreOf 2 H) L ≤ barM M (H ⊓ M) :=
  barM_mono (h.surv.ph3.inf_eq_inf_normalizer_twoCore ▸ fun _ hx => ⟨hL.le hx.2, hx.1⟩)

private theorem D1A15Data.le_three_of_pow_dvd_barM (h : D1A15Data P M H R c σ τ)
    {X : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hX : X ≤ barM M (H ⊓ M)) {n : ℕ}
    (hn : 5 ^ n ∣ Nat.card X) : n ≤ 3 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨T, hT⟩ := h.surv.ph3.isSylow
  have hH : 5 ^ n ∣ Nat.card H := by
    refine hn.trans ((Subgroup.card_dvd_of_le hX).trans ((Subgroup.card_map_dvd _ _).trans ?_))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : H ⊓ M ≤ M)).toEquiv]
    exact Subgroup.card_dvd_of_le inf_le_left
  have h1 := T.pow_dvd_card_of_pow_dvd_card hH
  rw [← Subgroup.card_map_of_injective H.subtype_injective, hT, h.card_R] at h1
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1

theorem D1A15Data.four_le_pRank_blockPL (h : D1A15Data P M H R c σ τ) (h85 : Asc81bEightFive)
    (hD2 : D1NoXBlock) (hf : KFactBlockThreeFives) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {Y : Subgroup G} (hYK : Y ≤ H ⊓ M)
    (hYn : H ⊓ M ≤ Subgroup.normalizer (Y : Set G)) (hRY : R ≤ Y)
    (hYP : barM M Y ≤ blockPL M (pCoreOf 2 H) L) :
    4 ≤ Open.pRank 3 (blockPL M (pCoreOf 2 H) L) := by
  have h3 := h.surv.ph3
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set N := GLBPrimeCore 5 H with hNdef
  set PL := blockPL M (pCoreOf 2 H) L with hPL
  set O := barM M N ⊓ PL with hO
  have hQN : pCoreOf 2 M ≤ N := h3.twoCore_M_le_glbPrimeCore
  have hPK : PL ≤ barM M (H ⊓ M) := h.blockPL_le hL
  have hmemO : ∀ x : M, mk x ∈ PL → (mk x ∈ O ↔ (x : G) ∈ N) := by
    intro x hxP
    refine ⟨fun hx => ?_, fun hx =>
      ⟨Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx), hxP⟩⟩
    obtain ⟨n, hn, hnx⟩ := hx.1
    have h1 : mk (n⁻¹ * x) = 1 := by rw [map_mul, map_inv, hnx, inv_mul_cancel]
    have h2 : (x : G) = n * ((n⁻¹ * x : M) : G) := by simp
    rw [h2]
    exact N.mul_mem (Subgroup.mem_subgroupOf.mp hn) (hQN (coe_mem_pCoreOf_two_of_mk_eq_one _ h1))
  have hO2 : PL ≤ Subgroup.normalizer (O : Set _) := by
    refine (le_inf (fun q hq => ?_) Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
    obtain ⟨k, hk, rfl⟩ := hPK hq
    have hNk : N.map (MulAut.conj (k : G)).toMonoidHom = N :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (le_normalizer_glbPrimeCore 5 H (Subgroup.mem_subgroupOf.mp hk).1)
    have he := barM_map_conj k.2 N
    rw [hNk] at he
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr he.symm
  have hO3 : Nat.Coprime 5 (Nat.card O) := by
    refine Nat.Coprime.coprime_dvd_right ((Subgroup.card_dvd_of_le inf_le_left).trans ?_)
      (glbPrimeCore_coprime 5 H)
    rw [barM, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe h3.primeCore_le).toEquiv]
    exact Subgroup.card_map_dvd _ _
  obtain ⟨J, hJ, hJJ, -⟩ := h.normal_closure Y hYK hYn hRY
  have hJM : ∀ i, J i ≤ M := fun i => (hJ i).1.trans (hYK.trans inf_le_right)
  let f : ∀ i, ↥(J i) →* ↥M ⧸ CFSG.pCore 2 ↥M := fun i => mk.comp (Subgroup.inclusion (hJM i))
  have hfP : ∀ i (x : J i), f i x ∈ PL := fun i x =>
    hYP ⟨Subgroup.inclusion (hJM i) x, Subgroup.mem_subgroupOf.mpr ((hJ i).1 x.2), rfl⟩
  refine hf G M (pCoreOf 2 H) L h3.isKGroup.1 h3.asc81bHyp hL
    (h3.nineThree_not_one h85 hD2 hL).1 (h3.not_isSylowTwoOf_inf h85 hD2 hL) O
    (fun i => (f i).range) inf_le_right hO2 hO3
    (card_eq_sixty_of_barM h.section_card (fun U hU => h3.preimage_le_inf (hU.trans hPK))
      fun x hxP hx => (hmemO x hxP).mpr hx) (fun i => ⟨?_, ?_⟩) ?_
  · rintro _ ⟨x, rfl⟩
    exact hfP i x
  · obtain ⟨φ, hφs, hφ⟩ := (hJ i).2.2
    exact exists_surjective_range_mk (hJM i) hQN (fun x => hmemO _ (hfP i x)) hφs hφ
  · intro i j hij
    rw [Subgroup.commutator_le]
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    set a := Subgroup.inclusion (hJM i) x
    set b := Subgroup.inclusion (hJM j) y
    have hab : ⁅f i x, f j y⁆ = mk ⁅a, b⁆ := (map_commutatorElement mk a b).symm
    have hP : mk ⁅a, b⁆ ∈ PL := by
      rw [← hab, commutatorElement_def]
      exact PL.mul_mem (PL.mul_mem (PL.mul_mem (hfP i x) (hfP j y)) (PL.inv_mem (hfP i x)))
        (PL.inv_mem (hfP j y))
    rw [hab]
    refine (hmemO _ hP).mpr ?_
    have hxy := hJJ i j hij (Subgroup.commutator_mem_commutator x.2 y.2)
    simpa [a, b, commutatorElement_def] using hxy

theorem D1A15Data.false_of_forall_map_conj_eq (h : D1A15Data P M H R c σ τ)
    (hb : StmtBlockInnerNormalizer) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (hD2 : D1NoXBlock) (hf : KFactBlockThreeFives) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hRE : R ≤ blockClosure M (H ⊓ M) L)
    (hA : ∀ k ∈ H ⊓ M, L.map (MulAut.conj k).toMonoidHom = L) : False := by
  have h3 := h.surv.ph3
  set Y : Subgroup G := (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L with hY
  have hYn : H ⊓ M ≤ Subgroup.normalizer (Y : Set G) :=
    (le_inf Subgroup.le_normalizer (le_normalizer_blockClosure inf_le_right)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hYL : barM M Y ≤ barM M L :=
    barM_le_of_le_preimage (inf_le_right.trans (blockClosure_le_preimage inf_le_right
      hL.toIsTwoPrimeComponent fun k hk => by rw [hA k hk]))
  have hYP : barM M Y ≤ blockPL M (pCoreOf 2 H) L := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := h3.mk_mem_blockPL_sup hb h84 h86 hD2 hL bot_le
      (Subgroup.mem_subgroupOf.mp hy).1 (by rw [sup_bot_eq]; exact hYL ⟨y, hy, rfl⟩)
    rwa [sup_bot_eq] at h1
  have h4 := h.four_le_pRank_blockPL h85 hD2 hf hL inf_le_left hYn (le_inf h3.le_inf hRE) hYP
  have h5 := (pRank_mono 3 Nat.prime_three (h.blockPL_le hL)).trans
    (pRank_barM_le Nat.prime_three (by decide) M (H ⊓ M) inf_le_right)
  have h6 := h.pRank_three_le
  omega

theorem D1A15Data.false_of_two_blocks (h : D1A15Data P M H R c σ τ)
    (hb : StmtBlockInnerNormalizer) (h84 : Asc81bEightFour) (h86 : Asc81bEightSix)
    (hD2 : D1NoXBlock) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hRE : R ≤ blockClosure M (H ⊓ M) L) {k : G} (hk : k ∈ H ⊓ M)
    (hne : L.map (MulAut.conj k).toMonoidHom ≠ L)
    (horb : ∀ k' ∈ H ⊓ M, L.map (MulAut.conj k').toMonoidHom = L ∨
      L.map (MulAut.conj k').toMonoidHom = L.map (MulAut.conj k).toMonoidHom) : False := by
  have h3 := h.surv.ph3
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set S := pCoreOf 2 H with hS
  set L₁ := L.map (MulAut.conj k).toMonoidHom with hL₁
  have hL₁w : IsWeakSBlock M S L₁ := hL.map_conj hk.2 (hKeq ▸ hk).2
  have c01 := barM_le_centralizer_of_ne hL.toIsTwoPrimeComponent hL₁w.toIsTwoPrimeComponent
    hne.symm
  have c10 := barM_le_centralizer_of_ne hL₁w.toIsTwoPrimeComponent hL.toIsTwoPrimeComponent hne
  set P₀ := blockPL M S L with hP₀def
  set P₁ := blockPL M S L₁ with hP₁def
  have hP₀ : P₀ ≤ barM M L := barM_mono inf_le_right
  have hP₁ : P₁ ≤ barM M L₁ := barM_mono inf_le_right
  have hRbar : barM M R ≤ barM M L ⊔ barM M L₁ := by
    refine barM_le_of_le_preimage (hRE.trans (blockClosure_le_preimage inf_le_right
      hL.toIsTwoPrimeComponent fun k₀ hk₀ => ?_))
    rcases horb k₀ hk₀ with he | he <;> rw [he]
    · exact le_sup_left
    · exact le_sup_right
  have hRP : barM M R ≤ P₀ ⊔ P₁ := by
    rintro _ ⟨⟨r, hrM⟩, hr, rfl⟩
    have hrK : r ∈ H ⊓ M := h3.le_inf (Subgroup.mem_subgroupOf.mp hr)
    have s1 := h3.mk_mem_blockPL_sup hb h84 h86 hD2 hL c10 hrK (hRbar ⟨⟨r, hrM⟩, hr, rfl⟩)
    rw [sup_comm] at s1
    have s2 := h3.mk_mem_blockPL_sup hb h84 h86 hD2 hL₁w (hP₀.trans c01) hrK s1
    rwa [sup_comm] at s2
  have hcop : Nat.Coprime 5 (Nat.card (P₀ ⊓ P₁ : Subgroup _)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le (le_inf (inf_le_left.trans hP₀)
      (inf_le_right.trans (hP₁.trans c10))))
      (coprime_card_inf_centralizer_of_pCore_eq_bot (h.pCore_five_eq_bot h84 hD2)
        hL.component.2.1)
  exact false_of_card_sup_five (h3.card_blockPL_map_conj hk)
    ((hP₁.trans c10).trans ((Subgroup.centralizer_le hP₀).trans
      (Subgroup.centralizer_le_normalizer _))) hcop hRP h.card_barM
    fun n hn => h.le_three_of_pow_dvd_barM (sup_le (h.blockPL_le hL) (h.blockPL_le hL₁w)) hn

theorem D1A15Data.false_of_three_blocks (h : D1A15Data P M H R c σ τ) (hB3 : StmtBlockThree)
    (hb : StmtBlockInnerNormalizer) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (hD2 : D1NoXBlock) (he : KFactBlockFiveNoncyclic) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hRE : R ≤ blockClosure M (H ⊓ M) L) {k k' : G}
    (hk : k ∈ H ⊓ M) (hk' : k' ∈ H ⊓ M) (h01 : L.map (MulAut.conj k).toMonoidHom ≠ L)
    (h02 : L.map (MulAut.conj k').toMonoidHom ≠ L)
    (h12 : L.map (MulAut.conj k').toMonoidHom ≠ L.map (MulAut.conj k).toMonoidHom) : False := by
  have h3 := h.surv.ph3
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  set S := pCoreOf 2 H with hS
  set L₁ := L.map (MulAut.conj k).toMonoidHom with hL₁
  set L₂ := L.map (MulAut.conj k').toMonoidHom with hL₂
  have hL₁w : IsWeakSBlock M S L₁ := hL.map_conj hk.2 (hKeq ▸ hk).2
  have hL₂w : IsWeakSBlock M S L₂ := hL.map_conj hk'.2 (hKeq ▸ hk').2
  have hc : ∀ {A B : Subgroup G}, IsWeakSBlock M S A → IsWeakSBlock M S B → A ≠ B →
      barM M A ≤ Subgroup.centralizer (barM M B : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    fun hA hB hAB => barM_le_centralizer_of_ne hA.toIsTwoPrimeComponent hB.toIsTwoPrimeComponent
      hAB
  have c01 := hc hL hL₁w h01.symm
  have c02 := hc hL hL₂w h02.symm
  have c10 := hc hL₁w hL h01
  have c12 := hc hL₁w hL₂w h12.symm
  have c20 := hc hL₂w hL h02
  have c21 := hc hL₂w hL₁w h12
  set P₀ := blockPL M S L with hP₀def
  set P₁ := blockPL M S L₁ with hP₁def
  set P₂ := blockPL M S L₂ with hP₂def
  have hP₀ : P₀ ≤ barM M L := barM_mono inf_le_right
  have hP₁ : P₁ ≤ barM M L₁ := barM_mono inf_le_right
  have hP₂ : P₂ ≤ barM M L₂ := barM_mono inf_le_right
  have hRbar : barM M R ≤ barM M L ⊔ (barM M L₁ ⊔ barM M L₂) := by
    refine barM_le_of_le_preimage (hRE.trans (blockClosure_le_preimage inf_le_right
      hL.toIsTwoPrimeComponent fun k₀ hk₀ => ?_))
    rcases h3.eq_or_eq_or_eq_of_isWeakSBlock h.pRank_three_le hB3 hL hL₁w hL₂w
      (hL.map_conj hk₀.2 (hKeq ▸ hk₀).2) h01.symm h02.symm h12.symm with he | he | he <;>
      rw [he]
    · exact le_sup_left
    · exact le_sup_left.trans le_sup_right
    · exact le_sup_right.trans le_sup_right
  have hRP : barM M R ≤ P₂ ⊔ (P₁ ⊔ P₀) := by
    rintro _ ⟨⟨r, hrM⟩, hr, rfl⟩
    have hrK : r ∈ H ⊓ M := h3.le_inf (Subgroup.mem_subgroupOf.mp hr)
    have s1 := h3.mk_mem_blockPL_sup hb h84 h86 hD2 hL (sup_le c10 c20) hrK
      (hRbar ⟨⟨r, hrM⟩, hr, rfl⟩)
    rw [sup_left_comm] at s1
    have s2 := h3.mk_mem_blockPL_sup hb h84 h86 hD2 hL₁w (sup_le (hP₀.trans c01) c21) hrK s1
    rw [← sup_assoc, sup_comm] at s2
    exact h3.mk_mem_blockPL_sup hb h84 h86 hD2 hL₂w (sup_le (hP₁.trans c12) (hP₀.trans c02))
      hrK s2
  have hN : ∀ {A B : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} {C D : Subgroup G}, A ≤ barM M C →
      B ≤ barM M D → barM M D ≤ Subgroup.centralizer (barM M C : Set _) →
      B ≤ Subgroup.normalizer (A : Set _) := fun hA hB hDC =>
    (hB.trans hDC).trans ((Subgroup.centralizer_le hA).trans
      (Subgroup.centralizer_le_normalizer _))
  have h5 : 5 ∣ Nat.card P₀ := by
    by_contra h5
    have hc0 : Nat.Coprime 5 (Nat.card P₀) :=
      (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h5
    have hc1 : Nat.Coprime 5 (Nat.card P₁) := by
      rw [hP₁def, h3.card_blockPL_map_conj hk]
      exact hc0
    have hc2 : Nat.Coprime 5 (Nat.card P₂) := by
      rw [hP₂def, h3.card_blockPL_map_conj hk']
      exact hc0
    have hcop := coprime_card_sup_of_le_normalizer
      (sup_le (hN hP₂ hP₁ c12) (hN hP₂ hP₀ c02)) hc2
      (coprime_card_sup_of_le_normalizer (hN hP₁ hP₀ c01) hc1 hc0)
    refine (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mp hcop
      ((?_ : 5 ∣ Nat.card (barM M R)).trans (Subgroup.card_dvd_of_le hRP))
    rw [h.card_barM]
    exact dvd_pow_self 5 (by norm_num)
  have h5' : ∀ {k₀ : G}, k₀ ∈ H ⊓ M →
      5 ∣ Nat.card (blockPL M S (L.map (MulAut.conj k₀).toMonoidHom)) := fun hk₀ => by
    rw [h3.card_blockPL_map_conj hk₀]
    exact h5
  have hX : ∀ {A : Subgroup G}, IsWeakSBlock M S A → ¬ InClassXBlock A ∧
      ¬ IsSylowTwoOf (S ⊓ A) A := fun hA =>
    ⟨(h3.nineThree_not_one h85 hD2 hA).1, h3.not_isSylowTwoOf_inf h85 hD2 hA⟩
  obtain ⟨⟨E, hEL, hE, hE9⟩, -⟩ :=
    he G M S L h3.isKGroup.1 h3.asc81bHyp hL (hX hL).1 (hX hL).2 h5
  obtain ⟨-, y, hyL, hy3, hyC⟩ :=
    he G M S L₁ h3.isKGroup.1 h3.asc81bHyp hL₁w (hX hL₁w).1 (hX hL₁w).2 (h5' hk)
  obtain ⟨-, z, hzL, hz3, hzC⟩ :=
    he G M S L₂ h3.isKGroup.1 h3.asc81bHyp hL₂w (hX hL₂w).1 (hX hL₂w).2 (h5' hk')
  have h4 := four_le_pRank_of_commuting_triple c01 c02 c12 hEL hE hE9 hyL hy3 hyC hzL hz3 hzC
  have hMtop : barM M M = ⊤ := by
    rw [barM, Subgroup.subgroupOf_self]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have h4M : 4 ≤ Open.pRank 3 M := by
    have h1 := pRank_barM_le Nat.prime_three (by decide) M M le_rfl
    rw [hMtop] at h1
    omega
  have hβ : 3 ∈ GLBBetaFour G :=
    mem_glbBetaFour_of_le_pRank Nat.prime_three (by decide) h3.maxTwoLocal_M.1 le_rfl h4M
  have hmap1 : L.map (MulAut.conj (1 : G)).toMonoidHom = L := by
    ext x
    simp
  have hK3 : 3 ≤ Open.pRank 3 (H ⊓ M) := by
    refine h3.le_pRank_three_of_injective_conj (fun A hA => hB3 h3 hA) hL ![1, k, k']
      (fun j => ?_) ?_
    · fin_cases j
      · exact (H ⊓ M).one_mem
      · exact hk
      · exact hk'
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
          hmap1] at hij
      all_goals first
        | rfl
        | exact absurd hij h01.symm
        | exact absurd hij h01
        | exact absurd hij h02.symm
        | exact absurd hij h02
        | exact absurd hij h12.symm
        | exact absurd hij h12
  exact false_of_guestPrime h3.glob.pre hβ (h.ind 3 hβ (by norm_num)) h3.maxTwoLocal_M
    h3.maxTwoLocal_H h3.not_le hK3

end A15

theorem stmtA15BlockOrbit_of (hB3 : StmtBlockThree) (hb : StmtBlockInnerNormalizer)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (hD2 : D1NoXBlock)
    (he : KFactBlockFiveNoncyclic) (hf : KFactBlockThreeFives) : StmtA15BlockOrbit := by
  intro G _ _ P M H R c σ τ h L hL hRE
  by_cases hA : ∀ k ∈ H ⊓ M, L.map (MulAut.conj k).toMonoidHom = L
  · exact h.false_of_forall_map_conj_eq hb h84 h85 h86 hD2 hf hL hRE hA
  push Not at hA
  obtain ⟨k, hk, hne⟩ := hA
  by_cases h3b : ∃ k' ∈ H ⊓ M, L.map (MulAut.conj k').toMonoidHom ≠ L ∧
      L.map (MulAut.conj k').toMonoidHom ≠ L.map (MulAut.conj k).toMonoidHom
  · obtain ⟨k', hk', h02, h12⟩ := h3b
    exact h.false_of_three_blocks hB3 hb h84 h85 h86 hD2 he hL hRE hk hk' hne h02 h12
  · push Not at h3b
    exact h.false_of_two_blocks hb h84 h86 hD2 hL hRE hk hne fun k' hk' =>
      (em _).imp_right (h3b k' hk')

end CFSG.AGLEmbedding
