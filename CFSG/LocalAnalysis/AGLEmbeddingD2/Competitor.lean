module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Assembly
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTheoremZ

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

section Ncl

variable {G : Type} [Group G]

theorem nclIn_le_nclIn_of_isSylow {p : ℕ} [Fact p.Prime] {H X H' : Subgroup G} (hXH : X ≤ H)
    (hX : IsPGroup p X) (hXs : p.Coprime (X.relIndex H)) (hJH' : nclIn H X ≤ H') :
    nclIn H X ≤ nclIn H' X := by
  set J := nclIn H X
  have hXJ : X ≤ J := le_nclIn hXH
  have hJH : J ≤ H := nclIn_le_self H X
  have hXJs : p.Coprime (X.relIndex J) :=
    Nat.Coprime.coprime_dvd_right (Dvd.intro _ (Subgroup.relIndex_mul_relIndex X J H hXJ hJH))
      hXs
  have hcop : p.Coprime ((nclIn J X).relIndex J) :=
    Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ (Subgroup.relIndex_mul_relIndex X _ _
      (le_nclIn hXJ) (nclIn_le_self _ X))) hXJs
  have hconj : ∀ c ∈ H, ∀ x ∈ X, c * x * c⁻¹ ∈ nclIn J X := by
    intro c hc x hx
    obtain ⟨k, hk⟩ := hX ⟨x, hx⟩
    have hxk : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine mem_of_pow_eq_one_of_coprime_relIndex (nclIn_le_self _ X) (le_normalizer_nclIn _ X)
      hcop ((Subgroup.mem_normalizer_iff.mp (le_normalizer_nclIn H X hc) x).mp (hXJ hx)) (k := k)
      ?_
    rw [conj_pow, hxk, mul_one, mul_inv_cancel]
  have hJJ : J ≤ nclIn J X := by
    rintro _ ⟨y, hy, rfl⟩
    have hcl : Subgroup.normalClosure ((X.subgroupOf H : Subgroup H) : Set H) ≤
        (nclIn J X).subgroupOf H := by
      show Subgroup.closure (Group.conjugatesOfSet _) ≤ _
      rw [Subgroup.closure_le]
      intro z hz
      obtain ⟨b, hb, hbz⟩ := Group.mem_conjugatesOfSet_iff.mp hz
      obtain ⟨c, rfl⟩ := isConj_iff.mp hbz
      exact hconj c c.2 b hb
    exact hcl hy
  exact hJJ.trans (nclIn_le_nclIn_of_le hXJ hJH')

end Ncl

section Reduced

variable {X : Type*} [Group X] [Finite X] {p : ℕ} {R : Sylow p X} {A X₀ K : Subgroup X}

theorem D2AlmostSimple.le_of_normal (h : D2AlmostSimple p X R A X₀ K) {W : Subgroup X}
    (hW : W.Normal) (hW1 : W ≠ ⊥) : K ≤ W := by
  have hKn := h.normal
  have hq : IsSimpleGroup (K ⧸ Subgroup.center K) := h.component.2.2.2
  have : IsSimpleGroup K := ((QuotientGroup.quotientMulEquivOfEq h.center_eq_bot).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W.subgroupOf K) with hb | ht
  · exfalso
    apply hW1
    have hWK : W ⊓ K = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx.2⟩ : K) ∈ W.subgroupOf K := hx.1
      rw [hb] at this
      simpa using congrArg Subtype.val ((Subgroup.mem_bot).mp this)
    have hcomm : ⁅W, K⁆ = ⊥ := by
      rw [eq_bot_iff, ← hWK]
      exact Subgroup.commutator_le_inf W K
    rw [eq_bot_iff, ← h.centralizer_eq_bot]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomm
  · intro x hx
    have : (⟨x, hx⟩ : K) ∈ W.subgroupOf K := ht ▸ Subgroup.mem_top _
    exact this

end Reduced

section Competitor

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M A H R : Subgroup G}

theorem D2Escape.not_le_of_nclIn_le (h : D2Escape p P M A H R) (hglob : AGLGlobal G)
    {H' : Subgroup G} (hJH' : nclIn H A ≤ H') : ¬ H' ≤ M := by
  intro hH'M
  obtain ⟨Rbar, K, -, hK⟩ := h.almostSimple hglob
  have hAH : A ≤ H := h.A_le.trans h.le_H
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  have hJn : (((nclIn H A).subgroupOf H).map π).Normal :=
    (nclIn_normal H A).map π (QuotientGroup.mk'_surjective _)
  have hJ1 : ((nclIn H A).subgroupOf H).map π ≠ ⊥ := by
    intro hbot
    have hle : (A.subgroupOf H).map π ≤ ⊥ :=
      hbot ▸ Subgroup.map_mono (Subgroup.subgroupOf_mono H (le_nclIn hAH))
    have hc := hK.card_A
    rw [le_bot_iff.mp hle, Subgroup.card_bot] at hc
    have := Nat.one_lt_pow two_ne_zero h.prime.one_lt
    omega
  apply hK.not_le
  refine (hK.le_of_normal hJn hJ1).trans (Subgroup.map_mono (Subgroup.subgroupOf_mono H ?_))
  exact le_inf (nclIn_le_self H A) (hJH'.trans hH'M)

theorem D2Escape.exists_of_maxTwoLocal (h : D2Escape p P M A H R) (hD1p : D1At G p)
    {H' : Subgroup G} (hH' : GLBIsMaxTwoLocal H') (hAH' : A ≤ H') (hH'M : ¬ H' ≤ M) :
    ∃ R' : Subgroup G, D2Escape p P M A H' R' ∧ A ≤ R' := by
  have hprime : p.Prime := h.prime
  have : Fact p.Prime := ⟨hprime⟩
  have hArank : 2 ≤ Open.pRank p A := le_pRank_of_isElemAbelian hprime h.elem h.card_A
  have hrank₁ : Open.pRank p (H' ⊓ M) ≤ 2 := by
    by_contra hlt
    exact hH'M (hD1p P M h.maxTwoLocal_M
      ((weakCore_le_fullCore p (P : Subgroup G)).trans h.core_le) H' hH'.1 (by omega))
  have hApGroup : IsPGroup p A := h.isPGroup.to_le h.A_le
  obtain ⟨T, hT⟩ := (hApGroup.comap_subtype (K := H')).exists_le_sylow
  set R' := (T : Subgroup H').map H'.subtype with hR'
  have hAR' : A ≤ R' := by
    rw [hR', ← Subgroup.map_subgroupOf_eq_of_le hAH']
    exact Subgroup.map_mono hT
  have hR'p : IsPGroup p R' := T.isPGroup'.map H'.subtype
  have hAM : A ≤ M := h.A_le.trans h.le_M
  have hR'M : R' ≤ M := by
    refine le_of_normalizer_inf_le hR'p fun x hx => ?_
    refine normalizer_le_of_core hprime P h.sylow_le h.core_le inf_le_right
      (hR'p.to_le inf_le_left) ?_ hx.2
    exact hArank.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hprime (le_inf hAR' hAM))
  have hR'H' : R' ≤ H' := Subgroup.map_subtype_le _
  refine ⟨R', ?_, hAR'⟩
  exact {
    prime := hprime
    ne_two := h.ne_two
    sylow_le := h.sylow_le
    core_le := h.core_le
    maxTwoLocal_M := h.maxTwoLocal_M
    maxTwoLocal_H := hH'
    elem := h.elem
    card_A := h.card_A
    core_A := h.core_A
    A_le := hAR'
    le_H := hR'H'
    le_M := hR'M
    isSylow := ⟨T, rfl⟩
    pRank_eq := le_antisymm
      ((CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hprime (le_inf hR'H' hR'M)).trans hrank₁)
      (hArank.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hprime hAR'))
    not_le := hH'M }

theorem D2Escape.eq_of_maxTwoLocal (h : D2Escape p P M A H A) (hmax : D2EscapeMax p P M A)
    (hD1p : D1At G p) {H' : Subgroup G} (hH' : GLBIsMaxTwoLocal H') (hAH' : A ≤ H')
    (hH'M : ¬ H' ≤ M) : D2Escape p P M A H' A := by
  obtain ⟨R', h', hAR'⟩ := h.exists_of_maxTwoLocal hD1p hH' hAH' hH'M
  have hR'A : R' = A := (Subgroup.eq_of_le_of_card_ge hAR' (hmax A H' R' h')).symm
  exact hR'A ▸ h'

theorem D2Escape.coprime_relIndex (h : D2Escape p P M A H A) : p.Coprime (A.relIndex H) := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨T, hT⟩ := h.isSylow
  have hTA : (T : Subgroup H) = A.subgroupOf H := by
    rw [← hT, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  rw [Subgroup.relIndex, ← hTA]
  exact (Nat.Prime.coprime_iff_not_dvd h.prime).mpr T.not_dvd_index

theorem false_of_survivorsAt (hglob : AGLGlobal G) (hD1p : D1At G p)
    (h84 : Asc81bEightFour) (hCGT : AschbacherLocalCGTBlock) (hD2 : NoXBlockFor G)
    (h : D2Escape p P M A H A) (hmax : D2EscapeMax p P M A)
    (hsurv : ∀ H' : Subgroup G, D2Escape p P M A H' A → AGLSurvivorData p M H' A A)
    (hO : CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥) : False := by
  have : Fact p.Prime := ⟨h.prime⟩
  refine false_of_aglSurvivorsOn h84 hCGT hD2 (C := fun H' => D2Escape p P M A H' A) hsurv hO
    ?_ h
  intro H₁ h₁ H' hH' hJH' hAH'
  have hH'M : ¬ H' ≤ M := h₁.not_le_of_nclIn_le hglob hJH'
  refine ⟨h₁.eq_of_maxTwoLocal hmax hD1p hH' hAH' hH'M, ?_⟩
  exact nclIn_le_nclIn_of_isSylow (h₁.A_le.trans h₁.le_H) (h₁.isPGroup.to_le h₁.A_le)
    h₁.coprime_relIndex hJH'

end Competitor

end CFSG.AGLEmbeddingD2
