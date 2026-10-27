module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.LieCross

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def IsD2LieCharSmall (p : ℕ) (d : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = p ∧
    ((q.exponent ≤ 2 ∧ d = .A 1 q) ∨ (q.exponent = 1 ∧ (d = .A 2 q ∨ d = .twistedA 2 q)))

@[expose] def KFactLieCharRank : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex),
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → ∀ p : ℕ, p.Prime → p ≠ 2 →
    p = d.1.characteristic → ¬ IsD2LieCharSmall p d.1 → 3 ≤ Open.pRank p (⊤ : Subgroup K)

@[expose] def KFactLieCharOut : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex),
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → ∀ p : ℕ, p.Prime → p ≠ 2 →
    IsD2LieCharSmall p d.1 → ¬ p ∣ Nat.card (Outer K)

@[expose] def KFactLinTwoPrimeRank : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex),
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → ∀ p : ℕ, p.Prime → p ≠ 2 →
    (∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ d.1 = .A 1 q) →
    Open.pRank p (⊤ : Subgroup K) ≤ 1

@[expose] def KFactLinThreeCore : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex),
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → ∀ p : ℕ, p.Prime → p ≠ 2 →
    (∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ d.1 = .A 2 q) →
    ∀ T : Sylow p K, GLBCore p 2 (T : Subgroup K) = ⊤

@[expose] def D2CaseL2Square : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.exponent = 2 ∧ d.1 = .A 1 q) →
    D2IndexCaseAt (.lie d) fun p => p = d.1.characteristic

@[expose] def D2CaseU3 : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex,
    (∃ q : TauCeti.PrimePower, q.exponent = 1 ∧ d.1 = .twistedA 2 q) →
    D2IndexCaseAt (.lie d) fun p => p = d.1.characteristic

variable {X : Type*} [Group X] [Finite X] {p : ℕ} {R : Sylow p X} {A X₀ K : Subgroup X}

theorem D2AlmostSimple.sylow_le_of_not_dvd_card_outer (h : D2AlmostSimple p X R A X₀ K)
    (hout : ¬ p ∣ Nat.card (Outer K)) : (R : Subgroup X) ≤ K := by
  have : K.Normal := h.normal
  intro r hr
  obtain ⟨k, hk⟩ := R.isPGroup' ⟨r, hr⟩
  have hrk : r ^ p ^ k = 1 := congrArg Subtype.val hk
  let ψ : X →* Outer K := (QuotientGroup.mk' (inner K)).comp (MulAut.conjNormal (H := K))
  have hcop : (p ^ k).Coprime (Nat.card (Outer K)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd h.prime).mpr hout)
  have hψ : ψ r = 1 :=
    (pow_eq_one_iff_of_coprime hcop).mp
      ⟨by rw [← map_pow, hrk, map_one], pow_card_eq_one'⟩
  obtain ⟨c, hc⟩ := (QuotientGroup.eq_one_iff _).mp hψ
  have hcent : (c : X)⁻¹ * r ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hc ⟨x, hx⟩)
    rw [MulAut.conjNormal_apply] at h1
    change (c : X) * x * (c : X)⁻¹ = r * x * r⁻¹ at h1
    calc x * ((c : X)⁻¹ * r) = (c : X)⁻¹ * ((c : X) * x * (c : X)⁻¹) * r := by group
      _ = (c : X)⁻¹ * (r * x * r⁻¹) * r := by rw [h1]
      _ = (c : X)⁻¹ * r * x := by group
  rw [h.centralizer_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at hcent
  exact hcent ▸ c.2

theorem D2AlmostSimple.pRank_top (h : D2AlmostSimple p X R A X₀ K) :
    Open.pRank p (⊤ : Subgroup X) = 2 := by
  rw [← pRank_sylow_eq_globalRank p h.prime R]
  exact h.pRank_eq

theorem pRank_top_subgroup_eq (hp : p.Prime) (S : Subgroup X) :
    Open.pRank p (⊤ : Subgroup S) = Open.pRank p S := by
  have h := CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp S.subtype
    S.subtype_injective ⊤
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h.symm

theorem D2AlmostSimple.false_of_three_le_pRank (h : D2AlmostSimple p X R A X₀ K)
    (h3 : 3 ≤ Open.pRank p (⊤ : Subgroup K)) : False := by
  have h1 : Open.pRank p K ≤ Open.pRank p (⊤ : Subgroup X) :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_mono p h.prime le_top
  rw [pRank_top_subgroup_eq h.prime] at h3
  have h2 := h.pRank_top
  omega

theorem D2AlmostSimple.two_le_pRank_of_sylow_le (h : D2AlmostSimple p X R A X₀ K)
    (hRK : (R : Subgroup X) ≤ K) : 2 ≤ Open.pRank p (⊤ : Subgroup K) := by
  rw [pRank_top_subgroup_eq h.prime]
  exact (le_pRank_of_isElemAbelian h.prime h.elem h.card_A).trans
    (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p h.prime (h.A_le.trans hRK))

theorem D2AlmostSimple.le_of_glbCore_eq_top (h : D2AlmostSimple p X R A X₀ K) {T : Subgroup K}
    (hTp : IsPGroup p T) (hTR : T.map K.subtype ≤ R) (hcore : GLBCore p 2 T = ⊤) : K ≤ X₀ := by
  have hle : GLBCore p 2 T ≤ X₀.subgroupOf K := by
    rw [fullCore_le_iff]
    intro Y hYT hY2 n hn
    have hYp : IsPGroup p (Y.map K.subtype) := (hTp.to_le hYT).map K.subtype
    have hY2' : 2 ≤ Open.pRank p (Y.map K.subtype) := by
      rwa [CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p h.prime K.subtype
        K.subtype_injective Y]
    have hYX : Y.map K.subtype ≤ X₀ := (Subgroup.map_mono hYT).trans (hTR.trans h.sylow_le)
    exact h.normalizer_le_of_rank _ hYX hYp hY2' (Subgroup.le_normalizer_map K.subtype ⟨n, hn, rfl⟩)
  rw [hcore, top_le_iff, Subgroup.subgroupOf_eq_top] at hle
  exact hle

theorem d2IndexCaseAt_lie_char_of (hrank : KFactLieCharRank) (hout : KFactLieCharOut)
    (hL2 : KFactLinTwoPrimeRank) (hL3 : KFactLinThreeCore) (hsq : D2CaseL2Square)
    (hU3 : D2CaseU3) (d : TauCeti.ValidLieTypeIndex) :
    D2IndexCaseAt (.lie d) fun p => p = d.1.characteristic := by
  intro G _ _ hglob hD1 p hp P M A H R hesc hmax hβ Rbar K hRbar hK ⟨e⟩
  by_cases hsmall : IsD2LieCharSmall p d.1
  · have hRK := hK.sylow_le_of_not_dvd_card_outer (hout K d ⟨e⟩ p hK.prime hK.ne_two hsmall)
    obtain ⟨q, hqp, hq⟩ := hsmall
    rcases hq with ⟨hq2, hd⟩ | ⟨hq1, hd | hd⟩
    · rcases (show q.exponent = 1 ∨ q.exponent = 2 by have := q.exponent_pos; omega) with h1 | h2
      · have := hL2 K d ⟨e⟩ p hK.prime hK.ne_two ⟨q, hqp, h1, hd⟩
        have := hK.two_le_pRank_of_sylow_le hRK
        omega
      · exact hsq d ⟨q, h2, hd⟩ G hglob hD1 p hp P M A H R hesc hmax hβ Rbar K hRbar hK ⟨e⟩
    · refine hK.not_le (hK.le_of_glbCore_eq_top (Rbar.subtype hRK).isPGroup' ?_
        (hL3 K d ⟨e⟩ p hK.prime hK.ne_two ⟨q, hqp, hq1, hd⟩ (Rbar.subtype hRK)))
      rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hRK]
    · exact hU3 d ⟨q, hq1, hd⟩ G hglob hD1 p hp P M A H R hesc hmax hβ Rbar K hRbar hK ⟨e⟩
  · exact hK.false_of_three_le_pRank (hrank K d ⟨e⟩ p hK.prime hK.ne_two hp hsmall)

end CFSG.AGLEmbeddingD2
