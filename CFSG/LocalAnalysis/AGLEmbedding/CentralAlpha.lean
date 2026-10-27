module

public import CFSG.LocalAnalysis.AGLEmbedding.CentralAlphaAux
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentCase
import CFSG.Goldschmidt.Steps.Sec82PGroup
public import CFSG.LocalAnalysis.AGLEmbedding.KFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

namespace ReducedNongeneration

variable {p : ℕ} {X : Type} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

theorem not_isCyclic_inf_of_mem (h : ReducedNongeneration p X R X₀) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hzK : z ∈ K) :
    ¬ IsCyclic ((R : Subgroup X) ⊓ K : Subgroup X) := by
  rcases h.mem_or_rankOne_of_center hz hzp hK with ⟨-, hnc⟩ | ⟨hzK', -⟩
  · exact hnc
  · exact (hzK' hzK).elim

theorem isCyclic_map_center (h : ReducedNongeneration p X R X₀) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hKn : K.Normal) :
    IsCyclic ((Subgroup.center K).map K.subtype) := by
  have : IsCyclic (CFSG.pCore p X) := h.isCyclic_pCore_of_component hK
  have hle : (Subgroup.center K).map K.subtype ≤ CFSG.pCore p X := le_sSup ⟨normal_map_center hKn,
    (isPGroup_center_of_isComponentOf h.prime h.core_eq_bot hK).map K.subtype⟩
  exact Subgroup.isCyclic_of_le hle

theorem isCyclic_center (h : ReducedNongeneration p X R X₀) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hKn : K.Normal) : IsCyclic (Subgroup.center K) := by
  have := h.isCyclic_map_center hK hKn
  exact isCyclic_of_surjective (Subgroup.equivMapOfInjective _ _ K.subtype_injective).symm
    (MulEquiv.surjective _)

theorem mem_zpowers_of_mem_inf_centralizer (h : ReducedNongeneration p X R X₀) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hKn : K.Normal) (hzK : z ∈ K) :
    ∀ c ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), orderOf c = p →
      c ∈ Subgroup.zpowers z := by
  intro c hc hcp
  have hzZ : z ∈ (Subgroup.center K).map K.subtype :=
    ⟨⟨z, hzK⟩, Subgroup.mem_center_iff.mpr fun k => Subtype.ext (Subgroup.mem_center_iff.mp hz k),
      rfl⟩
  have := h.isCyclic_map_center hK hKn
  rcases h.rankOne_or_center hK (h.not_isCyclic_inf_of_mem hz hzp hK hzK) with
    ⟨-, -, -, -, -, -, -, -, hZ⟩ | hall
  · exact (center_ne_bot_of_mem h.prime hz hzp hzK hZ).elim
  · exact mem_zpowers_of_orderOf_eq_of_isCyclic (hall c hc hcp) hzZ (by rw [hcp, hzp])

theorem pRank_inf_centralizer_le_one (h : ReducedNongeneration p X R X₀) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hKn : K.Normal) (hzK : z ∈ K) :
    Open.pRank p ((R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X)) ≤ 1 := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hE, hEel, hEcard⟩ :=
    pRank_attained p hp ((R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X))
  have hEz : E ≤ Subgroup.zpowers z := by
    intro e he
    by_cases he1 : e = 1
    · rw [he1]
      exact Subgroup.one_mem _
    · exact h.mem_zpowers_of_mem_inf_centralizer hz hzp hK hKn hzK e (hE he)
        (orderOf_eq_prime (hEel.2 e he) he1)
  have hcard := Subgroup.card_le_of_le hEz
  rw [hEcard, Nat.card_zpowers, hzp] at hcard
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp (by rwa [pow_one])

theorem false_of_pRank_mulAut_le_two (h : ReducedNongeneration p X R X₀)
    (hR4 : 4 ≤ Open.pRank p (R : Subgroup X)) {z : X} (hz : z ∈ Subgroup.center X)
    (hzp : orderOf z = p) {K : Subgroup X} (hK : IsComponentOf K ⊤) (hKn : K.Normal)
    (hzK : z ∈ K) (hb : Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2) : False := by
  have hp := h.prime
  have hineq := pRank_le_pRank_inf_centralizer_add_pRank_map_conjNormal hp K (R : Subgroup X)
  have h1 := h.pRank_inf_centralizer_le_one hz hzp hK hKn hzK
  have h2 := (PreuniquenessRankFour.Helpers.pRank_mono p hp
    (le_top : (R : Subgroup X).map (MulAut.conjNormal (H := K)) ≤ ⊤)).trans hb
  omega

theorem false_of_three_le_pRank_of_le (h : ReducedNongeneration p X R X₀) {K : Subgroup X}
    (hKn : K.Normal) (hKX₀ : K ≤ X₀) (h3 : 3 ≤ Open.pRank p (⊤ : Subgroup K)) : False := by
  have h2 := h.pRank_le_two_of_normal_le hKX₀
  rw [← pRank_map_of_injective p h.prime K.subtype K.subtype_injective, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h3
  omega

theorem le_of_glbCore_eq_top (h : ReducedNongeneration p X R X₀) {K : Subgroup X}
    {T : Subgroup K} (hT : T.map K.subtype = (R : Subgroup X) ⊓ K) (hc : GLBCore p 3 T = ⊤) :
    K ≤ X₀ := by
  have hp := h.prime
  have hle : GLBCore p 3 T ≤ X₀.comap K.subtype := by
    refine sSup_le ?_
    rintro N ⟨Q, hQT, hQ3, rfl⟩ k hk
    have hQR : Q.map K.subtype ≤ R := (Subgroup.map_mono hQT).trans (hT.le.trans inf_le_left)
    have hQ3' : 3 ≤ Open.pRank p (Q.map K.subtype) := by
      rw [pRank_map_of_injective p hp K.subtype K.subtype_injective]
      exact hQ3
    exact h.weakCore_le (normalizer_le_weakCore p hQR (by omega)
      (hQ3'.trans (PreuniquenessRankFour.Helpers.pRank_mono p hp le_sup_left))
      (Subgroup.le_normalizer_map K.subtype ⟨k, hk, rfl⟩))
  intro x hx
  exact hle (hc ▸ Subgroup.mem_top (⟨x, hx⟩ : K))

theorem mem_of_conjNormal_apply_eq (h : ReducedNongeneration p X R X₀) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X} [K.Normal]
    {A : Subgroup X} (hAR : A ≤ R) (hA : IsElemAbelian p A) (hA3 : 3 ≤ Open.pRank p A)
    {f : X} (hfA : f ∈ A) (hf : MulAut.conjNormal (H := K) f ≠ 1) {k : K}
    (hk : MulAut.conjNormal (H := K) f k = k) : (k : X) ∈ X₀ := by
  have hp := h.prime
  have hfC : f ∉ Subgroup.centralizer (K : Set X) := fun hfC =>
    hf (by rwa [← MonoidHom.mem_ker, ker_conjNormal_eq_centralizer])
  have hfz : f ∉ Subgroup.zpowers z := fun hfz =>
    hfC (Subgroup.zpowers_le.mpr (Subgroup.center_le_centralizer _ hz) hfz)
  have hQR : Subgroup.zpowers z ⊔ Subgroup.zpowers f ≤ R :=
    sup_le (Subgroup.zpowers_le.mpr (mem_sylow_of_mem_center hz hzp R))
      (Subgroup.zpowers_le.mpr (hAR hfA))
  have hQ2 : 2 ≤ Open.pRank p (Subgroup.zpowers z ⊔ Subgroup.zpowers f) :=
    two_le_pRank_of_commute_of_not_mem_zpowers hp hzp (hA.2 f hfA) hfz
      (Subgroup.mem_center_iff.mp hz f).symm (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers f))
  have hAQ : A ≤ Subgroup.centralizer
      ((Subgroup.zpowers z ⊔ Subgroup.zpowers f : Subgroup X) : Set X) := by
    rw [Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.zpowers_le.mpr (Subgroup.center_le_centralizer _ hz))
      (Subgroup.zpowers_le.mpr (Subgroup.le_centralizer_iff_isMulCommutative.mpr hA.1 hfA))
  have hN := (normalizer_le_weakCore p hQR hQ2 (hA3.trans
    (PreuniquenessRankFour.Helpers.pRank_mono p hp ((le_inf hAR hAQ).trans le_sup_right)))).trans
    h.weakCore_le
  have hfk : f * k * f⁻¹ = k := by
    rw [← MulAut.conjNormal_apply, hk]
  have hQk : Subgroup.zpowers z ⊔ Subgroup.zpowers f ≤ Subgroup.centralizer {(k : X)} :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_center_iff.mp hz k).symm))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
        (mul_inv_eq_iff_eq_mul.mp hfk)))
  exact hN (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.mp (hQk hq)))

theorem le_of_kGenThree (h : ReducedNongeneration p X R X₀)
    (hR4 : 4 ≤ Open.pRank p (R : Subgroup X)) {z : X} (hz : z ∈ Subgroup.center X)
    (hzp : orderOf z = p) {K : Subgroup X} (hK : IsComponentOf K ⊤) (hKn : K.Normal)
    (hzK : z ∈ K) (hgen : KGenThree p K) : K ≤ X₀ := by
  have hp := h.prime
  obtain ⟨A, hAR, hA, hAcard⟩ := pRank_attained p hp (R : Subgroup X)
  have hA4 : 4 ≤ Open.pRank p A :=
    hR4.trans (le_csSup (pRank_bddAbove p hp A) ⟨A, le_rfl, hA, hAcard⟩)
  have hineq := pRank_le_pRank_inf_centralizer_add_pRank_map_conjNormal hp K A
  have hAC : Open.pRank p (A ⊓ Subgroup.centralizer (K : Set X)) ≤ 1 :=
    (PreuniquenessRankFour.Helpers.pRank_mono p hp (inf_le_inf_right _ hAR)).trans
      (h.pRank_inf_centralizer_le_one hz hzp hK hKn hzK)
  have hgen' := hgen (A.map (MulAut.conjNormal (H := K))) (elementary_abelian_map p hA _)
    (by omega)
  intro x hx
  have hxmem : (⟨x, hx⟩ : K) ∈ Subgroup.closure
      {k : K | ∃ e ∈ A.map (MulAut.conjNormal (H := K)), e ≠ 1 ∧ e k = k} :=
    hgen' ▸ Subgroup.mem_top _
  refine (Subgroup.closure_le (X₀.comap K.subtype)).mpr ?_ hxmem
  rintro k ⟨_, ⟨f, hfA, rfl⟩, hf, hk⟩
  exact h.mem_of_conjNormal_apply_eq hz hzp hAR hA (by omega) hfA hf hk

theorem centralizer_le_of_not_isCyclic (h : ReducedNongeneration p X R X₀) {K : Subgroup X}
    (hKn : K.Normal) (hnc : ¬ IsCyclic ((R : Subgroup X) ⊓ K : Subgroup X)) :
    Subgroup.centralizer (K : Set X) ≤ X₀ := by
  have hp := h.prime
  have hRN : (R : Subgroup X) ≤
      Subgroup.normalizer (((R : Subgroup X) ⊓ K : Subgroup X) : Set X) :=
    (le_inf Subgroup.le_normalizer (by rw [Subgroup.normalizer_eq_top]; exact le_top)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  obtain ⟨V, hVRK, hRV, hVcard, hVp, hVab⟩ :=
    CFSG.Goldschmidt.Sec82.exists_normal_plane_le_of_le hp h.ne_two R.isPGroup' inf_le_left hRN
      hnc
  have hV : IsElemAbelian p V := ⟨⟨⟨fun x y => Subtype.ext (hVab x x.2 y y.2)⟩⟩, hVp⟩
  obtain ⟨A, hAR, hA, hAcard⟩ := pRank_attained p hp (R : Subgroup X)
  have hN := normalizer_le_of_elementary_rank_two_normalized_by_rank_three p hp R h.sylow_le
    h.weakCore_le hA _ h.three_le_pRank hAcard (hAR.trans h.sylow_le) hV hVcard
    ((hVRK.trans inf_le_left).trans h.sylow_le) (hAR.trans hRV)
  exact ((Subgroup.centralizer_le (hVRK.trans inf_le_right)).trans
    (Subgroup.centralizer_le_normalizer _)).trans hN

theorem false_of_normal_of_pow_mem (h : ReducedNongeneration p X R X₀) {N W : Subgroup X}
    [N.Normal] [W.Normal] (hNX₀ : N ≤ X₀) (hRW : (R : Subgroup X) ≤ W)
    (hW : ∀ w ∈ W, ∃ k : ℕ, w ^ p ^ k ∈ N) : False := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  refine not_le_of_normalizer_inf_le R ?_ h.ne_top
    ((le_sylow_sup_of_pow_mem R hW).trans (sup_le h.sylow_le hNX₀))
  rw [inf_eq_left.mpr hRW]
  exact (normalizer_le_weakCore_of_rank p hp _ h.three_le_pRank).trans h.weakCore_le

theorem false_of_kOutNormalSylow (h : ReducedNongeneration p X R X₀) {K : Subgroup X}
    [K.Normal] (hKX₀ : K ≤ X₀) (hCX₀ : Subgroup.centralizer (K : Set X) ≤ X₀)
    (hout : KOutNormalSylow p K) : False := by
  have : (MulAut.conj : K →* MulAut K).range.Normal := normal_range_mulAutConj K
  obtain ⟨S, hS⟩ := (R.isPGroup'.map (MulAut.conjNormal (H := K))).exists_le_sylow
  have := (hout S).comap (MulAut.conjNormal (H := K))
  refine h.false_of_normal_of_pow_mem
    (N := (MulAut.conj : K →* MulAut K).range.comap (MulAut.conjNormal (H := K)))
    (W := ((MulAut.conj : K →* MulAut K).range ⊔ (S : Subgroup (MulAut K))).comap
      (MulAut.conjNormal (H := K)))
    (comap_range_conj_le hKX₀ hCX₀) (fun r hr => Subgroup.mem_sup_right (hS ⟨r, hr, rfl⟩))
    fun w hw => ?_
  obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup S.isPGroup' hw
  exact ⟨k, by rw [Subgroup.mem_comap, map_pow]; exact hk⟩

theorem outTwo_of_mem (h : ReducedNongeneration p X R X₀)
    (hR4 : 4 ≤ Open.pRank p (R : Subgroup X)) (hX : CatalogSimpleSections X) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hKn : K.Normal) (hzK : z ∈ K) (hKF : KFactAlpha) :
    (∀ c ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), orderOf c = p →
        c ∈ Subgroup.zpowers z) ∧
      KOutTwoGroup K ∧
      ((∃ A : Subgroup X, A ≤ (R : Subgroup X) ⊓ K ∧
          A ≤ Subgroup.centralizer (((R : Subgroup X) ⊓ K : Subgroup X) : Set X) ∧
          IsElemAbelian p A ∧ Nat.card A = p ^ 2) ∨
        ((∀ t ∈ (R : Subgroup X) ⊓ K, t ^ p = 1) ∧
          Open.pRank p ((R : Subgroup X) ⊓ K) ≤ 3) ∨
        (∃ A : Subgroup X, A ≤ (R : Subgroup X) ⊓ K ∧
          (R : Subgroup X) ⊓ K ≤ Subgroup.normalizer (A : Set X) ∧ IsElemAbelian p A ∧
          p ^ (p + 1) ≤ Nat.card A)) := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hnc := h.not_isCyclic_inf_of_mem hz hzp hK hzK
  obtain ⟨T, hT⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal R
    (ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
      Subgroup.IsSubnormal.top)
  refine ⟨h.mem_zpowers_of_mem_inf_centralizer hz hzp hK hKn hzK, ?_⟩
  rcases hKF K hK.2.2 (hX.isCatalogGroup_center_quotient hK) p hp h.ne_two
      (center_ne_bot_of_mem hp hz hzp hzK) (isPGroup_center_of_isComponentOf hp h.core_eq_bot hK)
      (h.isCyclic_center hK hKn) T with
    ⟨hgen, h3 | hout⟩ | hb | ⟨hc, h3⟩ | ⟨h2, hd⟩
  · exact (h.false_of_three_le_pRank_of_le hKn (h.le_of_kGenThree hR4 hz hzp hK hKn hzK hgen)
      h3).elim
  · exact (h.false_of_kOutNormalSylow (h.le_of_kGenThree hR4 hz hzp hK hKn hzK hgen)
      (h.centralizer_le_of_not_isCyclic hKn hnc) hout).elim
  · exact (h.false_of_pRank_mulAut_le_two hR4 hz hzp hK hKn hzK hb).elim
  · exact (h.false_of_three_le_pRank_of_le hKn (h.le_of_glbCore_eq_top hT hc) h3).elim
  · refine ⟨h2, ?_⟩
    rw [← hT]
    rcases hd with hd | hd | hd
    · exact Or.inl (exists_map_of_exists_centralizer hd)
    · exact Or.inr (Or.inl (pow_and_pRank_map hp hd))
    · exact Or.inr (Or.inr (exists_map_of_exists_normalizer hd))

end ReducedNongeneration

end CFSG.AGLEmbedding
