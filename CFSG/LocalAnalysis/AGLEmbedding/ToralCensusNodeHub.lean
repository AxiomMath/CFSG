module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeGroup
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeRoots
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase

public section

namespace CFSG.AGLEmbedding

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbedding.ToralCensus
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg

namespace ToralCensus

variable {Y : Type*} [Group Y] [Finite Y]

theorem false_of_commutes_of_cyclic {p : ℕ} (hp : p.Prime) {V A B : Subgroup Y}
    (hcyc : ∀ Q : Subgroup Y, Q ≤ V → IsPGroup p Q → IsCyclic Q) (hAV : A ≤ V)
    (hA : ⁅A, A⁆ = A) (hAB : Commutes A B) {x y : Y} (hx : x ∈ A) (hy : y ∈ B) (hyV : y ∈ V)
    (hxp : orderOf x = p) (hyp : orderOf y = p) : False := by
  have hxp' : x ^ p = 1 := by rw [← hxp]; exact pow_orderOf_eq_one x
  have hxy := mem_zpowers_of_commute_of_pow hcyc (hAV hx) hyV (hAB x hx y hy) hxp' hyp
  have hxB : x ∈ B := (Subgroup.zpowers_le.2 hy) hxy
  have h1 := eq_one_of_commute_of_perfect_cyclic hp hA (fun Q hQ => hcyc Q (hQ.trans hAV)) hx
    (fun a ha => hAB a ha x hxB) hxp'
  rw [h1, orderOf_one] at hxp
  exact hp.one_lt.ne hxp

end ToralCensus

open ToralCensus in
theorem hubSingleNode :
    ∀ {K Y : Type} [Group K] [Group Y] [Finite K] [Finite Y] {D : UniversalRootDatum K}
      {nW : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M q : ℕ},
      BorelQuotient D nW H π M → D.divisible = ∅ → 4 ≤ q → (∀ i, RankOneNode D i q) →
      ∀ p : ℕ, p.Prime → p ≠ 2 →
      (∀ i, ∃ x ∈ (rankOne D.rootGroup i).map π, orderOf x = p) →
      ∀ (S₀ : Sylow 2 Y) (J : Subgroup Y),
        Subgroup.normalizer ((S₀ : Subgroup Y) : Set Y) ≤ J →
        J ≠ Subgroup.normalizer ((S₀ : Subgroup Y) : Set Y) → J ≠ ⊤ → CycPerfect p J →
      ∀ u ∈ perfectJoin J, u ^ p = 1 → u ∉ Subgroup.center Y →
      ∃ π' : K →* Y, Function.Surjective π' ∧ π'.ker = π.ker ∧
        (S₀ : Subgroup Y) = (posUnipotent D).map π' ∧
        ∃ i ∈ negIndices D (J.comap π'),
          (∃ g ∈ J, g * u * g⁻¹ ∈ (rankOne D.rootGroup i).map π') ∧
          (negIndices D (J.comap π') = {i} ∨
            ∃ j : Fin D.rank, j ≠ i ∧ negIndices D (J.comap π') = {i, j} ∧
              D.cartan i j * D.cartan j i = 1) := by
  intro K Y _ _ _ _ D nW H π M q h hD hq4 hrank p hp hp2 hord S₀ J hNJ hJN _ hcyc u hu hup _
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq S₀
  have hQ : BorelQuotient D nW H π' M :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hBJ : (borel D H).map π' ≤ J := by
    rw [← hNπ]
    exact hNJ
  have hBA : borel D H ≤ J.comap π' := fun b hb => hBJ ⟨b, hb, rfl⟩
  have hne : J.comap π' ≠ borel D H := by
    intro he
    apply hJN
    rw [hNπ, ← he, Subgroup.map_comap_eq_self_of_surjective hπ']
  obtain ⟨i, hi⟩ := negIndices_nonempty_of_ne h.ct h.extras hBA hne
  set I := negIndices D (J.comap π') with hI
  set P := perfectJoin J with hP
  have hcycP : ∀ Q : Subgroup Y, Q ≤ P → IsPGroup p Q → IsCyclic Q :=
    hcyc P (perfectJoin_le J) (perfectJoin_perfect J)
  have hLJ : ∀ j ∈ I, (rankOne D.rootGroup j).map π' ≤ J := fun j hj =>
    (Subgroup.map_mono (rankOne_le_of_mem_negIndices hBA hj)).trans (Subgroup.map_comap_le _ _)
  have hperf : ∀ j, ⁅(rankOne D.rootGroup j).map π', (rankOne D.rootGroup j).map π'⁆ =
      (rankOne D.rootGroup j).map π' := fun j => by
    rw [← Subgroup.map_commutator, (hrank j).perfect hq4]
  have hLP : ∀ j ∈ I, (rankOne D.rootGroup j).map π' ≤ P := fun j hj =>
    le_perfectJoin (hLJ j hj) (hperf j)
  have hord' : ∀ j, ∃ k ∈ rankOne D.rootGroup j, orderOf (π' k) = p := fun j => by
    obtain ⟨_, ⟨k, hk, rfl⟩, hkp⟩ := hord j
    refine ⟨k, hk, ?_⟩
    rw [← hkp]
    refine orderOf_eq_orderOf_iff.2 fun m => ?_
    rw [← map_pow, ← map_pow, ← MonoidHom.mem_ker, ← MonoidHom.mem_ker, hker]
  have hconj : ∀ {c x : K}, π' c ∈ J → π' x ∈ P → orderOf (π' x) = p →
      π' (c * x * c⁻¹) ∈ P ∧ orderOf (π' (c * x * c⁻¹)) = p := fun {c x} hc hx hxp => by
    refine ⟨by simpa using conj_mem_perfectJoin hc hx, ?_⟩
    rw [map_mul, map_mul, map_inv, ← hxp]
    simpa using MulEquiv.orderOf_eq (MulAut.conj (π' c)) (π' x)
  have hnJ : ∀ j ∈ I, π' (nW j) ∈ J := fun j hj => hLJ j hj ⟨nW j, h.ct.n_mem j, rfl⟩
  have hpair : ∀ a ∈ I, ∀ b ∈ I, a ≠ b → D.cartan a b * D.cartan b a = 1 := by
    intro a ha b hb hab
    obtain ⟨ka, hka, hkap⟩ := hord' a
    obtain ⟨kb, hkb, hkbp⟩ := hord' b
    have hxa : π' ka ∈ P := hLP a ha ⟨ka, hka, rfl⟩
    have hxb : π' kb ∈ P := hLP b hb ⟨kb, hkb, rfl⟩
    have hB2 : ∀ l ∈ I, ∀ s ∈ I, l ≠ s → D.cartan l s = -1 → D.cartan s l = -2 → False := by
      intro l hl s hs hls h1 h2
      obtain ⟨k, hk, hkp⟩ := hord' l
      have hx : π' k ∈ P := hLP l hl ⟨k, hk, rfl⟩
      obtain ⟨hyP, hyp⟩ := hconj (hnJ s hs) hx hkp
      exact false_of_commutes_of_cyclic hp hcycP (hLP l hl) (hperf l)
        ((commutes_rankOne_bTwo h.ct h.extras hD hls h1 h2).map π') ⟨k, hk, rfl⟩
        ⟨_, ⟨k, hk, rfl⟩, rfl⟩ hyP hkp hyp
    have hG2 : ∀ l ∈ I, ∀ s ∈ I, l ≠ s → D.cartan l s = -1 → D.cartan s l = -3 → False := by
      intro l hl s hs hls h1 h2
      obtain ⟨k, hk, hkp⟩ := hord' l
      obtain ⟨k', hk', hk'p⟩ := hord' s
      have hx' : π' k' ∈ P := hLP s hs ⟨k', hk', rfl⟩
      obtain ⟨hyP, hyp⟩ := hconj (c := nW s * nW l)
        (by rw [map_mul]; exact J.mul_mem (hnJ s hs) (hnJ l hl)) hx' hk'p
      exact false_of_commutes_of_cyclic hp hcycP (hLP l hl) (hperf l)
        ((commutes_rankOne_gTwo_long h.ct h.extras hD hls h1 h2).map π') ⟨k, hk, rfl⟩
        ⟨_, ⟨k', hk', rfl⟩, rfl⟩ hyP hkp hyp
    rcases cartan_pair_cases D.isFiniteType hab with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (false_of_commutes_of_cyclic hp hcycP (hLP a ha) (hperf a)
        ((commutes_rankOne_of_cartan_eq_zero h.extras hab h1).map π') ⟨ka, hka, rfl⟩
        ⟨kb, hkb, rfl⟩ hxb hkap hkbp).elim
    · rw [h1, h2]
      norm_num
    · exact (hB2 a ha b hb hab h1 h2).elim
    · exact (hB2 b hb a ha (Ne.symm hab) h2 h1).elim
    · exact (hG2 a ha b hb hab h1 h2).elim
    · exact (hG2 b hb a ha (Ne.symm hab) h2 h1).elim
  have hthree : ∀ a ∈ I, ∀ b ∈ I, ∀ c ∈ I, a ≠ b → a ≠ c → b ≠ c → False := by
    intro a ha b hb c hc hab hac hbc
    have hab' := hpair a ha b hb hab
    have hac' := hpair a ha c hc hac
    have hbc' := hpair b hb c hc hbc
    have h0 := D.isFiniteType.apply_eq_zero_of_apply_ne_zero hab hac hbc
      (fun h0 => by rw [h0, zero_mul] at hab'; exact zero_ne_one hab')
      (fun h0 => by rw [h0, zero_mul] at hac'; exact zero_ne_one hac')
    rw [h0, zero_mul] at hbc'
    exact zero_ne_one hbc'
  obtain ⟨k, hk, hkp⟩ := hord' i
  obtain ⟨g, hgP, hg⟩ :=
    exists_conj_mem_zpowers_of_cyclic hp hcycP hu (hLP i hi ⟨k, hk, rfl⟩) hup hkp
  refine ⟨π', hπ', hker, hT, i, hi,
    ⟨g, perfectJoin_le J hgP, (Subgroup.zpowers_le.2 (Subgroup.mem_map_of_mem π' hk)) hg⟩, ?_⟩
  by_cases hall : ∀ j ∈ I, j = i
  · left
    ext j
    exact ⟨fun hj => hall j hj, fun hj => hj ▸ hi⟩
  · right
    push Not at hall
    obtain ⟨j, hj, hji⟩ := hall
    refine ⟨j, hji, ?_, hpair i hi j hj (Ne.symm hji)⟩
    ext c
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · by_contra hcon
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hcon
      exact hthree i hi j hj c hc (Ne.symm hji) (Ne.symm hcon.1) (Ne.symm hcon.2)
    · rcases hc with rfl | rfl
      exacts [hi, hj]

end CFSG.AGLEmbedding
