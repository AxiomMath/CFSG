module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L315Tools
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Props315b
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L32Full

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G] {𝒜 : Thm13Ambient}

omit [Finite G] in
theorem commutator_le_inf_of_le_normalizer {A B : Subgroup G} (hAB : A ≤ normalizer (B : Set G))
    (hBA : B ≤ normalizer (A : Set G)) : ⁅A, B⁆ ≤ A ⊓ B := by
  refine commutator_le.mpr fun a ha b hb => mem_inf.mpr ⟨?_, ?_⟩
  · have h1 : b * a⁻¹ * b⁻¹ ∈ A := (mem_normalizer_iff.mp (hBA hb) _).mp (inv_mem ha)
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    exact mul_mem ha (by simpa [mul_assoc] using h1)
  · have h1 : a * b * a⁻¹ ∈ B := (mem_normalizer_iff.mp (hAB ha) _).mp hb
    rw [commutatorElement_def]
    exact mul_mem h1 (inv_mem hb)

omit [Finite G] in
theorem le_normalizer_sup {A B X : Subgroup G} (hA : X ≤ normalizer (A : Set G))
    (hB : X ≤ normalizer (B : Set G)) : X ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    (mem_normalizer_iff_map_conj_eq.mp (hA hx)), (mem_normalizer_iff_map_conj_eq.mp (hB hx))]

theorem oddCoreIn_le_of_conjClosure_le {X C : Subgroup G} (hXL : X ≤ twoLayerIn C)
    (h : conjClosure X (twoLayerIn C) ≤ oddCoreIn (twoLayerIn C) ⊔ X) :
    oddCoreIn X ≤ oddCoreIn C := by
  set L := twoLayerIn C with hL
  set P := oddCoreIn L with hP
  set Y := conjClosure X L with hY
  have hPL : P ≤ L := map_subtype_le _
  have hXY : X ≤ Y := le_conjClosure X L
  set Z := P ⊔ X with hZ
  have hZY : Z = P ⊔ Y := le_antisymm (sup_le_sup_left hXY P) (sup_le le_sup_left h)
  have hLZ : L ≤ normalizer (Z : Set G) := by
    rw [hZY]
    exact le_normalizer_sup (le_normalizer_oddCoreIn L) (Sol78.le_normalizer_conjClosure X L)
  have hZL : Z ≤ L := sup_le hPL hXL
  have hPZ : P ≤ oddCoreIn Z := by
    have h1 := inf_le_oddCoreIn (coprime_card_oddCoreIn L) (hZL.trans (le_normalizer_oddCoreIn L))
    rwa [inf_eq_left.mpr le_sup_left] at h1
  have hXZ : X ⊔ oddCoreIn Z = Z :=
    le_antisymm (sup_le le_sup_right (map_subtype_le _))
      (sup_le (hPZ.trans le_sup_right) le_sup_left)
  have h1 := oddCoreIn_le_of_sup_eq (le_sup_right : X ≤ Z) hXZ
  have hOZ : L ≤ normalizer (oddCoreIn Z : Set G) := fun l hl =>
    mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn (hLZ hl))
  have h2 := inf_le_oddCoreIn (coprime_card_oddCoreIn Z) hOZ
  rw [inf_eq_left.mpr (show oddCoreIn Z ≤ L from (map_subtype_le _).trans hZL)] at h2
  exact (h1.trans h2).trans (oddCoreIn_twoLayerIn_le C)

omit [Finite G] in
theorem isElemAbelian_zpowers {x : G} (hx : x ^ 2 = 1) :
    CFSG.Open.IsElemAbelian 2 (zpowers x) := CFSG.Open.isElemAbelian_zpowers hx

theorem oddCoreIn_le_centralizer_of_315b (hm : Lemma32FullFor 𝒜) (hq : QuasisimpleTwoPartInput)
    (hKP : KStarKProper G) (hb : Lemma315bInputFor 𝒜) (hG : 𝒜 G) {N : Subgroup G}
    (hN : IsSolomonChoice N) {K' : Subgroup G} (hK' : K' ∈ kStarComponents N) :
    oddCoreIn K' ≤ centralizer (K' : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK, hKK'⟩ := exists_mem_kStarComponents_ne hN K'
  obtain ⟨B, hBK, hB, hBcard⟩ := SectionRank.exists_pRank (p := 2) (by norm_num) K
  have hB4 : 4 ≤ Nat.card B := by
    rw [hBcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 K :=
        Nat.pow_le_pow_right (by norm_num) (two_le_pRank_of_mem_solomonKStar hK.2)
  have hB2 : IsPGroup 2 B := IsPGroup.of_card hBcard
  have hBQ : B ≤ coreActionKernel K' := fun x hx => mem_coreActionKernel_of_ne hK hK' hKK' (hBK hx)
  have hK'q : IsQuasisimple (↥K' ⧸ pPrimeCore 2 ↥K') :=
    isQuasisimple_quotient_of_isPComponent hK'.1.1 hK'.1.2
  set Y := K' ⊓ centralizer (B : Set G) with hY
  have hcov := inf_centralizer_sup_oddCoreIn_eq hB2 hBQ
  obtain ⟨hJ2, hJL, hJsup, -⟩ := cover_facts hK'q inf_le_left hcov
  set J := oddResidualIn Y with hJ
  have hJres : oddResidualIn J = J := oddResidualIn_oddResidualIn Y
  have hJY : J ≤ Y := hJ2.1
  have hJK' : J ≤ K' := hJY.trans inf_le_left
  have hJperf : Group.IsPerfect ↥J :=
    Subgroup.isPerfect_iff.mpr (UnbalancedCorr.commutator_eq_of_isPComponent hJ2.1 hJ2.2)
  have hnc := exists_noncentral_involution_coreQuot hq hKP hK'.1 hK'.2
  have hK'res : oddResidualIn K' = K' := by
    obtain ⟨-, hL, -, -⟩ := cover_facts hK'q le_rfl (sup_eq_left.mpr (map_subtype_le _))
    rw [← hL, twoLayerIn_eq_self_of_isTwoComponentIn hK'.1]
  have key : ∀ e ∈ B, e ≠ 1 →
      twoLayerIn (K' ⊓ centralizer ({e} : Set G)) = J ∧
        oddCoreIn J ≤ oddCoreIn (centralizer ({e} : Set G)) ∧
        J ≤ centralizer (oddCoreIn (centralizer ({e} : Set G)) : Set G) := by
    intro e heB he1
    have he2 : orderOf e = 2 := orderOf_eq_prime (hB.2 e heB) he1
    have heK : e ∈ K := hBK heB
    have heQ := mem_coreActionKernel_of_ne hK hK' hKK' heK
    set Ce := centralizer ({e} : Set G) with hCe
    set P := oddCoreIn Ce with hP
    have hJCe : J ≤ Ce := hJY.trans (inf_le_right.trans
      (centralizer_le (Set.singleton_subset_iff.mpr heB)))
    have hJP : J ≤ normalizer (P : Set G) := hJCe.trans (le_normalizer_oddCoreIn Ce)
    have hJcen : J ≤ centralizer (P : Set G) := by
      refine le_of_forall_involution hJK' hJsup hJres hK'q hnc
        (le_normalizer_centralizer hJP) fun x hxJ hx2 => ?_
      have hx2' : x ^ 2 = 1 := by rw [← hx2, pow_orderOf_eq_one]
      have hV : zpowers x ≤ twoLayerIn Y := by
        rw [hJL]
        exact zpowers_le.mpr hxJ
      have hV1 : zpowers x ≠ ⊥ := fun h => by
        rw [zpowers_eq_bot] at h
        rw [h, orderOf_one] at hx2
        norm_num at hx2
      have h := (hb G hG N hN K hK K' hK' hKK' B hBK hB hB4 (zpowers x) hV
        (isElemAbelian_zpowers hx2') hV1 e heB he1).1
      have h1 : P ≤ centralizer (zpowers x : Set G) := commutator_eq_bot_iff_le_centralizer.mp h
      rw [← le_centralizer_iff] at h1
      exact h1 (mem_zpowers x)
    have hU2 : IsPGroup 2 (zpowers e) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, he2, pow_one])
    have hCzb : centralizer ((zpowers e : Subgroup G) : Set G) = Ce := by
      rw [zpowers_eq_closure, centralizer_closure]
    have hcove := inf_centralizer_sup_oddCoreIn_eq hU2 (zpowers_le.mpr heQ)
    rw [hCzb] at hcove
    obtain ⟨hX2, hXL, hXsup, -⟩ := cover_facts hK'q inf_le_left hcove
    obtain ⟨-, -, -, hX212, -⟩ := pump_facts hK' heQ he2
    set X := twoLayerIn (K' ⊓ Ce) with hX
    have h32 := hm G hG N hN K hK K' hK' hKK' e heK he2
    have hXLC : X ≤ twoLayerIn Ce := hX212.trans (solomonKStarOf_le_twoLayerIn Ce)
    have hOX : oddCoreIn X ≤ P := oddCoreIn_le_of_conjClosure_le hXLC h32
    have hJX : J ≤ X := by
      rw [hXL]
      refine closure_mono fun g hg => ⟨?_, hg.2⟩
      exact ⟨hg.1.1, centralizer_le (Set.singleton_subset_iff.mpr heB) hg.1.2⟩
    have hXK' : X ≤ K' := by rw [hXL]; exact hX2.1.trans inf_le_left
    have hXres : oddResidualIn X = X := by rw [hXL]; exact oddResidualIn_oddResidualIn _
    have hK'n : J ≤ normalizer (oddCoreIn K' : Set G) := hJK'.trans (le_normalizer_oddCoreIn K')
    have hXdec : X ≤ J ⊔ (X ⊓ oddCoreIn K') := by
      intro x hx
      have hx' : x ∈ oddCoreIn K' ⊔ J := by rw [sup_comm, hJsup]; exact hXK' hx
      obtain ⟨o, ho, j, hj, rfl⟩ := exists_mul_of_mem_sup_normalizer hK'n hx'
      have hoX : o ∈ X := by
        have : o = o * j * j⁻¹ := by group
        rw [this]
        exact mul_mem hx (inv_mem (hJX hj))
      exact mul_mem (mem_sup_right ⟨hoX, ho⟩) (mem_sup_left hj)
    have hPJ : P ≤ centralizer (J : Set G) := le_centralizer_iff.mp hJcen
    have hXOJ : X ⊓ oddCoreIn K' ≤ normalizer (J : Set G) := fun o ho =>
      centralizer_le_normalizer _ (hPJ (hOX (oddCoreIn_inf_le hXK' (mem_inf.mpr ⟨ho.2, ho.1⟩))))
    have hXOodd : Nat.Coprime 2 (Nat.card ↥(X ⊓ oddCoreIn K')) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
        (coprime_card_oddCoreIn K')
    have hXJ : X = J := le_antisymm (le_of_le_sup_of_coprime hXres hXOJ hXOodd hXdec) hJX
    refine ⟨hXJ, ?_, hJcen⟩
    rw [← hXJ]
    exact hOX
  have := Fintype.ofFinite ↥B
  obtain ⟨e₀, -, he₀⟩ := Finset.exists_mem_ne (s := Finset.univ)
    (by rw [Finset.card_univ]; have := Nat.card_eq_fintype_card (α := ↥B); omega) (1 : ↥B)
  have he₀1 : (e₀ : G) ≠ 1 := fun h => he₀ (Subtype.ext h)
  obtain ⟨-, hOJ₀, hJcen₀⟩ := key e₀ e₀.2 he₀1
  have hOJ : oddCoreIn J ≤ centralizer (J : Set G) :=
    hOJ₀.trans (le_centralizer_iff.mp hJcen₀)
  have hBO : B ≤ normalizer (oddCoreIn K' : Set G) := fun x hx =>
    mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn (hBQ hx).1)
  have hlarge : 2 ^ (1 + 1) ≤ Nat.card B := by
    rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num]; exact hB4
  have hgen := SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 1
    Nat.prime_two B (oddCoreIn K') hB hlarge hBO (coprime_card_oddCoreIn K')
  have hOK'J : oddCoreIn K' ≤ normalizer (J : Set G) := by
    rw [← hgen]
    refine iSup₂_le fun S hS => ?_
    obtain ⟨hSB, hScard⟩ := hS
    have : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp (by rw [hScard]; norm_num)
    obtain ⟨s, hs⟩ := exists_ne (1 : ↥S)
    have hs1 : (s : G) ≠ 1 := fun h => hs (Subtype.ext h)
    obtain ⟨hXJ, -, -⟩ := key s (hSB s.2) hs1
    have h1 : oddCoreIn K' ⊓ centralizer (S : Set G) ≤
        K' ⊓ centralizer ({(s : G)} : Set G) :=
      inf_le_inf (map_subtype_le _) (centralizer_le (Set.singleton_subset_iff.mpr s.2))
    rw [← hXJ]
    exact h1.trans (le_normalizer_twoLayerIn _)
  have hcomm : ⁅oddCoreIn K', J⁆ = ⊥ := by
    refine commutator_eq_bot_of_le_centralizer hJperf ?_
    refine (commutator_le_inf_of_le_normalizer hOK'J
      (hJK'.trans (le_normalizer_oddCoreIn K'))).trans ?_
    exact (inf_le_oddCoreIn (coprime_card_oddCoreIn K')
      (hJK'.trans (le_normalizer_oddCoreIn K'))).trans hOJ
  have hJC : J ≤ centralizer (oddCoreIn K' : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have hOn : oddCoreIn K' ≤ normalizer (centralizer (oddCoreIn K' : Set G) : Set G) :=
    le_normalizer_centralizer ((map_subtype_le _).trans (le_normalizer_oddCoreIn K'))
  have hle : K' ≤ centralizer (oddCoreIn K' : Set G) ⊔ oddCoreIn K' :=
    calc K' = J ⊔ oddCoreIn K' := hJsup.symm
      _ ≤ centralizer (oddCoreIn K' : Set G) ⊔ oddCoreIn K' := sup_le_sup_right hJC _
  exact le_centralizer_iff.mp (le_of_le_sup_of_coprime hK'res hOn (coprime_card_oddCoreIn K') hle)

theorem lemma315aInputFor_of_315b (hm : Lemma32FullFor 𝒜) (hq : QuasisimpleTwoPartInput)
    (h𝒜 : ∀ (G : Type) [Group G] [Finite G], 𝒜 G → KStarKProper G)
    (hb : Lemma315bInputFor 𝒜) : Lemma315aInputFor 𝒜 := by
  intro G _ _ hG N hN
  set D := solomonKStarOf N with hD
  rw [le_centralizer_iff]
  refine iSup₂_le fun K' hK' => ?_
  have hK'D : K' ≤ D := le_iSup₂_of_le K' hK' le_rfl
  have hOK' := oddCoreIn_le_centralizer_of_315b hm hq (h𝒜 G hG) hb hG hN hK'
  have hperf : Group.IsPerfect ↥K' :=
    Subgroup.isPerfect_iff.mpr (UnbalancedCorr.commutator_eq_of_isPComponent hK'.1.1 hK'.1.2)
  have hDK' : D ≤ normalizer (K' : Set G) :=
    (solomonKStarOf_le_twoLayerIn N).trans (FooteLit.twoLayerIn_le_normalizer hK'.1.1 hK'.1.2)
  have hK'O : K' ≤ normalizer (oddCoreIn D : Set G) := hK'D.trans (le_normalizer_oddCoreIn D)
  have hcomm : ⁅oddCoreIn D, K'⁆ = ⊥ := by
    refine commutator_eq_bot_of_le_centralizer hperf ?_
    refine (commutator_le_inf_of_le_normalizer ((map_subtype_le _).trans hDK') hK'O).trans ?_
    exact (inf_le_oddCoreIn (coprime_card_oddCoreIn D) hK'O).trans hOK'
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)

end CFSG.ComponentClassification.Sol76T13
