module

public import CFSG.ClassicalInvolution.Asc77.AscE186CentA

public section

namespace CFSG.ClassicalInvolution.Asc77.AscE186

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {N : Subgroup G} [N.Normal]

theorem oddCoreOf_eq_bot_of_isPGroup (hN : IsPGroup 2 ↥N) : oddCoreOf N = ⊥ := by
  rw [oddCoreOf_normal_eq_inf]
  have h2 : IsPGroup 2 ↥(N ⊓ classicalInvolutionOddCore G) := hN.to_inf_left
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  have hodd : Odd (Nat.card ↥(N ⊓ classicalInvolutionOddCore G)) :=
    (CFSG.ComponentClassification.OddCore.odd_card G).of_dvd_nat
      (Subgroup.card_dvd_of_le inf_le_right)
  apply Subgroup.eq_bot_of_card_eq
  rw [hn] at hodd ⊢
  have hn0 : n = 0 := by
    by_contra hn0
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hn0⟩)
  rw [hn0, pow_zero]

variable (p f Ω N) in
structure CentQuot : Prop where
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  hyp : HypOmegaMod p f Ω
  hyp' : HypOmegaMod p f (quotFamily Ω N)
  central : N ≤ Subgroup.center G
  meet : ∀ J ∈ Ω, J ⊓ N = ⊥

theorem CentQuot.of_isPGroup (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hNc : N ≤ Subgroup.center G) (hN2 : IsPGroup 2 ↥N) (hmeet : ∀ J ∈ Ω, J ⊓ N = ⊥) :
    CentQuot p f Ω N :=
  { odd := hp
    five := hq
    hyp := hΩ
    hyp' := (l6_14' (l6_7_proved p f) (l6_2 p f) (l6_9_proved p f) (l6_11_proved p f) hp hq G Ω
      hΩ N (oddCoreOf_eq_bot_of_isPGroup hN2) (fun K hK => by
        rw [inf_comm, hmeet K hK]
        simp)).2
    central := hNc
    meet := hmeet }

namespace CentQuot

variable (c : CentQuot p f Ω N)

include c

omit [Finite G] in
theorem natCard_map {J : Subgroup G} (hJ : J ∈ Ω) :
    Nat.card ↥(J.map (QuotientGroup.mk' N)) = Nat.card J :=
  (Nat.card_congr (AscQuot.quotRestrictEquiv (c.meet J hJ)).toEquiv).symm

theorem isSylow2In_map {J V : Subgroup G} (hJ : J ∈ Ω) (hV : IsSylow2In V J) :
    IsSylow2In (V.map (QuotientGroup.mk' N)) (J.map (QuotientGroup.mk' N)) := by
  obtain ⟨V₀, hV₀, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := J.map (QuotientGroup.mk' N))
    (IsPGroup.of_bot) bot_le
  have hcard : Nat.card V = Nat.card V₀ := by
    rw [natCard_eq_pow_of_isSylow2In hV, natCard_eq_pow_of_isSylow2In hV₀, c.natCard_map hJ]
  have hVN : V ⊓ N = ⊥ := eq_bot_iff.mpr ((inf_le_inf_right N hV.1).trans (c.meet J hJ).le)
  have hmapcard : Nat.card ↥(V.map (QuotientGroup.mk' N)) = Nat.card V :=
    (Nat.card_congr (AscQuot.quotRestrictEquiv hVN).toEquiv).symm
  exact hV₀.of_natCard_le (hV.2.1.map _) (Subgroup.map_mono hV.1) (by rw [hmapcard, hcard])

omit [Finite G] in
theorem le_of_map_eq {A B : Subgroup G} (hA : A ∈ Ω)
    (h : A.map (QuotientGroup.mk' N) = B.map (QuotientGroup.mk' N)) : A ≤ B := by
  have h1 : A ≤ B ⊔ N := by
    have h2 : A ≤ (A.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) :=
      Subgroup.le_comap_map _ _
    rw [h, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2
    exact h2
  exact le_of_le_sup_central c.central (perfect_of_mem c.hyp hA) h1

omit [Finite G] in
theorem eq_of_map_eq {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (h : K.map (QuotientGroup.mk' N) = J.map (QuotientGroup.mk' N)) : K = J :=
  le_antisymm (c.le_of_map_eq hK h) (c.le_of_map_eq hJ h.symm)

omit [Finite G] in
theorem map_ne_of_ne {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hne : J ≠ K) :
    J.map (QuotientGroup.mk' N) ≠ K.map (QuotientGroup.mk' N) :=
  fun h => hne (c.eq_of_map_eq hJ hK h)

theorem mem_normalizer_of_map {K : Subgroup G} (hK : K ∈ Ω) {u : G}
    (hu : QuotientGroup.mk' N u ∈
      Subgroup.normalizer ((K.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))) :
    u ∈ Subgroup.normalizer (K : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq]
  apply conjSub_eq_of_le_sup_central c.central (perfect_of_mem c.hyp hK) u
  have h1 : (conjSub u K).map (QuotientGroup.mk' N) = K.map (QuotientGroup.mk' N) := by
    rw [AscQuot.map_conjSub]
    exact mem_normalizer_iff_conjSub_eq.mp hu
  have h2 : conjSub u K ≤ ((conjSub u K).map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) :=
    Subgroup.le_comap_map _ _
  rw [h1, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2
  exact h2

theorem exists_lift_RSet {J : Subgroup G} (hJ : J ∈ Ω) {Rb : Subgroup (G ⧸ N)}
    (hRb : Rb ∈ RSet (quotFamily Ω N)) (hRbJ : Rb ≤ J.map (QuotientGroup.mk' N)) :
    ∃ R ∈ RSet Ω, R ≤ J ∧ R.map (QuotientGroup.mk' N) = Rb := by
  set mk := QuotientGroup.mk' N with hmk
  have hJN : J ⊓ N = ⊥ := c.meet J hJ
  have hRbsyl : IsSylow2In Rb (J.map mk) :=
    c.hyp'.isSylow2In_of_mem_RSet_of_le c.odd (map_mem_quotFamily hJ) hRb hRbJ
  set R : Subgroup G := Rb.comap mk ⊓ J with hR
  have hRJ : R ≤ J := inf_le_right
  have hRN : R ⊓ N = ⊥ := eq_bot_iff.mpr ((inf_le_inf_right N hRJ).trans hJN.le)
  have hRmap : R.map mk = Rb := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.1
    · intro hy
      obtain ⟨x, hx, rfl⟩ := hRbJ hy
      exact ⟨x, ⟨hy, hx⟩, rfl⟩
  have hRcard : Nat.card R = Nat.card Rb := by
    rw [← hRmap]
    exact Nat.card_congr (AscQuot.quotRestrictEquiv hRN).toEquiv
  have hR2 : IsPGroup 2 R := by
    intro x
    obtain ⟨k, hk⟩ := hRbsyl.2.1 ⟨mk (x : G), hRmap ▸ Subgroup.mem_map_of_mem _ x.2⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : mk ((x : G) ^ 2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have h2 : (x : G) ^ 2 ^ k ∈ J ⊓ N :=
      ⟨J.pow_mem (hRJ x.2) _, (QuotientGroup.eq_one_iff _).mp h1⟩
    rw [hJN, Subgroup.mem_bot] at h2
    simpa using h2
  obtain ⟨V₀, hV₀, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := J) IsPGroup.of_bot bot_le
  have hcard : Nat.card V₀ = Nat.card Rb := by
    rw [natCard_eq_pow_of_isSylow2In hV₀, natCard_eq_pow_of_isSylow2In hRbsyl, c.natCard_map hJ]
  have hRsyl : IsSylow2In R J := hV₀.of_natCard_le hR2 hRJ (by rw [hRcard, hcard])
  exact ⟨R, mem_RSet_of_isSylow2In hJ hRsyl, hRJ, hRmap⟩

theorem exists_lift_USet {J : Subgroup G} (hJ : J ∈ Ω) {Ub : Subgroup (G ⧸ N)}
    (hUb : Ub ∈ USet (quotFamily Ω N)) (hUbJ : Ub ≤ J.map (QuotientGroup.mk' N)) :
    ∃ U ∈ USet Ω, U ≤ J ∧ U.map (QuotientGroup.mk' N) = Ub := by
  set mk := QuotientGroup.mk' N with hmk
  have hJN : J ⊓ N = ⊥ := c.meet J hJ
  obtain ⟨Rb, hRb, Jb₁, hJb₁, hRbsyl, hUbRb, hcyc, hcard, h4⟩ :=
    c.hyp'.exists_data_of_mem_USet c.odd hUb
  have hUb2 : IsPGroup 2 Ub := hRbsyl.2.1.to_le hUbRb
  have hJb : Jb₁ = J.map mk :=
    c.hyp'.eq_of_le_of_le hJb₁ (map_mem_quotFamily hJ) hUb2 h4 (hUbRb.trans hRbsyl.1) hUbJ
  rw [hJb] at hRbsyl
  set U : Subgroup G := Ub.comap mk ⊓ J with hU
  have hUJ : U ≤ J := inf_le_right
  have hUN : U ⊓ N = ⊥ := eq_bot_iff.mpr ((inf_le_inf_right N hUJ).trans hJN.le)
  have hUmap : U.map mk = Ub := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.1
    · intro hy
      obtain ⟨x, hx, rfl⟩ := hUbJ hy
      exact ⟨x, ⟨hy, hx⟩, rfl⟩
  have hUcard : Nat.card U = Nat.card Ub := by
    rw [← hUmap]
    exact (Nat.card_congr (AscQuot.quotRestrictEquiv hUN).toEquiv)
  have hUc : IsCyclic U := by
    have h1 : IsCyclic ↥(U.map mk) := hUmap ▸ hcyc
    exact (MulEquiv.isCyclic (AscQuot.quotRestrictEquiv hUN)).mpr h1
  have hU2 : IsPGroup 2 U := by
    intro x
    obtain ⟨k, hk⟩ := hUb2 ⟨mk (x : G), hUmap ▸ Subgroup.mem_map_of_mem _ x.2⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : mk ((x : G) ^ 2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have h2 : (x : G) ^ 2 ^ k ∈ J ⊓ N :=
      ⟨J.pow_mem (hUJ x.2) _, (QuotientGroup.eq_one_iff _).mp h1⟩
    rw [hJN, Subgroup.mem_bot] at h2
    simpa using h2
  obtain ⟨R, hR, hRsyl, hUR⟩ := exists_mem_RSet_ge hJ hU2 hUJ
  have hRcard : Nat.card R = 2 * Nat.card U := by
    have : Nat.card R = Nat.card Rb := by
      rw [natCard_eq_pow_of_isSylow2In hRsyl, natCard_eq_pow_of_isSylow2In hRbsyl,
        c.natCard_map hJ]
    rw [this, hcard, hUcard]
  exact ⟨U, mem_USet_of_natCard hJ hRsyl hUR hUc hRcard, hUJ, hUmap⟩

theorem omegaStarNbr_of_map {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (h : J.map (QuotientGroup.mk' N) ∈
      omegaStarNbr (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    J ∈ omegaStarNbr Ω K := by
  obtain ⟨-, hne, Ub, hUb, hUbJ, hUbN⟩ := h
  obtain ⟨U, hU, hUJ, hUmap⟩ := c.exists_lift_USet hJ hUb hUbJ
  refine ⟨hJ, fun h => hne (by rw [h]), U, hU, hUJ, fun u hu => ?_⟩
  exact c.mem_normalizer_of_map hK (hUbN (hUmap ▸ Subgroup.mem_map_of_mem _ hu))

theorem omegaNbr_of_map {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (h : J.map (QuotientGroup.mk' N) ∈
      omegaNbr (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    J ∈ omegaNbr Ω K := by
  obtain ⟨-, hne, Rb, hRb, hRbJ, hRbN⟩ := h
  obtain ⟨R, hR, hRJ, hRmap⟩ := c.exists_lift_RSet hJ hRb hRbJ
  refine ⟨hJ, fun h => hne (by rw [h]), R, hR, hRJ, fun u hu => ?_⟩
  exact c.mem_normalizer_of_map hK (hRbN (hRmap ▸ Subgroup.mem_map_of_mem _ hu))

theorem omegaNbr_map {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ omegaNbr Ω K) :
    J.map (QuotientGroup.mk' N) ∈
      omegaNbr (quotFamily Ω N) (K.map (QuotientGroup.mk' N)) := by
  obtain ⟨hJΩ, hne, T, hT, hTJ, hTN⟩ := hJ
  have hTsyl : IsSylow2In T J := c.hyp.isSylow2In_of_mem_RSet_of_le c.odd hJΩ hT hTJ
  refine ⟨map_mem_quotFamily hJΩ, c.map_ne_of_ne hK hJΩ hne, T.map (QuotientGroup.mk' N),
    mem_RSet_of_isSylow2In (map_mem_quotFamily hJΩ) (c.isSylow2In_map hJΩ hTsyl),
    Subgroup.map_mono hTJ, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact mk_mem_normalizer_map (N := N) (hTN ht)

theorem dstarAdj_of_map {L L' : Subgroup G} (hL : L ∈ Ω) (hL' : L' ∈ Ω)
    (h : dstarAdj (quotFamily Ω N) (L.map (QuotientGroup.mk' N))
      (L'.map (QuotientGroup.mk' N))) : dstarAdj Ω L L' := by
  rcases h.2 with h1 | h1
  · exact ⟨hL', Or.inl (c.omegaStarNbr_of_map hL hL' h1)⟩
  · exact ⟨hL', Or.inr (c.omegaStarNbr_of_map hL' hL h1)⟩

theorem exists_lift_dstarComp {K : Subgroup G} (hK : K ∈ Ω) {Mb : Subgroup (G ⧸ N)}
    (hMb : Mb ∈ dstarComp (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    ∃ M ∈ dstarComp Ω K, M.map (QuotientGroup.mk' N) = Mb := by
  obtain ⟨M, -, hMeq, hgood⟩ := exists_good_lift (N := N) (fun L : Subgroup G => L ∈ dstarComp Ω K)
    hK Relation.ReflTransGen.refl
    (fun L hL L' hL' hgood hadj => ⟨L', hL', rfl, hgood.tail (c.dstarAdj_of_map hL hL' hadj)⟩) hMb
  exact ⟨M, hgood, hMeq⟩

theorem aEmpty_quotFamily (hA : ∀ J ∈ Ω, AEmpty Ω J) :
    ∀ M ∈ quotFamily Ω N, AEmpty (quotFamily Ω N) M := by
  rintro _ ⟨K, hK, rfl⟩
  intro Jb hJbstar hJbnbr zKb zJb hzKb hzJb
  obtain ⟨J, hJ, rfl⟩ := hJbstar.1
  have hstar : J ∈ omegaStarNbr Ω K := c.omegaStarNbr_of_map hK hJ hJbstar
  have hnbr : J ∉ omegaNbr Ω K := fun h => hJbnbr (c.omegaNbr_map hK h)
  obtain ⟨z, hz⟩ := c.hyp.exists_uniqueInvolution c.odd c.five hK
  obtain ⟨zJ, hzJ⟩ := c.hyp.exists_uniqueInvolution c.odd c.five hJ
  have e1 : QuotientGroup.mk' N z = zKb :=
    (AscQuot.isUniqueInvolution_map_mk (c.meet K hK) hz).eq hzKb
  have e2 : QuotientGroup.mk' N zJ = zJb :=
    (AscQuot.isUniqueInvolution_map_mk (c.meet J hJ) hzJ).eq hzJb
  obtain ⟨g, hg, hgK⟩ := hA K hK J hstar hnbr z zJ hz hzJ
  refine ⟨QuotientGroup.mk' N g, ?_, ?_⟩
  · have h2 := map_pairNormalizers_le (N := N) K J z zJ (Subgroup.mem_map_of_mem _ hg)
    rw [e1, e2] at h2
    exact h2
  · have h3 := congrArg (Subgroup.map (QuotientGroup.mk' N)) hgK
    rw [AscQuot.map_conjSub] at h3
    exact h3

end CentQuot

end CFSG.ClassicalInvolution.Asc77.AscE186
