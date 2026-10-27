module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.AschTight.Hall196Idx
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64A
public import CFSG.ClassicalInvolution.Uniform.U5Util
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

structure CentQuotGen (Ω : Set (Subgroup G)) (N : Subgroup G) [N.Normal] : Prop where
  hyp : HypOmegaGen Ω
  hyp' : HypOmegaGen (quotFamily Ω N)
  meet : ∀ J ∈ Ω, J ⊓ N = ⊥
  eq_of_map : ∀ K ∈ Ω, ∀ J ∈ Ω,
    K.map (QuotientGroup.mk' N) = J.map (QuotientGroup.mk' N) → K = J
  normalizer_of_map : ∀ K ∈ Ω, ∀ u : G, QuotientGroup.mk' N u ∈
    Subgroup.normalizer ((K.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) →
    u ∈ Subgroup.normalizer (K : Set G)

namespace CentQuotGen

variable {N : Subgroup G} [N.Normal] (c : CentQuotGen Ω N)
include c

omit [Finite G] in
theorem natCard_map {J : Subgroup G} (hJ : J ∈ Ω) :
    Nat.card ↥(J.map (QuotientGroup.mk' N)) = Nat.card J :=
  (Nat.card_congr (AscQuot.quotRestrictEquiv (c.meet J hJ)).toEquiv).symm

theorem map_ne_of_ne {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hne : J ≠ K) :
    J.map (QuotientGroup.mk' N) ≠ K.map (QuotientGroup.mk' N) :=
  fun h => hne (c.eq_of_map J hJ K hK h)

theorem exists_lift_RSet {J : Subgroup G} (hJ : J ∈ Ω) {Rb : Subgroup (G ⧸ N)}
    (hRb : Rb ∈ RSet (quotFamily Ω N)) (hRbJ : Rb ≤ J.map (QuotientGroup.mk' N)) :
    ∃ R ∈ RSet Ω, R ≤ J ∧ R.map (QuotientGroup.mk' N) = Rb := by
  set mk := QuotientGroup.mk' N with hmk
  have hJN : J ⊓ N = ⊥ := c.meet J hJ
  have hRbsyl : IsSylow2In Rb (J.map mk) :=
    Sec6Gen.isSylow2In_of_mem_RSet_of_le c.hyp' (map_mem_quotFamily hJ) hRb hRbJ
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
    Sec6Gen.exists_data_of_mem_USet c.hyp' hUb
  have hUb2 : IsPGroup 2 Ub := hRbsyl.2.1.to_le hUbRb
  have hJb : Jb₁ = J.map mk :=
    Sec6Gen.eq_of_le_of_le c.hyp' hJb₁ (map_mem_quotFamily hJ) hUb2 h4 (hUbRb.trans hRbsyl.1) hUbJ
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
  exact c.normalizer_of_map K hK u (hUbN (hUmap ▸ Subgroup.mem_map_of_mem _ hu))

theorem omegaNbr_of_map {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (h : J.map (QuotientGroup.mk' N) ∈
      omegaNbr (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    J ∈ omegaNbr Ω K := by
  obtain ⟨-, hne, Rb, hRb, hRbJ, hRbN⟩ := h
  obtain ⟨R, hR, hRJ, hRmap⟩ := c.exists_lift_RSet hJ hRb hRbJ
  refine ⟨hJ, fun h => hne (by rw [h]), R, hR, hRJ, fun u hu => ?_⟩
  exact c.normalizer_of_map K hK u (hRbN (hRmap ▸ Subgroup.mem_map_of_mem _ hu))

theorem omegaNbr_map {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ omegaNbr Ω K) :
    J.map (QuotientGroup.mk' N) ∈
      omegaNbr (quotFamily Ω N) (K.map (QuotientGroup.mk' N)) := by
  obtain ⟨hJΩ, hne, T, hT, hTJ, hTN⟩ := hJ
  have hTsyl : IsSylow2In T J := Sec6Gen.isSylow2In_of_mem_RSet_of_le c.hyp hJΩ hT hTJ
  refine ⟨map_mem_quotFamily hJΩ, c.map_ne_of_ne hK hJΩ hne, T.map (QuotientGroup.mk' N),
    mem_RSet_of_isSylow2In (map_mem_quotFamily hJΩ)
      (Hall196.isSylow2In_map_hom (QuotientGroup.mk' N) hTsyl),
    Subgroup.map_mono hTJ, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact mk_mem_normalizer_map (N := N) (hTN ht)

theorem aEmpty_quotFamily (hA : ∀ J ∈ Ω, AEmpty Ω J) :
    ∀ M ∈ quotFamily Ω N, AEmpty (quotFamily Ω N) M := by
  rintro _ ⟨K, hK, rfl⟩
  intro Jb hJbstar hJbnbr zKb zJb hzKb hzJb
  obtain ⟨J, hJ, rfl⟩ := hJbstar.1
  have hstar : J ∈ omegaStarNbr Ω K := c.omegaStarNbr_of_map hK hJ hJbstar
  have hnbr : J ∉ omegaNbr Ω K := fun h => hJbnbr (c.omegaNbr_map hK h)
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution c.hyp hK
  obtain ⟨zJ, hzJ⟩ := Sec6Gen.exists_uniqueInvolution c.hyp hJ
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

end CentQuotGen

end CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
