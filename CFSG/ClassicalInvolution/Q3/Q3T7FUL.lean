module

public import CFSG.ClassicalInvolution.Q3.Q3T7FUQ
public import CFSG.ClassicalInvolution.Q3.Q3T7M02
public import CFSG.ClassicalInvolution.Asc77.AscE186CentC

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.T7FU

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77

variable {T : CFSG.ClassicalInvolution.Uniform.MemberType}

section

namespace Asc77.AscE186
open CFSG.ClassicalInvolution.Asc77.AscE186
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {N : Subgroup G} [N.Normal]

namespace CentQuot
open CFSG.ClassicalInvolution.Asc77.AscE186.CentQuot
variable (c : Asc77.AscE186.CentQuot T Ω N)
include c
omit [Finite G] in

theorem le_of_map_eq (hodd : ∀ K ∈ Ω, Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} = K)
    [Finite G] {A B : Subgroup G} (hA : A ∈ Ω) (hB : B ∈ Ω)
    (h : A.map (QuotientGroup.mk' N) = B.map (QuotientGroup.mk' N)) : A ≤ B := by
  have h1 : A ≤ B ⊔ N := by
    have h2 : A ≤ (A.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) :=
      Subgroup.le_comap_map _ _
    rw [h, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2
    exact h2
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.AscE186.le_of_le_sup_central c.central c.two
    (c.meet B hB) (hodd A hA) h1
omit [Finite G] in

theorem eq_of_map_eq (hodd : ∀ K ∈ Ω, Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} = K)
    [Finite G] {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (h : K.map (QuotientGroup.mk' N) = J.map (QuotientGroup.mk' N)) : K = J :=
  le_antisymm (c.le_of_map_eq hodd hK hJ h) (c.le_of_map_eq hodd hJ hK h.symm)
omit [Finite G] in

theorem map_ne_of_ne (hodd : ∀ K ∈ Ω, Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} = K)
    [Finite G] {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hne : J ≠ K) :
    J.map (QuotientGroup.mk' N) ≠ K.map (QuotientGroup.mk' N) :=
  fun h => hne (c.eq_of_map_eq hodd hJ hK h)

theorem mem_normalizer_of_map
    (hodd : ∀ K ∈ Ω, Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} = K)
    {K : Subgroup G} (hK : K ∈ Ω) {u : G}
    (hu : QuotientGroup.mk' N u ∈
      Subgroup.normalizer ((K.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))) :
    u ∈ Subgroup.normalizer (K : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq]
  apply CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.AscE186.conjSub_eq_of_le_sup_central c.central c.two
    (c.meet K hK) (hodd K hK) u
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
    c.hyp'.isSylow2In_of_mem_RSet_of_le (map_mem_quotFamily hJ) hRb hRbJ
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

theorem omegaStarNbr_of_map (hodd : ∀ K ∈ Ω, Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} = K)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (h : J.map (QuotientGroup.mk' N) ∈
      omegaStarNbr (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    J ∈ omegaStarNbr Ω K := by
  obtain ⟨-, hne, Ub, hUb, hUbJ, hUbN⟩ := h
  obtain ⟨U, hU, hUJ, hUmap⟩ := c.exists_lift_USet hJ hUb hUbJ
  refine ⟨hJ, fun h => hne (by rw [h]), U, hU, hUJ, fun u hu => ?_⟩
  exact c.mem_normalizer_of_map hodd hK (hUbN (hUmap ▸ Subgroup.mem_map_of_mem _ hu))

theorem omegaNbr_of_map (hodd : ∀ K ∈ Ω, Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} = K)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (h : J.map (QuotientGroup.mk' N) ∈
      omegaNbr (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    J ∈ omegaNbr Ω K := by
  obtain ⟨-, hne, Rb, hRb, hRbJ, hRbN⟩ := h
  obtain ⟨R, hR, hRJ, hRmap⟩ := c.exists_lift_RSet hJ hRb hRbJ
  refine ⟨hJ, fun h => hne (by rw [h]), R, hR, hRJ, fun u hu => ?_⟩
  exact c.mem_normalizer_of_map hodd hK (hRbN (hRmap ▸ Subgroup.mem_map_of_mem _ hu))

theorem omegaNbr_map (hodd : ∀ K ∈ Ω, Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} = K)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ omegaNbr Ω K) :
    J.map (QuotientGroup.mk' N) ∈
      omegaNbr (quotFamily Ω N) (K.map (QuotientGroup.mk' N)) := by
  obtain ⟨hJΩ, hne, T, hT, hTJ, hTN⟩ := hJ
  have hTsyl : IsSylow2In T J := c.hyp.isSylow2In_of_mem_RSet_of_le hJΩ hT hTJ
  refine ⟨map_mem_quotFamily hJΩ, c.map_ne_of_ne hodd hK hJΩ hne, T.map (QuotientGroup.mk' N),
    mem_RSet_of_isSylow2In (map_mem_quotFamily hJΩ) (c.isSylow2In_map hJΩ hTsyl),
    Subgroup.map_mono hTJ, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact mk_mem_normalizer_map (N := N) (hTN ht)

theorem dstarAdj_of_map (hodd : ∀ K ∈ Ω, Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} = K)
    {L L' : Subgroup G} (hL : L ∈ Ω) (hL' : L' ∈ Ω)
    (h : dstarAdj (quotFamily Ω N) (L.map (QuotientGroup.mk' N))
      (L'.map (QuotientGroup.mk' N))) : dstarAdj Ω L L' := by
  rcases h.2 with h1 | h1
  · exact ⟨hL', Or.inl (c.omegaStarNbr_of_map hodd hL hL' h1)⟩
  · exact ⟨hL', Or.inr (c.omegaStarNbr_of_map hodd hL' hL h1)⟩

theorem exists_lift_dstarComp
    (hodd : ∀ K ∈ Ω, Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} = K)
    {K : Subgroup G} (hK : K ∈ Ω) {Mb : Subgroup (G ⧸ N)}
    (hMb : Mb ∈ dstarComp (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    ∃ M ∈ dstarComp Ω K, M.map (QuotientGroup.mk' N) = Mb := by
  obtain ⟨M, -, hMeq, hgood⟩ := exists_good_lift (N := N) (fun L : Subgroup G => L ∈ dstarComp Ω K)
    hK Relation.ReflTransGen.refl
    (fun L hL L' hL' hgood hadj => ⟨L', hL', rfl, hgood.tail (c.dstarAdj_of_map hodd hL hL' hadj)⟩)
      hMb
  exact ⟨M, hgood, hMeq⟩

theorem aEmpty_quotFamily (hodd : ∀ K ∈ Ω, Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} = K)
    (hA : ∀ J ∈ Ω, AEmpty Ω J) :
    ∀ M ∈ quotFamily Ω N, AEmpty (quotFamily Ω N) M := by
  rintro _ ⟨K, hK, rfl⟩
  intro Jb hJbstar hJbnbr zKb zJb hzKb hzJb
  obtain ⟨J, hJ, rfl⟩ := hJbstar.1
  have hstar : J ∈ omegaStarNbr Ω K := c.omegaStarNbr_of_map hodd hK hJ hJbstar
  have hnbr : J ∉ omegaNbr Ω K := fun h => hJbnbr (c.omegaNbr_map hodd hK h)
  obtain ⟨z, hz⟩ := c.hyp.exists_uniqueInvolution hK
  obtain ⟨zJ, hzJ⟩ := c.hyp.exists_uniqueInvolution hJ
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

theorem exists_lift_kperp (c : T7FU.Asc77.AscE186.CentQuot T Ω N)
    (hodd : ∀ K ∈ Ω, Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} = K)
    {L : Subgroup G} (hL : L ∈ Ω)
    {Jb : Subgroup (G ⧸ N)}
    (hJb : Jb ∈ KPerp (quotFamily Ω N) (L.map (QuotientGroup.mk' N))) :
    ∃ J ∈ KPerp Ω L, J.map (QuotientGroup.mk' N) = Jb := by
  rcases hJb with rfl | hJbn
  · exact ⟨L, Set.mem_insert _ _, rfl⟩
  · obtain ⟨J₀, hJ₀, rfl⟩ := hJbn.1
    exact ⟨J₀, Set.mem_insert_of_mem _ (c.omegaNbr_of_map hodd hL hJ₀ hJbn), rfl⟩

theorem exists_lift_sylow_pair (hN2 : IsPGroup 2 ↥N) (c : T7FU.Asc77.AscE186.CentQuot T Ω N)
    (hodd : ∀ K ∈ Ω, Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} = K)
    {L J : Subgroup G}
    (hL : L ∈ Ω) (hJ : J ∈ KPerp Ω L) {Rb₁ Rb₂ : Subgroup (G ⧸ N)}
    (hRb₁ : Rb₁ ∈ RSet (quotFamily Ω N)) (hRb₁L : Rb₁ ≤ L.map (QuotientGroup.mk' N))
    (hRb₂ : Rb₂ ∈ RSet (quotFamily Ω N)) (hRb₂J : Rb₂ ≤ J.map (QuotientGroup.mk' N))
    (hc : Commutes Rb₁ Rb₂ ∨ Rb₂ = Rb₁) :
    ∃ R₁ R₂ : Subgroup G, R₁ ∈ RSet Ω ∧ R₁ ≤ L ∧ R₂ ∈ RSet Ω ∧ R₂ ≤ J ∧
      R₁.map (QuotientGroup.mk' N) = Rb₁ ∧ R₂.map (QuotientGroup.mk' N) = Rb₂ ∧
      (Commutes R₁ R₂ ∨ R₂ = R₁) := by
  have hJΩ : J ∈ Ω := by
    rcases hJ with rfl | hJn
    · exact hL
    · exact hJn.1
  obtain ⟨R₁, hR₁, hR₁L, hR₁map⟩ := c.exists_lift_RSet hL hRb₁ hRb₁L
  rcases hc with hcomm | heq
  · obtain ⟨R₂, hR₂, hR₂J, hR₂map⟩ := c.exists_lift_RSet hJΩ hRb₂ hRb₂J
    refine ⟨R₁, R₂, hR₁, hR₁L, hR₂, hR₂J, hR₁map, hR₂map, ?_⟩
    by_cases hR₁₂ : R₂ = R₁
    · exact Or.inr hR₁₂
    refine Or.inl ?_
    have hR₁₂' : IsPGroup 2 ↥(R₁ ⊔ R₂) := by
      refine isPGroup_of_map_isPGroup hN2 ?_
      rw [Subgroup.map_sup, hR₁map, hR₂map]
      have hb₁ : IsPGroup 2 ↥Rb₁ := by
        rw [← hR₁map]
        exact (isPGroup_of_mem_RSet hR₁).map _
      have hb₂ : IsPGroup 2 ↥Rb₂ := by
        rw [← hR₂map]
        exact (isPGroup_of_mem_RSet hR₂).map _
      exact hb₁.to_sup_of_normal_right' hb₂ fun x hx =>
        mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_of_mem_of_commutes hx hcomm)
    obtain ⟨S, hS⟩ := hR₁₂'.exists_le_sylow
    exact CFSG.ClassicalInvolution.Q3.Q3CP.l67Gen G Ω c.hyp.toGen S R₁ hR₁ R₂ hR₂
      (le_sup_left.trans hS)
      (le_sup_right.trans hS) (Ne.symm hR₁₂)
  · have hJL : J = L := by
      by_contra hne
      have hJn : J ∈ omegaNbr Ω L := hJ.resolve_left hne
      have hLJ : L.map (QuotientGroup.mk' N) ≠ J.map (QuotientGroup.mk' N) :=
        fun h => hne (c.eq_of_map_eq hodd hL hJΩ h).symm
      have h2 := c.hyp'.card_le_two_of_le_inf (map_mem_quotFamily hL) (map_mem_quotFamily hJΩ) hLJ
        (isPGroup_of_mem_RSet hRb₁) hRb₁L (heq ▸ hRb₂J)
      have h8 := c.hyp'.eight_le_of_mem_RSet hRb₁
      omega
    subst hJL
    exact ⟨R₁, R₁, hR₁, hR₁L, hR₁, hR₁L, hR₁map, heq.symm ▸ hR₁map, Or.inr rfl⟩

end Asc77.AscE186

end

end CFSG.ClassicalInvolution.T7FU
