module

public import CFSG.ClassicalInvolution.Asc77.AscE187Img
public import CFSG.ClassicalInvolution.Asc77.AscE186CentB
public import CFSG.ClassicalInvolution.Q3.Q3T7FU0

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.T7FU

variable {T : CFSG.ClassicalInvolution.Uniform.MemberType}

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement MatrixGroups
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
section Finite
variable [Finite G]

omit [Finite G] in

theorem conjInvariant_twFamily (hΩ : HM T Ω) (t : G) : ConjInvariant (twFamily Ω t) := by
  rintro n L ⟨M, hM, hMt, rfl⟩
  obtain ⟨c, rfl⟩ := twMk_surjective t n
  rw [twImage_conj]
  refine ⟨conjSub (c : G) M, hΩ.conjInvariant _ M hM, ?_, rfl⟩
  have hct : (c : G) * t * (c : G)⁻¹ = t := by
    rw [mem_TwC_iff.mp c.2]
    group
  have := hMt.conj (c : G)
  rwa [hct] at this

end Finite
end Asc77

end

section

namespace Asc77.AscE186
open CFSG.ClassicalInvolution.Asc77.AscE186
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {N : Subgroup G} [N.Normal]
variable (T Ω N) in

structure CentQuot : Prop where
  hyp : HM T Ω
  hyp' : HM T (quotFamily Ω N)
  central : N ≤ Subgroup.center G
  two : IsPGroup 2 ↥N
  meet : ∀ J ∈ Ω, J ⊓ N = ⊥

namespace CentQuot
open CFSG.ClassicalInvolution.Asc77.AscE186.CentQuot
variable (c : Asc77.AscE186.CentQuot T Ω N)
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

theorem exists_lift_USet {J : Subgroup G} (hJ : J ∈ Ω) {Ub : Subgroup (G ⧸ N)}
    (hUb : Ub ∈ USet (quotFamily Ω N)) (hUbJ : Ub ≤ J.map (QuotientGroup.mk' N)) :
    ∃ U ∈ USet Ω, U ≤ J ∧ U.map (QuotientGroup.mk' N) = Ub := by
  set mk := QuotientGroup.mk' N with hmk
  have hJN : J ⊓ N = ⊥ := c.meet J hJ
  obtain ⟨Rb, hRb, Jb₁, hJb₁, hRbsyl, hUbRb, hcyc, hcard, h4⟩ :=
    c.hyp'.exists_data_of_mem_USet hUb
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

end CentQuot
end Asc77.AscE186

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem twin_conj (hΩ : HM T Ω) {M : Subgroup G} {t δ : G} (hM : M ∈ Ω)
    (hMt : IsUniqueInvolution M t) (hδ : δ * t = t * δ) :
    conjSub δ M ∈ Ω ∧ IsUniqueInvolution (conjSub δ M) t := by
  refine ⟨hΩ.conjInvariant δ M hM, ?_⟩
  have := hMt.conj δ
  rwa [show δ * t * δ⁻¹ = t by rw [hδ]; group] at this
end Asc77

end

end CFSG.ClassicalInvolution.T7FU
