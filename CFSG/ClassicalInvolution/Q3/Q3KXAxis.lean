module

public import CFSG.ClassicalInvolution.Q3.Q3KXOrbit
public import CFSG.ClassicalInvolution.Q3.Q3T8B04

set_option autoImplicit false
set_option linter.unusedSectionVars false

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap

section Axis


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem BadStd8.false_of_linkConstCore [IsSimpleGroup G] (h : BadStd8 Ω K J S R T W z t)
    (hlink : ∀ J' ∈ omegaNbr Ω K, ∀ t' : G, IsUniqueInvolution J' t' →
      alphaCore (Subgroup.closure ({t', z} : Set G)) =
        alphaCore (Subgroup.closure ({t, z} : Set G)))
    (hodd : Odd (Nat.card ↥(alphaCore (Subgroup.closure ({t, z} : Set G))))) : False := by
  have hs := h.std
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hvertex : ∀ c ∈ Ω, ∀ y₂ : G, IsUniqueInvolution c y₂ → ∃ g : G,
      ∀ L ∈ omegaNbr Ω c, ∀ y : G, IsUniqueInvolution L y →
        alphaCore (Subgroup.closure ({y, y₂} : Set G)) =
          conjSub g (alphaCore (Subgroup.closure ({t, z} : Set G))) := by
    intro c hc y₂ hy₂
    obtain ⟨g, hg⟩ := hs.stand.trans c hc
    have hyg : y₂ = g * z * g⁻¹ := hy₂.eq (hg ▸ hs.hz.conj g)
    refine ⟨g, fun L hL y hy => ?_⟩
    have hL' : conjSub g⁻¹ L ∈ omegaNbr Ω K := by
      have := omegaNbr_conj hΩ.conjInvariant hL g⁻¹
      rwa [← hg, conjSub_inv_conjSub] at this
    have h0 := hlink _ hL' _ (hy.conj g⁻¹)
    have h1 : conjSub g (Subgroup.closure ({g⁻¹ * y * g⁻¹⁻¹, z} : Set G)) =
        Subgroup.closure ({y, y₂} : Set G) := by
      rw [conjSub_closure_pair, hyg]
      congr 2
      group
    rw [← h1, alphaCore_conjSub, h0]
  have hprop : ∀ L ∈ dComp Ω K, L ∈ Ω ∧ ∀ L' ∈ omegaNbr Ω L, ∀ y y' : G,
      IsUniqueInvolution L y → IsUniqueInvolution L' y' →
        alphaCore (Subgroup.closure ({y', y} : Set G)) =
          alphaCore (Subgroup.closure ({t, z} : Set G)) := by
    intro L hL
    induction hL with
    | refl =>
      refine ⟨hK, fun L' hL' y y' hy hy' => ?_⟩
      rw [hy.eq hs.hz]
      exact hlink L' hL' y' hy'
    | @tail b c _ hbc ih =>
      obtain ⟨hbΩ, hPb⟩ := ih
      obtain ⟨hcΩ, hadj⟩ := hbc
      have hcb : c ∈ omegaNbr Ω b ∧ b ∈ omegaNbr Ω c := by
        rcases hadj with h' | h'
        · exact ⟨h', Q3CL.T3.omegaNbr_symm (l6_2) hΩ hbΩ hcΩ h'⟩
        · exact ⟨Q3CL.T3.omegaNbr_symm (l6_2) hΩ hcΩ hbΩ h', h'⟩
      refine ⟨hcΩ, fun L'' hL'' y₂ y'' hy₂ hy'' => ?_⟩
      obtain ⟨yb, hyb⟩ := hΩ.exists_uniqueInvolution hbΩ
      obtain ⟨g, hg⟩ := hvertex c hcΩ y₂ hy₂
      have h1 : alphaCore (Subgroup.closure ({y'', y₂} : Set G)) =
          alphaCore (Subgroup.closure ({yb, y₂} : Set G)) := by
        rw [hg L'' hL'' y'' hy'', hg b hcb.2 yb hyb]
      have h2 : alphaCore (Subgroup.closure ({y₂, yb} : Set G)) =
          alphaCore (Subgroup.closure ({t, z} : Set G)) := hPb c hcb.1 yb y₂ hyb hy₂
      rw [h1, Set.pair_comm]
      exact h2
  have hN : (⊤ : Subgroup G) ≤
      Subgroup.normalizer (alphaCore (Subgroup.closure ({t, z} : Set G)) : Set G) := by
    intro n _
    have hKn : conjSub n K ∈ dComp Ω K := h.conn K hK _ (hΩ.conjInvariant n K hK)
    obtain ⟨-, hP⟩ := hprop _ hKn
    have h' := hP (conjSub n J) (omegaNbr_conj hΩ.conjInvariant hs.hJ n) (n * z * n⁻¹)
      (n * t * n⁻¹) (hs.hz.conj n) (hs.ht.conj n)
    rw [← conjSub_closure_pair, alphaCore_conjSub] at h'
    exact mem_normalizer_iff_conjSub_eq.mpr h'
  have hnorm : (alphaCore (Subgroup.closure ({t, z} : Set G))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hN)
  rcases hnorm.eq_bot_or_eq_top with h' | h'
  · exact h.bad (alphaOf_eq_bot_of_alphaCore_eq_bot h')
  · have hord : orderOf z = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hs.hz.sq) hs.hz.ne_one
    have hdvd : 2 ∣ Nat.card G := hord ▸ orderOf_dvd_natCard z
    rw [h', Subgroup.card_top] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem closure_mul_pair_eq (z t : G) :
    Subgroup.closure ({z * t, z} : Set G) = Subgroup.closure ({t, z} : Set G) := by
  have hz : z ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.subset_closure (by simp)
  have ht : t ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.subset_closure (by simp)
  refine le_antisymm ((Subgroup.closure_le _).mpr ?_) ((Subgroup.closure_le _).mpr ?_)
  · rintro _ (rfl | rfl)
    · exact Subgroup.mul_mem _ hz ht
    · exact hz
  · have hz' : z ∈ Subgroup.closure ({z * t, z} : Set G) := Subgroup.subset_closure (by simp)
    have hzt : z * t ∈ Subgroup.closure ({z * t, z} : Set G) := Subgroup.subset_closure (by simp)
    rintro x (hx | hx)
    · have : x = z⁻¹ * (z * t) := by rw [hx]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hz') hzt
    · rw [hx]
      exact hz'

theorem BadStd8.false_of_localAxis_rank [IsSimpleGroup G] (h : BadStd8 Ω K J S R T W z t)
    {B : Subgroup G} (hbal : RankThreeBalance B)
    (hpair : Subgroup.closure ({t, z} : Set G) ≤ B)
    (hgen : Subgroup.centralizer ({z} : Set G) ≤ rankTwoSpan B) : False := by
  have hF : Subgroup.closure ({t, z} : Set G) ∈ signalizerFunctorEk 2 2 B :=
    ⟨hpair, by simpa using h.isElemAbelian2_pair.1⟩
  have hAF : Balance.Theorem5.alphaFrame B = alphaCore (Subgroup.closure ({t, z} : Set G)) :=
    Balance.Theorem5.alphaFrame_eq_alphaCore hbal hF
  have hodd : Odd (Nat.card ↥(alphaCore (Subgroup.closure ({t, z} : Set G)))) := by
    rw [← hAF]
    exact Balance.Theorem5.odd_card_alphaFrame hbal
  have hnormB : ∀ c ∈ rankTwoSpan B, conjSub c (alphaCore (Subgroup.closure ({t, z} : Set G))) =
      alphaCore (Subgroup.closure ({t, z} : Set G)) := by
    intro c hc
    have := Balance.Theorem5.rankTwoSpan_le_normalizer_alphaFrame hbal hc
    rw [hAF] at this
    exact mem_normalizer_iff_conjSub_eq.mp this
  refine h.false_of_linkConstCore ?_ hodd
  intro J' hJ' t' ht'
  obtain ⟨c, hcz, hct⟩ := h.omega_orbit_two hJ' ht'
  have hcC : c ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc c * z = c * z * c⁻¹ * c := by group
      _ = z * c := by rw [hcz]
  have hpairEq : Subgroup.closure ({t', z} : Set G) =
      conjSub c (Subgroup.closure ({t, z} : Set G)) := by
    rcases hct with e | e
    · rw [conjSub_closure_pair, hcz, e]
    · rw [← closure_mul_pair_eq z t, conjSub_closure_pair, hcz, e]
  rw [hpairEq, alphaCore_conjSub, hnormB c (hgen hcC)]

theorem BadStd8.false_of_localAxis [IsSimpleGroup G] (h : BadStd8 Ω K J S R T W z t)
    {B : Subgroup G} (hB : Hyp51 B) (hpair : Subgroup.closure ({t, z} : Set G) ≤ B)
    (hgen : Subgroup.centralizer ({z} : Set G) ≤ rankTwoSpan B) : False :=
  h.false_of_localAxis_rank (lemma52 G B hB) hpair hgen

end Axis

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
