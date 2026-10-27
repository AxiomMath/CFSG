module

public import CFSG.ClassicalInvolution.Q3.Q3T8B00

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap

section Close


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem BadStd8.nonabelian (h : BadStd8 Ω K J S R T W z t) : ∃ a b : G, a * b ≠ b * a := by
  obtain ⟨a, -, hac⟩ := IsConcreteLE.not_le_iff_exists.mp
    (isClassicalMember3_of_uniqueInvolution h.std.stand.modU h.std.stand.mem
      h.std.hz).not_le_center
  rw [Subgroup.mem_center_iff] at hac
  push Not at hac
  obtain ⟨b, hb⟩ := hac
  exact ⟨b, a, hb⟩

theorem BadStd8.isElemAbelian2_pair (h : BadStd8 Ω K J S R T W z t) :
    IsElemAbelian2 (Subgroup.closure ({t, z} : Set G)) 2 := by
  have hs := h.std
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hc01 : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
  have hzt : t ≠ z := fun e => by
    have : IsUniqueInvolution J z := e ▸ hs.ht
    exact hs.hJ.2.1 (hnt K hs.stand.mem J ⟨hs.hJ.1, z, hs.hz, this⟩)
  exact T7A.isElemAbelian2_closure_pair hs.ht.sq hs.hz.sq hs.ht.ne_one hs.hz.ne_one hzt hc01.symm

theorem BadStd8.false_of_linkConst [IsSimpleGroup G] (h : BadStd8 Ω K J S R T W z t)
    (hlink : ∀ J' ∈ omegaNbr Ω K, ∀ t' : G, IsUniqueInvolution J' t' →
      alphaOf (Subgroup.closure ({t', z} : Set G)) = alphaOf (Subgroup.closure ({t, z} : Set G)))
    (hodd : Odd (Nat.card ↥(alphaOf (Subgroup.closure ({t, z} : Set G))))) : False := by
  have hs := h.std
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hvertex : ∀ c ∈ Ω, ∀ y₂ : G, IsUniqueInvolution c y₂ → ∃ g : G,
      ∀ L ∈ omegaNbr Ω c, ∀ y : G, IsUniqueInvolution L y →
        alphaOf (Subgroup.closure ({y, y₂} : Set G)) =
          conjSub g (alphaOf (Subgroup.closure ({t, z} : Set G))) := by
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
    rw [← h1, alphaOf_conjSub, h0]
  have hprop : ∀ L ∈ dComp Ω K, L ∈ Ω ∧ ∀ L' ∈ omegaNbr Ω L, ∀ y y' : G,
      IsUniqueInvolution L y → IsUniqueInvolution L' y' →
        alphaOf (Subgroup.closure ({y', y} : Set G)) =
          alphaOf (Subgroup.closure ({t, z} : Set G)) := by
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
      have h1 : alphaOf (Subgroup.closure ({y'', y₂} : Set G)) =
          alphaOf (Subgroup.closure ({yb, y₂} : Set G)) := by
        rw [hg L'' hL'' y'' hy'', hg b hcb.2 yb hyb]
      have h2 : alphaOf (Subgroup.closure ({y₂, yb} : Set G)) =
          alphaOf (Subgroup.closure ({t, z} : Set G)) := hPb c hcb.1 yb y₂ hyb hy₂
      rw [h1, Set.pair_comm]
      exact h2
  have hN : (⊤ : Subgroup G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := by
    intro n _
    have hKn : conjSub n K ∈ dComp Ω K := h.conn K hK _ (hΩ.conjInvariant n K hK)
    obtain ⟨-, hP⟩ := hprop _ hKn
    have h' := hP (conjSub n J) (omegaNbr_conj hΩ.conjInvariant hs.hJ n) (n * z * n⁻¹)
      (n * t * n⁻¹) (hs.hz.conj n) (hs.ht.conj n)
    rw [← conjSub_closure_pair, alphaOf_conjSub] at h'
    exact mem_normalizer_iff_conjSub_eq.mpr h'
  have hnorm : (alphaOf (Subgroup.closure ({t, z} : Set G))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hN)
  rcases hnorm.eq_bot_or_eq_top with h' | h'
  · exact h.bad h'
  · have hord : orderOf z = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hs.hz.sq) hs.hz.ne_one
    have hdvd : 2 ∣ Nat.card G := hord ▸ orderOf_dvd_natCard z
    rw [h', Subgroup.card_top] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem BadStd8.false_of_edgeAxis [IsSimpleGroup G] (h : BadStd8 Ω K J S R T W z t)
    {B : Subgroup G} (hB : EdgeAxis3 t z B) : False := by
  have hF : Subgroup.closure ({t, z} : Set G) ∈ signalizerFunctorEk 2 2 B :=
    ⟨hB.pair_le, by simpa using h.isElemAbelian2_pair.1⟩
  exact h.bad (alphaOf_eq_bot_of_alphaCore_eq_bot (hB.alphaCore_eq_bot h.nonabelian hF))

theorem BadStd8.false_of_hyp51Axis [IsSimpleGroup G] (h : BadStd8 Ω K J S R T W z t)
    {B : Subgroup G} (hB : Hyp51 B) (hzt : Subgroup.closure ({t, z} : Set G) ≤ B)
    (hgen : rankTwoSpan B = ⊤) : False :=
  h.false_of_edgeAxis ⟨hzt, lemma52 G B hB, hgen⟩

end Close

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
