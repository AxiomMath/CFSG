module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieBlockFrame
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePslNonab

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open

structure TwistFrame (C : Type) [Group C] (r : ℕ) (G : Type) [Group G] (μ : ℤ) where
  T : (Fin r → C) →* G
  A : alternatingGroup (Fin r) →* G
  T_injective : Function.Injective T
  A_conj : ∀ (σ : alternatingGroup (Fin r)) c,
    A σ * T c * (A σ)⁻¹ = T (c ∘ ⇑((σ : Equiv.Perm (Fin r))⁻¹))
  exists_swap : ∀ i j : Fin r, ∃ g : G, ∀ c, g * T c * g⁻¹ = T (c ∘ Equiv.swap i j)
  exists_twist : ∀ i : Fin r, ∃ g : G, ∀ c, g * T c * g⁻¹ = T (Function.update c i (c i ^ μ))

namespace TwistFrame

variable {C : Type} [Group C] {r : ℕ} {G G' : Type} [Group G] [Group G'] {μ : ℤ}

@[expose] def map (F : TwistFrame C r G μ) (h : G →* G')
    (hinj : Function.Injective (h.comp F.T)) : TwistFrame C r G' μ where
  T := h.comp F.T
  A := h.comp F.A
  T_injective := hinj
  A_conj σ c := by
    change h (F.A σ) * h (F.T c) * (h (F.A σ))⁻¹ =
      h (F.T (c ∘ ⇑((σ : Equiv.Perm (Fin r))⁻¹)))
    rw [← map_inv, ← map_mul, ← map_mul, F.A_conj]
  exists_swap i j := by
    obtain ⟨g, hg⟩ := F.exists_swap i j
    refine ⟨h g, fun c => ?_⟩
    change h g * h (F.T c) * (h g)⁻¹ = h (F.T (c ∘ Equiv.swap i j))
    rw [← map_inv, ← map_mul, ← map_mul, hg]
  exists_twist i := by
    obtain ⟨g, hg⟩ := F.exists_twist i
    refine ⟨h g, fun c => ?_⟩
    change h g * h (F.T c) * (h g)⁻¹ = h (F.T (Function.update c i (c i ^ μ)))
    rw [← map_inv, ← map_mul, ← map_mul, hg]

theorem normalizerMovesLines {p : ℕ} [Fact p.Prime] [Finite G] {a : ℕ} (hr : 2 ≤ r)
    (hμ : ¬ (p : ℤ) ∣ μ - 1) (F : TwistFrame (Multiplicative (ZMod (p ^ a))) r G μ) :
    NormalizerMovesLines p F.T.range := by
  obtain ⟨g, hg⟩ := F.exists_twist ⟨0, by omega⟩
  exact normalizerMovesLines_range_twisted hr F.T F.T_injective F.exists_swap ⟨0, by omega⟩
    ⟨g, μ, hμ, hg⟩

theorem hasNoncommPair {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {a : ℕ} (ha : 1 ≤ a) (hpr : p ≤ r)
    (F : TwistFrame (Multiplicative (ZMod (p ^ a))) r G μ) :
    CFSG.RankThree.PartOne.StrongP.HasNoncommPair p G := by
  have hp := (Fact.out : p.Prime)
  have hodd : Odd p := hp.odd_of_ne_two hp2
  haveI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin r), orderOf σ = p := by
    refine exists_prime_orderOf_dvd_card' p ?_
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact (Nat.Prime.dvd_factorial hp).2 hpr
  have hσp : σ ^ p = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hsign : Equiv.Perm.sign σ = 1 := by
    have h : Equiv.Perm.sign (σ ^ p) = 1 := by rw [hσp, map_one]
    rw [map_pow, Int.units_pow_eq_pow_mod_two, Nat.odd_iff.1 hodd, pow_one] at h
    exact h
  obtain ⟨τ, hτσ⟩ : ∃ τ : alternatingGroup (Fin r), (τ : Equiv.Perm (Fin r)) = σ :=
    ⟨⟨σ, Equiv.Perm.mem_alternatingGroup.2 hsign⟩, rfl⟩
  have hτp : τ ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, hτσ, hσp])
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin r, σ i₀ ≠ i₀ := by
    by_contra hcon
    push Not at hcon
    have h1 : σ = 1 := Equiv.ext hcon
    rw [h1, orderOf_one] at hσ
    exact hp.one_lt.ne hσ
  obtain ⟨g, hg⟩ : ∃ g : Multiplicative (ZMod (p ^ a)), orderOf g = p := by
    refine exists_prime_orderOf_dvd_card' p ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    exact dvd_pow_self p (by omega)
  have hgp : g ^ p = 1 := by
    have h := pow_orderOf_eq_one g
    rwa [hg] at h
  have hg1 : g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hg
    exact hp.one_lt.ne hg
  have hxp : F.A τ ^ p = 1 := by rw [← map_pow, hτp, map_one]
  have hyp : F.T (Pi.mulSingle i₀ g) ^ p = 1 := by
    rw [← map_pow, ← Pi.mulSingle_pow, hgp]
    simp
  refine ⟨F.A τ, F.T (Pi.mulSingle i₀ g), hxp, hyp, ?_, ?_⟩
  ·
    intro hxy
    have h1 : F.A τ * F.T (Pi.mulSingle i₀ g) * (F.A τ)⁻¹ = F.T (Pi.mulSingle i₀ g) := by
      rw [hxy, mul_inv_cancel_right]
    rw [F.A_conj, hτσ] at h1
    have h2 := congrFun (F.T_injective h1) (σ i₀)
    simp only [Function.comp_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply,
      Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hi₀] at h2
    exact hg1 h2
  ·
    have hTrange : IsPGroup p (F.T.range : Subgroup G) := by
      intro z
      obtain ⟨d, hd⟩ := z.2
      refine ⟨a, Subtype.ext ?_⟩
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← hd, ← map_pow, pow_pPow_eq_one_pi, map_one]
    have hZp : IsPGroup p (Subgroup.zpowers (F.A τ)) := by
      refine IsPGroup.of_card_dvd_pow (n := 1) ?_
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one hxp
    have hnorm : F.A τ ∈ Subgroup.normalizer (F.T.range : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      simp only [SetLike.mem_coe, MonoidHom.mem_range]
      constructor
      · rintro ⟨d, rfl⟩
        exact ⟨d ∘ ⇑((τ : Equiv.Perm (Fin r))⁻¹), (F.A_conj τ d).symm⟩
      · rintro ⟨e, he⟩
        refine ⟨e ∘ ⇑(τ : Equiv.Perm (Fin r)), ?_⟩
        have h1 := F.A_conj τ⁻¹ e
        simp only [map_inv, inv_inv, Subgroup.coe_inv] at h1
        rw [← h1, he]
        group
    have hsup : IsPGroup p (Subgroup.zpowers (F.A τ) ⊔ F.T.range : Subgroup G) :=
      hZp.to_sup_of_normal_right' hTrange (Subgroup.zpowers_le.2 hnorm)
    refine hsup.to_le ?_
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right ⟨_, rfl⟩

theorem wcOn {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) [Finite G] {a : ℕ} (ha : 1 ≤ a)
    (hμ : ¬ (p : ℤ) ∣ μ - 1) (F : TwistFrame (Multiplicative (ZMod (p ^ a))) r G μ)
    (hcard : (Nat.card G).factorization p = a * r + r.factorial.factorization p) : WCOn p G := by
  have hp := (Fact.out : p.Prime)
  by_cases hpr : p ≤ r
  · exact WCOn.of_hasNoncommPair (F.hasNoncommPair hp2 ha hpr)
  push Not at hpr
  have hfac : r.factorial.factorization p = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro h
    have := (Nat.Prime.dvd_factorial hp).1 h
    omega
  rw [hfac, add_zero] at hcard
  haveI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hT : Nat.card (Fin r → Multiplicative (ZMod (p ^ a))) =
      p ^ (Nat.card G).factorization p := by
    rw [hcard, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card, ← pow_mul]
  by_cases hr0 : r = 0
  · subst hr0
    refine WCOn.of_factorization_le_one ?_
    simp [hcard]
  by_cases hr1 : r = 1
  · subst hr1
    haveI : IsCyclic (Fin 1 → Multiplicative (ZMod (p ^ a))) :=
      isCyclic_of_surjective (MulEquiv.funUnique (Fin 1) (Multiplicative (ZMod (p ^ a)))).symm
        (MulEquiv.funUnique (Fin 1) (Multiplicative (ZMod (p ^ a)))).symm.surjective
    exact wcOn_of_range_cyclic F.T F.T_injective hT
  · have hr2 : 2 ≤ r := by omega
    exact wcOn_of_range_nml F.T F.T_injective hT (TwistFrame.normalizerMovesLines hr2 hμ F)

end TwistFrame

@[expose] def BlockFrame.toTwistFrame {C : Type} [Group C] {r : ℕ} {G : Type} [Group G]
    (F : BlockFrame C r G) : TwistFrame C r G (-1) where
  T := F.T
  A := F.S.comp (alternatingGroup (Fin r)).subtype
  T_injective := F.T_injective
  A_conj σ c := F.S_conj σ c
  exists_swap i j := ⟨F.S (Equiv.swap i j), fun c => by rw [F.S_conj, Equiv.swap_inv]⟩
  exists_twist i := by
    obtain ⟨g, hg⟩ := F.exists_inv i
    exact ⟨g, fun c => by rw [hg, zpow_neg_one]⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
