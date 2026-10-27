module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePslQuot
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureVacuous
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePslNonab

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open

structure BlockFrame (C : Type) [Group C] (r : ℕ) (G : Type) [Group G] where
  T : (Fin r → C) →* G
  S : Equiv.Perm (Fin r) →* G
  T_injective : Function.Injective T
  S_conj : ∀ σ c, S σ * T c * (S σ)⁻¹ = T (c ∘ ⇑(σ⁻¹ : Equiv.Perm (Fin r)))
  exists_inv : ∀ i : Fin r, ∃ g : G, ∀ c, g * T c * g⁻¹ = T (Function.update c i (c i)⁻¹)

namespace BlockFrame

variable {C : Type} [Group C] {r : ℕ} {G G' : Type} [Group G] [Group G']

@[expose] def map (F : BlockFrame C r G) (h : G →* G') (hinj : Function.Injective (h.comp F.T)) :
    BlockFrame C r G' where
  T := h.comp F.T
  S := h.comp F.S
  T_injective := hinj
  S_conj σ c := by
    change h (F.S σ) * h (F.T c) * (h (F.S σ))⁻¹ = h (F.T (c ∘ ⇑(σ⁻¹ : Equiv.Perm (Fin r))))
    rw [← map_inv, ← map_mul, ← map_mul, F.S_conj]
  exists_inv i := by
    obtain ⟨g, hg⟩ := F.exists_inv i
    refine ⟨h g, fun c => ?_⟩
    change h g * h (F.T c) * (h g)⁻¹ = h (F.T (Function.update c i (c i)⁻¹))
    rw [← map_inv, ← map_mul, ← map_mul, hg]

theorem normalizerMovesLines {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) [Finite G] {a : ℕ} (hr : 2 ≤ r)
    (F : BlockFrame (Multiplicative (ZMod (p ^ a))) r G) : NormalizerMovesLines p F.T.range := by
  have hp := (Fact.out : p.Prime)
  refine normalizerMovesLines_range_twisted hr F.T F.T_injective ?_ ⟨0, by omega⟩ ?_
  · intro i j
    refine ⟨F.S (Equiv.swap i j), fun c => ?_⟩
    rw [F.S_conj, Equiv.swap_inv]
  · obtain ⟨g, hg⟩ := F.exists_inv ⟨0, by omega⟩
    refine ⟨g, -1, ?_, fun c => ?_⟩
    · intro h
      have h2 : (p : ℤ) ∣ ((2 : ℕ) : ℤ) := by
        have e : (-1 : ℤ) - 1 = -((2 : ℕ) : ℤ) := by norm_num
        rw [e, dvd_neg] at h
        exact h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (Int.natCast_dvd_natCast.1 h2))
    · rw [zpow_neg_one]
      exact hg c

theorem hasNoncommPair {p : ℕ} [Fact p.Prime] {a : ℕ} (ha : 1 ≤ a) (hpr : p ≤ r)
    (F : BlockFrame (Multiplicative (ZMod (p ^ a))) r G) :
    CFSG.RankThree.PartOne.StrongP.HasNoncommPair p G := by
  have hp := (Fact.out : p.Prime)
  haveI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin r), orderOf σ = p := by
    refine exists_prime_orderOf_dvd_card' p ?_
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact (Nat.Prime.dvd_factorial hp).2 hpr
  have hσp : σ ^ p = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
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
  have hxp : F.S σ ^ p = 1 := by rw [← map_pow, hσp, map_one]
  have hyp : F.T (Pi.mulSingle i₀ g) ^ p = 1 := by
    rw [← map_pow, ← Pi.mulSingle_pow, hgp]
    simp
  refine ⟨F.S σ, F.T (Pi.mulSingle i₀ g), hxp, hyp, ?_, ?_⟩
  ·
    intro hxy
    have h1 : F.S σ * F.T (Pi.mulSingle i₀ g) * (F.S σ)⁻¹ = F.T (Pi.mulSingle i₀ g) := by
      rw [hxy, mul_inv_cancel_right]
    rw [F.S_conj] at h1
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
    have hZp : IsPGroup p (Subgroup.zpowers (F.S σ)) := by
      refine IsPGroup.of_card_dvd_pow (n := 1) ?_
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one hxp
    have hnorm : F.S σ ∈ Subgroup.normalizer (F.T.range : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      simp only [SetLike.mem_coe, MonoidHom.mem_range]
      constructor
      · rintro ⟨d, rfl⟩
        exact ⟨d ∘ ⇑(σ⁻¹), (F.S_conj σ d).symm⟩
      · rintro ⟨e, he⟩
        refine ⟨e ∘ ⇑σ, ?_⟩
        have h1 := F.S_conj σ⁻¹ e
        simp only [map_inv, inv_inv] at h1
        rw [← h1, he]
        group
    have hsup : IsPGroup p (Subgroup.zpowers (F.S σ) ⊔ F.T.range : Subgroup G) :=
      hZp.to_sup_of_normal_right' hTrange (Subgroup.zpowers_le.2 hnorm)
    refine hsup.to_le ?_
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right ⟨_, rfl⟩

theorem wcOn {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) [Finite G] {a : ℕ} (ha : 1 ≤ a)
    (F : BlockFrame (Multiplicative (ZMod (p ^ a))) r G)
    (hcard : (Nat.card G).factorization p = a * r + r.factorial.factorization p) : WCOn p G := by
  have hp := (Fact.out : p.Prime)
  by_cases hpr : p ≤ r
  · exact WCOn.of_hasNoncommPair (F.hasNoncommPair ha hpr)
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
    exact wcOn_of_range_nml F.T F.T_injective hT (BlockFrame.normalizerMovesLines hp2 hr2 F)

end BlockFrame

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
