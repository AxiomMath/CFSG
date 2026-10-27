module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePslQuot

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open

theorem pow_pPow_eq_one_zmod {p a : ℕ} (x : Multiplicative (ZMod (p ^ a))) : x ^ p ^ a = 1 := by
  rw [← ofAdd_toAdd x, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]

theorem pow_pPow_eq_one_pi {p a r : ℕ} (c : Fin r → Multiplicative (ZMod (p ^ a))) :
    c ^ p ^ a = 1 :=
  funext fun i => pow_pPow_eq_one_zmod (c i)

theorem pow_eq_one_iff_zmod {p a : ℕ} (m : ℕ) :
    (Multiplicative.ofAdd (1 : ZMod (p ^ a))) ^ m = 1 ↔ p ^ a ∣ m := by
  rw [← orderOf_dvd_iff_pow_eq_one, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

theorem nonscalarPPair_of_frame {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F]
    {n a r : ℕ} (ha : 1 ≤ a) (hpr : p ≤ r) (hrp : ¬ p ∣ Nat.card F - 1 ∨ ¬ p ∣ r)
    (T : (Fin r → Multiplicative (ZMod (p ^ a))) →* GL (Fin n) F)
    (S : Equiv.Perm (Fin r) →* GL (Fin n) F) (hTinj : Function.Injective T)
    (hS : ∀ σ c, S σ * T c * (S σ)⁻¹ = T (c ∘ ⇑(σ⁻¹ : Equiv.Perm (Fin r))))
    (hdetT : ∀ c : Fin r → Multiplicative (ZMod (p ^ a)), ∏ i, c i = 1 →
      ((T c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1)
    (hdetS : ∀ σ : Equiv.Perm (Fin r), σ ^ p = 1 →
      ((S σ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1) :
    NonscalarPPair p (StatedSL n F) := by
  have hp := (Fact.out : p.Prime)
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin r), orderOf σ = p := by
    refine exists_prime_orderOf_dvd_card' p ?_
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact (Nat.Prime.dvd_factorial hp).2 hpr
  have hσp : σ ^ p = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, σ i₀ ≠ i₀ := by
    by_contra hcon
    push Not at hcon
    have h1 : σ = 1 := Equiv.ext hcon
    rw [h1, orderOf_one] at hσ
    exact hp.one_lt.ne hσ
  set g : Multiplicative (ZMod (p ^ a)) := Multiplicative.ofAdd 1 with hg
  have hgord : ∀ m : ℕ, g ^ m = 1 ↔ p ^ a ∣ m := pow_eq_one_iff_zmod
  have hg2 : g ^ 2 ≠ 1 := by
    intro h
    have := Nat.le_of_dvd (by norm_num) ((hgord 2).1 h)
    have h3 : p ≤ p ^ a := Nat.le_self_pow (by omega) p
    omega
  set c : Fin r → Multiplicative (ZMod (p ^ a)) :=
    Pi.mulSingle i₀ g * Pi.mulSingle (σ i₀) g⁻¹ with hc
  have hci₀ : c i₀ = g := by
    simp [hc, Pi.mulSingle_eq_of_ne (Ne.symm hi₀)]
  have hcσ : c (σ i₀) = g⁻¹ := by
    simp [hc, Pi.mulSingle_eq_of_ne hi₀]
  have hprod : ∀ (j : Fin r) (x : Multiplicative (ZMod (p ^ a))),
      ∏ i, (Pi.mulSingle j x : Fin r → Multiplicative (ZMod (p ^ a))) i = x := by
    intro j x
    rw [Finset.prod_eq_single j]
    · simp
    · intro i _ hi
      exact Pi.mulSingle_eq_of_ne (M := fun _ : Fin r => Multiplicative (ZMod (p ^ a))) hi x
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hcprod : ∏ i, c i = 1 := by
    rw [hc]
    simp only [Pi.mul_apply, Finset.prod_mul_distrib, hprod]
    simp
  set d : Fin r → Multiplicative (ZMod (p ^ a)) := fun i => (c (σ i))⁻¹ * c i with hd
  have hdi₀ : d i₀ = g ^ 2 := by
    rw [hd]
    simp only [hcσ, hci₀, inv_inv, pow_two]
  have hdprod : ∏ i, d i = 1 := by
    rw [hd, Finset.prod_mul_distrib, Finset.prod_inv_distrib, Equiv.prod_comp σ c, hcprod]
    simp
  have hSσ : ((S σ : GL (Fin n) F) ^ p) = 1 := by rw [← map_pow, hσp, map_one]
  have hSinv : ∀ c : Fin r → Multiplicative (ZMod (p ^ a)),
      (S σ)⁻¹ * T c * S σ = T (c ∘ ⇑σ) := by
    intro c
    have h := hS σ⁻¹ c
    rw [map_inv, inv_inv, inv_inv] at h
    exact h
  have hcomm : (T c * S σ)⁻¹ * (S σ * T c) = T d := by
    calc (T c * S σ)⁻¹ * (S σ * T c) = ((S σ)⁻¹ * T c * S σ)⁻¹ * T c := by group
      _ = (T (c ∘ ⇑σ))⁻¹ * T c := by rw [hSinv]
      _ = T d := by
        rw [← map_inv, ← map_mul]
        rfl
  have hTpow : ∀ c : Fin r → Multiplicative (ZMod (p ^ a)), (T c) ^ p ^ a = 1 := fun c => by
    rw [← map_pow, pow_pPow_eq_one_pi, map_one]
  have hTrange : IsPGroup p (T.range : Subgroup (GL (Fin n) F)) := by
    intro x
    obtain ⟨c, hc'⟩ := x.2
    refine ⟨a, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hc']
    exact hTpow c
  have hZp : IsPGroup p (Subgroup.zpowers (S σ)) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hSσ
  have hnorm : S σ ∈ Subgroup.normalizer (T.range : Set (GL (Fin n) F)) := by
    apply mem_normalizer_of_conj_mem
    rintro _ ⟨c', rfl⟩
    rw [hS]
    exact ⟨_, rfl⟩
  have hsup : IsPGroup p (Subgroup.zpowers (S σ) ⊔ T.range : Subgroup (GL (Fin n) F)) :=
    hZp.to_sup_of_normal_right' hTrange (Subgroup.zpowers_le.2 hnorm)
  have hxSL : T c ∈ StatedSL n F :=
    CFSG.Open.StatedAPI.mem_statedSL_of_det (hdetT c hcprod)
  have hySL : S σ ∈ StatedSL n F :=
    CFSG.Open.StatedAPI.mem_statedSL_of_det (hdetS σ hσp)
  refine ⟨T c, S σ, hxSL, hySL, hsup.to_le ?_, ?_⟩
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_sup_right ⟨c, rfl⟩
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  · rw [hcomm]
    intro hmem
    rcases hrp with h1 | h2
    ·
      have hdet : ((T d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 :=
        det_eq_one_of_pow_eq_one h1 (hTpow d)
      have hmemN : (⟨T d, CFSG.Open.StatedAPI.mem_statedSL_of_det hdet⟩ : StatedSL n F) ∈
          (StatedScalars (Fin n) F).subgroupOf (StatedSL n F) := hmem
      have hpow : (⟨T d, CFSG.Open.StatedAPI.mem_statedSL_of_det hdet⟩ : StatedSL n F) ^
          p ^ a = 1 := Subtype.ext (by simpa using hTpow d)
      have h0 := eq_one_of_mem_of_pow_eq_one _
        (not_dvd_card_scalars_of_not_dvd_sub_one h1) hmemN hpow
      have h0' : T d = 1 := congrArg Subtype.val h0
      have hd1 : d = 1 := hTinj (by rw [h0', map_one])
      apply hg2
      rw [← hdi₀, hd1]
      rfl
    ·
      have hcen : T d ∈ Subgroup.center (GL (Fin n) F) := by
        rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
        exact hmem
      have hconst : ∀ i j : Fin r, d i = d j := by
        intro i j
        have h1 : S (Equiv.swap i j) * T d = T d * S (Equiv.swap i j) :=
          Subgroup.mem_center_iff.1 hcen _
        have h2 : S (Equiv.swap i j) * T d * (S (Equiv.swap i j))⁻¹ = T d := by
          rw [h1, mul_inv_cancel_right]
        rw [hS, Equiv.swap_inv] at h2
        have h3 := hTinj h2
        have h4 := congrFun h3 i
        simpa [Function.comp_apply, Equiv.swap_apply_left] using h4.symm
      have hdr : (g ^ 2) ^ r = 1 := by
        rw [← hdi₀, ← hdprod]
        rw [Finset.prod_congr rfl (fun i _ => hconst i i₀)]
        simp
      rw [← pow_mul] at hdr
      have h5 : p ^ a ∣ 2 * r := (hgord _).1 hdr
      have h6 : p ∣ 2 * r := (dvd_pow_self p (by omega)).trans h5
      rcases (Nat.Prime.dvd_mul hp).1 h6 with h7 | h7
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h7)
      · exact h2 h7

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
