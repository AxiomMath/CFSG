module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3A1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma perm3_conj_eq_or_inv : ∀ x y n : Equiv.Perm (Fin 3),
    y = n * x * n⁻¹ → x ^ 3 = 1 → y = x ∨ y = x⁻¹ := by
  decide

private lemma exists_conj_eq_or_inv_mul_of_secProp_perm3 {Γ : Type} [Group Γ] [Finite Γ]
    {N K : Subgroup Γ}
    (h : SecProp N K (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))))
    {k : Γ} (hkN : k ∈ N) (hk3 : k ^ 3 = 1) (hkK : k ∈ normalizer (K : Set Γ)) :
    ∀ n ∈ N, ∃ b ∈ K, n * k * n⁻¹ = k * b ∨ n * k * n⁻¹ = k⁻¹ * b := by
  obtain ⟨hKn, ⟨e⟩⟩ := h
  haveI := hKn
  let φ : ↥N →* Equiv.Perm (Fin 3) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (K.subgroupOf N))
  have hker : ∀ x : ↥N, φ x = 1 ↔ (x : Γ) ∈ K := by
    intro x
    have h1 : φ x = 1 ↔ QuotientGroup.mk' (K.subgroupOf N) x = 1 := by
      constructor
      · intro hx
        exact e.injective (by simpa [φ] using hx)
      · intro hx
        change e (QuotientGroup.mk' (K.subgroupOf N) x) = 1
        rw [hx, map_one]
    rw [h1, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf
  intro n hnN
  have hx3 : (φ ⟨k, hkN⟩) ^ 3 = 1 := by
    rw [← map_pow,
      show (⟨k, hkN⟩ : ↥N) ^ 3 = 1 from Subtype.ext (by simpa using hk3), map_one]
  have hy : φ (⟨n, hnN⟩ * ⟨k, hkN⟩ * ⟨n, hnN⟩⁻¹) =
      φ ⟨n, hnN⟩ * φ ⟨k, hkN⟩ * (φ ⟨n, hnN⟩)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  obtain hcase | hcase := perm3_conj_eq_or_inv (φ ⟨k, hkN⟩)
    (φ (⟨n, hnN⟩ * ⟨k, hkN⟩ * ⟨n, hnN⟩⁻¹)) (φ ⟨n, hnN⟩) hy hx3
  · have hφ1 : φ (⟨n, hnN⟩ * ⟨k, hkN⟩ * ⟨n, hnN⟩⁻¹ * ⟨k, hkN⟩⁻¹) = 1 := by
      rw [map_mul, hcase, map_inv, mul_inv_cancel]
    have hb' : n * k * n⁻¹ * k⁻¹ ∈ K := by
      have := (hker _).mp hφ1
      simpa using this
    refine ⟨k⁻¹ * (n * k * n⁻¹ * k⁻¹) * k, ?_, Or.inl ?_⟩
    · simpa [inv_inv] using (Subgroup.mem_normalizer_iff.mp (inv_mem hkK) _).mp hb'
    · group
  · have hφ1 : φ (⟨n, hnN⟩ * ⟨k, hkN⟩ * ⟨n, hnN⟩⁻¹ * ⟨k, hkN⟩) = 1 := by
      rw [map_mul, hcase, inv_mul_cancel]
    have hb' : n * k * n⁻¹ * k ∈ K := by
      have := (hker _).mp hφ1
      simpa using this
    refine ⟨k * (n * k * n⁻¹ * k) * k⁻¹, ?_, Or.inr ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hkK _).mp hb'
    · group

theorem f3_exists_k {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∃ k : G, k ∈ normIn L s.fr.B ∧ k ^ 3 = 1 ∧ k ≠ 1 ∧
      (∀ v ∈ cen s.fr.B, k * v * k⁻¹ = v → v = 1) ∧
      (∀ u ∈ cen s.fr.B, u ≠ 1 → ∀ v ∈ cen s.fr.B, v ≠ 1 → ∃ i : ℕ, k ^ i * u * (k ^ i)⁻¹ = v) ∧
      (∀ n ∈ normIn L s.fr.B, ∃ b ∈ s.fr.B, n * k * n⁻¹ = k * b ∨ n * k * n⁻¹ = k⁻¹ * b) := by
  classical
  obtain ⟨-, -, h3c, h3d, h3e, -⟩ := hH.hLF.fact18.2.1
  have hzL : zL L = ⊥ := f3_zL_eq_bot hH
  change ∃ k ∈ normIn L s.fr.B, IsPGroup 3 (zpowers k) ∧ k ∉ zL L at h3d
  obtain ⟨k₀, hk₀N, hk₀p, hk₀zL⟩ := h3d
  have hk₀1 : k₀ ≠ 1 := by simpa [hzL] using hk₀zL
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3dvd : 3 ∣ Nat.card ↥(zpowers k₀) := by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_mk k₀ (Subgroup.mem_zpowers k₀)]
    exact hk₀p.dvd_orderOf (by
      intro h
      exact hk₀1 (Subtype.ext_iff.mp h))
  obtain ⟨κ, hκord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(zpowers k₀)) 3 h3dvd
  have hkN : (κ : G) ∈ normIn L s.fr.B := (Subgroup.zpowers_le.mpr hk₀N) κ.2
  have hkord : orderOf (κ : G) = 3 := by rw [Subgroup.orderOf_coe κ, hκord]
  have hk3 : (κ : G) ^ 3 = 1 := by rw [← hkord]; exact pow_orderOf_eq_one _
  have hk1 : (κ : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hkord
    norm_num at hkord
  have hkp : IsPGroup 3 ↥(zpowers (κ : G)) :=
    IsPGroup.of_card (n := 1) (by simp [Nat.card_zpowers, hkord])
  have hkzL : (κ : G) ∉ zL L := by rw [hzL]; simpa using hk1
  have htran : ActsTransitively (zpowers (κ : G)) (cen s.fr.B) ⊥ :=
    (h3e (κ : G) hkN hkp hkzL).2.1
  have htrans : ∀ u ∈ cen s.fr.B, u ≠ 1 → ∀ v ∈ cen s.fr.B, v ≠ 1 →
      ∃ i : ℕ, (κ : G) ^ i * u * ((κ : G) ^ i)⁻¹ = v := by
    intro u huV hu1 v hvV hv1
    have hgu : u ∉ (⊥ : Subgroup G) := by rwa [Subgroup.mem_bot]
    have hgv : v ∉ (⊥ : Subgroup G) := by rwa [Subgroup.mem_bot]
    obtain ⟨k', hk'z, hk'v⟩ := htran.2.2 u huV hgu v hvV hgv
    have hku : k' * u * k'⁻¹ = v := by
      have h1 : v⁻¹ * (k' * u * k'⁻¹) = 1 := Subgroup.mem_bot.mp hk'v
      have h2 := congrArg (fun x => v * x) h1
      simpa [mul_assoc] using h2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hk'z
    have hj3 : ((j % (3 : ℤ)).toNat : ℤ) = j % (3 : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg j (by norm_num))
    have h1 : (κ : G) ^ (j % (3 : ℤ)) = (κ : G) ^ j := by
      simpa [hkord] using zpow_mod_orderOf (κ : G) j
    have hzpow : (κ : G) ^ j = (κ : G) ^ (j % 3).toNat := by
      rw [← h1, ← zpow_natCast, hj3]
    exact ⟨(j % 3).toNat, by rw [hzpow.symm.trans hj]; exact hku⟩
  have hfix : ∀ v ∈ cen s.fr.B, (κ : G) * v * (κ : G)⁻¹ = v → v = 1 := by
    intro v hvV hfixv
    by_contra hv1
    obtain ⟨w, hwV, hzV, hw1, hz1, hwz, -, -, -, -⟩ := f3_V_elems hH
    have hpow : ∀ i : ℕ, (κ : G) ^ i * v * ((κ : G) ^ i)⁻¹ = v := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        rw [pow_succ, mul_inv_rev]
        calc (κ : G) ^ i * (κ : G) * v * ((κ : G)⁻¹ * ((κ : G) ^ i)⁻¹)
            = (κ : G) ^ i * ((κ : G) * v * (κ : G)⁻¹) * ((κ : G) ^ i)⁻¹ := by group
          _ = (κ : G) ^ i * v * ((κ : G) ^ i)⁻¹ := by rw [hfixv]
          _ = v := ih
    have hvw : v = w := by
      obtain ⟨i, hi⟩ := htrans v hvV hv1 w hwV hw1
      rw [hpow i] at hi
      exact hi
    have hvz : v = s.fr.z := by
      obtain ⟨i, hi⟩ := htrans v hvV hv1 s.fr.z hzV hz1
      rw [hpow i] at hi
      exact hi
    exact hwz (hvw ▸ hvz)
  have h3c' : SecProp (normIn L s.fr.B) s.fr.B
      (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) := by
    have h : SecProp (normIn L s.fr.B) (zL L ⊔ s.fr.B)
        (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) := h3c
    rwa [hzL, bot_sup_eq] at h
  exact ⟨(κ : G), hkN, hk3, hk1, hfix, htrans,
    exists_conj_eq_or_inv_mul_of_secProp_perm3 h3c' hkN hk3 hkN.2⟩

end CFSG.OddStandard.HigherRank.YamadaG23
