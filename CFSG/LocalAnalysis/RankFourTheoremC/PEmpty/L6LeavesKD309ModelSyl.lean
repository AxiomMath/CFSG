module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309ModelMon
public import CFSG.Sporadic.J4.QT2LocHGen

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309M

open CFSG.LocalAnalysis.RankThreeUC.S15.ACore Subgroup

theorem sylow_monSub {G : Type} [Group G] [Finite G] (T : Sylow 5 G)
    (hT5 : Nat.card (T : Subgroup G) ≤ 5 ^ 5) {C : Type} [CommGroup C] [Finite C] {a : ℕ}
    (hC : Nat.card C = 5 ^ a) (ha : 1 ≤ a) (ψ : ↥(monSub C) →* G)
    (hψ : Function.Injective ψ) :
    Nat.card (T : Subgroup G) = 5 ^ 5 ∧ (∀ t ∈ (T : Subgroup G), t ^ 5 = 1) ∧
      ∃ s ∈ (T : Subgroup G), ∃ t ∈ (T : Subgroup G), s * t ≠ t * s := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set Q : Subgroup G := ψ.range with hQ
  have hQcard : Nat.card Q = 5 ^ (4 * a + 1) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv, card_monSub, hC, ← pow_mul,
      ← pow_succ, mul_comm]
  have hTcard := T.card_eq_multiplicity
  have hdvd : Nat.card Q ∣ Nat.card G := Subgroup.card_subgroup_dvd_card Q
  have hle : 4 * a + 1 ≤ (Nat.card G).factorization 5 := by
    rw [hQcard] at hdvd
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five Nat.card_pos.ne').mp hdvd
  have hv : (Nat.card G).factorization 5 ≤ 5 := by
    rw [hTcard] at hT5
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hT5
  have ha1 : a = 1 := by omega
  subst ha1
  have hv5 : (Nat.card G).factorization 5 = 5 := by omega
  have hTc : Nat.card (T : Subgroup G) = 5 ^ 5 := by rw [hTcard, hv5]
  have hQc : Nat.card Q = 5 ^ 5 := hQcard
  obtain ⟨g, hg⟩ := CFSG.Sporadic.J4.QT2.exists_conj_le_of_card Q (T : Subgroup G)
    (by rw [hQc, hv5]) T.isPGroup'
  have hC5 : ∀ c : C, c ^ 5 = 1 := fun c => by
    have := pow_card_eq_one' (x := c)
    rwa [hC, pow_one] at this
  refine ⟨hTc, fun t ht => ?_, ?_⟩
  · obtain ⟨m, hm⟩ := hg t ht
    have hm5 : m ^ 5 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact pow_five_monSub hC5 m.2)
    have h1 : (g * t * g⁻¹) ^ 5 = 1 := by rw [← hm, ← map_pow, hm5, map_one]
    have h2 : (g * t * g⁻¹) ^ 5 = g * t ^ 5 * g⁻¹ := conj_pow
    rw [h2] at h1
    have h3 := congrArg (fun y => g⁻¹ * y * g) h1
    simpa [mul_assoc] using h3
  · by_contra hall
    push Not at hall
    have hle2 : (T : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ Q := by
      rintro _ ⟨t, ht, rfl⟩
      exact hg t ht
    have hcardmap : Nat.card ((T : Subgroup G).map (MulAut.conj g).toMonoidHom) =
        Nat.card (T : Subgroup G) :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have heq : (T : Subgroup G).map (MulAut.conj g).toMonoidHom = Q :=
      Subgroup.eq_of_le_of_card_ge hle2 (by rw [hcardmap, hTc, hQc])
    have hnt : Nontrivial C := by
      rw [← Finite.one_lt_card_iff_nontrivial, hC]
      exact Nat.one_lt_pow (by omega) (by norm_num)
    obtain ⟨c, hc1⟩ := exists_ne (1 : C)
    have hc2 : c ^ 2 ≠ 1 := by
      intro h2
      apply hc1
      have h5 : c ^ 5 = (c ^ 2) ^ 2 * c := by rw [← pow_mul, ← pow_succ]
      rw [h2, one_pow, one_mul] at h5
      rw [← h5]
      exact hC5 c
    obtain ⟨a', ha', b', hb', hab⟩ := not_comm_monSub hc2
    apply hab
    have hmem : ∀ m : ↥(monSub C), ∃ t ∈ (T : Subgroup G), ψ m = g * t * g⁻¹ := fun m => by
      have : ψ m ∈ (T : Subgroup G).map (MulAut.conj g).toMonoidHom := by
        rw [heq]
        exact ⟨m, rfl⟩
      obtain ⟨t, ht, hm⟩ := this
      exact ⟨t, ht, hm.symm⟩
    obtain ⟨t1, ht1, h1⟩ := hmem ⟨a', ha'⟩
    obtain ⟨t2, ht2, h2⟩ := hmem ⟨b', hb'⟩
    have hcomm : ψ ⟨a', ha'⟩ * ψ ⟨b', hb'⟩ = ψ ⟨b', hb'⟩ * ψ ⟨a', ha'⟩ := by
      rw [h1, h2]
      have := hall t1 ht1 t2 ht2
      calc g * t1 * g⁻¹ * (g * t2 * g⁻¹) = g * (t1 * t2) * g⁻¹ := by group
        _ = g * (t2 * t1) * g⁻¹ := by rw [this]
        _ = g * t2 * g⁻¹ * (g * t1 * g⁻¹) := by group
    rw [← map_mul, ← map_mul] at hcomm
    exact congrArg Subtype.val (hψ hcomm)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309M
