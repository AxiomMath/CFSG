module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveQuot

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup Equiv Equiv.Perm

theorem cycleType_eq_singleton_five {x : Perm (Fin 10)} (hx : orderOf x = 5)
    (h3 : 3 ∣ Nat.card (centralizer ({x} : Set (Perm (Fin 10))))) : x.cycleType = {5} := by
  have hall : ∀ n ∈ x.cycleType, n = 5 := by
    intro n hn
    have h1 : n ∣ orderOf x := by
      rw [← lcm_cycleType]
      exact Multiset.dvd_lcm hn
    rw [hx] at h1
    have h2 := two_le_of_mem_cycleType hn
    rcases (Nat.dvd_prime Nat.prime_five).1 h1 with h | h
    · omega
    · exact h
  have hsum : x.cycleType.sum ≤ 10 := by
    rw [sum_cycleType]
    simpa using Finset.card_le_univ x.support
  obtain ⟨m, hm⟩ : ∃ m, x.cycleType = Multiset.replicate m 5 :=
    ⟨_, Multiset.eq_replicate_card.2 hall⟩
  rcases m with _ | _ | _ | m
  · exfalso
    have hx1 : x = 1 := cycleType_eq_zero.1 hm
    rw [hx1, orderOf_one] at hx
    omega
  · simpa using hm
  · exfalso
    rw [nat_card_centralizer, hm] at h3
    revert h3
    decide
  · exfalso
    rw [hm] at hsum
    simp at hsum
    omega

private noncomputable def fiveCycle : Perm (Fin 10) := Fin.cycleRange 4

private theorem fiveCycle_cycleType : fiveCycle.cycleType = {5} := by
  rw [fiveCycle, Fin.cycleType_cycleRange (by decide)]
  rfl

private theorem orderOf_fiveCycle : orderOf fiveCycle = 5 := by
  rw [← lcm_cycleType, fiveCycle_cycleType]
  rfl

private theorem fiveCycle_apply_of_le {i : Fin 10} (h : 5 ≤ i.val) : fiveCycle i = i :=
  Fin.cycleRange_of_gt (Fin.lt_def.2 (by simp; omega))

private theorem exists_upper_hom : ∃ u : Perm (Fin 5) →* Perm (Fin 10),
    Function.Injective u ∧ ∀ (σ : Perm (Fin 5)) (i : Fin 10), i.val < 5 → u σ i = i := by
  refine ⟨viaEmbeddingHom (Fin.natAddEmb 5 : Fin 5 ↪ Fin 10), viaEmbeddingHom_injective _,
    fun σ i hi => ?_⟩
  rw [viaEmbeddingHom_apply]
  refine viaEmbedding_apply_of_notMem _ _ i ?_
  rintro ⟨a, rfl⟩
  have h5 : ((Fin.natAddEmb 5 : Fin 5 ↪ Fin 10) a).val = 5 + a.val := rfl
  omega

theorem exists_mulEquiv_centralizer_perm_ten {x : Perm (Fin 10)} (hx : orderOf x = 5)
    (h3 : 3 ∣ Nat.card (centralizer ({x} : Set (Perm (Fin 10))))) :
    Nonempty (↥(centralizer ({x} : Set (Perm (Fin 10)))) ≃*
      Multiplicative (ZMod 5) × Perm (Fin 5)) := by
  have hct := cycleType_eq_singleton_five hx h3
  obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_iff_cycleType_eq.2 (fiveCycle_cycleType.trans hct.symm))
  obtain ⟨u, hu_inj, hu_fix⟩ := exists_upper_hom
  have hpow : fiveCycle ^ 5 = 1 := orderOf_dvd_iff_pow_eq_one.1 (dvd_of_eq orderOf_fiveCycle)
  have hdisj : ∀ σ : Perm (Fin 5), Perm.Disjoint fiveCycle (u σ) := fun σ i => by
    by_cases h : i.val < 5
    · exact Or.inr (hu_fix σ i h)
    · exact Or.inl (fiveCycle_apply_of_le (by omega))
  have hcomm : ∀ (k : Multiplicative (ZMod 5)) (σ : Perm (Fin 5)),
      Commute (zmodPowHom 5 fiveCycle hpow k) (u σ) := fun k σ => by
    rw [zmodPowHom_apply]
    exact ((hdisj σ).commute).pow_left _
  let Φ0 := (zmodPowHom 5 fiveCycle hpow).noncommCoprod u hcomm
  have hΦ0c : ∀ p, Commute fiveCycle (Φ0 p) := fun p => by
    rw [MonoidHom.noncommCoprod_apply, zmodPowHom_apply]
    exact (Commute.pow_right (Commute.refl _) _).mul_right (hdisj p.2).commute
  have hΦ0inj : Function.Injective Φ0 := by
    rw [injective_iff_map_eq_one]
    rintro ⟨k, σ⟩ h
    rw [MonoidHom.noncommCoprod_apply] at h
    have hk : zmodPowHom 5 fiveCycle hpow k = 1 := by
      refine Perm.ext fun i => ?_
      by_cases hi : i.val < 5
      · have := congr_arg (fun f : Perm (Fin 10) => f i) h
        simpa [Perm.mul_apply, hu_fix σ i hi] using this
      · rw [zmodPowHom_apply]
        exact Perm.pow_apply_eq_self_of_apply_eq_self (fiveCycle_apply_of_le (by omega)) _
    have hk1 : k = 1 :=
      zmodPowHom_injective hpow orderOf_fiveCycle (hk.trans (map_one _).symm)
    rw [hk1, map_one, one_mul] at h
    exact Prod.ext hk1 (hu_inj (h.trans (map_one u).symm))
  let Φ : Multiplicative (ZMod 5) × Perm (Fin 5) →* Perm (Fin 10) :=
    (MulAut.conj g).toMonoidHom.comp Φ0
  have hmem : ∀ p, Φ p ∈ centralizer ({x} : Set (Perm (Fin 10))) := fun p => by
    rw [mem_centralizer_singleton_iff]
    have h1 := (hΦ0c p).eq
    calc Φ p * x = g * (Φ0 p * fiveCycle) * g⁻¹ := by simp [← hg, Φ, mul_assoc]
      _ = g * (fiveCycle * Φ0 p) * g⁻¹ := by rw [h1]
      _ = x * Φ p := by simp [← hg, Φ, mul_assoc]
  let Ψ := Φ.codRestrict (centralizer ({x} : Set (Perm (Fin 10)))) hmem
  have hΨinj : Function.Injective Ψ := fun p q h =>
    hΦ0inj ((MulAut.conj g).injective (congr_arg Subtype.val h))
  have hcard : Nat.card (centralizer ({x} : Set (Perm (Fin 10)))) = 600 := by
    rw [nat_card_centralizer, hct]
    decide
  have hbij : Function.Bijective Ψ := by
    refine hΨinj.bijective_of_nat_card_le ?_
    rw [hcard, Nat.card_prod, Nat.card_perm]
    simp [Nat.factorial]
  exact ⟨(MulEquiv.ofBijective Ψ hbij).symm⟩

end CFSG.EvenSporadicStandard.HSStd
