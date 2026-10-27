module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
import TauCeti.RepresentationTheory.CharacterTable.Solvable

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec7l77_even_permVec {n : ℕ} (σ : Equiv.Perm (Fin n)) {v : Fin n → ZMod 2}
    (hv : IsEvenVec v) : IsEvenVec (permVec σ v) := by
  unfold IsEvenVec permVec at *
  simpa [Function.comp] using (Equiv.sum_comp σ.symm v).trans hv

theorem sec7l77_permVec_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (v : Fin n → ZMod 2) :
    permVec σ (permVec τ v) = permVec (σ * τ) v := by
  funext x
  simp [permVec, Equiv.Perm.mul_def]

theorem sec7l77_permVec_one {n : ℕ} (v : Fin n → ZMod 2) : permVec (1 : Equiv.Perm (Fin n)) v = v :=
  rfl

theorem sec7l77_perm_triv :
    ∀ σ : Equiv.Perm (Fin 5), (∀ v : Fin 5 → ZMod 2, ∑ i, v i = 0 → permVec σ v = v) →
      σ = 1 := by
  decide +kernel

theorem sec7l77_perm_five :
    ∀ σ : Equiv.Perm (Fin 5), σ ^ 5 = 1 → ∀ w : Fin 5 → ZMod 2, ∑ i, w i = 0 → w ≠ 0 →
      permVec σ w = w → σ = 1 := by
  decide +kernel

theorem sec7l77_cent_solvable [Finite G] {N B : Subgroup G}
    (hQ : QuotEquivTo N B (Equiv.Perm (Fin 5))) (hB : IsElemAb2 B 4) (hBN : B ≤ N)
    (hCB : N ⊓ centralizer (B : Set G) ≤ B)
    (hφ : ∃ φ : (Fin 5 → ZMod 2) → G, IsPermModuleVia IsEvenVec φ B N ⊤)
    {b : G} (hb : b ∈ B) (hb1 : b ≠ 1) :
    Group.IsSolvable ↥(N ⊓ centralizer ({b} : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨φ, hφ1, hφ2, hφ3, hφ4, -⟩ := hφ
  obtain ⟨ρ, hρs, hρk⟩ := hQ
  have hcardN : Nat.card N = 2 ^ 7 * 3 ^ 1 * 5 := by
    have h1 : Nat.card N = Nat.card (N ⧸ ρ.ker) * Nat.card ρ.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have h2 : Nat.card (N ⧸ ρ.ker) = Nat.card (Equiv.Perm (Fin 5)) :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρs).toEquiv
    have h3 : Nat.card ρ.ker = Nat.card B := by
      rw [hρk]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv
    have h4 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
      simp [Nat.factorial]
    rw [h1, h2, h3, h4, hB.2]
    norm_num
  have hφ0 : φ 0 = 1 := by
    have h := hφ1 0 0 (by simp [IsEvenVec]) (by simp [IsEvenVec])
    rw [add_zero] at h
    exact (mul_eq_left.mp h.symm)
  have h5 : ¬ 5 ∣ Nat.card ↥(N ⊓ centralizer ({b} : Set G)) := by
    intro h5d
    obtain ⟨ν, hν⟩ := exists_prime_orderOf_dvd_card' 5 h5d
    have hνN : (ν : G) ∈ N := ν.2.1
    have hνb : (ν : G) * b = b * (ν : G) := Subgroup.mem_centralizer_singleton_iff.mp ν.2.2
    have hνord : orderOf (ν : G) = 5 := by rw [Subgroup.orderOf_coe]; exact hν
    have hν5 : (ν : G) ^ 5 = 1 := by rw [← hνord]; exact pow_orderOf_eq_one _
    obtain ⟨σ, -, hσ⟩ := hφ4 (ν : G) hνN
    have hpow : ∀ k : ℕ, ∀ v, IsEvenVec v →
        (ν : G) ^ k * φ v * ((ν : G) ^ k)⁻¹ = φ (permVec (σ ^ k) v) := by
      intro k
      induction k with
      | zero => intro v _; simp [sec7l77_permVec_one]
      | succ k ih =>
        intro v hv
        have hk := sec7l77_even_permVec (σ ^ k) hv
        calc (ν : G) ^ (k + 1) * φ v * ((ν : G) ^ (k + 1))⁻¹
            = (ν : G) * ((ν : G) ^ k * φ v * ((ν : G) ^ k)⁻¹) * (ν : G)⁻¹ := by group
          _ = (ν : G) * φ (permVec (σ ^ k) v) * (ν : G)⁻¹ := by rw [ih v hv]
          _ = φ (permVec σ (permVec (σ ^ k) v)) := hσ _ hk
          _ = φ (permVec (σ ^ (k + 1)) v) := by rw [sec7l77_permVec_mul, ← pow_succ']
    have hσ5 : σ ^ 5 = 1 := by
      refine sec7l77_perm_triv _ fun v hv => ?_
      have h := hpow 5 v hv
      rw [hν5] at h
      simp only [one_mul, inv_one, mul_one] at h
      exact (hφ2 _ _ (sec7l77_even_permVec _ hv) hv h.symm)
    obtain ⟨w, hwe, hwb⟩ := (hφ3 b).mp hb
    have hw0 : w ≠ 0 := by
      rintro rfl
      exact hb1 (hwb ▸ hφ0)
    have hfix : permVec σ w = w := by
      have h := hσ w hwe
      rw [hwb] at h
      have h' : (ν : G) * b * (ν : G)⁻¹ = b := by rw [hνb]; group
      rw [h'] at h
      exact hφ2 _ _ (sec7l77_even_permVec σ hwe) hwe (by rw [← h, hwb])
    have hσ1 : σ = 1 := sec7l77_perm_five σ hσ5 w hwe hw0 hfix
    subst hσ1
    have hνB : (ν : G) ∈ centralizer (B : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      obtain ⟨v, hv, rfl⟩ := (hφ3 x).mp hx
      have h := hσ v hv
      rw [sec7l77_permVec_one] at h
      calc φ v * (ν : G) = ((ν : G) * φ v * (ν : G)⁻¹) * (ν : G) := by rw [h]
        _ = (ν : G) * φ v := by group
    have hνB' : (ν : G) ∈ B := hCB ⟨hνN, hνB⟩
    have hν2 : (ν : G) ^ 2 = 1 := hB.1.2 _ hνB'
    have hν1 : (ν : G) = 1 := by
      calc (ν : G) = (ν : G) ^ 5 * (((ν : G) ^ 2)⁻¹) ^ 2 := by group
        _ = 1 := by rw [hν5, hν2]; simp
    rw [hν1, orderOf_one] at hνord
    norm_num at hνord
  have hdvd : Nat.card ↥(N ⊓ centralizer ({b} : Set G)) ∣ Nat.card N :=
    Subgroup.card_dvd_of_le inf_le_left
  have hcop : Nat.Coprime (Nat.card ↥(N ⊓ centralizer ({b} : Set G))) 5 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr h5).symm
  have hfin : Nat.card ↥(N ⊓ centralizer ({b} : Set G)) ∣ 2 ^ 7 * 3 ^ 1 :=
    hcop.dvd_of_dvd_mul_right (hcardN ▸ hdvd)
  exact TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow Nat.prime_two Nat.prime_three hfin

end CFSG.OddStandard.SmallF3.Omega
