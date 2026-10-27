module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.AltRho

open Subgroup Equiv Equiv.Perm

variable {A : Type} [Group A]


theorem sign_eq_one_of_odd_orderOf {n : ℕ} {v : Perm (Fin n)} (hv : Odd (orderOf v)) :
    Perm.sign v = 1 := by
  have h1 : Perm.sign v ^ orderOf v = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  rcases Int.units_eq_one_or (Perm.sign v) with h | h
  · exact h
  · rw [h, hv.neg_one_pow] at h1
    exact absurd h1 (by decide)

theorem exists_odd_power {k : A} (hk : orderOf k ≠ 0) {r : ℕ} (hr : Odd r) :
    ∃ j : ℕ, Odd (orderOf (k ^ j)) ∧ j % r = 1 % r := by
  obtain ⟨b, m, hm, hbm⟩ := Nat.exists_eq_two_pow_mul_odd hk
  have hco : Nat.Coprime (2 ^ b) r := Nat.Coprime.pow_left b (Nat.coprime_two_left.mpr hr)
  obtain ⟨j, hj0, hj1⟩ := Nat.chineseRemainder hco 0 1
  refine ⟨j, ?_, hj1⟩
  have hdvd : 2 ^ b ∣ j := (Nat.modEq_zero_iff_dvd).mp hj0
  obtain ⟨j', rfl⟩ := hdvd
  have h1 : (k ^ (2 ^ b * j')) ^ m = 1 := by
    rw [← pow_mul, show 2 ^ b * j' * m = (2 ^ b * m) * j' by ring, pow_mul, ← hbm, pow_orderOf_eq_one,
      one_pow]
  exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one h1)





theorem exists_rho (K : Subgroup A) [K.Normal] [Group.IsPerfect ↥K] {n : ℕ} (hn5 : 5 ≤ n)
    (hn6 : n ≠ 6) (e : (↥K ⧸ center ↥K) ≃* alternatingGroup (Fin n)) :
    ∃ ρ : A →* Perm (Fin n),
      (∀ k : ↥K, ρ (k : A) = ((e (QuotientGroup.mk k) : alternatingGroup (Fin n)) : Perm (Fin n))) ∧
      ρ.ker = centralizer (K : Set A) := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6
  let c : Perm (Fin n) →* MulAut (alternatingGroup (Fin n)) := MulAut.conjNormal
  let eAut : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) := MulEquiv.ofBijective c hbij
  let ρ₁ : A →* MulAut ↥K := MulAut.conjNormal
  let ρ₂ := CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K
  let ρ₃ : MulAut (↥K ⧸ center ↥K) ≃* MulAut (alternatingGroup (Fin n)) := MulAut.congr e
  let ρ : A →* Perm (Fin n) := eAut.symm.toMonoidHom.comp (ρ₃.toMonoidHom.comp (ρ₂.comp ρ₁))
  have hρ : ∀ a, eAut (ρ a) = ρ₃ (ρ₂ (ρ₁ a)) := fun a => by
    simp [ρ]
  refine ⟨ρ, ?_, ?_⟩
  · intro k
    apply eAut.injective
    rw [hρ]
    refine MulEquiv.ext (fun s => ?_)
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.symm s)
    have hs : s = e (QuotientGroup.mk x) := by rw [hx]; simp
    have h3 : (ρ₁ (k : A)) x = k * x * k⁻¹ := by
      rw [show ρ₁ (k : A) = MulAut.conj k from MulAut.conjNormal_val]
      rfl
    have h2 : (ρ₂ (ρ₁ (k : A))) (QuotientGroup.mk x) =
        QuotientGroup.mk k * QuotientGroup.mk x * (QuotientGroup.mk k)⁻¹ := by
      have := CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk
        (ρ₁ (k : A)) x
      rw [h3] at this
      exact this
    apply Subtype.ext
    have h1 : (ρ₃ (ρ₂ (ρ₁ ↑k))) s = e ((ρ₂ (ρ₁ ↑k)) (e.symm s)) := rfl
    rw [h1, ← hx, h2, map_mul, map_mul, map_inv]
    have h4 : ((eAut ↑(e ↑k)) s : Perm (Fin n)) = ↑(e ↑k) * ↑s * (↑(e ↑k))⁻¹ := rfl
    rw [h4, hs]
    simp
  · ext a
    have hiff : ρ a = 1 ↔ ρ₁ a = 1 := by
      constructor
      · intro h
        have h1 : ρ₃ (ρ₂ (ρ₁ a)) = 1 := by
          have := hρ a
          rw [h, map_one] at this
          exact this.symm
        have h2 : ρ₂ (ρ₁ a) = 1 := ρ₃.injective (by rw [h1, map_one])
        exact CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective ↥K
          (by rw [h2, map_one])
      · intro h
        show eAut.symm (ρ₃ (ρ₂ (ρ₁ a))) = 1
        rw [h, map_one, map_one, map_one]
    rw [MonoidHom.mem_ker, hiff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h x hx
      have := congrArg (fun φ : MulAut ↥K => (φ ⟨x, hx⟩ : A)) h
      simp only [ρ₁, MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc x * a = (a * x * a⁻¹) * a := by rw [this]
        _ = a * x := by group
    · intro h
      refine MulEquiv.ext (fun x => ?_)
      apply Subtype.ext
      simp only [ρ₁, MulAut.conjNormal_apply, MulAut.one_apply]
      have := h x x.2
      calc a * (x : A) * a⁻¹ = (x * a) * a⁻¹ := by rw [← this]
        _ = x := by group




theorem exists_odd_lift [Finite A] (K : Subgroup A) [K.Normal] {n : ℕ}
    (ρ : A →* Perm (Fin n)) (e : (↥K ⧸ center ↥K) ≃* alternatingGroup (Fin n))
    (hρK : ∀ k : ↥K, ρ (k : A) = ((e (QuotientGroup.mk k) : alternatingGroup (Fin n)) : Perm (Fin n)))
    (hρker : ρ.ker = centralizer (K : Set A)) (hZ2 : IsPGroup 2 ↥(center ↥K))
    {zb : A} {v : Perm (Fin n)} (hv : Odd (orderOf v)) (hvy : v * ρ zb = ρ zb * v) :
    ∃ k₁ ∈ K, zb * k₁ * zb⁻¹ = k₁ ∧ ρ k₁ = v := by
  classical
  have hsign := sign_eq_one_of_odd_orderOf hv
  obtain ⟨q, hq⟩ := e.surjective ⟨v, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  have hρk : ρ (k : A) = v := by rw [hρK, hq]
  have hNk : orderOf (k : A) ≠ 0 := (orderOf_pos _).ne'
  obtain ⟨j, hjodd, hjmod⟩ := exists_odd_power hNk hv
  set k₁ : A := (k : A) ^ j with hk₁
  have hk₁K : k₁ ∈ K := K.pow_mem k.2 j
  have hρk₁ : ρ k₁ = v := by
    rw [hk₁, map_pow, hρk]
    calc v ^ j = v ^ (j % orderOf v) := (pow_mod_orderOf v j).symm
      _ = v ^ (1 % orderOf v) := by rw [hjmod]
      _ = v ^ 1 := pow_mod_orderOf v 1
      _ = v := pow_one v
  have hz'K : zb * k₁ * zb⁻¹ ∈ K := (inferInstance : K.Normal).conj_mem k₁ hk₁K zb
  set w : A := k₁⁻¹ * (zb * k₁ * zb⁻¹) with hw
  have hwK : w ∈ K := K.mul_mem (K.inv_mem hk₁K) hz'K
  have hρw : ρ w = 1 := by
    rw [hw, map_mul, map_inv, hρk₁, map_mul, map_mul, map_inv, hρk₁]
    calc v⁻¹ * (ρ zb * v * (ρ zb)⁻¹) = v⁻¹ * (v * ρ zb * (ρ zb)⁻¹) := by rw [hvy]
      _ = 1 := by group
  have hwC : w ∈ centralizer (K : Set A) := by
    rw [← hρker]; exact hρw
  have hwc : (⟨w, hwK⟩ : ↥K) ∈ center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hwC g g.2
  have hcomm : k₁ * w = w * k₁ := Subgroup.mem_centralizer_iff.mp hwC k₁ hk₁K
  have hk₁w : zb * k₁ * zb⁻¹ = k₁ * w := by rw [hw]; group
  have hwpow : w ^ orderOf k₁ = 1 := by
    have h1 : (zb * k₁ * zb⁻¹) ^ orderOf k₁ = 1 := by
      rw [conj_pow, pow_orderOf_eq_one]; group
    rw [hk₁w, (Commute.mul_pow (show Commute k₁ w from hcomm)), pow_orderOf_eq_one, one_mul] at h1
    exact h1
  let c : ↥(center ↥K) := ⟨⟨w, hwK⟩, hwc⟩
  have hcpow : c ^ orderOf k₁ = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simpa using hwpow
  obtain ⟨s, hs⟩ := (IsPGroup.iff_orderOf.mp hZ2) c
  have hs0 : s = 0 := by
    by_contra hs0
    have h2 : 2 ∣ orderOf c := by rw [hs]; exact dvd_pow_self 2 hs0
    have h3 : 2 ∣ orderOf k₁ := h2.trans (orderOf_dvd_of_pow_eq_one hcpow)
    exact (Nat.not_even_iff_odd.mpr hjodd) (even_iff_two_dvd.mpr h3)
  have hc1 : c = 1 := by
    rw [hs0, pow_zero] at hs
    exact orderOf_eq_one_iff.mp hs
  have hw1 : w = 1 := by
    have h1 := congrArg (fun t : ↥(center ↥K) => ((t : ↥K) : A)) hc1
    exact h1
  refine ⟨k₁, hk₁K, ?_, hρk₁⟩
  rw [hk₁w, hw1, mul_one]


end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.AltRho
