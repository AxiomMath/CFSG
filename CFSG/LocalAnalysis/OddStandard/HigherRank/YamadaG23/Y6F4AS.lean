module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AP
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

variable {X : Type*} [Group X] [Finite X] {τ : X} {A : Subgroup X}

theorem y6f4a_mem_normalizer_cent_of_mem_normalizer {y : X} (hy : y ∈ normalizer (A : Set X)) :
    y ∈ normalizer ((centralizer (A : Set X) : Subgroup X) : Set X) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro c
  change (∀ a ∈ A, a * c = c * a) ↔
    (∀ a ∈ A, a * (y * c * y⁻¹) = (y * c * y⁻¹) * a)
  constructor
  · intro hc a ha
    have hya : y⁻¹ * a * y ∈ A := (Subgroup.mem_set_normalizer_iff''.mp hy a).mp ha
    have hcomm := hc (y⁻¹ * a * y) hya
    calc a * (y * c * y⁻¹)
        = y * ((y⁻¹ * a * y) * c) * y⁻¹ := by group
      _ = y * (c * (y⁻¹ * a * y)) * y⁻¹ := by rw [hcomm]
      _ = (y * c * y⁻¹) * a := by group
  · intro hc a ha
    have hya : y * a * y⁻¹ ∈ A := (Subgroup.mem_set_normalizer_iff.mp hy a).mp ha
    have hcomm := hc (y * a * y⁻¹) hya
    calc a * c
        = y⁻¹ * ((y * a * y⁻¹) * (y * c * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * c * y⁻¹) * (y * a * y⁻¹)) * y := by rw [hcomm]
      _ = c * a := by group

theorem y6f4a_mem_normalizer_of_mem_normalizer_cent (hτ : orderOf τ = 2)
    (hτA : τ ∈ centralizer (A : Set X)) (hN : centralizer ({τ} : Set X) ≤ normalizer (A : Set X))
    (hC : centralizer (A : Set X) ⊓ centralizer ({τ} : Set X) = zpowers τ) {y : X}
    (hy : y ∈ normalizer ((centralizer (A : Set X) : Subgroup X) : Set X)) :
    y ∈ normalizer (A : Set X) := by
  obtain ⟨z, hz, c, hc, rfl⟩ := y6f4a_normalizer_eq_mul hτA hτ hC hy
  exact mul_mem (Subgroup.centralizer_le_normalizer (A : Set X) hz) (hN hc)

theorem y6f4a_normalizer_cent_eq (hτ : orderOf τ = 2) (hτA : τ ∈ centralizer (A : Set X))
    (hN : centralizer ({τ} : Set X) ≤ normalizer (A : Set X))
    (hC : centralizer (A : Set X) ⊓ centralizer ({τ} : Set X) = zpowers τ) :
    normalizer ((centralizer (A : Set X) : Subgroup X) : Set X) = normalizer (A : Set X) := by
  refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
  · exact y6f4a_mem_normalizer_of_mem_normalizer_cent hτ hτA hN hC hy
  · exact y6f4a_mem_normalizer_cent_of_mem_normalizer hy

theorem y6f4a_tight [Group.IsPerfect ↥A] (hτ : orderOf τ = 2) (hτA : τ ∈ centralizer (A : Set X))
    (hN : centralizer ({τ} : Set X) ≤ normalizer (A : Set X))
    (hC : centralizer (A : Set X) ⊓ centralizer ({τ} : Set X) = zpowers τ)
    (hperf : ∀ B : Subgroup X, B ≤ centralizer ({τ} : Set X) → Group.IsPerfect ↥B → B ≤ A)
    {y : X} (hy : y ∉ normalizer ((centralizer (A : Set X) : Subgroup X) : Set X)) :
    Odd (Nat.card ↥(centralizer (A : Set X) ⊓
      (centralizer (A : Set X)).map (MulAut.conj y).toMonoidHom)) := by
  set Z : Subgroup X := centralizer (A : Set X) with hZdef
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  have h2dvd : 2 ∣ Nat.card ↥(Z ⊓ Z.map (MulAut.conj y).toMonoidHom) :=
    even_iff_two_dvd.mp hodd
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  have huX : orderOf (u : X) = 2 := by rw [Subgroup.orderOf_coe, hu]
  have huZ : (u : X) ∈ Z := u.2.1
  have huZmap : (u : X) ∈ Z.map (MulAut.conj y).toMonoidHom := u.2.2
  obtain ⟨z, hzZ, hzconj⟩ := y6f4a_invol_conj hτA hτ hC huZ huX
  obtain ⟨w, hwZ, hw⟩ := Subgroup.mem_map.mp huZmap
  have hw' : MulAut.conj y w = (u : X) := by simpa using hw
  set y' : X := z⁻¹ * y with hy'def
  have hτeq : τ = z⁻¹ * (u : X) * z := by rw [← hzconj]; group
  have hconj_y' : MulAut.conj y' w = τ := by
    rw [hτeq, ← hw']
    simp only [MulAut.conj_apply, hy'def]
    group
  have hA'le : A.map (MulAut.conj y').toMonoidHom ≤ centralizer ({τ} : Set X) := by
    rintro a' ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [← hconj_y']
    have hwa : a * w = w * a := Subgroup.mem_centralizer_iff.mp hwZ a ha
    exact (by simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
      congrArg (MulAut.conj y') hwa)
  have hA'leA : A.map (MulAut.conj y').toMonoidHom ≤ A :=
    hperf _ hA'le (Group.IsPerfect.map (H := A) (f := (MulAut.conj y').toMonoidHom))
  have hcard : Nat.card ↥(A.map (MulAut.conj y').toMonoidHom) = Nat.card ↥A :=
    Subgroup.card_map_of_injective (K := A) (f := (MulAut.conj y').toMonoidHom)
      (MulAut.conj y').injective
  have hA'eq : A.map (MulAut.conj y').toMonoidHom = A :=
    Subgroup.eq_of_le_of_card_ge hA'leA (le_of_eq hcard.symm)
  have hy'NA : y' ∈ normalizer (A : Set X) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa using hA'eq
  have hNZeq : normalizer (Z : Set X) = normalizer (A : Set X) := by
    rw [hZdef]
    exact y6f4a_normalizer_cent_eq hτ hτA hN hC
  have hy'NZ : y' ∈ normalizer (Z : Set X) := by
    rw [hNZeq]; exact hy'NA
  have hy_eq : y = z * y' := by rw [hy'def]; group
  have hzNZ : z ∈ normalizer (Z : Set X) := Subgroup.le_normalizer hzZ
  exact hy (by rw [hy_eq]; exact mul_mem hzNZ hy'NZ)

theorem y6f4a_comm_conj_ne_bot (hτ : orderOf τ = 2) (hτA : τ ∈ centralizer (A : Set X))
    (hC : centralizer (A : Set X) ⊓ centralizer ({τ} : Set X) = zpowers τ)
    (h4 : 4 ∣ Nat.card ↥A) (y : X) : ⁅A, A.map (MulAut.conj y).toMonoidHom⁆ ≠ ⊥ := by
  intro hbot
  have hle : A.map (MulAut.conj y).toMonoidHom ≤ centralizer (A : Set X) :=
    Subgroup.le_centralizer_iff.mp
      ((Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := A)
        (H₂ := A.map (MulAut.conj y).toMonoidHom)).mp hbot)
  have hcard_dvd : Nat.card ↥A ∣ Nat.card ↥(centralizer (A : Set X)) := by
    have h := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective (K := A) (f := (MulAut.conj y).toMonoidHom)
      (MulAut.conj y).injective] at h
  have h4Z : 4 ∣ Nat.card ↥(centralizer (A : Set X)) := h4.trans hcard_dvd
  let S : Sylow 2 ↥(centralizer (A : Set X)) := Sylow.nonempty.some
  have hS : Nat.card S = 2 := y6f4a_sylow_card_two hτA hτ hC S
  have hmult : Nat.card S = 2 ^ (Nat.card ↥(centralizer (A : Set X))).factorization 2 :=
    Sylow.card_eq_multiplicity S
  have hpow : 2 ^ (Nat.card ↥(centralizer (A : Set X))).factorization 2 = 2 := by
    rw [← hmult]; exact hS
  have h4Z' : 2 ^ 2 ∣ Nat.card ↥(centralizer (A : Set X)) := by
    rw [show (2 : ℕ) ^ 2 = 4 from by norm_num]; exact h4Z
  have h2le : 2 ≤ (Nat.card ↥(centralizer (A : Set X))).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization (Nat.card_pos.ne')).mp h4Z'
  have hle2 : 2 ^ 2 ≤ 2 ^ (Nat.card ↥(centralizer (A : Set X))).factorization 2 :=
    Nat.pow_le_pow_right (by norm_num) h2le
  rw [hpow] at hle2
  norm_num at hle2

theorem y6f4a_standard_of_invol (hτ : orderOf τ = 2) (hA : CFSG.Open.IsQuasisimple ↥A)
    (hτA : τ ∈ centralizer (A : Set X)) (hN : centralizer ({τ} : Set X) ≤ normalizer (A : Set X))
    (hC : centralizer (A : Set X) ⊓ centralizer ({τ} : Set X) = zpowers τ)
    (hperf : ∀ B : Subgroup X, B ≤ centralizer ({τ} : Set X) → Group.IsPerfect ↥B → B ≤ A)
    (h4 : 4 ∣ Nat.card ↥A) :
    CFSG.Open.standardComponentIsStandard A ∧
      ∀ S : Sylow 2 ↥(centralizer (A : Set X)), Nat.card S = 2 := by
  haveI : Group.IsPerfect ↥A := ⟨hA.1⟩
  refine ⟨?_, fun S => y6f4a_sylow_card_two hτA hτ hC S⟩
  unfold CFSG.Open.standardComponentIsStandard
  refine ⟨hA, ?_, ?_, ?_, ?_⟩
  · have h2 : 2 ∣ Nat.card ↥(centralizer (A : Set X)) := by
      simpa [hτ] using Subgroup.orderOf_dvd_natCard (centralizer (A : Set X)) hτA
    exact even_iff_two_dvd.mpr h2
  · intro g hg
    exact y6f4a_tight hτ hτA hN hC hperf hg
  · exact y6f4a_normalizer_cent_eq hτ hτA hN hC
  · intro g
    exact y6f4a_comm_conj_ne_bot hτ hτA hC h4 g

end CFSG.OddStandard.HigherRank.YamadaG23
