module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4S47RInv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4S47Easy
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4S47Main
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FTwoPart

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

theorem sec4S47R_two_elt (h : Sec4FSetup t L S z A B φ) {σ : Equiv.Perm (Option (Fin 7))}
    (hσ : σ * σ = 1) {y₁ : G} (hy₁ : y₁ ∈ normalizer (A : Set G))
    (hρ : h.actHom ⟨y₁, hy₁⟩ = σ) :
    ∃ (y : G) (hy : y ∈ normalizer (A : Set G)), h.actHom ⟨y, hy⟩ = σ ∧
      ∃ n : ℕ, y ^ (2 ^ n) = 1 := by
  obtain ⟨x, o, -, ho, hxo, ⟨n, hn⟩, hodd⟩ :=
    sec4F_two_part (⟨y₁, hy₁⟩ : ↥(normalizer (A : Set G)))
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ho
  have hρo2 : h.actHom o * h.actHom o = 1 := by
    rw [← hk, map_zpow, hρ, ← (Commute.refl σ).mul_zpow, hσ, one_zpow]
  have hρo : h.actHom o = 1 := by
    obtain ⟨j, hj⟩ := hodd
    have h1 : (h.actHom o) ^ (orderOf o) = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    rw [hj, pow_succ, pow_mul, pow_two, hρo2, one_pow, one_mul] at h1
    exact h1
  have hρx : h.actHom x = σ := by
    have h2 := congrArg h.actHom hxo
    rw [hρ, map_mul, hρo, mul_one] at h2
    exact h2.symm
  exact ⟨(x : G), x.2, hρx, n, by simpa using congrArg Subtype.val hn⟩

theorem sec4S47R_split47Cent_of_odd (h : Sec4FSetup t L S z A B φ) {m : G}
    (hm : m ∈ normalizer (A : Set G))
    (hodd : Equiv.Perm.sign (h.actHom ⟨m, hm⟩) = -1) :
    ∃ K : Subgroup G, K ≤ centralizer ({t} : Set G) ⊓ normalizer (A : Set G) ∧
      K.relIndex (centralizer ({t} : Set G) ⊓ normalizer (A : Set G)) = 2 ∧ t ∉ K := by
  have hτ2 : sec4S47RTau * sec4S47RTau = 1 := Equiv.swap_mul_self _ _
  have hτs : Equiv.Perm.sign sec4S47RTau = -1 := Equiv.Perm.sign_swap (by decide)
  have hε : sec4S47RTau * (h.actHom ⟨m, hm⟩)⁻¹ ∈ alternatingGroup (Option (Fin 7)) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hτs, hodd]
    decide
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp (h.alt_le_range hε)
  have hρy₁ : h.actHom (u * ⟨m, hm⟩) = sec4S47RTau := by
    rw [map_mul, hu]
    group
  obtain ⟨y, hy, hρy, n, hn⟩ := sec4S47R_two_elt h hτ2 (u * ⟨m, hm⟩).2 hρy₁
  obtain ⟨a, haA, ha2⟩ := sec4S47R_exists_involution h hy hρy ⟨n, hn⟩
  have haN : a ∈ normalizer (A : Set G) := Subgroup.le_normalizer haA
  have hy₂N : y * a ∈ normalizer (A : Set G) := mul_mem hy haN
  have haC : a ∈ centralizer (A : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun b hb => h.A_comm hb haA
  have hρa : h.actHom ⟨a, haN⟩ = 1 := (h.actHom_eq_one_iff ⟨a, haN⟩).mpr haC
  have hρ₂ : h.actHom ⟨y * a, hy₂N⟩ = sec4S47RTau := by
    have hmul : (⟨y * a, hy₂N⟩ : ↥(normalizer (A : Set G))) = ⟨y, hy⟩ * ⟨a, haN⟩ := rfl
    rw [hmul, map_mul, hρy, hρa, mul_one]
  exact h.split47Cent_of_odd_involution hy₂N ha2 (by rw [hρ₂, hτs])

theorem asc82Split47Cent_of (I : Sec4FInputs) : Asc82Split47Cent := by
  intro G _ _ t L S z hctx hnot A hA
  obtain ⟨A₀, B, φ, hD⟩ := I.hAD G t L S z hctx
  obtain rfl : A = A₀ := hD.unique A hA
  have h := sec4FSetup_of_data I hctx hnot hD
  by_cases hex : ∃ (m : G) (hm : m ∈ normalizer (A : Set G)),
      Equiv.Perm.sign (h.actHom ⟨m, hm⟩) = -1
  · obtain ⟨m, hm, hs⟩ := hex
    exact sec4S47R_split47Cent_of_odd h hm hs
  · push Not at hex
    exact h.split47Cent_of_even fun m hm _ =>
      (Int.units_eq_one_or _).resolve_right (hex m hm)

theorem asc82Split47_holds (I : Sec4FInputs) : Asc82Split47 :=
  asc82Split47_of I (asc82Split47Cent_of I)

end CFSG.OddStandard.SmallF3.Omega
