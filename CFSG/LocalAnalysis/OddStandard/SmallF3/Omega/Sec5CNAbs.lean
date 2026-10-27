module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CNPair

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec5cn_comm_of_conj {g x : G} (h : g⁻¹ * x * g = x) : g * x = x * g := by
  calc g * x = g * (g⁻¹ * x * g) := by rw [h]
    _ = x * g := by group

theorem sec5cn_pow4_of_mul_self {x : G} (h : x * x = 1) : x ^ 4 = 1 := by
  have h2 : x ^ 2 = 1 := by rw [pow_two]; exact h
  calc x ^ 4 = (x ^ 2) ^ 2 := by rw [← pow_mul]
    _ = 1 := by rw [h2, one_pow]

theorem sec5cn_conj_mem {N : Subgroup G} {g x : G} (hg : g ∈ normalizer (N : Set G))
    (hx : x ∈ N) : g⁻¹ * x * g ∈ N := by
  have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp hx
  simpa using this

section Swap

variable {π : SL23 × SL23 →* G} {K₃ K₄ N : Subgroup G} {z t c₀ q : G}

theorem sec5cn_swap_N (hπ : Sec5CNPi π K₃ K₄ z) (hcent : ∀ g : G, g * t = t * g →
    g * z = z * g → g ∈ N) (hc₀ : c₀ ∈ N) (hc₀P : c₀ ∈ K₃ ⊔ K₄) (hc₀t : c₀⁻¹ * t * c₀ = t * z)
    (hq : q ∈ K₃ ⊔ K₄) (hqt : q⁻¹ * t * q = t ∨ q⁻¹ * t * q = t * z) : q ∈ N := by
  have hzq : z * q = q * z := hπ.z_comm hq
  have hzc₀ : z * c₀ = c₀ * z := hπ.z_comm hc₀P
  have hz2 : z * z = 1 := hπ.z_sq
  rcases hqt with h1 | h1
  · exact hcent q (sec5cn_comm_of_conj h1) hzq.symm
  · have e2 : c₀ * z * c₀⁻¹ = z := by
      calc c₀ * z * c₀⁻¹ = z * c₀ * c₀⁻¹ := by rw [← hzc₀]
        _ = z := by group
    have e1 : (c₀ * t * c₀⁻¹) * z = t := by
      calc (c₀ * t * c₀⁻¹) * z = (c₀ * t * c₀⁻¹) * (c₀ * z * c₀⁻¹) := by rw [e2]
        _ = c₀ * (t * z) * c₀⁻¹ := by group
        _ = c₀ * (c₀⁻¹ * t * c₀) * c₀⁻¹ := by rw [hc₀t]
        _ = t := by group
    have h2 : c₀ * t * c₀⁻¹ = t * z := by
      calc c₀ * t * c₀⁻¹ = ((c₀ * t * c₀⁻¹) * z) * z := by rw [mul_assoc _ z z, hz2, mul_one]
        _ = t * z := by rw [e1]
    have h3 : (q * c₀⁻¹)⁻¹ * t * (q * c₀⁻¹) = t := by
      calc (q * c₀⁻¹)⁻¹ * t * (q * c₀⁻¹) = c₀ * (q⁻¹ * t * q) * c₀⁻¹ := by group
        _ = c₀ * (t * z) * c₀⁻¹ := by rw [h1]
        _ = (c₀ * t * c₀⁻¹) * (c₀ * z * c₀⁻¹) := by group
        _ = (t * z) * z := by rw [h2, e2]
        _ = t := by rw [mul_assoc, hz2, mul_one]
    have hgz : (q * c₀⁻¹) * z = z * (q * c₀⁻¹) :=
      ((Commute.mul_right (show Commute z q from hzq)
        (Commute.inv_right (show Commute z c₀ from hzc₀))).eq).symm
    have hg := hcent (q * c₀⁻¹) (sec5cn_comm_of_conj h3) hgz
    simpa using mul_mem hg hc₀

end Swap

section Fix

variable {π : SL23 × SL23 →* G} {K₁ K₂ : Subgroup G} {z ρ : G}

theorem sec5cn_odd_cent (hπ : Sec5CNPi π K₁ K₂ z) (hz1 : z ≠ 1)
    (hρ : ρ ∈ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G))
    (hρQ : ∀ q ∈ K₁ ⊔ K₂, q ^ 4 = 1 → q * ρ = ρ * q) {κ : G} (hκ : κ ∈ K₁ ⊔ K₂)
    (hodd : Odd (orderOf κ)) : κ * ρ = ρ * κ := by
  have hκ' : ρ⁻¹ * κ * ρ ∈ K₁ ⊔ K₂ := sec5cn_conj_mem hρ hκ
  have hw : κ⁻¹ * (ρ⁻¹ * κ * ρ) = 1 ∨ κ⁻¹ * (ρ⁻¹ * κ * ρ) = z := by
    refine hπ.cent_q (mul_mem (inv_mem hκ) hκ') fun q hq hq4 => ?_
    have hq2 : κ * q * κ⁻¹ ∈ K₁ ⊔ K₂ := mul_mem (mul_mem hκ hq) (inv_mem hκ)
    have hq24 : (κ * q * κ⁻¹) ^ 4 = 1 := by
      rw [conj_pow, hq4]
      group
    have e1 : ρ * q = q * ρ := (hρQ q hq hq4).symm
    have e2 : ρ⁻¹ * (κ * q * κ⁻¹) = (κ * q * κ⁻¹) * ρ⁻¹ :=
      ((show Commute (κ * q * κ⁻¹) ρ from hρQ _ hq2 hq24).inv_right).eq.symm
    calc κ⁻¹ * (ρ⁻¹ * κ * ρ) * q = κ⁻¹ * ρ⁻¹ * κ * (ρ * q) := by group
      _ = κ⁻¹ * ρ⁻¹ * κ * (q * ρ) := by rw [e1]
      _ = κ⁻¹ * (ρ⁻¹ * (κ * q * κ⁻¹)) * κ * ρ := by group
      _ = κ⁻¹ * ((κ * q * κ⁻¹) * ρ⁻¹) * κ * ρ := by rw [e2]
      _ = q * (κ⁻¹ * (ρ⁻¹ * κ * ρ)) := by group
  rcases hw with hw | hw
  · have h1 : ρ⁻¹ * κ * ρ = κ := by
      calc ρ⁻¹ * κ * ρ = κ * (κ⁻¹ * (ρ⁻¹ * κ * ρ)) := by group
        _ = κ := by rw [hw, mul_one]
    exact (sec5cn_comm_of_conj h1).symm
  · exfalso
    have h1 : ρ⁻¹ * κ * ρ = κ * z := by
      calc ρ⁻¹ * κ * ρ = κ * (κ⁻¹ * (ρ⁻¹ * κ * ρ)) := by group
        _ = κ * z := by rw [hw]
    have h2 : (ρ⁻¹ * κ * ρ) ^ orderOf κ = 1 := by
      rw [show ρ⁻¹ * κ * ρ = ρ⁻¹ * κ * ρ⁻¹⁻¹ from by rw [inv_inv], conj_pow,
        pow_orderOf_eq_one]
      group
    have hκz : Commute κ z := (hπ.z_comm hκ).symm
    obtain ⟨m, hm⟩ := hodd
    have h3 : z = 1 := by
      have h4 : (κ * z) ^ orderOf κ = z := by
        rw [hκz.mul_pow, pow_orderOf_eq_one, one_mul, hm, pow_succ, pow_mul, pow_two, hπ.z_sq,
          one_pow, one_mul]
      rw [← h4, ← h1]
      exact h2
    exact hz1 h3


theorem sec5cn_agree (hπ : Sec5CNPi π K₁ K₂ z) {q s : G} (hq : q ∈ K₁ ⊔ K₂) (hq4 : q ^ 4 = 1)
    (hs : s ∈ K₁ ⊔ K₂) (hs2 : s * s = 1) (hρs : ρ * s = s * ρ) (hρz : ρ * z = z * ρ) :
    (q⁻¹ * (ρ⁻¹ * q * ρ)) * s = s * (q⁻¹ * (ρ⁻¹ * q * ρ)) := by
  have hs4 : s ^ 4 = 1 := sec5cn_pow4_of_mul_self hs2
  have hρs' : ρ⁻¹ * s * ρ = s := by
    calc ρ⁻¹ * s * ρ = ρ⁻¹ * (s * ρ) := by group
      _ = ρ⁻¹ * (ρ * s) := by rw [hρs]
      _ = s := by group
  have hρz' : ρ⁻¹ * z * ρ = z := by
    calc ρ⁻¹ * z * ρ = ρ⁻¹ * (z * ρ) := by group
      _ = ρ⁻¹ * (ρ * z) := by rw [hρz]
      _ = z := by group
  have hzq : z * q = q * z := hπ.z_comm hq
  have hz2 : z * z = 1 := hπ.z_sq
  rcases hπ.comm_q hq hs hq4 hs4 with h1 | h1
  · have h2 : (ρ⁻¹ * q * ρ) * s = s * (ρ⁻¹ * q * ρ) := by
      calc (ρ⁻¹ * q * ρ) * s = ρ⁻¹ * q * (ρ * s) := by group
        _ = ρ⁻¹ * q * (s * ρ) := by rw [hρs]
        _ = ρ⁻¹ * (q * s) * ρ := by group
        _ = ρ⁻¹ * (s * q) * ρ := by rw [h1]
        _ = (ρ⁻¹ * s * ρ) * (ρ⁻¹ * q * ρ) := by group
        _ = s * (ρ⁻¹ * q * ρ) := by rw [hρs']
    have h3 : q⁻¹ * s = s * q⁻¹ := (show Commute q s from h1).inv_left.eq
    calc (q⁻¹ * (ρ⁻¹ * q * ρ)) * s = q⁻¹ * ((ρ⁻¹ * q * ρ) * s) := by group
      _ = q⁻¹ * (s * (ρ⁻¹ * q * ρ)) := by rw [h2]
      _ = (q⁻¹ * s) * (ρ⁻¹ * q * ρ) := by group
      _ = (s * q⁻¹) * (ρ⁻¹ * q * ρ) := by rw [h3]
      _ = s * (q⁻¹ * (ρ⁻¹ * q * ρ)) := by group
  · have h2 : (ρ⁻¹ * q * ρ) * s = z * (s * (ρ⁻¹ * q * ρ)) := by
      calc (ρ⁻¹ * q * ρ) * s = ρ⁻¹ * q * (ρ * s) := by group
        _ = ρ⁻¹ * q * (s * ρ) := by rw [hρs]
        _ = ρ⁻¹ * (q * s) * ρ := by group
        _ = ρ⁻¹ * (z * (s * q)) * ρ := by rw [h1]
        _ = (ρ⁻¹ * z * ρ) * (ρ⁻¹ * s * ρ) * (ρ⁻¹ * q * ρ) := by group
        _ = z * s * (ρ⁻¹ * q * ρ) := by rw [hρz', hρs']
        _ = z * (s * (ρ⁻¹ * q * ρ)) := by group
    have h1' : s * q = z * (q * s) := by
      calc s * q = (z * z) * (s * q) := by rw [hz2, one_mul]
        _ = z * (z * (s * q)) := by group
        _ = z * (q * s) := by rw [← h1]
    have hqz : q⁻¹ * z * q = z := by
      calc q⁻¹ * z * q = q⁻¹ * (z * q) := by group
        _ = q⁻¹ * (q * z) := by rw [hzq]
        _ = z := by group
    have hzq' : q⁻¹ * z = z * q⁻¹ := ((show Commute z q from hzq).inv_right).eq.symm
    have h3 : q⁻¹ * s = z * (s * q⁻¹) := by
      calc q⁻¹ * s = q⁻¹ * (s * q) * q⁻¹ := by group
        _ = q⁻¹ * (z * (q * s)) * q⁻¹ := by rw [h1']
        _ = (q⁻¹ * z * q) * s * q⁻¹ := by group
        _ = z * s * q⁻¹ := by rw [hqz]
        _ = z * (s * q⁻¹) := by group
    calc (q⁻¹ * (ρ⁻¹ * q * ρ)) * s = q⁻¹ * ((ρ⁻¹ * q * ρ) * s) := by group
      _ = q⁻¹ * (z * (s * (ρ⁻¹ * q * ρ))) := by rw [h2]
      _ = (q⁻¹ * z) * (s * (ρ⁻¹ * q * ρ)) := by group
      _ = (z * q⁻¹) * (s * (ρ⁻¹ * q * ρ)) := by rw [hzq']
      _ = z * ((q⁻¹ * s) * (ρ⁻¹ * q * ρ)) := by group
      _ = z * ((z * (s * q⁻¹)) * (ρ⁻¹ * q * ρ)) := by rw [h3]
      _ = (z * z) * (s * (q⁻¹ * (ρ⁻¹ * q * ρ))) := by group
      _ = s * (q⁻¹ * (ρ⁻¹ * q * ρ)) := by rw [hz2, one_mul]

theorem sec5cn_fix_Q (hπ : Sec5CNPi π K₁ K₂ z) {a b : G} {E : Subgroup G} (ha : a ∈ K₁ ⊔ K₂)
    (hb : b ∈ K₁ ⊔ K₂) (ha2 : a * a = 1) (hb2 : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (haz : a ≠ z) (hbz : b ≠ z) (hba : b ≠ a) (hbaz : b ≠ a * z) (hab : a * b = b * a)
    (hzE : z ∈ E) (haE : a ∈ E) (hbE : b ∈ E) (hE2 : ∀ x ∈ E, x * x = 1)
    (hEρ : ∀ x ∈ E, x * ρ = ρ * x) (hρ : ρ ∈ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G))
    (hρ3 : ρ ^ 3 = 1) {q : G} (hq : q ∈ K₁ ⊔ K₂) (hq4 : q ^ 4 = 1) : q * ρ = ρ * q := by
  have hq' : ρ⁻¹ * q * ρ ∈ K₁ ⊔ K₂ := sec5cn_conj_mem hρ hq
  have hq'4 : (ρ⁻¹ * q * ρ) ^ 4 = 1 := by
    rw [show ρ⁻¹ * q * ρ = ρ⁻¹ * q * ρ⁻¹⁻¹ from by rw [inv_inv], conj_pow, hq4]
    group
  have heK : q⁻¹ * (ρ⁻¹ * q * ρ) ∈ K₁ ⊔ K₂ := mul_mem (inv_mem hq) hq'
  have he4 : (q⁻¹ * (ρ⁻¹ * q * ρ)) ^ 4 = 1 := hπ.div_q hq hq' hq4 hq'4
  have hρa : ρ * a = a * ρ := (hEρ a haE).symm
  have hρb : ρ * b = b * ρ := (hEρ b hbE).symm
  have hρz : ρ * z = z * ρ := (hEρ z hzE).symm
  obtain ⟨i, j, k, hijk⟩ := hπ.cent_pair ha hb heK ha2 hb2 ha1 hb1 haz hbz hba hbaz hab he4
    (sec5cn_agree hπ hq hq4 ha ha2 hρa hρz) (sec5cn_agree hπ hq hq4 hb hb2 hρb hρz)
  have heE : q⁻¹ * (ρ⁻¹ * q * ρ) ∈ E := by
    rw [hijk]
    exact mul_mem (mul_mem (pow_mem hzE _) (pow_mem haE _)) (pow_mem hbE _)
  have hee : (q⁻¹ * (ρ⁻¹ * q * ρ)) * (q⁻¹ * (ρ⁻¹ * q * ρ)) = 1 := hE2 _ heE
  have heρ : ρ⁻¹ * (q⁻¹ * (ρ⁻¹ * q * ρ)) * ρ = q⁻¹ * (ρ⁻¹ * q * ρ) := by
    have h1 := hEρ _ heE
    calc ρ⁻¹ * (q⁻¹ * (ρ⁻¹ * q * ρ)) * ρ = ρ⁻¹ * ((q⁻¹ * (ρ⁻¹ * q * ρ)) * ρ) := by group
      _ = ρ⁻¹ * (ρ * (q⁻¹ * (ρ⁻¹ * q * ρ))) := by rw [h1]
      _ = q⁻¹ * (ρ⁻¹ * q * ρ) := by group
  have hq'e : ρ⁻¹ * q * ρ = q * (q⁻¹ * (ρ⁻¹ * q * ρ)) := by group
  have h2 : ρ⁻¹ * (ρ⁻¹ * q * ρ) * ρ = q := by
    calc ρ⁻¹ * (ρ⁻¹ * q * ρ) * ρ = ρ⁻¹ * (q * (q⁻¹ * (ρ⁻¹ * q * ρ))) * ρ := by rw [← hq'e]
      _ = (ρ⁻¹ * q * ρ) * (ρ⁻¹ * (q⁻¹ * (ρ⁻¹ * q * ρ)) * ρ) := by group
      _ = (q * (q⁻¹ * (ρ⁻¹ * q * ρ))) * (q⁻¹ * (ρ⁻¹ * q * ρ)) := by rw [heρ, ← hq'e]
      _ = q := by rw [mul_assoc, hee, mul_one]
  have hρ3' : ρ * (ρ * ρ) = 1 := by rw [← pow_three]; exact hρ3
  have h3 : ρ⁻¹ * q * ρ = q := by
    calc ρ⁻¹ * q * ρ = ρ⁻¹ * (ρ⁻¹ * (ρ⁻¹ * q * ρ) * ρ) * ρ := by rw [h2]
      _ = (ρ * (ρ * ρ))⁻¹ * q * (ρ * (ρ * ρ)) := by group
      _ = q := by rw [hρ3']; group
  exact (sec5cn_comm_of_conj h3).symm

end Fix

section Onto

variable {π : SL23 × SL23 →* G} {K₃ K₄ K : Subgroup G} {z : G}

theorem sec5cn_Q_le_C (hπ : Sec5CNPi π K₃ K₄ z) {u v : SL23} (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (hzK : ∀ k ∈ K, k * z = z * k)
    (hρK : ∀ k ∈ K, k * π (u, v) = π (u, v) * k)
    (hQN : ∀ y ∈ K₃ ⊔ K₄, y ^ 4 = 1 → y ∈ normalizer (K : Set G)) {x : G} (hx : x ∈ K₃ ⊔ K₄)
    (hx4 : x ^ 4 = 1) {k : G} (hk : k ∈ K) : k * x = x * k := by
  obtain ⟨y, hy, hy4, hw⟩ := hπ.exists_comm_onto hu3 hv3 hu1 hv1 hx hx4
  have hk₁ : y * k * y⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hQN y hy hy4) k).mp hk
  have e1 : π (u, v) * k = k * π (u, v) := (hρK k hk).symm
  have e2 : (π (u, v))⁻¹ * (y * k * y⁻¹) = (y * k * y⁻¹) * (π (u, v))⁻¹ :=
    ((show Commute (y * k * y⁻¹) (π (u, v)) from hρK _ hk₁).inv_right).eq.symm
  have hwk : (y⁻¹ * (π (u, v))⁻¹ * y * π (u, v)) * k = k * (y⁻¹ * (π (u, v))⁻¹ * y * π (u, v)) := by
    calc (y⁻¹ * (π (u, v))⁻¹ * y * π (u, v)) * k
        = y⁻¹ * (π (u, v))⁻¹ * y * (π (u, v) * k) := by group
      _ = y⁻¹ * (π (u, v))⁻¹ * y * (k * π (u, v)) := by rw [e1]
      _ = y⁻¹ * ((π (u, v))⁻¹ * (y * k * y⁻¹)) * y * π (u, v) := by group
      _ = y⁻¹ * ((y * k * y⁻¹) * (π (u, v))⁻¹) * y * π (u, v) := by rw [e2]
      _ = k * (y⁻¹ * (π (u, v))⁻¹ * y * π (u, v)) := by group
  rcases hw with hw | hw
  · rw [hw] at hwk
    exact hwk.symm
  · rw [hw] at hwk
    have h1 : z * (x * k) = z * (k * x) := by
      calc z * (x * k) = (z * x) * k := by group
        _ = k * (z * x) := hwk
        _ = (k * z) * x := by group
        _ = (z * k) * x := by rw [hzK k hk]
        _ = z * (k * x) := by group
    exact (mul_left_cancel h1).symm

end Onto

end CFSG.OddStandard.SmallF3.Omega
