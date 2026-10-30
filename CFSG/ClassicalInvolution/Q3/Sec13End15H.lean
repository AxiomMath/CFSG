module

public import CFSG.ClassicalInvolution.Q3.Sec13End15G
public import CFSG.ClassicalInvolution.Q3.Sec13EndSp4
import CFSG.ClassicalInvolution.Q3.Sec13EndS3E8
import CFSG.ClassicalInvolution.Q3.Sec13PerpPair

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

namespace EndHyp

variable {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}

private theorem e15h1_zi {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) : z * i = i * z := by
  rw [← hQ.sq_i, mul_assoc]

private theorem e15h1_zj {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) : z * j = j * z := by
  rw [← hQ.sq_j, mul_assoc]

private theorem e15h1_ij_sq {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) :
    (i * j) * (i * j) = z := by
  have hiz : i * z = z * i := (e15h1_zi hQ).symm
  calc (i * j) * (i * j) = i * (j * i) * j := by group
    _ = i * (z * (i * j)) * j := by rw [hQ.comm]
    _ = (i * z) * (i * j) * j := by group
    _ = (z * i) * (i * j) * j := by rw [hiz]
    _ = z * (i * i) * (j * j) := by group
    _ = z * z * z := by rw [hQ.sq_i, hQ.sq_j]
    _ = z := by rw [hQ.inv.sq, one_mul]

private theorem e15h1_inv_i {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) :
    i⁻¹ = z * i := by
  apply inv_eq_of_mul_eq_one_right
  rw [← mul_assoc, ← e15h1_zi hQ, mul_assoc, hQ.sq_i, hQ.inv.sq]

private theorem e15h1_inv_j {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) :
    j⁻¹ = z * j := by
  apply inv_eq_of_mul_eq_one_right
  rw [← mul_assoc, ← e15h1_zj hQ, mul_assoc, hQ.sq_j, hQ.inv.sq]

private theorem e15h1_zij {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) :
    z * (i * j) = (i * j) * z := by
  calc z * (i * j) = (z * i) * j := by group
    _ = (i * z) * j := by rw [e15h1_zi hQ]
    _ = i * (z * j) := by group
    _ = i * (j * z) := by rw [e15h1_zj hQ]
    _ = (i * j) * z := by group

private theorem e15h1_inv_ij {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) :
    (i * j)⁻¹ = z * (i * j) := by
  apply inv_eq_of_mul_eq_one_right
  rw [e15h1_zij hQ, ← mul_assoc, e15h1_ij_sq hQ, hQ.inv.sq]

private theorem e15h1_sq_one {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) {c b : G}
    (hc : c = i ∨ c = z * i) (hb : b = i ∨ b = z * i) : (c * b) * (c * b) = 1 := by
  have h1 : i * (z * i) = 1 := by rw [← e15h1_inv_i hQ, mul_inv_cancel]
  have h2 : (z * i) * i = 1 := by rw [mul_assoc, hQ.sq_i, hQ.inv.sq]
  have h3 : (z * i) * (z * i) = z := by
    calc (z * i) * (z * i) = z * (i * z) * i := by group
      _ = z * (z * i) * i := by rw [← e15h1_zi hQ]
      _ = z * z * (i * i) := by group
      _ = z := by rw [hQ.inv.sq, hQ.sq_i, one_mul]
  have key : c * b = 1 ∨ c * b = z := by
    rcases hc with rfl | rfl <;> rcases hb with rfl | rfl
    · right
      rw [hQ.sq_i]
    · left
      exact h1
    · left
      exact h2
    · right
      exact h3
  rcases key with h | h
  · rw [h, one_mul]
  · rw [h, hQ.inv.sq]

private theorem e15h1_conj_sq {K : Subgroup G} {z i j g u : G} (hQ : Q8Data K z i j)
    (hgN : g ∈ Subgroup.normalizer (K : Set G))
    (hu : g * u * g⁻¹ = u ∨ g * u * g⁻¹ = z * u) : g * (g * u * g⁻¹) * g⁻¹ = u := by
  have hgz : g * z * g⁻¹ = z := conj_eq_self_of_normalizer hQ.inv hgN
  rcases hu with h1 | h1
  · rw [h1]
    exact h1
  · calc g * (g * u * g⁻¹) * g⁻¹ = g * (z * u) * g⁻¹ := by rw [h1]
      _ = (g * z * g⁻¹) * (g * u * g⁻¹) := by group
      _ = z * (z * u) := by rw [hgz, h1]
      _ = u := by rw [← mul_assoc, hQ.inv.sq, one_mul]

private theorem e15h1_commute_sq {K : Subgroup G} {z i j g u : G} (hQ : Q8Data K z i j)
    (hgN : g ∈ Subgroup.normalizer (K : Set G))
    (hu : g * u * g⁻¹ = u ∨ g * u * g⁻¹ = z * u) : Commute (g * g) u := by
  show (g * g) * u = u * (g * g)
  calc (g * g) * u = (g * (g * u * g⁻¹) * g⁻¹) * (g * g) := by group
    _ = u * (g * g) := by rw [e15h1_conj_sq hQ hgN hu]

private theorem e15h1_comm_of_gens {K : Subgroup G} {z i j w : G} (hQ : Q8Data K z i j)
    (hwi : Commute w i) (hwj : Commute w j) (hwz : Commute w z) : ∀ k ∈ K, Commute w k := by
  intro k hk
  rcases hQ.nf k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Commute.one_right w
  · exact hwz
  · exact hwi
  · exact hwz.mul_right hwi
  · exact hwj
  · exact hwz.mul_right hwj
  · exact hwi.mul_right hwj
  · exact hwz.mul_right (hwi.mul_right hwj)

private theorem e15h1_sq_comm {K : Subgroup G} {z i j g : G} (hQ : Q8Data K z i j)
    (hgN : g ∈ Subgroup.normalizer (K : Set G))
    (hgi : g * i * g⁻¹ = i ∨ g * i * g⁻¹ = z * i) (hgj : g * j * g⁻¹ = j ∨ g * j * g⁻¹ = z * j) :
    ∀ k ∈ K, Commute (g * g) k := by
  apply e15h1_comm_of_gens hQ
  · exact e15h1_commute_sq hQ hgN hgi
  · exact e15h1_commute_sq hQ hgN hgj
  · exact e15h1_commute_sq hQ hgN (Or.inl (conj_eq_self_of_normalizer hQ.inv hgN))

private theorem e15h1_comm_of_sq {y g : G} {m : ℕ} (hm : Odd m) (hym : y ^ m = 1)
    (h : Commute (y * y) g) : Commute y g := by
  obtain ⟨k, rfl⟩ := hm
  have hy : (y * y) ^ (k + 1) = y := by
    rw [← sq, ← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hym, one_mul]
  have h2 := h.pow_left (k + 1)
  rw [hy] at h2
  exact h2


private theorem e15h1_swap {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) : Q8Data K z j i where
  inv := hQ.inv
  mem_i := hQ.mem_j
  mem_j := hQ.mem_i
  sq_i := hQ.sq_j
  sq_j := hQ.sq_i
  comm := by rw [hQ.comm, ← mul_assoc, hQ.inv.sq, one_mul]
  nf := by
    intro x hx
    rcases hQ.nf x hx with h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · right; right; right; right; right; right; right
      rw [h, hQ.comm, ← mul_assoc, hQ.inv.sq, one_mul]
    · right; right; right; right; right; right; left
      rw [h, hQ.comm]

private theorem e15h1_sq_pow {y : G} {m : ℕ} (hym : y ^ m = 1) : (y * y) ^ m = 1 := by
  rw [← sq, ← pow_mul, mul_comm, pow_mul, hym, one_pow]

private theorem e15h1_yyi_fix {K : Subgroup G} {z i j y : G} (hQ : Q8Data K z i j)
    (hyN : y ∈ Subgroup.normalizer (K : Set G)) (hyi : y * i * y⁻¹ = i ∨ y * i * y⁻¹ = z * i) :
    (y * y) * i * (y * y)⁻¹ = i ∨ (y * y) * i * (y * y)⁻¹ = z * i := by
  have e : (y * y) * i * (y * y)⁻¹ = y * (y * i * y⁻¹) * y⁻¹ := by group
  rw [e]
  exact Or.inl (e15h1_conj_sq hQ hyN hyi)

private theorem e15h1_yyj {K : Subgroup G} {z i j y : G} (hQ : Q8Data K z i j)
    (hyz : y * z * y⁻¹ = z) (hyi : y * i * y⁻¹ = i ∨ y * i * y⁻¹ = z * i)
    (hb : y * j * y⁻¹ = i * j ∨ y * j * y⁻¹ = z * (i * j)) :
    (y * y) * j * (y * y)⁻¹ = (y * i * y⁻¹) * (i * j) := by
  have hzi : Commute z (y * i * y⁻¹) := by
    rcases hyi with h1 | h1 <;> rw [h1]
    · exact e15h1_zi hQ
    · exact (Commute.refl z).mul_right (e15h1_zi hQ)
  rcases hb with hb | hb
  · calc (y * y) * j * (y * y)⁻¹ = y * (y * j * y⁻¹) * y⁻¹ := by group
      _ = y * (i * j) * y⁻¹ := by rw [hb]
      _ = (y * i * y⁻¹) * (y * j * y⁻¹) := by group
      _ = (y * i * y⁻¹) * (i * j) := by rw [hb]
  · calc (y * y) * j * (y * y)⁻¹ = y * (y * j * y⁻¹) * y⁻¹ := by group
      _ = y * (z * (i * j)) * y⁻¹ := by rw [hb]
      _ = (y * z * y⁻¹) * (y * (i * j) * y⁻¹) := by group
      _ = z * ((y * i * y⁻¹) * (y * j * y⁻¹)) := by rw [hyz]; group
      _ = z * ((y * i * y⁻¹) * (z * (i * j))) := by rw [hb]
      _ = (z * (y * i * y⁻¹)) * (z * (i * j)) := by group
      _ = ((y * i * y⁻¹) * z) * (z * (i * j)) := by rw [hzi.eq]
      _ = (y * i * y⁻¹) * (z * (z * (i * j))) := by group
      _ = (y * i * y⁻¹) * ((z * z) * (i * j)) := by group
      _ = (y * i * y⁻¹) * (i * j) := by rw [hQ.inv.sq, one_mul]

private theorem e15h1_yyj_fix {K : Subgroup G} {z i j y : G} (hQ : Q8Data K z i j)
    (hyz : y * z * y⁻¹ = z) (hyi : y * i * y⁻¹ = i ∨ y * i * y⁻¹ = z * i)
    (hb : y * j * y⁻¹ = i * j ∨ y * j * y⁻¹ = z * (i * j)) :
    (y * y) * j * (y * y)⁻¹ = j ∨ (y * y) * j * (y * y)⁻¹ = z * j := by
  rw [e15h1_yyj hQ hyz hyi hb]
  rcases hyi with h1 | h1
  · right
    rw [h1]
    calc i * (i * j) = (i * i) * j := by group
      _ = z * j := by rw [hQ.sq_i]
  · left
    rw [h1]
    calc (z * i) * (i * j) = z * (i * i) * j := by group
      _ = z * z * j := by rw [hQ.sq_i]
      _ = j := by rw [hQ.inv.sq, one_mul]

private theorem e15h1_centralize {K : Subgroup G} {z i j y : G} (hQ : Q8Data K z i j)
    (hyN : y ∈ Subgroup.normalizer (K : Set G)) {m : ℕ} (hm : Odd m) (hym : y ^ m = 1)
    (hyi : y * i * y⁻¹ = i ∨ y * i * y⁻¹ = z * i) : ∀ k ∈ K, Commute y k := by
  have hyz : y * z * y⁻¹ = z := conj_eq_self_of_normalizer hQ.inv hyN
  have hbK : y * j * y⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hyN j).mp hQ.mem_j
  have hbb : (y * j * y⁻¹) * (y * j * y⁻¹) = z := by
    calc (y * j * y⁻¹) * (y * j * y⁻¹) = y * (j * j) * y⁻¹ := by group
      _ = y * z * y⁻¹ := by rw [hQ.sq_j]
      _ = z := hyz
  have hfin : (∀ k ∈ K, Commute (y * y) k) → ∀ k ∈ K, Commute y k :=
    fun hk k hkK => e15h1_comm_of_sq hm hym (hk k hkK)
  have hfin4 : (∀ k ∈ K, Commute ((y * y) * (y * y)) k) → ∀ k ∈ K, Commute y k :=
    fun hk k hkK => e15h1_comm_of_sq hm hym (e15h1_comm_of_sq hm (e15h1_sq_pow hym) (hk k hkK))
  rcases hQ.nf _ hbK with hb | hb | hb | hb | hb | hb | hb | hb
  ·
    exfalso
    rw [hb, mul_one] at hbb
    exact hQ.inv.ne_one hbb.symm
  ·
    exfalso
    rw [hb, hQ.inv.sq] at hbb
    exact hQ.inv.ne_one hbb.symm
  ·
    exfalso
    have hw : y * (i * j) * y⁻¹ = (y * i * y⁻¹) * (y * j * y⁻¹) := by group
    have hw2 : (y * (i * j) * y⁻¹) * (y * (i * j) * y⁻¹) = z := by
      calc (y * (i * j) * y⁻¹) * (y * (i * j) * y⁻¹) = y * ((i * j) * (i * j)) * y⁻¹ := by
            group
        _ = y * z * y⁻¹ := by rw [e15h1_ij_sq hQ]
        _ = z := hyz
    rw [hw, hb] at hw2
    rw [e15h1_sq_one hQ hyi (Or.inl rfl)] at hw2
    exact hQ.inv.ne_one hw2.symm
  ·
    exfalso
    have hw : y * (i * j) * y⁻¹ = (y * i * y⁻¹) * (y * j * y⁻¹) := by group
    have hw2 : (y * (i * j) * y⁻¹) * (y * (i * j) * y⁻¹) = z := by
      calc (y * (i * j) * y⁻¹) * (y * (i * j) * y⁻¹) = y * ((i * j) * (i * j)) * y⁻¹ := by
            group
        _ = y * z * y⁻¹ := by rw [e15h1_ij_sq hQ]
        _ = z := hyz
    rw [hw, hb] at hw2
    rw [e15h1_sq_one hQ hyi (Or.inr rfl)] at hw2
    exact hQ.inv.ne_one hw2.symm
  ·
    exact hfin (e15h1_sq_comm hQ hyN hyi (Or.inl hb))
  ·
    exact hfin (e15h1_sq_comm hQ hyN hyi (Or.inr hb))
  · exact hfin4 (e15h1_sq_comm hQ (mul_mem hyN hyN) (e15h1_yyi_fix hQ hyN hyi)
      (e15h1_yyj_fix hQ hyz hyi (Or.inl hb)))
  · exact hfin4 (e15h1_sq_comm hQ (mul_mem hyN hyN) (e15h1_yyi_fix hQ hyN hyi)
      (e15h1_yyj_fix hQ hyz hyi (Or.inr hb)))



theorem le_commutator_of_three_element (h : EndHyp Ω) (s : TwinSit Ω K K' z) {x : G}
    (hxN : x ∈ Subgroup.normalizer (K : Set G)) (hx3 : ∃ a : ℕ, x ^ 3 ^ a = 1)
    (hxK : ∃ k ∈ K, x * k ≠ k * x) : K ≤ commutator G := by
  obtain ⟨i, j, hi, hj, hii, hjj, hji, hNF⟩ :=
    exists_q8_gen s.isInv (h.isQuatSub_of_mem s.mem) (h.card_eq_eight s.mem)
  have hQ : Q8Data K z i j := ⟨s.isInv, hi, hj, hii, hjj, hji, hNF⟩
  have hQ' : Q8Data K z j i := e15h1_swap hQ
  obtain ⟨a3, ha3⟩ := hx3
  obtain ⟨k0, hk0, hnc⟩ := hxK
  have hodd : Odd (3 ^ a3) := Odd.pow (by decide)
  have hnotc : ¬ ∀ k ∈ K, Commute x k := fun hall => hnc (hall k0 hk0)
  have hA : ¬ (x * i * x⁻¹ = i ∨ x * i * x⁻¹ = z * i) :=
    fun hc => hnotc (e15h1_centralize hQ hxN hodd ha3 hc)
  have hB : ¬ (x * j * x⁻¹ = j ∨ x * j * x⁻¹ = z * j) :=
    fun hc => hnotc (e15h1_centralize hQ' hxN hodd ha3 hc)
  have hxz : x * z * x⁻¹ = z := conj_eq_self_of_normalizer s.isInv hxN
  have hsqa : (x * i * x⁻¹) * (x * i * x⁻¹) = z := by
    calc (x * i * x⁻¹) * (x * i * x⁻¹) = x * (i * i) * x⁻¹ := by group
      _ = z := by rw [hii, hxz]
  have hsqb : (x * j * x⁻¹) * (x * j * x⁻¹) = z := by
    calc (x * j * x⁻¹) * (x * j * x⁻¹) = x * (j * j) * x⁻¹ := by group
      _ = z := by rw [hjj, hxz]
  have haK : x * i * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hxN i).mp hi
  have hbK : x * j * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hxN j).mp hj
  have hcm : ∀ g : G, g * (x * g * x⁻¹)⁻¹ ∈ commutator G := fun g => by
    have h' : g * x * g⁻¹ * x⁻¹ ∈ commutator G :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top x)
    convert h' using 1
    group
  have hzG : z ∈ commutator G := by
    have h' : i * j * i⁻¹ * j⁻¹ ∈ commutator G :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top i) (Subgroup.mem_top j)
    have he : i * j * i⁻¹ * j⁻¹ = z := by
      rw [e15h1_inv_i hQ, e15h1_inv_j hQ]
      calc i * j * (z * i) * (z * j) = (i * j) * (i * z) * (z * j) := by rw [e15h1_zi hQ]
        _ = (i * j) * i * (z * z) * j := by group
        _ = (i * j) * i * j := by rw [hQ.inv.sq, mul_one]
        _ = (i * j) * (i * j) := by group
        _ = z := e15h1_ij_sq hQ
    rwa [he] at h'
  have hdiv : ∀ w : G, z * w ∈ commutator G → w ∈ commutator G := fun w hw => by
    have := mul_mem hzG hw
    rwa [← mul_assoc, hQ.inv.sq, one_mul] at this
  obtain ⟨a, ha⟩ : ∃ a, x * i * x⁻¹ = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, x * j * x⁻¹ = b := ⟨_, rfl⟩
  rw [ha] at haK hA hsqa
  rw [hb] at hbK hB hsqb
  have hua : i * a⁻¹ ∈ commutator G := by
    have := hcm i
    rwa [ha] at this
  have hvb : j * b⁻¹ ∈ commutator G := by
    have := hcm j
    rwa [hb] at this
  have hcaseA : (a = j ∨ a = z * j) ∨ (a = i * j ∨ a = z * (i * j)) := by
    rcases hNF a haK with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
    · exfalso
      rw [h1, one_mul] at hsqa
      exact hQ.inv.ne_one hsqa.symm
    · exfalso
      rw [h1, hQ.inv.sq] at hsqa
      exact hQ.inv.ne_one hsqa.symm
    · exact absurd (Or.inl h1) hA
    · exact absurd (Or.inr h1) hA
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr h1)
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  have hcaseB : (b = i ∨ b = z * i) ∨ (b = i * j ∨ b = z * (i * j)) := by
    rcases hNF b hbK with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
    · exfalso
      rw [h1, one_mul] at hsqb
      exact hQ.inv.ne_one hsqb.symm
    · exfalso
      rw [h1, hQ.inv.sq] at hsqb
      exact hQ.inv.ne_one hsqb.symm
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr h1)
    · exact absurd (Or.inl h1) hB
    · exact absurd (Or.inr h1) hB
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  have hPa1 : (a = j ∨ a = z * j) → i * j ∈ commutator G := by
    rintro (h1 | h1)
    · rw [h1, e15h1_inv_j hQ] at hua
      apply hdiv
      have e : i * (z * j) = z * (i * j) := by
        calc i * (z * j) = (i * z) * j := by group
          _ = (z * i) * j := by rw [e15h1_zi hQ]
          _ = z * (i * j) := by group
      rwa [e] at hua
    · rw [h1] at hua
      have e : i * (z * j)⁻¹ = i * j := by
        rw [inv_eq_of_mul_eq_one_right (show (z * j) * j = 1 by
          rw [mul_assoc, hQ.sq_j, hQ.inv.sq])]
      rwa [e] at hua
  have hPa2 : (a = i * j ∨ a = z * (i * j)) → j ∈ commutator G := by
    rintro (h1 | h1)
    · rw [h1, e15h1_inv_ij hQ] at hua
      have e : i * (z * (i * j)) = j := by
        calc i * (z * (i * j)) = (i * z) * (i * j) := by group
          _ = (z * i) * (i * j) := by rw [e15h1_zi hQ]
          _ = z * (i * (i * j)) := by group
          _ = z * ((i * i) * j) := by group
          _ = z * (z * j) := by rw [hii]
          _ = (z * z) * j := by group
          _ = j := by rw [hQ.inv.sq, one_mul]
      rwa [e] at hua
    · rw [h1] at hua
      have e : i * (z * (i * j))⁻¹ = z * j := by
        rw [inv_eq_of_mul_eq_one_right (show (z * (i * j)) * (i * j) = 1 by
          rw [mul_assoc, e15h1_ij_sq hQ, hQ.inv.sq])]
        calc i * (i * j) = (i * i) * j := by group
          _ = z * j := by rw [hii]
      rw [e] at hua
      exact hdiv j hua
  have hPb1 : (b = i ∨ b = z * i) → i * j ∈ commutator G := by
    rintro (h1 | h1)
    · rw [h1, e15h1_inv_i hQ] at hvb
      have e : j * (z * i) = i * j := by
        calc j * (z * i) = (j * z) * i := by group
          _ = (z * j) * i := by rw [e15h1_zj hQ]
          _ = z * (j * i) := by group
          _ = z * (z * (i * j)) := by rw [hji]
          _ = (z * z) * (i * j) := by group
          _ = i * j := by rw [hQ.inv.sq, one_mul]
      rwa [e] at hvb
    · rw [h1] at hvb
      have e : j * (z * i)⁻¹ = z * (i * j) := by
        rw [inv_eq_of_mul_eq_one_right (show (z * i) * i = 1 by
          rw [mul_assoc, hQ.sq_i, hQ.inv.sq])]
        exact hji
      apply hdiv
      rwa [e] at hvb
  have hPb2 : (b = i * j ∨ b = z * (i * j)) → i ∈ commutator G := by
    rintro (h1 | h1)
    · rw [h1, e15h1_inv_ij hQ] at hvb
      have e : j * (z * (i * j)) = z * i := by
        calc j * (z * (i * j)) = (j * z) * (i * j) := by group
          _ = (z * j) * (i * j) := by rw [e15h1_zj hQ]
          _ = z * (j * (i * j)) := by group
          _ = z * ((j * i) * j) := by group
          _ = z * ((z * (i * j)) * j) := by rw [hji]
          _ = z * (z * (i * (j * j))) := by group
          _ = z * (z * (i * z)) := by rw [hjj]
          _ = z * (z * (z * i)) := by rw [← e15h1_zi hQ]
          _ = (z * z) * (z * i) := by group
          _ = z * i := by rw [hQ.inv.sq, one_mul]
      rw [e] at hvb
      exact hdiv i hvb
    · rw [h1] at hvb
      have e : j * (z * (i * j))⁻¹ = i := by
        rw [inv_eq_of_mul_eq_one_right (show (z * (i * j)) * (i * j) = 1 by
          rw [mul_assoc, e15h1_ij_sq hQ, hQ.inv.sq])]
        calc j * (i * j) = (j * i) * j := by group
          _ = (z * (i * j)) * j := by rw [hji]
          _ = z * (i * (j * j)) := by group
          _ = z * (i * z) := by rw [hjj]
          _ = z * (z * i) := by rw [← e15h1_zi hQ]
          _ = (z * z) * i := by group
          _ = i := by rw [hQ.inv.sq, one_mul]
      rwa [e] at hvb
  have key1 : ∀ u v : G, u ∈ commutator G → u * v ∈ commutator G → v ∈ commutator G :=
    fun u v hu huv => by
      have := mul_mem (inv_mem hu) huv
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  have key2 : ∀ u v : G, u * v ∈ commutator G → v ∈ commutator G → u ∈ commutator G :=
    fun u v huv hv => by
      have := mul_mem huv (inv_mem hv)
      rwa [mul_assoc, mul_inv_cancel, mul_one] at this
  have hiG : i ∈ commutator G ∧ j ∈ commutator G := by
    rcases hcaseA with hA1 | hA2 <;> rcases hcaseB with hB1 | hB2
    ·
      exfalso
      have hsqx : (x * x) * i * (x * x)⁻¹ = i ∨ (x * x) * i * (x * x)⁻¹ = z * i := by
        have e : (x * x) * i * (x * x)⁻¹ = x * (x * i * x⁻¹) * x⁻¹ := by group
        rw [e, ha]
        rcases hA1 with h1 | h1
        · rw [h1, hb]
          exact hB1
        · have e2 : x * (z * j) * x⁻¹ = z * (x * j * x⁻¹) := by
            calc x * (z * j) * x⁻¹ = (x * z * x⁻¹) * (x * j * x⁻¹) := by group
              _ = z * (x * j * x⁻¹) := by rw [hxz]
          rw [h1, e2, hb]
          rcases hB1 with h2 | h2
          · right
            rw [h2]
          · left
            rw [h2, ← mul_assoc, hQ.inv.sq, one_mul]
      have hcx := e15h1_centralize hQ (mul_mem hxN hxN) hodd (e15h1_sq_pow ha3) hsqx
      exact hnotc (fun k hk => e15h1_comm_of_sq hodd ha3 (hcx k hk))
    · exact ⟨hPb2 hB2, key1 i j (hPb2 hB2) (hPa1 hA1)⟩
    · exact ⟨key2 i j (hPb1 hB1) (hPa2 hA2), hPa2 hA2⟩
    · exact ⟨hPb2 hB2, hPa2 hA2⟩
  intro k hk
  rcases hNF k hk with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1]
  · exact one_mem _
  · exact hzG
  · exact hiG.1
  · exact mul_mem hzG hiG.1
  · exact hiG.2
  · exact mul_mem hzG hiG.2
  · exact mul_mem hiG.1 hiG.2
  · exact mul_mem hzG (mul_mem hiG.1 hiG.2)


theorem commutator_eq_top_local (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hE : eGroup Ω K ≤ K ⊔ K') : commutator G = ⊤ := by
  obtain ⟨x, hxN, hx3, hxK, -⟩ := h.exists_three_element h9 s h13 hE
  have hK : K ≤ commutator G := h.le_commutator_of_three_element s hxN hx3 hxK
  have hall : pSpan Ω ≤ commutator G := by
    refine pSpan_le fun L hL => ?_
    obtain ⟨g, hg⟩ := h.thmD.trans K s.mem L hL
    rw [← hg]
    intro y hy
    have h1 : g⁻¹ * y * g ∈ K := mem_conjSub_iff.mp hy
    have h2 : g * (g⁻¹ * y * g) * g⁻¹ ∈ commutator G :=
      Subgroup.Normal.conj_mem inferInstance _ (hK h1) g
    have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rw [e] at h2
    exact h2
  rw [h.thmD.gen] at hall
  exact top_le_iff.mp hall

end EndHyp

structure SixPointData (D : Subgroup G) (σ : G →* Equiv.Perm (Fin 6))
    (β : Multiplicative (Fin 6 → ZMod 2) →* G) : Prop where
  mem_iff : ∀ g : G, g ∈ D ↔
    ∃ f : Multiplicative (Fin 6 → ZMod 2), ∑ i, f.toAdd i = 0 ∧ β f = g
  eq_one_iff : ∀ f : Multiplicative (Fin 6 → ZMod 2), ∑ i, f.toAdd i = 0 →
    (β f = 1 ↔ f.toAdd = 0 ∨ f.toAdd = fun _ => 1)
  conj : ∀ (g : G) (f : Multiplicative (Fin 6 → ZMod 2)), ∑ i, f.toAdd i = 0 →
    g * β f * g⁻¹ = β (Multiplicative.ofAdd fun i => f.toAdd ((σ g).symm i))
  ker : ∀ g : G, σ g = 1 ↔ g ∈ Subgroup.centralizer (D : Set G)
  range : σ.range = alternatingGroup (Fin 6)

namespace SixPointData

variable {D : Subgroup G} {σ : G →* Equiv.Perm (Fin 6)} {β : Multiplicative (Fin 6 → ZMod 2) →* G}

theorem exists_duad (hsp : SixPointData D σ β) {x : G} (hx : x ∈ D) (hx1 : x ≠ 1) :
    ∃ a b : Fin 6, a ≠ b ∧ x = β (Multiplicative.ofAdd (Sp4.duadVec a b)) := by
  obtain ⟨f, hf, rfl⟩ := (hsp.mem_iff _).mp hx
  have h1 : ¬ (f.toAdd = 0 ∨ f.toAdd = fun _ => 1) := fun h => hx1 ((hsp.eq_one_iff f hf).mpr h)
  have hl : Sp4.lin f.toAdd ≠ 0 := fun h0 => h1 ((Sp4.lin_even_eq_zero_iff _ hf).mp h0)
  obtain ⟨a, b, hab, hdv⟩ := Sp4.dv_surj _ hl
  have hD : Sp4.Even6 (Sp4.duadVec a b) := by
    have key : ∀ a b : Fin 6, a ≠ b → Sp4.Even6 (Sp4.duadVec a b) := by decide
    exact key a b hab
  have hlin : Sp4.lin (Sp4.duadVec a b) = Sp4.dv a b := by
    have key : ∀ a b : Fin 6, Sp4.lin (Sp4.duadVec a b) = Sp4.dv a b := by decide +kernel
    exact key a b
  have hsim := (Sp4.lin_eq_iff _ _ hf hD).mp (hdv.trans hlin.symm)
  refine ⟨a, b, hab, ?_⟩
  rcases hsim with h | h
  · have hfe : f = Multiplicative.ofAdd (Sp4.duadVec a b) := by
      rw [← ofAdd_toAdd f, h]
    rw [hfe]
  · have hfe : f = Multiplicative.ofAdd (Sp4.duadVec a b) * Multiplicative.ofAdd Sp4.ones := by
      rw [← ofAdd_add, ← h, ofAdd_toAdd]
    have hone : β (Multiplicative.ofAdd Sp4.ones) = 1 :=
      (hsp.eq_one_iff _ (by decide)).mpr (Or.inr rfl)
    rw [hfe, map_mul, hone, mul_one]

end SixPointData

namespace EndHyp

variable {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}

private def e15h1_conj {D : Subgroup G} (hD : D.Normal) (g : G) : D ≃* D where
  toFun d := ⟨g * d.1 * g⁻¹, hD.conj_mem d.1 d.2 g⟩
  invFun d := ⟨g⁻¹ * d.1 * g⁻¹⁻¹, hD.conj_mem d.1 d.2 g⁻¹⟩
  left_inv d := Subtype.ext (by simp [mul_assoc])
  right_inv d := Subtype.ext (by simp [mul_assoc])
  map_mul' d d' := Subtype.ext (by simp [mul_assoc])

private theorem e15h1_conj_val {D : Subgroup G} (hD : D.Normal) (g : G) (d : D) :
    (e15h1_conj hD g d).1 = g * d.1 * g⁻¹ := rfl

private theorem e15h1_conj_mul {D : Subgroup G} (hD : D.Normal) (g g' : G) (d : D) :
    e15h1_conj hD (g * g') d = e15h1_conj hD g (e15h1_conj hD g' d) :=
  Subtype.ext (by simp only [e15h1_conj_val, mul_assoc, mul_inv_rev])

private theorem e15h1_conj_one {D : Subgroup G} (hD : D.Normal) (d : D) :
    e15h1_conj hD 1 d = d :=
  Subtype.ext (by simp [e15h1_conj_val])

private def e15h1_psi {D : Subgroup G} (θ : D ≃* Multiplicative Sp4.V4) (hD : D.Normal) (g : G) :
    Sp4.V4 ≃+ Sp4.V4 :=
  MulEquiv.toAdditive (θ.symm.trans ((e15h1_conj hD g).trans θ))

theorem exists_sixPoint (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hE : eGroup Ω K ≤ K ⊔ K') :
    ∃ (σ : G →* Equiv.Perm (Fin 6)) (β : Multiplicative (Fin 6 → ZMod 2) →* G)
      (bf : zGroup Ω → zGroup Ω → ZMod 2), IsEndForm Ω bf ∧ SixPointData (zGroup Ω) σ β ∧
      ∀ (x y : zGroup Ω) (f g : Multiplicative (Fin 6 → ZMod 2)), ∑ i, f.toAdd i = 0 →
        ∑ i, g.toAdd i = 0 → x.1 = β f → y.1 = β g → bf x y = Sp4.dot f.toAdd g.toAdd := by
  haveI : Fact (EndHyp Ω) := ⟨h⟩
  haveI : Fact (Perp9 Ω) := ⟨h9⟩
  obtain ⟨hcard, hpt, -⟩ := h.natCard_zGroup_eq_sixteen_local h9 s h13 hE
  obtain ⟨bf, hbf⟩ := h.exists_endForm h9 s h13
  obtain ⟨θ0, hθ0⟩ := Sp4.exists_symplectic_iso hbf.sympForm hcard
  obtain ⟨θ, hθ⟩ : ∃ θ : zGroup Ω ≃* Multiplicative Sp4.V4,
      ∀ a b : zGroup Ω, Sp4.symp (Multiplicative.toAdd (θ a)) (Multiplicative.toAdd (θ b)) =
        bf a b :=
    ⟨{ θ0 with map_mul' := fun a b => θ0.map_mul a b }, hθ0⟩
  have hD : (zGroup Ω).Normal := zGroup_normal_of_conjInvariant h.thmD.hyp.conjInvariant
  obtain ⟨ψ, hψ⟩ : ∃ ψ : G → Sp4.V4 ≃+ Sp4.V4, ∀ g v, ψ g v =
      Multiplicative.toAdd (θ (e15h1_conj hD g (θ.symm (Multiplicative.ofAdd v)))) :=
    ⟨fun g => e15h1_psi θ hD g, fun g v => rfl⟩
  have hψθ : ∀ (g : G) (a : zGroup Ω),
      ψ g (Multiplicative.toAdd (θ a)) = Multiplicative.toAdd (θ (e15h1_conj hD g a)) := by
    intro g a
    rw [hψ]
    simp
  have hψmul : ∀ g g' v, ψ (g * g') v = ψ g (ψ g' v) := by
    intro g g' v
    obtain ⟨a, rfl⟩ : ∃ a : zGroup Ω, Multiplicative.toAdd (θ a) = v :=
      ⟨θ.symm (Multiplicative.ofAdd v), by simp⟩
    rw [hψθ, hψθ, hψθ, e15h1_conj_mul]
  have hψ1 : ∀ v, ψ 1 v = v := by
    intro v
    obtain ⟨a, rfl⟩ : ∃ a : zGroup Ω, Multiplicative.toAdd (θ a) = v :=
      ⟨θ.symm (Multiplicative.ofAdd v), by simp⟩
    rw [hψθ, e15h1_conj_one]
  have hiso : ∀ (g : G) (x y : Sp4.V4), Sp4.symp (ψ g x) (ψ g y) = Sp4.symp x y := by
    intro g x y
    obtain ⟨a, rfl⟩ : ∃ a : zGroup Ω, Multiplicative.toAdd (θ a) = x :=
      ⟨θ.symm (Multiplicative.ofAdd x), by simp⟩
    obtain ⟨b, rfl⟩ : ∃ b : zGroup Ω, Multiplicative.toAdd (θ b) = y :=
      ⟨θ.symm (Multiplicative.ofAdd y), by simp⟩
    rw [hψθ, hψθ, hθ, hθ]
    exact hbf.conj g a b (e15h1_conj hD g a) (e15h1_conj hD g b) rfl rfl
  choose σ0 hσ0 using fun g => Sp4.isometry_eq_perm (ψ g) (hiso g)
  have hσmul : ∀ g g', σ0 (g * g') = σ0 g * σ0 g' := by
    intro g g'
    apply Sp4.perm_unique
    intro a b
    rw [← hσ0 (g * g') a b, hψmul, hσ0 g' a b, hσ0 g, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  obtain ⟨σ, hσ⟩ : ∃ σ : G →* Equiv.Perm (Fin 6), ∀ g, σ g = σ0 g :=
    ⟨MonoidHom.mk' σ0 hσmul, fun g => rfl⟩
  have hfix : ∀ g, σ0 g = 1 → ∀ v, ψ g v = v := by
    intro g hg v
    by_cases hv : v = 0
    · rw [hv, map_zero]
    · obtain ⟨a, b, hab, rfl⟩ := Sp4.dv_surj v hv
      rw [hσ0 g a b, hg, Equiv.Perm.one_apply, Equiv.Perm.one_apply]
  have hker : ∀ g, σ0 g = 1 ↔ g ∈ Subgroup.centralizer (zGroup Ω : Set G) := by
    intro g
    constructor
    · intro hg
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have h1 := hfix g hg (Multiplicative.toAdd (θ ⟨d, hd⟩))
      rw [hψθ] at h1
      have h2 : e15h1_conj hD g ⟨d, hd⟩ = ⟨d, hd⟩ :=
        θ.injective (Multiplicative.toAdd.injective h1)
      have h3 : g * d * g⁻¹ = d := congrArg Subtype.val h2
      calc d * g = (g * d * g⁻¹) * g := by rw [h3]
        _ = g * d := by group
    · intro hg
      rw [Subgroup.mem_centralizer_iff] at hg
      have hc : ∀ d : zGroup Ω, e15h1_conj hD g d = d := by
        intro d
        apply Subtype.ext
        rw [e15h1_conj_val, ← hg d.1 d.2]
        group
      have hid : ∀ v, ψ g v = v := by
        intro v
        obtain ⟨d, rfl⟩ : ∃ d : zGroup Ω, Multiplicative.toAdd (θ d) = v :=
          ⟨θ.symm (Multiplicative.ofAdd v), by simp⟩
        rw [hψθ, hc]
      apply Sp4.perm_unique
      intro a b
      rw [Equiv.Perm.one_apply, Equiv.Perm.one_apply, ← hσ0 g a b, hid]
  obtain ⟨β, hβ⟩ : ∃ β : Multiplicative (Fin 6 → ZMod 2) →* G,
      ∀ f, β f = ((θ.symm (Multiplicative.ofAdd (Sp4.lin f.toAdd)) : zGroup Ω) : G) :=
    ⟨MonoidHom.mk' (fun f => ((θ.symm (Multiplicative.ofAdd (Sp4.lin f.toAdd)) : zGroup Ω) : G))
      (fun f g => by simp [ofAdd_add, map_add]), fun f => rfl⟩
  have hβD : ∀ f, β f ∈ zGroup Ω := fun f => by
    rw [hβ]
    exact (θ.symm _).2
  have hmem : ∀ g : G, g ∈ zGroup Ω ↔
      ∃ f : Multiplicative (Fin 6 → ZMod 2), ∑ i, f.toAdd i = 0 ∧ β f = g := by
    intro g
    constructor
    · intro hg
      obtain ⟨f, hf, hfv⟩ := Sp4.exists_even_lin_eq (Multiplicative.toAdd (θ ⟨g, hg⟩))
      refine ⟨Multiplicative.ofAdd f, ?_, ?_⟩
      · show ∑ i, (Multiplicative.ofAdd f).toAdd i = 0
        rw [toAdd_ofAdd]
        exact hf
      · rw [hβ, toAdd_ofAdd, hfv]
        simp
    · rintro ⟨f, -, rfl⟩
      exact hβD f
  have heq1 : ∀ f : Multiplicative (Fin 6 → ZMod 2), ∑ i, f.toAdd i = 0 →
      (β f = 1 ↔ f.toAdd = 0 ∨ f.toAdd = fun _ => 1) := by
    intro f hf
    have key := Sp4.lin_even_eq_zero_iff f.toAdd hf
    rw [hβ]
    constructor
    · intro h1
      have h4 : θ.symm (Multiplicative.ofAdd (Sp4.lin f.toAdd)) = 1 := Subtype.ext h1
      rw [MulEquiv.map_eq_one_iff, ofAdd_eq_one] at h4
      exact key.mp h4
    · intro h1
      have h4 : θ.symm (Multiplicative.ofAdd (Sp4.lin f.toAdd)) = 1 := by
        rw [MulEquiv.map_eq_one_iff, ofAdd_eq_one]
        exact key.mpr h1
      rw [h4]
      rfl
  have hconj : ∀ (g : G) (f : Multiplicative (Fin 6 → ZMod 2)), ∑ i, f.toAdd i = 0 →
      g * β f * g⁻¹ = β (Multiplicative.ofAdd fun i => f.toAdd ((σ0 g).symm i)) := by
    intro g f hf
    have key : e15h1_conj hD g (θ.symm (Multiplicative.ofAdd (Sp4.lin f.toAdd))) =
        θ.symm (Multiplicative.ofAdd (Sp4.lin (fun i => f.toAdd ((σ0 g).symm i)))) := by
      apply θ.injective
      apply Multiplicative.toAdd.injective
      rw [← hψ g (Sp4.lin f.toAdd), MulEquiv.apply_symm_apply, toAdd_ofAdd]
      exact Sp4.lin_permVec (ψ g).toAddMonoidHom (σ0 g) (fun a b => hσ0 g a b) f.toAdd hf
    rw [hβ, hβ]
    exact congrArg Subtype.val key
  have hvalbf : ∀ x y : zGroup Ω, ∀ f g : Multiplicative (Fin 6 → ZMod 2),
      ∑ i, f.toAdd i = 0 → ∑ i, g.toAdd i = 0 → x.1 = β f → y.1 = β g →
        bf x y = Sp4.dot f.toAdd g.toAdd := by
    intro x y f g hf hg hx hy
    have hx' : x = θ.symm (Multiplicative.ofAdd (Sp4.lin f.toAdd)) :=
      Subtype.ext (by rw [hx, hβ])
    have hy' : y = θ.symm (Multiplicative.ofAdd (Sp4.lin g.toAdd)) :=
      Subtype.ext (by rw [hy, hβ])
    have hxv : Multiplicative.toAdd (θ x) = Sp4.lin f.toAdd := by
      rw [hx', MulEquiv.apply_symm_apply, toAdd_ofAdd]
    have hyv : Multiplicative.toAdd (θ y) = Sp4.lin g.toAdd := by
      rw [hy', MulEquiv.apply_symm_apply, toAdd_ofAdd]
    rw [← hθ x y, hxv, hyv, Sp4.symp_lin _ _ hf hg]
  have hrange : σ.range = alternatingGroup (Fin 6) := by
    obtain ⟨x3, hN3, ⟨a3, hx3a⟩, ⟨k3, -, hnc3⟩, -⟩ := h.exists_three_element h9 s h13 hE
    have hzD : z ∈ zGroup Ω := Subgroup.subset_closure ⟨K, s.mem, s.isInv⟩
    have hz1 : (⟨z, hzD⟩ : zGroup Ω) ≠ 1 := fun e => s.isInv.ne_one (congrArg Subtype.val e)
    have hne : Multiplicative.toAdd (θ ⟨z, hzD⟩) ≠ 0 := by
      intro h0
      apply hz1
      apply θ.injective
      apply Multiplicative.toAdd.injective
      rw [h0, map_one, toAdd_one]
    obtain ⟨a0, b0, hab0, hz0⟩ := Sp4.dv_surj _ hne
    have hx3z : e15h1_conj hD x3 ⟨z, hzD⟩ = ⟨z, hzD⟩ :=
      Subtype.ext (by rw [e15h1_conj_val]; exact conj_eq_self_of_normalizer s.isInv hN3)
    have hfixz : ψ x3 (Sp4.dv a0 b0) = Sp4.dv a0 b0 := by
      rw [← hz0, hψθ, hx3z]
    have hx3ne : σ x3 ≠ 1 := by
      intro e
      rw [hσ] at e
      have hc := (hker x3).mp e
      have hodd : Odd (orderOf x3) :=
        Odd.of_dvd_nat (Odd.pow (by decide : Odd 3)) (orderOf_dvd_of_pow_eq_one hx3a)
      have h1 := h.eq_one_of_odd_mem_centralizer_zGroup h9 s h13 hc hodd
      exact hnc3 (by rw [h1]; simp)
    have hfixσ : ({σ x3 a0, σ x3 b0} : Finset (Fin 6)) = {a0, b0} := by
      have hne' : σ x3 a0 ≠ σ x3 b0 := fun e => hab0 ((σ x3).injective e)
      rw [← Sp4.dv_eq_iff _ _ _ _ hne' hab0, hσ, ← hσ0 x3 a0 b0, hfixz]
    have hnz : ∀ a b : Fin 6, a ≠ b → Sp4.dv a b ≠ 0 := by decide
    have htrans : ∀ v w : Sp4.V4, v ≠ 0 → w ≠ 0 → ∃ g : G, ψ g v = w := by
      intro v w hv hw
      obtain ⟨p, hp⟩ : ∃ p : zGroup Ω, Multiplicative.toAdd (θ p) = v :=
        ⟨θ.symm (Multiplicative.ofAdd v), by simp⟩
      obtain ⟨q, hq⟩ : ∃ q : zGroup Ω, Multiplicative.toAdd (θ q) = w :=
        ⟨θ.symm (Multiplicative.ofAdd w), by simp⟩
      have hp1 : p.1 ≠ 1 := by
        intro e
        apply hv
        rw [← hp, show p = 1 from Subtype.ext e, map_one, toAdd_one]
      have hq1 : q.1 ≠ 1 := by
        intro e
        apply hw
        rw [← hq, show q = 1 from Subtype.ext e, map_one, toAdd_one]
      obtain ⟨gp, hgp⟩ := hpt p.1 p.2 hp1
      obtain ⟨gq, hgq⟩ := hpt q.1 q.2 hq1
      have hpc : e15h1_conj hD gp ⟨z, hzD⟩ = p :=
        Subtype.ext (by rw [e15h1_conj_val]; exact hgp.symm)
      have hqc : e15h1_conj hD gq ⟨z, hzD⟩ = q :=
        Subtype.ext (by rw [e15h1_conj_val]; exact hgq.symm)
      have hv' : ψ gp (Multiplicative.toAdd (θ ⟨z, hzD⟩)) = v := by
        rw [hψθ, hpc, hp]
      have hw' : ψ gq (Multiplicative.toAdd (θ ⟨z, hzD⟩)) = w := by
        rw [hψθ, hqc, hq]
      refine ⟨gq * gp⁻¹, ?_⟩
      rw [← hv', ← hψmul, show gq * gp⁻¹ * gp = gq by group, hw']
    have htr : ∀ a b c d : Fin 6, a ≠ b → c ≠ d →
        ∃ h ∈ σ.range, ({h a, h b} : Finset (Fin 6)) = {c, d} := by
      intro a b c d hab hcd
      obtain ⟨g, hg⟩ := htrans (Sp4.dv a b) (Sp4.dv c d) (hnz a b hab) (hnz c d hcd)
      refine ⟨σ g, MonoidHom.mem_range.mpr ⟨g, rfl⟩, ?_⟩
      have hne' : σ g a ≠ σ g b := fun e => hab ((σ g).injective e)
      rw [← Sp4.dv_eq_iff _ _ _ _ hne' hcd, hσ, ← hσ0 g a b, hg]
    have hperf : commutator σ.range = ⊤ := by
      have hsurj := MonoidHom.rangeRestrict_surjective σ
      have hG := h.commutator_eq_top_local h9 s h13 hE
      have hmap : Subgroup.map σ.rangeRestrict (commutator G) = commutator σ.range := by
        rw [commutator_def, commutator_def, Subgroup.map_commutator,
          Subgroup.map_top_of_surjective _ hsurj]
      rw [← hmap, hG, Subgroup.map_top_of_surjective _ hsurj]
    exact Sp4.eq_alternatingGroup_of_duad_transitive σ.range hperf htr a0 b0 hab0
      (MonoidHom.mem_range.mpr ⟨x3, rfl⟩) hx3ne ⟨a3, by rw [← map_pow, hx3a, map_one]⟩ hfixσ
  refine ⟨σ, β, bf, hbf, ⟨hmem, heq1, ?_, ?_, hrange⟩, hvalbf⟩
  · intro g f hf
    rw [hσ]
    exact hconj g f hf
  · intro g
    rw [hσ]
    exact hker g

theorem exists_hom_alternating_six (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hE : eGroup Ω K ≤ K ⊔ K') :
    ∃ φ : G →* alternatingGroup (Fin 6), Function.Surjective φ ∧
      φ.ker = Subgroup.centralizer (zGroup Ω : Set G) := by
  obtain ⟨σ, _, _, -, hsp, -⟩ := h.exists_sixPoint h9 s h13 hE
  have hmem : ∀ g, σ g ∈ alternatingGroup (Fin 6) := fun g => by
    rw [← hsp.range]
    exact MonoidHom.mem_range.mpr ⟨g, rfl⟩
  let φ : G →* alternatingGroup (Fin 6) :=
    { toFun := fun g => ⟨σ g, hmem g⟩
      map_one' := Subtype.ext (map_one σ)
      map_mul' := fun a b => Subtype.ext (map_mul σ a b) }
  refine ⟨φ, ?_, ?_⟩
  · intro y
    have hy : (y : Equiv.Perm (Fin 6)) ∈ σ.range := by
      rw [hsp.range]
      exact y.2
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hy
    exact ⟨g, Subtype.ext hg⟩
  · ext g
    rw [MonoidHom.mem_ker, ← hsp.ker g, Subtype.ext_iff]
    rfl

theorem exists_mulEquiv_quotient_pCore_six_of_local (h : EndHyp Ω) (h9 : Perp9 Ω)
    (s : TwinSit Ω K K' z) (h13 : zGroup Ω ≠ eGroup Ω K) (hE : eGroup Ω K ≤ K ⊔ K') :
    Nonempty (G ⧸ pCore 2 G ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨φ, hsurj, hker⟩ := h.exists_hom_alternating_six h9 s h13 hE
  have hc := h.centralizer_zGroup_eq_pCore h9 s h13
  haveI : (pCore 2 G).Normal := CFSG.pCore_normal
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (hker.trans hc).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)⟩

end EndHyp



open scoped commutatorElement in
private theorem e15h2_transfer_core {Γ : Type} [Group Γ] [Finite Γ] (hperf : commutator Γ = ⊤)
    {A B : Subgroup Γ} (hB : ∀ q ∈ B, ∀ g : Γ, g * q = q * g)
    (hsq : ∀ q ∈ B, q * q = 1) (hAB : A ⊓ B = ⊥) (hodd : ¬ 2 ∣ (A ⊔ B).index) :
    B = ⊥ := by
  set H : Subgroup Γ := A ⊔ B with hHdef
  have hBH : B ≤ H := le_sup_right
  have hBn : B.Normal := ⟨fun n hn g => by
    rw [hB n hn g, mul_assoc, mul_inv_cancel, mul_one]
    exact hn⟩
  have hconj : ∀ (y b : Γ), b ∈ B → b * y * b⁻¹ = y := fun y b hb => by
    rw [← hB b hb y, mul_assoc, mul_inv_cancel, mul_one]
  have hτ : ∀ g, MonoidHom.transfer (Abelianization.of (G := H)) g = 1 := by
    intro g
    have hg : g ∈ commutator Γ := by rw [hperf]; exact Subgroup.mem_top g
    have hle : commutator Γ ≤ (MonoidHom.transfer (Abelianization.of (G := H))).ker :=
      Abelianization.commutator_subset_ker _
    exact hle hg
  have hcomm : ∀ x ∈ H, ∀ y ∈ H, ⁅x, y⁆ ∈ A := by
    intro x hx y hy
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := A) (t := B)).mp hx
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := A) (t := B)).mp hy
    have h1 : ∀ a y : Γ, ∀ b ∈ B, ⁅a * b, y⁆ = ⁅a, y⁆ := by
      intro a y b hb
      rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
      calc a * b * y * (b⁻¹ * a⁻¹) * y⁻¹ = a * (b * y * b⁻¹) * a⁻¹ * y⁻¹ := by group
        _ = a * y * a⁻¹ * y⁻¹ := by rw [hconj y b hb]
    have h2 : ∀ a y : Γ, ∀ b ∈ B, ⁅a, y * b⁆ = ⁅a, y⁆ := by
      intro a y b hb
      rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
      calc a * (y * b) * a⁻¹ * (b⁻¹ * y⁻¹) = a * y * (b * a⁻¹ * b⁻¹) * y⁻¹ := by group
        _ = a * y * a⁻¹ * y⁻¹ := by rw [hconj a⁻¹ b hb]
    rw [h1 a₁ (a₂ * b₂) b₁ hb₁, h2 a₁ a₂ b₂ hb₂, commutatorElement_def]
    exact A.mul_mem (A.mul_mem (A.mul_mem ha₁ ha₂) (A.inv_mem ha₁)) (A.inv_mem ha₂)
  have hle : commutator H ≤ A.subgroupOf H := by
    refine Subgroup.commutator_le.mpr ?_
    intro x _ y _
    rw [Subgroup.mem_subgroupOf]
    exact hcomm (x : Γ) x.2 (y : Γ) y.2
  have hBA : B = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    have hqH : q ∈ H := hBH hq
    have key : ∀ (k : ℕ) (g₀ : Γ), g₀⁻¹ * q ^ k * g₀ ∈ H → g₀⁻¹ * q ^ k * g₀ = q ^ k := by
      intro k g₀ _
      rw [hB (q ^ k) (B.pow_mem hq k) g₀⁻¹, mul_assoc, inv_mul_cancel, mul_one]
    have htr := MonoidHom.transfer_eq_pow (Abelianization.of (G := H)) q key
    have hpow : q ^ H.index = q := by
      obtain ⟨k, hk⟩ : ∃ k, H.index = 2 * k + 1 := ⟨H.index / 2, by omega⟩
      have hq2 : q ^ 2 = 1 := by rw [sq]; exact hsq q hq
      rw [hk, pow_succ, pow_mul, hq2, one_pow, one_mul]
    have hmem1 : Abelianization.of (⟨q ^ H.index, MonoidHom.transfer_eq_pow_aux q key⟩ : H)
        = 1 := by
      rw [← htr]
      exact hτ q
    have hmem2 : Abelianization.of (⟨q, hqH⟩ : H) = 1 := by
      have e : (⟨q ^ H.index, MonoidHom.transfer_eq_pow_aux q key⟩ : H) = ⟨q, hqH⟩ :=
        Subtype.ext hpow
      rw [← e]
      exact hmem1
    have hmemc : (⟨q, hqH⟩ : H) ∈ commutator H := by
      rw [← Abelianization.ker_of H, MonoidHom.mem_ker]
      exact hmem2
    have hqA : q ∈ A := Subgroup.mem_subgroupOf.mp (hle hmemc)
    have hqAB : q ∈ A ⊓ B := ⟨hqA, hq⟩
    rw [hAB] at hqAB
    exact hqAB
  exact hBA

theorem eq_of_transfer {D Q T : Subgroup G} [D.Normal] [Q.Normal] (hDQ : D ≤ Q)
    (hperf : commutator G = ⊤) (hcent : ∀ q ∈ Q, ∀ g : G, g * q * g⁻¹ * q⁻¹ ∈ D)
    (hsq : ∀ q ∈ Q, q * q = 1) (hTQ : T ⊓ Q = D) (hodd : ¬ 2 ∣ (T ⊔ Q).index) : Q = D := by
  set π : G →* G ⧸ D := QuotientGroup.mk' D with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective D
  have hperf' : commutator (G ⧸ D) = ⊤ := by
    have h := map_commutator_eq G π
    rw [hperf, MonoidHom.range_eq_top_of_surjective π hπs,
      Subgroup.map_top_of_surjective π hπs] at h
    exact h.symm
  have hcent' : ∀ q ∈ Q.map π, ∀ g : G ⧸ D, g * q = q * g := by
    intro q hq g
    obtain ⟨q₀, hq₀, rfl⟩ := Subgroup.mem_map.mp hq
    obtain ⟨g₀, rfl⟩ := hπs g
    rw [← map_mul, ← map_mul, hπdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have e : (g₀ * q₀)⁻¹ * (q₀ * g₀) = q₀⁻¹ * (g₀⁻¹ * q₀ * g₀⁻¹⁻¹ * q₀⁻¹) * q₀⁻¹⁻¹ := by
      group
    rw [e]
    exact Subgroup.Normal.conj_mem inferInstance _ (hcent q₀ hq₀ g₀⁻¹) q₀⁻¹
  have hsq' : ∀ q ∈ Q.map π, q * q = 1 := by
    intro q hq
    obtain ⟨q₀, hq₀, rfl⟩ := Subgroup.mem_map.mp hq
    rw [← map_mul, hsq q₀ hq₀, map_one]
  have hAB : T.map π ⊓ Q.map π = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx.1
    obtain ⟨q, hq, hqt⟩ := Subgroup.mem_map.mp hx.2
    have hd : q⁻¹ * t ∈ D := (QuotientGroup.eq).mp hqt
    have htQ : t ∈ Q := by
      have e : t = q * (q⁻¹ * t) := by group
      rw [e]
      exact Q.mul_mem hq (hDQ hd)
    have htD : t ∈ D := by
      have : t ∈ T ⊓ Q := ⟨ht, htQ⟩
      rwa [hTQ] at this
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff t).mpr htD
  have hodd' : ¬ 2 ∣ (T.map π ⊔ Q.map π).index := by
    have hker : π.ker ≤ T ⊔ Q := by
      rw [hπdef, QuotientGroup.ker_mk']
      exact hDQ.trans le_sup_right
    rw [← Subgroup.map_sup, Subgroup.index_map_eq (T ⊔ Q) hπs hker]
    exact hodd
  have hB := e15h2_transfer_core hperf' hcent' hsq' hAB hodd'
  have hQD : Q ≤ D := by
    intro q hq
    have hm : π q ∈ Q.map π := Subgroup.mem_map_of_mem π hq
    rw [hB, Subgroup.mem_bot] at hm
    exact (QuotientGroup.eq_one_iff q).mp hm
  exact le_antisymm hQD hDQ

private theorem e15h2_eq_zpowers {U : Subgroup G} {u : G} (hu : u ∈ U) (hu4 : orderOf u = 4)
    (hU4 : Nat.card ↥U = 4) : U = Subgroup.zpowers u := by
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hu) ?_).symm
  rw [Nat.card_zpowers, hu4, hU4]

private theorem e15h2_coset {K U : Subgroup G} (hUK : U ≤ K) (hK8 : Nat.card ↥K = 8)
    (hU4 : Nat.card ↥U = 4) {w x : G} (hw : w ∈ K) (hwU : w ∉ U) (hx : x ∈ K) (hxU : x ∉ U) :
    w⁻¹ * x ∈ U := by
  have hcard : Nat.card ↥(U.subgroupOf K) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUK).toEquiv, hU4]
  have hidx : (U.subgroupOf K).index = 2 := by
    have h := (U.subgroupOf K).card_mul_index
    rw [hcard, hK8] at h
    omega
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff'.mp hidx
  have hw2 : a * ⟨w, hw⟩ ∈ U.subgroupOf K := by
    rcases ha ⟨w, hw⟩ with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd (Subgroup.mem_subgroupOf.mp h1) hwU
  have hx2 : a * ⟨x, hx⟩ ∈ U.subgroupOf K := by
    rcases ha ⟨x, hx⟩ with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd (Subgroup.mem_subgroupOf.mp h1) hxU
  have hm := (U.subgroupOf K).mul_mem ((U.subgroupOf K).inv_mem hw2) hx2
  have e : (a * ⟨w, hw⟩)⁻¹ * (a * ⟨x, hx⟩) = (⟨w⁻¹ * x, K.mul_mem (K.inv_mem hw) hx⟩ : K) := by
    apply Subtype.ext
    simp [mul_assoc]
  rw [e] at hm
  exact Subgroup.mem_subgroupOf.mp hm

private theorem e15h2_zpow_mem_sq_iff {u : G} (hu4 : orderOf u = 4) (t : ℤ) :
    u ^ t ∈ Subgroup.zpowers (u ^ 2) ↔ Even t := by
  have e : ∀ s : ℤ, (u ^ 2) ^ s = u ^ (2 * s) := fun s => by
    rw [← zpow_natCast, ← zpow_mul]
    norm_num
  constructor
  · rintro ⟨s, hs⟩
    have hs' : (u ^ 2) ^ s = u ^ t := hs
    have h1 : u ^ (t - 2 * s) = 1 := by
      rw [zpow_sub, ← e, hs', mul_inv_cancel]
    have h2 : ((orderOf u : ℕ) : ℤ) ∣ t - 2 * s := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [hu4] at h2
    obtain ⟨c, hc⟩ := h2
    exact ⟨s + 2 * c, by push_cast at hc; omega⟩
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    show (u ^ 2) ^ s = u ^ t
    rw [e, hs]
    congr 1
    ring

private theorem e15h2_odd_of_conj {u w : G} (hu4 : orderOf u = 4) {e : ℤ}
    (he : w * u * w⁻¹ = u ^ e) : Odd e := by
  rcases Int.even_or_odd e with hE | hO
  · exfalso
    obtain ⟨m, hm⟩ := hE
    have h1 : (u ^ e) ^ 2 = 1 := by
      rw [← zpow_natCast, ← zpow_mul]
      apply orderOf_dvd_iff_zpow_eq_one.mp
      rw [hu4]
      exact ⟨m, by push_cast; omega⟩
    have h2 : w * u ^ 2 * w⁻¹ = 1 := by
      rw [← conj_pow, he, h1]
    have h3 : u ^ 2 = 1 := by
      calc u ^ 2 = w⁻¹ * (w * u ^ 2 * w⁻¹) * w := by group
        _ = 1 := by rw [h2]; group
    have h4 := orderOf_dvd_of_pow_eq_one h3
    rw [hu4] at h4
    norm_num at h4
  · exact hO

private theorem e15h2_sq_zpow (x : G) (s : ℤ) : (x ^ 2) ^ s = x ^ (2 * s) := by
  rw [← zpow_natCast, ← zpow_mul]
  norm_num

private theorem e15h2_sq_eq {K : Subgroup G} {z u : G} (hz : IsUniqueInvolution K z)
    (huK : u ∈ K) (hu4 : orderOf u = 4) : u ^ 2 = z := by
  have hmem : u ^ 2 ∈ K := K.pow_mem huK 2
  have h4 : u ^ 4 = 1 := by
    rw [← hu4]
    exact pow_orderOf_eq_one u
  have hsq : u ^ 2 * u ^ 2 = 1 := by
    rw [← pow_add]
    exact h4
  have hne : u ^ 2 ≠ 1 := by
    intro e1
    have h3 := orderOf_dvd_of_pow_eq_one e1
    rw [hu4] at h3
    norm_num at h3
  exact (hz.unique (u ^ 2) hmem hsq).resolve_left hne

private theorem e15h2_sup_mem {K J U V : Subgroup G} (hUK : U ≤ K) (hVJ : V ≤ J)
    (hbot : K ⊓ J = ⊥) (hcomm : ∀ a ∈ U, ∀ b ∈ V, a * b = b * a) {x : G} (hx : x ∈ U ⊔ V)
    (hxK : x ∈ K) : x ∈ U := by
  obtain ⟨a, ha, b, hb, rfl⟩ := perpP_mem_sup hcomm hx
  have hbK : b ∈ K := by
    simpa using K.mul_mem (K.inv_mem (hUK ha)) hxK
  have hb1 : b ∈ K ⊓ J := ⟨hbK, hVJ hb⟩
  rw [hbot, Subgroup.mem_bot] at hb1
  rw [hb1, mul_one]
  exact ha

private theorem e15h2_sylow_card8 {Γ : Type} [Group Γ] [Finite Γ] (hΓ : Nat.card Γ = 360)
    (P : Sylow 2 Γ) : Nat.card P = 8 := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp P.isPGroup'
  have hmul : Nat.card P * (P : Subgroup Γ).index = 360 := by
    rw [← hΓ]
    exact Subgroup.card_mul_index _
  have hm : ¬ 2 ∣ (P : Subgroup Γ).index := Sylow.not_dvd_index P
  rw [hn] at hmul ⊢
  rcases Nat.lt_or_ge n 4 with hn4 | hn4
  · interval_cases n
    · exfalso
      norm_num at hmul
      omega
    · exfalso
      norm_num at hmul
      omega
    · exfalso
      norm_num at hmul
      omega
    · norm_num
  · exfalso
    have h16 : 16 ∣ 2 ^ n := by
      have e16 : (16 : ℕ) = 2 ^ 4 := by norm_num
      rw [e16]
      exact pow_dvd_pow 2 hn4
    have h360 : 16 ∣ 360 := by
      rw [← hmul]
      exact Dvd.dvd.mul_right h16 _
    norm_num at h360

private theorem e15h2_card_A6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 6)
  have hp : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  omega

namespace EndHyp

variable {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}

theorem notMem_omegaNbr_of_notMem_twinSet (h : EndHyp Ω) (h9 : Perp9 Ω) (hK : K ∈ Ω)
    {J : Subgroup G} (hJt : J ∉ twinSet Ω K) : J ∉ omegaNbr Ω K := by
  intro hJN
  apply hJt
  rw [← h.kPerp_eq_twinSet_of_perp9 h9 hK]
  exact Set.mem_insert_of_mem K hJN

theorem pair_action (h : EndHyp Ω) (hK : K ∈ Ω) {J : Subgroup G} (hJ : J ∈ omegaStarNbr Ω K)
    (hJn : J ∉ omegaNbr Ω K) {u v : G} (hu : u ∈ K ⊓ Subgroup.normalizer (J : Set G))
    (hu4 : orderOf u = 4) (hv : v ∈ J ⊓ Subgroup.normalizer (K : Set G)) (hv4 : orderOf v = 4)
    {r : G} (hr : r ∈ K) (hrU : r ∉ Subgroup.normalizer (J : Set G)) :
    ∃ a : ℤ, Odd a ∧ v * r * v⁻¹ = r * u ^ a := by
  have hJΩ : J ∈ Ω := hJ.1
  have hKJ : K ≠ J := fun e => hJ.2.1 e.symm
  obtain ⟨-, hU4, -, -, hcomm, -⟩ := pair_structure h hK hJ hJn
  have hK8 : Nat.card ↥K = 8 := h.card_eq_eight hK
  have huv : Commute u v := hcomm u hu v hv
  have hUz : K ⊓ Subgroup.normalizer (J : Set G) = Subgroup.zpowers u :=
    e15h2_eq_zpowers hu hu4 hU4
  have hvJN : v ∈ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer hv.1
  have hc : v * r * v⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hv.2 r).mp hr
  have hcN : v * r * v⁻¹ ∉ Subgroup.normalizer (J : Set G) := by
    intro hcJ
    apply hrU
    have h3 := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hvJN) hcJ) hvJN
    convert h3 using 1
    group
  have hcr : r⁻¹ * (v * r * v⁻¹) ∈ K ⊓ Subgroup.normalizer (J : Set G) :=
    e15h2_coset inf_le_left hK8 hU4 hr (fun hh => hrU hh.2) hc (fun hh => hcN hh.2)
  rw [hUz] at hcr
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hcr
  have hcrel : v * r * v⁻¹ = r * u ^ a := by rw [ha]; group
  refine ⟨a, ?_, hcrel⟩
  rcases Int.even_or_odd a with hae | hao
  · exfalso
    obtain ⟨b, hb⟩ := hae
    have hu2a : u ^ (2 * a) = 1 :=
      orderOf_dvd_iff_zpow_eq_one.mp (by rw [hu4]; exact ⟨b, by push_cast; omega⟩)
    have hvu1 : v * u * v⁻¹ = u := by
      rw [← huv.eq]
      group
    have hvu : v * u ^ a * v⁻¹ = u ^ a := by
      rw [← conj_zpow, hvu1]
    have hvr2 : v ^ 2 * r * (v ^ 2)⁻¹ = r := by
      calc v ^ 2 * r * (v ^ 2)⁻¹ = v * (v * r * v⁻¹) * v⁻¹ := by
            rw [sq, mul_inv_rev]; simp only [mul_assoc]
        _ = v * (r * u ^ a) * v⁻¹ := by rw [hcrel]
        _ = (v * r * v⁻¹) * (v * u ^ a * v⁻¹) := by group
        _ = r * u ^ a * u ^ a := by rw [hcrel, hvu]
        _ = r * u ^ (2 * a) := by rw [mul_assoc, ← zpow_add, show a + a = 2 * a by ring]
        _ = r := by rw [hu2a, mul_one]
    have hrv2 : v ^ 2 * r = r * v ^ 2 := by
      calc v ^ 2 * r = (v ^ 2 * r * (v ^ 2)⁻¹) * v ^ 2 := (inv_mul_cancel_right _ _).symm
        _ = r * v ^ 2 := by rw [hvr2]
    have huv2 : Commute u (v ^ 2) := huv.pow_right 2
    set S : Subgroup G := K ⊓ Subgroup.centralizer ({v ^ 2} : Set G) with hS
    have huS : u ∈ S := ⟨hu.1, Subgroup.mem_centralizer_singleton_iff.mpr huv2.eq⟩
    have hrS : r ∈ S := ⟨hr, Subgroup.mem_centralizer_singleton_iff.mpr hrv2.symm⟩
    have hUS : Subgroup.zpowers u ≤ S := Subgroup.zpowers_le.mpr huS
    have hcardU : Nat.card ↥(Subgroup.zpowers u) = 4 := by rw [Nat.card_zpowers, hu4]
    have hne : Nat.card ↥S ≠ 4 := by
      intro h4
      have heq : Subgroup.zpowers u = S :=
        Subgroup.eq_of_le_of_card_ge hUS (by rw [hcardU, h4])
      have hrU' : r ∈ Subgroup.zpowers u := heq ▸ hrS
      rw [← hUz] at hrU'
      exact hrU hrU'.2
    have hge : 4 ≤ Nat.card ↥S := by
      have := Subgroup.card_le_of_le hUS
      omega
    have hdvd : Nat.card ↥S ∣ 8 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : S ≤ K)
      rwa [hK8] at this
    have hS8 : Nat.card ↥S = 8 := by
      have hle8 : Nat.card ↥S ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
      have hc5 : Nat.card ↥S = 5 ∨ Nat.card ↥S = 6 ∨ Nat.card ↥S = 7 ∨ Nat.card ↥S = 8 := by
        omega
      rcases hc5 with h5 | h5 | h5 | h5
      · rw [h5] at hdvd; norm_num at hdvd
      · rw [h5] at hdvd; norm_num at hdvd
      · rw [h5] at hdvd; norm_num at hdvd
      · exact h5
    have hSK : S = K := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    have hKC : K ≤ Subgroup.centralizer ({v ^ 2} : Set G) := by
      intro k hk
      have hkS : k ∈ S := hSK ▸ hk
      exact hkS.2
    have hvJinv : IsUniqueInvolution J (v ^ 2) := by
      obtain ⟨zJ, hzJ⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hJΩ
      have hmem : v ^ 2 ∈ J := J.pow_mem hv.1 2
      have hsq : v ^ 2 * v ^ 2 = 1 := by
        calc v ^ 2 * v ^ 2 = v ^ 4 := by rw [← pow_add]
          _ = 1 := by rw [← hv4]; exact pow_orderOf_eq_one v
      have hne1 : v ^ 2 ≠ 1 := by
        intro e1
        have h3 := orderOf_dvd_of_pow_eq_one e1
        rw [hv4] at h3
        norm_num at h3
      have hvz : v ^ 2 = zJ := (hzJ.unique (v ^ 2) hmem hsq).resolve_left hne1
      rw [hvz]
      exact hzJ
    have hKN : K ≤ Subgroup.normalizer (J : Set G) :=
      Sec6Gen.le_normalizer_of_le_centralizer h.thmD.hyp hJΩ hK hJ.2.1 hvJinv le_rfl
        (h.thmD.two K hK) (by omega) hKC
    exact hrU (hKN hr)
  · exact hao

theorem natCard_sup_pair (h : EndHyp Ω) (hK : K ∈ Ω) {J : Subgroup G} (hJ : J ∈ omegaStarNbr Ω K)
    (hJn : J ∉ omegaNbr Ω K) :
    Nat.card ↥(K ⊔ J ⊓ Subgroup.normalizer (K : Set G)) = 32 := by
  have hJΩ : J ∈ Ω := hJ.1
  have hKJ : K ≠ J := fun e => hJ.2.1 e.symm
  have hbot : K ⊓ J = ⊥ := perpP_inf_bot h hK hJΩ hKJ hJn
  obtain ⟨-, -, -, hV4, -, -⟩ := pair_structure h hK hJ hJn
  have hK8 : Nat.card ↥K = 8 := h.card_eq_eight hK
  have hVN : J ⊓ Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    inf_le_right
  have hprod := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer hVN
  have hVK : (J ⊓ Subgroup.normalizer (K : Set G)) ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxJ : x ∈ K ⊓ J := ⟨hx.2, hx.1.1⟩
    rw [hbot] at hxJ
    exact hxJ
  rw [hVK, Subgroup.card_bot, sup_comm, hV4, hK8] at hprod
  omega

open scoped Pointwise in
theorem inf_pCore_pair (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) {J : Subgroup G} (hJ : J ∈ omegaStarNbr Ω K)
    (hJn : J ∉ omegaNbr Ω K) {j : G} (hj : IsUniqueInvolution J j) :
    (K ⊔ J ⊓ Subgroup.normalizer (K : Set G)) ⊓ pCore 2 G = Subgroup.closure {z, j} := by
  have hJΩ : J ∈ Ω := hJ.1
  have hKJ : K ≠ J := fun e => hJ.2.1 e.symm
  obtain ⟨hcycU, hU4, hcycV, hV4, hcomm, hsup⟩ := pair_structure h s.mem hJ hJn
  have hK8 : Nat.card ↥K = 8 := h.card_eq_eight s.mem
  have hbot : K ⊓ J = ⊥ := perpP_inf_bot h s.mem hJΩ hKJ hJn
  obtain ⟨u, huU, hu4, -⟩ := perpP_gen hcycU hU4
  obtain ⟨v, hvV, hv4, -⟩ := perpP_gen hcycV hV4
  have hUz : K ⊓ Subgroup.normalizer (J : Set G) = Subgroup.zpowers u :=
    e15h2_eq_zpowers huU hu4 hU4
  have hVz : J ⊓ Subgroup.normalizer (K : Set G) = Subgroup.zpowers v :=
    e15h2_eq_zpowers hvV hv4 hV4
  have huK : u ∈ K := huU.1
  have hvJ : v ∈ J := hvV.1
  have hvN : v ∈ Subgroup.normalizer (K : Set G) := hvV.2
  have huv : Commute u v := hcomm u huU v hvV
  have hz2 : u ^ 2 = z := e15h2_sq_eq s.isInv huK hu4
  have hj2 : v ^ 2 = j := e15h2_sq_eq hj hvJ hv4
  have hzQ : z ∈ pCore 2 G := h.mem_pCore s.mem s.isInv
  have hjQ : j ∈ pCore 2 G := h.mem_pCore hJΩ hj
  have hQn : (pCore 2 G).Normal := CFSG.pCore_normal
  have hKQ : K ⊓ pCore 2 G = Subgroup.zpowers z := by
    rw [← centralizer_zGroup_eq_pCore h h9 s h13]
    exact inf_centralizer_zGroup_eq_zpowers h h9 s h13
  have hKQt : ∀ t : ℤ, u ^ t ∈ K ⊓ pCore 2 G ↔ Even t := fun t => by
    rw [hKQ, ← hz2]
    exact e15h2_zpow_mem_sq_iff hu4 t
  obtain ⟨w, hwK, hwU⟩ : ∃ w ∈ K, w ∉ K ⊓ Subgroup.normalizer (J : Set G) := by
    by_contra hcon
    push Not at hcon
    have hle : K ≤ K ⊓ Subgroup.normalizer (J : Set G) := fun x hx => hcon x hx
    have := Subgroup.card_le_of_le hle
    omega
  have hwN : w ∉ Subgroup.normalizer (J : Set G) := fun hh => hwU ⟨hwK, hh⟩
  obtain ⟨a₀, ha₀, hvw⟩ := pair_action h s.mem hJ hJn huU hu4 hvV hv4 hwK hwN
  have hwu : w * u * w⁻¹ ∈ K ⊓ Subgroup.normalizer (J : Set G) := by
    have hwX := hsup ((le_sup_left : K ≤ K ⊔ J) hwK)
    have huX : u ∈ (K ⊓ Subgroup.normalizer (J : Set G)) ⊔
        (J ⊓ Subgroup.normalizer (K : Set G)) := Subgroup.mem_sup_left huU
    have hwuX := (Subgroup.mem_normalizer_iff.mp hwX u).mp huX
    have hwuK : w * u * w⁻¹ ∈ K := K.mul_mem (K.mul_mem hwK huK) (K.inv_mem hwK)
    exact e15h2_sup_mem inf_le_left inf_le_left hbot hcomm hwuX hwuK
  obtain ⟨e, he⟩ : ∃ e : ℤ, u ^ e = w * u * w⁻¹ := by
    rw [hUz] at hwu
    exact Subgroup.mem_zpowers_iff.mp hwu
  have he_odd : Odd e := e15h2_odd_of_conj hu4 he.symm
  have hc_odd : Odd (-(e * a₀)) := (he_odd.mul ha₀).neg
  have hwuw : w * u ^ a₀ * w⁻¹ = u ^ (e * a₀) := by
    rw [← conj_zpow, ← he, ← zpow_mul]
  have h1 : v * w = w * u ^ a₀ * v := by
    calc v * w = (v * w * v⁻¹) * v := by group
      _ = w * u ^ a₀ * v := by rw [hvw]
  have hv_eq : (w * u ^ a₀ * w⁻¹) * (w * v * w⁻¹) = v := by
    calc (w * u ^ a₀ * w⁻¹) * (w * v * w⁻¹) = (w * u ^ a₀ * v) * w⁻¹ := by group
      _ = (v * w) * w⁻¹ := by rw [h1]
      _ = v := by group
  have hwvw : w * v * w⁻¹ = u ^ (-(e * a₀)) * v := by
    rw [hwuw] at hv_eq
    calc w * v * w⁻¹ = (u ^ (e * a₀))⁻¹ * (u ^ (e * a₀) * (w * v * w⁻¹)) := by group
      _ = (u ^ (e * a₀))⁻¹ * v := by rw [hv_eq]
      _ = u ^ (-(e * a₀)) * v := by rw [zpow_neg]
  have hVN : J ⊓ Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    inf_le_right
  have hKN : K ≤ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer
  apply le_antisymm
  · rintro n ⟨hnKV, hnQ⟩
    have hnN : n ∈ Subgroup.normalizer (K : Set G) := (sup_le hKN hVN) hnKV
    have hmem : n ∈ ((J ⊓ Subgroup.normalizer (K : Set G) : Subgroup G) : Set G) * (K : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hVN, sup_comm]
      exact hnKV
    obtain ⟨b, hb, k, hk, rfl⟩ := Set.mem_mul.mp hmem
    have hbz : b ∈ Subgroup.zpowers v := by
      rw [← hVz]
      exact hb
    obtain ⟨β, rfl⟩ := Subgroup.mem_zpowers_iff.mp hbz
    by_cases hkU : k ∈ K ⊓ Subgroup.normalizer (J : Set G)
    ·
      have hkz : k ∈ Subgroup.zpowers u := by
        rw [← hUz]
        exact hkU
      obtain ⟨γ, rfl⟩ := Subgroup.mem_zpowers_iff.mp hkz
      have hcm : Commute (u ^ γ) (v ^ β) := (huv.zpow_left γ).zpow_right β
      have hnQ' : u ^ γ * v ^ β ∈ pCore 2 G := by
        rw [hcm.eq]
        exact hnQ
      have hnN' : u ^ γ * v ^ β ∈ Subgroup.normalizer (K : Set G) :=
        Subgroup.mul_mem _ (Subgroup.le_normalizer (K.zpow_mem huK γ))
          (Subgroup.zpow_mem _ hvN β)
      have hwn : w * (u ^ γ * v ^ β) * w⁻¹ = u ^ (e * γ + -(e * a₀) * β) * v ^ β := by
        have hA : w * u ^ γ * w⁻¹ = u ^ (e * γ) := by
          rw [← conj_zpow, ← he, ← zpow_mul]
        have hB : w * v ^ β * w⁻¹ = u ^ (-(e * a₀) * β) * v ^ β := by
          rw [← conj_zpow, hwvw, (huv.zpow_left (-(e * a₀))).mul_zpow β, ← zpow_mul]
        calc w * (u ^ γ * v ^ β) * w⁻¹ = (w * u ^ γ * w⁻¹) * (w * v ^ β * w⁻¹) := by group
          _ = u ^ (e * γ) * (u ^ (-(e * a₀) * β) * v ^ β) := by rw [hA, hB]
          _ = u ^ (e * γ + -(e * a₀) * β) * v ^ β := by rw [zpow_add, mul_assoc]
      have hP : w * (u ^ γ * v ^ β) * w⁻¹ * (u ^ γ * v ^ β)⁻¹ =
          u ^ (e * γ + -(e * a₀) * β - γ) := by
        rw [hwn]
        group
      have hPK : w * (u ^ γ * v ^ β) * w⁻¹ * (u ^ γ * v ^ β)⁻¹ ∈ K := by
        have h2 : (u ^ γ * v ^ β) * w⁻¹ * (u ^ γ * v ^ β)⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp hnN' w⁻¹).mp (K.inv_mem hwK)
        have h3 := K.mul_mem hwK h2
        convert h3 using 1
        group
      have hPQ : w * (u ^ γ * v ^ β) * w⁻¹ * (u ^ γ * v ^ β)⁻¹ ∈ pCore 2 G :=
        (pCore 2 G).mul_mem (hQn.conj_mem _ hnQ' w) ((pCore 2 G).inv_mem hnQ')
      have hPz : w * (u ^ γ * v ^ β) * w⁻¹ * (u ^ γ * v ^ β)⁻¹ ∈ K ⊓ pCore 2 G := ⟨hPK, hPQ⟩
      rw [hP] at hPz
      have hEv : Even (e * γ + -(e * a₀) * β - γ) := (hKQt _).mp hPz
      have hβ : Even β := by
        obtain ⟨p, hp⟩ := id he_odd
        have hEq : e * γ + -(e * a₀) * β - γ = 2 * (p * γ) - e * a₀ * β := by
          rw [hp]
          ring
        have h2 : Even (2 * (p * γ) - e * a₀ * β) := hEq ▸ hEv
        have hX : Even (e * a₀ * β) := (Int.even_sub.mp h2).mp (even_two_mul _)
        rcases Int.even_mul.mp hX with h3 | h3
        · exact absurd h3 (Int.not_even_iff_odd.mpr (he_odd.mul ha₀))
        · exact h3
      obtain ⟨s', hs'⟩ := hβ
      have hvβ : v ^ β = j ^ s' := by
        rw [hs', show s' + s' = 2 * s' by ring, ← e15h2_sq_zpow, hj2]
      have hvβQ : v ^ β ∈ pCore 2 G := by
        rw [hvβ]
        exact (pCore 2 G).zpow_mem hjQ s'
      have hγQ : u ^ γ ∈ pCore 2 G := by
        have e1 : u ^ γ = (u ^ γ * v ^ β) * (v ^ β)⁻¹ := by group
        rw [e1]
        exact (pCore 2 G).mul_mem hnQ' ((pCore 2 G).inv_mem hvβQ)
      obtain ⟨γ', hγ'⟩ := (hKQt γ).mp ⟨K.zpow_mem huK γ, hγQ⟩
      have hγz : u ^ γ = z ^ γ' := by
        rw [hγ', show γ' + γ' = 2 * γ' by ring, ← e15h2_sq_zpow, hz2]
      rw [← hcm.eq, hγz, hvβ]
      exact Subgroup.mul_mem _
        (Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_insert z {j})) _)
        (Subgroup.zpow_mem _ (Subgroup.subset_closure
          (Set.mem_insert_of_mem z (Set.mem_singleton j))) _)
    ·
      have hwk : w⁻¹ * k ∈ K ⊓ Subgroup.normalizer (J : Set G) :=
        e15h2_coset inf_le_left hK8 hU4 hwK hwU hk hkU
      have hwkz : w⁻¹ * k ∈ Subgroup.zpowers u := by
        rw [← hUz]
        exact hwk
      obtain ⟨γ, hγ⟩ := Subgroup.mem_zpowers_iff.mp hwkz
      have hkeq : k = w * u ^ γ := by
        rw [hγ]
        group
      rw [hkeq] at hnQ ⊢
      have hconj_v : u ^ γ * v * (u ^ γ)⁻¹ = v := by
        rw [(huv.zpow_left γ).eq]
        group
      have hcβ : Commute (u ^ (-(e * a₀))) (v ^ β) := (huv.zpow_left _).zpow_right β
      have hnv : v ^ β * (w * u ^ γ) * v * (v ^ β * (w * u ^ γ))⁻¹ * v⁻¹ =
          u ^ (-(e * a₀)) := by
        calc v ^ β * (w * u ^ γ) * v * (v ^ β * (w * u ^ γ))⁻¹ * v⁻¹
            = v ^ β * (w * (u ^ γ * v * (u ^ γ)⁻¹) * w⁻¹) * (v ^ β)⁻¹ * v⁻¹ := by group
          _ = v ^ β * (w * v * w⁻¹) * (v ^ β)⁻¹ * v⁻¹ := by rw [hconj_v]
          _ = v ^ β * (u ^ (-(e * a₀)) * v) * (v ^ β)⁻¹ * v⁻¹ := by rw [hwvw]
          _ = (v ^ β * u ^ (-(e * a₀))) * (v * (v ^ β)⁻¹ * v⁻¹) := by group
          _ = (u ^ (-(e * a₀)) * v ^ β) * (v * (v ^ β)⁻¹ * v⁻¹) := by rw [← hcβ.eq]
          _ = u ^ (-(e * a₀)) * (v ^ β * (v * (v ^ β)⁻¹ * v⁻¹)) := by group
          _ = u ^ (-(e * a₀)) := by group
      have hcQ : u ^ (-(e * a₀)) ∈ pCore 2 G := by
        rw [← hnv]
        have h2 : v * (v ^ β * (w * u ^ γ))⁻¹ * v⁻¹ ∈ pCore 2 G :=
          hQn.conj_mem _ ((pCore 2 G).inv_mem hnQ) v
        have h3 := (pCore 2 G).mul_mem hnQ h2
        convert h3 using 1
        group
      exact absurd ((hKQt (-(e * a₀))).mp ⟨K.zpow_mem huK _, hcQ⟩)
        (Int.not_even_iff_odd.mpr hc_odd)
  · refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    rcases hx with hx | hx
    · rw [hx]
      exact ⟨(le_sup_left : K ≤ K ⊔ J ⊓ Subgroup.normalizer (K : Set G)) s.isInv.mem, hzQ⟩
    · rw [Set.mem_singleton_iff.mp hx]
      have hjV : j ∈ J ⊓ Subgroup.normalizer (K : Set G) := by
        rw [← hj2]
        exact (J ⊓ Subgroup.normalizer (K : Set G)).pow_mem hvV 2
      exact ⟨(le_sup_right : J ⊓ Subgroup.normalizer (K : Set G) ≤
        K ⊔ J ⊓ Subgroup.normalizer (K : Set G)) hjV, hjQ⟩

private theorem e15h2_zj_comm (h : EndHyp Ω) (s : TwinSit Ω K K' z) {J : Subgroup G}
    (hJ : J ∈ omegaStarNbr Ω K) (hJn : J ∉ omegaNbr Ω K) {j : G}
    (hj : IsUniqueInvolution J j) : z * j = j * z := by
  obtain ⟨hcycU, hU4, hcycV, hV4, hcomm, -⟩ := pair_structure h s.mem hJ hJn
  obtain ⟨u, huU, hu4, -⟩ := perpP_gen hcycU hU4
  obtain ⟨v, hvV, hv4, -⟩ := perpP_gen hcycV hV4
  have huv : Commute u v := hcomm u huU v hvV
  have hz2 : u ^ 2 = z := e15h2_sq_eq s.isInv huU.1 hu4
  have hj2 : v ^ 2 = j := e15h2_sq_eq hj hvV.1 hv4
  rw [← hz2, ← hj2]
  exact ((huv.pow_left 2).pow_right 2).eq

theorem pair_transfer_data (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) {J : Subgroup G} (hJ : J ∈ omegaStarNbr Ω K)
    (hJn : J ∉ omegaNbr Ω K) (hsyl : ∀ P : Sylow 2 (G ⧸ pCore 2 G), Nat.card P = 8) :
    ((K ⊔ J ⊓ Subgroup.normalizer (K : Set G)) ⊔ zGroup Ω) ⊓ pCore 2 G = zGroup Ω ∧
      ¬ 2 ∣ (((K ⊔ J ⊓ Subgroup.normalizer (K : Set G)) ⊔ zGroup Ω) ⊔ pCore 2 G).index := by
  have hJΩ : J ∈ Ω := hJ.1
  have hKJ : K ≠ J := fun e => hJ.2.1 e.symm
  have hbot : K ⊓ J = ⊥ := perpP_inf_bot h s.mem hJΩ hKJ hJn
  have hD : (zGroup Ω).Normal := zGroup_normal_of_conjInvariant h.thmD.hyp.conjInvariant
  have hQn : (pCore 2 G).Normal := CFSG.pCore_normal
  have hDQ : zGroup Ω ≤ pCore 2 G := h.zGroup_le_pCore
  obtain ⟨j, hj⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hJΩ
  have hX : (K ⊔ J ⊓ Subgroup.normalizer (K : Set G)) ⊓ pCore 2 G = Subgroup.closure {z, j} :=
    inf_pCore_pair h h9 s h13 hJ hJn hj
  have hzD : z ∈ zGroup Ω := Subgroup.subset_closure ⟨K, s.mem, s.isInv⟩
  have hjD : j ∈ zGroup Ω := Subgroup.subset_closure ⟨J, hJΩ, hj⟩
  have hZD : Subgroup.closure ({z, j} : Set G) ≤ zGroup Ω := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    rcases hx with hx | hx
    · rw [hx]
      exact hzD
    · rw [Set.mem_singleton_iff.mp hx]
      exact hjD
  have h1 : ((K ⊔ J ⊓ Subgroup.normalizer (K : Set G)) ⊔ zGroup Ω) ⊓ pCore 2 G = zGroup Ω := by
    apply le_antisymm
    · rintro y ⟨hyX, hyQ⟩
      obtain ⟨x, hx, d, hd, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hyX
      have hxQ : x ∈ pCore 2 G := by
        have e1 : x = (x * d) * d⁻¹ := by group
        rw [e1]
        exact (pCore 2 G).mul_mem hyQ ((pCore 2 G).inv_mem (hDQ hd))
      have hxZ : x ∈ (K ⊔ J ⊓ Subgroup.normalizer (K : Set G)) ⊓ pCore 2 G := ⟨hx, hxQ⟩
      rw [hX] at hxZ
      exact (zGroup Ω).mul_mem (hZD hxZ) hd
    · intro y hy
      exact ⟨Subgroup.mem_sup_right hy, hDQ hy⟩
  refine ⟨h1, ?_⟩
  have hT : ((K ⊔ J ⊓ Subgroup.normalizer (K : Set G)) ⊔ zGroup Ω) ⊔ pCore 2 G =
      (K ⊔ J ⊓ Subgroup.normalizer (K : Set G)) ⊔ pCore 2 G := by
    rw [sup_assoc, sup_eq_right.mpr hDQ]
  rw [hT]
  have hzj : z * j = j * z := e15h2_zj_comm h s hJ hJn hj
  have hZcard : Nat.card ↥(Subgroup.closure ({z, j} : Set G)) = 4 := by
    have hzord : orderOf z = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact s.isInv.sq) s.isInv.ne_one
    have hjord : orderOf j = 2 := orderOf_eq_prime (by rw [pow_two]; exact hj.sq) hj.ne_one
    have hzC : z ∈ Subgroup.centralizer ((Subgroup.zpowers j : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact ((show Commute z j from hzj).zpow_right k).eq.symm
    have hzN : Subgroup.zpowers z ≤
        Subgroup.normalizer ((Subgroup.zpowers j : Subgroup G) : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hzC)
    have hinter : Subgroup.zpowers z ⊓ Subgroup.zpowers j = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx1 : x ∈ K ⊓ J :=
        ⟨(Subgroup.zpowers_le.mpr s.isInv.mem) hx.1, (Subgroup.zpowers_le.mpr hj.mem) hx.2⟩
      rw [hbot] at hx1
      exact hx1
    have hprodZ := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer hzN
    rw [hinter, Subgroup.card_bot, Nat.card_zpowers, Nat.card_zpowers, hzord, hjord] at hprodZ
    have hcl : Subgroup.zpowers z ⊔ Subgroup.zpowers j = Subgroup.closure ({z, j} : Set G) := by
      apply le_antisymm
      · exact sup_le (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert _ _)))
          (Subgroup.zpowers_le.mpr
            (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
      · refine (Subgroup.closure_le _).mpr ?_
        intro x hx
        rcases hx with hx | hx
        · rw [hx]
          exact Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
        · rw [Set.mem_singleton_iff.mp hx]
          exact Subgroup.mem_sup_right (Subgroup.mem_zpowers j)
    rw [hcl] at hprodZ
    omega
  have hXN : (K ⊔ J ⊓ Subgroup.normalizer (K : Set G)) ≤ Subgroup.normalizer
      ((pCore 2 G : Subgroup G) : Set G) := Subgroup.le_normalizer_of_normal
  have hprod := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer hXN
  rw [hX, hZcard, natCard_sup_pair h s.mem hJ hJn] at hprod
  have hA : Nat.card ↥((K ⊔ J ⊓ Subgroup.normalizer (K : Set G)) ⊔ pCore 2 G) =
      8 * Nat.card ↥(pCore 2 G) := by
    omega
  have hQpos : 0 < Nat.card ↥(pCore 2 G) := Nat.card_pos
  have hi1 := Subgroup.card_mul_index ((K ⊔ J ⊓ Subgroup.normalizer (K : Set G)) ⊔ pCore 2 G)
  have hi2 := Subgroup.card_mul_index (pCore 2 G)
  have hQ8 : (pCore 2 G).index = 8 * ((K ⊔ J ⊓ Subgroup.normalizer (K : Set G)) ⊔
      pCore 2 G).index := by
    apply Nat.eq_of_mul_eq_mul_left hQpos
    rw [hi2, ← hi1, hA]
    ring
  obtain ⟨P⟩ : Nonempty (Sylow 2 (G ⧸ pCore 2 G)) := inferInstance
  have hPi := Subgroup.card_mul_index (P : Subgroup (G ⧸ pCore 2 G))
  have hPnd : ¬ 2 ∣ (P : Subgroup (G ⧸ pCore 2 G)).index := Sylow.not_dvd_index P
  have hPc : Nat.card ↥(P : Subgroup (G ⧸ pCore 2 G)) = 8 := hsyl P
  have hQidx : (pCore 2 G).index = Nat.card (G ⧸ pCore 2 G) := rfl
  rw [hPc] at hPi
  intro hdiv
  apply hPnd
  have hPQ : (pCore 2 G).index = 8 * (P : Subgroup (G ⧸ pCore 2 G)).index := by
    rw [hQidx]
    exact hPi.symm
  have : ((K ⊔ J ⊓ Subgroup.normalizer (K : Set G)) ⊔ pCore 2 G).index =
      (P : Subgroup (G ⧸ pCore 2 G)).index := by
    omega
  rw [← this]
  exact hdiv

theorem pCore_eq_zGroup_of_perfect (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hperf : commutator G = ⊤)
    (hsyl : ∀ P : Sylow 2 (G ⧸ pCore 2 G), Nat.card P = 8) : pCore 2 G = zGroup Ω := by
  obtain ⟨-, -, -, -, J, hJΩ, -, hJ, hJt, -⟩ := exists_choice h h9 s
  have hJn : J ∉ omegaNbr Ω K := h.notMem_omegaNbr_of_notMem_twinSet h9 s.mem hJt
  have hD : (zGroup Ω).Normal := zGroup_normal_of_conjInvariant h.thmD.hyp.conjInvariant
  have hQn : (pCore 2 G).Normal := CFSG.pCore_normal
  have hpt := pair_transfer_data h h9 s h13 hJ hJn hsyl
  exact eq_of_transfer h.zGroup_le_pCore hperf
    (fun q hq g => pCore_commutator_mem_zGroup h h9 s h13 hq g)
    (fun q hq => (pCore_comm_mul_self h h9 s h13 q hq q hq).2) hpt.1 hpt.2

theorem pCore_eq_zGroup_of_local (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hE : eGroup Ω K ≤ K ⊔ K') : pCore 2 G = zGroup Ω := by
  have hperf : commutator G = ⊤ := commutator_eq_top_local h h9 s h13 hE
  obtain ⟨e⟩ := exists_mulEquiv_quotient_pCore_six_of_local h h9 s h13 hE
  have hA : Nat.card (G ⧸ pCore 2 G) = 360 := by
    rw [Nat.card_congr e.toEquiv, e15h2_card_A6]
  exact pCore_eq_zGroup_of_perfect h h9 s h13 hperf (fun P => e15h2_sylow_card8 hA P)

end EndHyp

end CFSG.ClassicalInvolution.Q3.Sec13
