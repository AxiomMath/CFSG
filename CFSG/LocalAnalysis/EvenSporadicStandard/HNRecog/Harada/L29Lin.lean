module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.Open

variable {X : Type} [Group X]

private lemma mem_conj_iff {A : Subgroup X} {r x : X}
    (hr : r ∈ normalizer (A : Set X)) : r * x * r⁻¹ ∈ A ↔ x ∈ A :=
  ((mem_normalizer_iff.mp hr) x).symm

private lemma conj_mem_centralizer {i r w : X}
    (hw : w ∈ centralizer ({i} : Set X)) :
    r * w * r⁻¹ ∈ centralizer ({r * i * r⁻¹} : Set X) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hw ⊢
  calc (r * w * r⁻¹) * (r * i * r⁻¹)
      = r * (w * i) * r⁻¹ := by group
    _ = r * (i * w) * r⁻¹ := by rw [hw]
    _ = (r * i * r⁻¹) * (r * w * r⁻¹) := by group

private lemma mul_comm_of_mem {A : Subgroup X} (hA : IsElemAbelian 2 A) {a b : X}
    (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a := by
  haveI : IsMulCommutative A := hA.1
  have h := mul_comm' (⟨a, ha⟩ : A) (⟨b, hb⟩ : A)
  simpa using Subtype.ext_iff.mp h

private lemma inf_centralizer_eq_bot {A : Subgroup X} {i r z : X} (hA : IsElemAbelian 2 A)
    (hr : r ∈ normalizer (A : Set X)) (hi2 : i * i = 1) (hr5 : r ^ 5 = 1)
    (hinv : i * r * i⁻¹ * r ∈ A) (hfpf : ∀ a ∈ A, r * a * r⁻¹ = a → a = 1)
    (hzA : z ∈ A) (hzi : z ∈ centralizer ({i} : Set X))
    (hzi' : z ∈ centralizer ({r * i * r⁻¹} : Set X)) : z = 1 := by
  set α : X := i * r * i⁻¹ * r with hαdef
  have hαA : α ∈ A := by rw [hαdef]; exact hinv
  have hα : i * r * i⁻¹ = α * r⁻¹ := by rw [hαdef]; group
  have hα' : i * r = α * r⁻¹ * i := by
    calc i * r = i * r * i⁻¹ * i := by group
      _ = α * r⁻¹ * i := by rw [hα]
  have hii' : i * (r * i * r⁻¹) = α * (r ^ 2)⁻¹ := by
    calc i * (r * i * r⁻¹)
        = (i * r) * i * r⁻¹ := by group
      _ = (α * r⁻¹ * i) * i * r⁻¹ := by rw [hα']
      _ = α * r⁻¹ * (i * i) * r⁻¹ := by group
      _ = α * r⁻¹ * r⁻¹ := by rw [hi2]; group
      _ = α * (r ^ 2)⁻¹ := by group
  have hzi_eq : z * i = i * z := Subgroup.mem_centralizer_singleton_iff.mp hzi
  have hfix_i : i * z * i⁻¹ = z := by rw [← hzi_eq]; group
  have hzi'_eq : z * (r * i * r⁻¹) = (r * i * r⁻¹) * z :=
    Subgroup.mem_centralizer_singleton_iff.mp hzi'
  have hfix_i' : (r * i * r⁻¹) * z * (r * i * r⁻¹)⁻¹ = z := by
    rw [← hzi'_eq]; group
  have hfix_ii' : (i * (r * i * r⁻¹)) * z * (i * (r * i * r⁻¹))⁻¹ = z := by
    rw [mul_inv_rev]
    calc (i * (r * i * r⁻¹)) * z * ((r * i * r⁻¹)⁻¹ * i⁻¹)
        = i * ((r * i * r⁻¹) * z * (r * i * r⁻¹)⁻¹) * i⁻¹ := by group
      _ = i * z * i⁻¹ := by rw [hfix_i']
      _ = z := hfix_i
  have hbA : (r ^ 2)⁻¹ * z * r ^ 2 ∈ A := by
    simpa using (mem_conj_iff (inv_mem (pow_mem hr 2))).2 hzA
  have hfix_alpha : (α * (r ^ 2)⁻¹) * z * (α * (r ^ 2)⁻¹)⁻¹ =
      (r ^ 2)⁻¹ * z * r ^ 2 := by
    rw [mul_inv_rev, inv_inv]
    calc (α * (r ^ 2)⁻¹) * z * (r ^ 2 * α⁻¹)
        = α * ((r ^ 2)⁻¹ * z * r ^ 2) * α⁻¹ := by group
      _ = ((r ^ 2)⁻¹ * z * r ^ 2) * α * α⁻¹ := by
            rw [mul_comm_of_mem hA hαA hbA]
      _ = (r ^ 2)⁻¹ * z * r ^ 2 := by group
  have hzsq : (r ^ 2)⁻¹ * z * r ^ 2 = z := by
    rw [← hfix_alpha, ← hii']
    exact hfix_ii'
  have hz_comm_sq : Commute z (r ^ 2) := by
    rw [Commute]
    calc z * r ^ 2 = r ^ 2 * ((r ^ 2)⁻¹ * z * r ^ 2) := by group
      _ = r ^ 2 * z := by rw [hzsq]
  have hr6 : r ^ 6 = r := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, hr5, one_mul]
  have hr23 : (r ^ 2) ^ 3 = r := by
    rw [← pow_mul, show (2 * 3 : ℕ) = 6 from rfl, hr6]
  have hz_comm_r : Commute z r := by
    have := hz_comm_sq.pow_right 3
    rwa [hr23] at this
  have hz_fix : r * z * r⁻¹ = z := by
    rw [← hz_comm_r.eq]
    group
  exact hfpf z hzA hz_fix

theorem L29_card_centralizer_le {A : Subgroup X} (hA : IsElemAbelian 2 A)
    (hcard : Nat.card A = 2 ^ 8) {i r : X} (hi : i ∈ normalizer (A : Set X))
    (hr : r ∈ normalizer (A : Set X)) (hi2 : i * i = 1) (hr5 : r ^ 5 = 1)
    (hinv : i * r * i⁻¹ * r ∈ A) (hfpf : ∀ a ∈ A, r * a * r⁻¹ = a → a = 1) :
    Nat.card ↥(A ⊓ centralizer ({i} : Set X)) ≤ 16 := by
  classical
  haveI : Finite ↥A := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  set C : Subgroup X := A ⊓ centralizer ({i} : Set X) with hC
  change Nat.card ↥C ≤ 16
  have hCA : C ≤ A := by rw [hC]; exact inf_le_left
  have hCcent : C ≤ centralizer ({i} : Set X) := by rw [hC]; exact inf_le_right
  let f : ↥C × ↥C → ↥A := fun p =>
    ⟨p.1.1 * (r * p.2.1 * r⁻¹),
      A.mul_mem (hCA p.1.2) ((mem_conj_iff hr).2 (hCA p.2.2))⟩
  have hfinj : Function.Injective f := by
    intro p q heq
    obtain ⟨⟨px, hpxC⟩, ⟨py, hpyC⟩⟩ := p
    obtain ⟨⟨qx, hqxC⟩, ⟨qy, hqyC⟩⟩ := q
    have heq' : px * (r * py * r⁻¹) = qx * (r * qy * r⁻¹) := by
      have := congrArg Subtype.val heq
      simpa only [f] using this
    have hzC : qx⁻¹ * px ∈ C := C.mul_mem (C.inv_mem hqxC) hpxC
    have hzA : qx⁻¹ * px ∈ A := hCA hzC
    have hzi : qx⁻¹ * px ∈ centralizer ({i} : Set X) := hCcent hzC
    have hwC : qy * py⁻¹ ∈ C := C.mul_mem hqyC (C.inv_mem hpyC)
    have hwi : qy * py⁻¹ ∈ centralizer ({i} : Set X) := hCcent hwC
    have hzeq : qx⁻¹ * px = r * (qy * py⁻¹) * r⁻¹ := by
      have h1 : qx⁻¹ * (px * (r * py * r⁻¹)) = r * qy * r⁻¹ := by
        rw [heq']; group
      calc qx⁻¹ * px
          = qx⁻¹ * (px * (r * py * r⁻¹)) * (r * py * r⁻¹)⁻¹ := by group
        _ = (r * qy * r⁻¹) * (r * py * r⁻¹)⁻¹ := by rw [h1]
        _ = r * (qy * py⁻¹) * r⁻¹ := by group
    have hzi' : qx⁻¹ * px ∈ centralizer ({r * i * r⁻¹} : Set X) := by
      rw [hzeq]
      exact conj_mem_centralizer hwi
    have hz1 : qx⁻¹ * px = 1 :=
      inf_centralizer_eq_bot hA hr hi2 hr5 hinv hfpf hzA hzi hzi'
    have hpx : px = qx := by
      calc px = qx * (qx⁻¹ * px) := by group
        _ = qx * 1 := by rw [hz1]
        _ = qx := by group
    have hqy : qy * py⁻¹ = 1 := by
      have h2 : r * (qy * py⁻¹) * r⁻¹ = 1 := by rw [← hzeq, hz1]
      calc qy * py⁻¹ = r⁻¹ * (r * (qy * py⁻¹) * r⁻¹) * r := by group
        _ = r⁻¹ * 1 * r := by rw [h2]
        _ = 1 := by group
    have hpy : py = qy := by
      have h : qy = py := by
        calc qy = qy * py⁻¹ * py := by group
          _ = 1 * py := by rw [hqy]
          _ = py := by group
      exact h.symm
    exact Prod.ext (Subtype.ext hpx) (Subtype.ext hpy)
  have hcard_le : Nat.card ↥C * Nat.card ↥C ≤ Nat.card ↥A := by
    have h := Nat.card_le_card_of_injective f hfinj
    rwa [Nat.card_prod] at h
  have h : Nat.card ↥C * Nat.card ↥C ≤ 16 * 16 := by
    have := hcard_le
    rw [hcard] at this
    norm_num at this ⊢
    exact this
  exact Nat.mul_self_le_mul_self_iff.mp h

end CFSG.EvenSporadicStandard.HNRecog.Harada
