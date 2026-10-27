module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.CenMod
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.ExtB
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Fin4
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.ParaD
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Orbit

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem card_cent_step [Finite G] {y : G} (hy : y * y = 1) {N M : Subgroup G} (hNM : N ≤ M)
    (hMN : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N) (hyN : ∀ n ∈ N, y * n * y⁻¹ ∈ N)
    (hconj : ∀ p ∈ N, (p * y) * (p * y) = 1 → ∃ q ∈ N, p * y = q * y * q⁻¹) :
    Nat.card (cenMod M N y hMN) * Nat.card ↥(N ⊓ centralizer ({y} : Set G)) ≤
      Nat.card N * Nat.card ↥(M ⊓ centralizer ({y} : Set G)) := by
  have hF : ∀ f ∈ cenMod M N y hMN, ∃ n ∈ N, ∃ c ∈ M ⊓ centralizer ({y} : Set G), f = n * c := by
    intro f hf
    obtain ⟨k, hk, hkf⟩ := lift_cent hy hyN hconj hf.2
    refine ⟨k⁻¹, N.inv_mem hk, k * f, ⟨M.mul_mem (hNM hk) hf.1, ?_⟩, by group⟩
    show k * f ∈ centralizer ({y} : Set G)
    rw [mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    calc y * (k * f) = (y * (k * f) * y⁻¹) * y := by group
      _ = (k * f) * y := by rw [hkf]
  have := card_mul_inf_le hF
  have e : N ⊓ (M ⊓ centralizer ({y} : Set G)) = N ⊓ centralizer ({y} : Set G) := by
    rw [← inf_assoc, inf_of_le_left hNM]
  rw [e] at this
  exact this

theorem card_cent_chain [Finite G] {y : G} (hy : y * y = 1) (Pi : ℕ → Subgroup G)
    (h0 : Pi 0 = ⊥) {n : ℕ} (hfree : ∀ i < n, FreeSec2 y (Pi i) (Pi (i + 1)))
    (hconj : ∀ i < n, ∀ p ∈ Pi i, (p * y) * (p * y) = 1 → ∃ q ∈ Pi i, p * y = q * y * q⁻¹) :
    Nat.card (Pi n) ≤ Nat.card ↥(Pi n ⊓ centralizer ({y} : Set G)) ^ 2 := by
  induction n with
  | zero =>
    rw [h0]
    simp
  | succ i ih =>
    have ih' := ih (fun j hj => hfree j (by omega)) (fun j hj => hconj j (by omega))
    obtain ⟨hNM, hcomm, hsq, hyN, hyM, hcard⟩ := hfree i (by omega)
    have hMN : ∀ m ∈ Pi (i + 1), ∀ n ∈ Pi i, m * n * m⁻¹ ∈ Pi i := by
      intro m hm n' hn'
      have h := hcomm m hm n' (hNM hn')
      have e : m * n' * m⁻¹ = ⁅m, n'⁆ * n' := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (Pi i).mul_mem h hn'
    have hstep := card_cent_step hy hNM hMN hyN (hconj i (by omega))
    have hFcard : Nat.card (fixSec y (Pi i) (Pi (i + 1))) =
        Nat.card (cenMod (Pi (i + 1)) (Pi i) y hMN) :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun g => Iff.rfl))
    rw [← hFcard] at hstep
    set F := Nat.card (fixSec y (Pi i) (Pi (i + 1))) with hF
    set a := Nat.card (Pi i) with ha
    set b := Nat.card (Pi (i + 1)) with hb
    set c := Nat.card ↥(Pi i ⊓ centralizer ({y} : Set G)) with hc
    set d := Nat.card ↥(Pi (i + 1) ⊓ centralizer ({y} : Set G)) with hd
    have hapos : 0 < a := Nat.card_pos
    have hF2 : F ^ 2 = b * a := hcard
    have h1 : (F * c) ^ 2 ≤ (a * d) ^ 2 := Nat.pow_le_pow_left hstep 2
    have h2 : a * (b * c ^ 2) ≤ a * (a * d ^ 2) := by
      calc a * (b * c ^ 2) = F ^ 2 * c ^ 2 := by rw [hF2]; ring
        _ = (F * c) ^ 2 := by ring
        _ ≤ (a * d) ^ 2 := h1
        _ = a * (a * d ^ 2) := by ring
    have h3 : b * c ^ 2 ≤ a * d ^ 2 := Nat.le_of_mul_le_mul_left h2 hapos
    have h4 : b * a ≤ a * d ^ 2 := le_trans (Nat.mul_le_mul_left b ih') h3
    have h5 : a * b ≤ a * d ^ 2 := by rw [mul_comm]; exact h4
    exact Nat.le_of_mul_le_mul_left h5 hapos

theorem four_mul_le_card_cent [Finite G] {S P : Subgroup G} (hPS : P ≤ S) {y : G} (e : Fin 4 → G)
    (he : ∀ i, e i ∈ S ⊓ centralizer ({y} : Set G)) (hne : ∀ i j : Fin 4, i < j → (e i)⁻¹ * e j ∉ P) :
    4 * Nat.card ↥(P ⊓ centralizer ({y} : Set G)) ≤ Nat.card ↥(S ⊓ centralizer ({y} : Set G)) := by
  have hmem : ∀ (i : Fin 4) (p : ↥(P ⊓ centralizer ({y} : Set G))),
      e i * (p : G) ∈ S ⊓ centralizer ({y} : Set G) := fun i p =>
    (S ⊓ centralizer ({y} : Set G)).mul_mem (he i) ⟨hPS p.2.1, p.2.2⟩
  have hinj : Function.Injective (fun q : Fin 4 × ↥(P ⊓ centralizer ({y} : Set G)) =>
      (⟨e q.1 * (q.2 : G), hmem q.1 q.2⟩ : ↥(S ⊓ centralizer ({y} : Set G)))) := by
    intro a b hab
    have h0 := congrArg Subtype.val hab
    have h : e a.1 * (a.2 : G) = e b.1 * (b.2 : G) := h0
    have hij : a.1 = b.1 := by
      by_contra hne'
      rcases lt_or_gt_of_ne hne' with hlt | hgt
      · apply hne a.1 b.1 hlt
        have : (e a.1)⁻¹ * e b.1 = (a.2 : G) * (b.2 : G)⁻¹ := by
          have h' : e a.1 * (a.2 : G) * (b.2 : G)⁻¹ = e b.1 := by
            rw [h]; group
          calc (e a.1)⁻¹ * e b.1 = (e a.1)⁻¹ * (e a.1 * (a.2 : G) * (b.2 : G)⁻¹) := by rw [h']
            _ = (a.2 : G) * (b.2 : G)⁻¹ := by group
        rw [this]
        exact P.mul_mem a.2.2.1 (P.inv_mem b.2.2.1)
      · apply hne b.1 a.1 hgt
        have : (e b.1)⁻¹ * e a.1 = (b.2 : G) * (a.2 : G)⁻¹ := by
          have h' : e b.1 * (b.2 : G) * (a.2 : G)⁻¹ = e a.1 := by
            rw [← h]; group
          calc (e b.1)⁻¹ * e a.1 = (e b.1)⁻¹ * (e b.1 * (b.2 : G) * (a.2 : G)⁻¹) := by rw [h']
            _ = (b.2 : G) * (a.2 : G)⁻¹ := by group
        rw [this]
        exact P.mul_mem b.2.2.1 (P.inv_mem a.2.2.1)
    have hpp : (a.2 : G) = (b.2 : G) := by
      have h2 : e a.1 * (a.2 : G) = e a.1 * (b.2 : G) := by rw [h, ← hij]
      exact mul_left_cancel h2
    exact Prod.ext hij (Subtype.ext hpp)
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod] at this
  simpa using this

theorem centralizer_conj_eq (x w : G) :
    centralizer ({w * x * w⁻¹} : Set G) = cj w (centralizer ({x} : Set G)) := by
  ext g
  rw [mem_cj, mem_centralizer_iff, mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    have e : w⁻¹ * g * w * x = x * (w⁻¹ * g * w) := by
      calc w⁻¹ * g * w * x = w⁻¹ * (g * (w * x * w⁻¹)) * w := by group
        _ = w⁻¹ * ((w * x * w⁻¹) * g) * w := by rw [← h]
        _ = x * (w⁻¹ * g * w) := by group
    exact e.symm
  · intro h
    have e : (w * x * w⁻¹) * g = g * (w * x * w⁻¹) := by
      calc (w * x * w⁻¹) * g = w * (x * (w⁻¹ * g * w)) * w⁻¹ := by group
        _ = w * ((w⁻¹ * g * w) * x) * w⁻¹ := by rw [h]
        _ = g * (w * x * w⁻¹) := by group
    exact e

theorem sylowIn_cj_both {p : ℕ} {P C : Subgroup G} (m : G) (hP : SylowIn p P C) :
    SylowIn p (cj m P) (cj m C) := by
  refine ⟨?_, hP.isPGroup.map _, ?_⟩
  · rw [cj_eq_map, cj_eq_map]
    exact Subgroup.map_mono hP.le
  have := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj m).toMonoidHom) P C
    (MulAut.conj m).injective
  have e : (cj m P).relIndex (cj m C) = P.relIndex C := this
  rw [e]
  exact hP.2.2

theorem card_extremal [Finite G] {x : G} {T V S : Subgroup G} (hout : Out12 G x T V) {w : G}
    (hext : Sylow2In (S ⊓ centralizer ({w * x * w⁻¹} : Set G))
      (centralizer ({w * x * w⁻¹} : Set G))) :
    Nat.card ↥(S ⊓ centralizer ({w * x * w⁻¹} : Set G)) = Nat.card T := by
  have hTc : SylowIn 2 (cj w T) (centralizer ({w * x * w⁻¹} : Set G)) := by
    rw [centralizer_conj_eq]
    exact sylowIn_cj_both w hout.T_sylow
  have h := card_eq_of_sylow (C := centralizer ({w * x * w⁻¹} : Set G)) hTc hext
  rw [card_cj] at h
  exact h

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
