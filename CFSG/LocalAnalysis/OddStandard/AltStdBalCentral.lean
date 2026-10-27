module

public import CFSG.LocalAnalysis.OddStandard.AltStdBalCaseE
public import CFSG.LocalAnalysis.OddStandard.AltStdBalPermCentral

public section

namespace CFSG.OddStandard.AltStdBal

open Subgroup Equiv Equiv.Perm
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

section Central

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem false_of_central_sq (h : Setting G L n) (d : Cyc L Q z) {q : G}
    (hq2 : q ^ 2 = z) (hqc : ∀ c ∈ centralizer ({z} : Set G), c * q = q * c) : False := by
  obtain ⟨g, hne, hcomm, haK, hzK'⟩ := exists_partner h d
  have h' := h.conj g
  have d' := d.conj g
  obtain ⟨e'⟩ := h'.iso
  have haC : g⁻¹ * z * g ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 hcomm
  have hqa : q ∈ centralizer ({g⁻¹ * z * g} : Set G) :=
    mem_centralizer_singleton_iff.2 (hqc _ haC).symm
  have hqN : q ∈ normalizer ((CFSG.conjugate L g : Subgroup G) : Set G) :=
    centralizer_le_normalizer h' d' hqa
  have hzC' : z ∈ centralizer ({g⁻¹ * z * g} : Set G) :=
    mem_centralizer_singleton_iff.2 hcomm.symm
  have hzN : z ∈ normalizer ((CFSG.conjugate L g : Subgroup G) : Set G) :=
    centralizer_le_normalizer h' d' hzC'
  set σ : Perm (Fin n) := rho e' h'.hn ⟨q, hqN⟩ with hσ
  have hσ2 : σ ^ 2 = rho e' h'.hn ⟨z, hzN⟩ := by
    rw [hσ, ← map_pow]
    congr 1
    exact Subtype.ext hq2
  have hz2 : (⟨z, hzN⟩ : normalizer ((CFSG.conjugate L g : Subgroup G) : Set G)) ^ 2 = 1 :=
    Subtype.ext (by simpa [sq] using d.mul_self)
  have hσ4 : σ ^ 4 = 1 := by
    have : σ ^ 4 = (σ ^ 2) ^ 2 := by rw [← pow_mul]
    rw [this, hσ2, ← map_pow, hz2, map_one]
  have hρz : rho e' h'.hn ⟨z, hzN⟩ ≠ 1 := fun h1 =>
    hzK' ((rho_eq_one_iff e' h'.hn ⟨z, hzN⟩).1 h1)
  have hsgn : sign (σ ^ 2) = 1 := by
    rw [map_pow]
    exact Int.units_pow_two _
  let lam : alternatingGroup (Fin n) := ⟨σ ^ 2, mem_alternatingGroup.2 hsgn⟩
  have hlam2 : orderOf lam = 2 := by
    refine orderOf_eq_prime (p := 2) ?_ ?_
    · apply Subtype.ext
      show (σ ^ 2) ^ 2 = 1
      rw [← pow_mul]
      exact hσ4
    · intro h1
      apply hρz
      rw [← hσ2]
      exact congrArg Subtype.val h1
  have hcent : ∀ dd ∈ centralizer ({lam} : Set (alternatingGroup (Fin n))),
      σ * (dd : Perm (Fin n)) = (dd : Perm (Fin n)) * σ := by
    intro dd hdd
    rw [mem_centralizer_singleton_iff] at hdd
    have hdd' : (dd : Perm (Fin n)) * σ ^ 2 = σ ^ 2 * (dd : Perm (Fin n)) :=
      congrArg Subtype.val hdd
    have h1 := rho_conj e' h'.hn ⟨z, hzN⟩ dd
    rw [← hσ2] at h1
    have h2 : σ ^ 2 * (dd : Perm (Fin n)) * (σ ^ 2)⁻¹ = (dd : Perm (Fin n)) := by
      rw [← hdd']
      group
    have h3 := h1.symm.trans h2
    have h4 := e'.injective (Subtype.ext h3 |>.trans (e'.apply_symm_apply dd).symm)
    have h5 : z * (e'.symm dd : G) * z⁻¹ = (e'.symm dd : G) := congrArg Subtype.val h4
    have hyz : (e'.symm dd : G) * z = z * (e'.symm dd : G) := by
      calc (e'.symm dd : G) * z = (z * (e'.symm dd : G) * z⁻¹) * z := by rw [h5]
        _ = z * (e'.symm dd : G) := by group
    have hyC : (e'.symm dd : G) ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 hyz
    have h6 := hqc _ hyC
    have h7 := rho_conj e' h'.hn ⟨q, hqN⟩ dd
    have h8 : q * (e'.symm dd : G) * q⁻¹ = (e'.symm dd : G) := by
      calc q * (e'.symm dd : G) * q⁻¹ = (e'.symm dd : G) * q * q⁻¹ := by rw [← h6]
        _ = (e'.symm dd : G) := by group
    have h9 : e' ⟨q * (e'.symm dd : G) * q⁻¹, (mem_normalizer_iff.mp hqN _).mp (e'.symm dd).2⟩ =
        dd := by
      have : (⟨q * (e'.symm dd : G) * q⁻¹, (mem_normalizer_iff.mp hqN _).mp (e'.symm dd).2⟩ :
          CFSG.conjugate L g) = e'.symm dd := Subtype.ext h8
      rw [this, e'.apply_symm_apply]
    have h10 : σ * (dd : Perm (Fin n)) * σ⁻¹ = (dd : Perm (Fin n)) := by
      rw [hσ]
      refine h7.trans ?_
      rw [h9]
    calc σ * (dd : Perm (Fin n)) = (σ * (dd : Perm (Fin n)) * σ⁻¹) * σ := by group
      _ = (dd : Perm (Fin n)) * σ := by rw [h10]
  have h11 := sq_eq_one_of_commute_centralizer (α := Fin n) (by simpa using h'.hn) hlam2 hcent hσ4
  exact hρz (by rw [← hσ2]; exact h11)

theorem card_eq_two_of_central (h : Setting G L n) (d : Cyc L Q z)
    (hQc : ∀ c ∈ centralizer ({z} : Set G), ∀ q ∈ Q, c * q = q * c) : Nat.card Q = 2 := by
  rcases card_eq_two_or_four_le_Q d with h2 | h4
  · exact h2
  exfalso
  obtain ⟨q, hqQ, hq4⟩ := exists_orderOf_eq_two_pow (k := 2) d.cyclic d.pgroup
    (by simpa using h4)
  have hq2 : orderOf (q ^ 2) = 2 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hq4]; norm_num), hq4]
    norm_num
  have hqz : q ^ 2 = z :=
    eq_of_orderOf_eq_two_of_isCyclic d.cyclic (pow_mem hqQ 2) d.mem hq2 d.order
  exact false_of_central_sq h d hqz (fun c hc => hQc c hc q hqQ)

theorem mem_sup_or_inv_mul_mem_sup (h : Setting G L n) (d : Cyc L Q z) {u c : G}
    (hu : u ∈ centralizer ({z} : Set G)) (hu' : u ∉ L ⊔ Q)
    (hc : c ∈ centralizer ({z} : Set G)) : c ∈ L ⊔ Q ∨ u⁻¹ * c ∈ L ⊔ Q := by
  obtain ⟨e⟩ := h.iso
  by_cases hcq : c ∈ L ⊔ Q
  · exact Or.inl hcq
  · right
    have hs := signHom_eq_neg_one h d e hu hu'
    have hs' := signHom_eq_neg_one h d e hc hcq
    have hC : u⁻¹ * c ∈ centralizer ({z} : Set G) := mul_mem (inv_mem hu) hc
    rw [mem_sup_iff h d e hC]
    change signHom e h.hn ((⟨u, centralizer_le_normalizer h d hu⟩ :
      normalizer (L : Set G))⁻¹ * ⟨c, centralizer_le_normalizer h d hc⟩) = 1
    rw [map_mul, map_inv, hs, hs']
    decide

theorem central_of_commute_outer (h : Setting G L n) (d : Cyc L Q z) {u q : G}
    (hu : u ∈ centralizer ({z} : Set G)) (hu' : u ∉ L ⊔ Q) (hq : q ∈ Q) (huq : u * q = q * u) :
    ∀ c ∈ centralizer ({z} : Set G), c * q = q * c := by
  intro c hc
  rcases mem_sup_or_inv_mul_mem_sup h d hu hu' hc with hcq | hcq
  · exact (d.comm_sup hq hcq).symm
  · have h1 : q * (u⁻¹ * c) = (u⁻¹ * c) * q := d.comm_sup hq hcq
    have hc' : c = u * (u⁻¹ * c) := by group
    calc c * q = u * (u⁻¹ * c) * q := by rw [← hc']
      _ = u * (q * (u⁻¹ * c)) := by rw [h1]; group
      _ = (u * q) * (u⁻¹ * c) := by group
      _ = (q * u) * (u⁻¹ * c) := by rw [huq]
      _ = q * (u * (u⁻¹ * c)) := by group
      _ = q * c := by rw [← hc']

end Central

end CFSG.OddStandard.AltStdBal
