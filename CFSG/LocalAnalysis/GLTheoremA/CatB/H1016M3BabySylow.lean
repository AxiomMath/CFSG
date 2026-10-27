module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M3BabyData
import CFSG.Monster.B.Pinned.Primes.Extraspecial
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3.BabySyl

open CFSG.Monster.B.Pinned Subgroup
open scoped Matrix

section Generic

variable {G : Type*} [Group G]

private theorem exists_pow_mul [Finite G] {H : Subgroup G} {g : G} (hg : g ^ 3 = 1)
    (hN : ∀ h ∈ H, g⁻¹ * h * g ∈ H) {y : G} (hy : y ∈ H ⊔ zpowers g) :
    ∃ n < 3, ∃ u ∈ H, y = g ^ n * u := by
  have hN' : zpowers g ≤ normalizer (H : Set G) := zpowers_le.2 (mem_normalizer_of_conj hN)
  rw [sup_comm, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hN'] at hy
  obtain ⟨a, ha, u, hu, rfl⟩ := Set.mem_mul.1 hy
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 ha)
  exact ⟨n % 3, Nat.mod_lt _ (by norm_num), u, hu, by rw [← pow_eq_pow_mod n hg]⟩

private theorem exists_pow_of_mem [Finite G] {g y : G} (hg : g ^ 3 = 1) (hy : y ∈ zpowers g) :
    ∃ i < 3, y = g ^ i := by
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hy)
  exact ⟨n % 3, Nat.mod_lt _ (by norm_num), pow_eq_pow_mod n hg⟩

private theorem conj_mem_of_comm {H : Subgroup G} {g : G} (hc : ∀ h ∈ H, h * g = g * h) :
    ∀ h ∈ H, g⁻¹ * h * g ∈ H := fun h hh => by rwa [mul_assoc, hc h hh, inv_mul_cancel_left]

end Generic

private def baseA : Subgroup (GL (Fin 8) (ZMod 3)) := zpowers ga ⊔ zpowers gb ⊔ zpowers gc

def sylS : Subgroup (GL (Fin 8) (ZMod 3)) := baseA ⊔ zpowers gx

theorem sylS_le_KThree : sylS ≤ KThree := by
  obtain ⟨ha, hb, hc, hx⟩ := gens_mem_KThree
  exact sup_le (sup_le (sup_le (zpowers_le.2 ha) (zpowers_le.2 hb)) (zpowers_le.2 hc))
    (zpowers_le.2 hx)

private theorem mem_baseA : ga ∈ baseA ∧ gb ∈ baseA ∧ gc ∈ baseA :=
  ⟨mem_sup_left (mem_sup_left (mem_zpowers _)), mem_sup_left (mem_sup_right (mem_zpowers _)),
    mem_sup_right (mem_zpowers _)⟩

private theorem gx_inv : gx⁻¹ = gx ^ 2 :=
  inv_eq_of_mul_eq_one_right ((pow_succ' gx 2).symm.trans gens_pow_three.2.2.2)

private theorem comm_a_b : ∀ h ∈ zpowers ga, h * gb = gb * h := fun _ hh =>
  mem_centralizer_singleton_iff.1 (zpowers_le.2 (mem_centralizer_singleton_iff.2 gens_comm.1) hh)

private theorem comm_ab_c : ∀ h ∈ zpowers ga ⊔ zpowers gb, h * gc = gc * h := fun _ hh =>
  mem_centralizer_singleton_iff.1 (sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2
    gens_comm.2.1)) (zpowers_le.2 (mem_centralizer_singleton_iff.2 gens_comm.2.2)) hh)

private theorem baseA_comm {u v : GL (Fin 8) (ZMod 3)} (hu : u ∈ baseA) (hv : v ∈ baseA) :
    u * v = v * u := by
  have le : ∀ {g : GL (Fin 8) (ZMod 3)}, ga * g = g * ga → gb * g = g * gb → gc * g = g * gc →
      baseA ≤ centralizer {g} := fun ha hb hc =>
    sup_le (sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 ha))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 hb)))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 hc))
  obtain ⟨hab, hac, hbc⟩ := gens_comm
  have h1 := mem_centralizer_singleton_iff.1 (le rfl hab.symm hac.symm hu)
  have h2 := mem_centralizer_singleton_iff.1 (le hab rfl hbc.symm hu)
  have h3 := mem_centralizer_singleton_iff.1 (le hac hbc rfl hu)
  exact (mem_centralizer_singleton_iff.1 (le h1.symm h2.symm h3.symm hv)).symm

private theorem exists_of_mem_ab {s : GL (Fin 8) (ZMod 3)} (hs : s ∈ zpowers ga ⊔ zpowers gb) :
    ∃ j < 3, ∃ i < 3, s = gb ^ j * ga ^ i := by
  obtain ⟨j, hj, v, hv, rfl⟩ := exists_pow_mul gens_pow_three.2.1 (conj_mem_of_comm comm_a_b) hs
  obtain ⟨i, hi, rfl⟩ := exists_pow_of_mem gens_pow_three.1 hv
  exact ⟨j, hj, i, hi, rfl⟩

private theorem exists_of_mem_baseA {s : GL (Fin 8) (ZMod 3)} (hs : s ∈ baseA) :
    ∃ k < 3, ∃ j < 3, ∃ i < 3, s = gc ^ k * (gb ^ j * ga ^ i) := by
  obtain ⟨k, hk, u, hu, rfl⟩ :=
    exists_pow_mul gens_pow_three.2.2.1 (conj_mem_of_comm comm_ab_c) hs
  obtain ⟨j, hj, i, hi, rfl⟩ := exists_of_mem_ab hu
  exact ⟨k, hk, j, hj, i, hi, rfl⟩

private theorem gx_conj_mem : ∀ h ∈ baseA, gx⁻¹ * h * gx ∈ baseA := by
  obtain ⟨h1, h2, h3⟩ := gx_conj
  obtain ⟨ha, hb, hc⟩ := mem_baseA
  have e : ∀ h, (MulAut.conj gx⁻¹).toMonoidHom h = gx⁻¹ * h * gx := fun h => by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hle : baseA ≤ baseA.comap (MulAut.conj gx⁻¹).toMonoidHom := by
    refine sup_le (sup_le ?_ ?_) ?_ <;> rw [zpowers_le, mem_comap, e]
    · rw [h1]; exact mul_mem hb hc
    · rwa [h2]
    · rw [h3]; exact mul_mem (pow_mem ha 2) (mul_mem (pow_mem hb 2) (pow_mem hc 2))
  intro h hh
  have := hle hh
  rwa [mem_comap, e] at this

private theorem exists_of_mem_sylS {s : GL (Fin 8) (ZMod 3)} (hs : s ∈ sylS) :
    ∃ n < 3, ∃ u ∈ baseA, s = gx ^ n * u :=
  exists_pow_mul gens_pow_three.2.2.2 gx_conj_mem hs

theorem exists_eq_of_mem_sylS {s : GL (Fin 8) (ZMod 3)} (hs : s ∈ sylS) :
    ∃ n < 3, ∃ k < 3, ∃ j < 3, ∃ i < 3, s = gx ^ n * (gc ^ k * (gb ^ j * ga ^ i)) := by
  obtain ⟨n, hn, u, hu, rfl⟩ := exists_of_mem_sylS hs
  obtain ⟨k, hk, j, hj, i, hi, rfl⟩ := exists_of_mem_baseA hu
  exact ⟨n, hn, k, hk, j, hj, i, hi, rfl⟩

private theorem orderOf_gens :
    orderOf ga = 3 ∧ orderOf gb = 3 ∧ orderOf gc = 3 ∧ orderOf gx = 3 := by
  obtain ⟨ha, hb, hc, hx⟩ := gens_pow_three
  refine ⟨orderOf_eq_prime ha ga_ne_one, orderOf_eq_prime hb ?_, orderOf_eq_prime hc ?_,
    orderOf_eq_prime hx ?_⟩
  · simpa using gb_ne_pow 0 (by norm_num)
  · simpa using gc_ne_mul 0 (by norm_num) 0 (by norm_num)
  · simpa using gx_ne_mul 0 (by norm_num) 0 (by norm_num) 0 (by norm_num)

private theorem card_baseA : Nat.card baseA = 27 := by
  have hb : gb ∉ zpowers ga := fun h => by
    obtain ⟨i, hi, e⟩ := exists_pow_of_mem gens_pow_three.1 h
    exact gb_ne_pow i hi e
  have hc : gc ∉ zpowers ga ⊔ zpowers gb := fun h => by
    obtain ⟨j, hj, i, hi, e⟩ := exists_of_mem_ab h
    exact gc_ne_mul j hj i hi e
  have h := card_sup_zpowers orderOf_gens.2.2.1 hc (conj_mem_of_comm comm_ab_c)
  rw [card_sup_zpowers orderOf_gens.2.1 hb (conj_mem_of_comm comm_a_b), Nat.card_zpowers,
    orderOf_gens.1] at h
  exact h

theorem card_sylS : Nat.card sylS = 81 := by
  have hx : gx ∉ baseA := fun h => by
    obtain ⟨k, hk, j, hj, i, hi, e⟩ := exists_of_mem_baseA h
    exact gx_ne_mul k hk j hj i hi e
  have h := card_sup_zpowers orderOf_gens.2.2.2 hx gx_conj_mem
  rw [card_baseA] at h
  exact h

private theorem eq_baseA {D : Subgroup (GL (Fin 8) (ZMod 3))} (hDS : D ≤ sylS)
    (hD : ∀ d ∈ D, ∀ d' ∈ D, d * d' = d' * d) (h27 : 27 ≤ Nat.card D) : D = baseA := by
  refine eq_of_le_of_card_ge ?_ (by rw [card_baseA]; exact h27)
  by_contra hDA
  obtain ⟨y, hyD, hyA⟩ := SetLike.not_le_iff_exists.1 hDA
  obtain ⟨n, hn, u, hu, rfl⟩ := exists_of_mem_sylS (hDS hyD)
  have hn0 : n ≠ 0 := by rintro rfl; rw [pow_zero, one_mul] at hyA; exact hyA hu
  have hcap : baseA ⊓ D ≤ zpowers gb := by
    rintro s ⟨hsA, hsD⟩
    have hsx : s * gx ^ n = gx ^ n * s := mul_right_cancel (b := u) (by
      calc s * gx ^ n * u = s * (gx ^ n * u) := mul_assoc _ _ _
        _ = gx ^ n * u * s := hD s hsD _ hyD
        _ = gx ^ n * (s * u) := by rw [mul_assoc, baseA_comm hu hsA]
        _ = gx ^ n * s * u := (mul_assoc _ _ _).symm)
    have hsx1 : s * gx = gx * s := by
      interval_cases n
      · exact absurd rfl hn0
      · simpa using hsx
      · rw [← gx_inv] at hsx; exact Commute.inv_right_iff.1 hsx
    obtain ⟨k, hk, j, hj, i, hi, rfl⟩ := exists_of_mem_baseA hsA
    obtain ⟨rfl, rfl⟩ := eq_zero_of_comm_gx k hk j hj i hi hsx1
    rw [pow_zero, pow_zero, one_mul, mul_one]
    exact pow_mem (mem_zpowers gb) j
  have h1 : Nat.card ↥(baseA ⊓ D) ≤ 3 :=
    (card_le_of_le hcap).trans_eq (by rw [Nat.card_zpowers, orderOf_gens.2.1])
  have hidx : baseA.relIndex sylS = 3 := by
    have hle : baseA ≤ sylS := le_sup_left
    have h := relIndex_mul_card baseA sylS
    rw [inf_eq_left.2 hle, card_baseA, card_sylS] at h
    omega
  have h2 := relIndex_le_of_le_right (H := baseA) hDS (by rw [hidx]; norm_num)
  rw [hidx] at h2
  have h3 := relIndex_mul_card baseA D
  have h9 : Nat.card D ≤ 3 * 3 := by rw [← h3]; exact Nat.mul_le_mul h2 h1
  omega

theorem gens_mem_of_le_sylS {D : Subgroup (GL (Fin 8) (ZMod 3))} (hDS : D ≤ sylS)
    (hD : ∀ d ∈ D, ∀ d' ∈ D, d * d' = d' * d) (h27 : 27 ≤ Nat.card D) :
    ga ∈ D ∧ gb ∈ D ∧ gc ∈ D ∧ Nat.card D = 27 := by
  rw [eq_baseA hDS hD h27]
  exact ⟨mem_baseA.1, mem_baseA.2.1, mem_baseA.2.2, card_baseA⟩

private def isoG : Subgroup (GL (Fin 8) (ZMod 3)) where
  carrier := {g | ∀ u v : Fin 8 → ZMod 3, (u ᵥ* (g : Matrix (Fin 8) (Fin 8) (ZMod 3))) ⬝ᵥ
    (MThree *ᵥ (v ᵥ* (g : Matrix (Fin 8) (Fin 8) (ZMod 3)))) = u ⬝ᵥ (MThree *ᵥ v)}
  mul_mem' {g h} hg hh u v := by
    rw [Units.val_mul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
    exact (hh _ _).trans (hg u v)
  one_mem' u v := by rw [Units.val_one, Matrix.vecMul_one, Matrix.vecMul_one]
  inv_mem' {g} hg u v := by
    have h := hg (u ᵥ* ((g⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)))
      (v ᵥ* ((g⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)))
    simp only [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.vecMul_one] at h
    exact h.symm

private theorem sylS_le_isoG : sylS ≤ isoG := by
  have h : ∀ s, (s = ga ∨ s = gb ∨ s = gc ∨ s = gx) → zpowers s ≤ isoG := fun s hs =>
    zpowers_le.2 fun u v => isometry_gens hs u v
  exact sup_le (sup_le (sup_le (h _ (Or.inl rfl)) (h _ (Or.inr (Or.inl rfl))))
    (h _ (Or.inr (Or.inr (Or.inl rfl))))) (h _ (Or.inr (Or.inr (Or.inr rfl))))

theorem isometry_of_mem_sylS {s : GL (Fin 8) (ZMod 3)} (hs : s ∈ sylS) (u v : Fin 8 → ZMod 3) :
    (u ᵥ* (s : Matrix (Fin 8) (Fin 8) (ZMod 3))) ⬝ᵥ
      (MThree *ᵥ (v ᵥ* (s : Matrix (Fin 8) (Fin 8) (ZMod 3)))) = u ⬝ᵥ (MThree *ᵥ v) :=
  sylS_le_isoG hs u v

end CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3.BabySyl

end
