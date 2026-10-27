module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerU7Kern

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KU7

open Matrix Finset CFSG.Open CFSG.LocalAnalysis.ComponentInitial

open scoped Classical

variable {p f : ℕ} {K : Type} [Field K]

theorem scalar_seven_eq_one {x : GL (Fin 7) K} (hx : x ∈ StatedScalars (Fin 7) K)
    (hdet : (x : Matrix (Fin 7) (Fin 7) K).det = 1) : x ^ 7 = 1 := by
  obtain ⟨c, rfl⟩ := MonoidHom.mem_range.mp hx
  have hc7 : (c : K) ^ 7 = 1 := by
    rw [scalar_val, Matrix.scalar_apply, Matrix.det_diagonal] at hdet
    simpa using hdet
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, scalar_val, ← map_pow, hc7, map_one, Units.val_one]

theorem seven_of_piU (h : UnitaryFieldData p f K) {x : ↥(StatedSU 7 (p ^ f) K)}
    (hx : piU p f K x = 1) : x ^ 7 = 1 := by
  rw [piU_eq_one_iff] at hx
  have hdet := ((mem_statedSU_iff h 7 (x : GL (Fin 7) K)).mp x.2).1
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact scalar_seven_eq_one hx hdet

theorem lift_of_elemAbelianU (h : UnitaryFieldData p f K)
    {E : Subgroup (StatedProj (StatedSU 7 (p ^ f) K))}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hc : Nat.card E = 27) :
    ∃ P : Subgroup ↥(StatedSU 7 (p ^ f) K), P.map (piU p f K) = E ∧
      (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧ (∀ x ∈ P, x ^ 3 = 1) ∧ Nat.card P = 27 := by
  haveI : Finite K := h.finite
  let E' : Subgroup ↥(StatedSU 7 (p ^ f) K) := E.comap (piU p f K)
  let ρ : E' →* E := ((piU p f K).comp E'.subtype).codRestrict E (fun x => x.2)
  have hρ : Function.Surjective ρ := by
    intro e
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e : StatedProj (StatedSU 7 (p ^ f) K))
    refine ⟨⟨x, ?_⟩, ?_⟩
    · show piU p f K x ∈ E
      have hx' : piU p f K x = (e : StatedProj (StatedSU 7 (p ^ f) K)) := hx
      rw [hx']
      exact e.2
    · apply Subtype.ext
      exact hx
  have h27 : 3 ^ 3 ∣ Nat.card E' := by
    have hq := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).toEquiv
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker, hq, hc]
    norm_num
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := E') 3 h27
  let P : Subgroup ↥(StatedSU 7 (p ^ f) K) := Q.map E'.subtype
  have hcardP : Nat.card P = 27 := by
    rw [show P = Q.map E'.subtype from rfl,
      Subgroup.card_map_of_injective (f := E'.subtype) (Subgroup.subtype_injective E'), hQ]
    norm_num
  have hPmem : ∀ x ∈ P, piU p f K x ∈ E := by
    intro x hx
    obtain ⟨q, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact q.2
  have hinj : ∀ x ∈ P, piU p f K x = 1 → x = 1 := by
    intro x hx hpx
    have h7 : x ^ 7 = 1 := seven_of_piU h hpx
    have hx27 : x ^ 27 = 1 := by
      have h := pow_card_eq_one' (G := P) (x := ⟨x, hx⟩)
      have h' := congrArg Subtype.val h
      rw [hcardP] at h'
      simpa using h'
    have hg : x ^ (Nat.gcd 27 7) = 1 := pow_gcd_eq_one.mpr ⟨hx27, h7⟩
    have hg1 : Nat.gcd 27 7 = 1 := by norm_num
    rw [hg1, pow_one] at hg
    exact hg
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    have h1 : piU p f K (x * y) = piU p f K (y * x) := by
      rw [map_mul, map_mul]
      have h2 := congrArg Subtype.val
        (hE.1.is_comm.comm ⟨piU p f K x, hPmem x hx⟩ ⟨piU p f K y, hPmem y hy⟩)
      simpa using h2
    have hmem : (y * x)⁻¹ * (x * y) ∈ P :=
      mul_mem (inv_mem (mul_mem hy hx)) (mul_mem hx hy)
    have hpi : piU p f K ((y * x)⁻¹ * (x * y)) = 1 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    exact (inv_mul_eq_one.mp (hinj _ hmem hpi)).symm
  have hpow : ∀ x ∈ P, x ^ 3 = 1 := by
    intro x hx
    apply hinj (x ^ 3) (pow_mem hx 3)
    rw [map_pow]
    exact hE.2 _ (hPmem x hx)
  have hmapE : P.map (piU p f K) = E := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact hPmem x hx
    · rw [card_map_eq_of_injOn (piU p f K) P hinj, hcardP, hc]
  exact ⟨P, hmapE, hcomm, hpow, hcardP⟩

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KU7

end
