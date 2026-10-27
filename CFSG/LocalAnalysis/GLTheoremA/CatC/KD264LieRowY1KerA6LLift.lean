module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4Lift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA6L

open Matrix CFSG.LocalAnalysis.GLTheoremA.KD264LieA4

variable {K : Type} [Field K]

@[expose] def piSL6 (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin 6) K →* Matrix.ProjectiveSpecialLinearGroup (Fin 6) K :=
  QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) K))

theorem center_pow_six {x : Matrix.SpecialLinearGroup (Fin 6) K}
    (hx : x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) K)) : x ^ 6 = 1 := by
  obtain ⟨r, hr6, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
  have hr : r ^ 6 = 1 := by simpa using hr6
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrx, ← map_pow, hr, map_one,
    Matrix.SpecialLinearGroup.coe_one]

theorem central_eq_one_of_pow_three (hnr : ∀ r : K, r ^ 2 + r + 1 ≠ 0)
    {x : Matrix.SpecialLinearGroup (Fin 6) K}
    (hx : x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) K)) (h3 : x ^ 3 = 1) :
    x = 1 := by
  obtain ⟨r, -, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
  have hM : (Matrix.scalar (Fin 6) r) ^ 3 = 1 := by
    rw [hrx, ← Matrix.SpecialLinearGroup.coe_pow, h3, Matrix.SpecialLinearGroup.coe_one]
  rw [← map_pow] at hM
  have hr3 : r ^ 3 = 1 := by
    have h := congrFun (congrFun hM 0) 0
    simpa [Matrix.scalar_apply] using h
  have hr1 : r = 1 := by
    have hfac : (r - 1) * (r ^ 2 + r + 1) = 0 := by linear_combination hr3
    rcases mul_eq_zero.mp hfac with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h (hnr r)
  apply Subtype.ext
  rw [← hrx, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem lift_of_elemAbelian6 [Finite K] (hnr : ∀ r : K, r ^ 2 + r + 1 ≠ 0)
    {E : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 6) K)}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hc : Nat.card E = 27) :
    ∃ P : Subgroup (Matrix.SpecialLinearGroup (Fin 6) K), P.map (piSL6 K) = E ∧
      (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧ (∀ x ∈ P, x ^ 3 = 1) ∧ Nat.card P = 27 := by
  let E' : Subgroup (Matrix.SpecialLinearGroup (Fin 6) K) := E.comap (piSL6 K)
  let ρ : E' →* E := ((piSL6 K).comp E'.subtype).codRestrict E (fun x => x.2)
  have hρ : Function.Surjective ρ := by
    intro e
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective
      (e : Matrix.ProjectiveSpecialLinearGroup (Fin 6) K)
    refine ⟨⟨x, ?_⟩, ?_⟩
    · show piSL6 K x ∈ E
      have hx' : piSL6 K x = (e : Matrix.ProjectiveSpecialLinearGroup (Fin 6) K) := hx
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
  let P : Subgroup (Matrix.SpecialLinearGroup (Fin 6) K) := Q.map E'.subtype
  have hcardP : Nat.card P = 27 := by
    rw [show P = Q.map E'.subtype from rfl,
      Subgroup.card_map_of_injective (f := E'.subtype) (Subgroup.subtype_injective E'), hQ]
    norm_num
  have hPmem : ∀ x ∈ P, piSL6 K x ∈ E := by
    intro x hx
    obtain ⟨q, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact q.2
  have hinj : ∀ x ∈ P, piSL6 K x = 1 → x = 1 := by
    intro x hx h
    have hxc : x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) K) :=
      (QuotientGroup.eq_one_iff x).mp h
    have h6 : x ^ 6 = 1 := center_pow_six hxc
    have hx27 : x ^ 27 = 1 := by
      have h := pow_card_eq_one' (G := P) (x := ⟨x, hx⟩)
      have h' := congrArg Subtype.val h
      rw [hcardP] at h'
      simpa using h'
    have hg : x ^ (Nat.gcd 27 6) = 1 := pow_gcd_eq_one.mpr ⟨hx27, h6⟩
    have hg3 : Nat.gcd 27 6 = 3 := by norm_num
    rw [hg3] at hg
    exact central_eq_one_of_pow_three hnr hxc hg
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    have h1 : piSL6 K (x * y) = piSL6 K (y * x) := by
      rw [map_mul, map_mul]
      have h2 := congrArg Subtype.val
        (hE.1.is_comm.comm ⟨piSL6 K x, hPmem x hx⟩ ⟨piSL6 K y, hPmem y hy⟩)
      simpa using h2
    have hmem : (y * x)⁻¹ * (x * y) ∈ P :=
      mul_mem (inv_mem (mul_mem hy hx)) (mul_mem hx hy)
    have hpi : piSL6 K ((y * x)⁻¹ * (x * y)) = 1 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    exact (inv_mul_eq_one.mp (hinj _ hmem hpi)).symm
  have hpow : ∀ x ∈ P, x ^ 3 = 1 := by
    intro x hx
    apply hinj (x ^ 3) (pow_mem hx 3)
    rw [map_pow]
    exact hE.2 _ (hPmem x hx)
  have hmapE : P.map (piSL6 K) = E := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact hPmem x hx
    · rw [card_map_eq_of_injOn (piSL6 K) P hinj, hcardP, hc]
  exact ⟨P, hmapE, hcomm, hpow, hcardP⟩

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA6L

end
