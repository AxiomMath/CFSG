module

public import CFSG.ClassicalInvolution.Phan.PhanB2Family
public import CFSG.ClassicalInvolution.Phan.PhanD5Mat

public section

namespace CFSG.ClassicalInvolution.PhanB3

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalInvolution.PhanD4 (exists_normOne_sq_ne_one mem_range_torusTwo_of_commute
  exists_embSUid_torus_of_commute exists_scalar_decomp eq_one_of_conjDiag_weyl weylSU negOne
  negOne_ne_one conjDiag_one)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {hK : Nat.card K = (p ^ f) ^ 2} {F : Type} [Field F] {h2 : (2 : F) ≠ 0}
  {C : B2Coord hK F h2} {G : Type} [Group G]

structure GoodFamily (S : PhanFamilyB3 C G) : Prop where
  inj : ∀ i, Function.Injective (S.ι i)
  disj : ∀ i j, i ≠ j → (S.ι i).range ⊓ (S.ι j).range = ⊥
  kerθ : S.θ.ker ≤ Subgroup.center (Su K p f 3)
  kerϑ : S.ϑ.ker ≤ Subgroup.center (StatedSp 2 F)

section Cartan

theorem cartan_B3 {N : Type*} [CommGroup N] {t0 t1 t2 : N} (r0 : t0 * t0 * t1⁻¹ = 1)
    (r1 : t0⁻¹ * (t1 * t1) * (t2⁻¹ * t2⁻¹) = 1) (r2 : t1⁻¹ * (t2 * t2) = 1) :
    t0 = 1 ∧ t1 = 1 ∧ t2 * t2 = 1 := by
  have e0 : t1 = t0 * t0 := (mul_inv_eq_one.mp r0).symm
  have e2 : t2 * t2 = t1 := (inv_mul_eq_one.mp r2).symm
  have e1 : t0⁻¹ * t1 = 1 := by
    have h : t2⁻¹ * t2⁻¹ = (t1)⁻¹ := by rw [← e2, mul_inv]
    rw [h] at r1
    simpa [mul_assoc] using r1
  have h01 : t0 = t1 := (inv_mul_eq_one.mp e1)
  have h0 : t0 = 1 := by
    have : t0 * t0 = t0 * 1 := by rw [mul_one, ← e0, ← h01]
    exact mul_left_cancel this
  have h1 : t1 = 1 := by rw [← h01, h0]
  exact ⟨h0, h1, by rw [e2, h1]⟩

end Cartan

section Good

variable {S : PhanFamilyB3 C G}

theorem rho_zero (t : Fin 3 → normOne (unitaryInvolution K p f)) :
    rho 0 t = t 0 * t 0 * (t 1)⁻¹ := by
  rw [rho, chi_self, chi_one_zero, chi_two_zero, mul_one]

theorem rho_one (t : Fin 3 → normOne (unitaryInvolution K p f)) :
    rho 1 t = (t 0)⁻¹ * (t 1 * t 1) * ((t 2)⁻¹ * (t 2)⁻¹) := by
  rw [rho, chi_zero_one, chi_self, chi_two_one]

theorem rho_two (t : Fin 3 → normOne (unitaryInvolution K p f)) :
    rho 2 t = (t 1)⁻¹ * (t 2 * t 2) := by
  rw [rho, chi_zero_two, chi_one_two, chi_self, one_mul]

theorem GoodFamily.θ_injective (hg : GoodFamily S) : Function.Injective S.θ := by
  rw [injective_iff_map_eq_one]
  intro z hz
  obtain ⟨u, rfl⟩ := exists_scalar_decomp hK (hg.kerθ hz)
  rw [map_mul, ← ι_zero, ← ι_one_θ] at hz
  have h1 : S.ι 0 (torusTwo (unitaryInvolution K p f) u) =
      S.ι 1 (torusTwo (unitaryInvolution K p f) u) := by
    have := mul_eq_one_iff_eq_inv.mp hz
    rw [this, ← map_inv, ← map_inv, inv_inv]
  have hmem : S.ι 0 (torusTwo (unitaryInvolution K p f) u) ∈ (S.ι 0).range ⊓ (S.ι 1).range :=
    ⟨⟨_, rfl⟩, h1 ▸ ⟨_, rfl⟩⟩
  rw [hg.disj 0 1 (by decide), Subgroup.mem_bot] at hmem
  have hu : u = 1 := torusTwo_injective _ (by
    rw [map_one]
    exact hg.inj 0 (by rw [hmem, map_one]))
  subst hu
  simp

theorem GoodFamily.ϑ_injective (hg : GoodFamily S) : Function.Injective S.ϑ := by
  rw [injective_iff_map_eq_one]
  intro z hz
  obtain ⟨u, rfl⟩ := C.center_le z (hg.kerϑ hz)
  have : S.ι 2 u = 1 := by rw [ι_two]; exact hz
  rw [hg.inj 2 (this.trans (map_one _).symm), map_one]

theorem GoodFamily.tor_two_negOne_ne_one (hg : GoodFamily S) (h2K : (2 : K) ≠ 0) :
    tor S 2 (negOne (unitaryInvolution K p f)) ≠ 1 := by
  intro h
  have h' : torusTwo (unitaryInvolution K p f) (negOne (unitaryInvolution K p f)) = 1 :=
    hg.inj 2 (by simpa [tor] using h.trans (map_one (S.ι 2)).symm)
  exact negOne_ne_one _ h2K (torusTwo_injective _ (by rw [h', map_one]))

include hK in
theorem GoodFamily.mTor_injective (hg : GoodFamily S) (h2K : (2 : K) ≠ 0) :
    Function.Injective (mTor S) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  have hrho : ∀ j, rho j t = 1 := by
    intro j
    refine eq_one_of_conjDiag_weyl hK (hg.inj j ?_)
    rw [← mTor_conj_ι (hK := hK) S t j, ht, one_mul, inv_one, mul_one]
  have r0 := hrho 0
  have r1 := hrho 1
  have r2 := hrho 2
  rw [rho_zero] at r0
  rw [rho_one] at r1
  rw [rho_two] at r2
  obtain ⟨h0, h1, h22⟩ := cartan_B3 r0 r1 r2
  have h2' : t 2 = 1 ∨ t 2 = negOne (unitaryInvolution K p f) := by
    have e := congrArg (fun u : normOne (unitaryInvolution K p f) => (((u : normOne _) : Kˣ) : K))
      h22
    simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one] at e
    rcases mul_self_eq_one_iff.mp e with h | h
    · exact Or.inl (Subtype.ext (Units.ext (by simpa using h)))
    · exact Or.inr (Subtype.ext (Units.ext (by simpa [negOne] using h)))
  have hsplit := mTor_apply S t
  rw [ht, h0, h1, map_one, map_one, one_mul, one_mul] at hsplit
  rcases h2' with h | h
  · funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h
  · rw [h] at hsplit
    exact absurd hsplit.symm (hg.tor_two_negOne_ne_one h2K)

end Good

end CFSG.ClassicalInvolution.PhanB3
