module

public import CFSG.CGT.Timmesfeld75.Sec78Dihedral
public import CFSG.CGT.Timmesfeld75.Sec77R1
public import CFSG.CGT.Timmesfeld75.Sec78Core

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups Matrix commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

section Kernel

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

theorem indep_of_ker_ne {f f' : Module.Dual F V} (hf : f ≠ 0) (hf' : f' ≠ 0)
    (hne : ¬ ∀ w, f w = 0 ↔ f' w = 0) : ∀ r t : F, r • f + t • f' = 0 → r = 0 ∧ t = 0 := by
  intro r t h
  by_contra hrt
  apply hne
  have hr : r ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_add] at h
    rcases (smul_eq_zero.1 h) with h0 | h0
    · exact hrt ⟨rfl, h0⟩
    · exact hf' h0
  have ht : t ≠ 0 := by
    rintro rfl
    rw [zero_smul, add_zero] at h
    rcases (smul_eq_zero.1 h) with h0 | h0
    · exact hr h0
    · exact hf h0
  intro w
  have hw : r * f w + t * f' w = 0 := by
    have := congrArg (fun φ : Module.Dual F V => φ w) h
    simpa using this
  constructor
  · intro h0
    rw [h0, mul_zero, zero_add] at hw
    exact (mul_eq_zero.1 hw).resolve_left ht
  · intro h0
    rw [h0, mul_zero, add_zero] at hw
    exact (mul_eq_zero.1 hw).resolve_left hr

end Kernel

section U

variable [(T.subgroupOf (hSub T (normIn T₁ T))).Normal]

theorem Sec6Ctx.exists_u78 (h66 : Sec66) (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ n m) (hnat : NaturalSL T (hSub T (normIn T₁ T)) n m) (hn4 : 4 ≤ n)
    (hA8 : ¬ (n = 4 ∧ m = 1)) (M : TModel T T₁ n m) {x z y : G} {k : ℕ}
    (h : BadConfig78 T x z y k) :
    ∃ (u : G) (fz g : Module.Dual (GaloisField 2 m) (Fin n → GaloisField 2 m))
      (vz : Fin n → GaloisField 2 m), u ∈ normD T ∧ u ∉ T ∧ u * x = x * u ∧ u * z = z * u ∧
      u * z ∈ classD T ∧ vz ≠ 0 ∧ fz ≠ 0 ∧ g ≠ 0 ∧ fz vz = 0 ∧ g vz = 0 ∧
      (∀ w, sact (ubar M.ε z) w = w + fz w • vz) ∧ (∀ w, sact (ubar M.ε u) w = w + g w • vz) ∧
      (∀ r t : GaloisField 2 m, r • g + t • fz = 0 → r = 0 ∧ t = 0) ∧
      (∀ r t : GaloisField 2 m, r • fz + t • g = 0 → r = 0 ∧ t = 0) := by
  have hn3 : 3 ≤ n := by omega
  obtain ⟨fz, vz, hfzv, hvz, hfz0, hdz⟩ := M.exists_data h.zN h.zT
  obtain ⟨ξ, hξ⟩ : ∃ ξ : Fin n → GaloisField 2 m, ξ = Multiplicative.toAdd (M.φ ⟨x, h.xT⟩) :=
    ⟨_, rfl⟩
  have hfξ : fz ξ = 0 := by
    rw [hξ]
    exact (M.comm_iff_data h.zN hvz hdz h.xT).1 h.xz.symm
  have hxv : ∀ r : GaloisField 2 m, ξ ≠ r • vz := by
    intro r hr
    apply h.xzD
    have hmem := (hc.mem_classD_mul_iff h62 h63 M h.zN h.zT hfz0 hdz h.xT).2
      ⟨r, by rw [← hξ]; exact hr⟩
    rw [h.xz]
    exact hmem
  have hvξ : ∀ r s : GaloisField 2 m, r • vz + s • ξ = 0 → r = 0 ∧ s = 0 := by
    intro r s hrs
    by_cases hs : s = 0
    · subst hs
      rw [zero_smul, add_zero] at hrs
      exact ⟨(smul_eq_zero.1 hrs).resolve_right hvz, rfl⟩
    · exfalso
      apply hxv (-(s⁻¹ * r))
      have h6 : s • ξ = -(r • vz) := eq_neg_of_add_eq_zero_right hrs
      calc ξ = s⁻¹ • (s • ξ) := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
        _ = s⁻¹ • (-(r • vz)) := by rw [h6]
        _ = (-(s⁻¹ * r)) • vz := by rw [smul_neg, smul_smul]; exact (neg_smul _ _).symm
  obtain ⟨g, hgv, hgξ, hgind⟩ := exists_dual_indep_two hfz0 hfzv hfξ hvξ hn4
  have hg0 : g ≠ 0 := by
    intro h0
    have := hgind 0 1 (by rw [h0]; simp)
    exact one_ne_zero this.2
  obtain ⟨u₀, hu₀tr, hu₀⟩ := exists_sl_transvection hgv hg0 hvz
  obtain ⟨u, hu, huT, hub⟩ := hc.exists_lift M hu₀tr
  have hdu : ∀ w, sact (ubar M.ε u) w = w + g w • vz := by
    intro w
    rw [hub]
    exact hu₀ w
  have hux : u * x = x * u :=
    (M.comm_iff_data hu hvz hdu h.xT).2 (by rw [← hξ]; exact hgξ)
  have hcomm : ubar M.ε u * ubar M.ε z = ubar M.ε z * ubar M.ε u :=
    mul_comm_of_data hgv hfzv hdu hdz
  have huz : u * z = z * u :=
    hc.comm_of_ubar_comm h66 h1 h62 h63 hnat hn3 hA8 M hu huT h.zN h.zT hcomm
  have hind' : ∀ r t : GaloisField 2 m, r • g + t • fz = 0 → r = 0 ∧ t = 0 := by
    intro r t hrt
    have := hgind t r (by rw [add_comm]; exact hrt)
    exact ⟨this.2, this.1⟩
  have huzD : u * z ∈ classD T :=
    hc.mul_mem_classD_of_data h66 h62 h63 M hu h.zN h.zT huz hvz hgv hfzv hind' hdu hdz
  exact ⟨u, fz, g, vz, hu, huT, hux, huz, huzD, hvz, hfz0, hg0, hfzv, hgv, hdz, hdu, hind', hgind⟩

end U

end CFSG.CGT.Timmesfeld75
