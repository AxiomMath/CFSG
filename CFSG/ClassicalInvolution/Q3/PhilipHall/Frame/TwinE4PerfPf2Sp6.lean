module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4PerfPf2Sp6Data

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4Sp6

open CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.TL4.E4Sp6

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier.Co3
open CFSG.ComponentClassification.M12Cover CFSG.EvenSmallLie.Sp6
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Q3.TL4.E4C CFSG.ClassicalInvolution.Q3.TL4.E4Sp6Data


theorem acts3_ambient {K : Subgroup (Equiv.Perm (Fin 36))} {s : Equiv.Perm (Fin 36)}
    (hd : Vtx.AmbientQuatDatum co3X36 K s) :
    ∃ y ∈ co3X36, y * s = s * y ∧ y ^ 3 = 1 ∧ (∀ k ∈ K, y * k * y⁻¹ ∈ K) ∧
      ∃ k ∈ K, y * k * y⁻¹ * k⁻¹ ≠ 1 ∧ y * k * y⁻¹ * k⁻¹ ≠ s := by
  obtain ⟨g, hg, hgK⟩ := ident_ambient hd
  have hx3 : x3 () ∈ co3X36 := by
    show tab (evalCodes sp6Gens x3Word) ∈ co3X36
    rw [tab_eq, ← sp6Q_originalSubgroup]
    exact evalCodes_mem _ sp6Gens_mem _
  have hkmem : ∀ k ∈ K, g * k * g⁻¹ ∈ L0 () := fun k hk => by
    rw [← mem_K0_iff, ← hgK]
    exact conj_mem_conjSub hk
  have hback : ∀ y ∈ L0 (), g⁻¹ * y * g ∈ K := fun y hy => by
    have : y ∈ conjSub g K := by rw [hgK, mem_K0_iff]; exact hy
    rwa [mem_conjSub_iff] at this
  have hs' : g * s * g⁻¹ = tab sp6Rep2 := by
    have h1 := hkmem s hd.inv.mem
    have h2 : g * s * g⁻¹ * (g * s * g⁻¹) = 1 := by
      calc g * s * g⁻¹ * (g * s * g⁻¹) = g * (s * s) * g⁻¹ := by group
        _ = 1 := by rw [hd.inv.sq]; group
    rcases L0_inv _ h1 h2 with h3 | h3
    · exfalso
      apply hd.inv.ne_one
      calc s = g⁻¹ * (g * s * g⁻¹) * g := by group
        _ = 1 := by rw [h3]; group
    · exact h3
  have hρ : rho () ∈ L0 () := by simp [L0, q8Elems]
  refine ⟨g⁻¹ * x3 () * g, co3X36.mul_mem (co3X36.mul_mem (co3X36.inv_mem hg) hx3) hg, ?_, ?_, ?_,
    g⁻¹ * rho () * g, hback _ hρ, ?_, ?_⟩
  · calc g⁻¹ * x3 () * g * s = g⁻¹ * (x3 () * (g * s * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * s * g⁻¹) * x3 ()) * g := by rw [hs', x3_cent]
      _ = s * (g⁻¹ * x3 () * g) := by group
  · have : (g⁻¹ * x3 () * g) ^ 3 = g⁻¹ * (x3 () * x3 () * x3 ()) * g := by
      rw [pow_three']; group
    rw [this, x3_cube]; group
  · intro k hk
    have e1 : g⁻¹ * x3 () * g * k * (g⁻¹ * x3 () * g)⁻¹ =
        g⁻¹ * (x3 () * (g * k * g⁻¹) * (x3 ())⁻¹) * g := by group
    rw [e1]
    exact hback _ (x3_norm _ (hkmem k hk))
  · intro h1
    apply x3_act.1
    have e1 : g⁻¹ * x3 () * g * (g⁻¹ * rho () * g) * (g⁻¹ * x3 () * g)⁻¹ * (g⁻¹ * rho () * g)⁻¹ =
        g⁻¹ * (x3 () * rho () * (x3 ())⁻¹ * (rho ())⁻¹) * g := by group
    rw [e1] at h1
    calc x3 () * rho () * (x3 ())⁻¹ * (rho ())⁻¹
        = g * (g⁻¹ * (x3 () * rho () * (x3 ())⁻¹ * (rho ())⁻¹) * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · intro h1
    apply x3_act.2
    have e1 : g⁻¹ * x3 () * g * (g⁻¹ * rho () * g) * (g⁻¹ * x3 () * g)⁻¹ * (g⁻¹ * rho () * g)⁻¹ =
        g⁻¹ * (x3 () * rho () * (x3 ())⁻¹ * (rho ())⁻¹) * g := by group
    rw [e1] at h1
    calc x3 () * rho () * (x3 ())⁻¹ * (rho ())⁻¹
        = g * (g⁻¹ * (x3 () * rho () * (x3 ())⁻¹ * (rho ())⁻¹) * g) * g⁻¹ := by group
      _ = g * s * g⁻¹ := by rw [h1]
      _ = tab sp6Rep2 := hs'

section Model

variable {M : Type} [Group M] [Finite M]

omit [Finite M] in
theorem acts3_PSp (hM : CFSG.Blueprint.LieModel M .PSp 3 2 1) {R : Subgroup M} {t : M}
    (hq8 : Nonempty (↥R ≃* QuaternionGroup 2)) (hinv : IsUniqueInvolution R t)
    (htw : ∀ c ∈ Subgroup.centralizer ({t} : Set M), conjSub c R = R ∨
      ∀ x ∈ R, ∀ y ∈ conjSub c R, x * y = y * x) :
    ∃ x : M, x * t = t * x ∧ x ^ 3 = 1 ∧ (∀ r ∈ R, x * r * x⁻¹ ∈ R) ∧
      ∃ r ∈ R, x * r * x⁻¹ * r⁻¹ ≠ 1 ∧ x * r * x⁻¹ * r⁻¹ ≠ t := by
  obtain ⟨e⟩ := nonempty_mulEquiv_co3X36 hM
  have hinj := emb_injective e
  obtain ⟨eR⟩ := hq8
  have hd : Vtx.AmbientQuatDatum co3X36 (R.map (emb e)) (emb e t) := by
    rw [← range_emb e]
    refine ⟨Subgroup.map_le_range _ R, ⟨(R.equivMapOfInjective _ hinj).symm.trans eR⟩,
      Vtx.isUniqueInvolution_map _ hinj hinv, ?_⟩
    rintro _ ⟨m, rfl⟩ hms
    have hm : m ∈ Subgroup.centralizer ({t} : Set M) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hinj (by rw [map_mul, map_mul, hms])
    rw [conjSub_map]
    rcases htw m hm with h | h
    · left
      rw [h]
    · right
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, h x hx y hy]
  obtain ⟨y, hy, hys, hy3, hyK, k, hk, hk1, hk2⟩ := acts3_ambient hd
  obtain ⟨m, hm⟩ : ∃ m : M, emb e m = y := by
    rw [← range_emb e] at hy
    exact hy
  subst hm
  refine ⟨m, hinj (by rw [map_mul, map_mul]; exact hys), hinj (by rw [map_pow, hy3, map_one]), ?_, ?_⟩
  · intro r hr
    obtain ⟨r', hr', hr'e⟩ := hyK _ (Subgroup.mem_map_of_mem (emb e) hr)
    have : m * r * m⁻¹ = r' := hinj (by rw [map_mul, map_mul, map_inv, hr'e])
    rw [this]
    exact hr'
  · obtain ⟨r, hr, rfl⟩ := hk
    refine ⟨r, hr, fun h => hk1 ?_, fun h => hk2 ?_⟩
    · rw [← map_one (emb e), ← h]; simp [map_mul, map_inv]
    · rw [← h]; simp [map_mul, map_inv]

end Model

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4Sp6
