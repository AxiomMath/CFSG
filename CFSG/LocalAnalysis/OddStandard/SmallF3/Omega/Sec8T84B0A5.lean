module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B0A5Eq
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPConj

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace T84Co

open Matrix Certificates.Asc82NormA6 CFSG.Quasithin.L34Amalgam CFSG.CosetTable

@[expose] def pa : Equiv.Perm (Fin 6) := Equiv.swap 2 3 * Equiv.swap 4 5

@[expose] def pb : Equiv.Perm (Fin 6) :=
  (Equiv.swap 0 1 * Equiv.swap 1 2) * (Equiv.swap 3 4 * Equiv.swap 4 5)

theorem pa_sign : pa.sign = 1 := by decide +kernel

theorem pb_sign : pb.sign = 1 := by decide +kernel

theorem pa_sq : pa * pa = 1 := by decide +kernel

theorem pb_cube : pb ^ 3 = 1 := by decide +kernel

theorem pab_pow : (pa * pb) ^ 5 = 1 := by decide +kernel

theorem pa_ne : pa ≠ 1 := by decide +kernel

@[expose] def a6a : alternatingGroup (Fin 6) :=
  ⟨pa, Equiv.Perm.mem_alternatingGroup.mpr pa_sign⟩

@[expose] def a6b : alternatingGroup (Fin 6) :=
  ⟨pb, Equiv.Perm.mem_alternatingGroup.mpr pb_sign⟩

theorem a6a_sq : a6a * a6a = 1 := Subtype.ext pa_sq

theorem a6b_cube : a6b ^ 3 = 1 :=
  Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact pb_cube)

theorem a6ab_pow : (a6a * a6b) ^ 5 = 1 :=
  Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one]; exact pab_pow)

theorem a6a_ne : a6a ≠ 1 := fun h => pa_ne (congrArg Subtype.val h)

@[expose] noncomputable def phi : PG 2 a5Rels →* alternatingGroup (Fin 6) :=
  a5Hom a6a_sq a6b_cube a6ab_pow

theorem phi_a : phi (PresentedGroup.of 0) = a6a := a5Hom_of a6a_sq a6b_cube a6ab_pow 0

theorem phi_b : phi (PresentedGroup.of 1) = a6b := a5Hom_of a6a_sq a6b_cube a6ab_pow 1

theorem phi_injective : Function.Injective phi := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  haveI : IsSimpleGroup (PG 2 a5Rels) := MulEquiv.isSimpleGroup a5RelsEquivAlt5
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases Subgroup.Normal.eq_bot_or_eq_top (MonoidHom.ker phi) with h | h
  · exact h
  · exfalso
    have h1 : PresentedGroup.of (0 : Fin 2) ∈ MonoidHom.ker phi := by rw [h]; trivial
    exact a6a_ne (by rw [← phi_a]; exact h1)

@[expose] def orbStep (l : List (Fin 4 → ZMod 2)) : List (Fin 4 → ZMod 2) :=
  l ++ l.map (fun v => rho pa *ᵥ v) ++ l.map (fun v => rho pb *ᵥ v)

theorem orb_all : ∀ u w : Fin 4 → ZMod 2, u ≠ 0 → w ≠ 0 → w ∈ orbStep^[6] [u] := by
  decide +kernel

theorem orb_reach (u : Fin 4 → ZMod 2) :
    ∀ (n : ℕ) (w : Fin 4 → ZMod 2), w ∈ orbStep^[n] [u] →
      ∃ g : PG 2 a5Rels,
        rho ((phi g : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) *ᵥ u = w := by
  intro n
  induction n with
  | zero =>
    intro w hw
    have h : w = u := by simpa using hw
    refine ⟨1, ?_⟩
    rw [h, map_one]
    show rho 1 *ᵥ u = u
    rw [Certificates.certificate442267.rho_one, Matrix.one_mulVec]
  | succ n ih =>
    intro w hw
    rw [Function.iterate_succ_apply'] at hw
    simp only [orbStep, List.mem_append, List.mem_map] at hw
    rcases hw with (hw | ⟨s, hs, rfl⟩) | ⟨s, hs, rfl⟩
    · exact ih w hw
    · obtain ⟨g, rfl⟩ := ih s hs
      refine ⟨PresentedGroup.of 0 * g, ?_⟩
      have h1 : ((phi (PresentedGroup.of 0 * g) : alternatingGroup (Fin 6)) :
          Equiv.Perm (Fin 6)) = pa * ((phi g : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) := by
        rw [map_mul, phi_a]
        rfl
      rw [h1, Certificates.certificate442267.rho_mul, Matrix.mulVec_mulVec]
    · obtain ⟨g, rfl⟩ := ih s hs
      refine ⟨PresentedGroup.of 1 * g, ?_⟩
      have h1 : ((phi (PresentedGroup.of 1 * g) : alternatingGroup (Fin 6)) :
          Equiv.Perm (Fin 6)) = pb * ((phi g : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) := by
        rw [map_mul, phi_b]
        rfl
      rw [h1, Certificates.certificate442267.rho_mul, Matrix.mulVec_mulVec]

theorem phi_transitive (u w : Fin 4 → ZMod 2) (hu : u ≠ 0)
    (hw : w ≠ 0) :
    ∃ g : PG 2 a5Rels, rho ((phi g : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) *ᵥ u = w :=
  orb_reach u 6 w (orb_all u w hu hw)

end T84Co

theorem sec8t84FactA5_of_cert :
    Sec8T84FactA5 := by
  intro G _ B hB H hH
  obtain ⟨e, ψ, hact, -⟩ := sec8t84_a6_conj B hB H hH
  let Φ : alternatingGroup (Fin 5) →* MulAut ↥B :=
    H.subtype.comp (ψ.symm.toMonoidHom.comp (T84Co.phi.comp T84Co.a5RelsEquivAlt5.symm.toMonoidHom))
  have hΦ : Function.Injective Φ := by
    intro g g' hg
    have h1 : ψ.symm (T84Co.phi (T84Co.a5RelsEquivAlt5.symm g)) =
        ψ.symm (T84Co.phi (T84Co.a5RelsEquivAlt5.symm g')) := Subtype.ext hg
    exact T84Co.a5RelsEquivAlt5.symm.injective (T84Co.phi_injective (ψ.symm.injective h1))
  refine ⟨Φ.range, ?_, ⟨(MonoidHom.ofInjective hΦ).symm⟩, ?_⟩
  · rintro _ ⟨g, rfl⟩
    exact (ψ.symm (T84Co.phi (T84Co.a5RelsEquivAlt5.symm g))).2
  · intro x hx y hy
    have hne : ∀ z : ↥B, z ≠ 1 → Multiplicative.toAdd (e z) ≠ 0 := by
      intro z hz h0
      apply hz
      apply e.injective
      rw [map_one]
      exact Multiplicative.toAdd.injective (by rw [h0]; rfl)
    obtain ⟨g, hg⟩ := T84Co.phi_transitive _ _ (hne x hx) (hne y hy)
    refine ⟨Φ (T84Co.a5RelsEquivAlt5 g), ⟨_, rfl⟩, ?_⟩
    have hΦg : Φ (T84Co.a5RelsEquivAlt5 g) = ((ψ.symm (T84Co.phi g) : ↥H) : MulAut ↥B) := by
      simp [Φ]
    rw [hΦg]
    apply e.injective
    apply Multiplicative.toAdd.injective
    have h2 := hact (ψ.symm (T84Co.phi g)) x
    rw [MulEquiv.apply_symm_apply] at h2
    rw [h2, hg]

end CFSG.OddStandard.SmallF3.Omega
