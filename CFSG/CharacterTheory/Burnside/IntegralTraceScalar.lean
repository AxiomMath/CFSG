module

public import CFSG.CharacterTheory.Burnside.FiniteOrderTrace

public section

namespace CFSG

namespace Burnside

theorem Module.End.eq_smul_one_of_pow_eq_one_of_isIntegral_trace_div_finrank
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
    (f : Module.End ℂ V) {n : ℕ} (hn : 0 < n) (hpow : f ^ n = 1)
    (htrace0 : LinearMap.trace ℂ V f / (Module.finrank ℂ V : ℂ) ≠ 0)
    (htraceint :
      IsIntegral ℤ (LinearMap.trace ℂ V f / (Module.finrank ℂ V : ℂ))) :
    f = (LinearMap.trace ℂ V f / (Module.finrank ℂ V : ℂ)) • 1 := by
  classical
  let s : Multiset ℂ := (LinearMap.charpoly f).roots
  have hfinrank : 0 < Module.finrank ℂ V := Module.finrank_pos
  have hcard : s.card = Module.finrank ℂ V := by
    dsimp [s]
    rw [IsAlgClosed.card_roots_eq_natDegree, LinearMap.charpoly_natDegree]
  have hroot_pow : ∀ z ∈ s, z ^ n = 1 := by
    intro z hz
    have heig : f.HasEigenvalue z :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly f z).2
        (Polynomial.isRoot_of_mem_roots hz)
    obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
    have hvpow := hv.pow_apply n
    rw [hpow, Module.End.one_apply] at hvpow
    have hzsmul : (z ^ n - 1) • v = 0 := by
      rw [sub_smul, one_smul, ← hvpow, sub_self]
    rcases smul_eq_zero.mp hzsmul with hz | hvzero
    · exact sub_eq_zero.mp hz
    · exact (hv.2 hvzero).elim
  have htrace_sum : LinearMap.trace ℂ V f = s.sum := by
    simpa [s] using
      (Module.End.trace_eq_sum_roots_charpoly_of_splits
        (f := f) (IsAlgClosed.splits (LinearMap.charpoly f)))
  let T : Set ℂ := ↑s.toFinset
  have hTfinite : T.Finite := by
    simpa [T] using s.toFinset.finite_toSet
  let : Fintype T := hTfinite.fintype
  have hTint : ∀ z ∈ T, IsIntegral ℚ z := by
    intro z hz
    apply IsIntegral.of_pow hn
    rw [hroot_pow z (by simpa [T] using hz)]
    exact isIntegral_one
  let K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ T
  let : FiniteDimensional ℚ K := by
    dsimp only [K]
    exact IntermediateField.finiteDimensional_adjoin hTint
  let : NumberField K := NumberField.of_module_finite ℚ K
  let rootsK : Multiset K := s.attach.map fun z =>
    ⟨z.1, IntermediateField.mem_adjoin_of_mem ℚ
      (show z.1 ∈ T by simpa [T] using z.2)⟩
  have hcoe_rootsK : Multiset.map (fun z : K => (z : ℂ)) rootsK = s := by
    simp [rootsK, Multiset.attach_map_val]
  let x : K := rootsK.sum / (Module.finrank ℂ V : K)
  have hxcoe : (x : ℂ) =
      LinearMap.trace ℂ V f / (Module.finrank ℂ V : ℂ) := by
    dsimp only [x]
    change ((rootsK.sum : K) : ℂ) / (((Module.finrank ℂ V : K) : ℂ)) =
      LinearMap.trace ℂ V f / (Module.finrank ℂ V : ℂ)
    have hsumcoe : ((rootsK.sum : K) : ℂ) = s.sum := by
      rw [← hcoe_rootsK]
      simpa using (map_multiset_sum (IntermediateField.val K) rootsK)
    rw [hsumcoe, ← htrace_sum]
    norm_cast
  have hx0 : x ≠ 0 := by
    intro hx
    apply htrace0
    rw [← hxcoe, hx]
    rfl
  have hxint : IsIntegral ℤ x := by
    apply IntermediateField.coe_isIntegral_iff.mp
    rwa [hxcoe]
  have hrootK_pow : ∀ z ∈ rootsK, z ^ n = 1 := by
    intro z hz
    rcases Multiset.mem_map.mp hz with ⟨a, ha, rfl⟩
    apply Subtype.ext
    exact hroot_pow a.1 a.2
  have hemb : ∀ φ : K →+* ℂ, ‖φ x‖ ≤ 1 := by
    intro φ
    let rootsφ : Multiset ℂ := rootsK.map φ
    have hnormφ : ∀ z ∈ rootsφ, ‖z‖ = 1 := by
      intro z hz
      rcases Multiset.mem_map.mp hz with ⟨a, ha, rfl⟩
      apply Complex.norm_eq_one_of_pow_eq_one
      · rw [← map_pow, hrootK_pow a ha, map_one]
      · exact hn.ne'
    have hsum_le : ‖rootsφ.sum‖ ≤ (Module.finrank ℂ V : ℝ) := by
      have hmapnorm : rootsφ.map (fun z => ‖z‖) =
          Multiset.replicate rootsφ.card (1 : ℝ) := by
        have h := Multiset.eq_replicate_of_mem
          (s := rootsφ.map (fun z => ‖z‖)) (a := (1 : ℝ)) (by
            intro r hr
            obtain ⟨z, hz, hrz⟩ := Multiset.mem_map.mp hr
            subst r
            exact hnormφ z hz)
        simpa using h
      calc
        ‖rootsφ.sum‖ ≤ (rootsφ.map fun z => ‖z‖).sum := norm_multiset_sum_le rootsφ
        _ = (rootsφ.card : ℝ) := by rw [hmapnorm]; simp
        _ = (Module.finrank ℂ V : ℝ) := by simp [rootsφ, rootsK, hcard]
    have hφx : φ x = rootsφ.sum / (Module.finrank ℂ V : ℂ) := by
      simp [x, rootsφ, map_multiset_sum]
    rw [hφx, norm_div, Complex.norm_natCast]
    have hdpos : 0 < (Module.finrank ℂ V : ℝ) := by exact_mod_cast hfinrank
    exact (div_le_one₀ hdpos).mpr hsum_le
  obtain ⟨m, hm, hxm⟩ :=
    NumberField.Embeddings.pow_eq_one_of_norm_le_one K ℂ hx0 hxint hemb
  apply Module.End.eq_smul_one_of_pow_eq_one_of_trace_div_finrank_pow_eq_one
    f hn hpow hm
  calc
    (LinearMap.trace ℂ V f / (Module.finrank ℂ V : ℂ)) ^ m =
        ((x ^ m : K) : ℂ) := by rw [← hxcoe]; rfl
    _ = ((1 : K) : ℂ) := congrArg (fun y : K => (y : ℂ)) hxm
    _ = 1 := rfl

end Burnside

end CFSG
