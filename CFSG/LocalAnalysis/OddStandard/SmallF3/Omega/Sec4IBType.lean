module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBProj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBInv

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec4IPsi_hasType_iff (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q)
    {v : Fin 7 → ZMod 2} (hv : IsEvenVec v) (h0 : v ≠ 0) {r : ℕ} {α : ℤˣ}
    (hr : r = 2 ∨ r = 4 ∨ r = 6) :
    HasType (sec4IPsi fr v) r α ↔ r = vecWeight v ∧ α = (-1) ^ (vecWeight v / 2) := by
  constructor
  · intro h
    simp only [HasType] at h
    obtain ⟨_hx1, t, _htt, htype, hproj⟩ := h
    have hmem : (sec4IT fr v)⁻¹ * t ∈ piGroup Q := by
      apply (QuotientGroup.eq_one_iff (N := piGroup Q) ((sec4IT fr v)⁻¹ * t)).mp
      change toProj Q ((sec4IT fr v)⁻¹ * t) = 1
      rw [map_mul, map_inv, hproj]
      simp [sec4IPsi]
    rcases mem_piGroup_iff.mp hmem with hg | hg
    · have ht : t = sec4IT fr v := (eq_of_inv_mul_eq_one hg).symm
      have htype' : (vecWeight v, (-1) ^ (vecWeight v / 2)) = (r, α) := by
        rw [← sec4IT_invType hQ fr hv, ← ht]
        exact htype
      exact ⟨(congrArg Prod.fst htype').symm, (congrArg Prod.snd htype').symm⟩
    · exfalso
      have ht : t = sec4IT fr v * piOrth Q := eq_mul_of_inv_mul_eq hg
      have htv : t = sec4IT fr (v + sec4IOnes) := by
        rw [ht, ← sec4IT_ones fr, ← sec4IT_add]
      have hdim : invDim t = vecWeight (v + sec4IOnes) := by rw [htv, sec4IT_invDim]
      have hr_eq : r = vecWeight (v + sec4IOnes) :=
        (congrArg Prod.fst htype).symm.trans hdim
      have hnotEven : ¬ Even (vecWeight (v + sec4IOnes)) := fun h =>
        sec4I_not_isEvenVec_add_ones hv ((sec4I_isEvenVec_iff_even_vecWeight _).mpr h)
      have hEven : Even r := by
        rcases hr with h | h | h
        · rw [h]; exact ⟨1, by norm_num⟩
        · rw [h]; exact ⟨2, by norm_num⟩
        · rw [h]; exact ⟨3, by norm_num⟩
      exact hnotEven (hr_eq ▸ hEven)
  · rintro ⟨hr', hα⟩
    refine ⟨sec4IPsi_ne_one fr hv h0, sec4IT fr v, sec4IT_mul_self fr v, ?_, rfl⟩
    rw [sec4IT_invType hQ fr hv, hr', hα]

theorem sec4IPsi_hasType_two (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q)
    {v : Fin 7 → ZMod 2} (hv : IsEvenVec v) (h0 : v ≠ 0) :
    vecWeight v = 2 ↔ HasType (sec4IPsi fr v) 2 (-1) := by
  have hiff := sec4IPsi_hasType_iff (r := 2) (α := -1) hQ fr hv h0 (Or.inl rfl)
  exact ⟨fun h => hiff.mpr ⟨h.symm, by rw [h]; decide⟩,
    fun h => (hiff.mp h).1.symm⟩

theorem sec4IPsi_hasType_four (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q)
    {v : Fin 7 → ZMod 2} (hv : IsEvenVec v) (h0 : v ≠ 0) :
    vecWeight v = 4 ↔ HasType (sec4IPsi fr v) 4 1 := by
  have hiff := sec4IPsi_hasType_iff (r := 4) (α := 1) hQ fr hv h0 (Or.inr (Or.inl rfl))
  exact ⟨fun h => hiff.mpr ⟨h.symm, by rw [h]; decide⟩,
    fun h => (hiff.mp h).1.symm⟩

theorem sec4IPsi_hasType_six (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q)
    {v : Fin 7 → ZMod 2} (hv : IsEvenVec v) (h0 : v ≠ 0) :
    vecWeight v = 6 ↔ HasType (sec4IPsi fr v) 6 (-1) := by
  have hiff := sec4IPsi_hasType_iff (r := 6) (α := -1) hQ fr hv h0 (Or.inr (Or.inr rfl))
  exact ⟨fun h => hiff.mpr ⟨h.symm, by rw [h]; decide⟩,
    fun h => (hiff.mp h).1.symm⟩

end CFSG.OddStandard.SmallF3.Omega
