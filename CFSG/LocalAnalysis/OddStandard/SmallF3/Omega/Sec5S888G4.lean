module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888G2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888G3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Ctx

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Fact517Fuse_of_heart (h514 : Asc82Lemma514) (hdict : Asc82HeartDict) :
    Asc82Fact517Fuse := by
  intro G _ _ t L S z r B A K₁ K₂ h c
  obtain ⟨Alt, φ, hAlt, hperm, hz, hA₁, hA₂⟩ := hdict G t L S z r B A K₁ K₂ h c
  have hH := sec5b_heartData hperm
  obtain ⟨m, hm, v₁, v₂, hv₁, hv₂, hmz, ⟨h1sq, h1ne, h1nez⟩, ⟨h2sq, h2ne, h2nez⟩⟩ :=
    heart_fuse_data hAlt hH
  have hq : Sec5B517Quad (Kfam5 K₁ K₂ h) z := sec5b517_quad h514 c
  have ha : φ v₁ ∈ Kfam5 K₁ K₂ h 0 ⊔ Kfam5 K₁ K₂ h 1 := by
    have hmem : φ v₁ ∈ A ⊓ (K₁ ⊔ K₂) := (hA₁ (φ v₁)).mpr ⟨v₁, hv₁, rfl⟩
    have hmem' : φ v₁ ∈ K₁ ⊔ K₂ := (Subgroup.mem_inf.mp hmem).2
    simpa [Kfam5] using hmem'
  have hb : φ v₂ ∈ Kfam5 K₁ K₂ h 2 ⊔ Kfam5 K₁ K₂ h 3 := by
    have hmem : φ v₂ ∈ A ⊓ (CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h) :=
      (hA₂ (φ v₂)).mpr ⟨v₂, hv₂, rfl⟩
    have hmem' : φ v₂ ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h :=
      (Subgroup.mem_inf.mp hmem).2
    simpa [Kfam5] using hmem'
  have haz : φ v₁ ≠ z := by
    intro hxz
    exact h1nez (by rw [hxz, hz])
  have hbz : φ v₂ ≠ z := by
    intro hxz
    exact h2nez (by rw [hxz, hz])
  obtain ⟨hmp2, hmp1, hmpz, hmpQ, hmpl⟩ :=
    Sec5B517Quad.mul_pair_props hq ha h1sq h1ne haz hb h2sq h2ne hbz
  have hmz' : m⁻¹ * z * m = φ v₁ * φ v₂ := by rw [hz, hmz]
  refine ⟨m, hm, ?_, ?_⟩
  · rw [hmz']
    refine Or.inr ⟨?_, ?_, ?_⟩
    · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [pow_two]; exact hmp2) hmp1
    · rwa [sec5b517_Qsub_eq, hq.core_eq]
    · intro P hP
      rw [sec5b517_gamma_eq] at hP
      obtain ⟨i, rfl⟩ := hP
      exact hmpl i
  · rw [hmz']
    exact hmpz

end CFSG.OddStandard.SmallF3.Omega
