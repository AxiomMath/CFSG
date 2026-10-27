module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8SNorm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8SNormGL
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import Certificates.Certificate442267

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem asc82NormA6_of : Asc82NormA6 := by
  intro G _ _ B hB H₁ H₂ h12 hA hnorm
  have hcomm : ∀ a b : ↥B, a * b = b * a :=
    fun a b => hB.1.1.is_comm.comm a b
  have hpow : ∀ a : ↥B, a ^ 2 = 1 := by
    intro a
    apply Subtype.ext
    simpa using hB.1.2 (a : G) a.2
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (W := ↥B) hcomm hpow (n := 4) hB.2
  let Φ : MulAut ↥B ≃* GL (Fin 4) (ZMod 2) := CFSG.SectionRank.Ccomm.elemAutEquivGL e
  let H₁' : Subgroup (GL (Fin 4) (ZMod 2)) := H₁.map (Φ : MulAut ↥B →* GL (Fin 4) (ZMod 2))
  let H₂' : Subgroup (GL (Fin 4) (ZMod 2)) := H₂.map (Φ : MulAut ↥B →* GL (Fin 4) (ZMod 2))
  have h12' : H₁' ≤ H₂' := Subgroup.map_mono h12
  have hA' : Nonempty (↥H₁' ≃* alternatingGroup (Fin 6)) :=
    ⟨(Φ.subgroupMap H₁).symm.trans hA.some⟩
  have hnorm' : ∀ h ∈ H₂', ∀ a ∈ H₁', h * a * h⁻¹ ∈ H₁' := by
    intro h hh a ha
    obtain ⟨h₀, hh₀, rfl⟩ := Subgroup.mem_map.mp hh
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    exact Subgroup.mem_map.mpr
      ⟨h₀ * a₀ * h₀⁻¹, hnorm h₀ hh₀ a₀ ha₀, by simp [map_mul, map_inv]⟩
  rcases gl_normA6_of_facts Certificates.certificate442267 H₁' H₂' h12' hA' hnorm' with h | h
  · exact Or.inl ⟨(Φ.subgroupMap H₂).trans h.some⟩
  · exact Or.inr ⟨(Φ.subgroupMap H₂).trans h.some⟩

end CFSG.OddStandard.SmallF3.Omega
