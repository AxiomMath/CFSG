module

public import CFSG.GF2Type.Smith1979W3.Cert690.SoundFB4

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62 Module

class PGLFactsCert : Prop where
  proof : pglFactsCheck () = true

theorem natCard_KPGL_of_enum {D : PGLData} (hK : EnumCert kPGLGens D.elems.toList)
    (h3 : pglF3Of D = true) : Nat.card KPGL = 336 := by
  have h := hK.natCard
  have hsize := (pglF3Of_facts h3).1
  simpa [KPGL, Array.length_toList, hsize] using h

theorem natCard_KPGL0_of_enum {D : PGLData} (hK0 : EnumCert kPGL0Gens D.elems0.toList)
    (h3 : pglF3Of D = true) : Nat.card KPGL0 = 168 := by
  have h := hK0.natCard
  have hsize := (pglF3Of_facts h3).2
  simpa [KPGL0, Array.length_toList, hsize] using h

theorem KPGL_le_O₀_sound : KPGL ≤ O₀ false := KPGL_le_O₀

theorem pglFacts_core_of (hK : EnumCert kPGLGens (pglData ()).elems.toList)
    (hK0 : EnumCert kPGL0Gens (pglData ()).elems0.toList) (h : pglFactsCheck () = true) :
    KPGL ≤ O₀ false ∧ Nat.card KPGL = 336 ∧ Nat.card KPGL0 = 168 ∧
    (∀ v ∈ VPlus, qModel false v = 0) ∧ (∀ v ∈ VStar, qModel false v = 0) ∧
    VPlus ⊓ VStar = ⊥ ∧ VPlus ⊔ VStar = ⊤ ∧
    (∀ k ∈ KPGL0, VPlus.map (k : V₀ →ₗ[ZMod 2] V₀) = VPlus ∧
      VStar.map (k : V₀ →ₗ[ZMod 2] V₀) = VStar) ∧
    (∀ k ∈ KPGL, k ∉ KPGL0 → VPlus.map (k : V₀ →ₗ[ZMod 2] V₀) = VStar ∧
      VStar.map (k : V₀ →ₗ[ZMod 2] V₀) = VPlus) := by
  obtain ⟨-, -, h3, -, h5, h6, h7, -, -, -, -, -, -⟩ := pglFactsCheck_all h
  refine ⟨KPGL_le_O₀, natCard_KPGL_of_enum hK h3, natCard_KPGL0_of_enum hK0 h3,
    (fun v hv => VPlus_singular h5 hv), (fun v hv => VStar_singular h5 hv),
    VPlus_inf_VStar h5, VPlus_sup_VStar h5,
    KPGL0_preserves hK0 h5 h6, ?_⟩
  intro k hk hk0
  exact ⟨map_VPlus_eq_VStar_of_not_mem hK hK0 h5 h7 hk hk0,
    map_VStar_eq_VPlus_of_not_mem hK hK0 h5 h7 hk hk0⟩

end CFSG.GF2Type.Smith1979W3.Cert690
