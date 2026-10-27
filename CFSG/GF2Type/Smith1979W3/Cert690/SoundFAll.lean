module

public import CFSG.GF2Type.Smith1979W3.Cert690.SoundF
public import CFSG.GF2Type.Smith1979W3.Cert690.SoundFB6
public import CFSG.GF2Type.Smith1979W3.Cert690.SoundFB7

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62 Module

theorem pglFacts_sound_of_F10_F11 (hK : EnumCert kPGLGens (pglData ()).elems.toList)
    (hK0 : EnumCert kPGL0Gens (pglData ()).elems0.toList) (h : pglFactsCheck () = true)
    (h10 : ∀ e : V₀, e ≠ 0 → qModel false e = 0 → e ∉ VPlus → e ∉ VStar →
      ∀ L, ¬ CensusCond false KPGL L e)
    (h11 : ∀ u ∈ KPGL, u ∉ KPGL0 → u * u = 1 →
      Nat.card ↥(KPGL ⊓ Subgroup.centralizer {u}) = 12 ∧
      ∀ N : Subgroup (V₀ ≃ₗ[ZMod 2] V₀), N ≤ KPGL ⊓ Subgroup.centralizer {u} →
        (∀ c ∈ KPGL ⊓ Subgroup.centralizer {u}, ∀ n ∈ N, c * n * c⁻¹ ∈ N) →
        IsPGroup 2 N → N ≤ Subgroup.zpowers u) : PGLFactsProp := by
  obtain ⟨hKPGL, hcardK, hcardK0, hVPlus, hVStar, hInf, hSup, hPres, hSwap⟩ :=
    pglFacts_core_of hK hK0 h
  unfold PGLFactsProp
  exact ⟨hKPGL, hcardK, pglF4_sound_of hK hK0 h, hcardK0, hVPlus, hVStar, hInf, hSup,
    hPres, hSwap, pglF8_sound_of hK hK0 h, pglF9_sound_of hK hK0 h, h10, h11,
    pglF12_sound_of hK hK0 h, pglF13_sound_of hK hK0 h⟩

theorem pglFacts_sound_of (hK : EnumCert kPGLGens (pglData ()).elems.toList)
    (hK0 : EnumCert kPGL0Gens (pglData ()).elems0.toList) (h : pglFactsCheck () = true) :
    PGLFactsProp :=
  pglFacts_sound_of_F10_F11 hK hK0 h (pglF10_sound_of hK hK0 h) (pglF11_sound_of hK hK0 h)

end CFSG.GF2Type.Smith1979W3.Cert690
