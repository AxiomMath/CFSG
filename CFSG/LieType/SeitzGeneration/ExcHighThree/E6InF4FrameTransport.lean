module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InF4Frame

public section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.E6
  CFSG.HardMathSupport.Lang.AnisoE6 CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

@[expose] def E6TransportLevi : Prop :=
  ∀ (L : Type) [Field L], ∀ g : ModGL Tag.F4 L, g ∈ Lθ Tag.F4 L →
    ∃ h : adjointGroup .F4 L, (h : ModGL Tag.F4 L) = g ∧
      ((embE6F4 L h : adjointGroup .E6 L) : ModGL Tag.E6 L) ∈ Lθ Tag.E6 L

@[expose] def E6TransportFrob : Prop :=
  ∀ (L : Type) [Field L] (φ : L →+* L) (h : adjointGroup .F4 L),
    ∃ h' : adjointGroup .F4 L,
      (h' : ModGL Tag.F4 L) = Units.map (entrywiseHom φ) (h : ModGL Tag.F4 L) ∧
      Units.map (entrywiseHom φ) ((embE6F4 L h : adjointGroup .E6 L) : ModGL Tag.E6 L) =
        ((embE6F4 L h' : adjointGroup .E6 L) : ModGL Tag.E6 L)

@[expose] def E6TransportBase : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (z : adjointGroup .F4 K),
    ∃ z' : adjointGroup .F4 L,
      (z' : ModGL Tag.F4 L) = baseChangeGL (algebraMap K L) (z : ModGL Tag.F4 K) ∧
      baseChangeGL (algebraMap K L) ((embE6F4 K z : adjointGroup .E6 K) : ModGL Tag.E6 K) =
        ((embE6F4 L z' : adjointGroup .E6 L) : ModGL Tag.E6 L)

@[expose] def E6TransportTits : Prop :=
  ∀ (L : Type) [Field L],
    ∃ h : adjointGroup .F4 L,
      (h : ModGL Tag.F4 L) =
        canonicalRep (coxeterSystem TwClass.f4Six.tag) L TwClass.f4Six.w ∧
      ((embE6F4 L h : adjointGroup .E6 L) : ModGL Tag.E6 L) =
        canonicalRep (coxeterSystem TwClass.e6Six.tag) L TwClass.e6Six.w

@[expose] def E6TransportSplit : Prop :=
  ∀ (L : Type) [Field L] (ω : Lˣ), orderOf ω = 3 →
    ((embE6F4 L (zSplit L ω) : adjointGroup .E6 L) : ModGL Tag.E6 L) =
      rootDiagUnit TwClass.e6Six.tag (Pi.mulSingle (⟨3, by decide⟩ : Fin TwClass.e6Six.tag.rank) ω)

theorem e6TwistedTransport_of_facts (hLevi : E6TransportLevi) (hFrob : E6TransportFrob)
    (hBase : E6TransportBase) (hTits : E6TransportTits) (hSplit : E6TransportSplit) :
    E6TwistedTransport := by
  unfold E6TransportLevi at hLevi
  unfold E6TransportFrob at hFrob
  unfold E6TransportBase at hBase
  unfold E6TransportTits at hTits
  unfold E6TransportSplit at hSplit
  unfold E6TwistedTransport
  intro K _ _ hK h3 D₁ ω hω z hzbc
  letI : Field D₁.L := D₁.field
  letI : Algebra K D₁.L := D₁.algebra
  letI : IsAlgClosure K D₁.L := D₁.isAlgClosure
  obtain ⟨h₁, hh₁, hLev⟩ := hLevi D₁.L D₁.g D₁.g_mem
  obtain ⟨h₄, hh₄, hE₄⟩ := hTits D₁.L
  obtain ⟨h', hh', hF⟩ := hFrob D₁.L D₁.Fr h₁
  have hlangF4 :
      (h' : ModGL Tag.F4 D₁.L) = (h₁ : ModGL Tag.F4 D₁.L) * (h₄ : ModGL Tag.F4 D₁.L) := by
    rw [hh', hh₁, hh₄]
    exact D₁.lang
  have hh'eq : h' = h₁ * h₄ := Subtype.ext hlangF4
  obtain ⟨g₆, hg₆⟩ : ∃ g₆ : ModGL TwClass.e6Six.tag D₁.L,
      g₆ = ((embE6F4 D₁.L h₁ : adjointGroup .E6 D₁.L) : ModGL Tag.E6 D₁.L) := ⟨_, rfl⟩
  have hLev' : g₆ ∈ Lθ TwClass.e6Six.tag D₁.L := by
    rw [hg₆]
    exact hLev
  have hlangE6 : Units.map (entrywiseHom D₁.Fr) g₆ =
      g₆ * canonicalRep (coxeterSystem TwClass.e6Six.tag) D₁.L TwClass.e6Six.w := by
    have e3 : ((embE6F4 D₁.L h' : adjointGroup .E6 D₁.L) : ModGL Tag.E6 D₁.L) =
        ((embE6F4 D₁.L h₁ : adjointGroup .E6 D₁.L) : ModGL Tag.E6 D₁.L) *
          ((embE6F4 D₁.L h₄ : adjointGroup .E6 D₁.L) : ModGL Tag.E6 D₁.L) := by
      rw [hh'eq, map_mul, Subgroup.coe_mul]
    rw [hE₄] at e3
    rw [hg₆]
    exact hF.trans e3
  refine ⟨{ L := D₁.L, Fr := D₁.Fr, hFr := D₁.hFr, g := g₆, g_mem := hLev', lang := hlangE6 },
    ω, hω, ?_⟩
  let z4 : adjointGroup .F4 K := z
  obtain ⟨z', hz', hbase⟩ := hBase K D₁.L z4
  have hzbc' : baseChangeGL (algebraMap K D₁.L) ((z4 : adjointGroup .F4 K) : ModGL Tag.F4 K) =
      D₁.g * rootDiagUnit TwClass.f4Six.tag
        (Pi.mulSingle (⟨1, by decide⟩ : Fin TwClass.f4Six.tag.rank) ω) *
        D₁.g⁻¹ := hzbc
  have hz'eq : z' = h₁ * zSplit D₁.L ω * h₁⁻¹ := by
    apply Subtype.ext
    rw [hz', hzbc', Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hh₁]
    rfl
  show baseChangeGL (algebraMap K D₁.L) ((embE6F4 K z4 : adjointGroup .E6 K) : ModGL Tag.E6 K) =
    g₆ * rootDiagUnit TwClass.e6Six.tag
      (Pi.mulSingle (⟨3, by decide⟩ : Fin TwClass.e6Six.tag.rank) ω) *
      g₆⁻¹
  rw [hg₆, hbase, hz'eq, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv,
    hSplit D₁.L ω hω]
  rfl

end CFSG.LieType.SeitzGeneration.ExcHighThree

end
