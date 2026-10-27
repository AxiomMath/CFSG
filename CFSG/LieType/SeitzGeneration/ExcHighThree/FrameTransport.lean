module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Defs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Chevalley.RootWeightFiltration
public import CFSG.LieType.SeitzGeneration.ExcHighThree.Closing

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

section FrameTransport

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

variable {τ : Tag} {K : Type} [Field K]

abbrev frameIn (X : Subgroup (ModGL τ K)) : Subgroup (adjointGroup τ K) :=
  X.subgroupOf (adjointGroup τ K)

theorem closing_of_twFrameClosing {X : Subgroup (ModGL τ K)} (hle : X ≤ adjointGroup τ K)
    (hC : TwFrameClosing τ K X) :
    ∀ H : Subgroup (adjointGroup τ K), frameIn X ≤ H →
      ¬ H ≤ Subgroup.normalizer (frameIn X : Set (adjointGroup τ K)) → H = ⊤ := by
  intro H hXH hHN
  set H' : Subgroup (ModGL τ K) := H.map (adjointGroup τ K).subtype with hH'
  have hH'G : H' ≤ adjointGroup τ K := by
    rintro _ ⟨h, -, rfl⟩
    exact h.2
  have hX : X ≤ H' := fun x hx =>
    ⟨⟨x, hle hx⟩, hXH (Subgroup.mem_comap.2 hx), rfl⟩
  have hN : ¬ H' ≤ Subgroup.normalizer (X : Set (ModGL τ K)) := by
    intro hN
    apply hHN
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hn := Subgroup.mem_normalizer_iff.1 (hN ⟨h, hh, rfl⟩) (x : ModGL τ K)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hn
  have htop := hC H' hH'G hX hN
  rw [eq_top_iff]
  intro g _
  have : (g : ModGL τ K) ∈ H' := by rw [htop]; exact g.2
  obtain ⟨h, hh, hhg⟩ := this
  have : h = g := Subtype.ext hhg
  exact this ▸ hh

theorem normalizerSolvable_of_twFrame {X : Subgroup (ModGL τ K)} (hle : X ≤ adjointGroup τ K)
    (hN : TwFrameNormalizerSolvable τ K X) :
    ∀ P : Subgroup (adjointGroup τ K),
      P ≤ Subgroup.normalizer (frameIn X : Set (adjointGroup τ K)) →
      Group.IsSolvable ↥(P ⊓ frameIn X) → Group.IsSolvable ↥P := by
  intro P hP hPX
  set P' : Subgroup (ModGL τ K) := P.map (adjointGroup τ K).subtype with hP'
  have hP'G : P' ≤ adjointGroup τ K := by
    rintro _ ⟨p, -, rfl⟩
    exact p.2
  have hP'N : P' ≤ Subgroup.normalizer (X : Set (ModGL τ K)) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hpn := Subgroup.mem_normalizer_iff.1 (hP hp)
    constructor
    · intro hx
      have := (hpn ⟨x, hle hx⟩).1 hx
      exact this
    · intro hx
      have hxG : x ∈ adjointGroup τ K := by
        have h1 : ((p : ModGL τ K) * x * (p : ModGL τ K)⁻¹) ∈ adjointGroup τ K := hle hx
        have h2 : (p : ModGL τ K)⁻¹ ∈ adjointGroup τ K := (adjointGroup τ K).inv_mem p.2
        have h3 := (adjointGroup τ K).mul_mem ((adjointGroup τ K).mul_mem h2 h1) p.2
        simpa [mul_assoc] using h3
      exact (hpn ⟨x, hxG⟩).2 hx
  have hinf : P' ⊓ X = (P ⊓ frameIn X).map (adjointGroup τ K).subtype := by
    ext y
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hy⟩
      exact ⟨p, ⟨hp, hy⟩, rfl⟩
    · rintro ⟨p, ⟨hp, hy⟩, rfl⟩
      exact ⟨⟨p, hp, rfl⟩, hy⟩
  have hsol : Group.IsSolvable ↥(P' ⊓ X) := by
    rw [hinf]
    exact (isSolvable_map_iff _ (adjointGroup τ K).subtype_injective _).2 hPX
  exact (isSolvable_map_iff _ (adjointGroup τ K).subtype_injective P).1 (hN P' hP'G hP'N hsol)

theorem nonsolvable_frameIn {X : Subgroup (ModGL τ K)} (hle : X ≤ adjointGroup τ K)
    (h : ¬ Group.IsSolvable ↥X) : ¬ Group.IsSolvable ↥(frameIn X) := by
  intro hs
  apply h
  have := (isSolvable_map_iff _ (adjointGroup τ K).subtype_injective (frameIn X)).2 hs
  rwa [Subgroup.map_subgroupOf_eq_of_le hle] at this

end FrameTransport

end CFSG.LieType.SeitzGeneration.ExcHighThree
