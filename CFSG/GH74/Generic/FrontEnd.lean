module

public import CFSG.GH74.Generic.ComponentShapes
public import CFSG.GH74.Generic.OuterInvolution
public import CFSG.GH74.Generic.QuaternionCentral

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank CFSG.Blueprint Subgroup
  CFSG.GH74.Filter.ClassicalOdd

variable {G : Type} [Group G]

theorem ShapeS1.q8Frame {x : G} {K : Subgroup (CentralizerBar x)} (h : ShapeS1 x K) :
    Q8Frame ↥K :=
  IsSL4Model.q8Frame h.1

theorem ShapeS2.q8Frame {x : G} {K : Subgroup (CentralizerBar x)} (h : ShapeS2 x K) :
    Q8Frame ↥K := by
  obtain ⟨⟨F, _, _, hodd, ⟨e⟩⟩, -⟩ := h
  have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_two_ne_zero (two_ne_zero_of_odd_card hodd)
  obtain ⟨φ, hφ, w, hww, hsw⟩ := exists_q8q8_Sp4 hF2
  exact Q8Frame.of_mulEquiv ⟨φ, hφ, w, hww, hsw⟩ e.symm

variable [Finite G] in
theorem ShapeS1.xbar_eq_center (hgen : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (h : ShapeS1 x K) :
    ∃ z : ↥K, orderOf z = 2 ∧ (∀ g : ↥K, g ∈ Subgroup.center ↥K ↔ g = 1 ∨ g = z) ∧
      (z : CentralizerBar x) = xbar x := by
  obtain ⟨z, φ, w, hz2, hcenter, hφ, hφz, -, hsw⟩ := h.1.exists_q8_frame
  refine ⟨z, hz2, hcenter, ?_⟩
  have := frame_xbar_eq hgen hx φ hφ w hsw
  rwa [hφz] at this

@[expose] def twistedFixed {K : Type} [Group K] (α : MulAut K) (k : K) : Subgroup K :=
  MonoidHom.eqLocus (MulAut.conj k * α).toMonoidHom (MonoidHom.id K)

@[expose] def OuterInvolutionClasses (K : Type) [Group K] : Prop :=
  ∀ α : MulAut K, α * α = 1 → (∀ k : K, α ≠ MulAut.conj k) →
    (∃ (k : K) (j : ℕ) (φ : Qgen j × Qgen j →* K), 1 ≤ j ∧
        (∀ g, φ g = 1 → g = 1 ∨ g = (Qgen.z j, Qgen.z j)) ∧ ∀ g, φ g ∈ twistedFixed α k) ∨
      (∃ (k : K) (F : Type) (_ : Field F) (_ : Finite F),
        Nonempty (↥(layer ↥(twistedFixed α k)) ≃* StatedSL 3 F)) ∨
      (∃ (k : K) (F : Type) (_ : Field F) (_ : Finite F) (q : ℕ), Nat.card F = q ^ 2 ∧
        Nonempty (↥(layer ↥(twistedFixed α k)) ≃* StatedSU 3 q F)) ∨
      (∃ (k : K) (F : Type) (_ : Field F) (_ : Finite F),
        Nonempty (↥(layer ↥(twistedFixed α k)) ≃* StatedProj (StatedSL 2 F))) ∨
      (∃ (k : K) (F : Type) (_ : Field F) (_ : Finite F),
        Nonempty (↥(layer ↥(twistedFixed α k)) ≃* StatedSL 2 F))

variable [Finite G]

theorem generic_front_end (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a) (hgen : Gen4 G)
    {x : G} (hx : orderOf x = 2) {K : Subgroup (CentralizerBar x)} (hKc : IsComponent K)
    (hsh : ShapeS1 x K ∨ ShapeS2 x K) :
    xbar x ∈ K ∧ layer (CentralizerBar x) = K ∧
      centralizer (K : Set (CentralizerBar x)) = Subgroup.zpowers (xbar x) ∧
      pCore 2 (CentralizerBar x) = Subgroup.zpowers (xbar x) ∧
      fittingSubgroup (CentralizerBar x) = Subgroup.zpowers (xbar x) ∧
      generalizedFitting (CentralizerBar x) = K ∧
      IsCentralInvolution x ∧
      (∃ T : Sylow 2 G, x ∈ (T : Subgroup G) ∧ (∀ t ∈ (T : Subgroup G), t * x = x * t) ∧
        ∀ c ∈ (T : Subgroup G), (∀ t ∈ (T : Subgroup G), t * c = c * t) →
          c ∈ Subgroup.zpowers x) ∧
      (NoNoncentralInvolutionConj x K →
        ∃ (v : G) (hv : v ∈ centralizer ({x} : Set G)), IsConj x v ∧ v ≠ x ∧ v * v = 1 ∧
          barOf hv ≠ 1 ∧ barOf hv ≠ xbar x ∧ barOf hv ∉ K) := by
  have hfr : Q8Frame ↥K := by
    rcases hsh with h | h
    · exact h.q8Frame
    · exact h.q8Frame
  obtain ⟨hxK, hl, hc, hp, hf, hfs⟩ := frame_B2 hgen hx hKc hfr
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥(Subgroup.centralizer ({x} : Set G))) := inferInstance
  obtain ⟨T, -, hxT, hcomm, hZ⟩ := frame_sylow_centralizer_isSylow hgen hx hfr S
  exact ⟨hxK, hl, hc, hp, hf, hfs, frame_isCentralInvolution hgen hx hfr, ⟨T, hxT, hcomm, hZ⟩,
    fun hB5 => exists_outer_involution hs hn hgen hx hfr hB5⟩

theorem generic_shapes_front_end
    (hF : GenericKnownFacts) (hs : IsSimpleGroup G)
    (hn : ∃ a b : G, a * b ≠ b * a) (hgen : Gen4 G) (hK : KGH G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hKc : IsComponent K) (hG2 : GLS.InG2 ↥K) :
    GenericShape x K ∧ ((ShapeS1 x K ∨ ShapeS2 x K) →
      xbar x ∈ K ∧ layer (CentralizerBar x) = K ∧
        centralizer (K : Set (CentralizerBar x)) = Subgroup.zpowers (xbar x) ∧
        IsCentralInvolution x) := by
  have hsh := generic_component_shapes hF hs hn hgen hK hx hKc hG2
  refine ⟨hsh, fun h => ?_⟩
  obtain ⟨h1, h2, h3, -, -, -, h7, -⟩ := generic_front_end hs hn hgen hx hKc h
  exact ⟨h1, h2, h3, h7⟩

end CFSG.GH74.Generic
