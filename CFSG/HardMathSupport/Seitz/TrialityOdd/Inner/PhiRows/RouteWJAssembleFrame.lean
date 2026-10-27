module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJAssemble
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJOut
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.FrameSL23
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.HandbackPhi6
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWPlaneU
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWUnitaryFinal

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.PartOne.K128 CFSG.RankThree.Lattice

open scoped Matrix MatrixGroups

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

section FixedPoints

variable {K : Type} [Field K] [Finite K]

@[expose] def fieldActorFixed (σ : K ≃+* K) : Subgroup 𝒞[K, σ] :=
  MonoidHom.eqLocus (fieldActor (t := TwistTag.D4) σ σ).toMonoidHom (MonoidHom.id _)

theorem mem_fieldActorFixed {σ : K ≃+* K} {x : 𝒞[K, σ]} :
    x ∈ fieldActorFixed σ ↔ fieldActor (t := TwistTag.D4) σ σ x = x := Iff.rfl

end FixedPoints

section Frame

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] [CharP K ℓ] {σ : K ≃+* K} {r : ℕ}

@[expose] def toGH74Frame (F : D4PhiFrame ℓ f K σ (-1) r (AlgebraicClosure K)) :
    CFSG.GH74.GLS.Stage2.Bender.Thm1.D4PhiFrame K σ (ℓ ^ f) (-1) :=
  ⟨iterateFrobenius (AlgebraicClosure K) ℓ f, fun c => iterateFrobenius_def ℓ f c, F.n, F.hn, F.w,
    F.hnw, F.hw, F.g0, F.hg0C, F.hg0, F.hperf⟩

theorem mem_frameTorus_toGH74Frame (F : D4PhiFrame ℓ f K σ (-1) r (AlgebraicClosure K))
    (y : 𝒞[K, σ]) :
    y ∈ frameTorus (toGH74Frame F) ↔
      F.g0⁻¹ * triEmb K σ (AlgebraicClosure K) y * F.g0 ∈
        twistedTorusOf F.n (twistHom TwistTag.D4 (AlgebraicClosure K)
          (iterateFrobenius (AlgebraicClosure K) ℓ f)) :=
  Iff.rfl

theorem exists_phi6JData_C (hf : 1 ≤ f) (hℓ2 : ℓ ≠ 2) (hq3 : 3 ≤ ℓ ^ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hr : r.Prime) (hr3 : 3 < r)
    (hrd : (r : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1) :
    Nonempty (Phi6JData 𝒞[K, σ] (fieldActorFixed σ) (fixSubfield σ) r (ℓ ^ f)) := by
  classical
  obtain ⟨F, E, hEp, hEc, htor, s, hs, w, hwι, hww, hwE, hwfix, ⟨P, hEP, hPc, hPΩ⟩,
    ⟨x₁, hx₁E, hx₁1, u, hu1, huu, hux, huw⟩, ⟨c, hcE, hc1, hcfix⟩, x₀, hx₀E, hx₀1, sp, hsp, θ, hθP,
    hθw, hθker, hθcard, hθps, hθfix⟩ := exists_phi6_J_datum hf hℓ2 hq3 K hK σ hσ hr hr3 hrd
  have hEtor : E ≤ frameTorus (toGH74Frame F) := fun y hy =>
    (mem_frameTorus_toGH74Frame F y).2 (htor y hy)
  obtain ⟨a, b, y₁, y₂, y₃, y₄, h₁, h₂, h₃, h₄, ea, eb, -, -, hab, -, -, -, -, hnorm⟩ :=
    exists_quaternion_derived_normalizing_plane hf hK hσ (toGH74Frame F) hr hr3 hrd hs hwι hEtor hEp
      hEc P hEP hPΩ
  have hw1 : w ≠ 1 := ne_one_of_inverts hr (by omega) (hwE x₁ hx₁E) (hEp x₁ hx₁E) hx₁1
  refine ⟨{
    E₀ := E, w := w, P := P, u := u, x₁ := x₁, x₀ := x₀, c := c, a := a, b := b,
    y₁ := y₁, y₂ := y₂, y₃ := y₃, y₄ := y₄, θ := θ, hEp := hEp, hEc := hEc, hww := hww,
    hw1 := hw1, hwJ := hwfix, hwE := hwE, hEP := hEP, hPc := hPc, hPΩ := hPΩ, hu := huu,
    hu1 := hu1, hx₁E := hx₁E, hx₁1 := hx₁1, huw := huw, hux := hux, hx₀E := hx₀E, hx₀1 := hx₀1,
    hcE := hcE, hc1 := hc1, hcJ := hcfix, hθker := hθker, hθw := hθw,
    hθx := fun t => Subgroup.mem_centralizer_singleton_iff.1
      (d4phiPx_le_centralizer sp (hθP t)),
    hθJ := hθfix, hθcard := hθcard, hθsimple := hθps, hy₁ := h₁, hy₂ := h₂, hy₃ := h₃, hy₄ := h₄,
    ha := ea, hb := eb, haE := fun x hx => (hnorm x hx).1, hbE := fun x hx => (hnorm x hx).2.2.1,
    hab := hab }⟩

end Frame

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
