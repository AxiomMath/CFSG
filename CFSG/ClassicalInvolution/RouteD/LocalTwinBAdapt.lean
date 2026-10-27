module

public import CFSG.ClassicalInvolution.RouteD.LocalTwinBWeakChain
public import CFSG.ClassicalInvolution.RouteD.LocalTwinAdapt

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.CurtisTits CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub modelUniv InClass LocalOddCentral)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair)

variable {p f : ℕ} [Fact p.Prime]

theorem PartnerPatternBPair.of_toral {G : Type} [Group G] [Finite G] {m : ℕ} (hm : 3 ≤ m)
    {Ω : Set (Subgroup G)} {z : G} {K β : Subgroup G} (c : TCtx p f .POmegaOdd m Ω K z) {t : G}
    (ht : t * z * t⁻¹ = z) {j : Fin m → Subgroup G}
    (hjΩ : ∀ a : Fin m, a.val + 1 < m → j a ∈ Ω) (hjY : ∀ a, j a ≤ locLayer Ω z)
    (hjK : ∀ a, Commutes K (j a)) (hjperf : ∀ a, ⁅j a, j a⁆ = j a)
    (hjc : ∀ a b : Fin m, a.val + 1 < b.val → Commutes (j a) (j b))
    (hjp : ∀ a b : Fin m, a.val + 1 = b.val → b.val + 1 < m →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (j a) (j b))
    (hjsp : ∀ a b : Fin m, a.val + 2 = m → b.val + 1 = m →
      ∃ W, SymplecticBlockPair (GaloisField p f) W (j a) (j b))
    (hjimg : ∀ a : Fin m, locImg Ω z (j a) =
      (rankOne (modelUniv .POmegaOdd m p f Fact.out).D.rootGroup a).map c.d.ψ)
    (v : Fin m → ZMod 2)
    (hT : ∀ γ ∈ (modelUniv .POmegaOdd m p f Fact.out).D.roots,
      (∀ x ∈ ((modelUniv .POmegaOdd m p f Fact.out).D.rootGroup γ ⊔
          (modelUniv .POmegaOdd m p f Fact.out).D.rootGroup (-γ)).map c.d.ψ,
        Gaps.locAut c.hΩ.conjInvariant ht x = x) ↔ charOf v γ = 0)
    (hE : CharReach (modelUniv .POmegaOdd m p f Fact.out).D.cartan v
      (Pi.single (⟨0, by omega⟩ : Fin m) 1))
    (hS : ∀ y ∈ locLayer Ω z,
      (∀ b : Fin m, (∀ x ∈ locImg Ω z (conjSub y (j b)),
        Gaps.locAut c.hΩ.conjInvariant ht x = x) ↔ b.val ≠ 0) →
      ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β
        (conjSub y (j ⟨0, by omega⟩))) :
    PartnerPatternBPair p f m Ω K β t := by
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr c.hf
  have hadm : StatedLieAdmissible .POmegaOdd m p f := ⟨Fact.out, hf1, hm, c.hp2⟩
  obtain ⟨n, H, hct, -⟩ := ModelFacts.hasBruhatDatum .POmegaOdd m p f Fact.out trivial hadm
  obtain ⟨y, hy, hfix⟩ := c.exists_adapted_y_of_reach hct ht v hT hE hjimg
  have hfix' : ∀ b : Fin m, (∀ x ∈ locImg Ω z (conjSub y (j b)),
      Gaps.locAut c.hΩ.conjInvariant ht x = x) ↔ b.val ≠ 0 := fun b => by
    rw [hfix b]
    show (Pi.single (⟨0, by omega⟩ : Fin m) (1 : ZMod 2) : Fin m → ZMod 2) b = 0 ↔ b.val ≠ 0
    by_cases h : b = (⟨0, by omega⟩ : Fin m)
    · subst h
      simp
    · have : b.val ≠ 0 := fun h0 => h (Fin.ext h0)
      simp [h, this]
  refine PartnerPatternBPair.of_locAut c.hΩ c.hP1 hjΩ hjY hjK hjperf c.locLayer_le_normalizer hjc
    hjp hjsp hy ht (fun a ha x hx => (hfix' a).mpr (by omega) x hx) ?_
  intro a ha
  have h0 : a = (⟨0, by omega⟩ : Fin m) := Fin.ext ha
  rw [h0]
  exact hS y hy hfix'

end CFSG.ClassicalInvolution.RouteD
