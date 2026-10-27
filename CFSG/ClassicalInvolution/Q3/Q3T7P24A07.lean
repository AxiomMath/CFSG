module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24A05
public import CFSG.ClassicalInvolution.Q3.Q3T7P24A06
public import CFSG.ClassicalInvolution.Asc77.AscS24CGraph
public import CFSG.ClassicalInvolution.Asc77.AscS24BEnd
import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF07h

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace S24
open CFSG.ClassicalInvolution.Asc77.S24
section Ctx
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8 Ω K K' W S R R' z u)
include C in

theorem acts_pm {y : G} (hyS : y ∈ (S : Subgroup G)) (hT : S24B.TrivMu Ω W y) :
    (∀ w ∈ W, y * w * y⁻¹ = w) ∨ (∀ w ∈ W, y * w * y⁻¹ = w⁻¹) := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.acts_pm C.toFrame hyS hT
include C in

theorem exists_centralizes_r {y : G} (hyS : y ∈ (S : Subgroup G)) (hT : S24B.TrivMu Ω W y)
    (hinv : ∀ w ∈ W, y * w * y⁻¹ = w⁻¹) :
    ∃ k : ℤ, (y * C.D.x₃ ^ k) * C.D.F.ρ.r = C.D.F.ρ.r * (y * C.D.x₃ ^ k) := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.exists_centralizes_r C.toFrame hyS
    hT hinv
include C in

theorem graph_sq [IsSimpleGroup G] (h3 : S24B.H3) {c : G} (hcS : c ∈ (S : Subgroup G))
    (hT : S24B.TrivMu Ω W c) (hinv : ∀ w ∈ W, c * w * c⁻¹ = w⁻¹) : c * c = 1 := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.graph_sq C.toFrame
    (h3 G Ω K K' W S R R' z u C.hs C.hd C.h8 C.D C.hK C.hK' C.hR C.hR') hcS hT hinv
include C in

theorem not_mem_sZero {c : G} (hinv : ∀ w ∈ W, c * w * c⁻¹ = w⁻¹) : c ∉ sZero Ω W S := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.not_mem_sZero C.toFrame hinv
include C in

theorem mem_or_inv_mul_mem_sZero {c y : G} (hcS : c ∈ (S : Subgroup G))
    (hinv : ∀ w ∈ W, c * w * c⁻¹ = w⁻¹) (hyS : y ∈ (S : Subgroup G)) :
    y ∈ sZero Ω W S ∨ c⁻¹ * y ∈ sZero Ω W S := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.mem_or_inv_mul_mem_sZero C.toFrame
    hcS hinv hyS
include C in

theorem commutator_mem_sZero {c : G} (hcS : c ∈ (S : Subgroup G))
    (hinv : ∀ w ∈ W, c * w * c⁻¹ = w⁻¹) :
    ∀ y₁ ∈ (S : Subgroup G), ∀ y₂ ∈ (S : Subgroup G), y₁ * y₂ * y₁⁻¹ * y₂⁻¹ ∈ sZero Ω W S := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.commutator_mem_sZero C.toFrame hcS
    hinv
end Ctx
end S24
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
namespace Ctx8
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8 Ω K K' W S R R' z u)

theorem exists_gen [IsSimpleGroup G] (h3 : H3) (hng : NoGraph)
    (hSP : ¬ (S : Subgroup G) ≤ MGrp Ω W) :
    ∃ g₀ ∈ (S : Subgroup G), g₀ ^ 4 ∈ (S : Subgroup G) ⊓ MGrp Ω W ∧
      (∀ y ∈ (S : Subgroup G), ∃ k : ℤ, (g₀ ^ k)⁻¹ * y ∈ (S : Subgroup G) ⊓ MGrp Ω W) ∧
      ∃ d ∈ C.Dg, d * d = z := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.exists_gen C.toFrame
    (h3 G Ω K K' W S R R' z u C.hs C.hd C.h8 C.D C.hK C.hK' C.hR C.hR')
    (hng G Ω K K' W S R R' z u C.hs C.hd C.h8) hSP
end Ctx8
end S24B
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G]
variable [Finite G] {Ω : Set (Subgroup G)}
namespace Ctx8
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8 Ω K K' W S R R' z u)
include C in

theorem false_of [IsSimpleGroup G] (h3 : H3) (hng : NoGraph)
    (hSP : ¬ (S : Subgroup G) ≤ MGrp Ω W) : False := by
  obtain ⟨g₀, hg₀S, hg₀4, hgen, d, hd, hdd⟩ := C.exists_gen h3 hng hSP
  obtain ⟨hab, huniq⟩ := cyc_quot (fun g hg x hx => C.P_normal hg hx) hg₀S hg₀4 hgen
  have hdA := C.Dg_le_A hd
  have hdS : d ∈ (S : Subgroup G) := C.A_le_S hdA
  have hx₂P : C.D.x₂ ∈ (S : Subgroup G) ⊓ MGrp Ω W := C.W_le_P C.D.x₂_mem
  have hdP : d ∉ (S : Subgroup G) ⊓ MGrp Ω W := by
    intro h
    rcases C.Dg_mem_P hd h with h' | h'
    · rw [h', one_mul] at hdd
      exact C.hzK.ne_one hdd.symm
    · rw [h', C.hzK.sq] at hdd
      exact C.hzK.ne_one hdd.symm
  obtain ⟨e, he⟩ : ∃ e, e = d * C.D.x₂ := ⟨_, rfl⟩
  have heS : e ∈ (S : Subgroup G) := he ▸ (S : Subgroup G).mul_mem hdS hx₂P.1
  have heP : e ∉ (S : Subgroup G) ⊓ MGrp Ω W := by
    intro h
    apply hdP
    have e1 : d = e * C.D.x₂⁻¹ := by rw [he]; group
    rw [e1]
    exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ hx₂P)
  have hcx : d * C.D.x₂ = C.D.x₂ * d :=
    Subgroup.mem_centralizer_singleton_iff.mp (C.A_le_centralizer_x₂ hdA)
  have he2 : e * e = 1 := by
    calc e * e = d * (C.D.x₂ * d) * C.D.x₂ := by rw [he]; group
      _ = d * (d * C.D.x₂) * C.D.x₂ := by rw [hcx]
      _ = (d * d) * (C.D.x₂ * C.D.x₂) := by group
      _ = 1 := by rw [hdd, ← sq, C.x₂_sq, C.hzK.sq]
  have heR : R ≤ Subgroup.centralizer ({e} : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : v * d = d * v := Subgroup.mem_centralizer_iff.mp ((C.mem_A).mp hdA).2.2.1 v hv
    have h2 : v * C.D.x₂ = C.D.x₂ * v := C.commutes_R_R' v hv _ C.x₂_mem_R'
    calc v * e = v * d * C.D.x₂ := by rw [he, mul_assoc]
      _ = d * (v * C.D.x₂) := by rw [h1, mul_assoc]
      _ = e * v := by rw [h2, he, mul_assoc]
  have hez : e ≠ z := fun h => heP (h ▸ C.z_mem_P)
  have hne : ∀ g : G, g * z * g⁻¹ ≠ e :=
    C.ne_conj_z C.hs.stand.mem C.hRsyl C.hzK heR hez
  refine AschTight.S1916.false_of_transfer (T7C.exists_not_commute_of_stand C.hs.stand) S
    (P := (S : Subgroup G) ⊓ MGrp Ω W) ?_ hab heS heP he2 ?_
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => C.P_normal hg hx
    · intro hx
      have e1 : x = g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ := by group
      rw [e1]
      exact C.P_normal ((S : Subgroup G).inv_mem hg) hx
  · intro g hg
    have hb2 : (g⁻¹ * e * g) * (g⁻¹ * e * g) = 1 := by
      calc (g⁻¹ * e * g) * (g⁻¹ * e * g) = g⁻¹ * (e * e) * g := by group
        _ = 1 := by rw [he2]; group
    have hbP : g⁻¹ * e * g ∉ (S : Subgroup G) ⊓ MGrp Ω W := by
      intro hbP
      have hb1 : g⁻¹ * e * g ≠ 1 := by
        intro h1
        apply heP
        have e1 : e = g * (g⁻¹ * e * g) * g⁻¹ := by group
        rw [e1, h1, mul_one, mul_inv_cancel]
        exact Subgroup.one_mem _
      obtain ⟨g', hg'⟩ := C.kc hg hbP.2 hb2 hb1
      apply hne (g * g')
      calc g * g' * z * (g * g')⁻¹ = g * (g' * z * g'⁻¹) * g⁻¹ := by group
        _ = e := by rw [hg']; group
    exact huniq _ hg _ heS (by rw [hb2]; exact Subgroup.one_mem _)
      (by rw [he2]; exact Subgroup.one_mem _) hbP heP
end Ctx8

theorem c24_9_core_of (h3 : H3) (hng : NoGraph) : C24_9_core := by
  intro G _ _ _ Ω K K' W S R R' z u h h8 hSP
  obtain ⟨C⟩ := Ctx8.nonempty h.std.setting h.data h8
  exact C.false_of h3 hng hSP
end S24B
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
