module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf34Struct
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf34NoGraph
public import CFSG.ClassicalInvolution.Asc77.AscS24BEnd

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
namespace Ctx8F
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8F Ω K K' W S R R' z u)

include C in

theorem false_of₄ [CoreLike G] [Fact (CFSG.ClassicalInvolution.Q8P.P24.Hyp51TwinInnerAt Ω)]
    (h3 : H3) (hng : NoGraph) (hSP : ¬ (S : Subgroup G) ≤ MGrp Ω W) : False := by
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
  have he1 : e ≠ 1 := fun h => heP (h ▸ ((S : Subgroup G) ⊓ MGrp Ω W).one_mem)
  have hne : ∀ g : G, g * z * g⁻¹ ≠ e :=
    C.ne_conj_z C.hs.stand.mem C.hRsyl C.hzK heR hez
  refine false_of_transfer_ker C.hs.stand C.hs.stand.mem C.hRsyl S
    (N := (S : Subgroup G) ⊓ MGrp Ω W) hab heS heP (by rw [pow_two]; exact he2) ?_ ?_
  · intro g hg
    have hbS : g⁻¹ * e * g ∈ (S : Subgroup G) :=
      hg e ⟨heS, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    have hbP : g⁻¹ * e * g ∉ (S : Subgroup G) ⊓ MGrp Ω W :=
      C.not_mem_P_conj heS (fun y hy => (Subgroup.mem_centralizer_singleton_iff.mp (heR hy)).symm)
        he2 he1 hne hg
    have hb2 : (g⁻¹ * e * g) * (g⁻¹ * e * g) = 1 := by
      calc (g⁻¹ * e * g) * (g⁻¹ * e * g) = g⁻¹ * (e * e) * g := by group
        _ = 1 := by rw [he2]; group
    have h := huniq _ hbS _ heS (by rw [hb2]; exact Subgroup.one_mem _)
      (by rw [he2]; exact Subgroup.one_mem _) hbP heP
    have h' := Subgroup.inv_mem _ h
    simpa [mul_inv_rev] using h'
  · intro A _ ϕ hϕ
    have hε2 : ϕ ⟨e, heS⟩ ^ 2 = 1 := by
      rw [← map_pow]
      have : (⟨e, heS⟩ : (S : Subgroup G)) ^ 2 = 1 := Subtype.ext (by simp [pow_two, he2])
      rw [this, map_one]
    have hε1 : ϕ ⟨e, heS⟩ ≠ 1 := fun h => heP (((hϕ _).mp h))
    refine C.transfer_kills_R ϕ (ϕ ⟨e, heS⟩) hε2 hε1 (fun s hs => (hϕ s).mpr hs) (fun s hs2 => ?_)
    by_cases hsP : (s : G) ∈ (S : Subgroup G) ⊓ MGrp Ω W
    · exact Or.inl ((hϕ s).mpr hsP)
    · right
      have h := huniq _ s.2 _ heS (by rw [hs2]; exact Subgroup.one_mem _)
        (by rw [he2]; exact Subgroup.one_mem _) hsP heP
      have h1 : ϕ (s⁻¹ * ⟨e, heS⟩) = 1 := (hϕ _).mpr h
      rw [map_mul, map_inv, inv_mul_eq_one] at h1
      exact h1

end Ctx8F
end S24B

end Asc77

end CFSG.ClassicalInvolution.Q8P

namespace CFSG.ClassicalInvolution.Q8P.Asc77

open CFSG.ClassicalInvolution.Q8P


theorem S24B.c24_9_core_of₄ (h3 : S24B.H3) (hng : S24B.NoGraph) : C24_9_core := by
  intro G _ _ _ Ω K K' W S R R' z u hI h h8 hSP
  obtain ⟨C⟩ := S24B.Ctx8F.nonempty h h8
  exact C.false_of₄ h3 hng hSP

theorem S24B.c24_9_core_of_h3 (h3 : S24B.H3) : C24_9_core :=
  S24B.c24_9_core_of₄ h3 (S24.noGraph_of_h3 h3)

end CFSG.ClassicalInvolution.Q8P.Asc77
