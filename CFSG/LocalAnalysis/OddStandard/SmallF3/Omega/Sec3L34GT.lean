module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GTLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GTCenter
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GTSub
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Lift
public import CFSG.GH74.GLS.Balance.CompSwap

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec3_pocket_diag_transport {G : Type} [Group G] [Finite G] {v r : G} {D Δ : Subgroup G}
    (hr : orderOf r = 2) (hrv : r * v = v * r)
    (hD : IsComponentIn D (centralizer ({v} : Set G))) (hDF : InFStar D)
    (hne : CFSG.conjugate D r ≠ D)
    (hΔ : ∀ g : G, g ∈ Δ ↔ ∃ d ∈ D, g = d * (r * d * r⁻¹)) {b : G}
    (hb : IsI4PlusIn Δ b) :
    ∃ b₁ ∈ D, b = b₁ * (r * b₁ * r⁻¹) ∧ IsI4PlusIn D b₁ := by
  have hbΔ : b ∈ Δ := by
    obtain ⟨-, K, hbK, hKle, -, -⟩ := hb
    exact (hKle hbK).1
  have hrC : r ∈ centralizer ({v} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hrv
  have hDr : IsComponentIn (CFSG.conjugate D r) (centralizer ({v} : Set G)) := hD.conjugate hrC
  have hcomm : ∀ a ∈ D, ∀ c ∈ D, a * (r * c * r⁻¹) = (r * c * r⁻¹) * a := fun a ha c hc =>
    hD.commute_of_ne hDr (Ne.symm hne) a ha _ (sec63P_conj_mem_conjugate hr hc)
  obtain ⟨φ, hφ⟩ := CFSG.GH74.GLS.Balance.Comp.exists_diagHom hcomm
  have hker : φ.ker ≤ center ↥D := CFSG.GH74.GLS.Balance.Comp.diagHom_ker_le_center hcomm hφ
  have hφΔ : ∀ d : ↥D, φ d ∈ Δ := fun d => (hΔ _).mpr ⟨d, d.2, hφ d⟩
  let ψ : ↥D →* ↥Δ := φ.codRestrict Δ hφΔ
  have hψ : ∀ d : ↥D, ((ψ d : ↥Δ) : G) = (d : G) * (r * d * r⁻¹) := fun d => hφ d
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨g, hg⟩
    obtain ⟨d, hd, rfl⟩ := (hΔ g).mp hg
    exact ⟨⟨d, hd⟩, Subtype.ext (hψ ⟨d, hd⟩)⟩
  have hψker : ψ.ker = φ.ker := by
    ext d
    simp [MonoidHom.mem_ker, ψ, Subtype.ext_iff]
  have h2 : ∀ P : Subgroup ↥D, IsPGroup 2 ↥P → P ≤ ψ.ker → Nat.card ↥P ≤ 2 := by
    intro P hP hPker
    have hPc : P ≤ center ↥D := hψker ▸ hPker |>.trans hker
    have hPc' : ∀ n ∈ P.map D.subtype, ∀ a ∈ D, a * n = n * a := by
      rintro n ⟨p, hp, rfl⟩ a ha
      have := Subgroup.mem_center_iff.mp (hPc hp) ⟨a, ha⟩
      exact congrArg Subtype.val this
    have hP2 : IsPGroup 2 ↥(P.map D.subtype) :=
      hP.of_surjective (P.equivMapOfInjective D.subtype D.subtype_injective).toMonoidHom
        (P.equivMapOfInjective D.subtype D.subtype_injective).surjective
    have := l34g_card_le_two_of_central_two hDF (Subgroup.map_subtype_le P) hPc' hP2
    rwa [Subgroup.card_map_of_injective D.subtype_injective] at this
  obtain ⟨b₁, hb₁, hb₁I⟩ := l34g_lift ψ hψsurj (hψker ▸ hker) h2
    (l34g_isI4PlusIn_top_of_subtype hbΔ hb)
  refine ⟨(b₁ : G), b₁.2, ?_, isI4PlusIn_of_top b₁.2 hb₁I⟩
  have := congrArg Subtype.val hb₁
  rw [hψ] at this
  exact this.symm

end CFSG.OddStandard.SmallF3.Omega
