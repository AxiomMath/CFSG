module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GT
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GDiag
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GPocketP
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GConj

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem l34g_diag_step [Finite G] {v x u : G} {D I : Subgroup G} (hv : orderOf v = 2)
    (hx : orderOf x = 2) (hxv : x * v = v * x)
    (hDv : IsComponentIn D (centralizer ({v} : Set G))) (huD : u ∈ D) (hu4 : IsI4PlusIn D u)
    (hI : IsComponentIn I (centralizer ({u} : Set G))) (hIF : InFStar I)
    (hle : CFSG.conjugate D x ≤ I ⊔ CFSG.conjugate I v) (hIv : CFSG.conjugate I v ≠ I) :
    ∃ (u₂ : G) (K₂ : Subgroup G), Sec3PocketData (x⁻¹ * u * x) (CFSG.conjugate I x) u₂ K₂ ∧
      CFSG.conjugate (CFSG.conjugate I x) v ≠ CFSG.conjugate I x := by
  let D₂ : Subgroup G := CFSG.conjugate I x
  let v₂ : G := x⁻¹ * u * x
  have hD₂def : D₂ = CFSG.conjugate I x := rfl
  have hu : orderOf u = 2 := hu4.1
  have hvu : v * u = u * v :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hDv.1 huD)).symm
  have hvx_inv : x⁻¹ * v = v * x⁻¹ := by
    calc x⁻¹ * v = x⁻¹ * (v * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * v) * x⁻¹ := by rw [← hxv]
      _ = v * x⁻¹ := by group
  have hvv₂ : v * v₂ = v₂ * v := by
    dsimp [v₂]
    calc v * (x⁻¹ * u * x) = (v * x⁻¹) * u * x := by group
      _ = (x⁻¹ * v) * u * x := by rw [hvx_inv]
      _ = x⁻¹ * (v * u) * x := by group
      _ = x⁻¹ * (u * v) * x := by rw [hvu]
      _ = x⁻¹ * u * (v * x) := by group
      _ = x⁻¹ * u * (x * v) := by rw [← hxv]
      _ = (x⁻¹ * u * x) * v := by group
  have hv₂ : orderOf v₂ = 2 := by
    dsimp [v₂]
    have h2 := MulEquiv.orderOf_eq (MulAut.conj x⁻¹) u
    rw [MulAut.conj_apply, inv_inv, hu] at h2
    exact h2
  have hD₂ : IsComponentIn D₂ (centralizer ({v₂} : Set G)) :=
    l34g_isComponentIn_conjugate_centralizer hI x
  have hD₂F : InFStar D₂ := hIF.conjugate x
  have hD₂v : IsComponentIn (CFSG.conjugate D₂ v) (centralizer ({v₂} : Set G)) :=
    hD₂.conjugate (Subgroup.mem_centralizer_singleton_iff.mpr hvv₂)
  have hD₂v_eq : CFSG.conjugate D₂ v = CFSG.conjugate (CFSG.conjugate I v) x := by
    dsimp [D₂]
    rw [l34g_conjugate_conjugate I x v, hxv, ← l34g_conjugate_conjugate I v x]
  have hne : CFSG.conjugate D₂ v ≠ D₂ := by
    intro heq
    have heq' : CFSG.conjugate (CFSG.conjugate I v) x = CFSG.conjugate I x := by
      calc CFSG.conjugate (CFSG.conjugate I v) x = CFSG.conjugate D₂ v := hD₂v_eq.symm
        _ = D₂ := heq
        _ = CFSG.conjugate I x := hD₂def
    have hcongr := congrArg (fun K : Subgroup G => CFSG.conjugate K x) heq'
    rw [l34g_conjugate_conjugate_self (CFSG.conjugate I v) hx,
        l34g_conjugate_conjugate_self I hx] at hcongr
    exact hIv hcongr
  have hconj_sup : ∀ (A B : Subgroup G) (g : G),
      CFSG.conjugate (A ⊔ B) g = CFSG.conjugate A g ⊔ CFSG.conjugate B g := by
    intro A B g
    unfold CFSG.conjugate
    exact Subgroup.map_sup A B _
  have hsup : CFSG.conjugate (I ⊔ CFSG.conjugate I v) x = D₂ ⊔ CFSG.conjugate D₂ v := by
    rw [hconj_sup]
    rw [hD₂def.symm, hD₂v_eq.symm]
  have hle' : D ≤ D₂ ⊔ CFSG.conjugate D₂ v := by
    have hmono : CFSG.conjugate (CFSG.conjugate D x) x ≤
        CFSG.conjugate (I ⊔ CFSG.conjugate I v) x := Subgroup.map_mono hle
    rw [l34g_conjugate_conjugate_self D hx] at hmono
    rwa [hsup] at hmono
  have hW : IsComponentIn D ((D₂ ⊔ CFSG.conjugate D₂ v) ⊓ centralizer ({v} : Set G)) :=
    hDv.mono (le_inf hle' hDv.1) inf_le_right
  have hcomm : ∀ a ∈ D₂, ∀ c ∈ CFSG.conjugate D₂ v, a * c = c * a :=
    hD₂.commute_of_ne hD₂v (Ne.symm hne)
  have hΔ : ∀ g : G, g ∈ D ↔ ∃ a ∈ D₂, g = a * (v * a * v⁻¹) :=
    l34g_diag_eq hv hD₂.isQuasisimple hcomm hle' hW
  obtain ⟨u₂, -, -, hu₂I4⟩ :=
    sec3_pocket_diag_transport hv hvv₂ hD₂ hD₂F hne hΔ hu4
  obtain ⟨hu₂2, K₂, hK₂⟩ := hu₂I4
  exact ⟨u₂, K₂, l34g_pocketData_of_pocketIn hv₂ hD₂ hD₂F hu₂2 hK₂, hne⟩

end CFSG.OddStandard.SmallF3.Omega
