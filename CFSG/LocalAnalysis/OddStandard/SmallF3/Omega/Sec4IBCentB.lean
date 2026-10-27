module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBTrans
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ZAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem sec4I_centB (hL : IsOmega7Group L) {P B : Subgroup G} (hP : IsSylow2Of P L)
    (hB : IsMaxElemAbelianIn P B) {x : G} (hx : x ∈ normalizer (L : Set G))
    (hxB : ∀ b ∈ B, x * b = b * x) : x ∈ B ⊔ centralizer (L : Set G) := by
  obtain ⟨e⟩ := sec4I_exists_model hL
  obtain ⟨fr, hfr⟩ := sec4I_exists_frame_good (sec4IRho_isSylow2Of hL e hP)
  have hBeq : B = sec4ILiftB e fr P := sec4ILift_unique hL e hP hfr B hB
  subst hBeq
  have hmap := sec4ILift_map_eq hL e hP hfr
  have hact : Sec4IActs e x (sec4ZAct e ⟨x, hx⟩) := sec4ZAct_spec e ⟨x, hx⟩
  have hcent : sec4ZAct e ⟨x, hx⟩ ∈
      Subgroup.centralizer (sec4IB0 fr : Set (ProjOrth Sec4IQ)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [← hmap] at hy
    obtain ⟨b, hb, rfl⟩ := hy
    have hbB : (b : G) ∈ sec4ILiftB e fr P := hb
    have hcomm : x * (b : G) = (b : G) * x := hxB b hbB
    have h1 := hact.2 b b (by rw [hcomm]; group)
    change sec4IRho e b * sec4ZAct e ⟨x, hx⟩ = sec4ZAct e ⟨x, hx⟩ * sec4IRho e b
    have h2 : sec4IRho e b = sec4ZAct e ⟨x, hx⟩ * sec4IRho e b * (sec4ZAct e ⟨x, hx⟩)⁻¹ := h1
    calc sec4IRho e b * sec4ZAct e ⟨x, hx⟩
        = (sec4ZAct e ⟨x, hx⟩ * sec4IRho e b * (sec4ZAct e ⟨x, hx⟩)⁻¹) *
            sec4ZAct e ⟨x, hx⟩ := by rw [← h2]
      _ = sec4ZAct e ⟨x, hx⟩ * sec4IRho e b := by group
  have ha0 : sec4ZAct e ⟨x, hx⟩ ∈ sec4IB0 fr := by
    rw [← sec4I_centralizer_B0 sec4IQ_nondegenerate fr]
    exact hcent
  rw [← hmap] at ha0
  obtain ⟨b₀, hb₀, hb₀a⟩ := ha0
  have hb₀B : (b₀ : G) ∈ sec4ILiftB e fr P := hb₀
  have hactb : Sec4IActs e (b₀ : G) (sec4ZAct e ⟨x, hx⟩) := by
    rw [← hb₀a]
    exact Sec4IActs.of_mem e b₀.2
  have hact' : Sec4IActs e ((b₀ : G)⁻¹ * x) ((sec4ZAct e ⟨x, hx⟩)⁻¹ * sec4ZAct e ⟨x, hx⟩) :=
    hactb.inv.mul hact
  rw [inv_mul_cancel] at hact'
  have hcentL : (b₀ : G)⁻¹ * x ∈ centralizer (L : Set G) := (Sec4IActs.eq_one_iff hL hact').mp rfl
  have hxeq : x = (b₀ : G) * ((b₀ : G)⁻¹ * x) := by group
  rw [hxeq]
  exact Subgroup.mul_mem_sup hb₀B hcentL

end CFSG.OddStandard.SmallF3.Omega
