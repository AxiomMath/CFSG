module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Fus
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Hconj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410U
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Nrm

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

namespace Fz410Set

variable {G : Type} [Group G] [Finite G] {t : G} {L S T : Subgroup G}
  {x₁ x₂ lam rho tau s : G} {Z E W Q R P : Subgroup G}

private lemma fz410_case_exists_move {G : Type} [Group G] [Finite G] {W : Subgroup G} {u : G}
    (hu : u ∉ normalizer (W : Set G)) : ∃ w ∈ W, u * w * u⁻¹ ∉ W := by
  by_contra h
  have h' : ∀ w ∈ W, u * w * u⁻¹ ∈ W := by
    intro w hw
    by_contra hc
    exact h ⟨w, hw, hc⟩
  apply hu
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using h' y hy
  · rw [Subgroup.card_map_of_injective (MulAut.conj u).injective]

private lemma fz410_case_comm_mul_iff {G : Type} [Group G] {c x y : G}
    (hcx : c * x = x * c) : (c * y) * x = x * (c * y) ↔ y * x = x * y := by
  constructor
  · intro h
    have h' : c * (y * x) = c * (x * y) := by
      calc c * (y * x) = (c * y) * x := by group
        _ = x * (c * y) := h
        _ = c * (x * y) := by
              calc x * (c * y) = (x * c) * y := by group
                _ = (c * x) * y := by rw [hcx]
                _ = c * (x * y) := by group
    exact mul_left_cancel h'
  · intro h
    calc (c * y) * x = c * (y * x) := by group
      _ = c * (x * y) := by rw [h]
      _ = (c * x) * y := by group
      _ = (x * c) * y := by rw [hcx]
      _ = x * (c * y) := by group

variable (D : Fz410Set t L S T x₁ x₂ lam rho tau s Z E W Q R P)

include D

theorem exists_move : ∃ g ∈ fz410M R E, ∃ w ∈ W, g * w * g⁻¹ ∉ W := by
  obtain ⟨u, huN, huT, hp⟩ := fz410_exists_u D.str.pgroup_T D.not_sylow
  have huN2 : u ∉ fzN2 t x₁ x₂ := D.u_notin_N2 huN huT hp
  have huN3 : u ∈ normalizer (R : Set G) := D.u_mem_N3 huN
  have huinvN3 : u⁻¹ ∈ normalizer (R : Set G) := (normalizer (R : Set G)).inv_mem huN3
  have huNW : u ∉ normalizer (W : Set G) := by
    rw [D.hW]
    simpa only [fzN2] using huN2
  obtain ⟨w, hwW, hwmove⟩ := fz410_case_exists_move huNW
  rcases D.conjE huN3 with hA1 | hA2
  · refine ⟨u, ?_, w, hwW, hwmove⟩
    refine Subgroup.mem_inf.mpr ⟨huN3, ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 : u⁻¹ * (u * y * u⁻¹) * u = y := by group
    have := hA1 (u * y * u⁻¹)
    rwa [h1] at this
  · obtain ⟨a, haE, haZ⟩ := D.exists_E_not_Z
    have haP : a ∈ P := D.pf.EP haE
    have hB2 : ∀ b : G, u * b * u⁻¹ ∈ E ↔ b ∈ fz410F P t s := by
      rcases D.conjE huinvN3 with hB1 | hB2
      · exfalso
        have hxE : u * a * u⁻¹ ∈ E := by
          simpa [inv_inv] using (hB1 a).mpr haE
        have hxFu : u⁻¹ * (u * a * u⁻¹) * u = a := by group
        have hxF : u * a * u⁻¹ ∈ fz410F P t s :=
          (hA2 (u * a * u⁻¹)).mp (by rw [hxFu]; exact haE)
        have hxZ : u * a * u⁻¹ ∈ Z := D.facts.ef (u * a * u⁻¹) hxE hxF
        have hZmem : u⁻¹ * (u * a * u⁻¹) * (u⁻¹)⁻¹ ∈ Z :=
          (D.nrmZ huinvN3 (u * a * u⁻¹)).mpr hxZ
        have h2 : u⁻¹ * (u * a * u⁻¹) * (u⁻¹)⁻¹ = a := by group
        rw [h2] at hZmem
        exact haZ hZmem
      · intro b
        simpa [inv_inv] using hB2 b
    set a' : G := u⁻¹ * a * u with ha'
    have ha'F : a' ∈ fz410F P t s := by
      have h := (hB2 (u⁻¹ * a * u)).mp
        (by rw [show u * (u⁻¹ * a * u) * u⁻¹ = a by group]; exact haE)
      simpa [ha'] using h
    have ha'P : a' ∈ P := (Subgroup.mem_inf.mp ha'F).1
    set i0 : G := u * t * u⁻¹ with hi0
    have hi0R : i0 ∈ R := by rw [hi0]; exact D.facts.charR u huN t D.t_mem_R
    have hi0notP : i0 ∉ P := by
      rw [hi0]
      intro hcon
      exact D.t_notin_P ((D.nrmP huN3 t).1 hcon)
    have hi0sq : i0 ^ 2 = 1 := by
      rw [hi0, pow_two]
      calc (u * t * u⁻¹) * (u * t * u⁻¹) = u * t * t * u⁻¹ := by group
        _ = u * t ^ 2 * u⁻¹ := by rw [pow_two]; group
        _ = u * 1 * u⁻¹ := by rw [D.str.t_sq]
        _ = 1 := by group
    have hcomm_i0 : ∀ x ∈ P, (i0 * x = x * i0 ↔ x ∈ fz410F P t s) := by
      intro x hxP
      have hxP' : u⁻¹ * x * u ∈ P := by
        have := (D.nrmP huinvN3 x).mpr hxP
        simpa [inv_inv] using this
      have hconj : i0 * x = x * i0 ↔ t * (u⁻¹ * x * u) = (u⁻¹ * x * u) * t := by
        rw [hi0]
        constructor
        · intro h
          have h' := congrArg (fun y => u⁻¹ * y * u) h
          calc t * (u⁻¹ * x * u) = u⁻¹ * (u * t * u⁻¹ * x) * u := by group
            _ = u⁻¹ * (x * (u * t * u⁻¹)) * u := h'
            _ = (u⁻¹ * x * u) * t := by group
        · intro h
          have h' := congrArg (fun y => u * y * u⁻¹) h
          calc (u * t * u⁻¹) * x = u * (t * (u⁻¹ * x * u)) * u⁻¹ := by group
            _ = u * ((u⁻¹ * x * u) * t) * u⁻¹ := h'
            _ = x * (u * t * u⁻¹) := by group
      have hEcent : t * (u⁻¹ * x * u) = (u⁻¹ * x * u) * t ↔ u⁻¹ * x * u ∈ E :=
        (eq_comm).trans (D.E_cent (u⁻¹ * x * u) hxP')
      exact hconj.trans (hEcent.trans (hA2 x))
    obtain ⟨e0, he0E, hi0eq⟩ := D.facts.invF i0 hi0R hi0notP hi0sq hcomm_i0
    set e1 : G := a * e0 with he1
    have he1E : e1 ∈ E := E.mul_mem haE he0E
    have hi1eq : e1 * (t * s) = a * i0 := by
      rw [he1]
      calc a * e0 * (t * s) = a * (e0 * (t * s)) := by group
        _ = a * i0 := by rw [← hi0eq]
    obtain ⟨h0, -, hconj0⟩ := D.Hconj e0 he0E
    obtain ⟨h1, -, hconj1⟩ := D.Hconj e1 he1E
    have hg't : (h1 * h0⁻¹ * u) * t * (h1 * h0⁻¹ * u)⁻¹ = e1 * (t * s) := by
      have hh0' : h0⁻¹ * i0 * h0 = t * s := by
        rw [hi0eq, ← hconj0]
        group
      calc (h1 * h0⁻¹ * u) * t * (h1 * h0⁻¹ * u)⁻¹
          = h1 * (h0⁻¹ * (u * t * u⁻¹) * h0) * h1⁻¹ := by group
        _ = h1 * (h0⁻¹ * i0 * h0) * h1⁻¹ := by rw [← hi0]
        _ = h1 * (t * s) * h1⁻¹ := by rw [hh0']
        _ = e1 * (t * s) := hconj1
    obtain ⟨n1, hn1N3, z1, hz1Z, hn1t⟩ := D.fusion he1E hg't
    set g : G := u⁻¹ * n1 with hg
    have hinv_n1 : n1⁻¹ ∈ normalizer (R : Set G) :=
      (normalizer (R : Set G)).inv_mem hn1N3
    have hz1E : z1 ∈ E := D.str.ZE hz1Z
    have hcE : a * z1 ∈ E := E.mul_mem haE hz1E
    have hiz : i0 * z1 = z1 * i0 := by
      have h := D.str.R_Z i0 hi0R z1 hz1Z
      calc i0 * z1 = (i0 * z1 * i0⁻¹) * i0 := by group
        _ = z1 * i0 := by rw [h]
    have hn1t' : n1 * t * n1⁻¹ = (a * z1) * i0 := by
      rw [hn1t, hi1eq]
      calc a * i0 * z1 = a * (i0 * z1) := by group
        _ = a * (z1 * i0) := by rw [hiz]
        _ = (a * z1) * i0 := by group
    have hn1_conjE : ∀ x : G, n1⁻¹ * x * n1 ∈ E ↔ x ∈ fz410F P t s := by
      intro x
      by_cases hxP : x ∈ P
      · have hxP' : n1⁻¹ * x * n1 ∈ P := by
          have := (D.nrmP hinv_n1 x).mpr hxP
          simpa [inv_inv] using this
        have hEcent := D.E_cent (n1⁻¹ * x * n1) hxP'
        have hconj : (n1⁻¹ * x * n1) * t = t * (n1⁻¹ * x * n1) ↔
            x * (n1 * t * n1⁻¹) = (n1 * t * n1⁻¹) * x := by
          constructor
          · intro h
            have h' := congrArg (fun y => n1 * y * n1⁻¹) h
            calc x * (n1 * t * n1⁻¹) = n1 * ((n1⁻¹ * x * n1) * t) * n1⁻¹ := by group
              _ = n1 * (t * (n1⁻¹ * x * n1)) * n1⁻¹ := h'
              _ = (n1 * t * n1⁻¹) * x := by group
          · intro h
            have h' := congrArg (fun y => n1⁻¹ * y * n1) h
            calc (n1⁻¹ * x * n1) * t = n1⁻¹ * (x * (n1 * t * n1⁻¹)) * n1 := by group
              _ = n1⁻¹ * ((n1 * t * n1⁻¹) * x) * n1 := h'
              _ = t * (n1⁻¹ * x * n1) := by group
        have hrewrite : x * (n1 * t * n1⁻¹) = (n1 * t * n1⁻¹) * x ↔
            x * ((a * z1) * i0) = ((a * z1) * i0) * x := by
          simp only [hn1t']
        have hcomm := fz410_case_comm_mul_iff (c := a * z1) (x := x) (y := i0)
          (D.facts.P_comm (a * z1) (D.pf.EP hcE) x hxP)
        exact hEcent.symm.trans
          (hconj.trans (hrewrite.trans (eq_comm.trans (hcomm.trans (hcomm_i0 x hxP)))))
      · constructor
        · intro hcon
          exact absurd ((D.nrmP hinv_n1 x).mp (by simpa [inv_inv] using D.pf.EP hcon)) hxP
        · intro hF
          exact absurd (Subgroup.mem_inf.mp hF).1 hxP
    have hgN3 : g ∈ normalizer (R : Set G) := by
      rw [hg]
      exact (normalizer (R : Set G)).mul_mem huinvN3 hn1N3
    have hgE : g ∈ normalizer (E : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hgform : g * y * g⁻¹ = u⁻¹ * (n1 * y * n1⁻¹) * u := by rw [hg]; group
      rw [hgform]
      have h1 : y ∈ E ↔ (n1 * y * n1⁻¹) ∈ fz410F P t s := by
        have := hn1_conjE (n1 * y * n1⁻¹)
        rwa [show n1⁻¹ * (n1 * y * n1⁻¹) * n1 = y by group] at this
      have h2 : (n1 * y * n1⁻¹) ∈ fz410F P t s ↔ u⁻¹ * (n1 * y * n1⁻¹) * u ∈ E :=
        (hA2 (n1 * y * n1⁻¹)).symm
      exact h1.trans h2
    set z' : G := u⁻¹ * z1 * u with hz'
    have hz'Z : z' ∈ Z := by
      have := (D.nrmZ huinvN3 z1).mpr hz1Z
      simpa [hz', inv_inv] using this
    have hui0 : u⁻¹ * i0 * u = t := by rw [hi0]; group
    have hz't : z' * t = t * z' :=
      D.str.W_comm z' (D.str.EW (D.str.ZE hz'Z)) t D.str.t_mem
    have hgt : g * t * g⁻¹ = a' * (t * z') := by
      calc g * t * g⁻¹ = u⁻¹ * (n1 * t * n1⁻¹) * u := by rw [hg]; group
        _ = u⁻¹ * ((a * z1) * i0) * u := by rw [hn1t']
        _ = a' * z' * t := by
              rw [ha', hz', ← hui0]
              group
        _ = a' * (t * z') := by
            rw [show a' * z' * t = a' * (z' * t) by group, hz't]
    have hnotW : g * t * g⁻¹ ∉ W := by
      intro hW
      have htz'W : t * z' ∈ W := W.mul_mem D.str.t_mem (D.str.EW (D.str.ZE hz'Z))
      have ha'W : a' ∈ W := by
        have h1 : a' = (g * t * g⁻¹) * (t * z')⁻¹ := by rw [hgt]; group
        rw [h1]
        exact W.mul_mem hW (W.inv_mem htz'W)
      have ha'E : a' ∈ E := D.pf.PW a' ha'P ha'W
      have ha'Z : a' ∈ Z := D.facts.ef a' ha'E ha'F
      have hZmem : u * a' * u⁻¹ ∈ Z := (D.nrmZ huN3 a').mpr ha'Z
      have hua : u * a' * u⁻¹ = a := by rw [ha']; group
      rw [hua] at hZmem
      exact haZ hZmem
    exact ⟨g, Subgroup.mem_inf.mpr ⟨hgN3, hgE⟩, t, D.str.t_mem, hnotW⟩

end Fz410Set

end CFSG.OddStandard.SmallF3.FritzII
