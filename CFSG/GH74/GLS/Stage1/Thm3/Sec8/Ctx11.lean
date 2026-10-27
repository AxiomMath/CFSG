module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx3

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem z_comm (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {c : G} (hc : c ∈ S) :
    z * c = c * z :=
  (Subgroup.mem_centralizer_iff.1 (hs.S_le_C hII hc)) z (Set.mem_singleton z)

theorem mem_W_iff (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {s : G} :
    s ∈ Wsub S U ↔ s ∈ S ∧ s * u = u * s := by
  constructor
  · intro h1
    exact ⟨h1.1, ((Subgroup.mem_centralizer_iff.1 h1.2) u hs.u_mem).symm⟩
  · rintro ⟨hsS, hsu⟩
    refine Subgroup.mem_inf.2 ⟨hsS, Subgroup.mem_centralizer_iff.2 (fun y hy => ?_)⟩
    have hzs : z * s = s * z := hs.z_comm hII hsS
    rcases hs.U_elems y hy with h' | h' | h' | h'
    · rw [h']; simp
    · rw [h']; exact hzs
    · rw [h']; exact hsu.symm
    · rw [h']
      calc (u * z) * s = u * (z * s) := by group
        _ = u * (s * z) := by rw [hzs]
        _ = (u * s) * z := by group
        _ = (s * u) * z := by rw [hsu]
        _ = s * (u * z) := by group

theorem conj_u (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {s : G} (hsS : s ∈ S) :
    s * u * s⁻¹ = u ∨ s * u * s⁻¹ = u * z := by
  have hU := hs.U_norm s hsS u hs.u_mem
  have hzs : z * s = s * z := hs.z_comm hII hsS
  rcases hs.U_elems _ hU with h1 | h1 | h1 | h1
  · exfalso
    apply hs.u_ne
    have e : u = s⁻¹ * (s * u * s⁻¹) * s := by group
    rw [h1] at e
    have : u = 1 := by rw [e]; group
    rw [this]; exact one_mem _
  · exfalso
    apply hs.u_ne
    have e : u = s⁻¹ * (s * u * s⁻¹) * s := by group
    rw [h1] at e
    have : u = z := by
      rw [e]
      calc s⁻¹ * z * s = s⁻¹ * (z * s) := by group
        _ = s⁻¹ * (s * z) := by rw [hzs]
        _ = z := by group
    rw [this]; exact Subgroup.mem_zpowers z
  · exact Or.inl h1
  · exact Or.inr h1

theorem relIndex_W_le_two (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    (Wsub S U).relIndex S ≤ 2 := by
  by_cases hall : ∀ s ∈ S, s ∈ Wsub S U
  · have : (Wsub S U).relIndex S = 1 := Subgroup.relIndex_eq_one.2 hall
    omega
  · push Not at hall
    obtain ⟨s₀, hs₀S, hs₀W⟩ := hall
    have hs₀u : s₀ * u * s₀⁻¹ = u * z := by
      rcases hs.conj_u hII hs₀S with h1 | h1
      · exfalso
        apply hs₀W
        rw [hs.mem_W_iff hII]
        refine ⟨hs₀S, ?_⟩
        calc s₀ * u = (s₀ * u * s₀⁻¹) * s₀ := by group
          _ = u * s₀ := by rw [h1]
      · exact h1
    have hidx : ((Wsub S U).subgroupOf S).index = 2 := by
      refine Subgroup.index_eq_two_iff.2 ⟨⟨s₀, hs₀S⟩, fun b => ?_⟩
      have hbS : (b : G) ∈ S := b.2
      by_cases hb : (b : G) ∈ Wsub S U
      · right
        refine ⟨hb, ?_⟩
        intro hba
        have hba' : (b : G) * s₀ ∈ Wsub S U := hba
        have : s₀ ∈ Wsub S U := by
          have e : s₀ = (b : G)⁻¹ * ((b : G) * s₀) := by group
          rw [e]
          exact mul_mem (inv_mem hb) hba'
        exact hs₀W this
      · left
        refine ⟨?_, hb⟩
        have hbu : (b : G) * u * (b : G)⁻¹ = u * z := by
          rcases hs.conj_u hII hbS with h1 | h1
          · exfalso
            apply hb
            rw [hs.mem_W_iff hII]
            refine ⟨hbS, ?_⟩
            calc (b : G) * u = ((b : G) * u * (b : G)⁻¹) * (b : G) := by group
              _ = u * (b : G) := by rw [h1]
          · exact h1
        have hbz : (b : G) * z * (b : G)⁻¹ = z := by
          have hzb : z * (b : G) = (b : G) * z := hs.z_comm hII hbS
          rw [← hzb]; group
        have hmem : (b : G) * s₀ ∈ Wsub S U := by
          rw [hs.mem_W_iff hII]
          refine ⟨mul_mem hbS hs₀S, ?_⟩
          have e1 : (b : G) * s₀ * u * ((b : G) * s₀)⁻¹ = u := by
            calc (b : G) * s₀ * u * ((b : G) * s₀)⁻¹
                = (b : G) * (s₀ * u * s₀⁻¹) * (b : G)⁻¹ := by group
              _ = (b : G) * (u * z) * (b : G)⁻¹ := by rw [hs₀u]
              _ = ((b : G) * u * (b : G)⁻¹) * ((b : G) * z * (b : G)⁻¹) := by group
              _ = (u * z) * z := by rw [hbu, hbz]
              _ = u := by
                have hz2 := hs.z_sq
                calc (u * z) * z = u * (z * z) := by group
                  _ = u := by rw [hz2]; group
          calc (b : G) * s₀ * u = ((b : G) * s₀ * u * ((b : G) * s₀)⁻¹) * ((b : G) * s₀) := by group
            _ = u * ((b : G) * s₀) := by rw [e1]
        exact hmem
    have : (Wsub S U).relIndex S = 2 := hidx
    omega

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
