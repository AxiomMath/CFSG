module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Weak

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_weakClosureIn_of_conj_le_centralizer {M L T V : Subgroup G} (hLM : L ≤ M)
    (hML : M ≤ normalizer (L : Set G)) (hTM : T ≤ M)
    (hCL : L ⊓ centralizer (V : Set G) ≤ T)
    (hW : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ M →
      V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G)) :
    L ≤ normalizer (weakClosureIn V T : Set G) := by
  have key : ∀ x ∈ L, ∀ y ∈ weakClosureIn V T, x * y * x⁻¹ ∈ weakClosureIn V T := by
    intro x hx y hy
    have hxM : x ∈ M := hLM hx
    refine Subgroup.iSup_induction _ (C := fun y => x * y * x⁻¹ ∈ weakClosureIn V T) hy
      (fun g z hz => ?_) ?_ (fun a b ha hb => ?_)
    · obtain ⟨z₀, hz₀, rfl⟩ := hz
      have hVg : V.map (MulAut.conj (g : G)).toMonoidHom ≤ M := g.2.trans hTM
      have hVxg : V.map (MulAut.conj (x * (g : G))).toMonoidHom ≤ M := by
        rintro _ ⟨v', hv', rfl⟩
        have h1 : (g : G) * v' * (g : G)⁻¹ ∈ M := hVg ⟨v', hv', rfl⟩
        have h2 := M.mul_mem (M.mul_mem hxM h1) (M.inv_mem hxM)
        simpa [mul_assoc] using h2
      have hcW := hW _ hVg
      have hcXW := hW _ hVxg
      have hxg : V.map (MulAut.conj (x * (g : G))).toMonoidHom ≤ T := by
        rintro _ ⟨v, hv, rfl⟩
        have hwT : (g : G) * v * (g : G)⁻¹ ∈ T := g.2 ⟨v, hv, rfl⟩
        have hwM : (g : G) * v * (g : G)⁻¹ ∈ M := hTM hwT
        have hwC : (g : G) * v * (g : G)⁻¹ ∈ centralizer (V : Set G) := hcW ⟨v, hv, rfl⟩
        have hxwC : x * ((g : G) * v * (g : G)⁻¹) * x⁻¹ ∈ centralizer (V : Set G) :=
          hcXW ⟨v, hv, by simp [mul_assoc]⟩
        have hcL : ((g : G) * v * (g : G)⁻¹)⁻¹ * (x * ((g : G) * v * (g : G)⁻¹) * x⁻¹) ∈ L := by
          have h1 : ((g : G) * v * (g : G)⁻¹)⁻¹ * x * ((g : G) * v * (g : G)⁻¹) ∈ L := by
            have := (mem_normalizer_iff.mp (hML (M.inv_mem hwM)) x).mp hx
            simpa [mul_assoc] using this
          have h2 := L.mul_mem h1 (L.inv_mem hx)
          simpa [mul_assoc] using h2
        have hcC : ((g : G) * v * (g : G)⁻¹)⁻¹ * (x * ((g : G) * v * (g : G)⁻¹) * x⁻¹) ∈
            centralizer (V : Set G) :=
          Subgroup.mul_mem _ (Subgroup.inv_mem _ hwC) hxwC
        have hcT := hCL ⟨hcL, hcC⟩
        have e1 : x * ((g : G) * v * (g : G)⁻¹) * x⁻¹ =
            ((g : G) * v * (g : G)⁻¹) *
              (((g : G) * v * (g : G)⁻¹)⁻¹ * (x * ((g : G) * v * (g : G)⁻¹) * x⁻¹)) := by
          group
        have e2 : (x * (g : G)) * v * (x * (g : G))⁻¹ =
            x * ((g : G) * v * (g : G)⁻¹) * x⁻¹ := by group
        show (x * (g : G)) * v * (x * (g : G))⁻¹ ∈ T
        rw [e2, e1]
        exact T.mul_mem hwT hcT
      exact map_conj_le_weakClosureIn hxg ⟨z₀, hz₀, by simp [mul_assoc]⟩
    · simp
    · simpa [mul_assoc] using mul_mem ha hb
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact ⟨fun hy => key x hx y hy, fun hy => by
    simpa [mul_assoc] using key x⁻¹ (L.inv_mem hx) _ hy⟩

end CFSG.LocalAnalysis.RankThreeUC
