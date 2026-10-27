module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OPlane
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OFields

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin (quadMinus nondegenerate_polarBilin_quadMinus_of_finite)

variable {G : Type} [Group G] [Finite G] {n p : ℕ} {M L V : Subgroup G}

theorem exists_gl_isometry_pair {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {w u : OW F}
    (hli : LinearIndependent F ![w, u]) (hw : quadMinus 3 F b c w = 0)
    (hu : quadMinus 3 F b c u = 0) (hwu : polar (quadMinus 3 F b c) w u = 0) :
    ∃ G : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F,
      toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F G ∈
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 F b c) ∧
      gv G (eV F idx0) = w ∧ gv G (eV F idx1) = u := by
  have hQn := nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr
  have hne : idx0 ≠ idx1 := by decide
  have hli0 : LinearIndependent F ![eV F idx0, eV F idx1] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h0 := congrFun hst (Sum.inl idx0)
    have h1 := congrFun hst (Sum.inl idx1)
    simp [Pi.single_apply, hne, hne.symm] at h0 h1
    exact ⟨h0, h1⟩
  have hee : ∀ i j : Fin (3 - 1), polar (quadMinus 3 F b c) (eV F i) (eV F j) = 0 := by
    intro i j
    rw [polar_e_right]
    simp [Pi.single_apply]
  obtain ⟨g₀, hg₀, hgu⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq
    hQn (k := 2) ![eV F idx0, eV F idx1] ![w, u] hli0 hli
    (by
      simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [hw, hu, quad_eV, quad_eV]
      exact ⟨rfl, rfl⟩)
    (by
      simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · rw [polar_self_eq_two_mul, polar_self_eq_two_mul, hw, quad_eV, mul_zero]
      · rw [hwu, hee]
      · rw [polar_comm, hwu, hee]
      · rw [polar_self_eq_two_mul, polar_self_eq_two_mul, hu, quad_eV, mul_zero])
  obtain ⟨G₀, hG₀⟩ : ∃ G₀ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F,
      G₀ = (toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).symm g₀ := ⟨_, rfl⟩
  have hG₀mul : ∀ x : OW F, gv G₀ x = g₀ x := by
    intro x
    show ((G₀ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
      Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x =
        g₀ x
    rw [← toLinEquiv_apply, hG₀, MulEquiv.apply_symm_apply]
  have h0 : g₀ (eV F idx0) = w := hgu 0
  have h1 : g₀ (eV F idx1) = u := hgu 1
  refine ⟨G₀, ?_, by rw [hG₀mul, h0], by rw [hG₀mul, h1]⟩
  rw [hG₀, MulEquiv.apply_symm_apply]
  exact hg₀

theorem O6NatData.exists_lift_stab_plane (d : O6NatData G n L V) [CharP d.F 2] (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hn : 1 ≤ n) (hLM : L ≤ M) (Y : Submodule d.F (OW d.F))
    (hY2 : Module.finrank d.F Y = 2)
    (hYs : ∀ y ∈ Y, StatedQuadMinus 3 d.F d.b d.c y = 0) :
    ∃ P : Subgroup G, P ≤ L ∧ 2 ≤ CFSG.Open.pRank p P ∧ ∀ x ∈ P, ∃ hx : x ∈ L, ∀ y ∈ Y,
      gv ((d.ε ⟨x, hx⟩ : ↥(StatedOmega (StatedQuadMinus 3 d.F d.b d.c))) :
        GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) y ∈ Y := by
  obtain ⟨Mdl⟩ := d.nonempty_model hn
  have hp2 := prime_ne_two_of_dvd_two_pow_add_one hn hpq
  have hpq' : p ∣ Nat.card d.F + 1 := by
    rw [d.card_F]
    exact hpq
  obtain ⟨E, hEΩ, hEa, hEc, hEY⟩ := exists_stab_plane Mdl d.irred hp hpq' Y hY2 hYs
  set f : ↥L →* GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F :=
    (StatedOmega (StatedQuadMinus 3 d.F d.b d.c)).subtype.comp d.ε with hf
  have hker : IsPGroup 2 ↥f.ker := by
    have h : f.ker = CFSG.pCore 2 ↥L := by
      rw [hf, MonoidHom.ker_comp_of_injective _ _
        (StatedOmega (StatedQuadMinus 3 d.F d.b d.c)).subtype_injective, d.ε_ker]
    rw [h]
    exact CFSG.pCore_isPGroup
  have hEf : E ≤ f.range := by
    intro g hg
    obtain ⟨l, hl⟩ := d.ε_surj ⟨g, hEΩ hg⟩
    exact ⟨l, congrArg Subtype.val hl⟩
  obtain ⟨S, hSa, hSc, hSm⟩ := exists_elemAbelian_lift_of_ker f hker hp hp2 hEa hEf
  refine ⟨S.map L.subtype, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact s.2
  · refine CFSG.SectionRank.le_pRank hp.one_lt (le_refl _) (IsElemAbelian.map hSa _) ?_
    rw [Subgroup.card_map_of_injective L.subtype_injective, hSc, hEc]
  · intro x hx
    obtain ⟨s, hsS, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨s.2, fun y hy => ?_⟩
    have hfs : f s ∈ E := hSm ▸ Subgroup.mem_map_of_mem f hsS
    exact hEY (f s) hfs y hy

end CFSG.LocalAnalysis.RankThreeUC
