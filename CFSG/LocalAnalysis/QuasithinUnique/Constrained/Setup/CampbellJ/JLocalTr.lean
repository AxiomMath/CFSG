module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.JLocal
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.JBasic

public section

namespace CFSG.QuasithinUnique.Setup.CampbellJ

open CFSG.QuasithinUnique.Setup.Campbell

variable {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

section Translated

private theorem thompsonJ_eq_sup_inf_coreJ {Y : Subgroup G}
    (hY : Y ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G))
    (hS : (S : Subgroup G) = Y ⊔ CFSG.pCore 2 G) :
    CFSG.Quasithin.thompsonJ (S : Subgroup G) =
      Y ⊔ (CFSG.pCore 2 G ⊓ CFSG.Quasithin.thompsonJ (S : Subgroup G)) := by
  apply le_antisymm
  · intro x hxJ
    have hxS : x ∈ (S : Subgroup G) := thompsonJ_le_self' _ hxJ
    rw [hS] at hxS
    obtain ⟨y, hy, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hxS
    have hyJ : y ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G) := hY hy
    have hqJ : q ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G) := by
      have : y⁻¹ * (y * q) ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hyJ) hxJ
      simpa using this
    exact Subgroup.mul_mem_sup hy ⟨hq, hqJ⟩
  · exact sup_le hY inf_le_right

theorem tr_Fcore_repJ (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) (g : G) {Y : Subgroup G}
    (hY : Adm (cj (CFSG.Quasithin.thompsonJ (S : Subgroup G)) g) Y) :
    tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (Fcore G) =
      tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (Vmod G) ⊔
        (tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (Fcore G) ⊓
          Subgroup.centralizer (Y : Set G)) := by
  obtain ⟨A, hA, hYA⟩ := adm_thompsonJ_iff.mp (adm_trInv α g hY)
  have h1 := h.Fcore_eq_Vmod_sup_cent hA hYA
  have hY0 : trInv (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g Y ≤
      CFSG.Quasithin.thompsonJ (S : Subgroup G) := trInv_le_S
  have h2 := congrArg (tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g) h1
  rw [tr_sup (Vmod_le_JS h)
      (inf_le_left.trans (Fcore_le_JS h)), tr_centralizer hY0,
    tr_trInv hY.le] at h2
  exact h2

theorem isMaxElemAbelian_tr_Fcore_supJ (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) (g : G) {A' : Subgroup G}
    (hA' : CFSG.Quasithin.IsMaxElemAbelian (cj (CFSG.Quasithin.thompsonJ (S : Subgroup G)) g) A') :
    CFSG.Quasithin.IsMaxElemAbelian (cj (CFSG.Quasithin.thompsonJ (S : Subgroup G)) g)
      (tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (Fcore G) ⊔
        (A' ⊓ Subgroup.centralizer ((tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g
          (Fcore G) : Subgroup G) : Set G))) := by
  have hYJ : trInv (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g A' ≤
      CFSG.Quasithin.thompsonJ (S : Subgroup G) := trInv_le_S
  have hA := isMaxElemAbelian_trInv (α := α) (g := g) hA'
  have hAS := (isMaxElemAbelian_JS_iff (S := S) _).mp hA
  have h1 := (h.isMaxElemAbelian_core_sup_Fcore hAS).2
  rw [← h.inf_centralizer_Fcore hAS] at h1
  have h1J := (isMaxElemAbelian_JS_iff (S := S) _).mpr h1
  have h2 := isMaxElemAbelian_tr (α := α) (g := g) h1J
  rw [tr_sup (inf_le_left.trans hYJ) (Fcore_le_JS h),
    tr_centralizer (Fcore_le_JS h), tr_trInv hA'.1, sup_comm] at h2
  exact h2

theorem tr_commutator_A_FcoreJ (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) (g : G) {A' : Subgroup G}
    (hA' : CFSG.Quasithin.IsMaxElemAbelian (cj (CFSG.Quasithin.thompsonJ (S : Subgroup G)) g) A') :
    (A' ≤ tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (CFSG.pCore 2 G) →
      ⁅A', tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (Fcore G)⁆ = ⊥) ∧
    (¬ A' ≤ tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (CFSG.pCore 2 G) →
      ⁅A', tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (Fcore G)⁆ =
          tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (Zfix S) ∧
        cj (CFSG.Quasithin.thompsonJ (S : Subgroup G)) g =
          A' ⊔ tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (CFSG.pCore 2 G)) := by
  have hA := isMaxElemAbelian_trInv (α := α) (g := g) hA'
  have hAS := (isMaxElemAbelian_JS_iff (S := S) _).mp hA
  have hYJ : trInv (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g A' ≤
      CFSG.Quasithin.thompsonJ (S : Subgroup G) := trInv_le_S
  have hA'eq : tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g
      (trInv (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g A') = A' := tr_trInv hA'.1
  have htrQ : tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g
      (CFSG.pCore 2 G ⊓ CFSG.Quasithin.thompsonJ (S : Subgroup G)) =
        tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (CFSG.pCore 2 G) := by
    unfold tr
    rw [aimg_inf_self]
  have hiff : trInv (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g A' ≤ CFSG.pCore 2 G ↔
      A' ≤ tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (CFSG.pCore 2 G) := by
    rw [← htrQ]
    constructor
    · intro hYQ
      rw [← hA'eq]
      exact (tr_le_tr_iff hYJ inf_le_right).mpr (le_inf hYQ hYJ)
    · intro hA'Q
      have hle := (tr_le_tr_iff hYJ inf_le_right).mp (by rw [hA'eq]; exact hA'Q)
      exact fun x hx => (hle hx).1
  refine ⟨fun hle => ?_, fun hnle => ?_⟩
  · have h1 := IsSeed.commutator_A_Fcore_of_le hAS (hiff.mpr hle)
    have h2 := congrArg (tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g) h1
    rwa [tr_commutator hYJ (Fcore_le_JS h), hA'eq, tr_bot] at h2
  · have hnle' : ¬ trInv (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g A' ≤
        CFSG.pCore 2 G := fun hh => hnle (hiff.mp hh)
    refine ⟨?_, ?_⟩
    · have h1 := h.commutator_A_Fcore hAS hnle'
      have h2 := congrArg (tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g) h1
      rwa [tr_commutator hYJ (Fcore_le_JS h), hA'eq] at h2
    · have hsup := thompsonJ_eq_sup_inf_coreJ (S := S) hYJ (h.sylow_eq_sup hAS hnle')
      have h2 := congrArg (tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g) hsup
      rw [tr_self, tr_sup hYJ inf_le_right, tr_trInv hA'.1, htrQ] at h2
      exact h2

theorem tr_commutator_eq_of_ne_botJ (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) (g : G) {A : Subgroup G}
    (hA : CFSG.Quasithin.IsMaxElemAbelian (cj (CFSG.Quasithin.thompsonJ (S : Subgroup G)) g) A)
    (hne : ⁅A, tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (Fcore G)⁆ ≠ ⊥) :
    ⁅A, tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (Fcore G)⁆ =
        tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (Zfix S) ∧
      ¬ A ≤ tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (CFSG.pCore 2 G) ∧
      cj (CFSG.Quasithin.thompsonJ (S : Subgroup G)) g =
        A ⊔ tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (CFSG.pCore 2 G) := by
  obtain ⟨h1, h2⟩ := tr_commutator_A_FcoreJ h α g hA
  by_cases hAQ : A ≤ tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (CFSG.pCore 2 G)
  · exact absurd (h1 hAQ) hne
  · exact ⟨(h2 hAQ).1, hAQ, (h2 hAQ).2⟩

theorem tr_sylow_not_core_comm_VmodJ (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) (g : G) {s w : G}
    (hs : s ∈ cj (CFSG.Quasithin.thompsonJ (S : Subgroup G)) g)
    (hsQ : s ∉ tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (CFSG.pCore 2 G))
    (hw : w ∈ tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (Vmod G))
    (hc : s * w = w * s) :
    w ∈ tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (Zfix S) := by
  have hs1 : g * s * g⁻¹ ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G) := mem_cj.mp hs
  have hw1 : g * w * g⁻¹ ∈
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) := mem_cj.mp hw
  have hw1S : g * w * g⁻¹ ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G) := aimg_le hw1
  have hsQ' : ((α.symm ⟨g * s * g⁻¹, hs1⟩ :
      ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) ∉ CFSG.pCore 2 G := by
    intro hQ
    apply hsQ
    have h1 : ((α (α.symm ⟨g * s * g⁻¹, hs1⟩) :
        ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) ∈
        aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (CFSG.pCore 2 G) :=
      mem_aimg_of_mem hQ
    rw [α.apply_symm_apply] at h1
    exact mem_cj.mpr h1
  have hwV' : ((α.symm ⟨g * w * g⁻¹, hw1S⟩ :
      ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) ∈ Vmod G :=
    (mem_aimg_symm_iff hw1S).mp hw1
  have hcomm : (α.symm ⟨g * s * g⁻¹, hs1⟩ :
        ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) *
      α.symm ⟨g * w * g⁻¹, hw1S⟩ =
      α.symm ⟨g * w * g⁻¹, hw1S⟩ * α.symm ⟨g * s * g⁻¹, hs1⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show g * s * g⁻¹ * (g * w * g⁻¹) = g * w * g⁻¹ * (g * s * g⁻¹)
    calc g * s * g⁻¹ * (g * w * g⁻¹) = g * (s * w) * g⁻¹ := by group
      _ = g * (w * s) * g⁻¹ := by rw [hc]
      _ = g * w * g⁻¹ * (g * s * g⁻¹) := by group
  have hZ := h.sylow_not_core_comm_Vmod
    (thompsonJ_le_self' _ (α.symm ⟨g * s * g⁻¹, hs1⟩).2) hsQ' hwV'
    (congrArg Subtype.val hcomm)
  have h2 : ((α (α.symm ⟨g * w * g⁻¹, hw1S⟩) :
      ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) ∈
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) := mem_aimg_of_mem hZ
  rw [α.apply_symm_apply] at h2
  exact mem_cj.mpr h2

omit [Finite G] in
theorem tr_core_commute_tr_VmodJ (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (g : G) {q w : G}
    (hq : q ∈ tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (CFSG.pCore 2 G))
    (hw : w ∈ tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (Vmod G)) :
    q * w = w * q := by
  obtain ⟨qt, hqq, hqe⟩ := mem_tr.mp hq
  obtain ⟨wt, hwV', hwe⟩ := mem_tr.mp hw
  have h1 : qt * wt = wt * qt := Subtype.ext (Ecore_commute_core hqq (Vmod_le_Ecore hwV'))
  have h2 := congrArg α h1
  rw [map_mul, map_mul] at h2
  have h3 := congrArg Subtype.val h2
  simp only [Subgroup.coe_mul] at h3
  rw [hqe, hwe] at h3
  have : g * (q * w) * g⁻¹ = g * (w * q) * g⁻¹ := by
    calc g * (q * w) * g⁻¹ = g * q * g⁻¹ * (g * w * g⁻¹) := by group
      _ = g * w * g⁻¹ * (g * q * g⁻¹) := h3
      _ = g * (w * q) * g⁻¹ := by group
  simpa using this

end Translated

end CFSG.QuasithinUnique.Setup.CampbellJ

end
