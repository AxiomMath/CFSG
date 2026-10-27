module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.JLocalTr
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.JBasic

public section

namespace CFSG.QuasithinUnique.Setup.CampbellJ

open CFSG.QuasithinUnique.Setup.Campbell

variable {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

section Translates

private theorem commutator_thompsonJ_aimgJ_Fcore_aux (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) :
    ⁅CFSG.Quasithin.thompsonJ (S : Subgroup G),
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)⁆ =
        aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) := by
  have h1 := aimg_commutator (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) (α := α)
    (Y := CFSG.Quasithin.thompsonJ (S : Subgroup G)) (Y' := Fcore G) le_rfl (Fcore_le_JS h)
  rw [aimg_self, h.commutator_thompsonJ_Fcore] at h1
  exact h1.symm

private theorem partnerCoreJ_commA (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) {A : Subgroup G}
    (hA : CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G) A) :
    ⁅A, aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)⁆ = ⊥ ∨
      ⁅A, aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)⁆ =
        aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) := by
  have hAT : CFSG.Quasithin.IsMaxElemAbelian (CFSG.Quasithin.thompsonJ (S : Subgroup G)) A :=
    (isMaxElemAbelian_JS_iff A).mpr hA
  have hA0T : CFSG.Quasithin.IsMaxElemAbelian (CFSG.Quasithin.thompsonJ (S : Subgroup G))
      (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm A) :=
    isMaxElemAbelian_aimg (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm hAT
  have hA0S : CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G)
      (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm A) :=
    (isMaxElemAbelian_JS_iff _).mp hA0T
  have hAle : A ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G) := maxElem_le_thompsonJ hA
  have hAF : ⁅aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm A, Fcore G⁆ = ⊥ ∨
      ⁅aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm A, Fcore G⁆ = Zfix S := by
    by_cases hQ : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm A ≤ CFSG.pCore 2 G
    · exact Or.inl (IsSeed.commutator_A_Fcore_of_le hA0S hQ)
    · exact Or.inr (h.commutator_A_Fcore hA0S hQ)
  have hcomm := aimg_commutator (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) (α := α)
    (Y := aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm A) (Y' := Fcore G)
    (aimg_le (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) (α := α.symm) (Y := A))
    (Fcore_le_JS h)
  rw [aimg_aimg_symm hAle] at hcomm
  rcases hAF with hbot | hZ
  · left; rw [← hcomm, hbot, aimg_bot]
  · right; rw [← hcomm, hZ]

private theorem partnerCoreJ_sup_max (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) {A : Subgroup G}
    (hA : CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G) A) :
    CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G)
      (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ⊔
        (A ⊓ Subgroup.centralizer
          ((aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) :
            Subgroup G) : Set G))) := by
  have hAT : CFSG.Quasithin.IsMaxElemAbelian (CFSG.Quasithin.thompsonJ (S : Subgroup G)) A :=
    (isMaxElemAbelian_JS_iff A).mpr hA
  have hAle : A ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G) := maxElem_le_thompsonJ hA
  have hA0T : CFSG.Quasithin.IsMaxElemAbelian (CFSG.Quasithin.thompsonJ (S : Subgroup G))
      (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm A) :=
    isMaxElemAbelian_aimg (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm hAT
  have hA0S : CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G)
      (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm A) :=
    (isMaxElemAbelian_JS_iff _).mp hA0T
  have hcore : CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G)
      (Fcore G ⊔ (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm A ⊓
        Subgroup.centralizer (Fcore G : Set G))) := by
    have h1 := (h.isMaxElemAbelian_core_sup_Fcore hA0S).2
    rw [← h.inf_centralizer_Fcore hA0S, sup_comm] at h1
    exact h1
  have hXmax : CFSG.Quasithin.IsMaxElemAbelian (CFSG.Quasithin.thompsonJ (S : Subgroup G))
      (Fcore G ⊔ (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm A ⊓
        Subgroup.centralizer (Fcore G : Set G))) :=
    (isMaxElemAbelian_JS_iff _).mpr hcore
  have hImgMax :=
    isMaxElemAbelian_aimg (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) α hXmax
  have hFle : Fcore G ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G) := Fcore_le_JS h
  have hXle : (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm A ⊓
      Subgroup.centralizer (Fcore G : Set G)) ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G) :=
    inf_le_left.trans (aimg_le (S := CFSG.Quasithin.thompsonJ (S : Subgroup G))
      (α := α.symm) (Y := A))
  have hsup := aimg_sup (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) (α := α)
    (Y := Fcore G) (Y' := aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm A ⊓
      Subgroup.centralizer (Fcore G : Set G)) hFle hXle
  have hcen := aimg_centralizer (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) (α := α)
    (Y := aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm A) (Y' := Fcore G) hFle
  rw [hsup, hcen, aimg_aimg_symm hAle] at hImgMax
  exact (isMaxElemAbelian_JS_iff _).mp hImgMax

theorem partnerCoreJ_aimg (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) :
    PartnerCoreJ (S : Subgroup G)
      (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G))
      (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s hs x hx
    exact aimgJ_Fcore_normal α hs hx
  · intro s hs z hz
    exact aimgJ_Zfix_central α hs hz
  · exact commutator_thompsonJ_aimgJ_Fcore_aux h α
  · intro A hA
    exact partnerCoreJ_commA h α hA
  · intro A hA
    exact partnerCoreJ_sup_max h α hA

theorem aimgJ_Fcore_le_core (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G) :
    aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≤ CFSG.pCore 2 G := by
  have hrep := tr_Fcore_repJ h α 1 (Y := Fcore G)
    (by rw [cj_one]; exact (adm_thompsonJ_iff (Y := Fcore G)).mpr h.adm_Fcore)
  have hrep' : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) =
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ⊔
        (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ⊓
          Subgroup.centralizer (Fcore G : Set G)) := by
    simpa only [tr_one] using hrep
  calc aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)
      = aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ⊔
        (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ⊓
          Subgroup.centralizer (Fcore G : Set G)) := hrep'
    _ ≤ CFSG.pCore 2 G := sup_le hV fun x hx =>
        h.sylow_inf_centralizer_Fcore_le
          ⟨thompsonJ_le_self' (S : Subgroup G) (aimg_le hx.1), hx.2⟩

theorem adm_core_aimgJ_Fcore (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G) :
    Adm (CFSG.pCore 2 G) (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) := by
  obtain ⟨A, hA, hFA⟩ := h.adm_Fcore
  have hAT : CFSG.Quasithin.IsMaxElemAbelian (CFSG.Quasithin.thompsonJ (S : Subgroup G)) A :=
    (isMaxElemAbelian_JS_iff A).mpr hA
  have hA' : CFSG.Quasithin.IsMaxElemAbelian (CFSG.Quasithin.thompsonJ (S : Subgroup G))
      (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α A) :=
    isMaxElemAbelian_aimg (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) α hAT
  have hadmT : Adm (CFSG.Quasithin.thompsonJ (S : Subgroup G))
      (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) :=
    ⟨_, hA', aimg_mono hFA⟩
  exact h.adm_core_of_adm ((adm_thompsonJ_iff (Y := _)).mp hadmT)
    (aimgJ_Fcore_le_core h α hV)

theorem aimgJ_Fcore_le_thompsonJ_core (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G) :
    aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≤
      CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) := by
  obtain ⟨A, hA, hle⟩ := adm_core_aimgJ_Fcore h α hV
  exact hle.trans (maxElem_le_thompsonJ hA)

theorem aimgJ_Zfix_le_Fcore (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) :
    aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) ≤ Fcore G := by
  intro z hz
  exact mem_Fcore_of_JS_central_involution h (aimg_le hz)
    (fun t ht => (aimgJ_Zfix_central α ht hz).symm)
    ((isElemAbelian_iff.mp (isElemAbelian_aimg
      (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) α isElemAbelian_Zfix)).2 z hz)

theorem commutator_thompsonJ_aimgJ_Fcore (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) :
    ⁅CFSG.Quasithin.thompsonJ (S : Subgroup G),
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)⁆ =
        aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) :=
  commutator_thompsonJ_aimgJ_Fcore_aux h α

theorem tr_Fcore_le_thompsonJ_coreJ (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) (g : G)
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G) :
    tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (Fcore G) ≤
      CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) := by
  have h1 := cj_mono (g := g) (aimgJ_Fcore_le_thompsonJ_core h α hV)
  rw [cj_eq_self_of_normal (Y := CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G))] at h1
  exact h1

theorem tr_Fcore_le_thompsonJ_sylowJ (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) (g : G)
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G) :
    tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α g (Fcore G) ≤
      CFSG.Quasithin.thompsonJ (S : Subgroup G) :=
  (tr_Fcore_le_thompsonJ_coreJ h α g hV).trans h.thompsonJ_core_le_thompsonJ_sylow

end Translates

end CFSG.QuasithinUnique.Setup.CampbellJ

end
