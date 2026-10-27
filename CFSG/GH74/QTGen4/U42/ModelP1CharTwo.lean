module

public import CFSG.GH74.QTGen4.U42.ModelU
public import CFSG.GH74.QTGen4.U42.ModelCoordsRelabelled
public import CFSG.GH74.QTGen4.U42.U0Centralizer
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocFinal2

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.A5Model
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5
open CFSG.Quasithin.H13.F431.U42 U42F431

theorem centralizer_pCoreOf_P1_le :
    ∀ g ∈ P1, (∀ u ∈ pCoreOf 2 P1, g * u = u * g) → g ∈ pCoreOf 2 P1 := by
  classical
  obtain ⟨e, he1, he2⟩ := exists_model_coords_relabelled
  have htV : tPrime ∈ Vsub := tPrime_mem_Vsub
  have hlist : subProdL L0 6 = comp (tpTab.getD 15 []) (tpTab.getD 16 []) := by
    decide +kernel
  have hrep : RepL (subProdL L0 6) ((tPrime : Y) : P45) := by
    rw [hlist]
    exact repL_tPrime
  have hpsi : psiEq (⟨tPrime, htV⟩ : Vsub) = Multiplicative.ofAdd ⟨FV 6, FV_mem 6⟩ :=
    (psiEq_apply _).trans ((psiM_apply _).trans (psiF_eq _ (s := 6) (by norm_num) hrep))
  have htR : tPrime ∈ pCoreOf 2 P1 := by
    apply (model_U_iff e he1 he2 ⟨tPrime, Vsub_le_P2 htV⟩).mpr
    rw [he1 tPrime htV, hpsi]
    decide +kernel
  let C : Ctx Y :=
    { φ1 := P1.subtype
      φ2 := P2.subtype
      inj1 := P1.subtype_injective
      inj2 := P2.subtype_injective
      agree := fun _ _ _ => rfl
      cent := by
        intro g hg
        have hgP : g ∈ P1 := by
          rw [← centralizer_x]
          exact Subgroup.mem_centralizer_singleton_iff.mpr hg
        exact ⟨⟨g, hgP⟩, rfl⟩
      norm := by
        intro g hg
        rw [Subgroup.map_subgroupOf_eq_of_le Vsub_le_P2, normalizer_V] at hg
        exact ⟨⟨g, hg⟩, rfl⟩ }
  have htG : C.tG = tPrime := by
    rw [Ctx.tG_def, C.Φ2_of_mem (Vsub_le_P2 htV)]
    rfl
  intro g hg hc
  have hgP2 : g ∈ P2 := by
    have hcg : g ∈ Subgroup.centralizer ({C.tG} : Set Y) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (by rw [htG]; exact hc tPrime htR)
    obtain ⟨p, hp⟩ := C.centralizer_tG_le_range hcg
    exact hp ▸ p.2
  let gp : ↥P2 := ⟨g, hgP2⟩
  have hx : ((e gp : Mof _) : Mc) ∈ Subgroup.centralizer (U0 : Set Mc) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hsign : u.right.sign = 1 := by
      rcases hu.2 with h | h | h | h <;> rw [h] <;> decide +kernel
    have huM : u ∈ Mof (alternatingGroup (Fin 5)) :=
      mem_Mof.mpr (Equiv.Perm.mem_alternatingGroup.mpr hsign)
    let up : ↥P2 := e.symm ⟨u, huM⟩
    have heup : ((e up : Mof _) : Mc) = u := congrArg Subtype.val (e.apply_symm_apply ⟨u, huM⟩)
    have huR : (up : Y) ∈ pCoreOf 2 P1 :=
      (model_U_iff e he1 he2 up).mpr (by rw [heup]; exact hu)
    have hcomm : gp * up = up * gp := Subtype.ext (hc (up : Y) huR)
    have h := congrArg (fun z : ↥P2 => ((e z : Mof _) : Mc)) hcomm
    simpa only [map_mul, Subgroup.coe_mul, heup] using h.symm
  exact (model_U_iff e he1 he2 gp).mpr (centralizer_U0_le_U0 hx)

end CFSG.GH74.QTGen4.U42
