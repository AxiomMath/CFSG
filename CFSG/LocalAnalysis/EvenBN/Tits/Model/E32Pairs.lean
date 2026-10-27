module

public import CFSG.LocalAnalysis.EvenBN.Tits.Model.E32Orbits
public import Certificates.Certificate27582
public import Certificates.Certificate27583

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.Model

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open Certificates.TitsAschbacherParrott Certificates.TitsAschbacherSecFour
  Certificates.TitsAschbacherE32
open CFSG.Quasithin (tπ)

@[expose] noncomputable def jElt (w : List ℕ) : Equiv.Perm (Fin 1755) :=
  (w.map (chainGen titsJArrs)).prod

theorem rep_jElt {w : List ℕ}
    (hw : jLetters w = true) : Rep 1755 (jArr w) (jElt w) ∧ jElt w ∈ titsJ := by
  have hl : ∀ i ∈ w, i < 4 := fun i hi => by
    have := List.all_eq_true.1 hw i hi
    simpa using this
  refine ⟨rep_prodArr fun i hi => chainGen_J_rep (hl i hi),
    list_prod_map_mem fun i hi => ?_⟩
  rw [titsJ_eq_closure_chainGen]
  exact subset_closure ⟨⟨i, hl i hi⟩, rfl⟩

theorem pairCheck_eq_true : pairCheck () = true :=
  Certificates.certificate27582

theorem exists_mem_titsJ_comm_conj
    {a b : Equiv.Perm (Fin 1755)} (ha : a ∈ hatE) (hb : b ∈ hatE) (ha1 : a ≠ 1)
    (haz : a ≠ titsZ) (hb1 : b ≠ 1) (hbz : b ≠ titsZ) (hba : b ≠ a) (hbaz : b ≠ a * titsZ) :
    ∃ x ∈ titsJ, x * a = a * x ∧ x * b * x⁻¹ = b * titsZ := by
  obtain ⟨m₁, hm₁, rfl⟩ := mem_hatE_iff.1 ha
  obtain ⟨m₂, hm₂, rfl⟩ := mem_hatE_iff.1 hb
  have h := pairCheck_eq_true
  unfold pairCheck at h
  have hok := List.all_eq_true.1 (List.all_eq_true.1 h m₁ (List.mem_range.2 hm₁)) m₂
    (List.mem_range.2 hm₂)
  unfold pairOK at hok
  have ra := rep_eArrs hm₁
  have rb := rep_eArrs hm₂
  have rz : Rep 1755 (vA 12) titsZ := by
    rw [← parrottV_twelve_eq]
    exact rep_vA (by norm_num)
  have f1 : eqA 1755 ((eArrs ()).getD m₁ #[]) (idA 1755) = false :=
    Bool.eq_false_iff.2 fun h => ha1 ((eqA_iff ra rep_idA).1 h)
  have f2 : eqA 1755 ((eArrs ()).getD m₁ #[]) (vA 12) = false :=
    Bool.eq_false_iff.2 fun h => haz ((eqA_iff ra rz).1 h)
  have f3 : eqA 1755 ((eArrs ()).getD m₂ #[]) (idA 1755) = false :=
    Bool.eq_false_iff.2 fun h => hb1 ((eqA_iff rb rep_idA).1 h)
  have f4 : eqA 1755 ((eArrs ()).getD m₂ #[]) (vA 12) = false :=
    Bool.eq_false_iff.2 fun h => hbz ((eqA_iff rb rz).1 h)
  have f5 : eqA 1755 ((eArrs ()).getD m₂ #[]) ((eArrs ()).getD m₁ #[]) = false :=
    Bool.eq_false_iff.2 fun h => hba ((eqA_iff rb ra).1 h)
  have f6 : eqA 1755 ((eArrs ()).getD m₂ #[])
      (compA 1755 ((eArrs ()).getD m₁ #[]) (vA 12)) = false :=
    Bool.eq_false_iff.2 fun h => hbaz ((eqA_iff rb (rep_compA ra rz)).1 h)
  simp only [f1, f2, f3, f4, f5, f6, Bool.false_or] at hok
  obtain ⟨e, -, he⟩ := List.any_eq_true.1 hok
  simp only [Bool.and_eq_true] at he
  obtain ⟨⟨⟨-, hw⟩, hc⟩, hcj⟩ := he
  obtain ⟨rx, hxJ⟩ := rep_jElt hw
  refine ⟨jElt e.2.2, hxJ, ?_, ?_⟩
  · exact (eqA_iff (rep_compA rx ra) (rep_compA ra rx)).1 hc
  · exact conj_eq_of_conjToA rx rb (rep_compA rb rz) hcj

theorem titsQH_baseCount_five :
    titsQH.baseCount = 5 := by
  show (finList 1755 titsHBase).length = 5
  simp [finList, titsCentral_check.2.1]

theorem centFCheck_eq_true : centFCheck () = true :=
  Certificates.certificate27583

theorem titsA_centralizer_parrottF
    : titsA ⊓ centralizer (parrottF : Set (Equiv.Perm (Fin 1755))) = parrottF := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxA, hxC⟩ := mem_inf.1 hx
    have hcomm : ∀ i ∈ fIdx, x * parrottV i = parrottV i * x := by
      intro i hi
      have hiF : parrottV i ∈ parrottF := by
        refine subset_closure ⟨i, ?_, rfl⟩
        simp only [fIdx, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp
      exact (mem_centralizer_iff.1 hxC _ hiF).symm
    have hi13 : ∀ i ∈ fIdx, i < 13 := by decide
    have hzF : titsZ ∈ parrottF := by
      rw [← parrottV_twelve_eq]
      exact subset_closure ⟨12, by simp, rfl⟩
    have hxz : x ∈ titsA ⊓ centralizer {titsZ} :=
      mem_inf.2 ⟨hxA, mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hxC _ hzF).symm⟩
    rw [centralizer_titsZ_eq] at hxz
    have hcheck := centFCheck_eq_true
    unfold centFCheck at hcheck
    rcases hxz with hxH | hxH
    · have hxQ : x ∈ titsQH.originalSubgroup := by
        rw [titsQH_facts.2.2.1]
        exact hxH
      obtain ⟨a, ha, hp⟩ := all5_spec titsH_chainArrays (by norm_num : 0 < 4)
        titsLocalChains_check.1 titsQH_baseCount_five hcheck hxQ
      rw [Bool.and_eq_true] at hp
      have hcF : commF a = true := List.all_eq_true.2 fun i hi =>
        (eqA_iff (rep_compA ha (rep_vA (hi13 i hi))) (rep_compA (rep_vA (hi13 i hi)) ha)).2
          (hcomm i hi)
      rw [hcF, Bool.not_true, Bool.false_or] at hp
      obtain ⟨f, hf, hfe⟩ := List.any_eq_true.1 hp.1
      obtain ⟨m, hm, hfm⟩ := exists_of_mem_fArrs hf
      rw [(eqA_iff ha hfm).1 hfe]
      exact fElt_mem hm
    · exfalso
      have hQ : x * tπ⁻¹ ∈ titsQH.originalSubgroup := by
        rw [titsQH_facts.2.2.1]
        exact hxH
      obtain ⟨a, ha, hp⟩ := all5_spec titsH_chainArrays (by norm_num : 0 < 4)
        titsLocalChains_check.1 titsQH_baseCount_five hcheck hQ
      rw [Bool.and_eq_true] at hp
      have hrep := rep_compA ha CFSG.Quasithin.tπ_rep
      rw [inv_mul_cancel_right] at hrep
      have hcF : commF (compA 1755 a CFSG.Quasithin.titsPiArr) = true :=
        List.all_eq_true.2 fun i hi =>
          (eqA_iff (rep_compA hrep (rep_vA (hi13 i hi))) (rep_compA (rep_vA (hi13 i hi)) hrep)).2
            (hcomm i hi)
      rw [hcF] at hp
      exact absurd hp.2 (by decide)
  · exact le_inf (parrottF_le_titsD.trans titsD_le_titsA) fun x hx =>
      mem_centralizer_iff.2 fun y hy => parrottF_elemAbelian.1 y hy x hx

end CFSG.LocalAnalysis.EvenBN.Tits.Model
