module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915D1
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Sl2
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Cores

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

@[expose] def Prop9_5CaseC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx9 G z k S M p →
    ∀ (N A B : Subgroup G) (h : L915.Hyp95 z M p N A B), Op 2 N = ⊥ → Fs N ≠ Op p N →
      ¬ A ≤ centralizer (Em N : Set G) →
      C43c (zSec z N (L915.z_mem_N h) (pCore p ↥N)) p (xBar p N (L915.A1 z M N p)) → False

namespace L915

section Case

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
  {N A B : Subgroup G}

theorem false_of_sl2_case (hC : Ctx9 G z k S M p) (h : Hyp95 z M p N A B) (hO2 : Op 2 N = ⊥)
    (hAE : ¬ A ≤ centralizer (Em N : Set G)) {q : ℕ} (hq : Odd q) (h4 : 4 ≤ q)
    (hK : HasSL2Model ↥(ncl (xBar p N (A1 z M N p))) (fun q' => q' = q)) : False := by
  have hp := hC.prime
  have hp2 : p ≠ 2 := hC.odd
  have hO2' : pCore 2 ↥N = ⊥ := by
    have := hO2
    rw [Op_eq_map, Subgroup.map_eq_bot_iff, Subgroup.ker_subtype] at this
    exact le_bot_iff.mp this
  obtain ⟨J, hJ, hAJ⟩ := exists_component_noncentral_of_Em h.A_N hAE
  have hJ' : IsComponent (J.map (QuotientGroup.mk' (pCore p ↥N))) :=
    isComponent_map_mk hp CFSG.pCore_normal hJ CFSG.pCore_isPGroup
  have hA₁ : A.subgroupOf N ≤ (A1 z M N p).subgroupOf N := fun x hx => A_le_A1 h hx
  have hnc : ¬ xBar p N (A1 z M N p) ≤
      centralizer ((J.map (QuotientGroup.mk' (pCore p ↥N)) : Subgroup _) : Set _) :=
    not_le_centralizer_map hp hJ hA₁ hAJ
  have : (ncl (xBar p N (A1 z M N p))).Normal := Subgroup.normalClosure_normal
  have hJK : J.map (QuotientGroup.mk' (pCore p ↥N)) ≤ ncl (xBar p N (A1 z M N p)) :=
    component_le_of_noncentral inferInstance hJ' Subgroup.subset_normalClosure hnc
  exact false_of_sl2_section hp hp2 hO2' hJ hJK hq h4 hK

end Case

end L915

theorem prop9_5core_of_43E (h43E : Prop4_3E) (h512 : IG_5_12) (hc : Prop9_5CaseC) :
    Prop9_5Core := by
  intro G _ _ z k S M p hC N A B h hO2 hnot hAE
  have hp := hC.prime
  have hp2 : p ≠ 2 := hC.odd
  have hodd : Odd p := hp.odd_of_ne_two hp2
  rcases L915.concl43E_A1 h43E hC h hAE with hb | hc' | hd1 | he
  · obtain ⟨n, h3, hK, -⟩ := hb
    exact L915.false_of_sl2_case hC h hO2 hAE (q := p ^ n) hodd.pow (by omega) hK
  · exact hc G z k S M p hC N A B h hO2 hnot hAE hc'
  · exact L915.false_of_d1 h512 hC h hAE hd1
  · exact L915.false_of_sl2_case hC h hO2 hAE (q := 5) (by decide) (by norm_num) he.1

end CFSG.GH74.GLS.Stage2.Bender.Thm2
