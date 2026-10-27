module

public import CFSG.GH74.Generic.BProg.B3.S1ThreeReduce
public import CFSG.GH74.Generic.S1.Exo.Q3Single
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.GH74.E2.FactsK

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S1Three

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.BProg
open CFSG.GH74.GLS.C3.Layer1 Subgroup
open CFSG.GH74.Filter.ClassicalOdd (Q8)

variable {G : Type} [Group G] [Finite G]

theorem bar_ne_one {a u : G} (hu : u ∈ centralizer ({a} : Set G)) (hu2 : orderOf u = 2) :
    bar a u ≠ 1 :=
  (CFSG.GH74.Generic.BProg.B1.PilotS5.bar_facts le_rfl hu hu2).2.1

section Beta


theorem s1three_beta
    {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G} (hc : Ctx21 G x K A a D J)
    (h1 : QShape1 (↥K ⧸ pPrimeCore 2 ↥K)) {φA φB : Q8 →* CentralizerBar a}
    (hd : S1ThreeData x a φA φB) (hB : ∀ q, φB q ∈ PumpCalc.bar a J)
    (hA : ∀ q, φA q ∈ PumpCalc.bar a J) : False := by
  classical
  obtain ⟨-, -, hxA, -⟩ := s1_basic hc h1
  have hAel : CFSG.IsElementaryAbelian 2 ↥A := hc.src.2.1
  have hAcomm : x * a = a * x :=
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥A)).comm ⟨x, hxA⟩ ⟨a, hc.a_mem⟩)
  have ha2 : orderOf a = 2 := hc.obs.y_ord
  have hx2 : orderOf x = 2 := hc.circ.1.1.1.1
  have haa : a * a = 1 := by
    have h := pow_orderOf_eq_one a
    rw [ha2, pow_two] at h
    exact h
  have haC : a ∈ centralizer ({a} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hxC : x ∈ centralizer ({a} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hAcomm
  set Jb : Subgroup (CentralizerBar a) := PumpCalc.bar a J with hJb
  have hJc : IsComponent Jb := PumpCalc.isComponent_bar hc.obs.comp
  have hcJ : bar a a ∈ Jb := hd.zA ▸ hA _
  have hyJ : bar a (x * a) ∈ Jb := hd.zB ▸ hB _
  set c : ↥Jb := ⟨bar a a, hcJ⟩ with hcdef
  set y : ↥Jb := ⟨bar a (x * a), hyJ⟩ with hydef
  have hcent := bar_self_central a
  have hxbar := bar_mul_bar haa hAcomm
  have hnot := xbar_not_cent hc h1
  have hbx1 : bar a x ≠ 1 := bar_ne_one hxC hx2
  have hxaC : x * a ∈ centralizer ({a} : Set G) := Subgroup.mul_mem _ hxC haC
  have hxa2 : orderOf (x * a) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · have hxx : x * x = 1 := by
        have h := pow_orderOf_eq_one x
        rw [hx2, pow_two] at h
        exact h
      calc (x * a) ^ 2 = x * (a * x) * a := by rw [pow_two]; simp only [mul_assoc]
        _ = x * (x * a) * a := by rw [hAcomm]
        _ = (x * x) * (a * a) := by simp only [mul_assoc]
        _ = 1 := by rw [hxx, haa, one_mul]
    · intro h
      apply s1_a_ne_x hc h1
      have h' : x = a⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [h', inv_eq_of_mul_eq_one_left haa]
  have hcc : bar a a * bar a a = 1 := by
    rw [bar_of_mem haC, ← map_mul]
    have : (⟨a, haC⟩ : ↥(centralizer ({a} : Set G))) * ⟨a, haC⟩ = 1 := Subtype.ext haa
    rw [this, map_one]
  have cfg : CFSG.GH74.Generic.S1.Exo.Q3Cfg ↥Jb c y (φA.codRestrict Jb hA) (φB.codRestrict Jb hB) :=
    { quasi := hJc.1
      hZ := by
        obtain ⟨e⟩ := PumpCalc.kBar_equiv_bar hc.obs.comp
        exact PumpRigid.isPGroup_two_center_of_equiv e (PumpRigid.isPGroup_two_center_hat ↥J)
      gen4 := Gen4.subgroup Jb (CFSG.GH74.Generic.S1.Exo.barC_gen4 hc.hyp.gen4)
      gh := CFSG.GH74.Generic.S1.Exo.barC_gh hc.hyp.simple hc.hyp.nonab hc.hyp.kgh ha2 Jb
        (center ↥Jb) hJc.1.2.1 hJc.1.2.2
      c_mem := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (hcent g)
      c_ne_one := fun h => bar_ne_one haC ha2 (congrArg Subtype.val h)
      y_ne_one := fun h => bar_ne_one hxaC hxa2 (congrArg Subtype.val h)
      c_ne_y := by
        intro h
        have h1 : bar a a = bar a (x * a) := congrArg Subtype.val h
        apply hbx1
        rw [← hxbar, ← h1, hcc]
      zA := Subtype.ext hd.zA
      zB := Subtype.ext hd.zB
      injA := fun p q h => hd.injA (congrArg Subtype.val h)
      injB := fun p q h => hd.injB (congrArg Subtype.val h)
      comm := fun p q => Subtype.ext (hd.comm p q)
      y_nc := by
        intro hy
        apply hnot
        intro j hj
        have h2 : bar a (x * a) * j = j * bar a (x * a) :=
          congrArg Subtype.val (Subgroup.mem_center_iff.1 hy ⟨j, hj⟩).symm
        rw [← hxbar]
        calc bar a a * bar a (x * a) * j = bar a a * (bar a (x * a) * j) := mul_assoc _ _ _
          _ = bar a a * (j * bar a (x * a)) := by rw [h2]
          _ = (bar a a * j) * bar a (x * a) := (mul_assoc _ _ _).symm
          _ = (j * bar a a) * bar a (x * a) := by rw [hcent j]
          _ = j * (bar a a * bar a (x * a)) := mul_assoc _ _ _ }
  exact cfg.false (genericKnownFacts_of_griess
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds) E2.e2ComponentFacts

end Beta

end S1Three

end CFSG.GH74.Generic.BProg.B3
