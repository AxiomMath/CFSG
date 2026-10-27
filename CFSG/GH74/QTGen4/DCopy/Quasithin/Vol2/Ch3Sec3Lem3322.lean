module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3322A
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3322C
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3322D
public import CFSG.Quasithin.H13.A7Nat1236Insp
public import CFSG.Quasithin.H13.A7NatSL2
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3322E

public section
namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique hiding evenWeight
open CFSG.Quasithin.H13.A7 (vec)

theorem stmt3_3_22_of_F4
    (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h8 : Stmt3_3_8) (h10 : Stmt3_3_10) (h14 : Stmt3_3_14_F4)
    (h17 : Stmt3_3_17_F4) (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat) (h38' : A38ForSQTK) (hF : A318Facts)
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G) : Stmt3_3_22_F4 := by
  intro G _ _ T M L D h
  refine ⟨fun e => ?_⟩
  obtain ⟨-, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  obtain ⟨ψ, hc⟩ := L3322.exists_coord322_F4 h5 h8 h10 h14 h17 h e
  obtain ⟨a, ha⟩ := A7.exists_vec_eq ψ
    (SteinbergCB.mem_evenWeight.2 (by decide +kernel) : L3322.vecZO ∈ SteinbergCB.evenWeight 7)
  obtain ⟨b, hb⟩ := A7.exists_vec_eq ψ A7.vecSix_mem
  have hbZ : (b : G) ∈ quasithinOmegaOneCenter T :=
    (L3322.mem_Z_iff h hTL hc b).2 (Or.inr (Or.inr (Or.inr hb)))
  have hθ : ∀ c ∈ quasithinOmegaOneCenter T, c ∈ Subgroup.centralizer (L : Set G) →
      thetaOf (Subgroup.centralizer ({c * (b : G)} : Set G)) ≤ L3322.lTheta L b :=
    fun c hcZ hcL => L3322.thetaOf_centralizer_le_F4 h5 h7 h14 h38 h39 h38' hF (hC27 G)
      A7.insp1236_proved A7.inspSL2NoA6_proved h hc hb hbZ hcZ hcL
  obtain ⟨d, hdD, hd⟩ := L3322.exists_conj_eq_F4 h5 h7 h14 h hc ha hb hθ
  have hθ1 : thetaOf (Subgroup.centralizer ({(b : G)} : Set G)) ≤ L3322.lTheta L b := by
    have := hθ 1 (Subgroup.one_mem _) (Subgroup.one_mem _)
    rwa [one_mul] at this
  exact L3322.false_of_conj h hTL hc ha hb hθ1 (h.DN hdD) hd

end CFSG.Quasithin.H13
