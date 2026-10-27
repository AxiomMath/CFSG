module

public import CFSG.Certificates.Kernel.J4TreeNode.Node

public section

namespace CFSG.KC.J4TreeN

open CFSG.KC.J4Tree CFSG.KC.F2W CFSG.J4Tree.Native CFSG.ASVolI CFSG.Sporadic.J4
open CFSG.Sporadic.J4.QT

theorem nwFrom_append {G : Type*} [Group G] :
    ∀ (l₁ l₂ : List G) (m : ℕ), nwFrom 1 (l₁ ++ l₂) m =
      nwFrom 1 l₁ (m % 2 ^ l₁.length) * nwFrom 1 l₂ (m / 2 ^ l₁.length)
  | [], l₂, m => by simp [nwFrom]
  | x :: l₁, l₂, m => by
    rw [List.cons_append, nwFrom_cons, nwFrom_append l₁ l₂ (m / 2), nwFrom_cons, List.length_cons,
      pow_succ', Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul,
      Nat.mod_mod_of_dvd m (Dvd.intro _ rfl), mul_assoc]

section W


theorem w_core {T : Tabs}
    (hsx : ∀ t < 2048, T.sx.testBit t = (burnsideJ4NP_sextArr ())[t]?.getD false)
    {A W : Subgroup J} {bJ wJ cJ : List J} {B Wc Cc : List ℕ} {D : WRec}
    (hB2 : List.Forall₂ PK bJ B) (hW2 : List.Forall₂ PK wJ Wc) (hC2 : List.Forall₂ PK cJ Cc)
    (hAdef : A = Subgroup.closure {g | g ∈ bJ}) (hWdef : W = Subgroup.closure {g | g ∈ wJ})
    (hcA : ∀ c ∈ cJ, c ∈ A) (hwl : D.wmask.length = Wc.length)
    (hwcl : D.wcert.length = Wc.length) (hbl : D.bmask.length = B.length)
    (hBc : B.all (fun b => sqOneK b && B.all fun b' => commK b b') = true)
    (hwm : (Wc.zip D.wmask).all (fun p => Nat.beq p.1 (prodMask B p.2)) = true)
    (hbm : (B.zip D.bmask).all
      (fun p => Nat.blt p.2 (2 ^ (Wc ++ Cc).length) && Nat.beq p.1 (prodMask (Wc ++ Cc) p.2)) = true)
    (hwc : (Wc.zip D.wcert).all (fun p => !(Nat.beq p.1 oneK) && is2AK T.sx p.1 p.2) = true)
    (hwlt : ∀ X ∈ Wc, X < 2 ^ 144)
    (henum : enumZ (fun X m z => Nat.blt m (2 ^ Wc.length) || Nat.beq X oneK || non2AK T.sx X z)
      (Wc ++ Cc) oneK 0 0 D.certs = true) :
    A ≤ Hj ∧ Subgroup.closure {x | x ∈ A ∧ x * x = 1 ∧ x ≠ 1 ∧
      burnsideJ4NP_treeTest (burnsideJ4NP_encJ x) = true} = W := by
  have hG2 : List.Forall₂ PK (wJ ++ cJ) (Wc ++ Cc) := List.rel_append hW2 hC2
  obtain ⟨hbsq, hbcomm⟩ := basis_props hB2 hBc
  have hAab : (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧ ∀ x ∈ A, x * x = 1 := by
    rw [hAdef]
    exact burnsideJ4NP_closure_elemAb (s := {g | g ∈ bJ}) hbcomm hbsq
  have hAH : A ≤ Hj := by
    rw [hAdef]
    exact (Subgroup.closure_le Hj).mpr (mem_Hj_of hB2)
  refine ⟨hAH, ?_⟩
  have hwA : ∀ w ∈ wJ, w ∈ A := by
    intro w hw
    obtain ⟨X, hX, hwX⟩ := forall₂_exists hW2 w hw
    obtain ⟨m, -, hm⟩ := zip_all_mem hwm hwl.symm hX
    rw [pk_beq hwX (pk_prodMask hB2 m) hm, hAdef]
    exact nwFrom_mem (fun b hb => Subgroup.subset_closure hb) (Subgroup.one_mem _) m
  have hGA : ∀ g ∈ wJ ++ cJ, g ∈ A := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hwA g hg
    · exact hcA g hg
  have hAle : A ≤ Subgroup.closure {g | g ∈ wJ ++ cJ} := by
    rw [hAdef, Subgroup.closure_le]
    intro b hb
    obtain ⟨X, hX, hbX⟩ := forall₂_exists hB2 b hb
    obtain ⟨m, -, hm⟩ := zip_all_mem hbm hbl.symm hX
    rw [Bool.and_eq_true] at hm
    rw [pk_beq hbX (pk_prodMask hG2 m) hm.2]
    exact nwFrom_mem (fun g hg => Subgroup.subset_closure hg) (Subgroup.one_mem _) m
  have hGlen : (wJ ++ cJ).length = (Wc ++ Cc).length := forall₂_length hG2
  have hwlen : wJ.length = Wc.length := forall₂_length hW2
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    have hxA : x ∈ A := hx.1
    have hx1 : x ≠ 1 := hx.2.2.1
    have hxt : burnsideJ4NP_treeTest (burnsideJ4NP_encJ x) = true := hx.2.2.2
    have hxG : x ∈ Subgroup.closure {g | g ∈ wJ ++ cJ} := hAle hxA
    obtain ⟨m, hm, hxm⟩ : ∃ m < 2 ^ (wJ ++ cJ).length, x = nwFrom 1 (wJ ++ cJ) m := by
      refine mem_closure_nw ?_ ?_ hxG
      · intro a ha b hb
        exact hAab.1 a (hGA a ha) b (hGA b hb)
      · intro a ha
        exact hAab.2 a (hGA a ha)
    obtain ⟨z, hz⟩ := enumZ_spec henum m (by rwa [← hGlen])
    simp only [Nat.zero_add, Nat.pow_zero, Nat.one_mul, Bool.or_eq_true] at hz
    have hpk : PK (nwFrom 1 (wJ ++ cJ) m) (prodFrom oneK (Wc ++ Cc) m) := pk_prodFrom hG2 pk_one m
    rw [hxm] at hx1 hxt ⊢
    rcases hz with (hz | hz) | hz
    · have hmW : m < 2 ^ wJ.length := by rw [hwlen]; exact Nat.blt_eq.mp hz
      rw [nwFrom_append, Nat.mod_eq_of_lt hmW, Nat.div_eq_of_lt hmW, nwFrom_zero, mul_one, hWdef]
      exact nwFrom_mem (fun w hw => Subgroup.subset_closure hw) (Subgroup.one_mem _) m
    · exact absurd (pk_beq hpk pk_one hz) hx1
    · rw [non2AK_spec hz hpk.2 hsx] at hxt
      exact absurd hxt Bool.false_ne_true
  · rw [hWdef, Subgroup.closure_le]
    intro w hw
    obtain ⟨X, hX, hwX⟩ := forall₂_exists hW2 w hw
    obtain ⟨v, -, hv⟩ := zip_all_mem hwc hwcl.symm hX
    rw [Bool.and_eq_true, Bool.not_eq_true'] at hv
    refine Subgroup.subset_closure ⟨hwA w hw, ?_, fun h1 => ?_, is2AK_spec hv.2 hwX.2 hsx⟩
    · exact hAab.2 w (hwA w hw)
    have hc := pk_canon hwX pk_one (hwlt X hX) oneK_lt h1
    rw [hc, Nat.beq_refl] at hv
    exact Bool.noConfusion hv.1

theorem w_sound {T : Tabs} (hT : tabsOK T = true)
    (hsx : ∀ t < 2048, T.sx.testBit t = (burnsideJ4NP_sextArr ())[t]?.getD false) {k : ℕ}
    {D : WRec} (h : wChk T k D = true) :
    burnsideJ4NP_Rep k ≤ Hj ∧
      Subgroup.closure {x | x ∈ burnsideJ4NP_Rep k ∧ x * x = 1 ∧ x ≠ 1 ∧
        burnsideJ4NP_treeTest (burnsideJ4NP_encJ x) = true} = burnsideJ4NP_Wv k := by
  unfold wChk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hcB, hcW⟩, hwl⟩, hwcl⟩, -⟩, hbl⟩, -⟩, hBc⟩, hwm⟩, hbm⟩, hwc⟩, henum⟩ := h
  have hB2 := forall₂_cc hT _ (List.all_eq_true.mp hcB)
  have hC2 : List.Forall₂ PK (D.comp.map (nwFrom 1 ((treeBasis k).map burnsideJ4NP_treeElt)))
      (D.comp.map (prodMask ((treeBasis k).map (ccT T)))) := by
    have key : ∀ l : List ℕ, List.Forall₂ PK
        (l.map (nwFrom 1 ((treeBasis k).map burnsideJ4NP_treeElt)))
        (l.map (prodMask ((treeBasis k).map (ccT T)))) := by
      intro l
      induction l with
      | nil => exact .nil
      | cons m l ih => exact .cons (pk_prodMask hB2 m) ih
    exact key D.comp
  refine w_core hsx hB2 (forall₂_cc hT _ (List.all_eq_true.mp hcW)) hC2 rfl rfl ?_ hwl hwcl hbl
    hBc hwm hbm hwc ?_ henum
  · intro c hc
    obtain ⟨m, -, rfl⟩ := List.mem_map.mp hc
    exact nwFrom_mem (fun b hb => Subgroup.subset_closure hb) (Subgroup.one_mem _) m
  · intro X hX
    obtain ⟨ce, -, rfl⟩ := List.mem_map.mp hX
    exact M_lt _ _

end W

end CFSG.KC.J4TreeN
