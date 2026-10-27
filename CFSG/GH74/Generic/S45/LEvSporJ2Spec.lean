module

public import CFSG.GH74.Generic.S45.LEvSporSpec
public import CFSG.GH74.Generic.S45.LEvSporLeaf1
public import Certificates.Data.GH74EvSporCheck
public meta import Certificates.Data.GH74EvSporCheck
public import CFSG.Sporadic.Schreier.PairJ2CertInputs
public import CFSG.Sporadic.Schreier.PairJ2CheckInputs
public import CFSG.Sporadic.SmallOddCore.J2CheckInputs
public meta import CFSG.Sporadic.SmallOddCore.J2Data
public meta import CFSG.Sporadic.Schreier.PairJ2Check
public import CFSG.Sporadic.Schreier.PairJ2Order
public import CFSG.Sporadic.SmallOddCore.J2
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutTables
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Sporadic.Th.F2Spec

public section

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open scoped commutatorElement

namespace CFSG.GH74.Generic.S45.EvSpor

open CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Certificates.Native
  CFSG.ComponentClassification.J2Cover

theorem j2Row2A_mem : j2Row2A ∈ j2Rows := List.getElem_mem _
theorem j2Row2B_mem : j2Row2B ∈ j2Rows := List.getElem_mem _
theorem j2Row2A_centOrder : j2Row2A.centOrder = 1920 := rfl
theorem j2Row2B_centOrder : j2Row2B.centOrder = 240 := rfl
theorem j2Row2A_outer : j2Row2A.outer = false := rfl
theorem j2Row2B_outer : j2Row2B.outer = false := rfl

theorem j2Rows_cases (r : ClassRow) (hr : r ∈ j2Rows) :
    r.outer = true ∨ r = j2Row2B ∨ r = j2Row2A := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hr
  have hlen : j2Rows.length = 3 := rfl
  rw [hlen] at hi
  interval_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem j2_reps (h : j2RepsOK = true) :
    Rep 315 j2OuterTbl (tp 315 j2OuterTbl) ∧ Rep 315 j2Row2A.rep (tp 315 j2Row2A.rep) ∧
      Rep 315 j2Row2B.rep (tp 315 j2Row2B.rep) := by
  simp only [j2RepsOK, Bool.and_eq_true] at h
  exact ⟨rep_tp h.1.1, rep_tp h.1.2, rep_tp h.2⟩

theorem j2_rows_spec :
    (∀ r ∈ j2Rows, tp 315 r.rep ∈ j2R ∧ orderOf (tp 315 r.rep) = 2 ∧
      (r.outer = true ↔ tp 315 r.rep ∉ j2P) ∧
      j2C r = j2P ⊓ Subgroup.centralizer ({tp 315 r.rep} : Set (Equiv.Perm (Fin 315))) ∧
      Nat.card ↥(j2P ⊓ Subgroup.centralizer ({tp 315 r.rep} : Set (Equiv.Perm (Fin 315)))) =
        r.centOrder) ∧
    (∀ t ∈ j2R, orderOf t = 2 → ∃ r ∈ j2Rows, ∃ g ∈ j2P, t = g * tp 315 r.rep * g⁻¹) := by
  obtain ⟨-, -, -, hrows, hcover, -⟩ := ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  refine ⟨fun r hr => ?_, hcover⟩
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hrows r hr
  exact ⟨h1, h2, h3, h4, h5⟩

theorem j2_C2A_enums
    (h : j2C2AEnumOK = true) :
    EnumsSub 315 j2C2A (j2P ⊓ Subgroup.centralizer ({tp 315 j2Row2A.rep} :
      Set (Equiv.Perm (Fin 315)))) ∧ invsOK 315 j2C2A = true := by
  have hn : (315 : ℕ) < 2 ^ 32 := by norm_num
  rw [j2C2AEnumOK, Bool.and_eq_true] at h
  obtain ⟨⟨hE, -, -⟩, hinv⟩ := And.intro (enumOK_spec hn h.1) h.2
  refine ⟨?_, hinv⟩
  have hC := (j2_rows_spec.1 j2Row2A j2Row2A_mem).2.2.2.1
  rw [← hC]
  exact hE

theorem j2_C2B_enums
    (h : j2C2BEnumOK = true) :
    EnumsSub 315 j2C2B (j2P ⊓ Subgroup.centralizer ({tp 315 j2Row2B.rep} :
      Set (Equiv.Perm (Fin 315)))) ∧ invsOK 315 j2C2B = true := by
  have hn : (315 : ℕ) < 2 ^ 32 := by norm_num
  rw [j2C2BEnumOK, Bool.and_eq_true] at h
  obtain ⟨⟨hE, -, -⟩, hinv⟩ := And.intro (enumOK_spec hn h.1) h.2
  refine ⟨?_, hinv⟩
  have hC := (j2_rows_spec.1 j2Row2B j2Row2B_mem).2.2.2.1
  rw [← hC]
  exact hE

theorem j2_gens_mem {gs : List Table}
    (hrep : ∀ g ∈ gs, Rep 315 g (tp 315 g)) (h : gs.all j2Sift = true) :
    closure (tp 315 '' {x | x ∈ gs.toArray}) ≤ j2P := by
  rw [closure_le]
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ gs := List.mem_toArray.mp hx
  exact (j2_groupData.sift x (tp 315 x) (hrep x hx')).1 ((List.all_eq_true.1 h) x hx')

theorem conj_mem_closure_of_gens {S : Set (Equiv.Perm (Fin 315))} {e : Equiv.Perm (Fin 315)}
    (h : ∀ s ∈ S, e * s * e⁻¹ ∈ closure S) : ∀ m ∈ closure S, e * m * e⁻¹ ∈ closure S := by
  intro m hm
  have : closure S ≤ (closure S).comap (MulAut.conj e).toMonoidHom :=
    (closure_le _).2 fun s hs => h s hs
  exact this hm

theorem j2_Kb_facts
    (h : j2KbEnumOK = true) :
    EnumsSub 315 j2Kb (closure (tp 315 '' {x | x ∈ j2KbGens.toArray})) ∧
      Nat.card ↥(closure (tp 315 '' {x | x ∈ j2KbGens.toArray})) = 60 ∧
      closure (tp 315 '' {x | x ∈ j2KbGens.toArray}) ≤ j2P ∧
      Rep 315 j2KbA (tp 315 j2KbA) ∧ Rep 315 j2KbB (tp 315 j2KbB) := by
  have hn : (315 : ℕ) < 2 ^ 32 := by norm_num
  rw [j2KbEnumOK, Bool.and_eq_true] at h
  obtain ⟨hE, hc, hrep⟩ := enumOK_spec hn h.1
  exact ⟨hE, hc, j2_gens_mem hrep h.2, hrep _ (by simp [j2KbGens]), hrep _ (by simp [j2KbGens])⟩

theorem j2_E16_facts
    (hKb : j2KbEnumOK = true) (h : j2E16OK = true) :
    ∃ E : Subgroup (Equiv.Perm (Fin 315)),
      E ≤ j2P ⊓ Subgroup.normalizer
        ((closure (tp 315 '' {x | x ∈ j2KbGens.toArray}) : Subgroup (Equiv.Perm (Fin 315))) :
          Set (Equiv.Perm (Fin 315))) ∧ IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 16 := by
  have hn : (315 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hMenum, -, -, hA, hB⟩ := j2_Kb_facts hKb
  rw [j2E16OK] at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨hEnum, hsift⟩, hab⟩, hconj⟩ := h
  obtain ⟨hEE, hEc, hrep⟩ := enumOK_spec hn hEnum
  refine ⟨closure (tp 315 '' {x | x ∈ j2E16Gens.toArray}), ?_, ?_, hEc⟩
  · rw [le_inf_iff]
    refine ⟨j2_gens_mem hrep (List.all_eq_true.2 hsift), ?_⟩
    rw [closure_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ j2E16Gens := List.mem_toArray.mp hx
    have hxrep := hrep x hx'
    have hxinv : Rep 315 (invT 315 x) (tp 315 x)⁻¹ := rep_invT_of_rep hn hxrep
    have hc := (conjIn_spec hMenum hA hB hxrep hxinv).1 (hconj x hx')
    refine mem_normalizer_of_conj_le ?_
    refine conj_mem_closure_of_gens (S := tp 315 '' {x | x ∈ j2KbGens.toArray}) ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ j2KbGens := List.mem_toArray.mp hy
    simp only [j2KbGens, List.mem_cons, List.not_mem_nil, or_false] at hy'
    rcases hy' with rfl | rfl
    · exact hc.1
    · exact hc.2
  · rw [CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian]
    have hall := elemAb_spec hn hEE hab
    refine ⟨⟨⟨fun a b => Subtype.ext ((hall a a.2).2 b b.2)⟩⟩, fun x hx => ?_⟩
    rw [pow_two]
    exact (hall x hx).1

theorem j2_normCount_levelTables :
    normCount 315 (levelTables j2Chain) j2Kb j2KbA j2KbB = j2NormCount :=
  congrArg (fun T => normCount 315 T j2Kb j2KbA j2KbB)
    (levelTables_eq j2ChainArrays (chainCheckFacts PairJ2.chain_check.1))

theorem j2_norm_card
    (hKb : j2KbEnumOK = true) (hcount : j2NormCount = 720) :
    Nat.card ↥(j2P ⊓ Subgroup.normalizer
      ((closure (tp 315 '' {x | x ∈ j2KbGens.toArray}) : Subgroup (Equiv.Perm (Fin 315))) :
        Set (Equiv.Perm (Fin 315)))) = 720 := by
  have hn : (315 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hMenum, -, -, hA, hB⟩ := j2_Kb_facts hKb
  set M : Subgroup (Equiv.Perm (Fin 315)) := closure (tp 315 '' {x | x ∈ j2KbGens.toArray})
    with hM
  have hcard := card_normCount hn j2Chain_valid.1 hMenum hA hB
  rw [j2_normCount_levelTables, hcount] at hcard
  rw [← hcard]
  have haM : tp 315 j2KbA ∈ M := subset_closure ⟨j2KbA, by simp [j2KbGens], rfl⟩
  have hbM : tp 315 j2KbB ∈ M := subset_closure ⟨j2KbB, by simp [j2KbGens], rfl⟩
  refine Nat.card_congr
    { toFun := fun y => ⟨⟨y.1, by rw [← j2P_eq_original]; exact y.2.1⟩,
        (Subgroup.mem_normalizer_iff.1 y.2.2 _).1 haM, (Subgroup.mem_normalizer_iff.1 y.2.2 _).1 hbM⟩
      invFun := fun z => ⟨z.1.1, by rw [j2P_eq_original]; exact z.1.2, ?_⟩
      left_inv := fun y => rfl
      right_inv := fun z => rfl }
  exact mem_normalizer_of_conj_le (conj_mem_closure_of_gens (S := tp 315 '' {x | x ∈ j2KbGens.toArray})
    (by
      rintro _ ⟨y, hy, rfl⟩
      have hy' : y ∈ j2KbGens := List.mem_toArray.mp hy
      simp only [j2KbGens, List.mem_cons, List.not_mem_nil, or_false] at hy'
      rcases hy' with rfl | rfl
      · exact z.2.1
      · exact z.2.2))

theorem j2_row_mem_P
    {r : ClassRow} (hr : r ∈ j2Rows) (hout : r.outer = false) :
    tp 315 r.rep ∈ j2P := by
  by_contra h
  have := ((j2_rows_spec.1 r hr).2.2.1).2 h
  rw [hout] at this
  exact Bool.noConfusion this

theorem j2_cover :
    ∀ y ∈ j2P, orderOf y = 2 →
    (∃ g ∈ j2P, y = g * tp 315 j2Row2A.rep * g⁻¹) ∨
      ∃ g ∈ j2P, y = g * tp 315 j2Row2B.rep * g⁻¹ := by
  intro y hy hy2
  obtain ⟨r, hr, g, hg, hyg⟩ := j2_rows_spec.2 y (le_sup_left (a := j2P) hy) hy2
  rcases j2Rows_cases r hr with hout | rfl | rfl
  · exfalso
    have h3 := ((j2_rows_spec.1 r hr).2.2.1).1 hout
    apply h3
    have : tp 315 r.rep = g⁻¹ * y * g := by rw [hyg]; group
    rw [this]
    exact j2P.mul_mem (j2P.mul_mem (j2P.inv_mem hg) hy) hg
  · exact Or.inr ⟨g, hg, hyg⟩
  · exact Or.inl ⟨g, hg, hyg⟩

end CFSG.GH74.Generic.S45.EvSpor
