module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBQ
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBBlocksAction
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.U42Basic
public import Certificates.Certificate450107

public noncomputable section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Sporadic.FischerOddCore
open CFSG.ComponentClassification.CatFactsSmall.PSp43 (x45 y45 f45 QA45 QA45_closure)

@[expose] def xyfN : ℕ → Equiv.Perm (Fin 45)
  | 0 => x45
  | 1 => y45
  | _ => f45

@[expose] def blockTau (k : ℕ) : Equiv.Perm (Fin 45) :=
  Quiver.SchreierGraph.evalWord (fun h : Fin 3 => xyfN h) (toLetters 3 (tauWords.getD k []))

@[expose] def blockOpt (m : ℕ) : Option (Fin 45) := if h : m < 45 then some ⟨m, h⟩ else none

@[expose] def blockOf (p : Fin 3510) : Option (Fin 45) := blockOpt (labelOf p)

theorem blockOpt_val (x : Fin 45) : blockOpt (x : ℕ) = some x := by
  simp [blockOpt]

theorem rep_xyfArr_x : Rep 45 xyfArr[0]! x45 := by
  unfold CFSG.Monster.B.Co2.Rep
  decide +kernel

theorem rep_xyfArr_y : Rep 45 xyfArr[1]! y45 := by
  unfold CFSG.Monster.B.Co2.Rep
  decide +kernel

theorem rep_xyfArr_f : Rep 45 xyfArr[2]! f45 := by
  unfold CFSG.Monster.B.Co2.Rep
  decide +kernel

theorem rep_xyfArr : ∀ h < 3, Rep 45 xyfArr[h]! (xyfN h) := by
  intro h hh
  interval_cases h
  · exact rep_xyfArr_x
  · exact rep_xyfArr_y
  · exact rep_xyfArr_f

theorem blockOf_eq_of_arr {lab : Array ℕ} (hlab : ∀ p : Fin 3510, lab[(p : ℕ)]! = labelOf p)
    {A : Array ℕ} {g : Equiv.Perm (Fin 3510)} (hA : Rep 3510 A g)
    (h : allLt 3510 (fun p => lab[A[p]!]! == lab[p]!) = true) (p : Fin 3510) :
    blockOf (g p) = blockOf p := by
  have h1 := allLt_spec h p.2
  simp only [beq_iff_eq] at h1
  rw [hA.apply p.2] at h1
  have e : (⟨(p : ℕ), p.2⟩ : Fin 3510) = p := rfl
  rw [e, hlab (g p), hlab p] at h1
  exact congrArg blockOpt h1

theorem blockOf_act {lab : Array ℕ} (hlab : ∀ p : Fin 3510, lab[(p : ℕ)]! = labelOf p)
    {A : Array ℕ} {g : Equiv.Perm (Fin 3510)} (hA : Rep 3510 A g)
    {Tarr : Array ℕ} {τ : Equiv.Perm (Fin 45)} (hT : Rep 45 Tarr τ)
    (h : allLt 3510 (fun p => lab[A[p]!]! == extGet Tarr lab[p]!) = true) (p : Fin 3510) :
    blockOf (g p) = (blockOf p).map τ := by
  have h1 := allLt_spec h p.2
  simp only [beq_iff_eq] at h1
  rw [hA.apply p.2] at h1
  have e : (⟨(p : ℕ), p.2⟩ : Fin 3510) = p := rfl
  rw [e, hlab (g p), hlab p] at h1
  unfold blockOf
  rw [h1]
  by_cases hm : labelOf p < 45
  · have e2 : extGet Tarr (labelOf p) = (τ ⟨labelOf p, hm⟩ : ℕ) := by
      rw [extGet, if_pos hm, hT.apply hm]
    rw [e2, blockOpt_val]
    simp [blockOpt, hm]
  · have e2 : extGet Tarr (labelOf p) = 45 := by rw [extGet, if_neg hm]
    rw [e2]
    simp [blockOpt, hm]

theorem checkBlocks_spec
    (h : checkBlocks () = true) :
    (∀ (k : Fin 10) (p : Fin 3510), blockOf (cGen k p) = (blockOf p).map (blockTau k)) ∧
    (∀ p : Fin 3510, blockOf (t1 p) = blockOf p) ∧
    (∀ (j : Fin 10) (p : Fin 3510), blockOf (qGen j p) = blockOf p) ∧
    (∀ i : Fin 45, ∃ p : Fin 3510, blockOf p = some i) ∧
    Subgroup.closure (Set.range fun k : Fin 10 => blockTau k) = QA45.originalSubgroup ∧
    (∀ k : Fin 10, Rep 45 (tauArrs ())[(k : ℕ)]! (blockTau k)) := by
  unfold checkBlocks at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb, hτl⟩, hgl⟩, hXs⟩, hw3⟩, hw10⟩, hq⟩, hXinv⟩, hTinv⟩, hgen⟩, hsurj⟩,
    hact⟩, ht1⟩, hqk⟩ := h
  set X := xyfArr with hX
  set Xi := X.map (invCand 45) with hXi
  set T := tauArrs () with hT
  set Ti := T.map (invCand 45) with hTi
  set lab := labelArr () with hlabdef
  set S : Array (Array ℕ) := Array.ofFn (n := 10) fun h => genArr h with hS
  set Si : Array (Array ℕ) := S.map (invCand 3510) with hSi
  set qa : Array (Array ℕ) :=
    Array.ofFn (n := 10) fun j => wordA 3510 S Si (qWords.getD j []) with hqa
  have hXrep : ∀ h < 3, Rep 45 X[h]! (xyfN h) := rep_xyfArr
  have hXirep : ∀ h < 3, Rep 45 Xi[h]! (xyfN h)⁻¹ := fun k hk =>
    rep_inv_of_isInvA (hXrep k hk) (allLt_spec hXinv hk)
  have hlet3 : ∀ k : Fin 10, lettersOK 3 (tauWords.getD k []) = true := by
    intro k
    simp only [List.all_eq_true] at hw3
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hw3 _ (List.getElem_mem _)
  have hlet10 : ∀ j : Fin 3, lettersOK 10 (genWords.getD j []) = true := by
    intro j
    simp only [List.all_eq_true] at hw10
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hw10 _ (List.getElem_mem _)
  have hTrep : ∀ k : Fin 10, Rep 45 T[(k : ℕ)]! (blockTau k) := by
    intro k
    rw [hT, tauArrs, getElem!_ofFn_arr _ k.2]
    exact rep_wordA (gs := xyfN) (j := 3) hXrep hXirep _ (hlet3 k)
  have hTirep : ∀ k : Fin 10, Rep 45 Ti[(k : ℕ)]! (blockTau k)⁻¹ := fun k =>
    rep_inv_of_isInvA (hTrep k) (allLt_spec hTinv k.2)
  have hgenw : ∀ j : Fin 3, xyfN j =
      Quiver.SchreierGraph.evalWord (fun h : Fin 10 => blockTau h)
        (toLetters 10 (genWords.getD j [])) := by
    intro j
    have hrep := rep_wordA (gs := blockTau) (j := 10) (S := T) (Sinv := Ti)
      (fun h hh => hTrep ⟨h, hh⟩) (fun h hh => hTirep ⟨h, hh⟩) _ (hlet10 j)
    exact (eq_of_eqA hrep (hXrep j j.2) (allLt_spec hgen j.2)).symm
  have hclos : Subgroup.closure (Set.range fun k : Fin 10 => blockTau k) =
      QA45.originalSubgroup := by
    rw [QA45_closure]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨k, rfl⟩
      have hmem := Quiver.SchreierGraph.evalWord_mem_closure (fun h : Fin 3 => xyfN h)
        (toLetters 3 (tauWords.getD k []))
      refine Subgroup.closure_mono ?_ hmem
      rintro _ ⟨⟨h, hh⟩, rfl⟩
      interval_cases h
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rw [Subgroup.closure_le]
      have key : ∀ j : Fin 3,
          xyfN j ∈ Subgroup.closure (Set.range fun k : Fin 10 => blockTau k) := by
        intro j
        rw [hgenw j]
        exact Quiver.SchreierGraph.evalWord_mem_closure _ _
      intro x hx
      rcases hx with rfl | rfl | rfl
      · exact key 0
      · exact key 1
      · exact key 2
  have hSrep : ∀ k : Fin 10, Rep 3510 S[(k : ℕ)]! (cGen k) := by
    intro k
    rw [hS, getElem!_ofFn_arr _ k.2]
    exact rep_genArr k
  have hSirep : ∀ k : Fin 10, Rep 3510 Si[(k : ℕ)]! (cGen k)⁻¹ := by
    intro k
    have hk : (k : ℕ) < S.size := by simp [hS]
    rw [hSi, getElem!_pos (S.map (invCand 3510)) (k : ℕ) (by simpa using hk), Array.getElem_map,
      ← getElem!_pos S (k : ℕ) hk, hS, getElem!_ofFn_arr _ k.2]
    exact rep_fi22CentPerm_inv (cLine_lt k)
  have hqrep : ∀ j : Fin 10, Rep 3510 qa[(j : ℕ)]! (qGen j) := by
    intro j
    rw [hqa, getElem!_ofFn_arr _ j.2]
    exact rep_wordA (gs := fun h => fi22CentPerm (cLine h)) (j := 10)
      (fun h hh => hSrep ⟨h, hh⟩) (fun h hh => hSirep ⟨h, hh⟩) _ (lettersOK_qWords j.2 hq)
  have hlab : ∀ p : Fin 3510, lab[(p : ℕ)]! = labelOf p := by
    intro p
    rw [hlabdef, labelArr, getElem!_ofFn_arr _ p.2]
  refine ⟨fun k p => blockOf_act hlab (hSrep k) (hTrep k) (allLt_spec hact k.2) p,
    fun p => blockOf_eq_of_arr hlab rep_t1Arr ht1 p,
    fun j p => blockOf_eq_of_arr hlab (hqrep j) (allLt_spec hqk j.2) p, ?_, hclos, hTrep⟩
  intro i
  have h1 := allLt_spec hsurj i.2
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
  obtain ⟨hlt, hl⟩ := h1
  refine ⟨⟨(blocks45.getD i []).headD 0, hlt⟩, ?_⟩
  unfold blockOf
  have e := hlab ⟨(blocks45.getD i []).headD 0, hlt⟩
  rw [← e]
  show blockOpt lab[(blocks45.getD i []).headD 0]! = some i
  rw [hl, blockOpt_val]

theorem eq_one_of_forall_map_eq {Ω ι : Type*} (β : Ω → Option ι)
    (hsurj : ∀ i : ι, ∃ p, β p = some i) (σ : Equiv.Perm ι) (h : ∀ p, (β p).map σ = β p) :
    σ = 1 := by
  ext i
  obtain ⟨p, hp⟩ := hsurj i
  have h1 := h p
  rw [hp] at h1
  simpa using Option.some.inj h1

theorem mem_map_ker_of_fix (ρ : ↥Cbar →* Equiv.Perm (Fin 45))
    (h1 : ∀ (g : ↥Cbar) (p : Fin 3510), blockOf ((g : Equiv.Perm (Fin 3510)) p) =
      (blockOf p).map (ρ g))
    (hsurj : ∀ i : Fin 45, ∃ p : Fin 3510, blockOf p = some i) {g : Equiv.Perm (Fin 3510)}
    (hg : g ∈ Cbar) (hfix : ∀ p, blockOf (g p) = blockOf p) : g ∈ ρ.ker.map Cbar.subtype := by
  refine ⟨⟨g, hg⟩, ?_, rfl⟩
  refine eq_one_of_forall_map_eq blockOf hsurj _ fun p => ?_
  rw [← h1 ⟨g, hg⟩ p]
  exact hfix p

theorem card_Cbar :
    Nat.card Cbar = 106168320 := by
  obtain ⟨-, hcR, hcP, hct⟩ : fi22R ≤ fi22AutG ∧ fi22CentC ∈ fi22R ∧ fi22CentC ∉ fi22P ∧
      fi22CentC * fi22ExtRep 1 = fi22ExtRep 1 * fi22CentC := by
    obtain ⟨h1, -, -, -, -, h2, h3, h4⟩ := CTUC_Fi22_involution_relational_graph_bounds
    exact ⟨h1, h2, h3, h4⟩
  have hCP : fi22P ⊓ Subgroup.centralizer {fi22ExtRep 1} = fi22H 1 :=
    CTUC_Fi22_five_exact_involution_fixed_subgroups.2.1
  have hcard : Nat.card Cbar = 2 * Nat.card (fi22H 1) := by
    have := card_inf_centralizer_R hcR hcP hct
    rw [hCP] at this
    exact this
  have hH : Nat.card (fi22H 1) = 53084160 := card_fi22H (c := 1) (by norm_num)
  rw [hcard, hH]

theorem exists_rho :
    ∃ ρ : ↥Cbar →* Equiv.Perm (Fin 45), ρ.range = QA45.originalSubgroup ∧
      ρ.ker = Qbar.subgroupOf Cbar ∧
      ∀ (k : Fin 10) (hk : cGen k ∈ Cbar), ρ ⟨cGen k, hk⟩ = blockTau k := by
  obtain ⟨hact, ht1, hq, hsurj, hclos, -⟩ := checkBlocks_spec Certificates.certificate450107
  obtain ⟨ρ, h1, h2, h3⟩ :=
    exists_block_hom cGen Cbar closure_cGen blockOf hsurj (fun k => blockTau k) hact
  have hrange : ρ.range = QA45.originalSubgroup := h3.trans hclos
  have hK : Qbar ≤ ρ.ker.map Cbar.subtype := by
    rw [Qbar, Subgroup.closure_le]
    rintro x (rfl | ⟨j, rfl⟩)
    · exact mem_map_ker_of_fix ρ h1 hsurj (Qbar_le_Cbar t1_mem_Qbar) ht1
    · exact mem_map_ker_of_fix ρ h1 hsurj (Qbar_le_Cbar (qGen_mem_Qbar j)) (hq j)
  have hle : Qbar.subgroupOf Cbar ≤ ρ.ker := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hK (Subgroup.mem_subgroupOf.1 hx)
    have hyx' : y = x := Subtype.ext hyx
    exact hyx' ▸ hy
  have hX := isU42Two_QA45
  have hcardker : Nat.card ρ.ker = 2 ^ 11 := by
    have h4 := Subgroup.card_mul_index ρ.ker
    rw [Subgroup.index_ker, hrange, hX.card_eq, card_Cbar] at h4
    omega
  have hcardsub : Nat.card (Qbar.subgroupOf Cbar) = 2 ^ 11 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe Qbar_le_Cbar).toEquiv).trans card_Qbar
  have hker : Qbar.subgroupOf Cbar = ρ.ker :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardker, hcardsub])
  exact ⟨ρ, hrange, hker.symm, h2⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB
