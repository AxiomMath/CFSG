module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7SylowAnn
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7SylowGen
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7SylowTuple
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7SylowBasic

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction
open CFSG.SeitzReduction.E6Pilot (rootProd RootCommFamily conjCoeff)

section Lists

theorem oddDerivMemB_of_mem {n : ℕ} {v : Fin n → ℤ} {L : List (Fin n → ℤ)} (h : v ∈ L) :
    oddDerivMemB v L = true :=
  List.any_eq_true.2 ⟨v, h, oddDerivVecEq_self v⟩

theorem not_mem_of_oddDerivMemB_eq_false {n : ℕ} {v : Fin n → ℤ} {L : List (Fin n → ℤ)}
    (h : oddDerivMemB v L = false) : v ∉ L := fun hv => by
  rw [oddDerivMemB_of_mem hv] at h
  exact Bool.false_ne_true h.symm

theorem nodup_of_e7NodupB : ∀ {l : List (Fin Tag.E7.rank → ℤ)}, e7NodupB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    simp only [e7NodupB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    exact List.nodup_cons.2 ⟨not_mem_of_oddDerivMemB_eq_false h.1, nodup_of_e7NodupB h.2⟩

theorem mem_of_mem_e7Erase {a : Fin Tag.E7.rank → ℤ} :
    ∀ {l : List (Fin Tag.E7.rank → ℤ)} {y : Fin Tag.E7.rank → ℤ}, y ∈ e7Erase a l → y ∈ l
  | [], _, h => by simp [e7Erase] at h
  | b :: l, y, h => by
    simp only [e7Erase] at h
    split_ifs at h
    · exact List.mem_cons_of_mem _ h
    · rcases List.mem_cons.1 h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_of_mem_e7Erase h)

theorem perm_cons_e7Erase {a : Fin Tag.E7.rank → ℤ} :
    ∀ {l : List (Fin Tag.E7.rank → ℤ)}, a ∈ l → l.Perm (a :: e7Erase a l)
  | [], h => by simp at h
  | b :: l, h => by
    simp only [e7Erase]
    split_ifs with hb
    · rw [eq_of_oddDerivVecEq hb]
    · have hab : a ≠ b := fun e => by
        rw [e, oddDerivVecEq_self] at hb
        exact hb rfl
      have ha := (List.mem_cons.1 h).resolve_left hab
      exact (List.Perm.cons b (perm_cons_e7Erase ha)).trans (List.Perm.swap a b _)

theorem nodup_e7Erase {a : Fin Tag.E7.rank → ℤ} {l : List (Fin Tag.E7.rank → ℤ)}
    (hnd : l.Nodup) (ha : a ∈ l) : (e7Erase a l).Nodup :=
  (List.nodup_cons.1 ((perm_cons_e7Erase ha).nodup_iff.1 hnd)).2

end Lists

section Kill

variable {K : Type} [Field K]

theorem eq_zero_of_e7KillStepB [CharP K 2] {D C : List (Fin Tag.E7.rank → ℤ)}
    {ℓ β : Fin Tag.E7.rank → ℤ} (hk : e7KillStepB D C ℓ β = true) {w : ModGL .E7 K}
    (hwβ : w * pinnedX .E7 K β 1 = pinnedX .E7 K β 1 * w) (hCnd : C.Nodup)
    (hCp : ∀ y ∈ C, IsRoot .E7 y ∧ 0 < height y) (hC : RootCommFamily .E7 K C)
    {c : (Fin Tag.E7.rank → ℤ) → K} (hw : w = rootProd .E7 K C c) : c ℓ = 0 := by
  classical
  simp only [e7KillStepB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hℓC, -⟩, hβr⟩, hρr⟩, hρpos⟩, hρC⟩, hβℓ⟩, hCy⟩, hβρ⟩, hβρr⟩, hρcomm⟩,
    hCB⟩ := hk
  have hℓC := mem_of_oddDerivMemB hℓC
  have hβ := isRoot_of_oddDerivIsRootB hβr
  have hρ := isRoot_of_oddDerivIsRootB hρr
  have hρC := not_mem_of_oddDerivMemB_eq_false hρC
  have hρpos : 0 < height (ℓ + β) := by rwa [oddDerivHeight_eq] at hρpos
  set ρ := ℓ + β with hρdef
  set l := C ++ [ρ] with hl
  set c' : (Fin Tag.E7.rank → ℤ) → K := fun r => if r ∈ C then c r else 0 with hc'
  have hlnd : l.Nodup := List.nodup_append.2 ⟨hCnd, List.nodup_singleton _, fun a ha b hb e =>
    hρC (by
      rw [List.mem_singleton] at hb
      rw [← hb, ← e]
      exact ha)⟩
  have hlp : ∀ y ∈ l, IsRoot .E7 y ∧ 0 < height y := fun y hy => by
    rcases List.mem_append.1 hy with hy | hy
    · exact hCp y hy
    · rw [List.mem_singleton.1 hy]
      exact ⟨hρ, hρpos⟩
  have hρy : ∀ y ∈ C, ρ ≠ -y ∧ ¬IsRoot .E7 (ρ + y) := fun y hy => of_e7SCommB (hρcomm y hy)
  have hlfam : RootCommFamily .E7 K l := by
    intro a ha b hb s t
    rcases List.mem_append.1 ha with ha | ha <;> rcases List.mem_append.1 hb with hb | hb
    · exact hC a ha b hb s t
    · rw [List.mem_singleton.1 hb]
      exact (commute_pinnedX_of_oddDeriv hρ (hCp a ha).1 (hρy a ha).1 (hρy a ha).2 t s).symm
    · rw [List.mem_singleton.1 ha]
      exact commute_pinnedX_of_oddDeriv hρ (hCp b hb).1 (hρy b hb).1 (hρy b hb).2 s t
    · rw [List.mem_singleton.1 ha, List.mem_singleton.1 hb]
      show pinnedX .E7 K ρ s * pinnedX .E7 K ρ t = pinnedX .E7 K ρ t * pinnedX .E7 K ρ s
      rw [← pinnedX_add, ← pinnedX_add, add_comm]
  have hwl : w = rootProd .E7 K l c' := by
    rw [hw, hl, E6Pilot.rootProd_append, E6Pilot.rootProd_cons, E6Pilot.rootProd_nil]
    have h0 : c' ρ = 0 := by
      show (if ρ ∈ C then c ρ else 0) = 0
      exact ite_eq_right hρC
    rw [h0, pinnedX_zero, mul_one, mul_one]
    exact E6Pilot.rootProd_congr fun y hy => by
      show c y = if y ∈ C then c y else 0
      exact (ite_eq_left hy).symm
  have hB : ∀ β' ∈ [β], IsRoot .E7 β' ∧ ∀ y ∈ l, β' ≠ -y ∧ (IsRoot .E7 (β' + y) → β' + y ∈ l) := by
    intro β' hβ'
    rw [List.mem_singleton.1 hβ']
    refine ⟨hβ, fun y hy => ?_⟩
    rcases List.mem_append.1 hy with hy | hy
    · obtain ⟨hne, hor⟩ := hCy y hy
      refine ⟨ne_of_oddDerivVecEq_eq_false hne, fun hr => ?_⟩
      rcases hor with he | hn
      · rw [eq_of_oddDerivVecEq he, add_comm]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      · exact absurd hr (not_isRoot_of_oddDerivNotRootB hn)
    · rw [List.mem_singleton.1 hy]
      exact ⟨ne_of_oddDerivVecEq_eq_false hβρ, fun hr =>
        absurd hr (not_isRoot_of_oddDerivNotRootB hβρr)⟩
  have hCl : ∀ s ∈ C, s ∈ l := fun s hs => List.mem_append_left _ hs
  have hCB' : ∀ s ∈ C, ∀ β' ∈ [β], s - β' ∉ l := by
    intro s hs β' hβ'
    rw [List.mem_singleton.1 hβ']
    exact not_mem_of_oddDerivMemB_eq_false (hCB s hs)
  have hRB : ∀ ρ' ∈ l, ρ' ∉ C → ∀ β' ∈ [β], ρ' - β' ∈ l → ρ' - β' ∈ C := by
    intro ρ' hρ' hρ'C β' hβ' _
    rcases List.mem_append.1 hρ' with h | h
    · exact absurd h hρ'C
    · rw [List.mem_singleton.1 h, List.mem_singleton.1 hβ', hρdef, add_sub_cancel_right]
      exact hℓC
  have hcomm : ([β].map fun β' => pinnedX .E7 K β' 1).prod * rootProd .E7 K l c' =
      rootProd .E7 K l c' * ([β].map fun β' => pinnedX .E7 K β' 1).prod := by
    rw [List.map_singleton, List.prod_singleton, ← hwl]
    exact hwβ.symm
  have hsum := sum_eq_zero_of_commute_conj hlnd hlp hlfam hCl hB hCB' hRB c' hcomm
    (List.mem_append_right _ (List.mem_singleton_self _)) hρC
  have hℓ : ρ - β = ℓ := by rw [hρdef, add_sub_cancel_right]
  rw [List.map_singleton, List.sum_singleton, hℓ,
    ite_eq_left ⟨hℓC, ne_of_oddDerivVecEq_eq_false hβℓ⟩] at hsum
  have h1 : c' ℓ = c ℓ := by
    show (if ℓ ∈ C then c ℓ else 0) = c ℓ
    exact ite_eq_left hℓC
  rw [← h1]
  exact hsum

theorem e7KillsB_sound [CharP K 2] {D : List (Fin Tag.E7.rank → ℤ)} {w : ModGL .E7 K}
    (hwD : ∀ β ∈ D, w * pinnedX .E7 K β 1 = pinnedX .E7 K β 1 * w)
    (c : (Fin Tag.E7.rank → ℤ) → K) :
    ∀ (ks : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ)))
      (C C' : List (Fin Tag.E7.rank → ℤ)), e7KillsB D C ks = some C' → C.Nodup →
      (∀ y ∈ C, IsRoot .E7 y ∧ 0 < height y) → RootCommFamily .E7 K C →
        w = rootProd .E7 K C c → C'.Nodup ∧ (∀ y ∈ C', y ∈ C) ∧ w = rootProd .E7 K C' c := by
  intro ks
  induction ks with
  | nil =>
    intro C C' h hCnd _ _ hw
    simp only [e7KillsB, Option.some.injEq] at h
    subst h
    exact ⟨hCnd, fun y hy => hy, hw⟩
  | cons p ks ih =>
    intro C C' h hCnd hCp hC hw
    simp only [e7KillsB] at h
    split_ifs at h with hk
    have hℓC : p.1 ∈ C := by
      simp only [e7KillStepB, Bool.and_eq_true] at hk
      exact mem_of_oddDerivMemB hk.1.1.1.1.1.1.1.1.1.1.1
    have hβD : p.2 ∈ D := by
      simp only [e7KillStepB, Bool.and_eq_true] at hk
      exact mem_of_oddDerivMemB hk.1.1.1.1.1.1.1.1.1.1.2
    have hc0 := eq_zero_of_e7KillStepB hk (hwD p.2 hβD) hCnd hCp hC hw
    have hsub : ∀ y ∈ e7Erase p.1 C, y ∈ C := fun y hy => mem_of_mem_e7Erase hy
    have hw' : w = rootProd .E7 K (e7Erase p.1 C) c := by
      rw [hw, E6Pilot.rootProd_perm hC (perm_cons_e7Erase hℓC), E6Pilot.rootProd_cons, hc0,
        pinnedX_zero, one_mul]
    obtain ⟨h1, h2, h3⟩ := ih (e7Erase p.1 C) C' h (nodup_e7Erase hCnd hℓC)
      (fun y hy => hCp y (hsub y hy)) (hC.of_sublist hsub) hw'
    exact ⟨h1, fun y hy => hsub y (h2 y hy), h3⟩

end Kill

section Mix

theorem eq_of_e7ListEqB : ∀ {l l' : List (Fin Tag.E7.rank → ℤ)}, e7ListEqB l l' = true → l = l'
  | [], [], _ => rfl
  | a :: l, b :: l', h => by
    simp only [e7ListEqB, Bool.and_eq_true] at h
    rw [eq_of_oddDerivVecEq h.1, eq_of_e7ListEqB h.2]
  | [], _ :: _, h => by simp [e7ListEqB] at h
  | _ :: _, [], h => by simp [e7ListEqB] at h

variable {K : Type} [Field K]

theorem sum_ite_eq_sum_e7MixSources {F : List (Fin Tag.E7.rank → ℤ)}
    (c : (Fin Tag.E7.rank → ℤ) → K) (ρ : Fin Tag.E7.rank → ℤ) :
    ∀ B : List (Fin Tag.E7.rank → ℤ),
      (B.map fun β => if ρ - β ∈ F ∧ β ≠ ρ - β then c (ρ - β) else 0).sum =
        ((e7MixSources F B ρ).map c).sum
  | [] => by simp [e7MixSources]
  | β :: B => by
    classical
    have ih := sum_ite_eq_sum_e7MixSources (F := F) c ρ B
    simp only [e7MixSources, List.map_cons, List.sum_cons, List.filterMap_cons] at ih ⊢
    by_cases h : ρ - β ∈ F ∧ β ≠ ρ - β
    · have hb : (oddDerivMemB (ρ - β) F && !oddDerivVecEq β (ρ - β)) = true := by
        rw [oddDerivMemB_of_mem h.1, Bool.true_and, Bool.not_eq_true']
        exact Bool.eq_false_iff.2 fun e => h.2 (eq_of_oddDerivVecEq e)
      rw [ite_eq_left h, ite_eq_left hb, List.map_cons, List.sum_cons, ih]
    · have hb : (oddDerivMemB (ρ - β) F && !oddDerivVecEq β (ρ - β)) = false := by
        rw [Bool.eq_false_iff]
        intro e
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at e
        exact h ⟨mem_of_oddDerivMemB e.1, ne_of_oddDerivVecEq_eq_false e.2⟩
      rw [ite_eq_right h, ite_eq_right (by rw [hb]; exact Bool.false_ne_true), zero_add, ih]

end Mix

section MixSound

variable {K : Type} [Field K]

theorem e7MixB_facts {F : List (Fin Tag.E7.rank → ℤ)} {m : E7Mix} (h : e7MixB F m = true) :
    m.rhos.Nodup ∧ (∀ ρ ∈ m.rhos, IsRoot .E7 ρ ∧ 0 < height ρ ∧ ρ ∉ F) ∧
      (∀ ρ ∈ m.rhos, ∀ s ∈ F, ρ ≠ -s ∧ ¬IsRoot .E7 (ρ + s)) ∧
      (∀ ρ ∈ m.rhos, ∀ ρ' ∈ m.rhos, ρ = ρ' ∨ (ρ ≠ -ρ' ∧ ¬IsRoot .E7 (ρ + ρ'))) ∧
      (∀ β ∈ e7WordImage m.word F, IsRoot .E7 β ∧ ∀ y ∈ F ++ m.rhos,
        β ≠ -y ∧ (IsRoot .E7 (β + y) → β + y ∈ F ++ m.rhos)) ∧
      (∀ s ∈ F, ∀ β ∈ e7WordImage m.word F, s - β ∉ F ++ m.rhos) ∧
      (∀ ρ ∈ m.rhos, ∀ β ∈ e7WordImage m.word F, ρ - β ∉ m.rhos) ∧
      (∀ ρ ∈ m.rhos, ∃ e ∈ m.eqs, e.1 = ρ) ∧
      ∀ e ∈ m.eqs, e.1 ∈ m.rhos ∧
        e7MixSources F (e7WordImage m.word F) e.1 = [e.2.1, e.2.2] := by
  simp only [e7MixB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨nodup_of_e7NodupB h1, fun ρ hρ => ?_, fun ρ hρ s hs => of_e7SCommB (h3 ρ hρ s hs),
    fun ρ hρ ρ' hρ' => ?_, fun β hβ => ?_, fun s hs β hβ =>
      not_mem_of_oddDerivMemB_eq_false (h6 s hs β hβ), fun ρ hρ β hβ =>
      not_mem_of_oddDerivMemB_eq_false (h7 ρ hρ β hβ), fun ρ hρ => ?_, fun e he => ?_⟩
  · obtain ⟨⟨hr, hp⟩, hF⟩ := h2 ρ hρ
    exact ⟨isRoot_of_oddDerivIsRootB hr, by rwa [oddDerivHeight_eq] at hp,
      not_mem_of_oddDerivMemB_eq_false hF⟩
  · rcases h4 ρ hρ ρ' hρ' with he | hc
    · exact Or.inl (eq_of_oddDerivVecEq he)
    · exact Or.inr (of_e7SCommB hc)
  · obtain ⟨hr, hy⟩ := h5 β hβ
    refine ⟨isRoot_of_oddDerivIsRootB hr, fun y hy' => ?_⟩
    obtain ⟨hne, hor⟩ := hy y hy'
    refine ⟨ne_of_oddDerivVecEq_eq_false hne, fun hroot => ?_⟩
    rcases hor with hn | hm
    · exact absurd hroot (not_isRoot_of_oddDerivNotRootB hn)
    · exact mem_of_oddDerivMemB hm
  · obtain ⟨e, he, he'⟩ := h8 ρ hρ
    exact ⟨e, he, eq_of_oddDerivVecEq he'⟩
  · obtain ⟨hρ, hs⟩ := h9 e he
    exact ⟨mem_of_oddDerivMemB hρ, eq_of_e7ListEqB hs⟩

theorem mem_of_mem_e7MixSources {F B : List (Fin Tag.E7.rank → ℤ)} {ρ x : Fin Tag.E7.rank → ℤ}
    (h : x ∈ e7MixSources F B ρ) : x ∈ F := by
  obtain ⟨β, -, hβ⟩ := List.mem_filterMap.1 h
  split_ifs at hβ with hb
  simp only [Option.some.injEq] at hβ
  rw [← hβ]
  simp only [Bool.and_eq_true] at hb
  exact mem_of_oddDerivMemB hb.1

end MixSound

section MixMain

variable {K : Type} [Field K]

theorem e7MixB_sound [CharP K 2] {F : List (Fin Tag.E7.rank → ℤ)}
    (hFp : ∀ σ ∈ F, IsRoot .E7 σ ∧ 0 < height σ) (hFnd : F.Nodup) (hFc : RootCommFamily .E7 K F)
    {m : E7Mix} (hm : e7MixB F m = true) :
    Commute ((e7WordImage m.word F).map fun β => pinnedX .E7 K β 1).prod (rootProd .E7 K F 1) ∧
      ∀ c : (Fin Tag.E7.rank → ℤ) → K,
        Commute ((e7WordImage m.word F).map fun β => pinnedX .E7 K β 1).prod
          (rootProd .E7 K F c) → ∀ e ∈ m.eqs, c e.2.1 = c e.2.2 := by
  obtain ⟨hRnd, hRp, hRF, hRR, hB, hCB, hRB, hRe, heqs⟩ := e7MixB_facts hm
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hlnd : (F ++ m.rhos).Nodup := List.nodup_append.2 ⟨hFnd, hRnd, fun a ha b hb e =>
    (hRp b hb).2.2 (by rw [← e]; exact ha)⟩
  have hlp : ∀ y ∈ F ++ m.rhos, IsRoot .E7 y ∧ 0 < height y := fun y hy => by
    rcases List.mem_append.1 hy with hy | hy
    · exact hFp y hy
    · exact ⟨(hRp y hy).1, (hRp y hy).2.1⟩
  have hlr : ∀ y ∈ F ++ m.rhos, IsRoot .E7 y := fun y hy => (hlp y hy).1
  have hlfam : RootCommFamily .E7 K (F ++ m.rhos) := by
    intro a ha b hb s t
    rcases List.mem_append.1 ha with ha | ha <;> rcases List.mem_append.1 hb with hb | hb
    · exact hFc a ha b hb s t
    · exact (commute_pinnedX_of_oddDeriv (hRp b hb).1 (hFp a ha).1 (hRF b hb a ha).1
        (hRF b hb a ha).2 t s).symm
    · exact commute_pinnedX_of_oddDeriv (hRp a ha).1 (hFp b hb).1 (hRF a ha b hb).1
        (hRF a ha b hb).2 s t
    · rcases hRR a ha b hb with rfl | hc
      · show pinnedX .E7 K a s * pinnedX .E7 K a t = pinnedX .E7 K a t * pinnedX .E7 K a s
        rw [← pinnedX_add, ← pinnedX_add, add_comm]
      · exact commute_pinnedX_of_oddDeriv (hRp a ha).1 (hRp b hb).1 hc.1 hc.2 s t
  have hCl : ∀ s ∈ F, s ∈ F ++ m.rhos := fun s hs => List.mem_append_left _ hs
  have hRB' : ∀ ρ ∈ F ++ m.rhos, ρ ∉ F → ∀ β ∈ e7WordImage m.word F,
      ρ - β ∈ F ++ m.rhos → ρ - β ∈ F := fun ρ hρ hρF β hβ h =>
    (List.mem_append.1 h).resolve_right (hRB ρ ((List.mem_append.1 hρ).resolve_left hρF) β hβ)
  have hext : ∀ c : (Fin Tag.E7.rank → ℤ) → K,
      rootProd .E7 K (F ++ m.rhos) (fun r => if r ∈ F then c r else 0) = rootProd .E7 K F c := by
    intro c
    rw [E6Pilot.rootProd_append]
    have h0 : rootProd .E7 K m.rhos (fun r => if r ∈ F then c r else 0) = 1 := by
      have e : rootProd .E7 K m.rhos (fun r => if r ∈ F then c r else 0) =
          rootProd .E7 K m.rhos 0 :=
        E6Pilot.rootProd_congr fun ρ hρ => by simp [(hRp ρ hρ).2.2]
      rw [e, E6Pilot.rootProd_zero]
    rw [h0, mul_one]
    exact E6Pilot.rootProd_congr fun s hs => by simp [hs]
  have hsum : ∀ c : (Fin Tag.E7.rank → ℤ) → K, ∀ e ∈ m.eqs,
      ((e7WordImage m.word F).map fun β => if e.1 - β ∈ F ∧ β ≠ e.1 - β then
        (fun r => if r ∈ F then c r else 0) (e.1 - β) else 0).sum = c e.2.1 + c e.2.2 := by
    intro c e he
    refine (sum_ite_eq_sum_e7MixSources (F := F) (fun r => if r ∈ F then c r else 0) e.1
      _).trans ?_
    rw [(heqs e he).2]
    have h1 : e.2.1 ∈ F := mem_of_mem_e7MixSources (B := e7WordImage m.word F) (ρ := e.1)
      (by rw [(heqs e he).2]; exact List.mem_cons_self)
    have h2' : e.2.2 ∈ F := mem_of_mem_e7MixSources (B := e7WordImage m.word F) (ρ := e.1)
      (by rw [(heqs e he).2]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      ite_eq_left h1, ite_eq_left h2']
  refine ⟨?_, fun c hc e he => ?_⟩
  ·
    have hconj := conj_list_rootProd hlnd hlr hlfam hB
      (fun r => if r ∈ F then (1 : (Fin Tag.E7.rank → ℤ) → K) r else 0)
    have hcoef := conjCoeffList_apply hlnd hlr hCl hCB hRB'
      (fun r => if r ∈ F then (1 : (Fin Tag.E7.rank → ℤ) → K) r else 0)
    have hfix : rootProd .E7 K (F ++ m.rhos) (conjCoeffList K (e7WordImage m.word F)
        (F ++ m.rhos) fun r => if r ∈ F then (1 : (Fin Tag.E7.rank → ℤ) → K) r else 0) =
        rootProd .E7 K (F ++ m.rhos)
          (fun r => if r ∈ F then (1 : (Fin Tag.E7.rank → ℤ) → K) r else 0) := by
      refine E6Pilot.rootProd_congr fun y hy => ?_
      by_cases hyF : y ∈ F
      · exact hcoef.1 y hyF
      · rw [hcoef.2 y hy hyF]
        have hyR := (List.mem_append.1 hy).resolve_left hyF
        obtain ⟨e, he, hey⟩ := hRe y hyR
        have hs := hsum 1 e he
        rw [hey] at hs
        have h11 : (1 : (Fin Tag.E7.rank → ℤ) → K) e.2.1 + (1 : (Fin Tag.E7.rank → ℤ) → K) e.2.2 =
            0 := by
          simp only [Pi.one_apply]
          rw [← two_mul, h2, zero_mul]
        rw [hs, h11, add_zero]
    rw [hfix, hext] at hconj
    exact (mul_inv_eq_iff_eq_mul.1 hconj)
  · have hc' : ((e7WordImage m.word F).map fun β => pinnedX .E7 K β 1).prod *
        rootProd .E7 K (F ++ m.rhos) (fun r => if r ∈ F then c r else 0) =
        rootProd .E7 K (F ++ m.rhos) (fun r => if r ∈ F then c r else 0) *
          ((e7WordImage m.word F).map fun β => pinnedX .E7 K β 1).prod := by
      rw [hext]
      exact hc.eq
    have hz := sum_eq_zero_of_commute_conj hlnd hlp hlfam hCl hB hCB hRB'
      (fun r => if r ∈ F then c r else 0) hc' (List.mem_append_right _ (heqs e he).1)
      (hRp _ (heqs e he).1).2.2
    rw [hsum c e he] at hz
    linear_combination hz - c e.2.2 * h2

end MixMain

section Conn

variable {K : Type}

theorem e7ConnStep_foldl {c : (Fin Tag.E7.rank → ℤ) → K} {d : K} :
    ∀ (pairs : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ)))
      (acc : List (Fin Tag.E7.rank → ℤ)), (∀ p ∈ pairs, c p.1 = c p.2) →
        (∀ y ∈ acc, c y = d) → ∀ y ∈ pairs.foldl e7ConnStep acc, c y = d
  | [], acc, _, hacc => hacc
  | p :: ps, acc, hp, hacc => by
    refine e7ConnStep_foldl ps (e7ConnStep acc p) (fun q hq => hp q (List.mem_cons_of_mem _ hq))
      fun y hy => ?_
    have hp1 := hp p List.mem_cons_self
    simp only [e7ConnStep] at hy
    split_ifs at hy with h1 h2 h3
    · exact hacc y hy
    · rcases List.mem_cons.1 hy with rfl | hy
      · rw [← hp1]
        exact hacc _ (mem_of_oddDerivMemB h1)
      · exact hacc y hy
    · rcases List.mem_cons.1 hy with rfl | hy
      · rw [hp1]
        exact hacc _ (mem_of_oddDerivMemB h3)
      · exact hacc y hy
    · exact hacc y hy

theorem e7ConnB_sound {F : List (Fin Tag.E7.rank → ℤ)}
    {pairs : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ))} (h : e7ConnB F pairs = true)
    {c : (Fin Tag.E7.rank → ℤ) → K} (hp : ∀ p ∈ pairs, c p.1 = c p.2) :
    ∃ d : K, ∀ s ∈ F, c s = d := by
  cases F with
  | nil => simp [e7ConnB] at h
  | cons s₀ F =>
    refine ⟨c s₀, fun s hs => ?_⟩
    simp only [e7ConnB, List.all_eq_true] at h
    exact e7ConnStep_foldl pairs [s₀] hp (fun y hy => by rw [List.mem_singleton.1 hy]) s
      (mem_of_oddDerivMemB (h s hs))

end Conn

section Main

variable {K : Type} [Field K]

theorem iform_eq_zero_of_pairwise {F : List (Fin Tag.E7.rank → ℤ)}
    (hFo : F.Pairwise fun σ σ' => iform σ σ' = 0) {a b : Fin Tag.E7.rank → ℤ} (ha : a ∈ F)
    (hb : b ∈ F) (hab : a ≠ b) : iform a b = 0 := by
  induction F with
  | nil => simp at ha
  | cons x F ih =>
    rw [List.pairwise_cons] at hFo
    rcases List.mem_cons.1 ha with h1 | h1 <;> rcases List.mem_cons.1 hb with h2 | h2
    · exact absurd (h1.trans h2.symm) hab
    · rw [h1]
      exact hFo.1 b h2
    · rw [h2, iform_comm]
      exact hFo.1 a h1
    · exact ih hFo.2 h1 h2

theorem rootCommFamily_of_frame {F : List (Fin Tag.E7.rank → ℤ)} (hFr : ∀ σ ∈ F, IsRoot .E7 σ)
    (hFo : F.Pairwise fun σ σ' => iform σ σ' = 0) : RootCommFamily .E7 K F := by
  intro a ha b hb s t
  by_cases hab : a = b
  · subst hab
    show pinnedX .E7 K a s * pinnedX .E7 K a t = pinnedX .E7 K a t * pinnedX .E7 K a s
    rw [← pinnedX_add, ← pinnedX_add, add_comm]
  · have hi : iform a b = 0 := iform_eq_zero_of_pairwise hFo ha hb hab
    exact commute_pinnedX_of_iform_eq_zero_e7 (hFr a ha) (hFr b hb) hi s t

theorem sylowData_of_e7SylowCheck [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K)
    {F : List (Fin Tag.E7.rank → ℤ)} (hFp : ∀ σ ∈ F, IsRoot .E7 σ ∧ 0 < height σ)
    (hFnd : F.Nodup) (hFo : F.Pairwise fun σ σ' => iform σ σ' = 0) {cert : E7SylowCert}
    (hchk : e7SylowCheck F cert = true) :
    Exc.SylowData (e7FramePt K F) (e7FrameLine K F) := by
  classical
  intro w _ hconj hpow
  obtain ⟨k, hk⟩ := hpow
  have hFr : ∀ σ ∈ F, IsRoot .E7 σ := fun σ hσ => (hFp σ hσ).1
  have hFfam : RootCommFamily .E7 K F := rootCommFamily_of_frame hFr hFo
  simp only [e7SylowCheck] at hchk
  split at hchk
  · exact absurd hchk Bool.false_ne_true
  rename_i D hD
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h11⟩, htail⟩, hSD⟩, hann⟩, hLnd⟩, hkills⟩, hmix⟩, hconn⟩ := hchk
  replace hann := annListCheck_of_e7AnnB hann
  have hN : ∀ d ∈ D, ∀ c : K, e7FrameElt K [d] c ∈ conjCentGen (e7FramePt K F) :=
    e7NDeriv_sound hFr hFnd (fun ω hTF t ht c => e7FrameElt_single_mem_of_tuple h4 hFr hFnd hFo
      ω hTF (fun b hb => conj_mem_conjCentGen hb) ht c) cert.steps [] D hD (by simp)
  have hwD : ∀ d ∈ D, ∀ c : K, (w : ModGL .E7 K) * pinnedX .E7 K d c =
      pinnedX .E7 K d c * (w : ModGL .E7 K) := fun d hd c => by
    have h := congrArg Subtype.val (commute_of_mem_conjCentGen hconj (hN d hd c))
    simpa only [Subgroup.coe_mul, coe_e7FrameElt_singleton] using h
  have hB := mem_borelGroup_of_commute_of_tail h1 (simpleDiffTail_of_le h11) htail hwD
  have hk' : (w : ModGL .E7 K) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hU := mem_posUnipotent_of_mem_borelGroup_of_pow hB hk'
  have hLnd' := nodup_of_e7NodupB hLnd
  obtain ⟨hLfam, c, hc⟩ := exists_rootProd_of_annListCheck hann hLnd' hU fun δ hδ =>
    hwD δ (mem_of_oddDerivMemB (hSD δ hδ)) 1
  have hLp := (annListCheck_sound hann).2.1
  split at hkills
  · exact absurd hkills Bool.false_ne_true
  rename_i C hCk
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hkills
  obtain ⟨hlen, hFC⟩ := hkills
  obtain ⟨hCnd, hCsub, hwC⟩ := e7KillsB_sound (fun β hβ => hwD β hβ 1) c cert.kills cert.annL C
    hCk hLnd' hLp hLfam hc
  have hperm : F.Perm C := (List.subperm_of_subset hFnd fun s hs =>
    mem_of_oddDerivMemB (hFC s hs)).perm_of_length_le hlen
  have hwF : (w : ModGL .E7 K) = rootProd .E7 K F c := by
    rw [hwC, E6Pilot.rootProd_perm (hLfam.of_sublist hCsub) hperm.symm]
  have hpairs : ∀ p ∈ cert.pairs, c p.1 = c p.2 := by
    intro p hp
    simp only [E7SylowCert.pairs, List.mem_flatMap, List.mem_map] at hp
    obtain ⟨m, hm, e, he, rfl⟩ := hp
    have hsound := e7MixB_sound hFp hFnd hFfam (hmix m hm)
    set b := e7WeylRep K ((coxeterSystem .E7).wordProd m.word)
    have hbx : b * e7FramePt K F * b⁻¹ = e7FrameElt K (e7WordImage m.word F) 1 := by
      rw [← e7FrameElt_one]
      exact e7FrameElt_conj_word m.word hFr 1
    have hbC : b * e7FramePt K F * b⁻¹ ∈ Exc.cent (e7FramePt K F) := by
      rw [hbx, Exc.cent, mem_centralizer_singleton_iff]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, coe_e7FrameElt]
      exact hsound.1.eq
    have hwb := mem_centralizer_singleton_iff.1 (hconj b hbC)
    rw [hbx] at hwb
    have hwb' := congrArg Subtype.val hwb
    simp only [Subgroup.coe_mul, coe_e7FrameElt, hwF] at hwb'
    exact hsound.2 c (Commute.symm hwb') e he
  obtain ⟨d, hd⟩ := e7ConnB_sound hconn hpairs
  refine (mem_e7FrameLine hFr hFo).2 ⟨d, Subtype.ext ?_⟩
  rw [coe_e7FrameElt, hwF]
  exact congrArg List.prod (List.map_congr_left fun s hs => by rw [hd s hs])

end Main

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
