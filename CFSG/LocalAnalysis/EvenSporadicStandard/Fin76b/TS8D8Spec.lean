module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8D8Check
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.EvenSporadicStandard.Fin76b.TS8D8

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native Subgroup

structure TabOK (n : ℕ) (A B U : Array ℕ) (ws : List (List ℕ)) (E M : Array (Array ℕ))
    (I : Array ℕ) (gens : Array (Array ℕ)) (par gen : Array ℕ) : Prop where
  gens_eq : gens = gensT n A B U ws
  hA : isInvA n A (invCand n A) = true
  hB : isInvA n B (invCand n B) = true
  hU : isInvA n U (invCand n U) = true
  hid : eqA n E[0]! (idA n) = true
  hperm : ∀ a < 256, isInvA n E[a]! (invCand n E[a]!) = true
  hdist : ∀ a < 256, ∀ b < a, eqA n E[a]! E[b]! = false
  hgen : ∀ a < 256, a ≠ 0 → par[a]! < a ∧ gen[a]! < gens.size ∧
    eqA n (compA n E[par[a]!]! gens[gen[a]!]!) E[a]! = true
  hmul : ∀ a < 256, ∀ b < 256, (M[a]!)[b]! < 256 ∧
    eqA n (compA n E[a]! E[b]!) E[(M[a]!)[b]!]! = true
  hinv : ∀ a < 256, I[a]! < 256 ∧ eqA n (invCand n E[a]!) E[I[a]!]! = true
  hquad : ∀ a < 256, ∀ b < 256, ∀ c < 256, ∀ d < 256, quadIx M I a b c d = false

theorem searchD8_spec {M : Array (Array ℕ)} {I : Array ℕ} (h : searchD8 M I = true) {a b c d : ℕ}
    (ha : a < 256) (hb : b < 256) (hc : c < 256) (hd : d < 256) :
    quadIx M I a b c d = false := by
  by_contra hq
  have hq' : quadIx M I a b c d = true := by simpa using hq
  simp only [quadIx, Bool.and_eq_true, and_assoc] at hq'
  obtain ⟨o4a, iib, o4c, cac, cbc, neq, iid, cad, cbd⟩ := hq'
  simp only [searchD8, CFSG.Monster.B.Co2.allLt_iff, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h a ha with h1 | h1
  · simp [o4a] at h1
  rcases h1 b hb with h2 | h2
  · simp [iib] at h2
  rcases h2 c hc with h3 | h3
  · simp [o4c, cac, cbc, neq] at h3
  have h4 := h3 d hd
  simp [iid, cad, cbd] at h4

theorem checkD8_tabOK {n : ℕ} {A B U : Array ℕ} {ws : List (List ℕ)}
    (h : checkD8 n A B U ws = true) :
    TabOK n A B U ws (bfsT n (gensT n A B U ws)).1
      (mulTabT n (bfsT n (gensT n A B U ws)).1 (idxT (bfsT n (gensT n A B U ws)).1))
      (invTabT n (bfsT n (gensT n A B U ws)).1 (idxT (bfsT n (gensT n A B U ws)).1))
      (gensT n A B U ws) (bfsT n (gensT n A B U ws)).2.1 (bfsT n (gensT n A B U ws)).2.2 := by
  unfold checkD8 at h
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨hA, hB, hU, -, hid, hperm, hdist, hgen, hmul, hinv, hquad⟩ := h
  simp only [idOKT, permOKT, distinctOKT, genOKT, mulOKT, invOKT, CFSG.Monster.B.Co2.allLt_iff,
    Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    Bool.not_eq_true] at hid hperm hdist hgen hmul hinv
  exact {
    gens_eq := rfl
    hA := hA
    hB := hB
    hU := hU
    hid := hid
    hperm := hperm
    hdist := fun a ha b hb => hdist a ha b hb
    hgen := fun a ha ha0 => by
      obtain ⟨⟨p, g⟩, e⟩ := (hgen a ha).resolve_left ha0
      exact ⟨p, g, e⟩
    hmul := fun a ha b hb => hmul a ha b hb
    hinv := fun a ha => hinv a ha
    hquad := fun a ha b hb c hc d hd => searchD8_spec hquad ha hb hc hd }

section Generic

variable {n : ℕ} {A B U : Array ℕ} {ws : List (List ℕ)} {E M : Array (Array ℕ)} {I : Array ℕ}
  {gens : Array (Array ℕ)} {par gen : Array ℕ}

@[expose] noncomputable def EpT (n : ℕ) (E : Array (Array ℕ)) (a : ℕ) : Equiv.Perm (Fin n) :=
  permOfArr n E[a]!

theorem rep_EpT (h : TabOK n A B U ws E M I gens par gen) {a : ℕ} (ha : a < 256) :
    Rep n E[a]! (EpT n E a) :=
  (rep_permOfArr (h.hperm a ha)).1

theorem EpT_zero (h : TabOK n A B U ws E M I gens par gen) : EpT n E 0 = 1 :=
  (eqA_iff (rep_EpT h (by norm_num)) rep_idA).1 h.hid

theorem EpT_mul (h : TabOK n A B U ws E M I gens par gen) {a b : ℕ} (ha : a < 256) (hb : b < 256) :
    EpT n E (mulIx M a b) = EpT n E a * EpT n E b := by
  have hm := h.hmul a ha b hb
  exact ((eqA_iff (rep_compA (rep_EpT h ha) (rep_EpT h hb)) (rep_EpT h hm.1)).1 hm.2).symm

theorem EpT_inv (h : TabOK n A B U ws E M I gens par gen) {a : ℕ} (ha : a < 256) :
    EpT n E (invIx I a) = (EpT n E a)⁻¹ := by
  have hi := h.hinv a ha
  have hr := rep_inv_of_isInvA (rep_EpT h ha) (h.hperm a ha)
  exact ((eqA_iff hr (rep_EpT h hi.1)).1 hi.2).symm

theorem EpT_inj (h : TabOK n A B U ws E M I gens par gen) {a b : ℕ} (ha : a < 256) (hb : b < 256)
    (hab : EpT n E a = EpT n E b) : a = b := by
  rcases lt_trichotomy a b with hlt | heq | hgt
  · have h1 : eqA n E[b]! E[a]! = true := (eqA_iff (rep_EpT h hb) (rep_EpT h ha)).2 hab.symm
    have h2 := h.hdist b hb a hlt
    rw [h1] at h2
    exact absurd h2 (by decide)
  · exact heq
  · have h1 : eqA n E[a]! E[b]! = true := (eqA_iff (rep_EpT h ha) (rep_EpT h hb)).2 hab
    have h2 := h.hdist a ha b hgt
    rw [h1] at h2
    exact absurd h2 (by decide)

theorem mulIx_lt (h : TabOK n A B U ws E M I gens par gen) {a b : ℕ} (ha : a < 256)
    (hb : b < 256) : mulIx M a b < 256 :=
  (h.hmul a ha b hb).1

theorem invIx_lt (h : TabOK n A B U ws E M I gens par gen) {a : ℕ} (ha : a < 256) :
    invIx I a < 256 :=
  (h.hinv a ha).1

@[expose] noncomputable def letPermT (n : ℕ) (A B U : Array ℕ) (l : ℕ) : Equiv.Perm (Fin n) :=
  if l = 0 then permOfArr n A else if l = 1 then permOfArr n B
    else if l = 2 then (permOfArr n A)⁻¹ else if l = 3 then (permOfArr n B)⁻¹ else permOfArr n U

theorem rep_letT (hA : isInvA n A (invCand n A) = true) (hB : isInvA n B (invCand n B) = true)
    (hU : isInvA n U (invCand n U) = true) (l : ℕ) :
    Rep n (letT n A B U l) (letPermT n A B U l) := by
  unfold letT letPermT
  split_ifs
  · exact (rep_permOfArr hA).1
  · exact (rep_permOfArr hB).1
  · exact (rep_permOfArr hA).2
  · exact (rep_permOfArr hB).2
  · exact (rep_permOfArr hU).1

theorem letPermT_mem {R : Subgroup (Equiv.Perm (Fin n))} (hRA : permOfArr n A ∈ R)
    (hRB : permOfArr n B ∈ R) (hRU : permOfArr n U ∈ R) (l : ℕ) : letPermT n A B U l ∈ R := by
  unfold letPermT
  split_ifs
  · exact hRA
  · exact hRB
  · exact R.inv_mem hRA
  · exact R.inv_mem hRB
  · exact hRU

theorem rep_wordT (hA : isInvA n A (invCand n A) = true) (hB : isInvA n B (invCand n B) = true)
    (hU : isInvA n U (invCand n U) = true) (w : List ℕ) :
    Rep n (wordT n A B U w) (w.map (letPermT n A B U)).prod := by
  have key : ∀ (w : List ℕ) (acc : Array ℕ) (g : Equiv.Perm (Fin n)), Rep n acc g →
      Rep n (w.foldl (fun acc l => compA n acc (letT n A B U l)) acc)
        (g * (w.map (letPermT n A B U)).prod) := by
    intro w
    induction w with
    | nil => intro acc g hg; simpa using hg
    | cons l w ih =>
      intro acc g hg
      simp only [List.foldl_cons, List.map_cons, List.prod_cons]
      have := ih (compA n acc (letT n A B U l)) (g * letPermT n A B U l)
        (rep_compA hg (rep_letT hA hB hU l))
      simpa [mul_assoc] using this
  have hw := key w (idA n) 1 rep_idA
  simpa [wordT] using hw

theorem wordPermT_mem {R : Subgroup (Equiv.Perm (Fin n))} (hRA : permOfArr n A ∈ R)
    (hRB : permOfArr n B ∈ R) (hRU : permOfArr n U ∈ R) (w : List ℕ) :
    (w.map (letPermT n A B U)).prod ∈ R := by
  refine Subgroup.list_prod_mem R fun x hx => ?_
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
  exact letPermT_mem hRA hRB hRU l

theorem gensT_getElem! (n : ℕ) (A B U : Array ℕ) (ws : List (List ℕ)) {k : ℕ} (hk : k < ws.length) :
    (gensT n A B U ws)[k]! = wordT n A B U ws[k] := by
  simp [gensT, getElem!_pos, hk]

theorem gens_rep (h : TabOK n A B U ws E M I gens par gen) {R : Subgroup (Equiv.Perm (Fin n))}
    (hRA : permOfArr n A ∈ R) (hRB : permOfArr n B ∈ R) (hRU : permOfArr n U ∈ R) {k : ℕ}
    (hk : k < gens.size) : ∃ g ∈ R, Rep n gens[k]! g := by
  have hk' : k < ws.length := by
    have hk2 := hk
    rw [h.gens_eq] at hk2
    simpa [gensT] using hk2
  rw [h.gens_eq, gensT_getElem! n A B U ws hk']
  exact ⟨_, wordPermT_mem hRA hRB hRU _, rep_wordT h.hA h.hB h.hU _⟩

theorem EpT_mem (h : TabOK n A B U ws E M I gens par gen) {R : Subgroup (Equiv.Perm (Fin n))}
    (hRA : permOfArr n A ∈ R) (hRB : permOfArr n B ∈ R) (hRU : permOfArr n U ∈ R) :
    ∀ a : ℕ, a < 256 → EpT n E a ∈ R := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro ha
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0
      rw [EpT_zero h]
      exact R.one_mem
    · obtain ⟨hlt, hgi, hg⟩ := h.hgen a ha (by omega)
      obtain ⟨g, hgR, hrep⟩ := gens_rep h hRA hRB hRU hgi
      have hp : par[a]! < 256 := by omega
      have key := (eqA_iff (rep_compA (rep_EpT h hp) hrep) (rep_EpT h ha)).1 hg
      rw [← key]
      exact R.mul_mem (ih _ hlt hp) hgR

@[expose] noncomputable def sigmaT (h : TabOK n A B U ws E M I gens par gen) :
    Subgroup (Equiv.Perm (Fin n)) where
  carrier := {g | ∃ a, a < 256 ∧ EpT n E a = g}
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨mulIx M a b, mulIx_lt h ha hb, EpT_mul h ha hb⟩
  one_mem' := ⟨0, by norm_num, EpT_zero h⟩
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨invIx I a, invIx_lt h ha, EpT_inv h ha⟩

theorem card_sigmaT (h : TabOK n A B U ws E M I gens par gen) : Nat.card (sigmaT h) = 256 := by
  have hbij : Function.Bijective (fun a : Fin 256 =>
      (⟨EpT n E a, (a : ℕ), a.2, rfl⟩ : (sigmaT h : Subgroup (Equiv.Perm (Fin n))))) := by
    constructor
    · intro a b hab
      exact Fin.ext (EpT_inj h a.2 b.2 (congrArg Subtype.val hab))
    · intro x
      obtain ⟨a, ha, hg⟩ := x.2
      exact ⟨⟨a, ha⟩, Subtype.ext hg⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_fin]

theorem sigmaT_le (h : TabOK n A B U ws E M I gens par gen) {R : Subgroup (Equiv.Perm (Fin n))}
    (hRA : permOfArr n A ∈ R) (hRB : permOfArr n B ∈ R) (hRU : permOfArr n U ∈ R) :
    (sigmaT h : Subgroup (Equiv.Perm (Fin n))) ≤ R := by
  rintro _ ⟨a, ha, rfl⟩
  exact EpT_mem h hRA hRB hRU a ha

end Generic

end CFSG.EvenSporadicStandard.Fin76b.TS8D8
