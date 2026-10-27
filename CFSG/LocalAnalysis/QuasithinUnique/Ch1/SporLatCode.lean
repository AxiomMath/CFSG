module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatPt
public import Certificates.Data.CFSGNative.SporLat.Code

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat

open CFSG.QuasithinUnique.K1.SporadicPerm

theorem encodeSet_cons (n p : ℕ) (l : List ℕ) :
    encodeSet n (p :: l) = (p + 1) + (n + 1) * encodeSet n l := by
  simp [encodeSet]

theorem encodeSet_ge (n : ℕ) (l : List ℕ) : l.length ≤ encodeSet n l := by
  induction l with
  | nil => simp [encodeSet]
  | cons p l ih =>
    rw [encodeSet_cons]
    simp only [List.length_cons]
    have : encodeSet n l ≤ (n + 1) * encodeSet n l := Nat.le_mul_of_pos_left _ (by omega)
    omega

theorem decodeSet_encodeSet (n : ℕ) (l : List ℕ) (hl : ∀ p ∈ l, p < n) :
    ∀ fuel, l.length ≤ fuel → decodeSet n fuel (encodeSet n l) = l := by
  induction l with
  | nil =>
    intro fuel _
    cases fuel <;> simp [decodeSet, encodeSet]
  | cons p l ih =>
    intro fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hp : p < n := hl p List.mem_cons_self
    have hmod : (p + 1 + (n + 1) * encodeSet n l) % (n + 1) = p + 1 := by
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by omega)
    have hdiv : (p + 1 + (n + 1) * encodeSet n l) / (n + 1) = encodeSet n l := by
      rw [Nat.add_mul_div_left _ _ (by omega : 0 < n + 1), Nat.div_eq_of_lt (by omega)]
      simp
    rw [encodeSet_cons, decodeSet]
    have hne : ¬ (p + 1 + (n + 1) * encodeSet n l = 0) := by omega
    simp only [hne, ↓reduceIte, hmod, hdiv]
    simp only [List.cons.injEq]
    exact ⟨by omega, ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) f
      (by simpa using hf)⟩

@[expose] def ValidCode (n c : ℕ) : Prop := ∃ l, PtValid n l ∧ encodeSet n l = c

theorem codeAct_encodeSet (n : ℕ) (t : Array ℕ) (l : List ℕ) (hl : ∀ p ∈ l, p < n) :
    codeAct n t (encodeSet n l) = encodeSet n (ptAct t l) := by
  unfold codeAct ptAct
  rw [decodeSet_encodeSet n l hl _ (encodeSet_ge n l)]

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

@[expose] def codeLab (n : ℕ) : LabAct ℕ := ⟨codeAct n⟩

theorem codeLab_lawful : LabLawful Γ n (codeLab n) (ValidCode n) where
  valid_act g c hc := by
    obtain ⟨l, hl, rfl⟩ := hc
    refine ⟨ptAct (tab n g).toArray l, ptLab_lawful.valid_act g hl, ?_⟩
    exact (codeAct_encodeSet n _ l hl.2).symm
  act_mul g h c hc := by
    obtain ⟨l, hl, rfl⟩ := hc
    show codeAct n (tab n (g * h)).toArray (encodeSet n l) =
      codeAct n (tab n g).toArray (codeAct n (tab n h).toArray (encodeSet n l))
    have hv : ∀ p ∈ ptAct (tab n h).toArray l, p < n := (ptLab_lawful.valid_act h hl).2
    rw [codeAct_encodeSet n _ l hl.2, codeAct_encodeSet n _ l hl.2,
      codeAct_encodeSet n _ _ hv]
    exact congrArg (encodeSet n) (ptLab_lawful.act_mul g h hl)
  act_one {c} hc := by
    obtain ⟨l, hl, rfl⟩ := hc
    show codeAct n (tab n (1 : Γ)).toArray (encodeSet n l) = encodeSet n l
    rw [codeAct_encodeSet n _ l hl.2]
    exact congrArg (encodeSet n) (ptLab_lawful.act_one hl)

@[expose] def codeSetLab (n : ℕ) : LabAct (List ℕ) := ⟨codeSetAct n⟩

@[expose] def CodeSetValid (n : ℕ) (L : List ℕ) : Prop :=
  L.Pairwise (· ≤ ·) ∧ ∀ c ∈ L, ValidCode n c

theorem codeSetLab_lawful : LabLawful Γ n (codeSetLab n) (CodeSetValid n) where
  valid_act g L hL := by
    refine ⟨sortN_sorted _, fun c hc => ?_⟩
    have hc' : c ∈ codeSetAct n (tab n g).toArray L := hc
    unfold codeSetAct at hc'
    rw [mem_sortN] at hc'
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hc'
    exact codeLab_lawful.valid_act g (hL.2 y hy)
  act_mul g h L hL := by
    show codeSetAct n (tab n (g * h)).toArray L =
      codeSetAct n (tab n g).toArray (codeSetAct n (tab n h).toArray L)
    unfold codeSetAct
    rw [sortN_map_sortN, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact codeLab_lawful.act_mul g h (hL.2 c hc)
  act_one {L} hL := by
    show codeSetAct n (tab n (1 : Γ)).toArray L = L
    unfold codeSetAct
    have : (L.map (codeAct n (tab n (1 : Γ)).toArray)) = L :=
      (List.map_congr_left (g := fun c => c) fun c hc => codeLab_lawful.act_one (hL.2 c hc)).trans
        (List.map_id' L)
    rw [this]
    exact sortN_of_pairwise hL.1

end CFSG.QuasithinUnique.Ch1.SporLat
