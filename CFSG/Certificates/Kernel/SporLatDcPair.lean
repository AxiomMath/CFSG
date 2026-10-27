module

public import Certificates.Data.Kernel.SporLatDcCode
public import CFSG.Certificates.Kernel.SporLatDcSound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCode
public import CFSG.Quasithin.EmptyFaithful.S151S9TData
public import Mathlib.Algebra.Group.Action.TransferInstance
public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.Logic.Equiv.Fin.Basic

public section

namespace CFSG.KC.SLDc

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.E64F

@[reducible] def pairAction (Γ : Type) [Group Γ] (n : ℕ) [MulAction Γ (Fin n)] :
    MulAction Γ (Fin (n * n)) :=
  (finProdFinEquiv (m := n) (n := n)).symm.mulAction Γ

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem act_pair (g : Γ) {p : ℕ} (hp : p < n * n) :
    @act Γ _ (n * n) (pairAction Γ n) g p = act n g (p % n) + n * act n g (p / n) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hp)
  have h1 : p % n < n := Nat.mod_lt _ hn
  have h2 : p / n < n := Nat.div_lt_of_lt_mul hp
  have e0 : @act Γ _ (n * n) (pairAction Γ n) g p =
      (@HSMul.hSMul Γ (Fin (n * n)) (Fin (n * n)) (@instHSMul Γ (Fin (n * n))
        (pairAction Γ n).toSMul) g ⟨p, hp⟩).val :=
    @act_eq Γ _ (n * n) (pairAction Γ n) g ⟨p, hp⟩
  have e1 : act n g (p % n) = (g • (⟨p % n, h1⟩ : Fin n)).val := act_eq g ⟨p % n, h1⟩
  have e2 : act n g (p / n) = (g • (⟨p / n, h2⟩ : Fin n)).val := act_eq g ⟨p / n, h2⟩
  rw [e0, e1, e2]
  rfl

theorem good_pair {g : Γ} {f : ℕ → ℕ} (h : Good n (tab n g).toArray f) :
    Good (n * n) (@tab Γ _ (n * n) (pairAction Γ n) g).toArray (pairF n f) := by
  refine ⟨by simp [tab], fun p hp => ?_⟩
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hp)
  have h1 : p % n < n := Nat.mod_lt _ hn
  have h2 : p / n < n := Nat.div_lt_of_lt_mul hp
  have hv : (@tab Γ _ (n * n) (pairAction Γ n) g).toArray.getD p 0 =
      @act Γ _ (n * n) (pairAction Γ n) g p := @img_tab Γ _ (n * n) (pairAction Γ n) g p
  have ha := h.2 _ h1
  have hb := h.2 _ h2
  have ea : act n g (p % n) = f (p % n) := by rw [← img_tab]; exact ha.1
  have eb : act n g (p / n) = f (p / n) := by rw [← img_tab]; exact hb.1
  have hf : pairF n f p = f (p % n) + n * f (p / n) := rfl
  refine ⟨by rw [hv, act_pair g hp, ea, eb, hf], ?_⟩
  rw [hf]
  have hx := ha.2
  have hy := hb.2
  calc f (p % n) + n * f (p / n) < n + n * f (p / n) := by omega
    _ = n * (f (p / n) + 1) := by ring
    _ ≤ n * n := Nat.mul_le_mul_left _ hy

theorem sep_pair (hB : ∀ g : Γ, (∀ b ∈ List.range n, act n g b = b) → g = 1) (g : Γ)
    (hg : ∀ p ∈ (List.range n).map (fun i => i + n * i),
      @act Γ _ (n * n) (pairAction Γ n) g p = p) : g = 1 := by
  refine hB g fun b hb => ?_
  have hbn := List.mem_range.1 hb
  have hp : b + n * b < n * n := by
    calc b + n * b < n + n * b := by omega
      _ = n * (b + 1) := by ring
      _ ≤ n * n := Nat.mul_le_mul_left _ hbn
  have e := hg (b + n * b) (List.mem_map.2 ⟨b, hb, rfl⟩)
  have hm : (b + n * b) % n = b := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hbn]
  have hd : (b + n * b) / n = b := by
    rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hbn, Nat.zero_add]
  rw [act_pair g hp, hm, hd] at e
  have e' : (n + 1) * act n g b = (n + 1) * b := by linarith
  exact Nat.eq_of_mul_eq_mul_left (by omega) e'

theorem stab_of_complete {Lab : Type} {A : LabAct Lab} {valid : Lab → Prop}
    (hlaw : LabLawful Γ n A valid) {Δ : Lab} (hΔ : valid Δ) (a b : Γ) (sg : List Γ)
    (mw : List (List (List ℕ)))
    (hcomp : ∀ Z : Subgroup Γ, Subgroup.closure {x | x ∈ sg} ≤ Z → ∃ j ≤ mw.length,
      Z = memberOrTop mw.length
        (fun j => Subgroup.closure {x | x ∈ sg ++ (mw.getD j []).map (wordElt a b)}) j)
    (hfix : ∀ s ∈ sg, lab n A Δ s = Δ) (h0 : mw.getD 0 [] = [])
    (hmove : ∀ j, 0 < j → j < mw.length → ∃ w ∈ mw.getD j [], lab n A Δ (wordElt a b w) ≠ Δ)
    (htop : lab n A Δ a ≠ Δ ∨ lab n A Δ b ≠ Δ) :
    ∀ g : Γ, lab n A Δ g = Δ ↔ g ∈ Subgroup.closure {x | x ∈ sg} := by
  have hS : Subgroup.closure {x | x ∈ sg} ≤ stab hlaw hΔ :=
    (Subgroup.closure_le _).2 fun s hs => (mem_stab hlaw hΔ).2 (hfix s hs)
  obtain ⟨j, -, hZ⟩ := hcomp _ hS
  intro g
  refine ⟨fun hg => ?_, fun hg => (mem_stab hlaw hΔ).1 (hS hg)⟩
  have hgZ : g ∈ stab hlaw hΔ := (mem_stab hlaw hΔ).2 hg
  rcases Nat.lt_or_ge j mw.length with hjl | hjl
  · rcases Nat.eq_zero_or_pos j with rfl | hjp
    · rw [hZ, memberOrTop, if_pos hjl, h0, List.map_nil, List.append_nil] at hgZ
      exact hgZ
    · exfalso
      obtain ⟨w, hw, hne⟩ := hmove j hjp hjl
      have hm : wordElt a b w ∈ stab hlaw hΔ := by
        rw [hZ, memberOrTop, if_pos hjl]
        exact Subgroup.subset_closure (List.mem_append_right _ (List.mem_map_of_mem hw))
      exact hne ((mem_stab hlaw hΔ).1 hm)
  · exfalso
    have hm : ∀ x : Γ, x ∈ stab hlaw hΔ := by
      intro x
      rw [hZ, memberOrTop, if_neg (by omega)]
      exact Subgroup.mem_top x
    rcases htop with h | h
    · exact h ((mem_stab hlaw hΔ).1 (hm a))
    · exact h ((mem_stab hlaw hΔ).1 (hm b))

theorem wordTabA_eq_L : wordTabA = wordTabL := by
  funext tabs m w
  apply Array.toList_inj.1
  simp [wordTabA, wordTabL, Array.toList_range]

theorem idTab_eq (m : ℕ) : CFSG.Quasithin.S151S9T.idTab m = (List.range m).toArray := by
  apply Array.toList_inj.1
  simp [CFSG.Quasithin.S151S9T.idTab, Array.toList_range]

theorem codeSetAct_eq (m : ℕ) : codeSetAct m = codeSetT m := by
  funext t x
  have e : codeAct m t = codeAT m t := by
    funext c
    simp only [codeAct, codeAT, sortN_eq]
  simp only [codeSetAct, codeSetT, sortN_eq, e]

theorem omCode_sound {m : ℕ} {ts : Array (Array ℕ)} {x0 : List ℕ} {O : OmegaData (List ℕ)}
    (h : omCodeOK m ts x0 O = true) : OmegaSpec (codeSetAct m) ts x0 O :=
  (omOKG_sound (act := codeSetAct m) (letters := ts) (fun _ => True) trivial
    (fun l _ x _ => ⟨trivial, by rw [codeSetAct_eq, Array.getElem!_eq_getD]; rfl⟩) h).1

end CFSG.KC.SLDc

end
