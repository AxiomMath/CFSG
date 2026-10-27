module

public import CFSG.CGT.PushingUpLit.SYMB.FiveConj
public import CFSG.CGT.PushingUpLit.SYMB.FiveInj
public import CFSG.CGT.PushingUpLit.SYMB.FiveTable

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7 Equiv
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T V : Subgroup Γ}
  {φ : ↥G →* Equiv.Perm (Fin 5)} {ψ : ↥V →* ↥(G6.coreMod 5)} {T' : Set (Equiv.Perm (Fin 5))}
  {S : SymSetting G T V 5 φ ψ T'} {V₁ : Subgroup Γ}

structure Pts (G T : Subgroup Γ) (φ : ↥G →* Equiv.Perm (Fin 5)) (a b c d : Fin 5) : Prop where
  hab : a ≠ b
  hcd : c ≠ d
  hac : a ≠ c
  had : a ≠ d
  hbc : b ≠ c
  hbd : b ≠ d
  hY : imgG G φ (baum T) = Subgroup.zpowers (swap a b) ⊔ Subgroup.zpowers (swap c d)

omit [Finite Γ] in
theorem Pts.symm {a b c d : Fin 5} (h : Pts G T φ a b c d) : Pts G T φ c d a b where
  hab := h.hcd
  hcd := h.hab
  hac := h.hac.symm
  had := h.hbc.symm
  hbc := h.had.symm
  hbd := h.hbd.symm
  hY := by rw [h.hY, sup_comm]

@[expose] def Good (a b c d : Fin 5) (P : Subgroup (Equiv.Perm (Fin 5))) : Prop :=
  P = ⊥ ∨ P = Subgroup.zpowers (swap a b) ∨ P = Subgroup.zpowers (swap c d) ∨
    P = Subgroup.zpowers (swap a b) ⊔ Subgroup.zpowers (swap c d)

omit [Finite Γ] in
theorem Pts.table {a b c d : Fin 5} (h : Pts G T φ a b c d) {P : Subgroup (Equiv.Perm (Fin 5))}
    (hP : Good a b c d P) :
    Nat.card ↥P * Nat.card ↥(Delta5Swaps.Fixed P) = 16 :=
  table_good h.hab h.hcd h.hac h.had h.hbc h.hbd hP

theorem member_good (hV : V1Iso S V₁) {a b c d : Fin 5} (h : Pts G T φ a b c d) {A : Subgroup Γ}
    (hA : IsMaxElemAbelian T A) : Good a b c d (imgG G φ A) := by
  have hAB : A ≤ baum T := (B6.le_thompsonJ hA).trans (B6.thompsonJ_le_baum T)
  have hle : imgG G φ A ≤ Subgroup.zpowers (swap a b) ⊔ Subgroup.zpowers (swap c d) := by
    rw [← h.hY]
    exact imgG_mono G φ hAB
  rcases classify h.hac h.had h.hbc h.hbd hle with hg | hp
  · exact hg
  · exfalso
    have h16 := sixteen_le S hV hA
    rw [hV.card_Cfix, hp] at h16
    rw [table_prod h.hab h.hcd h.hac h.had h.hbc h.hbd] at h16
    omega

theorem Up_mem_Wset (hV : V1Iso S V₁) {a b c d : Fin 5} (h : Pts G T φ a b c d)
    {A : Subgroup Γ} {P₀ P : Subgroup (Equiv.Perm (Fin 5))} (hA : A ∈ Wset G T φ P₀)
    (hP₀ : Good a b c d P₀) (hP : Good a b c d P) (hle : P ≤ P₀) :
    Up φ ψ V₁ A P ∈ Wset G T φ P := by
  have hPA : P ≤ imgG G φ A := by rw [hA.2]; exact hle
  refine ⟨Up_isMax hV hA.1 hPA (h.table hP) (by rw [hA.2]; exact h.table hP₀), imgG_Up hV hPA⟩

section Swaps

variable {a b c d : Fin 5}

theorem swap_ab_not_mem_cd (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) :
    swap a b ∉ Subgroup.zpowers (swap c d) := by
  intro h
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 h
  rcases zpow_of_mul_self (swap_mul_self c d) j with h' | h'
  · rw [h'] at hj
    exact swap_ne_one hab hj.symm
  · rw [h'] at hj
    exact swap_ne_swap hab hac had hj.symm

theorem prod_not_mem_ab (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) :
    swap a b * swap c d ∉ Subgroup.zpowers (swap a b) := by
  intro h
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 h
  rcases zpow_of_mul_self (swap_mul_self a b) j with h' | h'
  · rw [h'] at hj
    exact swap_mul_swap_ne_one hab hac had hj.symm
  · rw [h'] at hj
    exact swap_ne_one hcd (mul_left_cancel (a := swap a b) (by rw [mul_one]; exact hj.symm))

theorem prod_not_mem_cd (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) :
    swap a b * swap c d ∉ Subgroup.zpowers (swap c d) := by
  intro h
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 h
  rcases zpow_of_mul_self (swap_mul_self c d) j with h' | h'
  · rw [h'] at hj
    exact swap_mul_swap_ne_one hab hac had hj.symm
  · rw [h'] at hj
    exact swap_ne_one hab (mul_right_cancel (b := swap c d) (by rw [one_mul]; exact hj.symm))

end Swaps

@[expose] def memSet (T : Subgroup Γ) (x : Γ) : Set (Subgroup Γ) :=
  {A | IsMaxElemAbelian T A ∧ x ∈ A}

@[expose] def Wx (G T : Subgroup Γ) (φ : ↥G →* Equiv.Perm (Fin 5))
    (P : Subgroup (Equiv.Perm (Fin 5))) (x : Γ) : Set (Subgroup Γ) :=
  {A | A ∈ Wset G T φ P ∧ x ∈ A}

theorem mem_of_Cfix (hV : V1Iso S V₁) {A : Subgroup Γ} {P Q : Subgroup (Equiv.Perm (Fin 5))}
    (hA : A ∈ Wset G T φ P) (hPQ : P ≤ Q) {v : Γ} (hv : v ∈ Cfix ψ V₁ Q) : v ∈ A := by
  have h1 : v ∈ V₁ ⊓ A := by
    rw [V₁_inf_eq S hV hA.1, hA.2]
    exact Cfix_anti hPQ hv
  exact h1.2

theorem ncard_le_memSet (hV : V1Iso S V₁) {Q : Subgroup (Equiv.Perm (Fin 5))} (hQ : Q ≠ ⊥)
    {v : Γ} (hv : v ∈ Cfix ψ V₁ Q) :
    (Wset G T φ ⊥).ncard + (Wset G T φ Q).ncard ≤ (memSet T v).ncard := by
  have hdisj : Disjoint (Wset G T φ ⊥) (Wset G T φ Q) := by
    rw [Set.disjoint_left]
    intro A hA hA'
    exact hQ (hA'.2.symm.trans hA.2)
  rw [← Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
  refine Set.ncard_le_ncard (fun A hA => ?_) (Set.toFinite _)
  rcases hA with hA | hA
  · exact ⟨hA.1, mem_of_Cfix hV hA bot_le hv⟩
  · exact ⟨hA.1, mem_of_Cfix hV hA (le_of_eq rfl) hv⟩

theorem ncard_Wx_le (hV : V1Iso S V₁) {a b c d : Fin 5} (h : Pts G T φ a b c d)
    {P₀ P : Subgroup (Equiv.Perm (Fin 5))} (hP₀ : Good a b c d P₀) (hP : Good a b c d P)
    (hle : P ≤ P₀) {x : Γ} (hxG : x ∈ G)
    (hPc : ∀ p ∈ P, p * φ ⟨x, hxG⟩ = φ ⟨x, hxG⟩ * p)
    (hP₀le : P₀ ≤ P ⊔ Subgroup.zpowers (φ ⟨x, hxG⟩)) :
    (Wx G T φ P₀ x).ncard ≤ (Wset G T φ P).ncard :=
  Set.ncard_le_ncard_of_injOn (Up φ ψ V₁ · P) (fun A hA => Up_mem_Wset hV h hA.1 hP₀ hP hle)
    (fun A₁ hA₁ A₂ hA₂ he => eq_of_Up_eq hV hA₁.1.1 hA₂.1.1 hA₁.2 hA₂.2 hxG hPc
      (by rw [hA₁.1.2]; exact hP₀le) (by rw [hA₂.1.2]; exact hP₀le) he)
    (Set.toFinite _)

end CFSG.CGT.PushingUpLit.SYMB
