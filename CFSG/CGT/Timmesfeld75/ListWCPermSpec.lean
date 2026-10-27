module

public import CFSG.CGT.Timmesfeld75.ListWCPermCheck
public import CFSG.Sporadic.Th.TableSpec
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.CGT.Timmesfeld75.WCCheck

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

section Semantics

variable {n : ℕ} {M : Subgroup (Equiv.Perm (Fin n))}

theorem eq_of_rep {T : Table} {g h : M} (hg : Rep n T g) (hh : Rep n T h) : g = h := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  apply Fin.ext
  have h1 := hg i.val i.isLt
  have h2 := hh i.val i.isLt
  rw [idx_of_lt _ i.isLt] at h1 h2
  exact h1.symm.trans h2

theorem eq_of_beq {A B : Table} {g h : M} (hg : Rep n A g) (hh : Rep n B h)
    (hAB : (A == B) = true) : g = h := by
  rw [beq_iff_eq] at hAB
  subst hAB
  exact eq_of_rep hg hh

theorem beq_of_eq {A B : Table} {g : M} (hA : Rep n A g) (hB : Rep n B g) (hsA : A.size = n)
    (hsB : B.size = n) : (A == B) = true := by
  rw [beq_iff_eq]
  refine Array.ext (hsA.trans hsB.symm) fun i hi₁ hi₂ => ?_
  have hin : i < n := hsA ▸ hi₁
  have h1 := hA i hin
  have h2 := hB i hin
  unfold ap at h1 h2
  rw [getElem!_pos A i hi₁] at h1
  rw [getElem!_pos B i hi₂] at h2
  exact UInt32.toNat_inj.1 (h1.trans h2.symm)

theorem size_compT' (P Q : Table) : (compT n P Q).size = n := Array.size_ofFn

theorem size_idT' : (idT n).size = n := Array.size_ofFn

end Semantics

section Words

variable (D : Data) {M : Subgroup (Equiv.Perm (Fin D.n))} (genG : ℤ → M)

noncomputable abbrev wG (w : List ℤ) : M := wordG genG w

variable {D genG}

theorem rep_wT (hn : D.n < 2 ^ 32) (hgen : ∀ l, Rep D.n (D.gens l) (genG l)) (w : List ℤ) :
    Rep D.n (wT D w) (wG D genG w) :=
  Rep.wordT hn w fun l _ => hgen l

theorem size_wT (w : List ℤ) : (wT D w).size = D.n := wordT_size _ _ _

theorem wG_invWord (hinv : ∀ l, genG (-l) = (genG l)⁻¹) (w : List ℤ) :
    wG D genG (invWord w) = (wG D genG w)⁻¹ := by
  simp only [wG, wordG, invWord, List.map_reverse, List.map_map]
  rw [List.prod_inv_reverse, List.map_map]
  congr 2
  exact List.map_congr_left fun l _ => by simp [hinv]

end Words

section Enumeration

variable {n : ℕ} {M : Subgroup (Equiv.Perm (Fin n))}

noncomputable def eltG : List M → ℕ → M
  | [], _ => 1
  | s :: ss, m => (if m % 2 = 1 then s else 1) * eltG ss (m / 2)

theorem rep_eltT (hn : n < 2 ^ 32) :
    ∀ {Ts : List Table} {Gs : List M}, List.Forall₂ (Rep n) Ts Gs → ∀ m : ℕ,
      Rep n (eltT n Ts m) (eltG Gs m)
  | [], [], .nil, m => by
    simp only [eltT, eltG]
    exact Rep.idT hn
  | T :: Ts, G :: Gs, .cons hT hTs, m => by
    simp only [eltT, eltG]
    refine Rep.compT ?_ (rep_eltT hn hTs (m / 2))
    split_ifs
    · exact hT
    · exact Rep.idT hn

theorem size_eltT (Ts : List Table) (m : ℕ) : (eltT n Ts m).size = n := by
  cases Ts with
  | nil => exact size_idT'
  | cons T Ts => exact size_compT' _ _

theorem eltG_mem_closure :
    ∀ (Gs : List M) (m : ℕ), eltG Gs m ∈ Subgroup.closure {g | g ∈ Gs}
  | [], _ => Subgroup.one_mem _
  | s :: ss, m => by
    simp only [eltG]
    refine Subgroup.mul_mem _ ?_ ?_
    · split_ifs
      · exact Subgroup.subset_closure (List.mem_cons_self ..)
      · exact Subgroup.one_mem _
    · exact Subgroup.closure_mono (fun g hg => List.mem_cons_of_mem _ hg) (eltG_mem_closure ss _)

theorem eltG_zero : ∀ Gs : List M, eltG Gs 0 = 1
  | [] => rfl
  | s :: ss => by simp [eltG, eltG_zero ss]

end Enumeration

section Elements

variable (D : Data) {M : Subgroup (Equiv.Perm (Fin D.n))} (genG : ℤ → M)

noncomputable abbrev pcG : List M := D.pc.map (wG D genG)

variable {D genG}

theorem forall₂_pcT (hn : D.n < 2 ^ 32) (hgen : ∀ l, Rep D.n (D.gens l) (genG l)) :
    List.Forall₂ (Rep D.n) (pcT D) (pcG D genG) := by
  rw [pcT, pcG, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.2 fun w _ => rep_wT hn hgen w

theorem rep_el (hn : D.n < 2 ^ 32) (hgen : ∀ l, Rep D.n (D.gens l) (genG l)) (m : ℕ) :
    Rep D.n (el D m) (eltG (pcG D genG) m) :=
  rep_eltT hn (forall₂_pcT hn hgen) m

theorem size_el (m : ℕ) : (el D m).size = D.n := size_eltT _ _

end Elements

end CFSG.CGT.Timmesfeld75.WCCheck
