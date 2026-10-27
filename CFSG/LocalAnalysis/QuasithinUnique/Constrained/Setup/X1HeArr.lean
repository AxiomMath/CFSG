module

public import CFSG.Monster.B.Co2.PermArr
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Sub

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

section PArr

variable {n : ℕ}

abbrev PArr : Type := Array ℕ × Array ℕ

@[expose] def PRep (n : ℕ) (x : PArr) (g : Equiv.Perm (Fin n)) : Prop :=
  Rep n x.1 g ∧ Rep n x.2 g⁻¹

@[expose] def pId (n : ℕ) : PArr := (idA n, idA n)

@[expose] def pMul (n : ℕ) (x y : PArr) : PArr := (compA n x.1 y.1, compA n y.2 x.2)

@[expose] def pInv (x : PArr) : PArr := (x.2, x.1)

theorem pRep_id : PRep n (pId n) 1 :=
  ⟨rep_idA, by rw [inv_one]; exact rep_idA⟩

theorem PRep.mul {x y : PArr} {g h : Equiv.Perm (Fin n)} (hx : PRep n x g) (hy : PRep n y h) :
    PRep n (pMul n x y) (g * h) :=
  ⟨rep_compA hx.1 hy.1, by rw [mul_inv_rev]; exact rep_compA hy.2 hx.2⟩

theorem PRep.inv {x : PArr} {g : Equiv.Perm (Fin n)} (hx : PRep n x g) : PRep n (pInv x) g⁻¹ :=
  ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

theorem PRep.of_sq {a : Array ℕ} {g : Equiv.Perm (Fin n)} (ha : Rep n a g) (hg : g * g = 1) :
    PRep n (a, a) g := by
  refine ⟨ha, ?_⟩
  have : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  rw [this]
  exact ha

@[expose] def pLetter (n : ℕ) (regs : List PArr) (z : ℤ) : PArr :=
  if z = 0 then pId n
  else if 0 < z then regs.getD (z.toNat - 1) (pId n)
  else pInv (regs.getD ((-z).toNat - 1) (pId n))

@[expose] def pRun (n : ℕ) : List PArr → List (ℤ × ℤ) → List PArr
  | regs, [] => regs
  | regs, pq :: rest =>
      pRun n (regs ++ [pMul n (pLetter n regs pq.1) (pLetter n regs pq.2)]) rest

@[expose] def pWord (n : ℕ) (gens : List PArr) : List ℤ → PArr
  | [] => pId n
  | z :: w => pMul n (pLetter n gens z) (pWord n gens w)

@[expose] def pConj (n : ℕ) (g t : PArr) : PArr := pMul n (pMul n g t) (pInv g)

@[expose] def RegIn (n : ℕ) (K : Subgroup (Equiv.Perm (Fin n))) (regs : List PArr) : Prop :=
  ∀ r ∈ regs, ∃ g ∈ K, PRep n r g

variable {K : Subgroup (Equiv.Perm (Fin n))} {regs : List PArr}

theorem RegIn.letter (h : RegIn n K regs) (z : ℤ) : ∃ g ∈ K, PRep n (pLetter n regs z) g := by
  unfold pLetter
  split_ifs with h0 h1
  · exact ⟨1, K.one_mem, pRep_id⟩
  · by_cases hlen : z.toNat - 1 < regs.length
    · obtain ⟨g, hg, hr⟩ := h _ (List.getD_eq_getElem regs (pId n) hlen ▸ List.getElem_mem hlen)
      exact ⟨g, hg, hr⟩
    · rw [List.getD_eq_default _ _ (by omega)]
      exact ⟨1, K.one_mem, pRep_id⟩
  · by_cases hlen : (-z).toNat - 1 < regs.length
    · obtain ⟨g, hg, hr⟩ := h _ (List.getD_eq_getElem regs (pId n) hlen ▸ List.getElem_mem hlen)
      exact ⟨g⁻¹, K.inv_mem hg, hr.inv⟩
    · rw [List.getD_eq_default _ _ (by omega)]
      exact ⟨1, K.one_mem, by simpa [pInv, pId] using (pRep_id (n := n))⟩

theorem RegIn.run (prog : List (ℤ × ℤ)) : ∀ {regs : List PArr}, RegIn n K regs →
    RegIn n K (pRun n regs prog) := by
  induction prog with
  | nil => intro regs h; exact h
  | cons pq rest ih =>
    intro regs h
    refine ih ?_
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact h r hr
    · rw [List.mem_singleton] at hr
      subst hr
      obtain ⟨g1, hg1, hr1⟩ := h.letter pq.1
      obtain ⟨g2, hg2, hr2⟩ := h.letter pq.2
      exact ⟨g1 * g2, K.mul_mem hg1 hg2, hr1.mul hr2⟩

theorem RegIn.word (h : RegIn n K regs) : ∀ w : List ℤ, ∃ g ∈ K, PRep n (pWord n regs w) g := by
  intro w
  induction w with
  | nil => exact ⟨1, K.one_mem, pRep_id⟩
  | cons z w ih =>
    obtain ⟨g1, hg1, hr1⟩ := h.letter z
    obtain ⟨g2, hg2, hr2⟩ := ih
    exact ⟨g1 * g2, K.mul_mem hg1 hg2, hr1.mul hr2⟩

end PArr

section ThreeConj

variable {n : ℕ} {K : Subgroup (Equiv.Perm (Fin n))} {gens : List PArr}

theorem exists_conjugators (hK : RegIn n K gens) {t : PArr} {τ : Equiv.Perm (Fin n)}
    (ht : PRep n t τ) :
    ∀ ws : List (List ℤ), ∃ gs : List (Equiv.Perm (Fin n)), gs.length = ws.length ∧
      (∀ g ∈ gs, g ∈ K) ∧
      ∀ r ∈ ws.map (fun w => pConj n (pWord n gens w) t), ∃ g ∈ gs, PRep n r (g * τ * g⁻¹) := by
  intro ws
  induction ws with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons w ws ih =>
    obtain ⟨gs, hlen, hgs, hr⟩ := ih
    obtain ⟨g, hg, hrep⟩ := hK.word w
    refine ⟨g :: gs, by simp [hlen], ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hg
      · exact hgs x hx
    · intro r hr'
      rcases List.mem_cons.1 hr' with rfl | hr'
      · exact ⟨g, List.mem_cons_self, (hrep.mul ht).mul hrep.inv⟩
      · obtain ⟨g', hg', h'⟩ := hr r hr'
        exact ⟨g', List.mem_cons_of_mem _ hg', h'⟩

@[expose] def threeConjCheck (n : ℕ) (gens : List PArr) (t : PArr) (ws : List (List ℤ))
    (prog : List (ℤ × ℤ)) (targets : List (Array ℕ)) : Bool :=
  let regs := pRun n (ws.map fun w => pConj n (pWord n gens w) t) prog
  targets.all fun A => regs.any fun r => eqA n r.1 A

theorem threeConj_sound (hK : RegIn n K gens) {t : PArr} {τ : Equiv.Perm (Fin n)}
    (ht : PRep n t τ) {ws : List (List ℤ)} {prog : List (ℤ × ℤ)} {targets : List (Array ℕ)}
    (hc : threeConjCheck n gens t ws prog targets = true) :
    ∃ gs : List (Equiv.Perm (Fin n)), gs.length = ws.length ∧ (∀ g ∈ gs, g ∈ K) ∧
      ∀ A ∈ targets, ∀ a : Equiv.Perm (Fin n), Rep n A a →
        a ∈ Subgroup.closure (conjSet gs {τ}) := by
  obtain ⟨gs, hlen, hgs, hr⟩ := exists_conjugators hK ht ws
  refine ⟨gs, hlen, hgs, fun A hA a hAa => ?_⟩
  set K' : Subgroup (Equiv.Perm (Fin n)) := Subgroup.closure (conjSet gs {τ}) with hK'
  have hreg : RegIn n K' (ws.map fun w => pConj n (pWord n gens w) t) := by
    intro r hr0
    obtain ⟨g, hg, hrep⟩ := hr r hr0
    exact ⟨g * τ * g⁻¹, Subgroup.subset_closure ⟨g, hg, τ, rfl, rfl⟩, hrep⟩
  have hrun := hreg.run prog
  simp only [threeConjCheck, List.all_eq_true, List.any_eq_true] at hc
  obtain ⟨r, hrmem, hrA⟩ := hc A hA
  obtain ⟨g', hg', hrep⟩ := hrun r hrmem
  have : g' = a := (eqA_iff hrep.1 hAa).1 hrA
  rw [← this]
  exact hg'

end ThreeConj

end CFSG.QuasithinUnique.Setup.X1
