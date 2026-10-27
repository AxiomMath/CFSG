module

public import Certificates.Data.Kernel.RankElim

public section

namespace CFSG.KC.RankElim

open SimpleGraph CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.ElimCert
  CFSG.Sporadic.Co1Patterson

variable {n : ℕ} {nb : Array (Array ℕ)} {par dep : ℕ → ℕ} {rk ap bp : ℕ → ℕ → ℕ}
  {tri : ℕ → ℕ → ℕ → Bool}

theorem ok_parts (h : ok n nb par dep rk ap bp tri = true) :
    0 < n ∧ (∀ x < n, x = 0 ∨ (par x < n ∧ dep (par x) < dep x ∧ adjB nb (par x) x = true)) ∧
      ∀ x < n, ∀ k < (nb[x]!).size, listOK n nb par rk ap bp tri x k = true := by
  simp only [ok, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hn, hp⟩, hl⟩ := h
  exact ⟨hn, fun x hx => by simpa [and_assoc] using hp x hx, hl⟩

noncomputable def parF (hn : 0 < n) (par : ℕ → ℕ)
    (hp : ∀ x < n, x = 0 ∨ (par x < n ∧ dep (par x) < dep x ∧ adjB nb (par x) x = true))
    (x : Fin n) : Fin n :=
  if hx : x.1 = 0 then ⟨0, hn⟩ else ⟨par x.1, ((hp x.1 x.2).resolve_left hx).1⟩

theorem parF_spec {hn : 0 < n}
    {hp : ∀ x < n, x = 0 ∨ (par x < n ∧ dep (par x) < dep x ∧ adjB nb (par x) x = true)}
    (x : Fin n) (hx : x.1 ≠ 0) :
    dep (parF (dep := dep) (nb := nb) hn par hp x).1 < dep x.1 ∧
      (nbrGraph n nb).Adj (parF (dep := dep) (nb := nb) hn par hp x) x := by
  have h := (hp x.1 x.2).resolve_left hx
  simp only [parF, hx, ↓reduceDIte]
  exact ⟨h.2.1, nbrGraph_adj_iff.2 h.2.2⟩

theorem parF_val {hn : 0 < n}
    {hp : ∀ x < n, x = 0 ∨ (par x < n ∧ dep (par x) < dep x ∧ adjB nb (par x) x = true)}
    (x : Fin n) (hx : x.1 ≠ 0) : (parF (dep := dep) (nb := nb) hn par hp x).1 = par x.1 := by
  simp only [parF, hx, ↓reduceDIte]

theorem triangulableBy_of_ok {T : Set (Fin n) → Prop}
    (htri : ∀ x y z : Fin n, tri x.1 y.1 z.1 = true → T {x, y, z})
    (h : ok n nb par dep rk ap bp tri = true) : TriangulableBy (nbrGraph n nb) T := by
  obtain ⟨hn, hp, hl⟩ := ok_parts h
  let pF := parF (dep := dep) (nb := nb) hn par hp
  let d : Fin n → ℕ := fun x => dep x.1
  have hpar : ∀ x : Fin n, x.1 ≠ 0 → d (pF x) < d x ∧ (nbrGraph n nb).Adj (pF x) x :=
    fun x hx => parF_spec x hx
  let tree : Fin n → Fin n → Prop := fun x y => y.1 ≠ 0 ∧ pF y = x
  have htree : ∀ x y, tree x y → ∃ h : (nbrGraph n nb).Adj x y,
      treeWalk _ hn pF d hpar y = (treeWalk _ hn pF d hpar x).concat h := by
    rintro x y ⟨hy, rfl⟩
    exact ⟨(hpar y hy).2, treeWalk_of_ne hy⟩
  have key : ∀ r x (hx : x < n) k, k < (nb[x]!).size → rk x k = r →
      ∀ hy : (nb[x]!)[k]! < n, x ≠ (nb[x]!)[k]! →
        Derivable (nbrGraph n nb) T tree ⟨x, hx⟩ ⟨_, hy⟩ := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro x hx k hk hr hy hxy
      have hL := hl x hx k hk
      simp only [listOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
        bne_iff_ne, ne_eq] at hL
      rcases hL with ((he | hge) | ⟨h0, ⟨hy0, hpy⟩ | ⟨hx0, hpx⟩⟩) | hL
      · exact absurd he hxy
      · omega
      · refine .tree ⟨by simp only; omega, Fin.ext ?_⟩
        rw [parF_val _ (by simp only; omega)]
        exact hpy
      · refine .symm (.tree ⟨by simp only; omega, Fin.ext ?_⟩)
        rw [parF_val _ (by simp only; omega)]
        exact hpx
      · obtain ⟨⟨⟨⟨⟨⟨⟨hr0, hap⟩, hz⟩, hxz⟩, hzy⟩, hra⟩, hsub⟩, ht⟩ := hL
        rw [hr] at hr0 hra
        have d₁ := ih _ hra x hx (ap x k) hap rfl hz hxz
        have d₂ : Derivable (nbrGraph n nb) T tree ⟨_, hz⟩ ⟨_, hy⟩ := by
          rcases hsub with ⟨⟨hb, hbe⟩, hbr⟩ | ⟨⟨hb, hbe⟩, hbr⟩
          · rw [hr] at hbr
            have := ih _ hbr _ hz (bp x k) hb rfl (by rw [hbe]; exact hy) (by rw [hbe]; exact hzy)
            simp only [hbe] at this
            exact this
          · rw [hr] at hbr
            have := ih _ hbr _ hy (bp x k) hb rfl (by rw [hbe]; exact hz)
              (by rw [hbe]; exact Ne.symm hzy)
            simp only [hbe] at this
            exact this.symm
        have hadj : (nbrGraph n nb).Adj ⟨x, hx⟩ ⟨_, hy⟩ :=
          ⟨fun e => hxy (congrArg Fin.val e), Or.inl (occB_iff.2 ⟨k, hk, rfl⟩)⟩
        exact .tri hadj (htri ⟨x, hx⟩ ⟨_, hz⟩ ⟨_, hy⟩ ht) d₁ d₂
  have hlist : ∀ (x y : Fin n), x ≠ y → occB nb[x.1]! y.1 = true →
      Derivable (nbrGraph n nb) T tree x y := by
    intro x y hxy hocc
    obtain ⟨k, hk, hky⟩ := occB_iff.1 hocc
    have := key _ x.1 x.2 k hk rfl (by rw [hky]; exact y.2)
      (by rw [hky]; exact fun e => hxy (Fin.ext e))
    simp only [hky] at this
    exact this
  refine triangulableBy_of_derivable (treeWalk _ hn pF d hpar) htree fun x y hxy => ?_
  obtain ⟨hne, hocc | hocc⟩ := hxy
  · exact hlist x y hne hocc
  · exact (hlist y x (Ne.symm hne) hocc).symm

theorem preconnected_of_ok (h : ok n nb par dep rk ap bp tri = true) :
    (nbrGraph n nb).Preconnected := by
  obtain ⟨hn, hp, -⟩ := ok_parts h
  let pF := parF (dep := dep) (nb := nb) hn par hp
  let d : Fin n → ℕ := fun x => dep x.1
  have hpar : ∀ x : Fin n, x.1 ≠ 0 → d (pF x) < d x ∧ (nbrGraph n nb).Adj (pF x) x :=
    fun x hx => parF_spec x hx
  intro x y
  exact ((treeWalk _ hn pF d hpar x).reverse.append (treeWalk _ hn pF d hpar y)).reachable

end CFSG.KC.RankElim
