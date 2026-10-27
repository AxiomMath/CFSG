module

public import Certificates.Data.Sylow185.U38

public section

namespace CFSG.KC.U38R

open CFSG.RankThree.PartTwo.Sec18.Item185Proof.U38Elim
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.Monster.B.Fischer CFSG.Monster.B.Co2

theorem getD_foldl_insert {f : ℕ → ℕ} :
    ∀ N : ℕ, (∀ a < N, ∀ b < N, f a = f b → a = b) → ∀ m < N,
      ((List.range N).foldl (fun mp i => mp.insert (f i) i) (∅ : Std.HashMap ℕ ℕ)).getD (f m) 0 = m
  | 0, _, m, hm => absurd hm (Nat.not_lt_zero m)
  | N + 1, hinj, m, hm => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Std.HashMap.getD_insert]
    by_cases h : m = N
    · subst h
      simp
    · have hmN : m < N := by omega
      have hne : (f N == f m) = false := by
        rw [beq_eq_false_iff_ne]
        intro e
        exact h (hinj m hm N (by omega) e.symm)
      rw [hne]
      exact getD_foldl_insert N (fun a ha b hb => hinj a (by omega) b (by omega)) m hmN

theorem ps_eq : ps = [0, 1] := rfl

theorem hps : ∀ p ∈ ps, p < 513 := by decide

theorem keyProd_eq (E : Array (Array ℕ)) (i j : ℕ) :
    keyProd E i j = keyA 513 ps (compA 513 E[i]! E[j]!) := by
  unfold keyA keyProd
  apply congrArg (Nat.ofDigits 513)
  apply List.map_congr_left
  intro p hp
  rw [compA_get (hps p hp)]

theorem keyProd_closure {gs : Array (Array ℕ)} {c : ArrCert} (h : enumOK 513 gs ps c = true)
    {i j : ℕ} (hi : i < c.pts.size) (hj : j < c.pts.size) :
    ∃ m < c.pts.size, keyA 513 ps c.pts[m]! = keyProd c.pts i j := by
  obtain ⟨hmem, -, hval⟩ := enumOK_spec hps h
  have hx : permOfArr 513 c.pts[i]! * permOfArr 513 c.pts[j]! ∈
      Subgroup.closure (permsA 513 gs) :=
    Subgroup.mul_mem _ ((hmem _).2 ⟨i, hi, rfl⟩) ((hmem _).2 ⟨j, hj, rfl⟩)
  obtain ⟨m, hm, hrep⟩ := enumOK_exists_rep hps h hx
  have hc := rep_compA (rep_of_validA (hval i hi)) (rep_of_validA (hval j hj))
  refine ⟨m, hm, ?_⟩
  unfold keyA keyProd
  congr 1
  apply List.map_congr_left
  intro p hp
  have hp' : p < 513 := hps p hp
  rw [hrep.apply hp', ← hc.apply hp', compA_get hp']

section Table

variable {gs : Array (Array ℕ)} {c : ArrCert} (h : enumOK 513 gs ps c = true) {K : ℕ → ℕ}
  (hK : ∀ m < c.pts.size, K (keyA 513 ps c.pts[m]!) = m)
include h hK

theorem keyProd_idx {i j : ℕ} (hi : i < c.pts.size) (hj : j < c.pts.size) :
    K (keyProd c.pts i j) < c.pts.size ∧
      keyA 513 ps c.pts[K (keyProd c.pts i j)]! = keyProd c.pts i j := by
  obtain ⟨m, hm, e⟩ := keyProd_closure h hi hj
  rw [← e, hK m hm]
  exact ⟨hm, rfl⟩

theorem mulI_mulTab {i j : ℕ} (hi : i < c.pts.size) (hj : j < c.pts.size) :
    mulI (mulTab c.pts) i j = K (keyProd c.pts i j) := by
  have hinj : ∀ a < c.pts.size, ∀ b < c.pts.size,
      keyA 513 ps c.pts[a]! = keyA 513 ps c.pts[b]! → a = b := fun a ha b hb e => by
    rw [← hK a ha, ← hK b hb, e]
  obtain ⟨m, hm, e⟩ := keyProd_closure h hi hj
  unfold mulI mulTab
  simp only
  rw [getElem!_ofFn_nat' hi, getElem!_ofFn_nat' hj, ← e, hK m hm]
  exact getD_foldl_insert (f := fun i => keyA 513 ps c.pts[i]!) c.pts.size hinj m hm
where
  getElem!_ofFn_nat' {α : Type} [Inhabited α] {m k : ℕ} {f : Fin m → α} (hk : k < m) :
      (Array.ofFn f)[k]! = f ⟨k, hk⟩ := by
    rw [getElem!_pos (Array.ofFn f) k (by simpa using hk), Array.getElem_ofFn]

theorem tabOK_mulTab : tabOK c.pts (mulTab c.pts) = true := by
  unfold tabOK
  rw [allLt_iff]
  intro i hi
  rw [allLt_iff]
  intro j hj
  rw [mulI_mulTab h hK hi hj]
  obtain ⟨h1, h2⟩ := keyProd_idx h hK hi hj
  rw [h2, decide_eq_true h1]
  simp

end Table

end CFSG.KC.U38R

end
