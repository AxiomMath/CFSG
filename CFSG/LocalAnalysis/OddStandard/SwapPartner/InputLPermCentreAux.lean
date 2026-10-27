module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Equiv Equiv.Perm Subgroup

theorem perm_mul_self_apply {π : Perm (Fin 12)} (hπ : π * π = 1) (x : Fin 12) :
    π (π x) = x := by
  have h := congrArg (fun f : Perm (Fin 12) => f x) hπ
  simpa only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using h

theorem commute_of_fixes_moved {π g : Perm (Fin 12)}
    (hg : ∀ w, π w ≠ w → g w = w) : g * π = π * g := by
  apply Equiv.ext
  intro w
  simp only [Equiv.Perm.mul_apply]
  by_cases hw : π w = w
  · rw [hw]
    by_contra h
    have hne : π (g w) ≠ g w := fun hh => h hh.symm
    have hfix : g (g w) = g w := hg (g w) hne
    have hgw : g w = w := g.injective hfix
    exact hne (by rw [hgw, hw])
  · have hne : π (π w) ≠ π w := fun hh => hw (π.injective hh)
    rw [hg w hw, hg (π w) hne]

private theorem swap_mul_swap_comm {a b c d : Fin 12} (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) : swap a b * swap c d = swap c d * swap a b := by
  apply Equiv.Perm.Disjoint.commute
  intro i
  by_cases hi : i = a ∨ i = b
  · right
    rcases hi with rfl | rfl
    · exact Equiv.swap_apply_of_ne_of_ne hac had
    · exact Equiv.swap_apply_of_ne_of_ne hbc hbd
  · push Not at hi
    exact Or.inl (Equiv.swap_apply_of_ne_of_ne hi.1 hi.2)

private theorem swap_triple_apply_eq_self {x p q w : Fin 12} (hwx : w ≠ x) (hwp : w ≠ p)
    (hwq : w ≠ q) : (swap x p * swap p q) w = w := by
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hwp hwq,
    Equiv.swap_apply_of_ne_of_ne hwx hwp]

private theorem swap_triple_apply_left {x p q : Fin 12} (hxp : x ≠ p) (hxq : x ≠ q) :
    (swap x p * swap p q) x = p := by
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxp hxq, Equiv.swap_apply_left]

private theorem mem_triple_of_commute {c : Perm (Fin 12)} {x p q : Fin 12}
    (hxp : x ≠ p) (hxq : x ≠ q) (hpq : p ≠ q)
    (hcomm : (swap x p * swap p q) * c = c * (swap x p * swap p q)) :
    c x = x ∨ c x = p ∨ c x = q := by
  by_contra hmem
  simp only [not_or] at hmem
  obtain ⟨hcx, hcp, hcq⟩ := hmem
  have hfix : (swap x p * swap p q) (c x) = c x :=
    swap_triple_apply_eq_self hcx hcp hcq
  have hcong : (swap x p * swap p q) (c x) = c ((swap x p * swap p q) x) := by
    have := congrArg (fun f : Perm (Fin 12) => f x) hcomm
    simpa only [Equiv.Perm.mul_apply] using this
  rw [hfix, swap_triple_apply_left hxp hxq] at hcong
  exact hxp (c.injective hcong)

private theorem commute_pi_swap_mul {π : Perm (Fin 12)}
    {u v x y : Fin 12} (huv : π u = v) (hvu : π v = u) (hx : π x = x) (hy : π y = y) :
    π * (swap u v * swap x y) = (swap u v * swap x y) * π := by
  have hA : π * swap u v = swap u v * π := by
    rw [Equiv.mul_swap_eq_swap_mul, huv, hvu, Equiv.swap_comm]
  have hB : π * swap x y = swap x y * π := by
    rw [Equiv.mul_swap_eq_swap_mul, hx, hy]
  calc π * (swap u v * swap x y)
      = (π * swap u v) * swap x y := by rw [mul_assoc]
    _ = (swap u v * π) * swap x y := by rw [hA]
    _ = swap u v * (π * swap x y) := by rw [mul_assoc]
    _ = swap u v * (swap x y * π) := by rw [hB]
    _ = (swap u v * swap x y) * π := by rw [mul_assoc]

theorem apply_eq_self_of_forall_commute {π : Perm (Fin 12)}
    (hf : 5 ≤ Fintype.card {x : Fin 12 // π x = x}) {c : Perm (Fin 12)}
    (hcc : ∀ g ∈ alternatingGroup (Fin 12), (∀ x, π x ≠ x → g x = x) → g * c = c * g)
    {x : Fin 12} (hx : π x = x) : c x = x := by
  classical
  let F : Finset (Fin 12) := Finset.univ.filter (fun w => π w = w)
  have hxmem : x ∈ F := by
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hx
  let T : Finset (Fin 12) := F.erase x
  have hTcard : 4 ≤ T.card := by
    have hFcard : F.card = Fintype.card {x : Fin 12 // π x = x} := by
      simp only [F]
      exact (Fintype.card_subtype (fun w : Fin 12 => π w = w)).symm
    have herase : T.card = F.card - 1 := by
      simp only [T]
      exact Finset.card_erase_of_mem hxmem
    omega
  obtain ⟨y, hy, z, hz, y', hy', z', hz', hyz, hyy', hyz', hzy', hzz', hy'z'⟩ :=
    Finset.three_lt_card.mp (show 3 < T.card by omega)
  simp only [T, F] at hy hz hy' hz'
  have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
  have hyfix : π y = y := (Finset.mem_filter.mp (Finset.mem_erase.mp hy).2).2
  have hzx : z ≠ x := (Finset.mem_erase.mp hz).1
  have hzfix : π z = z := (Finset.mem_filter.mp (Finset.mem_erase.mp hz).2).2
  have hy'x : y' ≠ x := (Finset.mem_erase.mp hy').1
  have hy'fix : π y' = y' := (Finset.mem_filter.mp (Finset.mem_erase.mp hy').2).2
  have hz'x : z' ≠ x := (Finset.mem_erase.mp hz').1
  have hz'fix : π z' = z' := (Finset.mem_filter.mp (Finset.mem_erase.mp hz').2).2
  have hxy : x ≠ y := hyx.symm
  have hxz : x ≠ z := hzx.symm
  have hxy' : x ≠ y' := hy'x.symm
  have hxz' : x ≠ z' := hz'x.symm
  have hgA : (swap x y * swap y z) ∈ alternatingGroup (Fin 12) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hxy,
      Equiv.Perm.sign_swap hyz]
    decide
  have hgfix : ∀ w, π w ≠ w → (swap x y * swap y z) w = w := by
    intro w hw
    exact swap_triple_apply_eq_self (fun h => hw (h ▸ hx)) (fun h => hw (h ▸ hyfix))
      (fun h => hw (h ▸ hzfix))
  have hgc : (swap x y * swap y z) * c = c * (swap x y * swap y z) := hcc _ hgA hgfix
  have hcyxz : c x = x ∨ c x = y ∨ c x = z := mem_triple_of_commute hxy hxz hyz hgc
  have hg'A : (swap x y' * swap y' z') ∈ alternatingGroup (Fin 12) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hxy',
      Equiv.Perm.sign_swap hy'z']
    decide
  have hg'fix : ∀ w, π w ≠ w → (swap x y' * swap y' z') w = w := by
    intro w hw
    exact swap_triple_apply_eq_self (fun h => hw (h ▸ hx)) (fun h => hw (h ▸ hy'fix))
      (fun h => hw (h ▸ hz'fix))
  have hg'c : (swap x y' * swap y' z') * c = c * (swap x y' * swap y' z') := hcc _ hg'A hg'fix
  have hcy'z' : c x = x ∨ c x = y' ∨ c x = z' := mem_triple_of_commute hxy' hxz' hy'z' hg'c
  rcases hcyxz with h | h | h
  · exact h
  · rw [h] at hcy'z'
    rcases hcy'z' with h' | h' | h'
    · exact absurd h' hyx
    · exact absurd h' hyy'
    · exact absurd h' hyz'
  · rw [h] at hcy'z'
    rcases hcy'z' with h' | h' | h'
    · exact absurd h' hzx
    · exact absurd h' hzy'
    · exact absurd h' hzz'

theorem swap_mul_swap_mem_inf_centralizer_fixed {π : Perm (Fin 12)} {u v x y : Fin 12}
    (huv : π u = v) (hvu : π v = u) (hx : π x = x) (hy : π y = y) (hne : u ≠ v) (hxy : x ≠ y) :
    swap u v * swap x y ∈
      alternatingGroup (Fin 12) ⊓ centralizer ({π} : Set (Perm (Fin 12))) := by
  refine ⟨?_, ?_⟩
  · change swap u v * swap x y ∈ alternatingGroup (Fin 12)
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne,
      Equiv.Perm.sign_swap hxy]
    decide
  · change swap u v * swap x y ∈ centralizer ({π} : Set (Perm (Fin 12)))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_pi_swap_mul huv hvu hx hy).symm

theorem swap_mul_swap_mem_inf_centralizer_moved {π : Perm (Fin 12)} {a a' b b' : Fin 12}
    (ha : a' = π a) (hb : b' = π b) (hπa' : π a' = a) (hπb' : π b' = b) (hab : a ≠ b)
    (haa' : a ≠ a') (hab' : a ≠ b') (ha'b : a' ≠ b) (ha'b' : a' ≠ b') (hbb' : b ≠ b') :
    swap a b * swap a' b' ∈
      alternatingGroup (Fin 12) ⊓ centralizer ({π} : Set (Perm (Fin 12))) := by
  have hdisj : swap a' b' * swap a b = swap a b * swap a' b' :=
    swap_mul_swap_comm haa'.symm ha'b hab'.symm hbb'.symm
  have h1 : π * swap a b = swap a' b' * π := by
    rw [Equiv.mul_swap_eq_swap_mul, ← ha, ← hb]
  have h2 : π * swap a' b' = swap a b * π := by
    rw [Equiv.mul_swap_eq_swap_mul, hπa', hπb']
  have hcomm : π * (swap a b * swap a' b') = (swap a b * swap a' b') * π := by
    calc π * (swap a b * swap a' b')
        = (π * swap a b) * swap a' b' := by rw [mul_assoc]
      _ = (swap a' b' * π) * swap a' b' := by rw [h1]
      _ = swap a' b' * (π * swap a' b') := by rw [mul_assoc]
      _ = swap a' b' * (swap a b * π) := by rw [h2]
      _ = (swap a' b' * swap a b) * π := by rw [mul_assoc]
      _ = (swap a b * swap a' b') * π := by rw [hdisj]
  refine ⟨?_, ?_⟩
  · change swap a b * swap a' b' ∈ alternatingGroup (Fin 12)
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
      Equiv.Perm.sign_swap ha'b']
    decide
  · change swap a b * swap a' b' ∈ centralizer ({π} : Set (Perm (Fin 12)))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm.symm

end CFSG.OddStandard.AltStdSec.SwapPartner
