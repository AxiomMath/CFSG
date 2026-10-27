module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevExcU33Data
public import CFSG.GroupTheory.PCoreOfInvolution

public section

namespace CFSG.GroupTheory.GomiExcU33

open CFSG.Open CFSG.Quasithin CFSG.Sporadic.Bridge Subgroup

theorem repL_u33ConjL {w : List (ℕ × Bool)}
    (hw : ∀ l ∈ w, l.1 < 5) {o : List ℕ} {σ : Equiv.Perm (Fin 28)} (ho : RepL o σ) :
    RepL (u33ConjL w o) (wordProd u33GenP w * σ * (wordProd u33GenP w)⁻¹) := by
  have hi := u33_wordL_rep (u33InvW w) (by
    intro l hl
    simp only [u33InvW, List.mem_map, List.mem_reverse] at hl
    obtain ⟨l', hl', rfl⟩ := hl
    exact hw l' hl')
  rw [wordProd_invW] at hi
  exact repL_mul (repL_mul (u33_wordL_rep w hw) ho) hi

private lemma card_le_24 :
    Nat.card ↥(u33J ⊓ centralizer ({u33Pi} : Set (Equiv.Perm (Fin 28)))) ≤ 24 := by
  set C : Subgroup (Equiv.Perm (Fin 28)) := u33J ⊓ centralizer {u33Pi}
  let L : List (List ℕ) := u33OrbWords.map fun s => u33ConjL (u33W s) u33PiTab
  have hL : L.length = 252 := by simp only [L, List.length_map, u33Words_length.1]
  let w : Fin L.length → String := fun k =>
    u33OrbWords[k.1]'(by rw [u33Words_length.1]; omega)
  let e : String → Equiv.Perm (Fin 28) := fun s => wordProd u33GenP (u33W s)
  have hwS : ∀ k, w k ∈ u33OrbWords := fun k => by
    dsimp only [w]; exact List.getElem_mem (l := u33OrbWords) (n := k.1)
      (h := by rw [u33Words_length.1]; omega)
  have hlet : ∀ k, ∀ l ∈ u33W (w k), l.1 < 5 := fun k => u33Words_letters.1 (w k) (hwS k)
  have heJ : ∀ k, e (w k) ∈ u33J := fun k =>
    wordProd_mem_pred (P := fun i => i < 5) (fun i _ => u33GenP_mem i) (hlet k)
  let F : Fin L.length → (↥u33J ⧸ C.subgroupOf u33J) := fun k =>
    ((⟨e (w k), heJ k⟩ : ↥u33J) : ↥u33J ⧸ C.subgroupOf u33J)
  have hF : Function.Injective F := by
    intro i j hij
    have hmem : (e (w i))⁻¹ * e (w j) ∈ C :=
      Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hij)
    have hcomm : (e (w i))⁻¹ * e (w j) * u33Pi = u33Pi * ((e (w i))⁻¹ * e (w j)) :=
      ((Subgroup.mem_centralizer_iff.1 hmem.2) u33Pi (by simp)).symm
    have hconj : wordProd u33GenP (u33W (w i)) * u33Pi * (wordProd u33GenP (u33W (w i)))⁻¹
        = wordProd u33GenP (u33W (w j)) * u33Pi * (wordProd u33GenP (u33W (w j)))⁻¹ := by
      let A : Equiv.Perm (Fin 28) := e (w i)
      let B : Equiv.Perm (Fin 28) := e (w j)
      have hc : A⁻¹ * B * u33Pi = u33Pi * (A⁻¹ * B) := hcomm
      have h : A * (A⁻¹ * B * u33Pi) * B⁻¹ = A * (u33Pi * (A⁻¹ * B)) * B⁻¹ := by rw [hc]
      change A * u33Pi * A⁻¹ = B * u33Pi * B⁻¹
      simpa [mul_assoc] using h.symm
    have hrep_i := repL_u33ConjL (w := u33W (w i)) (hlet i) u33_pi_rep
    have hrep_j := repL_u33ConjL (w := u33W (w j)) (hlet j) u33_pi_rep
    have hlist : u33ConjL (u33W (w i)) u33PiTab = u33ConjL (u33W (w j)) u33PiTab :=
      repL_unique hrep_i (hconj.symm ▸ hrep_j)
    have hnodup : L.Nodup := by simpa [L] using u33OrbWords_nodup
    have hget : L[i.1]'i.2 = L[j.1]'j.2 := by simpa [L, w] using hlist
    exact Fin.ext ((hnodup.getElem_inj_iff (hi := i.2) (hj := j.2)).1 hget)
  have hindex : 252 ≤ (C.subgroupOf u33J).index := by
    rw [Subgroup.index_eq_card]
    simpa [hL] using Nat.card_le_card_of_injective F hF
  have h24 : Nat.card ↥(C.subgroupOf u33J) ≤ 24 := by
    have h := Nat.mul_le_mul_left (Nat.card ↥(C.subgroupOf u33J)) hindex
    rw [Subgroup.card_mul_index, card_u33J] at h
    omega
  rwa [show Nat.card ↥C = Nat.card ↥(C.subgroupOf u33J) from
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show C ≤ u33J from inf_le_left)).toEquiv).symm]

private lemma exists_eq_of_mem :
    ∀ x ∈ (u33J ⊓ centralizer ({u33Pi} : Set (Equiv.Perm (Fin 28)))),
      ∃ s, s ∈ u33CentWords ∧ x = wordProd u33GenP (u33W s) := by
  set C : Subgroup (Equiv.Perm (Fin 28)) := u33J ⊓ centralizer {u33Pi}
  let L : List (List ℕ) := u33CentWords.map fun s => u33WordL (u33W s)
  have hL : L.length = 24 := by simp only [L, List.length_map, u33Words_length.2.1]
  let w : Fin L.length → String := fun k =>
    u33CentWords[k.1]'(by rw [u33Words_length.2.1]; omega)
  let e : String → Equiv.Perm (Fin 28) := fun s => wordProd u33GenP (u33W s)
  have hwS : ∀ k, w k ∈ u33CentWords := fun k => by
    dsimp only [w]; exact List.getElem_mem (l := u33CentWords) (n := k.1)
      (h := by rw [u33Words_length.2.1]; omega)
  have hlet : ∀ k, ∀ l ∈ u33W (w k), l.1 < 5 := fun k => u33Words_letters.2.1 (w k) (hwS k)
  have heJ : ∀ k, e (w k) ∈ u33J := fun k =>
    wordProd_mem_pred (P := fun i => i < 5) (fun i _ => u33GenP_mem i) (hlet k)
  have heC : ∀ k, e (w k) ∈ C := by
    refine fun k => ⟨heJ k, ?_⟩
    change e (w k) ∈ centralizer ({u33Pi} : Set (Equiv.Perm (Fin 28)))
    rw [Subgroup.mem_centralizer_iff]
    rintro y rfl
    have hrep1 := repL_mul (u33_wordL_rep (u33W (w k)) (hlet k)) u33_pi_rep
    have hrep2 := repL_mul u33_pi_rep (u33_wordL_rep (u33W (w k)) (hlet k))
    have hrep2' : RepL (compL (u33WordL (u33W (w k))) u33PiTab)
        (u33Pi * wordProd u33GenP (u33W (w k))) := by
      rw [← u33CentWords_comm (w k) (hwS k)] at hrep2
      exact hrep2
    have hcomm : e (w k) * u33Pi = u33Pi * e (w k) := eq_of_repL hrep1 hrep2'
    exact hcomm.symm
  let g : Fin L.length → ↥C := fun k => ⟨e (w k), heC k⟩
  have hg : Function.Injective g := by
    intro i j hij
    have hval : wordProd u33GenP (u33W (w i)) = wordProd u33GenP (u33W (w j)) :=
      congrArg (fun z : ↥C => (z : Equiv.Perm (Fin 28))) hij
    have hrep_i := u33_wordL_rep (u33W (w i)) (hlet i)
    have hrep_j := u33_wordL_rep (u33W (w j)) (hlet j)
    have hlist : u33WordL (u33W (w i)) = u33WordL (u33W (w j)) :=
      repL_unique hrep_i (hval.symm ▸ hrep_j)
    have hnodup : L.Nodup := by simpa [L] using u33CentWords_nodup
    have hget : L[i.1]'i.2 = L[j.1]'j.2 := by simpa [L, w] using hlist
    exact Fin.ext ((hnodup.getElem_inj_iff (hi := i.2) (hj := j.2)).1 hget)
  have hbij : Function.Bijective g :=
    Function.Injective.bijective_of_nat_card_le hg (by
      rw [show Nat.card (Fin L.length) = 24 by simp [hL]]
      exact card_le_24)
  intro x hx
  obtain ⟨k, hk⟩ := hbij.2 ⟨x, hx⟩
  refine ⟨w k, hwS k, ?_⟩
  exact (congrArg (fun z : ↥C => (z : Equiv.Perm (Fin 28))) hk).symm

theorem pCoreOf_inf_centralizer_u33Pi_ne_bot :
    pCoreOf 2 (u33J ⊓ centralizer ({u33Pi} : Set (Equiv.Perm (Fin 28)))) ≠ ⊥ := by
  classical
  let C : Subgroup (Equiv.Perm (Fin 28)) := u33J ⊓ centralizer {u33Pi}
  change pCoreOf 2 C ≠ ⊥
  have ht_mem : u33A2 ∈ C := by
    refine ⟨?_, ?_⟩
    · show u33GenP 0 * u33GenP 0 ∈ u33J
      exact u33J.mul_mem (u33GenP_mem 0) (u33GenP_mem 0)
    · change u33A2 ∈ centralizer ({u33Pi} : Set (Equiv.Perm (Fin 28)))
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have hrep1 := repL_mul u33_a2_rep u33_pi_rep
      have hrep2 := repL_mul u33_pi_rep u33_a2_rep
      have hrep2' : RepL (compL u33A2Tab u33PiTab) (u33Pi * u33A2) := by
        rw [← u33A2Tab_facts.2.2] at hrep2
        exact hrep2
      have hcomm : u33A2 * u33Pi = u33Pi * u33A2 := eq_of_repL hrep1 hrep2'
      exact hcomm.symm
  have ht1 : u33A2 ≠ 1 :=
    ne_of_repL_ne u33_a2_rep (repL_one 28) u33A2Tab_facts.2.1
  have ht2 : u33A2 * u33A2 = 1 := by
    have h := repL_mul u33_a2_rep u33_a2_rep
    rw [u33A2Tab_facts.1] at h
    exact eq_of_repL h (repL_one 28)
  have hc : ∀ x ∈ C, x * u33A2 * x⁻¹ * u33A2 = u33A2 * (x * u33A2 * x⁻¹) := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := exists_eq_of_mem x hx
    have hlet : ∀ l ∈ u33W s, l.1 < 5 := u33Words_letters.2.1 s hs
    have hrep1 := repL_mul (repL_u33ConjL (w := u33W s) hlet u33_a2_rep) u33_a2_rep
    have hrep2 := repL_mul u33_a2_rep (repL_u33ConjL (w := u33W s) hlet u33_a2_rep)
    have hrep2' : RepL (compL (u33ConjL (u33W s) u33A2Tab) u33A2Tab)
        (u33A2 * (wordProd u33GenP (u33W s) * u33A2 * (wordProd u33GenP (u33W s))⁻¹)) := by
      rw [← u33CentWords_conj s hs] at hrep2
      exact hrep2
    exact eq_of_repL hrep1 hrep2'
  exact pCoreOf_ne_bot_of_commute_conj ht_mem ht1 ht2 hc

end CFSG.GroupTheory.GomiExcU33
