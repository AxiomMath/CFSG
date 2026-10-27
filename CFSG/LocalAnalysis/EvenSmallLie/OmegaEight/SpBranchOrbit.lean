module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchCode
public import Mathlib.GroupTheory.Rank
public import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.Index

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup MulAction

variable {H : Type*} [Group H]

theorem card_centralizer_mul_ncard (u : H) :
    Nat.card (centralizer ({u} : Set H)) * (orbit (ConjAct H) u).ncard = Nat.card H := by
  rw [nat_card_centralizer_nat_card_stabilizer, ← index_stabilizer, card_mul_index]
  exact Nat.card_congr ConjAct.ofConjAct.toEquiv

theorem mem_orbit_iff_conj {u x : H} : x ∈ orbit (ConjAct H) u ↔ ∃ g : H, g * u * g⁻¹ = x := by
  rw [ConjAct.mem_orbit_conjAct, isConj_comm, isConj_iff]

@[expose] def orbOK (mul : ℕ → ℕ → ℕ) (inv : ℕ → ℕ) (N u : ℕ) (O : List (ℕ × ℕ)) : Bool :=
  (O.all fun p => decide (p.2 < N) && p.1 == cconj mul inv p.2 u) && decide (O.map Prod.fst).Nodup

@[expose] def orbClosed (mul : ℕ → ℕ → ℕ) (inv : ℕ → ℕ) (gens : List ℕ) (u : ℕ)
    (O : List (ℕ × ℕ)) : Bool :=
  (O.map Prod.fst).contains u &&
    O.all fun p => gens.all fun g => (O.map Prod.fst).contains (cconj mul inv g p.1)

@[expose] def orbitStep (mul : ℕ → ℕ → ℕ) (inv : ℕ → ℕ) (gens : List ℕ)
    (st : List (ℕ × ℕ) × ℕ) : List (ℕ × ℕ) × ℕ :=
  match st.1[st.2]? with
  | none => st
  | some (o, w) =>
    (gens.foldl (fun acc g =>
      let v := cconj mul inv g o
      if acc.any (fun p => p.1 == v) then acc else acc ++ [(v, mul g w)]) st.1, st.2 + 1)

@[expose] def orbitRec (mul : ℕ → ℕ → ℕ) (inv : ℕ → ℕ) (gens : List ℕ) (bound u : ℕ) :
    List (ℕ × ℕ) :=
  ((List.range (bound + 2)).foldl (fun st _ =>
    if st.1.length > bound then st else orbitStep mul inv gens st) ([(u, 0)], 0)).1

@[expose] def invOK (mul : ℕ → ℕ → ℕ) (inv : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range N).all fun c => decide (inv c < N) && mul c (inv c) == 0

theorem inv_spec {mul : ℕ → ℕ → ℕ} {inv : ℕ → ℕ} {N : ℕ} (hinv : invOK mul inv N = true) {c : ℕ}
    (hc : c < N) : inv c < N ∧ mul c (inv c) = 0 := by
  have h := List.all_eq_true.1 hinv c (List.mem_range.2 hc)
  simpa using h

theorem nodup_of_orbOK {mul : ℕ → ℕ → ℕ} {inv : ℕ → ℕ} {N u : ℕ} {O : List (ℕ × ℕ)}
    (hO : orbOK mul inv N u O = true) : (O.map Prod.fst).Nodup := by
  unfold orbOK at hO
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hO
  exact hO.2

namespace CodeIso

variable {N : ℕ} {mul : ℕ → ℕ → ℕ} (Φ : CodeIso H N mul) {inv : ℕ → ℕ}

theorem exists_conj_of_orbOK (h0 : mul 0 0 = 0) (hinv : invOK mul inv N = true) {u : H}
    {O : List (ℕ × ℕ)} (hO : orbOK mul inv N (Φ.f u) O = true) {o : ℕ}
    (ho : o ∈ O.map Prod.fst) : ∃ g : H, Φ.f (g * u * g⁻¹) = o := by
  unfold orbOK at hO
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hO
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ho
  obtain ⟨hw, hpo⟩ := hO.1 p hp
  refine ⟨Φ.g p.2, ?_⟩
  rw [Φ.f_conj h0 (fun c hc => inv_spec hinv hc), Φ.f_g hw, hpo]

theorem length_le_ncard (h0 : mul 0 0 = 0) (hinv : invOK mul inv N = true) {u : H}
    {O : List (ℕ × ℕ)} (hO : orbOK mul inv N (Φ.f u) O = true) :
    O.length ≤ (orbit (ConjAct H) u).ncard := by
  classical
  have := Φ.finite
  set L := O.map Prod.fst
  have hsub : (↑(L.toFinset.image Φ.g) : Set H) ⊆ orbit (ConjAct H) u := by
    intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, List.mem_toFinset] at hx
    obtain ⟨o, ho, rfl⟩ := hx
    obtain ⟨g, hg⟩ := Φ.exists_conj_of_orbOK h0 hinv hO ho
    rw [mem_orbit_iff_conj]
    exact ⟨g, by rw [← hg, Φ.g_f]⟩
  have hinj : Set.InjOn Φ.g (L.toFinset : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, List.mem_toFinset] at ha hb
    obtain ⟨g, rfl⟩ := Φ.exists_conj_of_orbOK h0 hinv hO ha
    obtain ⟨g', rfl⟩ := Φ.exists_conj_of_orbOK h0 hinv hO hb
    rw [Φ.g_f, Φ.g_f] at hab
    rw [hab]
  calc O.length = L.length := (List.length_map _).symm
    _ = L.toFinset.card := (List.toFinset_card_of_nodup (nodup_of_orbOK hO)).symm
    _ = (L.toFinset.image Φ.g).card := (Finset.card_image_of_injOn hinj).symm
    _ = (↑(L.toFinset.image Φ.g) : Set H).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

theorem mem_orbit_iff (h0 : mul 0 0 = 0) (hinv : invOK mul inv N = true) {gens : List ℕ}
    (hgens : ∀ g ∈ gens, g < N) (hG : Gen mul gens N) {u : H} {O : List (ℕ × ℕ)}
    (hO : orbOK mul inv N (Φ.f u) O = true) (hC : orbClosed mul inv gens (Φ.f u) O = true)
    (x : H) : x ∈ orbit (ConjAct H) u ↔ Φ.f x ∈ O.map Prod.fst := by
  unfold orbClosed at hC
  simp only [Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true] at hC
  constructor
  · rw [mem_orbit_iff_conj]
    rintro ⟨g, rfl⟩
    have key : ∀ g : H, ∀ y : H, Φ.f y ∈ O.map Prod.fst → Φ.f (g * y * g⁻¹) ∈ O.map Prod.fst := by
      intro g
      refine Φ.induction h0 hgens hG (P := fun g => ∀ y : H, Φ.f y ∈ O.map Prod.fst →
        Φ.f (g * y * g⁻¹) ∈ O.map Prod.fst) (fun y hy => ?_) ?_ g
      · rwa [one_mul, inv_one, mul_one]
      intro h hP c hc y hy
      have e : h * Φ.g c * y * (h * Φ.g c)⁻¹ = h * (Φ.g c * y * (Φ.g c)⁻¹) * h⁻¹ := by group
      rw [e]
      refine hP _ ?_
      rw [Φ.f_conj h0 (fun c hc => inv_spec hinv hc), Φ.f_g (hgens c hc)]
      obtain ⟨p, hp, hpy⟩ := List.mem_map.1 hy
      have := hC.2 p hp c hc
      rwa [hpy] at this
    exact key g u hC.1
  · intro hx
    obtain ⟨g, hg⟩ := Φ.exists_conj_of_orbOK h0 hinv hO hx
    rw [mem_orbit_iff_conj]
    exact ⟨g, Φ.inj hg⟩

theorem ncard_eq (h0 : mul 0 0 = 0) (hinv : invOK mul inv N = true) {gens : List ℕ}
    (hgens : ∀ g ∈ gens, g < N) (hG : Gen mul gens N) {u : H} {O : List (ℕ × ℕ)}
    (hO : orbOK mul inv N (Φ.f u) O = true) (hC : orbClosed mul inv gens (Φ.f u) O = true) :
    (orbit (ConjAct H) u).ncard = O.length := by
  classical
  refine le_antisymm ?_ (Φ.length_le_ncard h0 hinv hO)
  have := Φ.finite
  set L := O.map Prod.fst
  have hsub : orbit (ConjAct H) u ⊆ (↑(L.toFinset.image Φ.g) : Set H) := by
    intro x hx
    rw [Φ.mem_orbit_iff h0 hinv hgens hG hO hC] at hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, List.mem_toFinset]
    exact ⟨_, hx, Φ.g_f x⟩
  calc (orbit (ConjAct H) u).ncard ≤ (↑(L.toFinset.image Φ.g) : Set H).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = (L.toFinset.image Φ.g).card := Set.ncard_coe_finset _
    _ ≤ L.toFinset.card := Finset.card_image_le
    _ ≤ L.length := List.toFinset_card_le _
    _ = O.length := List.length_map _

end CodeIso

end CFSG.EvenSmallLie.OmegaEight.SpBranch
