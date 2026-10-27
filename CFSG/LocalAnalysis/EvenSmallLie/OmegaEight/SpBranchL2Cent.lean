module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchKillD
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchSPrime

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup

section Data

variable (mul : ℕ → ℕ → ℕ) (inv : ℕ → ℕ) (gens : List ℕ) (N : ℕ)

@[expose] def centOK3 (B : ℕ) (e : ℕ × List ℕ × ℕ × ℕ) : Bool :=
  decide (e.1 < N) && orbOKM mul inv N e.1 (recMB mul inv gens B e.1) &&
    orbClosedM mul inv gens e.1 (recMB mul inv gens B e.1) &&
    ((e.2.1.zip e.2.1.tail).all fun p => decide (p.1 < p.2)) &&
    (e.2.1.all fun c => decide (c < N) && mul c e.1 == mul e.1 c) &&
    e.2.1.length * (recMB mul inv gens B e.1).length == N &&
    (e.2.1.filter fun c => mul c c == 0 && c != 0).length == e.2.2.1 &&
    (e.2.1.filter (isOrd4 mul)).length == e.2.2.2

end Data

theorem chain_of_zip_tail' {C : List ℕ} (h : ∀ p ∈ C.zip C.tail, p.1 < p.2) :
    C.IsChain (· < ·) := by
  induction C with
  | nil => exact List.isChain_nil
  | cons a l ih =>
    refine List.isChain_cons.2 ⟨fun y hy => ?_, ih fun p hp => h p ?_⟩
    · cases l with
      | nil => simp at hy
      | cons b l =>
        obtain rfl : b = y := by simpa using hy
        exact h (a, b) (by simp)
    · cases l with
      | nil => simp at hp
      | cons b l =>
        simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]
        exact Or.inr hp

section Spec

variable {H : Type*} [Group H] {N : ℕ} {mul : ℕ → ℕ → ℕ} (Φ : CodeIso H N mul) {inv : ℕ → ℕ}
  {gens : List ℕ} (h0 : mul 0 0 = 0) (hinv : invOK mul inv N = true) (hgens : ∀ g ∈ gens, g < N)
  (hG : Gen mul gens N)

include Φ h0 hinv hgens hG in
theorem centOK3_spec {B : ℕ} {e : ℕ × List ℕ × ℕ × ℕ} (hc : centOK3 mul inv gens N B e = true) :
    kCount mul (kInv mul N) e.1 = e.2.2.1 ∧ kCount mul (kOrd4 mul N) e.1 = e.2.2.2 := by
  unfold centOK3 at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨hlt, hO⟩, hCl⟩, hsort⟩, hcomm⟩, hlen⟩, hcntI⟩, hcnt⟩ := hc
  have hO' := orbOK_of_M mul inv N hO
  have hCl' := orbClosed_of_M mul inv gens hCl
  have hu : Φ.f (Φ.g e.1) = e.1 := Φ.f_g hlt
  have hnd : e.2.1.Nodup :=
    (List.isChain_iff_pairwise.1 (chain_of_zip_tail' hsort)).imp ne_of_lt
  refine ⟨?_, ?_⟩
  · have key := count_comm_eq Φ (Φ.g e.1) hnd (fun c hc => by
      rw [hu]; exact hcomm c hc) (by
        rw [Φ.ncard_eq h0 hinv hgens hG (by rw [hu]; exact hO') (by rw [hu]; exact hCl')]
        exact hlen) (fun c => mul c c == 0 && c != 0)
    rw [hu] at key
    rw [← hcntI, ← key]
    unfold kCount kInv
    rw [List.filter_filter]
    congr 1
    apply List.filter_congr
    intro c _
    rw [Bool.and_comm]
  · have key := kCount_kOrd4_list Φ h0 hinv hgens hG (u := Φ.g e.1)
      (O := recMB mul inv gens B e.1) (by rw [hu]; exact hO') (by rw [hu]; exact hCl')
      hnd (fun c hc => by rw [hu]; exact hcomm c hc) hlen
    rw [hu] at key
    rw [key, hcnt]

end Spec

section Counts

variable {G : Type*} [Group G] {T : Subgroup G} {N : ℕ} {mul : ℕ → ℕ → ℕ}
  (Φ : CodeIso T N mul) (h0 : mul 0 0 = 0)

include h0 in
theorem nInv_inf_centralizer (u : T) :
    nInv (T ⊓ centralizer ({(u : G)} : Set G)) = kCount mul (kInv mul N) (Φ.f u) := by
  unfold kCount nInv
  rw [Φ.length_kInv_filter h0]
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨x.1, x.2.1.1⟩, ?_, ?_, ?_⟩
      invFun := fun h => ⟨h.1, ⟨h.1.2, ?_⟩, ?_, ?_⟩
      left_inv := fun x => rfl
      right_inv := fun h => rfl }
  · exact Subtype.ext x.2.2.1
  · intro h; exact x.2.2.2 (congrArg Subtype.val h)
  · rw [beq_iff_eq, ← Φ.map_mul, ← Φ.map_mul, Φ.f_eq_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.1 x.2.1.2)
  · have h3 := h.2.2.2
    rw [beq_iff_eq, ← Φ.map_mul, ← Φ.map_mul, Φ.f_eq_iff] at h3
    exact mem_centralizer_singleton_iff.2 (congrArg Subtype.val h3)
  · exact congrArg Subtype.val h.2.1
  · intro h1; exact h.2.2.1 (Subtype.ext h1)

include h0 in
theorem nOrd4_inf_centralizer (u : T) :
    nOrd4 (T ⊓ centralizer ({(u : G)} : Set G)) = kCount mul (kOrd4 mul N) (Φ.f u) := by
  unfold kCount nOrd4
  rw [Φ.length_kOrd4_filter h0]
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨x.1, x.2.1.1⟩, ?_, ?_, ?_⟩
      invFun := fun h => ⟨h.1, ⟨h.1.2, ?_⟩, ?_, ?_⟩
      left_inv := fun x => rfl
      right_inv := fun h => rfl }
  · intro h; exact x.2.2.1 (congrArg Subtype.val h)
  · exact Subtype.ext x.2.2.2
  · rw [beq_iff_eq, ← Φ.map_mul, ← Φ.map_mul, Φ.f_eq_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.1 x.2.1.2)
  · have h3 := h.2.2.2
    rw [beq_iff_eq, ← Φ.map_mul, ← Φ.map_mul, Φ.f_eq_iff] at h3
    exact mem_centralizer_singleton_iff.2 (congrArg Subtype.val h3)
  · intro h1; exact h.2.1 (Subtype.ext h1)
  · exact congrArg Subtype.val h.2.2.1

end Counts

end CFSG.EvenSmallLie.OmegaEight.SpBranch

end
