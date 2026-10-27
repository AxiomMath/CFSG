module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Arr
public import Certificates.Data.E189E4tCheck
public import CFSG.ClassicalInvolution.Generic.Frame

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4C

open CFSG.ClassicalInvolution.Generic

variable {n : ℕ}

theorem commGens_spec {i j b : Equiv.Perm (Fin n)} (h : commGens i j b = true) :
    Subgroup.closure ({i, j} : Set (Equiv.Perm (Fin n))) ≤
      Subgroup.centralizer ({b} : Set (Equiv.Perm (Fin n))) := by
  simp only [commGens, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [Subgroup.closure_le]
  rintro z (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  · exact h.1.symm
  · exact h.2.symm

theorem comm_of_mem_conjSub {G : Type*} [Group G] {K : Subgroup G} {x a : G}
    (h : K ≤ Subgroup.centralizer ({x⁻¹ * a * x} : Set G)) {w : G} (hw : w ∈ conjSub x K) :
    w * a = a * w := by
  rw [mem_conjSub_iff] at hw
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp (h hw)
  calc w * a = x * ((x⁻¹ * w * x) * (x⁻¹ * a * x)) * x⁻¹ := by group
    _ = x * ((x⁻¹ * a * x) * (x⁻¹ * w * x)) * x⁻¹ := by rw [h1]
    _ = a * w := by group

theorem goodWit_spec {i j r t x : Equiv.Perm (Fin n)} (h : goodWit r i j t x = true) :
    ∀ w ∈ conjSub x (Subgroup.closure ({i, j} : Set (Equiv.Perm (Fin n)))) ⊔
      conjSub x (conjSub t (Subgroup.closure ({i, j} : Set (Equiv.Perm (Fin n))))),
      w * (r * t) = (r * t) * w := by
  simp only [goodWit, Bool.and_eq_true] at h
  have hle : conjSub x (Subgroup.closure ({i, j} : Set (Equiv.Perm (Fin n)))) ⊔
      conjSub x (conjSub t (Subgroup.closure ({i, j} : Set (Equiv.Perm (Fin n))))) ≤
      Subgroup.centralizer ({r * t} : Set (Equiv.Perm (Fin n))) := by
    refine sup_le (fun w hw => ?_) (fun w hw => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (comm_of_mem_conjSub (commGens_spec h.1) hw)
    · rw [← conjSub_mul] at hw
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (comm_of_mem_conjSub (commGens_spec h.2) hw)
  intro w hw
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)

theorem exists_good_of_tCheck {L : List (Equiv.Perm (Fin n))} {r i j : Equiv.Perm (Fin n)}
    {ws : List (Equiv.Perm (Fin n))} (hc : tCheck L r i j ws = true) {k : ℕ} (hk : k < ws.length)
    (hrel : relevantT L r i j (ws.getD k 1 * r * (ws.getD k 1)⁻¹) = true) :
    ∃ l < ws.length,
      goodWit r i j (ws.getD k 1 * r * (ws.getD k 1)⁻¹) (ws.getD l 1) = true := by
  simp only [tCheck, memberOK, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', List.any_eq_true] at hc
  rcases hc k hk with h | ⟨l, hl, hg⟩
  · rw [hrel] at h
    exact absurd h (by simp)
  · exact ⟨l, hl, hg⟩

end CFSG.ClassicalInvolution.Q3.TL4.E4C

namespace CFSG.ClassicalInvolution.Q3.TL4.E4A

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.ClassicalInvolution.Q3.TL4.E4C

variable {n : ℕ} {LA : List (Array ℕ)} {LP : List (Equiv.Perm (Fin n))} {i j : Array ℕ}
  {I J : Equiv.Perm (Fin n)}

theorem commGensA_eq (hi : Rep n i I) (hj : Rep n j J) {b : Array ℕ} {B : Equiv.Perm (Fin n)}
    (hb : Rep n b B) : commGensA n i j b = commGens I J B := by
  rw [commGensA, commGens, eqA_eq (rep_compA hb hi) (rep_compA hi hb),
    eqA_eq (rep_compA hb hj) (rep_compA hj hb)]

theorem goodWitA_eq (hi : Rep n i I) (hj : Rep n j J) {r t x : Array ℕ}
    {R T X : Equiv.Perm (Fin n)} (hr : Rep n r R) (ht : Rep n t T) (hx : Rep n x X) :
    goodWitA n r i j t x = goodWit R I J T X := by
  rw [goodWitA, goodWit]
  have ha := rep_compA hr ht
  have hxt := rep_compA hx ht
  rw [commGensA_eq hi hj (rep_compA (rep_compA (rep_inv hx) ha) hx),
    commGensA_eq hi hj (rep_compA (rep_compA (rep_inv hxt) ha) hxt)]

theorem relevantTA_eq (hL : List.Forall₂ (Rep n) LA LP) (hi : Rep n i I) (hj : Rep n j J)
    {r t : Array ℕ} {R T : Equiv.Perm (Fin n)} (hr : Rep n r R) (ht : Rep n t T) :
    relevantTA n LA r i j t = relevantT LP R I J T := by
  rw [relevantTA, relevantT, eqA_eq (rep_compA ht hr) (rep_compA hr ht),
    normsA_eq hL hi hj ht]

theorem tCheckA_eq (hL : List.Forall₂ (Rep n) LA LP) (hi : Rep n i I) (hj : Rep n j J)
    {r : Array ℕ} {R : Equiv.Perm (Fin n)} (hr : Rep n r R) {wA : List (Array ℕ)}
    {wP : List (Equiv.Perm (Fin n))} (hw : List.Forall₂ (Rep n) wA wP) :
    tCheckA n LA r i j wA = tCheck LP R I J wP := by
  rw [tCheckA, tCheck, hw.length_eq]
  congr 1
  funext k
  rw [memberOKA, memberOK, hw.length_eq,
    relevantTA_eq hL hi hj hr (rep_conjA (rep_getD hw k) hr)]
  congr 1
  congr 1
  funext l
  exact goodWitA_eq hi hj hr (rep_conjA (rep_getD hw k) hr) (rep_getD hw l)

end CFSG.ClassicalInvolution.Q3.TL4.E4A
