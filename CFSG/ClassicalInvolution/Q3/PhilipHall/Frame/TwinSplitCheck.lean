module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4tCheck
public import Certificates.Data.E4SplitCheck
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Check

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4C

open CFSG.ClassicalInvolution.Generic

variable {n : ℕ}

theorem conjSub_closure_pair (w i j : Equiv.Perm (Fin n)) :
    conjSub w (Subgroup.closure ({i, j} : Set (Equiv.Perm (Fin n)))) =
      Subgroup.closure ({w * i * w⁻¹, w * j * w⁻¹} : Set (Equiv.Perm (Fin n))) := by
  rw [conjSub, MonoidHom.map_closure, Set.image_pair]
  rfl

theorem splitWit_spec {L : List (Equiv.Perm (Fin n))} {i j w c : Equiv.Perm (Fin n)}
    (hL : ∀ x, x ∈ Subgroup.closure ({i, j} : Set (Equiv.Perm (Fin n))) ↔ x ∈ L)
    (h : splitWit L i j w c = true) :
    c ^ 3 = 1 ∧
      conjSub c (Subgroup.closure ({i, j} : Set (Equiv.Perm (Fin n)))) =
        Subgroup.closure ({i, j} : Set (Equiv.Perm (Fin n))) ∧
      (∀ y ∈ conjSub w (Subgroup.closure ({i, j} : Set (Equiv.Perm (Fin n)))), c * y = y * c) ∧
      ∃ k ∈ Subgroup.closure ({i, j} : Set (Equiv.Perm (Fin n))), c * k * c⁻¹ ≠ k := by
  simp only [splitWit, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h3, hn⟩, hc⟩, hnc⟩ := h
  have h3' : c * c = c⁻¹ := of_decide_eq_true h3
  refine ⟨?_, conjSub_eq_of_norms hL hn, fun y hy => ?_, ?_⟩
  · rw [pow_succ, sq, h3', inv_mul_cancel]
  · rw [conjSub_closure_pair] at hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp (commGens_spec hc hy)).symm
  · have hnot : ¬ (c * i = i * c ∧ c * j = j * c) := by
      rintro ⟨h1, h2⟩
      simp [commGens, h1, h2] at hnc
    by_cases hi : c * i = i * c
    · refine ⟨j, Subgroup.subset_closure (by simp), fun h => hnot ⟨hi, ?_⟩⟩
      calc c * j = c * j * c⁻¹ * c := by group
        _ = j * c := by rw [h]
    · refine ⟨i, Subgroup.subset_closure (by simp), fun h => hi ?_⟩
      calc c * i = c * i * c⁻¹ * c := by group
        _ = i * c := by rw [h]

theorem exists_split_of_check {L : List (Equiv.Perm (Fin n))} {r i j : Equiv.Perm (Fin n)}
    {ws cs : List (Equiv.Perm (Fin n))} (hc : splitCheck L r i j ws cs = true) {k : ℕ}
    (hk : k < ws.length) (hr : ws.getD k 1 * r * (ws.getD k 1)⁻¹ = r)
    (hn : norms L i j (ws.getD k 1) = false) :
    ∃ c ∈ cs, splitWit L i j (ws.getD k 1) c = true := by
  simp only [splitCheck, splitOK, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', List.any_eq_true] at hc
  rcases hc k hk with h | ⟨c, hc, hw⟩
  · rw [hn, Bool.not_false, Bool.and_true] at h
    exact absurd hr (of_decide_eq_false h)
  · exact ⟨c, hc, hw⟩

end CFSG.ClassicalInvolution.Q3.TL4.E4C

namespace CFSG.ClassicalInvolution.Q3.TL4.E4A

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.ClassicalInvolution.Q3.TL4.E4C

variable {n : ℕ} {LA : List (Array ℕ)} {LP : List (Equiv.Perm (Fin n))} {i j : Array ℕ}
  {I J : Equiv.Perm (Fin n)}

theorem splitWitA_eq (hL : List.Forall₂ (Rep n) LA LP) (hi : Rep n i I) (hj : Rep n j J)
    {w c : Array ℕ} {W C : Equiv.Perm (Fin n)} (hw : Rep n w W) (hc : Rep n c C) :
    splitWitA n LA i j w c = splitWit LP I J W C := by
  rw [splitWitA, splitWit, eqA_eq (rep_compA hc hc) (rep_inv hc), normsA_eq hL hi hj hc,
    commGensA_eq (rep_conjA hw hi) (rep_conjA hw hj) hc, commGensA_eq hi hj hc]

theorem splitOKA_eq (hL : List.Forall₂ (Rep n) LA LP) (hi : Rep n i I) (hj : Rep n j J)
    {r : Array ℕ} {R : Equiv.Perm (Fin n)} (hr : Rep n r R) {csA : List (Array ℕ)}
    {csP : List (Equiv.Perm (Fin n))} (hcs : List.Forall₂ (Rep n) csA csP) {w : Array ℕ}
    {W : Equiv.Perm (Fin n)} (hw : Rep n w W) :
    splitOKA n LA r i j csA w = splitOK LP R I J csP W := by
  rw [splitOKA, splitOK, eqA_eq (rep_conjA hw hr) hr, normsA_eq hL hi hj hw]
  congr 1
  exact any_eq_of_forall₂ hcs fun a b hab => splitWitA_eq hL hi hj hw hab

theorem splitCheckA_eq (hL : List.Forall₂ (Rep n) LA LP) (hi : Rep n i I) (hj : Rep n j J)
    {r : Array ℕ} {R : Equiv.Perm (Fin n)} (hr : Rep n r R) {wA : List (Array ℕ)}
    {wP : List (Equiv.Perm (Fin n))} (hw : List.Forall₂ (Rep n) wA wP) {csA : List (Array ℕ)}
    {csP : List (Equiv.Perm (Fin n))} (hcs : List.Forall₂ (Rep n) csA csP) :
    splitCheckA n LA r i j wA csA = splitCheck LP R I J wP csP := by
  rw [splitCheckA, splitCheck, hw.length_eq]
  congr 1
  funext k
  exact splitOKA_eq hL hi hj hr hcs (rep_getD hw k)

end CFSG.ClassicalInvolution.Q3.TL4.E4A
