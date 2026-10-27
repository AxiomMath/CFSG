module

public import Certificates.Data.Kernel.SporCov.CenL
public import CFSG.Certificates.Kernel.SporCov.CensusSound

public section

namespace CFSG.KD.SporCov

open CFSG.KC.SporCov

theorem nthW_succ_tailW : ∀ (T : List (List ℕ)) (n : ℕ), nthW T (n + 1) = nthW (tailW T) n
  | [], n => by rw [nthW_nil]; exact (nthW_nil n).symm
  | _ :: _, _ => rfl

theorem cenAll_spec {E : List ℕ → List ℕ → Bool} {p k : ℕ} {H Rp Gs : List (List ℕ)} :
    ∀ {P : List ℕ} {T : List (List ℕ)}, cenAll E p H k Rp Gs P T = true →
      ∀ n < P.length, cenE E p H k Rp Gs (nthN P n) (nthW T n) = true
  | [], _, _, n, hn => absurd hn (by simp)
  | m :: P, T, h, n, hn => by
    change (cenE E p H k Rp Gs m (headW T) && cenAll E p H k Rp Gs P (tailW T)) = true at h
    rw [Bool.and_eq_true] at h
    cases n with
    | zero => exact h.1
    | succ n =>
      rw [nthN_cons_succ, nthW_succ_tailW]
      exact cenAll_spec h.2 n (by simp at hn; omega)

theorem cenOK_of_cenE {E : List ℕ → List ℕ → Bool} {p k N n : ℕ} {H Rp Gs T : List (List ℕ)}
    {P : List ℕ} (h : cenE E p H k Rp Gs (nthN P n) (nthW T n) = true) :
    cenOK E p H k Rp Gs P T N n = true := by
  revert h
  unfold cenE cenOK
  cases Nat.beq (nthN (nthW T n) 0) 0 <;> cases Nat.beq (nthN (nthW T n) 0) 1 <;>
    cases Nat.beq (nthN (nthW T n) 0) 2 <;> simp only [cond_false, cond_true] <;> intro h <;>
    first | exact h | exact absurd h Bool.false_ne_true

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow

variable {G : Type} [Group G]

theorem closure_eq_pcSub (g : ℕ → G) (k : ℕ) :
    Subgroup.closure {x | ∃ j < k, x = g j} = pcSub (fun t : Fin k => (g t)⁻¹) 0 := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x ⟨j, hj, rfl⟩
    have h : (g j)⁻¹ ∈ pcSub (fun t : Fin k => (g t)⁻¹) 0 :=
      Subgroup.subset_closure ⟨⟨j, hj⟩, Nat.zero_le _, rfl⟩
    simpa using Subgroup.inv_mem _ h
  · unfold pcSub
    rw [Subgroup.closure_le]
    rintro x ⟨t, -, rfl⟩
    exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨t.val, t.isLt, rfl⟩)

namespace Model

variable {L : ℕ → Bool} {E : List ℕ → List ℕ → Bool} {ev : List ℕ → G} (hM : Model L E ev)
include hM

theorem pcSub_card_of_cen [Finite G] {p k : ℕ} (hp : p.Prime) (K : List ℕ → ℕ)
    (hK : ∀ u v, chW L u = true → chW L v = true → ev u = ev v → K u = K v)
    {H R : List (List ℕ)} {P : List ℕ} (oH : chA L H = true)
    (hR : ∀ i < k, ∀ j < k, i ≤ j → pcR E p H R k i j = true)
    (hlen : P.length = p ^ k) (hI : keyInc K H k p P = true) :
    Nat.card (pcSub (fun t : Fin k => (ev (nthW H t))⁻¹) 0) = p ^ k := by
  set g : ℕ → G := fun t => ev (nthW H t) with hg
  set S := pcSub (fun t : Fin k => (g t)⁻¹) 0 with hSdef
  set w : ℕ → List ℕ := fun n => cw H k p (nthN P n) with hw
  have ow : ∀ n, chW L (w n) = true := fun n => chW_nfW oH _ _ _
  have hwS : ∀ n, ev (w n) ∈ S := fun n => by
    rw [hw]
    unfold cw
    rw [hM.ev_nfW]
    exact nfG_mem g _ 0 k 0 (by omega) fun t _ _ => Or.inr (Nat.zero_le t)
  obtain ⟨hpow, hconj⟩ := hM.pcR_facts oH hR
  have hle : Nat.card S ≤ p ^ k := pc_card hp.pos g hpow hconj
  let f : Fin (p ^ k) → S := fun n => ⟨ev (w n), hwS n⟩
  have hf : Function.Injective f := by
    intro a b hab
    have e : ev (w a) = ev (w b) := congrArg Subtype.val hab
    have eK := hK _ _ (ow a) (ow b) e
    by_contra hne'
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne') with h | h
    · exact absurd eK (keyInc_mono K H k p hI a b h (by rw [hlen]; exact b.isLt)).ne
    · exact absurd eK (keyInc_mono K H k p hI b a h (by rw [hlen]; exact a.isLt)).ne'
  refine le_antisymm hle ?_
  have := Nat.card_le_card_of_injective f hf
  simpa using this

end Model

end CFSG.KD.SporCov

end
