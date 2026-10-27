module

public import CFSG.Certificates.Kernel.Misc.Sp6TransvSound
public import Certificates.Data.Kernel.Misc.Sp6Transv
import CFSG.Certificates.Kernel.Misc.PermClosProof

public section

namespace CFSG.KC.Misc.Sp6Transv

open CFSG.KD.Sp62 CFSG.KC.Sp62 CFSG.KC.Misc.Clos CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

theorem enc6_pow (g : H6) : ∀ n, enc6 (g ^ n) = PW (enc6 g) n
  | 0 => by rw [pow_zero, enc6_enc.enc_one]; rfl
  | n + 1 => by
    rw [pow_succ, enc6_enc.enc_mul, enc6_pow g n]
    rfl

@[expose] noncomputable def wordE (lt : ℕ → H6) : ℕ → ℕ → H6
  | 0, _ => 1
  | n + 1, v => lt (v % 8) * wordE lt n (v / 8)

theorem wordF_enc {L : ℕ → ℕ} {lt : ℕ → H6} (hL : ∀ l < 8, L l = enc6 (lt l)) :
    ∀ n v, wordF L n v = enc6 (wordE lt n v)
  | 0, _ => by rw [wordE, enc6_enc.enc_one]; rfl
  | n + 1, v => by
    change MULF (L (v % 8)) (wordF L n (v / 8)) = _
    rw [hL _ (Nat.mod_lt _ (by norm_num)), wordF_enc hL n, wordE, enc6_enc.enc_mul]

theorem wordI_enc {LI : ℕ → ℕ} {lt : ℕ → H6} (hL : ∀ l < 8, LI l = enc6 (lt l)⁻¹) :
    ∀ n v, wordI LI n v = enc6 (wordE lt n v)⁻¹
  | 0, _ => by rw [wordE, inv_one, enc6_enc.enc_one]; rfl
  | n + 1, v => by
    change MULF (wordI LI n (v / 8)) (LI (v % 8)) = _
    rw [hL _ (Nat.mod_lt _ (by norm_num)), wordI_enc hL n, wordE, mul_inv_rev,
      enc6_enc.enc_mul]

theorem conj_tree {g gi : ℕ → ℕ} {G : ℕ → H6} (hg : ∀ l < 2, g l = enc6 (G l))
    (hgi : ∀ l < 2, gi l = enc6 (G l)⁻¹) {x₀ : H6} {N : ℕ} {E PA : ℕ → ℕ}
    (ht : ∀ k < N, treeAt (fun x l => conjF (g l) (gi l) x) (enc6 x₀) (fun l => l) 2 E PA k =
      true) :
    ∀ k < N, ∃ h : H6, E k = enc6 (h * x₀ * h⁻¹) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    cases k with
    | zero =>
      have h : Nat.beq (E 0) (enc6 x₀) = true := ht 0 hk
      exact ⟨1, by rw [one_mul, inv_one, mul_one]; exact Nat.eq_of_beq_eq_true h⟩
    | succ k =>
      have h := ht (k + 1) hk
      simp only [treeAt, letB_eq] at h
      obtain ⟨hp, h⟩ := andB_eq_true h
      obtain ⟨hl, he⟩ := andB_eq_true h
      have hp' := Nat.blt_eq.mp hp
      have hl' := Nat.blt_eq.mp hl
      obtain ⟨u, hu⟩ := ih _ hp' (by omega)
      refine ⟨G (Nat.shiftRight (PA (k + 1)) 24) * u, ?_⟩
      rw [Nat.eq_of_beq_eq_true he, conjF, hu, hg _ hl', hgi _ hl', ← enc6_enc.enc_mul,
        ← enc6_enc.enc_mul]
      exact congrArg enc6 (by group)

theorem sort_mono {N : ℕ} {E SG : ℕ → ℕ} (hs : ∀ i < N, sortAt N E SG i = true) :
    ∀ i j, i < j → j < N → E (SG i) < E (SG j) := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
    · exact (ih h (by omega)).trans ((sortAt_spec (hs j (by omega))).2 hj)
    · exact (sortAt_spec (hs i (by omega))).2 hj

theorem sort_surj {N : ℕ} {E SG : ℕ → ℕ} (hs : ∀ i < N, sortAt N E SG i = true) :
    ∀ k < N, ∃ i < N, SG i = k := by
  have hmono := sort_mono hs
  let f : Fin N → Fin N := fun i => ⟨SG i, (sortAt_spec (hs i i.2)).1⟩
  have finj : Function.Injective f := by
    intro a b hab
    have e : SG a = SG b := congrArg Fin.val hab
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · exact absurd (congrArg E e) (hmono a b h b.2).ne
    · exact absurd (congrArg E e).symm (hmono b a h a.2).ne
  have fsurj := Finite.injective_iff_surjective.1 finj
  intro k hk
  obtain ⟨i, hi⟩ := fsurj ⟨k, hk⟩
  exact ⟨i, i.2, congrArg Fin.val hi⟩

theorem not_mem_of_gap {N : ℕ} {E SG : ℕ → ℕ} (hs : ∀ i < N, sortAt N E SG i = true) {y r : ℕ}
    (hr : r ≤ N) (hlo : 0 < r → E (SG (r - 1)) < y) (hhi : r < N → y < E (SG r)) :
    ∀ k < N, E k ≠ y := by
  intro k hk e
  obtain ⟨i, hi, rfl⟩ := sort_surj hs k hk
  have hmono := sort_mono hs
  rcases Nat.lt_or_ge i r with h | h
  · have h1 := hlo (by omega)
    rcases Nat.lt_or_ge i (r - 1) with h' | h'
    · have := hmono i (r - 1) h' (by omega)
      omega
    · have e' : i = r - 1 := by omega
      rw [e'] at e
      omega
  · have h1 := hhi (by omega)
    rcases Nat.lt_or_ge r i with h' | h'
    · have := hmono r i h' hi
      omega
    · have e' : i = r := by omega
      rw [e'] at e
      omega

theorem cntR_succ (n : ℕ) (f : ℕ → Bool) :
    cntR (n + 1) f = cntR n f + if f n = true then 1 else 0 := by
  change Bool.rec (motive := fun _ => ℕ) (cntR n f) (Nat.succ (cntR n f)) (f n) = _
  cases f n <;> rfl

theorem cntR_eq (n : ℕ) (f : ℕ → Bool) :
    cntR n f = ((Finset.range n).filter fun i => f i = true).card := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cntR_succ, ih, Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]
    · rw [Nat.add_zero]

theorem card_inf_of_cnt {H K : Subgroup H6} {N : ℕ} {E : ℕ → ℕ}
    (hE : ∀ k < N, ∃ g ∈ H, enc6 g = E k) (hall : ∀ g ∈ H, ∃ k < N, enc6 g = E k)
    (hdist : ∀ i < N, ∀ j < N, E i = E j → i = j) {f : ℕ → Bool}
    (hf : ∀ k < N, ∀ g : H6, enc6 g = E k → (f k = true ↔ g ∈ K)) :
    Nat.card ↥(H ⊓ K) = cntR N f := by
  classical
  rw [cntR_eq]
  choose! elt heltH helt using hE
  refine (Nat.card_eq_of_bijective (fun i : ((Finset.range N).filter fun i => f i = true) =>
    (⟨elt i, ?_, ?_⟩ : ↥(H ⊓ K))) ⟨?_, ?_⟩).symm.trans ?_
  · exact heltH _ (Finset.mem_range.1 (Finset.mem_filter.1 i.2).1)
  · have hi := Finset.mem_filter.1 i.2
    exact (hf _ (Finset.mem_range.1 hi.1) _ (helt _ (Finset.mem_range.1 hi.1))).1 hi.2
  · intro a b hab
    have e : elt a = elt b := congrArg Subtype.val hab
    have ha := Finset.mem_range.1 (Finset.mem_filter.1 a.2).1
    have hb := Finset.mem_range.1 (Finset.mem_filter.1 b.2).1
    exact Subtype.ext (hdist _ ha _ hb (by rw [← helt _ ha, ← helt _ hb, e]))
  · rintro ⟨g, hgH, hgK⟩
    obtain ⟨k, hk, hgk⟩ := hall g hgH
    have hfk : f k = true := (hf k hk g hgk).2 hgK
    refine ⟨⟨k, Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, hfk⟩⟩, Subtype.ext ?_⟩
    exact enc6_enc.inj (by rw [helt _ hk, hgk])
  · rw [Nat.card_eq_fintype_card, Fintype.card_coe]

end CFSG.KC.Misc.Sp6Transv

end
