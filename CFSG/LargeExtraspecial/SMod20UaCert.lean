module

public import Certificates.Certificate21263

public section

namespace CFSG.LargeExtraspecial.SMod20

open CFSG.Fischer CFSG.SmithE CFSG.F4.Native CFSG.Fischer.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native

theorem uaPlaneCheck_holds : chkUA () = true :=
  Certificates.certificate21263

structure UaFacts : Prop where
  size : uaPts.size = 891
  plane : ∀ i < 891, uaPlaneOK (perpTab ()) tvTabs uaPts[i]! = true
  hyp : uaHypOK (perpTab ()) tvTabs = true
  distinct : uaDistinctOK uaPts = true
  mask : uaMaskOK uaPts = true

theorem uaFacts : UaFacts := by
  have h := uaPlaneCheck_holds
  unfold chkUA at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1, parAll_eq_true h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

@[expose] def wPt (i k : ℕ) : Fin 693 :=
  if h : (uaPts[i]!)[k]! < 693 then ⟨(uaPts[i]!)[k]!, h⟩ else 0

@[expose] def wPlane (i : ℕ) : Set (Fin 693) := {p | ∃ k < 21, wPt i k = p}

@[expose] noncomputable def uaGen (i k : ℕ) :
    Equiv.Perm (Fin 693) :=
  tvP (wPt i k)

@[expose] def bitProd {G : Type*} [Group G] (g : ℕ → G) (a : ℕ) : ℕ → G
  | 0 => 1
  | n + 1 => bitProd g a n * if a.testBit n then g n else 1

@[expose] def bitSum (v : ℕ → ℕ) (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => bitSum v a n ^^^ if a.testBit n then v n else 0

@[expose] noncomputable def uaPsi (i a : ℕ) :
    Equiv.Perm (Fin 693) :=
  bitProd (uaGen i) a 9

theorem mem_wPlane {i : ℕ} {p : Fin 693} : p ∈ wPlane i ↔ ∃ k < 21, wPt i k = p := Iff.rfl

theorem wPt_mem (i : ℕ) {k : ℕ} (hk : k < 21) : wPt i k ∈ wPlane i := ⟨k, hk, rfl⟩

theorem wPlane_finite (i : ℕ) : (wPlane i).Finite := Set.toFinite _

section Facts


theorem uaPlane_parts {i : ℕ} (hi : i < 891) :
    uaPts[i]!.size = 21 ∧ (∀ k < 21, (uaPts[i]!)[k]! < 693) ∧
      (∀ k < 21, ∀ l < 21, k ≠ l → (uaPts[i]!)[k]! ≠ (uaPts[i]!)[l]!) ∧
      (∀ k < 21, ∀ l < 21, ((perpTab ())[(uaPts[i]!)[k]!]!)[(uaPts[i]!)[l]!]! = true) ∧
      (∀ q < 693, (∀ k < 21, ((perpTab ())[(uaPts[i]!)[k]!]!)[q]! = true) →
        ∃ k < 21, (uaPts[i]!)[k]! = q) ∧
      (∀ k < 21, ∀ x < 693, uaAp tvTabs uaPts[i]! uaCo[k]! 9 x = ap (tvTabs[(uaPts[i]!)[k]!]!) x) ∧
      ∀ a, 1 ≤ a → a < 512 → ∃ x < 693, uaAp tvTabs uaPts[i]! a 9 x ≠ x := by
  have h := uaFacts.plane i hi
  unfold uaPlaneOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, fun k hk => ?_, fun k hk l hl hkl => ?_, fun k hk l hl => ?_, fun q hq H => ?_,
    fun k hk x hx => ?_, fun a ha1 ha2 => ?_⟩
  · exact of_decide_eq_true ((allIn_eq_true.1 h2) k (Nat.zero_le _) hk)
  · have := (allIn_eq_true.1 ((allIn_eq_true.1 h3) k (Nat.zero_le _) hk)) l (Nat.zero_le _) hl
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at this
    exact this.resolve_left hkl
  · exact (allIn_eq_true.1 ((allIn_eq_true.1 h4) k (Nat.zero_le _) hk)) l (Nat.zero_le _) hl
  · have := (allIn_eq_true.1 h5) q (Nat.zero_le _) hq
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
    rcases this with h' | h'
    · exact absurd (allIn_eq_true.2 fun k _ hk => H k hk) (by rw [h']; decide)
    · obtain ⟨k, hk, hkq⟩ := anyIn_eq_true.1 h'
      exact ⟨k, hk, beq_iff_eq.1 hkq⟩
  · exact beq_iff_eq.1 ((allIn_eq_true.1 ((allIn_eq_true.1 h6) k (Nat.zero_le _) hk)) x
      (Nat.zero_le _) hx)
  · obtain ⟨x, hx, hne⟩ := anyIn_eq_true.1 ((allIn_eq_true.1 h7) a ha1 ha2)
    exact ⟨x, hx, bne_iff_ne.1 hne⟩

theorem wPt_val {i k : ℕ} (hi : i < 891) (hk : k < 21) : (wPt i k).val = (uaPts[i]!)[k]! := by
  unfold wPt
  split
  · rfl
  · exact absurd ((uaPlane_parts hi).2.1 k hk) ‹_›

theorem wPt_inj {i k l : ℕ} (hi : i < 891) (hk : k < 21) (hl : l < 21)
    (h : wPt i k = wPt i l) : k = l := by
  by_contra hkl
  have := congrArg Fin.val h
  rw [wPt_val hi hk, wPt_val hi hl] at this
  exact (uaPlane_parts hi).2.2.1 k hk l hl hkl this

section Perp


theorem perp_wPt {i k l : ℕ} (hi : i < 891) (hk : k < 21) (hl : l < 21) :
    perp (wPt i k) (wPt i l) := by
  rw [← perpTab_spec, wPt_val hi hk, wPt_val hi hl]
  exact (uaPlane_parts hi).2.2.2.1 k hk l hl

theorem perp_of_mem_wPlane {i : ℕ} (hi : i < 891) {p q : Fin 693} (hp : p ∈ wPlane i)
    (hq : q ∈ wPlane i) : perp p q := by
  obtain ⟨k, hk, rfl⟩ := hp
  obtain ⟨l, hl, rfl⟩ := hq
  exact perp_wPt hi hk hl

theorem mem_wPlane_of_perp {i : ℕ} (hi : i < 891) {q : Fin 693}
    (h : ∀ p ∈ wPlane i, perp p q) : q ∈ wPlane i := by
  obtain ⟨k, hk, hkq⟩ := (uaPlane_parts hi).2.2.2.2.1 q.val q.2 fun k hk => by
    have := (perpTab_spec (wPt i k) q).2 (h _ (wPt_mem i hk))
    rwa [wPt_val hi hk] at this
  exact ⟨k, hk, Fin.ext (by rw [wPt_val hi hk, hkq])⟩

theorem not_perp_tvP {p q : Fin 693} (h : ¬ perp p q) : ¬ perp q (tvP p q) := by
  have H := (allIn_eq_true.1 ((allIn_eq_true.1 uaFacts.hyp) p.val (Nat.zero_le _) p.2)) q.val
    (Nat.zero_le _) q.2
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at H
  rcases H with H | H
  · exact absurd ((perpTab_spec p q).1 H) h
  · intro h'
    have hr : ap tvTabs[p.val]! q.val = (tvP p q).val := by
      rw [rep_tvP p q.val q.2, idx_of_lt _ q.2]
      rfl
    rw [hr, (perpTab_spec q (tvP p q)).2 h'] at H
    exact absurd H (by decide)

end Perp

theorem wPlane_injective {i j : ℕ} (hi : i < 891) (hj : j < 891) (h : wPlane i = wPlane j) :
    i = j := by
  by_contra hij
  have H := (allIn_eq_true.1 ((allIn_eq_true.1 uaFacts.distinct) i (Nat.zero_le _) hi)) j
    (Nat.zero_le _) hj
  simp only [Bool.or_eq_true, beq_iff_eq] at H
  obtain ⟨k, hk, hk'⟩ := anyIn_eq_true.1 (H.resolve_left hij)
  have hmem : wPt i k ∈ wPlane j := h ▸ wPt_mem i hk
  obtain ⟨l, hl, hlk⟩ := hmem
  rw [Bool.not_eq_true'] at hk'
  have : uaMem uaPts[j]! (uaPts[i]!)[k]! = true :=
    anyIn_eq_true.2 ⟨l, hl, by rw [beq_iff_eq, ← wPt_val hj hl, hlk, wPt_val hi hk]⟩
  rw [hk'] at this
  exact Bool.false_ne_true this

theorem mem_wPlane_iff_mask {i : ℕ} (hi : i < 891) {p : Fin 693} :
    p ∈ wPlane i ↔ (maskArr[i]!).testBit uPts[p.val]! = true := by
  have H := (allIn_eq_true.1 ((allIn_eq_true.1 uaFacts.mask) i (Nat.zero_le _) hi)) p.val
    (Nat.zero_le _) p.2
  rw [beq_iff_eq] at H
  rw [H]
  unfold uaMem
  rw [anyIn_eq_true]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, by rw [beq_iff_eq, wPt_val hi hk]⟩
  · rintro ⟨k, hk, he⟩
    exact ⟨k, hk, Fin.ext (by rw [wPt_val hi hk]; exact beq_iff_eq.1 he)⟩

theorem ncard_wPlane {i : ℕ} (hi : i < 891) : (wPlane i).ncard = 21 := by
  have : wPlane i = (fun k : Fin 21 => wPt i k.val) '' Set.univ := by
    ext p
    simp only [mem_wPlane, Set.image_univ, Set.mem_range]
    exact ⟨fun ⟨k, hk, e⟩ => ⟨⟨k, hk⟩, e⟩, fun ⟨k, e⟩ => ⟨k.val, k.2, e⟩⟩
  rw [this, Set.ncard_image_of_injective _ fun k l h => Fin.ext (wPt_inj hi k.2 l.2 h),
    Set.ncard_univ, Nat.card_fin]

end Facts

end CFSG.LargeExtraspecial.SMod20
