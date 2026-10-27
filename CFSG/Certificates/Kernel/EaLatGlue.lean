module

public import CFSG.Certificates.Kernel.EaLatBits

public section

namespace CFSG.KC.EaLat

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos

variable {G : Type*} [Group G] [DecidableEq G]

@[expose] def TagOK (M : ℕ → ℕ → ℕ) (one n : ℕ) (V E TG : ℕ → ℕ) (e : ℕ) : Prop :=
  (TG e < n ∧ E e = V (TG e)) ∨ (E e = one ∨ M (E e) (E e) ≠ one)

theorem ea_of_checks [Finite G] {enc : G → ℕ} {M : ℕ → ℕ → ℕ} {one : ℕ}
    (henc : ClosEnc enc M one) (gens : List G) {Gc : ℕ → ℕ} {N : ℕ} {E PA SG CT : ℕ → ℕ}
    (hG : ∀ j < gens.length, Gc j = enc (gens.getD j 1)) (hN : 0 < N)
    (ht : ∀ k < N, treeAt M one Gc gens.length E PA k = true)
    (hs : ∀ i < N, sortAt N E SG i = true)
    (hcl : ∀ k < N, closedAt M Gc gens.length N E CT k = true)
    {n NF : ℕ} (hn : n ≤ 255) (hNF : 0 < NF) (v : ℕ → G) {V CM PR REC CH TG : ℕ → ℕ}
    {ncw : ℕ → ℕ → ℕ → Bool} (hV : ∀ i < n, enc (v i) = V i) {W : ℕ}
    (hncw : ∀ x y : G, ∀ w < W, ncw (enc x) (enc y) w = true → x * y ≠ y * x)
    (hW : ∀ i < n, ∀ j < i, bit (CM i) j = false → prb PR i j < W)
    (htag : ∀ e < N, TagOK M one n V E TG e)
    (hu : ∀ i < n, uniAt M one n V CM PR ncw i = true)
    (hb : baseOK n REC = true) (hg : ∀ f, 0 < f → f < NF → genAt n REC CM PR f = true)
    (hc : ∀ f < NF, covAt NF REC CH f = true) :
    Nat.card (Subgroup.closure {g | g ∈ gens}) = N ∧
      ∀ K : Subgroup G, K ≤ Subgroup.closure {g | g ∈ gens} →
        (∀ x ∈ K, ∀ y ∈ K, x * y = y * x) → (∀ x ∈ K, x * x = 1) →
        ∃ f < NF, ∀ x, x ∈ K ↔ x = 1 ∨ ∃ i ∈ recS REC f, v i = x := by
  obtain ⟨-, -, hcl'⟩ := clos_card henc gens hG hN ht hs
  obtain ⟨hcard, hall⟩ := hcl' hcl
  obtain ⟨huni, hcm⟩ := uni_of_checks hn henc v hV hncw hW hu
  have hr := recs_of_checks hn v hcm hb hg hc
  refine ⟨hcard, fun K hKT hcomm hsq => ea_complete huni hr hNF _ ?_ K hKT hcomm hsq⟩
  intro s hsT hss hs1
  obtain ⟨k, hk, hsk⟩ := hall s hsT
  rcases htag k hk with ⟨htn, hte⟩ | hno
  · refine ⟨TG k, htn, henc.inj ?_⟩
    rw [hV _ htn, hsk, hte]
  · exfalso
    rcases hno with h1 | h2
    · exact hs1 (henc.inj (by rw [hsk, h1, henc.enc_one]))
    · exact h2 (by rw [← hsk, ← henc.enc_mul, hss, henc.enc_one])

end CFSG.KC.EaLat

end
