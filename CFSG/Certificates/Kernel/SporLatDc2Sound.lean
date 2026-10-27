module

public import CFSG.Certificates.Kernel.SporLatDc2Lev2

public section

namespace CFSG.KC.SLD2

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.E64F
open MulAction

namespace Dc2SoundCtx

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)] (P : Dc2SoundCtx Γ n)

theorem itW_eq {w : List ℕ} (hw : ∀ l ∈ w, l < P.C.nl) (e : ℕ) :
    ∀ p < n, itW P.C.L w e p = act n (P.elt w ^ e) p := by
  induction e with
  | zero =>
    intro p hp
    rw [itW, pow_zero, act_one hp]
  | succ e ih =>
    intro p hp
    obtain ⟨h1, h2⟩ := P.act_wordF w hw p hp
    rw [itW, ih _ h2, ← h1, pow_succ, act_mul _ _ hp]

theorem witW_lt {r : List ℕ} (hr : ∀ l ∈ r, l < P.C.nl) {ss : List (List ℕ)}
    (hs : ∀ s ∈ ss, ∀ l ∈ s, l < P.C.nl) : ∀ l ∈ witW r ss, l < P.C.nl := by
  induction ss with
  | nil =>
    intro l hl
    simp [witW] at hl
  | cons s t ih =>
    intro l hl
    rw [witW, List.mem_append, List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · exact hr l hl
    · exact hs s List.mem_cons_self l hl
    · exact ih (fun s' hs' => hs s' (List.mem_cons_of_mem _ hs')) l hl

theorem elt_witW_mem {K : Subgroup Γ} {r : List ℕ} (hr : P.elt r ∈ K) {ss : List (List ℕ)}
    (hs : ∀ s ∈ ss, P.elt s ∈ K) : P.elt (witW r ss) ∈ K := by
  induction ss with
  | nil =>
    rw [witW, P.elt_nil]
    exact K.one_mem
  | cons s t ih =>
    rw [witW, P.elt_append, P.elt_append]
    exact K.mul_mem (K.mul_mem hr (hs s List.mem_cons_self))
      (ih fun s' hs' => hs s' (List.mem_cons_of_mem _ hs'))

theorem root_wit {t : Root} (ht : t ∈ P.D.roots.flatten) (hc : t.c < P.D.R1.length) :
    (P.D.R1.getD t.c default).u ++ t.φ = [] ∨ ((∀ s ∈ t.s, ∀ l ∈ s, l < P.C.ns) ∧
      3 ∣ orderOf (P.elt (witW ((P.D.R1.getD t.c default).u ++ t.φ) t.s))) := by
  obtain ⟨hφ, -, hw⟩ := P.root_facts ht
  have hu := (P.rec1_facts (P.parts.2.2.1 _ hc)).1
  unfold witOK at hw
  rw [Bool.or_eq_true] at hw
  rcases hw with h0 | hw
  · exact Or.inl (List.isEmpty_iff.1 h0)
  right
  simp only [Bool.and_eq_true] at hw
  obtain ⟨⟨⟨⟨hs, hp⟩, hl⟩, h1⟩, h2⟩ := hw
  have hs' : ∀ s ∈ t.s, ∀ l ∈ s, l < P.C.ns := fun s hs1 =>
    (isS_iff P.C).1 (List.all_eq_true.1 hs s hs1)
  rw [Nat.blt_eq, P.hn] at hp
  rw [Nat.beq_eq] at hl h1
  have hr : ∀ l ∈ (P.D.R1.getD t.c default).u ++ t.φ, l < P.C.nl := by
    intro l hl'
    rcases List.mem_append.1 hl' with hl' | hl'
    · exact hu l hl'
    · exact lt_of_lt_of_le (hφ l hl') P.nf_le
  have hw := P.witW_lt hr fun s hs1 l hl' =>
    lt_of_lt_of_le (hs' s hs1 l hl') (le_trans P.ns_le P.nf_le)
  have h2' : itW P.C.L (witW ((P.D.R1.getD t.c default).u ++ t.φ) t.s) (t.l / 3) t.p ≠ t.p := by
    intro e
    have h2'' : (!Nat.beq (itW P.C.L (witW ((P.D.R1.getD t.c default).u ++ t.φ) t.s) (t.l / 3)
      t.p) t.p) = true := h2
    rw [e, Nat.beq_refl] at h2''
    exact absurd h2'' (by decide)
  refine ⟨hs', three_dvd_orderOf (P.elt _) ⟨t.p, hp⟩ (Nat.dvd_of_mod_eq_zero hl) ?_ ?_⟩
  · apply Fin.ext
    rw [act_val hp, ← P.itW_eq hw _ _ hp]
    exact h1
  · intro e
    apply h2'
    rw [P.itW_eq hw _ _ hp, ← act_val hp, e]

end Dc2SoundCtx

theorem dc2Check_sound {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]
    (C : Dc2Ctx) (hn : C.n = n) (D : Dc2Data) (els : List Γ) (hel : els.length = C.nl)
    (hL : ∀ l < C.nl, Good n (tab n (els.getD l 1)).toArray (C.L l))
    (hk : Nat.card (Subgroup.closure {x | x ∈ els.take C.ns}) = 2 ^ C.k)
    (hN : Nat.card Γ = C.N1 * C.N2 * 2 ^ C.k)
    (hsep : ∀ g : Γ, (∀ p ∈ D.sep, act n g p = p) → g = 1)
    (h : dc2Check C D = true) :
    ∀ Z : Subgroup Γ, Subgroup.closure {x | x ∈ els.take C.ns} ≤ Z →
      Z = Subgroup.closure {x | x ∈ els.take C.ns} ∨ 3 ∣ Nat.card Z := by
  intro Z hSZ
  let P : Dc2SoundCtx Γ n := ⟨C, hn, D, els, hel, hL, hk, hN, hsep, h⟩
  have hSZ' : P.S ≤ Z := hSZ
  by_cases hZ : Z = P.S
  · exact Or.inl hZ
  right
  obtain ⟨g, hgZ, hgS⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hSZ' (Ne.symm hZ))
  obtain ⟨t, ht, htc, s₁, hs₁, s₂, hs₂, rfl⟩ := P.cover g
  rcases P.root_wit ht htc with hr | ⟨hss, h3⟩
  · rw [hr, P.elt_nil, mul_one] at hgS
    exact absurd (P.S.mul_mem hs₁ hs₂) hgS
  · have hrZ : P.elt ((D.R1.getD t.c default).u ++ t.φ) ∈ Z := by
      have e : P.elt ((D.R1.getD t.c default).u ++ t.φ) =
          s₁⁻¹ * (s₁ * P.elt ((D.R1.getD t.c default).u ++ t.φ) * s₂) * s₂⁻¹ := by
        group
      rw [e]
      exact Z.mul_mem (Z.mul_mem (Z.inv_mem (hSZ' hs₁)) hgZ) (Z.inv_mem (hSZ' hs₂))
    have hwZ := P.elt_witW_mem hrZ fun s hs => hSZ' (P.elt_mem_S (hss s hs))
    exact h3.trans (Subgroup.orderOf_dvd_natCard Z hwZ)

end CFSG.KC.SLD2

end
