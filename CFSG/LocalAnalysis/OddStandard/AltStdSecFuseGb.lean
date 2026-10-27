module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseFb

public section

namespace CFSG.OddStandard.AltStdSec.SylowSn

@[expose] def Gb (a : ℕ) : Set (W a) := {x | x * x = 1 ∧ fixW a x = 2}

theorem Gb_sq {a : ℕ} {x : W a} (hx : x ∈ Gb a) : x * x = 1 := hx.1

theorem mem_Gb {a : ℕ} {x : W a} : x ∈ Gb a ↔ x * x = 1 ∧ fixW a x = 2 := Iff.rfl

theorem disjoint_Fb_Gb (a : ℕ) : Disjoint (Fb a) (Gb a) := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  have h1 : fixW a x = 0 := hx.2
  have h2 : fixW a x = 2 := hx'.2
  omega

theorem Gb_conj {a : ℕ} (g : W a) {x : W a} (hx : x ∈ Gb a) : g * x * g⁻¹ ∈ Gb a := by
  refine ⟨?_, by rw [fixW_conj]; exact hx.2⟩
  have h : g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
  rw [h, hx.1]
  group

theorem Gb_one : Gb 1 = {1} := by
  ext x
  obtain ⟨u, v, q, rfl⟩ : ∃ (u v : W 0) (q : Z2), x = wr u v q := ⟨_, _, _, (wr_eta x).symm⟩
  obtain rfl : u = 1 := Subsingleton.elim _ _
  obtain rfl : v = 1 := Subsingleton.elim _ _
  constructor
  · intro hx
    rcases z2_cases q with rfl | rfl
    · exact Set.mem_singleton_iff.2 wr_one
    · have h : fixW (0 + 1) (wr (1 : W 0) 1 z2) = 2 := hx.2
      rw [fixW_wr] at h
      simp [z2_ne_one] at h
  · intro hx
    have hx' : (wr (1 : W 0) 1 q : W 0 ≀ᵣ Z2) = 1 := Set.mem_singleton_iff.1 hx
    refine ⟨?_, ?_⟩
    · show (wr (1 : W 0) 1 q : W 0 ≀ᵣ Z2) * wr 1 1 q = 1
      rw [hx']
      exact one_mul 1
    · show fixW (0 + 1) (wr (1 : W 0) 1 q) = 2
      rw [hx']
      exact fixW_one 1

theorem mem_Gb_wr (a : ℕ) (ha : 1 ≤ a) (u v : W a) (q : Z2) :
    wr u v q ∈ Gb (a + 1) ↔ q = 1 ∧ ((u ∈ Gb a ∧ v ∈ Fb a) ∨ (u ∈ Fb a ∧ v ∈ Gb a)) := by
  show (wr u v q : W a ≀ᵣ Z2) * wr u v q = 1 ∧ fixW (a + 1) (wr u v q) = 2 ↔ _
  rcases z2_cases q with rfl | rfl
  · rw [wr_mul_one, ← wr_one, wr_inj, fixW_wr]
    obtain ⟨k, hk⟩ := fixW_even a ha u
    obtain ⟨l, hl⟩ := fixW_even a ha v
    simp only [mem_Gb, mem_Fb, ite_true, true_and, and_true]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rcases (by omega : (fixW a u = 2 ∧ fixW a v = 0) ∨ (fixW a u = 0 ∧ fixW a v = 2)) with
        ⟨h4, h5⟩ | ⟨h4, h5⟩
      · exact Or.inl ⟨⟨h1, h4⟩, h2, h5⟩
      · exact Or.inr ⟨⟨h1, h4⟩, h2, h5⟩
    · rintro (⟨⟨h1, h4⟩, h2, h5⟩ | ⟨⟨h1, h4⟩, h2, h5⟩)
      · exact ⟨⟨h1, h2⟩, by omega⟩
      · exact ⟨⟨h1, h2⟩, by omega⟩
  · rw [wr_mul_z2, z2_mul_self, ← wr_one, wr_inj, fixW_wr]
    simp [z2_ne_one]

theorem card_Gb_succ (a : ℕ) (ha : 1 ≤ a) :
    Nat.card (Gb (a + 1)) = 2 * Nat.card (Fb a) * Nat.card (Gb a) := by
  let f : (Gb a × Fb a) ⊕ (Fb a × Gb a) → Gb (a + 1) :=
    Sum.elim
      (fun p => ⟨wr p.1.1 p.2.1 1, (mem_Gb_wr a ha _ _ _).2 ⟨rfl, Or.inl ⟨p.1.2, p.2.2⟩⟩⟩)
      (fun p => ⟨wr p.1.1 p.2.1 1, (mem_Gb_wr a ha _ _ _).2 ⟨rfl, Or.inr ⟨p.1.2, p.2.2⟩⟩⟩)
  have hinj : Function.Injective f := by
    rintro (⟨u, v⟩ | ⟨u, v⟩) (⟨u', v'⟩ | ⟨u', v'⟩) hh
    · have h1 : (wr u.1 v.1 1 : W a ≀ᵣ Z2) = wr u'.1 v'.1 1 := congrArg Subtype.val hh
      obtain ⟨h2, h3, -⟩ := wr_inj.1 h1
      rw [Subtype.ext h2, Subtype.ext h3]
    · have h1 : (wr u.1 v.1 1 : W a ≀ᵣ Z2) = wr u'.1 v'.1 1 := congrArg Subtype.val hh
      obtain ⟨h2, -, -⟩ := wr_inj.1 h1
      exact absurd (h2 ▸ u.2) (Set.disjoint_left.1 (disjoint_Fb_Gb a) u'.2)
    · have h1 : (wr u.1 v.1 1 : W a ≀ᵣ Z2) = wr u'.1 v'.1 1 := congrArg Subtype.val hh
      obtain ⟨h2, -, -⟩ := wr_inj.1 h1
      exact absurd (h2 ▸ u'.2) (Set.disjoint_left.1 (disjoint_Fb_Gb a) u.2)
    · have h1 : (wr u.1 v.1 1 : W a ≀ᵣ Z2) = wr u'.1 v'.1 1 := congrArg Subtype.val hh
      obtain ⟨h2, h3, -⟩ := wr_inj.1 h1
      rw [Subtype.ext h2, Subtype.ext h3]
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨u, v, q, rfl⟩ : ∃ (u v : W a) (q : Z2), y = wr u v q := ⟨_, _, _, (wr_eta y).symm⟩
    obtain ⟨rfl, h | h⟩ := (mem_Gb_wr a ha u v q).1 hy
    · exact ⟨Sum.inl (⟨u, h.1⟩, ⟨v, h.2⟩), rfl⟩
    · exact ⟨Sum.inr (⟨u, h.1⟩, ⟨v, h.2⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_sum, Nat.card_prod,
    Nat.card_prod]
  ring

end CFSG.OddStandard.AltStdSec.SylowSn
