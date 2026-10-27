module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9CG

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat

open CFSG Subgroup

@[expose] def ExactResidueOutcome (S : Type) [Group S] : Prop :=
  Blueprint.LieModel S .PSU 3 5 1 ∨ Blueprint.LieModel S .PSp 2 5 1 ∨
  Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .J2)

@[expose] def IsSectionOf (Q S : Type) [Group Q] [Group S] : Prop :=
  ∃ (H : Subgroup S) (φ : ↥H →* Q), Function.Surjective φ

theorem IsSectionOf.card_dvd {Q S : Type} [Group Q] [Group S] [Finite S] (h : IsSectionOf Q S) :
    Nat.card Q ∣ Nat.card S := by
  obtain ⟨H, φ, hφ⟩ := h
  exact (Subgroup.card_dvd_of_surjective hφ).trans (Subgroup.card_subgroup_dvd_card H)

@[expose] def U45NoA9Section : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Blueprint.LieModel S .PSU 4 5 1 →
    ¬ IsSectionOf (alternatingGroup (Fin 9)) S

end CFSG.ComponentClassification.SolMax.FiveCat

namespace CFSG.ComponentClassification.SolMax.SwapP2

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

structure ExactData (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (F : Subgroup X) (DF : Finset (Fin n))
    (f : X) (L N : Subgroup X) : Prop where
  FJ : F ≤ J
  Fk : Nonempty (F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
  DFc : DF.card = 4
  Fs : ∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
    ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω
  fF : f ∈ F
  f1 : f ≠ 1
  LJ : L ≤ J
  LC : L ≤ centralizer ({t} : Set X) ⊓ centralizer ({f} : Set X)
  Lpc : IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set X) ⊓ centralizer ({f} : Set X)))
  Ltype : Nonempty (↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin 5))
  NC : N ≤ centralizer ({f} : Set X)
  Npc : IsPComponent 2 (N.subgroupOf (centralizer ({f} : Set X)))
  LN : L ≤ N
  Nt : conjBy N t = N
  Nnt : L ⊔ core N ≠ N

theorem exactFivePump_iff {t : X} {J : Subgroup X} {n : ℕ}
    {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} :
    ExactFivePump t J n e ↔ ∃ (F : Subgroup X) (DF : Finset (Fin n)) (f : X) (L N : Subgroup X),
      ExactData t J n e F DF f L N := by
  constructor
  · rintro ⟨F, DF, f, L, N, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
    exact ⟨F, DF, f, L, N, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩⟩
  · rintro ⟨F, DF, f, L, N, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩⟩
    exact ⟨F, DF, f, L, N, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

section Exact

variable {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {F : Subgroup X} {DF : Finset (Fin n)}
  {f : X} {L N : Subgroup X}

theorem ExactData.orderOf_f (hx : ExactData t J n e F DF f L N) : orderOf f = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hff : f * f = 1 := by rw [← sq]; exact (card_sq_of_klein hx.Fk).2 f hx.fF
  exact orderOf_eq_prime (by rw [sq]; exact hff) hx.f1

variable [Finite X] [IsSimpleGroup X] {E : Subgroup X} {D : Finset (Fin n)} {M : Subgroup X}

theorem ExactData.t_mem_centralizer (hs : Setting t J n e E D M)
    (hx : ExactData t J n e F DF f L N) : t ∈ centralizer ({f} : Set X) :=
  mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp (hs.sig.pair.1.2.1 (hx.FJ hx.fF))).symm

end Exact

@[expose] def ExactGenerationInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Y N L : Subgroup X) (t : X), N ≤ Y →
    IsPComponent 2 (N.subgroupOf Y) → t ∈ Y → orderOf t = 2 → conjBy N t = N → L ≤ N →
    L ≤ centralizer ({t} : Set X) →
    IsPComponent 2 (L.subgroupOf (Y ⊓ centralizer ({t} : Set X))) →
    Nonempty (↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin 5)) → L ⊔ core N ≠ N →
    (∀ T' : Subgroup X, T' ≤ N → T' ≤ centralizer ({t} : Set X) →
      IsPComponent 2 (T'.subgroupOf (Y ⊓ centralizer ({t} : Set X))) → T' = L) →
    FiveCat.ExactResidueOutcome (↥N ⧸ Open.fusionZStar ↥N) →
    ∀ G : Subgroup X, G ≤ N → core N ≤ G → L ≤ G →
      (∀ u ∈ L, u * u = 1 → ∀ x ∈ N, x ∈ centralizer ({u * t} : Set X) → x ∈ G) → G = N

theorem card_alt_nine : Nat.card (alternatingGroup (Fin 9)) = 181440 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem not_dvd_alt_three_six_hundred (m : ℕ) (hm : Odd m) (h7 : 7 ≤ m) (h9 : m ≤ 9) :
    ¬ 3600 ∣ Nat.card (alternatingGroup (Fin m)) := by
  have : m = 7 ∨ m = 9 := by obtain ⟨k, hk⟩ := hm; omega
  rcases this with rfl | rfl <;> (rw [nat_card_alternatingGroup, Nat.card_fin]; decide)

end CFSG.ComponentClassification.SolMax.SwapP2
