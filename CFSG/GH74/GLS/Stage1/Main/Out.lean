module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Defs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Defs
public import CFSG.GH74.GLS.Stage2.Local.Ctx0

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm3.Sec7
  CFSG.GH74.GLS.Stage1.Thm3.Sec8

theorem card_statedSL_two' (F : Type) [Field F] [Finite F] :
    Nat.card (StatedSL 2 F) = Nat.card F * (Nat.card F ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_statedSL_two F

theorem factorization_two_mul_sq_sub_one (q : ℕ) (h : q % 8 = 3 ∨ q % 8 = 5) :
    (q * (q ^ 2 - 1)).factorization 2 = 3 := by
  obtain ⟨m, hm, hq⟩ : ∃ m, Odd m ∧ q * (q ^ 2 - 1) = 8 * m := by
    rcases h with h | h
    · obtain ⟨k, rfl⟩ : ∃ k, q = 8 * k + 3 := ⟨q / 8, by omega⟩
      have e : (8 * k + 3) ^ 2 - 1 = 8 * ((2 * k + 1) * (4 * k + 1)) := by
        have : (8 * k + 3) ^ 2 = 64 * k ^ 2 + 48 * k + 9 := by ring
        have h2 : 8 * ((2 * k + 1) * (4 * k + 1)) = 64 * k ^ 2 + 48 * k + 8 := by ring
        omega
      refine ⟨(8 * k + 3) * ((2 * k + 1) * (4 * k + 1)), ?_, ?_⟩
      · have o1 : Odd (8 * k + 3) := ⟨4 * k + 1, by ring⟩
        have o2 : Odd (2 * k + 1) := ⟨k, rfl⟩
        have o3 : Odd (4 * k + 1) := ⟨2 * k, by ring⟩
        exact o1.mul (o2.mul o3)
      · rw [e]; ring
    · obtain ⟨k, rfl⟩ : ∃ k, q = 8 * k + 5 := ⟨q / 8, by omega⟩
      have e : (8 * k + 5) ^ 2 - 1 = 8 * ((2 * k + 1) * (4 * k + 3)) := by
        have : (8 * k + 5) ^ 2 = 64 * k ^ 2 + 80 * k + 25 := by ring
        have h2 : 8 * ((2 * k + 1) * (4 * k + 3)) = 64 * k ^ 2 + 80 * k + 24 := by ring
        omega
      refine ⟨(8 * k + 5) * ((2 * k + 1) * (4 * k + 3)), ?_, ?_⟩
      · have o1 : Odd (8 * k + 5) := ⟨4 * k + 2, by ring⟩
        have o2 : Odd (2 * k + 1) := ⟨k, rfl⟩
        have o3 : Odd (4 * k + 3) := ⟨2 * k + 1, by ring⟩
        exact o1.mul (o2.mul o3)
      · rw [e]; ring
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [hq, Nat.factorization_mul (by norm_num) hm0]
  have h8 : (Nat.factorization 8) 2 = 3 := by
    have : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [this, Nat.Prime.factorization_pow Nat.prime_two]; simp
  have : m.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by
    intro hd; exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hd))
  simp [this, h8]

@[expose] def G2Term (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧
    (∃ (Gs : Type) (_ : Group Gs) (_ : Finite Gs), LieModel Gs .G2 0 p f ∧
      ∃ S' : Sylow 2 Gs, Nonempty (↥S ≃* ↥(S' : Subgroup Gs))) ∧
    (∀ v : G, orderOf v = 2 → IsConj z v) ∧
    HasSL2ProductOfIndexTwoCh6 (oPrimeResidual 2 (CentralizerBar z)) (p ^ f)

theorem G2Term.of_G2TermType {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (h : G2TermType G z S) : G2Term G z S := by
  obtain ⟨q, ⟨Gs, i1, i2, p, f, hp, hp2, hpf, hL, S', hS⟩, hone, hsl⟩ := h
  obtain ⟨F₁, F₂, f1, f2, fin1, fin2, hodd1, hodd2, hle, hF₂q, h5, hfac, K, hK, hidx, hcp⟩ := hsl
  refine ⟨p, f, hp, hp2, ⟨Gs, i1, i2, hL, S', hS⟩, hone, ?_⟩
  refine ⟨F₂, F₁, F₂, f2, f1, f2, fin2, fin1, fin2, ?_, hodd1, hodd2, hle, h5, hfac, rfl, K, hK, hidx, hcp⟩
  rw [hF₂q, hpf]

theorem G2Term.of_G2Concl {G : Type} [Group G] [Finite G] {z : G} {S K : Subgroup G}
    (h : G2Concl G z S K) : G2Term G z S := by
  obtain ⟨q, hq8, hq5, -, -, -, ⟨Gs, i1, i2, p, f, hp, hp2, hpf, hL, S', hS⟩, hone, hsl⟩ := h
  obtain ⟨F₁, F₂, f1, f2, fin1, fin2, hodd1, hodd2, hle, hF₂, h5, hfac, K, hK, hidx, hcp⟩ := hsl
  have : Fact p.Prime := ⟨hp⟩
  have hf : f ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hpf
    omega
  have hcardF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hF3 : (Nat.card ↥(StatedSL 2 F₂)).factorization 2 = 3 := by
    rw [card_statedSL_two', hF₂]
    exact factorization_two_mul_sq_sub_one 3 (Or.inl rfl)
  have hFq : (Nat.card ↥(StatedSL 2 (GaloisField p f))).factorization 2 = 3 := by
    rw [card_statedSL_two', hcardF, hpf]
    exact factorization_two_mul_sq_sub_one q hq8
  refine ⟨p, f, hp, hp2, ⟨Gs, i1, i2, hL, S', hS⟩, hone, ?_⟩
  refine ⟨GaloisField p f, F₁, F₂, inferInstance, f1, f2, inferInstance, fin1, fin2, hcardF, hodd1,
    hodd2, hle, h5, ?_, ?_, K, hK, hidx, hcp⟩
  · rw [hfac, hF3, hFq]
  · rw [hF3, hFq]

@[expose] def Term7Out (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (q : ℕ) (w : G) : Prop :=
  ∃ K₁ K₂ : Subgroup G, Std4 G z S K₁ K₂ ∧ Odd q ∧ 5 ≤ q ∧ HatSL2 K₁ q ∧ HatSL2 K₂ q ∧
    Term7 z S K₁ K₂ q w

@[expose] def L4U4TermTypeE (ε : Bool) (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) : Prop :=
  (∀ v : G, orderOf v = 2 → IsConj z v) ∧
  ∃ (Gs : Type) (_ : Group Gs) (_ : Finite Gs) (p f : ℕ), p.Prime ∧ p ≠ 2 ∧
    ((ε = true ∧ p ^ f % 8 = 5 ∧ LieModel Gs .PSL 4 p f) ∨
      (ε = false ∧ p ^ f % 8 = 3 ∧ 3 < p ^ f ∧ LieModel Gs .PSU 4 p f)) ∧
    (∃ S' : Sylow 2 Gs, Nonempty (↥S ≃* ↥(S' : Subgroup Gs))) ∧
    ∀ (z' : Gs) (S' : Sylow 2 ↥(centralizer ({z'} : Set Gs))), IsCentralInvolution z' →
      ∀ S'' : Sylow 2 Gs, Nonempty (↥S ≃* ↥(S'' : Subgroup Gs)) →
        (S'' : Subgroup Gs) = (S' : Subgroup ↥(centralizer ({z'} : Set Gs))).map
            (centralizer ({z'} : Set Gs)).subtype →
          Nonempty (↥(Stage1.Thm3.Sec8.layerSBar z S) ≃* ↥(Stage1.Thm3.Sec8.layerSBar z' (S'' : Subgroup Gs)))

theorem L4U4TermTypeE.toTermType {ε : Bool} {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (h : L4U4TermTypeE ε G z S) : L4U4TermType G z S := by
  obtain ⟨hone, Gs, _, _, p, f, hp, hp2, hm, hS, hC⟩ := h
  refine ⟨hone, Gs, ‹_›, ‹_›, p, f, hp, hp2, ?_, hS, hC⟩
  rcases hm with ⟨_, h8, hL⟩ | ⟨_, h8, h3, hL⟩
  · exact Or.inl ⟨h8, hL⟩
  · exact Or.inr ⟨h8, h3, hL⟩

theorem L4U4TermType.exists_eps {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (h : L4U4TermType G z S) : ∃ ε : Bool, L4U4TermTypeE ε G z S := by
  obtain ⟨hone, Gs, _, _, p, f, hp, hp2, hm, hS, hC⟩ := h
  rcases hm with ⟨h8, hL⟩ | ⟨h8, h3, hL⟩
  · exact ⟨true, hone, Gs, ‹_›, ‹_›, p, f, hp, hp2, Or.inl ⟨rfl, h8, hL⟩, hS, hC⟩
  · exact ⟨false, hone, Gs, ‹_›, ‹_›, p, f, hp, hp2, Or.inr ⟨rfl, h8, h3, hL⟩, hS, hC⟩

@[expose] def L4U4TermTypeQ (ε : Bool) (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (q : ℕ) :
    Prop :=
  L4U4TermTypeE ε G z S ∧
    ∃ (Gs : Type) (_ : Group Gs) (_ : Finite Gs) (p f : ℕ), p.Prime ∧ p ≠ 2 ∧ p ^ f = q ∧
      ((ε = true ∧ LieModel Gs .PSL 4 p f) ∨ (ε = false ∧ LieModel Gs .PSU 4 p f)) ∧
      (∃ S' : Sylow 2 Gs, Nonempty (↥S ≃* ↥(S' : Subgroup Gs))) ∧
      ∀ (z' : Gs) (S'c : Sylow 2 ↥(centralizer ({z'} : Set Gs))), IsCentralInvolution z' →
        ∀ S'' : Sylow 2 Gs, Nonempty (↥S ≃* ↥(S'' : Subgroup Gs)) →
          (S'' : Subgroup Gs) = (S'c : Subgroup ↥(centralizer ({z'} : Set Gs))).map
              (centralizer ({z'} : Set Gs)).subtype →
            Nonempty (↥(Stage1.Thm3.Sec8.layerSBar z S) ≃* ↥(Stage1.Thm3.Sec8.layerSBar z' (S'' : Subgroup Gs)))

theorem layerSBar_eq_sup {G : Type} [Group G] (z : G) (S : Subgroup G) :
    Stage1.Thm3.Sec8.layerSBar z S = layer (CentralizerBar z) ⊔ barOf z S := rfl

inductive Stage1Out (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) : Kind → Prop
  | g2 (h : Stage2Ctx0 G z Kind.g2 S) (t : G2Term G z S) : Stage1Out G z S Kind.g2
  | m12 (h : Stage2Ctx0 G z Kind.m12 S) : Stage1Out G z S Kind.m12
  | psp4 (h : Stage2Ctx0 G z Kind.psp4 S) (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z))
      (hq : Stage1PSp4 G z S q L₁ L₂) (ht : Term7Out G z S q 1) : Stage1Out G z S Kind.psp4
  | l4NF (ε : Bool) (h : Stage2Ctx0 G z (Kind.l4 ε) S) (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z))
      (hq : Stage1L4 G z S ε q L₁ L₂) (hq4 : q % 4 = (if ε then 3 else 1)) (w : G) (hw : w ≠ 1)
      (ht : Term7Out G z S q w) : Stage1Out G z S (Kind.l4 ε)
  | l4F (ε : Bool) (h : Stage2Ctx0 G z (Kind.l4 ε) S) (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z))
      (hq : Stage1L4 G z S ε q L₁ L₂) (ht : L4U4TermTypeQ ε G z S q) : Stage1Out G z S (Kind.l4 ε)
  | mcl (h : Stage2Ctx0 G z Kind.mcl S) : Stage1Out G z S Kind.mcl
  | ly (h : Stage2Ctx0 G z Kind.ly S) : Stage1Out G z S Kind.ly

theorem Stage1Out.ctx {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {k : Kind}
    (h : Stage1Out G z S k) : Stage2Ctx0 G z k S := by
  cases h with
  | g2 h _ => exact h
  | m12 h => exact h
  | psp4 h _ _ _ _ _ => exact h
  | l4NF _ h _ _ _ _ _ _ _ _ => exact h
  | l4F _ h _ _ _ _ _ => exact h
  | mcl h => exact h
  | ly h => exact h

theorem Stage1Out.ctxStd {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {k : Kind}
    (h : Stage1Out G z S k) (hs : Std G) : Stage2Ctx G z k S :=
  h.ctx.toCtx' hs

end CFSG.GH74.GLS.Stage1.Main
