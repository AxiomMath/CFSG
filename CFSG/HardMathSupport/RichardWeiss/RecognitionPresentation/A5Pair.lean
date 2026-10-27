module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.A5Clique
public import CFSG.HardMathSupport.RichardWeiss.Proving.ConjugateGenerator
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.Setup

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

open CFSG.CGT.PushingUpLit.CGT6 CFSG.ComponentClassification.PresentationLocal

section Generic

variable {J : Type*} [Group J]

theorem card_closure_pair_le_twelve {p q : J} (hp : p ^ 3 = 1) (hq : q ^ 3 = 1)
    (h : (p * q) ^ 2 = 1) :
    Finite (Subgroup.closure ({p, q} : Set J)) ∧ Nat.card (Subgroup.closure ({p, q} : Set J)) ≤ 12 := by
  have key := finite_closure_and_card_le_of_carmichael (G := J) 2 ![p, q]
    (by intro i; fin_cases i <;> simpa) (by
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · simpa using h
      · simpa using sq_comm_eq_one h
      · exact absurd rfl hij)
  have hrange : Set.range (![p, q] : Fin 2 → J) = {p, q} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rw [hrange] at key
  exact ⟨key.1, by simpa [Nat.factorial] using key.2⟩

theorem closure_pair_comm {p q : J} (h : p * q = q * p) {a b : J}
    (ha : a ∈ Subgroup.closure ({p, q} : Set J)) (hb : b ∈ Subgroup.closure ({p, q} : Set J)) :
    a * b = b * a := by
  have hs : ∀ x ∈ ({p, q} : Set J), ∀ y ∈ ({p, q} : Set J), y * x = x * y := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact h.symm
    · exact h
    · rfl
  have h1 : ∀ k ∈ Subgroup.closure ({p, q} : Set J), ∀ x ∈ ({p, q} : Set J), x * k = k * x := by
    intro k hk x hx
    have : Subgroup.closure ({p, q} : Set J) ≤ Subgroup.centralizer ({x} : Set J) := by
      rw [Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]; exact (hs x hx y hy).symm
    have := this hk
    rw [Subgroup.mem_centralizer_iff] at this
    exact this x rfl
  have h2 : Subgroup.closure ({p, q} : Set J) ≤ Subgroup.centralizer ({a} : Set J) := by
    rw [Subgroup.closure_le]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]; exact (h1 a ha y hy).symm
  have := h2 hb
  rw [Subgroup.mem_centralizer_iff] at this
  exact this a rfl

theorem alt_five_not_comm : ∃ u v : alternatingGroup (Fin 5), u * v ≠ v * u := by decide +kernel

end Generic

variable {S : Type} [Group S] [Finite S] [DecidableEq S]

omit [DecidableEq S] in
theorem exists_aalt_of_pairGen_iso {Y : Subgroup S} (hY : Nat.card Y = 3)
    (hpair : ∀ g h : S, IsZ3E9A4A5 ↥(pairGen Y g h)) {g h : S}
    (e : ↥(pairGen Y g h) ≃* alternatingGroup (Fin 5)) :
    ∃ p q : S, IsDGen Y p ∧ IsDGen Y q ∧ AAlt p q := by
  have hD := orderThreeClass_isDGen hY hpair
  obtain ⟨a, ha3, hag⟩ := CFSG.HardMathSupport.RichardWeiss.Proving.exists_gen_map_conj hY g
  obtain ⟨b, hb3, hbh⟩ := CFSG.HardMathSupport.RichardWeiss.Proving.exists_gen_map_conj hY h
  have hDa : IsDGen Y a := ⟨g, hag.symm⟩
  have hDb : IsDGen Y b := ⟨h, hbh.symm⟩
  refine ⟨a, b, hDa, hDb, ?_⟩
  have hK60 : Nat.card ↥(pairGen Y g h) = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hKle : ∀ L : Subgroup S, a ∈ L → b ∈ L → pairGen Y g h ≤ L := by
    intro L haL hbL
    rw [pairGen, Subgroup.closure_le]
    rintro x (hx | hx)
    · rw [SetLike.mem_coe, hag] at hx
      exact (Subgroup.zpowers_le.2 haL) hx
    · rw [SetLike.mem_coe, hbh] at hx
      exact (Subgroup.zpowers_le.2 hbL) hx
  have hcard_le : ∀ L : Subgroup S, a ∈ L → b ∈ L → Nat.card L < 60 → False := by
    intro L haL hbL hL
    have := Subgroup.card_le_of_le (hKle L haL hbL)
    omega
  have hz : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, ha3]
  rcases hD.pair a b hDa hDb with h1 | h1 | h1 | h1 | h1 | h1
  · exfalso
    refine hcard_le (Subgroup.zpowers a) (Subgroup.mem_zpowers a) ?_ (by omega)
    rw [eq_inv_of_mul_eq_one_right h1]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a)
  · exfalso
    refine hcard_le (Subgroup.zpowers a) (Subgroup.mem_zpowers a) ?_ (by omega)
    rw [← mul_inv_eq_one.1 h1]
    exact Subgroup.mem_zpowers a
  · exfalso
    obtain ⟨u, v, huv⟩ := alt_five_not_comm
    have hcomm : ∀ x y : ↥(pairGen Y g h), x * y = y * x := by
      intro x y
      have hle : pairGen Y g h ≤ Subgroup.closure ({a, b} : Set S) :=
        hKle _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
      exact Subtype.ext (closure_pair_comm h1 (hle x.2) (hle y.2))
    apply huv
    have := congrArg e (hcomm (e.symm u) (e.symm v))
    simpa using this
  · exfalso
    obtain ⟨hfin, hcard⟩ := card_closure_pair_le_twelve (hD.cube a hDa) (hD.cube b hDb) h1
    exact hcard_le (Subgroup.closure ({a, b} : Set S)) (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)) (by omega)
  · exfalso
    have hDbi : IsDGen Y b⁻¹ := hDb.inv
    obtain ⟨hfin, hcard⟩ := card_closure_pair_le_twelve (hD.cube a hDa) (hD.cube _ hDbi) h1
    have hbmem : b ∈ Subgroup.closure ({a, b⁻¹} : Set S) := by
      have : b⁻¹ ∈ Subgroup.closure ({a, b⁻¹} : Set S) := Subgroup.subset_closure (by simp)
      simpa using Subgroup.inv_mem _ this
    exact hcard_le (Subgroup.closure ({a, b⁻¹} : Set S)) (Subgroup.subset_closure (by simp))
      hbmem (by omega)
  · exact h1

theorem exists_clique_three_of_pairGen_iso {Y : Subgroup S} (hY : Nat.card Y = 3)
    (hpair : ∀ g h : S, IsZ3E9A4A5 ↥(pairGen Y g h)) {g h : S}
    (e : ↥(pairGen Y g h) ≃* alternatingGroup (Fin 5)) :
    ∃ F : Finset S, IsClique (IsDGen Y) F ∧ 3 ≤ F.card := by
  obtain ⟨p, q, hp, hq, hA⟩ := exists_aalt_of_pairGen_iso hY hpair e
  exact exists_clique_three_of_aalt (orderThreeClass_isDGen hY hpair) hp hq hA

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

end
