module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup MulAction

variable {G : Type*} [Group G]

@[expose] def conjCommSet (a b : G) : Set G := {x | IsConj a x ∧ Commute x b}

theorem conjCommSet_conj (a b g : G) :
    (fun x => g * x * g⁻¹) '' conjCommSet a b = conjCommSet a (g * b * g⁻¹) := by
  ext y
  constructor
  · rintro ⟨x, ⟨hax, hxb⟩, rfl⟩
    refine ⟨hax.trans (isConj_iff.2 ⟨g, rfl⟩), ?_⟩
    simp only [Commute, SemiconjBy] at hxb ⊢
    calc g * x * g⁻¹ * (g * b * g⁻¹) = g * (x * b) * g⁻¹ := by group
      _ = g * (b * x) * g⁻¹ := by rw [hxb]
      _ = g * b * g⁻¹ * (g * x * g⁻¹) := by group
  · rintro ⟨hay, hyb⟩
    refine ⟨g⁻¹ * y * g, ⟨hay.trans (isConj_iff.2 ⟨g⁻¹, by group⟩), ?_⟩, by group⟩
    simp only [Commute, SemiconjBy] at hyb ⊢
    calc g⁻¹ * y * g * b = g⁻¹ * (y * (g * b * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * b * g⁻¹) * y) * g := by rw [hyb]
      _ = b * (g⁻¹ * y * g) := by group

theorem ncard_conjCommSet_of_isConj [Finite G] (a : G) {b y : G} (h : IsConj b y) :
    (conjCommSet a y).ncard = (conjCommSet a b).ncard := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 h
  rw [← conjCommSet_conj]
  exact Set.ncard_image_of_injective _ (fun x y h => by simpa using h)

open Classical in
theorem card_filter_commute_eq [Fintype G] (a b : G) (A : Finset G)
    (hA : ∀ x, x ∈ A ↔ IsConj a x) {y : G} (hy : IsConj b y) :
    (A.filter fun x => Commute x y).card = (conjCommSet a b).ncard := by
  rw [← ncard_conjCommSet_of_isConj a hy, ← Set.ncard_coe_finset]
  congr 1
  ext x
  simp [conjCommSet, hA]

theorem ncard_conjCommSet_mul [Finite G] (a b : G) :
    (conjCommSet a b).ncard * {y : G | IsConj b y}.ncard =
      (conjCommSet b a).ncard * {x : G | IsConj a x}.ncard := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set A : Finset G := Finset.univ.filter fun x => IsConj a x with hAdef
  set B : Finset G := Finset.univ.filter fun y => IsConj b y with hBdef
  have hA : ∀ x, x ∈ A ↔ IsConj a x := by simp [A]
  have hB : ∀ y, y ∈ B ↔ IsConj b y := by simp [B]
  have hAc : {x : G | IsConj a x}.ncard = A.card := by
    rw [← Set.ncard_coe_finset]; congr 1; ext x; simp [hA]
  have hBc : {y : G | IsConj b y}.ncard = B.card := by
    rw [← Set.ncard_coe_finset]; congr 1; ext x; simp [hB]
  let P : Finset (G × G) := (A ×ˢ B).filter fun p => Commute p.1 p.2
  have h1 : P.card = ∑ y ∈ B, (A.filter fun x => Commute x y).card := by
    simp only [P, Finset.card_filter, Finset.sum_product_right]
  have h2 : P.card = ∑ x ∈ A, (B.filter fun y => Commute x y).card := by
    simp only [P, Finset.card_filter, Finset.sum_product]
  have h1' : P.card = B.card * (conjCommSet a b).ncard := by
    rw [h1, Finset.sum_congr rfl fun y hy => card_filter_commute_eq a b A hA ((hB y).1 hy),
      Finset.sum_const, smul_eq_mul]
  have h2' : P.card = A.card * (conjCommSet b a).ncard := by
    rw [h2, Finset.sum_congr rfl fun x hx => ?_, Finset.sum_const, smul_eq_mul]
    have : (B.filter fun y => Commute x y) = (B.filter fun y => Commute y x) := by
      ext y; simp [Commute.symm_iff]
    rw [this]
    exact card_filter_commute_eq b a B hB ((hA x).1 hx)
  rw [hAc, hBc]
  linarith [h1', h2']

theorem ncard_isConj_mul_card_centralizer [Finite G] (a : G) :
    {x : G | IsConj a x}.ncard * Nat.card (centralizer ({a} : Set G)) = Nat.card G := by
  have h1 : {x : G | IsConj a x} = orbit (ConjAct G) a := by
    ext x
    rw [ConjAct.mem_orbit_conjAct]
    exact isConj_comm
  have h2 : Nat.card (centralizer ({a} : Set G)) = Nat.card (stabilizer (ConjAct G) a) := by
    refine Nat.card_congr (Equiv.subtypeEquiv ConjAct.toConjAct.toEquiv fun x => ?_)
    rw [mem_centralizer_singleton_iff, MulAction.mem_stabilizer_iff]
    change x * a = a * x ↔ ConjAct.toConjAct x • a = a
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
    constructor
    · intro h
      rw [h]
      group
    · intro h
      calc x * a = x * a * x⁻¹ * x := by group
        _ = a * x := by rw [h]
  rw [h1, h2, ← MulAction.index_stabilizer, Subgroup.index_mul_card]
  exact Nat.card_congr ConjAct.toConjAct.symm.toEquiv

theorem ncard_conjCommSet_mul_card_centralizer [Finite G] (a b : G) :
    (conjCommSet a b).ncard * Nat.card (centralizer ({a} : Set G)) =
      (conjCommSet b a).ncard * Nat.card (centralizer ({b} : Set G)) := by
  have hG : 0 < Nat.card G := Nat.card_pos
  have h := ncard_conjCommSet_mul a b
  have ha := ncard_isConj_mul_card_centralizer a
  have hb := ncard_isConj_mul_card_centralizer b
  apply Nat.eq_of_mul_eq_mul_left hG
  calc Nat.card G * ((conjCommSet a b).ncard * Nat.card (centralizer ({a} : Set G)))
      = ((conjCommSet a b).ncard * {y : G | IsConj b y}.ncard) *
          (Nat.card (centralizer ({a} : Set G)) * Nat.card (centralizer ({b} : Set G))) := by
        rw [← hb]; ring
    _ = ((conjCommSet b a).ncard * {x : G | IsConj a x}.ncard) *
          (Nat.card (centralizer ({a} : Set G)) * Nat.card (centralizer ({b} : Set G))) := by
        rw [h]
    _ = Nat.card G * ((conjCommSet b a).ncard * Nat.card (centralizer ({b} : Set G))) := by
        rw [← ha]; ring

theorem exists_mem_normalizer_not_mem {p : ℕ} [Fact p.Prime] [Finite G] {V Q : Subgroup G}
    (hQ : IsPGroup p Q) (hlt : V < Q) :
    ∃ g ∈ Q, g ∉ V ∧ g ∈ normalizer (V : Set G) := by
  have : Group.IsNilpotent Q := hQ.isNilpotent
  have htop : V.subgroupOf Q < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    obtain ⟨q, hqQ, hqV⟩ := IsConcreteLE.exists_of_lt hlt
    apply hqV
    have : (⟨q, hqQ⟩ : Q) ∈ V.subgroupOf Q := by rw [h]; exact mem_top _
    exact this
  obtain ⟨⟨g, hgQ⟩, hgN, hgV⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ htop)
  refine ⟨g, hgQ, hgV, ?_⟩
  rw [mem_normalizer_iff]
  intro h
  by_cases hh : h ∈ Q
  · have := (mem_normalizer_iff.1 hgN) ⟨h, hh⟩
    simpa [mem_subgroupOf] using this
  · have h1 : h ∉ V := fun hv => hh (hlt.le hv)
    have h2 : g * h * g⁻¹ ∉ V := by
      intro hv
      apply hh
      have : g⁻¹ * (g * h * g⁻¹) * g ∈ Q :=
        Q.mul_mem (Q.mul_mem (Q.inv_mem hgQ) (hlt.le hv)) hgQ
      simpa [mul_assoc] using this
    exact iff_of_false h1 h2

theorem eq_of_isPGroup_of_centralizer {p : ℕ} [Fact p.Prime] [Finite G] {V : Subgroup G}
    {S : Set G} (hVS : ∀ v ∈ S, V ≤ centralizer ({v} : Set G))
    (hmax : ∀ v ∈ S, ∀ Q : Subgroup G, IsPGroup p Q → V ≤ Q → Q ≤ centralizer ({v} : Set G) →
      Q = V)
    (hN : ∀ g ∈ normalizer (V : Set G), IsPGroup p (zpowers g) → ∃ v ∈ S, Commute g v)
    {Q : Subgroup G} (hQ : IsPGroup p Q) (hVQ : V ≤ Q) : Q = V := by
  by_contra hne
  obtain ⟨g, hgQ, hgV, hgN⟩ :=
    exists_mem_normalizer_not_mem hQ (lt_of_le_of_ne hVQ (Ne.symm hne))
  have hgp : IsPGroup p (zpowers g) := hQ.to_le ((zpowers_le).2 hgQ)
  obtain ⟨v, hvS, hgv⟩ := hN g hgN hgp
  have hle : V ⊔ zpowers g ≤ Q := sup_le hVQ ((zpowers_le).2 hgQ)
  have hC : V ⊔ zpowers g ≤ centralizer ({v} : Set G) :=
    sup_le (hVS v hvS) ((zpowers_le).2 (mem_centralizer_singleton_iff.2 hgv.eq))
  have := hmax v hvS (V ⊔ zpowers g) (hQ.to_le hle) le_sup_left hC
  exact hgV (this ▸ (le_sup_right : zpowers g ≤ V ⊔ zpowers g) (mem_zpowers g))

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
