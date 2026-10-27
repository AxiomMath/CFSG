module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3GJComp
public import CFSG.HardMathSupport.Solomon.Coordinator.L3GJDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma511Ns

theorem layerStatement_congr {G : Type} [Group G] [Finite G] (B : Subgroup G) {J J' : Subgroup G}
    (h : J = J') :
    (3 ∣ Nat.card ↥J ∧ ∀ (y : G) (hy : y ∈ J), y ∈ B → y ≠ 1 →
        HasOrderThreeLift (barOf 3 J) (QuotientGroup.mk (⟨y, hy⟩ : ↥J))) ↔
      (3 ∣ Nat.card ↥J' ∧ ∀ (y : G) (hy : y ∈ J'), y ∈ B → y ≠ 1 →
        HasOrderThreeLift (barOf 3 J') (QuotientGroup.mk (⟨y, hy⟩ : ↥J'))) := by
  subst h
  exact Iff.rfl

theorem gapJStructure_of_lift (hlift : Lemma510iiLift) : Gap_JStructure := by
  intro G _ _ m hS hC B hB b hb hb1 L hLU hty A hA hbA hfld
  have hAB : A ≤ B := hA.1
  have hAel : IsElemAbelian 3 A := hA.2.1
  have hAc : Nat.card A = 9 := by simpa using hA.2.2
  have hBel : IsElemAbelian 3 B := hB.1.1
  have hbl : b ^ 3 = 1 := hAel.2 b hbA
  have hbz : Nat.card (Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hbl hb1]
  obtain ⟨a, haA, hab⟩ : ∃ a ∈ A, a ∉ Subgroup.zpowers b := by
    by_contra hno
    push Not at hno
    have h1 : A ≤ Subgroup.zpowers b := fun a ha => hno a ha
    have := Subgroup.card_le_of_le h1
    omega
  have ha3 : a ^ 3 = 1 := hAel.2 a haA
  have ha1 : a ≠ 1 := fun h => hab (h ▸ Subgroup.one_mem _)
  have haz : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
  have hba : b ∉ Subgroup.zpowers a := by
    intro hba
    have hle : Subgroup.zpowers b ≤ Subgroup.zpowers a := Subgroup.zpowers_le.2 hba
    have heq : Subgroup.zpowers b = Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [haz, hbz])
    exact hab (heq ▸ Subgroup.mem_zpowers a)
  have hcomm : ∀ h ∈ Subgroup.zpowers a, h * b = b * h := by
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have := elemAbelian_comm hAel haA (hbA : b ∈ A)
    exact (Commute.zpow_left (show Commute a b from this) k).eq
  have hcard := card_sup_zpowers_of_pow_three_eq_one (H := Subgroup.zpowers a) hbl hba hcomm
  have hsupA : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ A :=
    sup_le (Subgroup.zpowers_le.2 haA) (Subgroup.zpowers_le.2 hbA)
  have hAeq : Subgroup.zpowers a ⊔ Subgroup.zpowers b = A :=
    Subgroup.eq_of_le_of_card_ge hsupA (by rw [hcard, haz, hAc])
  have hbL : L ≤ Subgroup.centralizer ({b} : Set G) := hLU.1.1
  have hCeq : L ⊓ Subgroup.centralizer (A : Set G) = L ⊓ Subgroup.centralizer ({a} : Set G) := by
    ext l
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hlL, hlA⟩
      exact ⟨hlL, Subgroup.centralizer_le (Set.singleton_subset_iff.2 haA) hlA⟩
    · rintro ⟨hlL, hla⟩
      refine ⟨hlL, ?_⟩
      have hla' : a ∈ Subgroup.centralizer ({l} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hla ⊢
        exact hla.symm
      have hlb : b ∈ Subgroup.centralizer ({l} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.1 (hbL hlL)).symm
      have hAl : A ≤ Subgroup.centralizer ({l} : Set G) :=
        hAeq ▸ sup_le (Subgroup.zpowers_le.2 hla') (Subgroup.zpowers_le.2 hlb)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact Subgroup.mem_centralizer_singleton_iff.1 (hAl hh)
  obtain ⟨haN, hafld⟩ := hfld a haA
  obtain ⟨J₁, hJeq, hJ₁, hSc, hO, h3d⟩ := exists_layer_data hLU.1 hty haN ha3 hafld
  have hJ' : GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G)) = J₁.map L.subtype := by
    rw [hCeq]
    exact hJeq
  refine (layerStatement_congr B hJ').2 ⟨three_dvd_card_layer hO h3d, ?_⟩
  intro y hy hyB hy1
  have hy' := hy
  obtain ⟨j, hj, rfl⟩ := hy'
  have hyL : (j : G) ∈ L := j.2
  exact layer_lift_core hLU.1 haN ha3 hafld hSc hO j hj (hBel.2 _ hyB) hy1
    (hlift G m hS hC B hB b hb hb1 L hLU hty _ hyL hyB hy1)

end CFSG.HardMathSupport.Solomon.Coordinator
