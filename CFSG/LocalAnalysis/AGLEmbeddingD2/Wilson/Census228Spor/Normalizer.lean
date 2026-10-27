module

public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofThreeFive

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census228Spor

open Subgroup CFSG.RankThree.PartTwo.Sec21

theorem card_inf_normalizer_le_four_mul {X : Type*} [Group X] [Finite X] (C : Subgroup X)
    {k : X} (hk : orderOf k = 5) :
    Nat.card (C ⊓ normalizer ((zpowers k : Subgroup X) : Set X) : Subgroup X) ≤
      4 * Nat.card (C ⊓ centralizer ({k} : Set X) : Subgroup X) := by
  classical
  set N : Subgroup X := C ⊓ normalizer ((zpowers k : Subgroup X) : Set X) with hN
  set Cc : Subgroup X := C ⊓ centralizer ({k} : Set X) with hCc
  have hcomm : ∀ g ∈ centralizer ({k} : Set X), Commute g k := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mp hg
  have hk1 : k ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hk
    omega
  have hle : Cc ≤ N := by
    intro g hg
    refine ⟨hg.1, ?_⟩
    show g ∈ normalizer ((zpowers k : Subgroup X) : Set X)
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ n : ℤ, g * k ^ n * g⁻¹ = k ^ n := fun n => by
      have : Commute g (k ^ n) := Commute.zpow_right (hcomm g hg.2) n
      rw [this.eq]; group
    have key' : ∀ n : ℤ, g⁻¹ * k ^ n * g = k ^ n := fun n => by
      have : Commute g⁻¹ (k ^ n) := Commute.zpow_right ((hcomm g hg.2).inv_left) n
      rw [this.eq]; group
    intro h
    constructor
    · intro hh
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      rw [key]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers k) n
    · intro hh
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hh
      have : h = g⁻¹ * (g * h * g⁻¹) * g := by group
      rw [this, ← hn, key']
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers k) n
  have hmem : ∀ g : N, (g : X) * k * (g : X)⁻¹ ∈ zpowers k := fun g => by
    have := (Subgroup.mem_normalizer_iff.mp g.2.2 k).mp (Subgroup.mem_zpowers k)
    exact this
  set s : Subgroup N := Cc.subgroupOf N with hs
  have hscard : Nat.card s = Nat.card Cc :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  let f : N ⧸ s → {y : zpowers k // y ≠ 1} :=
    Quotient.lift (fun g : N => (⟨⟨(g : X) * k * (g : X)⁻¹, hmem g⟩, fun h => hk1 (by
      have := congrArg Subtype.val h
      simp only [Subgroup.coe_one] at this
      have h2 : (g : X) * k * (g : X)⁻¹ = 1 := this
      simpa using h2)⟩ : {y : zpowers k // y ≠ 1})) (by
      intro a b hab
      have hab' : a⁻¹ * b ∈ s := (QuotientGroup.leftRel_apply).mp hab
      have hc : ((a⁻¹ * b : N) : X) ∈ centralizer ({k} : Set X) :=
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hab')).2
      have hcm : Commute ((a⁻¹ * b : N) : X) k := hcomm _ hc
      apply Subtype.ext
      apply Subtype.ext
      show (a : X) * k * (a : X)⁻¹ = (b : X) * k * (b : X)⁻¹
      have h1 : (a : X)⁻¹ * (b : X) * k = k * ((a : X)⁻¹ * (b : X)) := hcm.eq
      have h2 : ((a : X)⁻¹ * (b : X)) * k * ((a : X)⁻¹ * (b : X))⁻¹ = k := by
        rw [h1]; group
      calc (a : X) * k * (a : X)⁻¹
          = (a : X) * (((a : X)⁻¹ * (b : X)) * k * ((a : X)⁻¹ * (b : X))⁻¹) * (a : X)⁻¹ := by
            rw [h2]
        _ = (b : X) * k * (b : X)⁻¹ := by group)
  have hfinj : Function.Injective f := by
    intro q1 q2
    induction q1 using Quotient.inductionOn with
    | h a =>
    induction q2 using Quotient.inductionOn with
    | h b =>
    intro hab
    have h3 : (a : X) * k * (a : X)⁻¹ = (b : X) * k * (b : X)⁻¹ :=
      congrArg (fun y : {y : zpowers k // y ≠ 1} => (y.1 : X)) hab
    apply Quotient.sound
    apply (QuotientGroup.leftRel_apply).mpr
    refine Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩
    · exact C.mul_mem (C.inv_mem a.2.1) b.2.1
    · show (((a⁻¹ * b : N)) : X) ∈ centralizer ({k} : Set X)
      rw [Subgroup.mem_centralizer_singleton_iff]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      refine Eq.symm ?_
      have : k = (a : X)⁻¹ * (b : X) * k * ((b : X)⁻¹ * (a : X)) := by
        calc k = (a : X)⁻¹ * ((a : X) * k * (a : X)⁻¹) * (a : X) := by group
          _ = (a : X)⁻¹ * ((b : X) * k * (b : X)⁻¹) * (a : X) := by rw [h3]
          _ = _ := by group
      calc k * ((a : X)⁻¹ * (b : X))
          = ((a : X)⁻¹ * (b : X) * k * ((b : X)⁻¹ * (a : X))) * ((a : X)⁻¹ * (b : X)) := by
            rw [← this]
        _ = (a : X)⁻¹ * (b : X) * k := by group
  have hcard4 : Nat.card {y : zpowers k // y ≠ 1} = 4 := by
    have : Fintype (zpowers k) := Fintype.ofFinite _
    have h5 : Fintype.card (zpowers k) = 5 := by
      rw [← Nat.card_eq_fintype_card, Nat.card_zpowers, hk]
    have h1 : Fintype.card {y : zpowers k // y = 1} = 1 := by
      rw [Fintype.card_subtype_eq]
    rw [Nat.card_eq_fintype_card]
    have := Fintype.card_subtype_compl (fun y : zpowers k => y = 1)
    simp only [h5, h1] at this
    convert this using 1
  have hq : Nat.card (N ⧸ s) ≤ 4 := hcard4 ▸ Nat.card_le_card_of_injective f hfinj
  calc Nat.card N = Nat.card (N ⧸ s) * Nat.card s := Subgroup.card_eq_card_quotient_mul_card_subgroup s
    _ ≤ 4 * Nat.card Cc := by rw [hscard]; exact Nat.mul_le_mul_right _ hq


theorem threeFiveData228_of_centralizer_cards {X : Type} [Group X] [Finite X] {a m : ℕ}
    (h3 : ∀ x : X, orderOf x = 3 → Nat.card (centralizer ({x} : Set X)) = a ∨
      ¬ 5 ∣ Nat.card (centralizer ({x} : Set X)))
    (h5 : ∀ k : X, orderOf k = 5 → Nat.card (centralizer ({k} : Set X)) ∣ m)
    (hlt : 72 * Nat.gcd m a < a) : ThreeFiveData228 X := by
  intro x k hx hk hxk
  have hkC : k ∈ centralizer ({x} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxk.symm
  have h5C : 5 ∣ Nat.card (centralizer ({x} : Set X)) := by
    have := orderOf_dvd_natCard (⟨k, hkC⟩ : centralizer ({x} : Set X))
    rwa [Subgroup.orderOf_mk, hk] at this
  have hxa : Nat.card (centralizer ({x} : Set X)) = a := by
    rcases h3 x hx with h | h
    · exact h
    · exact absurd h5C h
  have hle := card_inf_normalizer_le_four_mul (centralizer ({x} : Set X)) hk
  have hdvd1 : Nat.card (centralizer ({x} : Set X) ⊓ centralizer ({k} : Set X) : Subgroup X) ∣
      m := (Subgroup.card_dvd_of_le inf_le_right).trans (h5 k hk)
  have hdvd2 : Nat.card (centralizer ({x} : Set X) ⊓ centralizer ({k} : Set X) : Subgroup X) ∣
      a := hxa ▸ Subgroup.card_dvd_of_le inf_le_left
  have hg : Nat.card (centralizer ({x} : Set X) ⊓ centralizer ({k} : Set X) : Subgroup X) ≤
      Nat.gcd m a := by
    refine Nat.le_of_dvd ?_ (Nat.dvd_gcd hdvd1 hdvd2)
    exact Nat.gcd_pos_of_pos_right _ (hxa ▸ Nat.card_pos)
  rw [hxa]
  omega

end CFSG.AGLEmbeddingD2.Wilson.Census228Spor
