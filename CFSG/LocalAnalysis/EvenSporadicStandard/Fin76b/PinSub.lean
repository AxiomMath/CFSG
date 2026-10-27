module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.PinModel

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem PinModel.of_sub_table {M : Type*} [Group M] {K S : Subgroup M} (hSK : S ≤ K)
    (hS2 : IsPGroup 2 S) (hodd : ∃ m : ℕ, Odd m ∧ Nat.card K = Nat.card S * m) {t : M}
    (ht2 : t * t = 1) (ht1 : t ≠ 1) (htS : t ∈ S) (htc : ∀ x ∈ S, x * t = t * x)
    (hcen : ∀ y ∈ S, (∀ x ∈ S, x * y = y * x) → y = 1 ∨ y = t)
    (n : ℕ) (elt : ℕ → M) (mul : ℕ → ℕ → ℕ) (tI : ℕ)
    (hmemT : ∀ a < n, elt a ∈ S) (hsurj : ∀ x ∈ S, ∃ a < n, elt a = x)
    (hinj : ∀ a b, a < n → b < n → elt a = elt b → a = b)
    (hmul : ∀ a b, a < n → b < n → mul a b < n ∧ elt a * elt b = elt (mul a b))
    (h0 : elt 0 = 1) (htI : tI < n ∧ elt tI = t) (hn : 0 < n)
    (hcheck : TablePin.pinCheck n mul tI = true) :
    ∃ (T E : Subgroup K) (t' : K), PinModel K T E t' := by
  classical
  obtain ⟨m, hm, hcard⟩ := hodd
  have htK : t ∈ K := hSK htS
  have hmem : ∀ x : K, x ∈ S.subgroupOf K ↔ (x : M) ∈ S := fun x => mem_subgroupOf
  let elt' : ℕ → ↥K := fun a => if h : a < n then ⟨elt a, hSK (hmemT a h)⟩ else 1
  have helt' : ∀ a < n, ((elt' a : ↥K) : M) = elt a := fun a ha => by simp [elt', ha]
  have htc' : ∀ x ∈ S.subgroupOf K, x * (⟨t, htK⟩ : K) = ⟨t, htK⟩ * x := fun x hx =>
    Subtype.ext (htc x ((hmem x).1 hx))
  have hspec : TablePin.TableSpec (S.subgroupOf K) (⟨t, htK⟩ : K) n elt' mul tI :=
    { memT := fun a ha => (hmem _).2 (by rw [helt' a ha]; exact hmemT a ha)
      surj := fun x hx => by
        obtain ⟨a, ha, hax⟩ := hsurj (x : M) ((hmem x).1 hx)
        exact ⟨a, ha, Subtype.ext (by rw [helt' a ha]; exact hax)⟩
      inj := fun a b ha hb h => hinj a b ha hb (by rw [← helt' a ha, ← helt' b hb, h])
      mul_spec := fun a b ha hb => by
        obtain ⟨h1, h2⟩ := hmul a b ha hb
        refine ⟨h1, Subtype.ext ?_⟩
        rw [Subgroup.coe_mul, helt' a ha, helt' b hb, helt' _ h1]
        exact h2
      zero := Subtype.ext (by rw [helt' 0 hn, Subgroup.coe_one]; exact h0)
      tI_lt := htI.1
      tI_elt := Subtype.ext (by rw [helt' _ htI.1]; exact htI.2)
      pos := hn }
  refine ⟨S.subgroupOf K, _, ⟨t, htK⟩, PinModel.of_table hspec hcheck hS2.comap_subtype
    ⟨m, hm, ?_⟩ (Subtype.ext ht2) (fun h => ht1 (congrArg Subtype.val h)) htc' ?_⟩
  · rw [Nat.card_congr (subgroupOfEquivOfLe hSK).toEquiv]
    exact hcard
  · intro y hy hc
    have h1 : (y : M) = 1 ∨ (y : M) = t := hcen y ((hmem y).1 hy) fun x hx =>
      congrArg Subtype.val (hc ⟨x, hSK hx⟩ ((hmem _).2 hx))
    rcases h1 with h1 | h1
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Subtype.ext h1)

end CFSG.EvenSporadicStandard.Fin76b
