module

public import CFSG.GH74.Filter.Statements
public import CFSG.GH74.Filter.Witness
public import CFSG.LieType.Ree.SuzukiUnipotentStructure

public section

namespace CFSG.GH74.Filter.Lie

open CFSG.Blueprint CFSG.LieType.Ree

theorem multiplicative_field_facts {K : Type} [Field K] [Finite K] (h2 : (2 : K) = 0) {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 5 ≤ n) :
    (∀ a b : Multiplicative K, a * b = b * a) ∧ (∀ a : Multiplicative K, a ^ 2 = 1) ∧
      2 ^ 4 < Nat.card (Multiplicative K) := by
  refine ⟨fun a b => mul_comm a b, fun a => ?_, ?_⟩
  · apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul]
    calc Multiplicative.toAdd a + Multiplicative.toAdd a = 2 * Multiplicative.toAdd a := by ring
      _ = 0 := by rw [h2, zero_mul]
  · rw [show Nat.card (Multiplicative K) = Nat.card K from Nat.card_congr Multiplicative.toAdd, hK]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)

@[expose] def additiveFamilyHom {K G : Type*} [AddCommGroup K] [Group G] (S : K → G) (h0 : S 0 = 1)
    (hmul : ∀ v w, S v * S w = S (v + w)) : Multiplicative K →* G where
  toFun x := S (Multiplicative.toAdd x)
  map_one' := by simpa using h0
  map_mul' x y := by simpa using (hmul (Multiplicative.toAdd x) (Multiplicative.toAdd y)).symm

theorem additiveFamilyHom_injective {K G : Type*} [AddCommGroup K] [Group G] (S : K → G)
    (h0 : S 0 = 1) (hmul : ∀ v w, S v * S w = S (v + w)) (hinj : Function.Injective S) :
    Function.Injective (additiveFamilyHom S h0 hmul) := fun _ _ h =>
  Multiplicative.toAdd.injective (hinj h)

end CFSG.GH74.Filter.Lie

namespace CFSG.GH74.Filter

open CFSG.GH74.Filter.Lie
open CFSG.Blueprint CFSG.LieType.Ree

theorem t_suzuki_large : S_suzuki_large := by
  rintro G _ _ p f hf ⟨rfl, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩
  obtain ⟨h2, -⟩ := suzuki_frob_data a hK
  let S : K → suzukiGroup a K := fun v => suzukiSElt a K 0 v
  have h0 : S 0 = 1 := suzukiSElt_zero_zero hK
  have hmul : ∀ v w, S v * S w = S (v + w) := fun v w => by
    simp only [S]
    rw [suzukiSElt_mul hK]
    congr 1 <;> simp
  have hinj : Function.Injective S := fun v w h => (suzukiSElt_inj.1 h).2
  obtain ⟨hc, hs, hcard⟩ := multiplicative_field_facts h2 hK hf
  exact not_gen4_of_mulEquiv e.symm (not_gen4_of_injective (additiveFamilyHom S h0 hmul)
    (additiveFamilyHom_injective S h0 hmul hinj) hc hs hcard)

end CFSG.GH74.Filter
