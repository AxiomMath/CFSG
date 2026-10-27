module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Goldschmidt.Steps.G310TypeID
public import CFSG.Holt.Induced
public import CFSG.CharacterTheory.Burnside
public import CFSG.LocalAnalysis.EvenBN.Tits.N.Generic
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Norm

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits.N

variable {Γ : Type*} [Group Γ]

theorem mem_normalizer_of_maxElemAbelian2 [Finite Γ] {K W : Subgroup Γ}
    (hmax : maxElemAbelian2 K = {W}) {k : Γ} (hk : k ∈ K) : k ∈ normalizer (W : Set Γ) := by
  have hW : W ∈ maxElemAbelian2 K := by rw [hmax]; rfl
  obtain ⟨hWK, hWab, hWmax⟩ := hW
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : W.map (MulAut.conj k).toMonoidHom ≤ K := by
    rintro _ ⟨w, hw, rfl⟩
    exact mul_mem (mul_mem hk (hWK hw)) (Subgroup.inv_mem _ hk)
  have hel : IsElemAbelian 2 (W.map (MulAut.conj k).toMonoidHom) := hWab.map _
  have hcard : Nat.card (W.map (MulAut.conj k).toMonoidHom) = Nat.card W :=
    Subgroup.card_map_of_injective (MulAut.conj k).injective
  have hmem : W.map (MulAut.conj k).toMonoidHom ∈ maxElemAbelian2 K :=
    ⟨hle, hel, fun D hD hDab => (hWmax D hD hDab).trans hcard.ge⟩
  rw [hmax] at hmem
  exact hmem

theorem le_of_fusionIsSylowIn_of_normalizes {H P Q : Subgroup Γ} (hQ : fusionIsSylowIn 2 Q H)
    (hP : IsPGroup 2 P) (hPH : P ≤ H) (hn : Q ≤ normalizer (P : Set Γ)) : P ≤ Q := by
  have hsup : IsPGroup 2 (P ⊔ Q : Subgroup Γ) := hP.to_sup_of_normal_left' hQ.2.1 hn
  have hEq : P ⊔ Q = Q := hQ.2.2 _ (sup_le hPH hQ.1) hsup le_sup_right
  exact hEq ▸ le_sup_left

theorem normalizer_zpowers_of_commute {g t : Γ} (h : g * t = t * g) :
    g ∈ normalizer ((zpowers t : Subgroup Γ) : Set Γ) := by
  refine Subgroup.centralizer_le_normalizer ((zpowers t : Subgroup Γ) : Set Γ)
    (mem_centralizer_iff.2 ?_)
  rintro a ⟨n, rfl⟩
  exact (Commute.zpow_left (show Commute t g from h.symm) n).eq

theorem fusionIsSylowIn_imgIn [Finite Γ] (V : Subgroup Γ) {S L : Subgroup Γ}
    (hS : fusionIsSylowIn 2 S L) (hL : L ≤ normalizer (V : Set Γ)) :
    fusionIsSylowIn 2 (imgIn V S) (imgIn V L) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := CFSG.Goldschmidt.G310.fusionIsSylowIn_subgroupOf hS hL
  exact CFSG.Holt.fusionIsSylowIn_map (conjActHom V) h1

theorem fpf_of_commutator [Finite Γ] {W₀ W : Subgroup Γ} {x : Γ} (hW₀ : IsPGroup 2 W₀)
    (hx5 : x ^ 5 = 1) (hx1 : x ≠ 1) (hxN : x ∈ normalizer (W₀ : Set Γ))
    (hW : W = ⁅W₀, zpowers x⁆) (hWab : IsElemAbelian 2 W) :
    ∀ w ∈ W, x * w * x⁻¹ = w → w = 1 := by
  intro w hw hxw
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hord : orderOf x = 5 := orderOf_eq_prime hx5 hx1
  have hX : IsPGroup 5 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  have hXP : zpowers x ≤ normalizer (W₀ : Set Γ) := zpowers_le.2 hxN
  have hab : IsMulCommutative (⁅W₀, zpowers x⁆ : Subgroup Γ) := by
    rw [← hW]; exact hWab.1
  have h0 := centralizer_commutator_eq_bot (p := 2) (r := 5) (by norm_num) hW₀ hX hXP hab
  have hwW : w ∈ (⁅W₀, zpowers x⁆ : Subgroup Γ) := by rw [← hW]; exact hw
  have hwC : w ∈ centralizer ((zpowers x : Subgroup Γ) : Set Γ) := by
    rw [mem_centralizer_iff]
    rintro a ⟨n, rfl⟩
    have hc : Commute x w := by
      have : x * w = w * x := by
        calc x * w = (x * w * x⁻¹) * x := by group
          _ = w * x := by rw [hxw]
      exact this
    exact (hc.zpow_left n).eq
  have hmem : w ∈ (⁅W₀, zpowers x⁆ : Subgroup Γ) ⊓ centralizer ((zpowers x : Subgroup Γ) : Set Γ) :=
    ⟨hwW, hwC⟩
  rw [h0] at hmem
  exact mem_bot.1 hmem

theorem isSolvable_of_card_dvd_two_pow_mul_five {X : Type*} [Group X] [Finite X] {a : ℕ}
    (h : Nat.card X ∣ 2 ^ a * 5) : Group.IsSolvable X := by
  obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := Nat.dvd_mul.1 h
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk₁
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 (by simpa using hk₂ : k₂ ∣ 5 ^ 1)
  have : Fintype X := Fintype.ofFinite X
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_five (by norm_num) (by rw [← Nat.card_eq_fintype_card, ← hk])

theorem le_centralizer_of_isElemAbelian {W : Subgroup Γ} (h : IsElemAbelian 2 W) :
    W ≤ centralizer (W : Set Γ) := fun w hw =>
  mem_centralizer_iff.2 fun v hv => h.comm hv hw

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
