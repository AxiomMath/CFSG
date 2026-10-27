module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroThreeMovedAux
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPTransvect
import CFSG.LocalAnalysis.AGLEmbedding.ResidualToolsAux

public section
namespace CFSG.AGLEmbedding

open CFSG.Open

variable {Y : Type} [Group Y] [Finite Y]

theorem false_of_moved_component_three {L B X₀ : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hZ3 : ∀ L' : Subgroup Y, IsComponentOf L' ⊤ → ∀ w ∈ L',
      w ∈ Subgroup.centralizer (L' : Set Y) → IsPGroup 3 (Subgroup.zpowers w) → w = 1)
    (hB : CFSG.Open.pRank 3 B ≤ 3) {x z : Y} (hxB : x ∈ B) (hx3 : x ^ 3 = 1)
    (hxL : x ∉ Subgroup.normalizer (L : Set Y)) (hzB : z ∈ B) (hz3 : z ^ 3 = 1)
    (hxz : x * z = z * x) (hzN : z ∈ Subgroup.normalizer (L : Set Y))
    (hzL : z ∉ Subgroup.centralizer (L : Set Y)) {j : Y} (hj : j ∈ L ⊓ B)
    (hzj : z * j⁻¹ ∈ Subgroup.centralizer (L : Set Y)) (hX₀B : X₀ ≤ B)
    (hX₀ : IsElemAbelian 3 X₀) (hX₀ne : X₀ ≠ ⊥) (hX₀L : X₀ ≤ Subgroup.normalizer (L : Set Y))
    (hX₀z : X₀ ≤ Subgroup.centralizer ({z} : Set Y))
    (hxX₀ : x ∈ Subgroup.normalizer (X₀ : Set Y)) (hzX₀ : z ∉ X₀) : False := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hcomp : ∀ g : Y, IsComponentOf (L.map (MulAut.conj g).toMonoidHom) ⊤ := fun g =>
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) L).mpr hL
  set L₁ := L.map (MulAut.conj x).toMonoidHom with hL₁
  set L₂ := L.map (MulAut.conj (x ^ 2)).toMonoidHom with hL₂
  have hL₁c : IsComponentOf L₁ ⊤ := hcomp x
  have hL₂c : IsComponentOf L₂ ⊤ := hcomp (x ^ 2)
  have hmm : ∀ (a b : Y) (K : Subgroup Y), K.map (MulAut.conj (a * b)).toMonoidHom =
      (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
    intro a b K
    rw [Subgroup.map_map]
    congr 1
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  have hx4 : x ^ 2 * x ^ 2 = x := by
    rw [← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_add, hx3, one_mul, pow_one]
  have h01 : L ≠ L₁ := fun h => hxL (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have h02 : L ≠ L₂ := fun h => by
    apply hxL
    have hx2 : x ^ 2 ∈ Subgroup.normalizer (L : Set Y) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm
    rw [← hx4]
    exact Subgroup.mul_mem _ hx2 hx2
  have h12 : L₁ ≠ L₂ := fun h => by
    apply h01
    have h' : (L.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).toMonoidHom =
        L.map (MulAut.conj x).toMonoidHom := by
      rw [← hmm, ← pow_two]
      exact h.symm
    exact (Subgroup.map_injective (MulAut.conj x).injective h').symm
  have hC01 := le_centralizer_of_component_ne hL hL₁c h01
  have hC02 := le_centralizer_of_component_ne hL hL₂c h02
  have hC12 := le_centralizer_of_component_ne hL₁c hL₂c h12
  set A : Subgroup Y := X₀ ⊔ Subgroup.zpowers z with hA
  have hAel : IsElemAbelian 3 A := isElemAbelian_sup_zpowers_of_le_centralizer hX₀ hX₀z hz3
  have hAB : A ≤ B := sup_le hX₀B (Subgroup.zpowers_le.mpr hzB)
  have hAL : A ≤ Subgroup.normalizer (L : Set Y) := sup_le hX₀L (Subgroup.zpowers_le.mpr hzN)
  have hzA : z ∈ A := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hxZ : x ∈ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup Y) : Set Y) := by
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    rintro _ ⟨k, rfl⟩
    exact (Commute.zpow_left (Commute.symm hxz) k).eq
  have hxNA : x ∈ Subgroup.normalizer (A : Set Y) :=
    Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hxX₀, hxZ⟩
  have hconjA : ∀ g ∈ Subgroup.normalizer (A : Set Y), ∀ c ∈ Subgroup.centralizer (A : Set Y),
      g * c * g⁻¹ ∈ Subgroup.centralizer (A : Set Y) := fun g hg c hc =>
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer hg) c).mp hc
  obtain ⟨y₀, hy₀LB, hy₀A, hzy₀, hy₀3, hy₀1⟩ :=
    exists_inner_pow_three_of_coprime (hZ3 L hL) hAel hAB hAL hzA hzL hj hzj
  set y₁ := x * y₀ * x⁻¹ with hy₁
  set y₂ := x ^ 2 * y₀ * (x ^ 2)⁻¹ with hy₂
  have hy₁L : y₁ ∈ L₁ := ⟨y₀, hy₀LB.1, rfl⟩
  have hy₂L : y₂ ∈ L₂ := ⟨y₀, hy₀LB.1, rfl⟩
  have hx2B : x ^ 2 ∈ B := B.pow_mem hxB 2
  have hy₁B : y₁ ∈ B := B.mul_mem (B.mul_mem hxB hy₀LB.2) (B.inv_mem hxB)
  have hy₂B : y₂ ∈ B := B.mul_mem (B.mul_mem hx2B hy₀LB.2) (B.inv_mem hx2B)
  have hy₁A : y₁ ∈ Subgroup.centralizer (A : Set Y) := hconjA x hxNA y₀ hy₀A
  have hy₂A : y₂ ∈ Subgroup.centralizer (A : Set Y) :=
    hconjA (x ^ 2) (Subgroup.pow_mem _ hxNA 2) y₀ hy₀A
  have hxz2 : x ^ 2 * z = z * x ^ 2 := (Commute.pow_left hxz 2).eq
  have hzy₁ : z * y₁⁻¹ ∈ Subgroup.centralizer (L₁ : Set Y) := by
    have : z * y₁⁻¹ = x * (z * y₀⁻¹) * x⁻¹ := by
      rw [hy₁]
      calc z * (x * y₀ * x⁻¹)⁻¹ = (x * z * x⁻¹) * (x * y₀ * x⁻¹)⁻¹ := by
            rw [hxz, mul_inv_cancel_right]
        _ = x * (z * y₀⁻¹) * x⁻¹ := by group
    rw [this]
    exact conj_mem_centralizer_map hzy₀
  have hzy₂ : z * y₂⁻¹ ∈ Subgroup.centralizer (L₂ : Set Y) := by
    have : z * y₂⁻¹ = x ^ 2 * (z * y₀⁻¹) * (x ^ 2)⁻¹ := by
      rw [hy₂]
      calc z * (x ^ 2 * y₀ * (x ^ 2)⁻¹)⁻¹ = (x ^ 2 * z * (x ^ 2)⁻¹) *
            (x ^ 2 * y₀ * (x ^ 2)⁻¹)⁻¹ := by rw [hxz2, mul_inv_cancel_right]
        _ = x ^ 2 * (z * y₀⁻¹) * (x ^ 2)⁻¹ := by group
    rw [this]
    exact conj_mem_centralizer_map hzy₀
  have hy₁3 : y₁ ^ 3 = 1 := by rw [hy₁, conj_pow, hy₀3, mul_one, mul_inv_cancel]
  have hy₂3 : y₂ ^ 3 = 1 := by rw [hy₂, conj_pow, hy₀3, mul_one, mul_inv_cancel]
  have hy₁1 : y₁ ≠ 1 := fun h => hy₀1 (by
    have := congrArg (fun g => x⁻¹ * g * x) h
    simpa [hy₁, mul_assoc] using this)
  have hy₂1 : y₂ ≠ 1 := fun h => hy₀1 (by
    have := congrArg (fun g => (x ^ 2)⁻¹ * g * x ^ 2) h
    simpa [hy₂, mul_assoc] using this)
  have hzc0 : Commute z y₀ := Subgroup.mem_centralizer_iff.mp hy₀A z hzA
  have hzc1 : Commute z y₁ := Subgroup.mem_centralizer_iff.mp hy₁A z hzA
  have hzc2 : Commute z y₂ := Subgroup.mem_centralizer_iff.mp hy₂A z hzA
  have hc01 : Commute y₀ y₁ := (Subgroup.mem_centralizer_iff.mp (hC01 hy₀LB.1) y₁ hy₁L).symm
  have hc02 : Commute y₀ y₂ := (Subgroup.mem_centralizer_iff.mp (hC02 hy₀LB.1) y₂ hy₂L).symm
  have hc12 : Commute y₁ y₂ := (Subgroup.mem_centralizer_iff.mp (hC12 hy₁L) y₂ hy₂L).symm
  have hzeq : z = y₀ * y₁ * y₂ := eq_mul_mul_of_three_components hZ3 hL hL₁c hL₂c h01 h02 h12
    hB hy₀LB.1 hy₁L hy₂L hy₀LB.2 hy₁B hy₂B hzB hy₀3 hy₁3 hy₂3 hy₀1 hy₁1 hy₂1 hz3 hzc0 hzc1
    hzc2 hzy₀ hzy₁ hzy₂
  have hX₀W := le_sup_zpowers_of_three_components hZ3 hL hL₁c hL₂c h01 h02 h12 hB hy₀LB.1
    hy₁L hy₂L hy₀LB.2 hy₁B hy₂B hy₀3 hy₁3 hy₂3 hy₀1 hy₁1 hy₂1 hX₀B hX₀.2 fun w hw =>
      ⟨Subgroup.mem_centralizer_iff.mp hy₀A w (Subgroup.mem_sup_left hw),
        Subgroup.mem_centralizer_iff.mp hy₁A w (Subgroup.mem_sup_left hw),
        Subgroup.mem_centralizer_iff.mp hy₂A w (Subgroup.mem_sup_left hw)⟩
  have hX₀p : IsPGroup 3 X₀ := fun w => ⟨1, Subtype.ext (by rw [pow_one]; exact hX₀.2 w w.2)⟩
  obtain ⟨w, hwX₀, hw1, hxw⟩ := exists_fixed_ne_one hX₀p hX₀ne hxX₀
    (CFSG.AGLEmbedding.isPGroup_zpowers_of_pow_eq_one (k := 1) (by rwa [pow_one]))
  obtain ⟨k₀, k₁, k₂, hwu⟩ := exists_zpow_of_mem_sup hc01 hc02 hc12 (hX₀W hwX₀)
  have hxy₀ : x * y₀ * x⁻¹ = y₁ := rfl
  have hxy₁ : x * y₁ * x⁻¹ = y₂ := by rw [hy₁, hy₂, pow_two]; group
  have hxy₂ : x * y₂ * x⁻¹ = y₀ := by
    rw [hy₂]
    calc x * (x ^ 2 * y₀ * (x ^ 2)⁻¹) * x⁻¹ = x ^ 3 * y₀ * (x ^ 3)⁻¹ := by group
      _ = y₀ := by rw [hx3, one_mul, inv_one, mul_one]
  have hconj : ∀ (g : Y) (k : ℤ), x * g ^ k * x⁻¹ = (x * g * x⁻¹) ^ k := fun g k => by
    rw [conj_zpow]
  have hxw' : x * w * x⁻¹ = y₀ ^ k₂ * y₁ ^ k₀ * y₂ ^ k₁ := by
    have : x * (y₀ ^ k₀ * y₁ ^ k₁ * y₂ ^ k₂) * x⁻¹ =
        (x * y₀ ^ k₀ * x⁻¹) * (x * y₁ ^ k₁ * x⁻¹) * (x * y₂ ^ k₂ * x⁻¹) := by group
    rw [hwu, this, hconj, hconj, hconj, hxy₀, hxy₁, hxy₂]
    have hcomm' : Commute (y₁ ^ k₀ * y₂ ^ k₁) (y₀ ^ k₂) :=
      (hc01.symm.zpow_zpow k₀ k₂).mul_left (hc02.symm.zpow_zpow k₁ k₂)
    rw [hcomm'.eq, mul_assoc]
  rw [hxw, hwu] at hxw'
  obtain ⟨e0, e1, e2⟩ := zpow_eq_of_three_components hZ3 hL hL₁c hL₂c h01 h02 h12 hy₀LB.1 hy₁L
    hy₂L hy₀3 hy₁3 hxw'
  have e2' : y₂ ^ k₂ = y₂ ^ k₀ := by
    have h1 := congrArg (fun g => x * g * x⁻¹) e1
    simp only [hconj, hxy₁] at h1
    rw [e2, h1]
  have hwz : w = z ^ k₀ := by
    rw [hwu, e1, e2', hzeq, (hc02.mul_left hc12).mul_zpow, hc01.mul_zpow]
  have hzk : z ^ k₀ ≠ 1 := hwz ▸ hw1
  have hord : orderOf z = 3 := orderOf_eq_prime hz3 (fun h => hzL (by
    rw [h]
    exact Subgroup.one_mem _))
  have hzmem : z ∈ Subgroup.zpowers (z ^ k₀) := by
    rw [mem_zpowers_zpow_iff, hord]
    have h3 : ¬ (3 : ℤ) ∣ k₀ := by
      rintro ⟨q, rfl⟩
      apply hzk
      rw [zpow_mul, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hz3, one_zpow]
    have h3' : ¬ 3 ∣ k₀.natAbs := fun h => h3 (Int.natCast_dvd.mpr h)
    have hcop : Nat.gcd k₀.natAbs 3 = 1 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3')
    simpa [Int.gcd] using hcop
  exact hzX₀ ((Subgroup.zpowers_le.mpr (hwz ▸ hwX₀)) hzmem)

end CFSG.AGLEmbedding
