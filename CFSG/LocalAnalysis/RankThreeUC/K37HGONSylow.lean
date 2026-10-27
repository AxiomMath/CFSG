module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma59
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37H

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma59Ns (InputONSylow)
open scoped commutatorElement

theorem k37G_pow_three_of_isPGroup (hSyl : InputONSylow) {Y : Type} [Group Y] [Finite Y]
    (hY : IsHatON Y) {k : Y} (hk : IsPGroup 3 (Subgroup.zpowers k)) : k ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := hk.exists_le_sylow
  exact (hSyl Y hY P).2.1 k (hP (Subgroup.mem_zpowers k))

private noncomputable def k37G_commHom {Y : Type} [Group Y] (P : Subgroup Y) (k : Y)
    (hc : ∀ x ∈ P, ⁅x, k⁆ ∈ Subgroup.center Y) : P →* Subgroup.center Y where
  toFun x := ⟨⁅(x : Y), k⁆, hc x x.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    have ha := Subgroup.mem_center_iff.mp (hc x x.2)
    have hb := Subgroup.mem_center_iff.mp (hc y y.2)
    simp only [commutatorElement_def] at ha hb
    show ⁅(x : Y) * (y : Y), k⁆ = ⁅(x : Y), k⁆ * ⁅(y : Y), k⁆
    simp only [commutatorElement_def]
    calc (x : Y) * (y : Y) * k * ((x : Y) * (y : Y))⁻¹ * k⁻¹
        = (x : Y) * ((y : Y) * k * (y : Y)⁻¹ * k⁻¹) * k * (x : Y)⁻¹ * k⁻¹ := by group
      _ = ((y : Y) * k * (y : Y)⁻¹ * k⁻¹) * (x : Y) * k * (x : Y)⁻¹ * k⁻¹ := by
        rw [hb (x : Y)]
      _ = ((y : Y) * k * (y : Y)⁻¹ * k⁻¹) * ((x : Y) * k * (x : Y)⁻¹ * k⁻¹) := by group
      _ = ((x : Y) * k * (x : Y)⁻¹ * k⁻¹) * ((y : Y) * k * (y : Y)⁻¹ * k⁻¹) := by
        rw [ha ((y : Y) * k * (y : Y)⁻¹ * k⁻¹)]

theorem k37G_exists_E27 (hSyl : InputONSylow) {Y : Type} [Group Y] [Finite Y] (hY : IsHatON Y)
    {k : Y} (hk : IsPGroup 3 (Subgroup.zpowers k)) (hkz : k ∉ Subgroup.center Y) :
    ∃ F : Subgroup Y, IsElemAbelian 3 F ∧ Nat.card F = 27 ∧ ∀ x ∈ F, x * k = k * x := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hkP⟩ := hk.exists_le_sylow
  obtain ⟨hcardP, hexp, hcomm, -⟩ := hSyl Y hY P
  have hkP' : k ∈ (P : Subgroup Y) := hkP (Subgroup.mem_zpowers k)
  have hk3 : k ^ 3 = 1 := hexp k hkP'
  have hZ3 : Nat.card (Subgroup.center Y) = 3 := hY.2.1
  have hZc : ∀ z ∈ Subgroup.center Y, ∀ y : Y, z * y = y * z := fun z hz y =>
    (Subgroup.mem_center_iff.mp hz y).symm
  have hZe : ∀ z ∈ Subgroup.center Y, z ^ 3 = 1 := fun z hz => by
    have := pow_card_eq_one' (G := Subgroup.center Y) (x := ⟨z, hz⟩)
    rw [hZ3] at this
    exact congrArg Subtype.val this
  have hZel : IsElemAbelian 3 (Subgroup.center Y) :=
    ⟨⟨⟨fun a b => Subtype.ext (hZc a a.2 b)⟩⟩, hZe⟩
  obtain ⟨hA1el, hA1card⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hZel
    (y := k) hkz hk3 (fun a ha => hZc a ha k)
  rw [hZ3] at hA1card
  have hc : ∀ x ∈ (P : Subgroup Y), ⁅x, k⁆ ∈ Subgroup.center Y := fun x hx => hcomm x hx k hkP'
  set φ := k37G_commHom (P : Subgroup Y) k hc with hφ
  have hker : ∀ x : (P : Subgroup Y), x ∈ φ.ker ↔ (x : Y) * k = k * (x : Y) := by
    intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : ⁅(x : Y), k⁆ = 1 := congrArg Subtype.val h
      rw [commutatorElement_def] at h1
      calc (x : Y) * k = ((x : Y) * k * (x : Y)⁻¹ * k⁻¹) * (k * (x : Y)) := by group
        _ = k * (x : Y) := by rw [h1, one_mul]
    · intro h
      apply Subtype.ext
      show ⁅(x : Y), k⁆ = 1
      rw [commutatorElement_def, h]
      group
  have hP5 : Nat.card (P : Subgroup Y) = 3 ^ 5 := hcardP
  have hindex : φ.ker.index = Nat.card φ.range := Subgroup.index_ker φ
  have hrange : Nat.card φ.range ≤ 3 :=
    (Subgroup.card_le_card_group φ.range).trans hZ3.le
  have hker81 : 81 ≤ Nat.card φ.ker := by
    have h1 := Subgroup.card_mul_index φ.ker
    rw [hindex, hP5] at h1
    have hpos : 0 < Nat.card φ.range := Nat.card_pos
    have hpos2 : 0 < Nat.card φ.ker := Nat.card_pos
    by_contra hlt
    push Not at hlt
    have : Nat.card φ.ker * Nat.card φ.range ≤ 80 * 3 := Nat.mul_le_mul (by omega) hrange
    omega
  obtain ⟨x, hxk, hxA⟩ : ∃ x : (P : Subgroup Y), (x : Y) * k = k * (x : Y) ∧
      (x : Y) ∉ (Subgroup.center Y ⊔ Subgroup.zpowers k) := by
    by_contra hall
    push Not at hall
    have hle : Nat.card φ.ker ≤ Nat.card (Subgroup.center Y ⊔ Subgroup.zpowers k : Subgroup Y) :=
      Nat.card_le_card_of_injective (fun x => (⟨(x.1 : Y), hall x.1 ((hker x.1).mp x.2)⟩ :
        (Subgroup.center Y ⊔ Subgroup.zpowers k : Subgroup Y)))
        fun a b h => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))
    omega
  have hx3 : (x : Y) ^ 3 = 1 := hexp x x.2
  have hxc : ∀ a ∈ (Subgroup.center Y ⊔ Subgroup.zpowers k : Subgroup Y), a * (x : Y) = x * a := by
    intro a ha
    have hle : (Subgroup.center Y ⊔ Subgroup.zpowers k : Subgroup Y) ≤
        Subgroup.centralizer ({(x : Y)} : Set Y) := by
      refine sup_le (fun z hz => ?_) ?_
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hZc z hz x
      · refine Subgroup.zpowers_le.2 ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hxk.symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
  obtain ⟨hA2el, hA2card⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hA1el
    (y := (x : Y)) hxA hx3 hxc
  rw [hA1card] at hA2card
  refine ⟨_, hA2el, hA2card, fun y hy => ?_⟩
  have hle : (Subgroup.center Y ⊔ Subgroup.zpowers k ⊔ Subgroup.zpowers (x : Y) : Subgroup Y) ≤
      Subgroup.centralizer ({k} : Set Y) := by
    refine sup_le (sup_le (fun z hz => ?_) ?_) ?_
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hZc z hz k
    · refine Subgroup.zpowers_le.2 ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
    · refine Subgroup.zpowers_le.2 ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hxk
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

end CFSG.LocalAnalysis.RankThreeUC.S15.K37H

end
