module

public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aAutSmall

@[expose] public section

namespace CFSG

open CFSG.RankThree.PartTwo.Sec21.FF79

theorem MulAut.act_trivial_of_preserves_card_nine
    {B : Type} [Group B] [Finite B] {Y : Subgroup (MulAut B)}
    (hcop : Nat.Coprime (Nat.card Y) 6) {C : Subgroup B} [Finite C]
    (hC : IsElemAb 3 2 C)
    (hpres : ∀ y : MulAut B, y ∈ Y → Subgroup.map y C = C) :
    ∀ (y : MulAut B), y ∈ Y → ∀ c : B, c ∈ C → y c = c := by
  classical
  let φ : ↥Y → MulAut ↥C := fun y =>
    (MulEquiv.subgroupMap (y : MulAut B) C).trans
      (MulEquiv.subgroupCongr (hpres (y : MulAut B) y.2))
  have hφ : ∀ (y : ↥Y) (c : ↥C), ((φ y c : ↥C) : B) = (y : MulAut B) c :=
    fun y c => rfl
  let Φ : ↥Y →* MulAut ↥C :=
    MonoidHom.mk' φ fun y z => by
      ext c
      rw [MulAut.mul_apply, hφ, hφ, hφ]
      rfl
  have hΦ : Φ = 1 :=
    MulAut.eq_one_of_coprime_six_of_card_nine (G := B) (W := C) hC hcop Φ
  intro y hy c hc
  have hfix : Φ ⟨y, hy⟩ ⟨c, hc⟩ = ⟨c, hc⟩ := by
    rw [DFunLike.congr_fun hΦ ⟨y, hy⟩]
    rfl
  have h := congrArg (fun x : ↥C => (x : B)) hfix
  simpa [Φ, φ] using h

theorem MulAut.act_trivial_of_preserves_card_three
    {B : Type} [Group B] [Finite B] {Y : Subgroup (MulAut B)}
    (hodd : Odd (Nat.card Y)) {C : Subgroup B} [Finite C]
    (hC : Nat.card C = 3)
    (hpres : ∀ y : MulAut B, y ∈ Y → Subgroup.map y C = C) :
    ∀ (y : MulAut B), y ∈ Y → ∀ c : B, c ∈ C → y c = c := by
  classical
  let φ : ↥Y → MulAut ↥C := fun y =>
    (MulEquiv.subgroupMap (y : MulAut B) C).trans
      (MulEquiv.subgroupCongr (hpres (y : MulAut B) y.2))
  have hφ : ∀ (y : ↥Y) (c : ↥C), ((φ y c : ↥C) : B) = (y : MulAut B) c :=
    fun y c => rfl
  let Φ : ↥Y →* MulAut ↥C :=
    MonoidHom.mk' φ fun y z => by
      ext c
      rw [MulAut.mul_apply, hφ, hφ, hφ]
      rfl
  have hΦ : Φ = 1 :=
    MulAut.eq_one_of_odd_of_card_three (W := ↥C) hC hodd Φ
  intro y hy c hc
  have hfix : Φ ⟨y, hy⟩ ⟨c, hc⟩ = ⟨c, hc⟩ := by
    rw [DFunLike.congr_fun hΦ ⟨y, hy⟩]
    rfl
  have h := congrArg (fun x : ↥C => (x : B)) hfix
  simpa [Φ, φ] using h

end CFSG
