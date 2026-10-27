module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycGroup

public section

namespace CFSG.AGLEmbedding.BlockCyc

open CFSG.Open

theorem aut5Le_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (h : Aut5Le X) :
    Aut5Le Y := by
  intro W hW
  have h1 := h (W.map (MulAut.congr e).symm.toMonoidHom) (isElemAbelian_map _ hW)
  rwa [Subgroup.card_map_of_injective (MulAut.congr e).symm.injective] at h1

theorem aut5Le_of_not_sq_dvd {Y : Type*} [Group Y] [Finite Y] (h : ¬ 25 ∣ Nat.card (MulAut Y)) :
    Aut5Le Y := by
  intro W hW
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hp : IsPGroup 5 W := fun x => ⟨1, by
    have := hW.2 x x.2
    simpa [Subtype.ext_iff] using this⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hdvd : Nat.card W ∣ Nat.card (MulAut Y) := Subgroup.card_subgroup_dvd_card W
  by_contra hgt
  push Not at hgt
  have hk2 : 2 ≤ k := by
    by_contra hk2
    have h5k : 5 ^ k ≤ 5 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have : 25 ∣ Nat.card W := by
    rw [hk]
    exact (pow_dvd_pow 5 hk2 : 5 ^ 2 ∣ 5 ^ k)
  exact h (this.trans hdvd)

end CFSG.AGLEmbedding.BlockCyc
