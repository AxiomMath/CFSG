module

public import CFSG.RankThree.PartOne.S12.PushingUp
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.CGT.PushingUp

open CFSG CFSG.RankThree.PartOne

theorem card_specialLinear_two_galoisField_one :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)) = 6 := by
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 1) = 2 := by
    rw [← Nat.card_eq_fintype_card]
    simpa using GaloisField.card 2 1 one_ne_zero
  rw [Matrix.card_SL_field (𝔽 := GaloisField 2 1) 2, hq]
  decide

theorem not_isNaturalSLTwoModule_one {L : Type} [Group L] [Finite L] (hL : IsShortGroup L) :
    ¬ IsNaturalSLTwoModule L 1 := by
  rintro ⟨φ, -⟩
  set SL := Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1) with hSL
  have hcard : Nat.card SL = 6 := card_specialLinear_two_galoisField_one
  have hdvd : 3 ∣ Nat.card SL := by
    rw [hcard]
    norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := SL) 3 hdvd
  set N₀ : Subgroup SL := Subgroup.zpowers x with hN₀
  have hN₀card : Nat.card N₀ = 3 := by
    rw [hN₀, Nat.card_zpowers, hx]
  have hindex : N₀.index = 2 := by
    have h := Subgroup.index_mul_card N₀
    rw [hcard, hN₀card] at h
    omega
  have : N₀.Normal := Subgroup.normal_of_index_eq_two hindex
  let π : L →* SL := φ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hπ : Function.Surjective π := fun s => by
    obtain ⟨q, rfl⟩ := φ.surjective s
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨l, rfl⟩
  set N : Subgroup L := N₀.comap π with hN
  have : N.Normal := Subgroup.Normal.comap inferInstance π
  have hNindex : N.index = 2 := by
    rw [hN, Subgroup.index_comap_of_surjective _ hπ, hindex]
  have hquot : IsPGroup 2 (L ⧸ N) :=
    IsPGroup.iff_card.mpr ⟨1, by rw [pow_one]; exact hNindex⟩
  have hle : oResidualTwo L ≤ N := sInf_le ⟨inferInstance, hquot⟩
  rw [hL.residual_eq, top_le_iff] at hle
  rw [hle, Subgroup.index_top] at hNindex
  omega

end CFSG.CGT.PushingUp
