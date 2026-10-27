module

public import CFSG.ClassicalInvolution.RankTwo.Witness
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Sylow
import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open
open scoped MatrixGroups

theorem false_of_central_involution_of_simple {F : Type*} [Group F] [Finite F] [IsSimpleGroup F]
    (hnab : ∃ a b : F, a * b ≠ b * a) {t : F} (ht : orderOf t = 2)
    (hc : (QuotientGroup.mk t : F ⧸ CFSG.oddCore F) ∈ Subgroup.center (F ⧸ CFSG.oddCore F)) :
    False := by
  have hO : CFSG.oddCore F = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.oddCore F) with h | h
    · exact h
    · exfalso
      have hodd := QuaternionStructure.odd_natCard_oddCore F
      rw [h, Subgroup.card_top] at hodd
      have h2 : 2 ∣ Nat.card F := ht ▸ orderOf_dvd_natCard t
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have htc : t ∈ Subgroup.center F := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := Subgroup.mem_center_iff.mp hc (QuotientGroup.mk g)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hO,
      Subgroup.mem_bot, inv_mul_eq_one] at h
    exact h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center F) with h | h
  · rw [h, Subgroup.mem_bot] at htc
    rw [htc, orderOf_one] at ht
    exact absurd ht (by norm_num)
  · obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have hb : b ∈ Subgroup.center F := h ▸ Subgroup.mem_top b
    exact Subgroup.mem_center_iff.mp hb a

theorem false_of_witness_of_equiv_alternatingGroup_seven {F : Type*} [Group F] [Finite F]
    [IsSimpleGroup F] (hnab : ∃ a b : F, a * b ≠ b * a) (e : F ≃* alternatingGroup (Fin 7))
    {K : Subgroup F} (hw : classicalInvolutionWitness K) : False := by
  have hF : Nat.card F = 2520 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.card_eq_fintype_card, Nat.factorial]
  rcases exists_sylow_quaternion_or_dvd_of_witness hw with ⟨S, k, hk, ⟨q⟩⟩ | hdvd
  · set S' : Subgroup F := (S : Subgroup K).map K.subtype with hS'
    have hSp : IsPGroup 2 S' := S.isPGroup'.map K.subtype
    have hcardS : Nat.card S' = 2 ^ (k + 2) := by
      rw [hS', Subgroup.card_map_of_injective K.subtype_injective, Nat.card_congr q.toEquiv,
        Nat.card_eq_fintype_card, QuaternionGroup.card]
      ring
    have hdvd : 2 ^ (k + 2) ∣ 2520 := hF ▸ hcardS ▸ Subgroup.card_subgroup_dvd_card S'
    have hk1 : k = 1 := by
      by_contra hne
      have h16 : 2 ^ 4 ∣ 2 ^ (k + 2) := pow_dvd_pow 2 (by omega)
      have := h16.trans hdvd
      norm_num at this
    subst hk1
    have hidx : ¬ 2 ∣ S'.index := by
      have h := Subgroup.card_mul_index S'
      rw [hcardS, hF] at h
      have : S'.index = 315 := by omega
      rw [this]
      norm_num
    let P : Sylow 2 F := hSp.toSylow hidx
    have hP : (P : Subgroup F) = S' := rfl
    have hquat : Nonempty ((P : Subgroup F) ≃* QuaternionGroup (2 ^ (3 - 2))) :=
      ⟨(MulEquiv.subgroupCongr hP).trans
        ((Subgroup.equivMapOfInjective (S : Subgroup K) K.subtype K.subtype_injective).symm.trans
          q)⟩
    have h8 : 2 ∣ Nat.card (P : Subgroup F) := by
      rw [hP, hcardS]
      norm_num
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := (P : Subgroup F)) 2 h8
    have hxo : orderOf (x : F) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
    exact false_of_central_involution_of_simple hnab hxo
      (CFSG.BrauerSuzuki.brauer_suzuki 3 le_rfl P hquat (x : F) x.2 hxo)
  · have h := hdvd.trans (hF ▸ Subgroup.card_subgroup_dvd_card K)
    have := Nat.le_of_dvd (by norm_num) h
    omega

open CFSG.RankTwoShapes in
theorem not_isQuaternionPair_unitaryFourW {K : Type} [Field K] {hK : Nat.card K = 16}
    (x y : unitaryFourW K hK) : ¬ IsQuaternionPair x y := by
  rintro ⟨h1, h2, h3⟩
  have := charP_two_of_natCard_eq_sixteen hK
  have hsnd1 := congrArg UnitaryFourW.snd h1
  have hsnd2 := congrArg UnitaryFourW.snd h2
  rw [UnitaryFourW.snd_sq, UnitaryFourW.snd_sq] at hsnd1
  rw [UnitaryFourW.snd_sq, UnitaryFourW.snd_sq, UnitaryFourW.fst_mul] at hsnd2
  have hn : UnitaryFourW.fst x ^ 5 ≠ 0 := by
    intro h
    apply h3
    apply UnitaryFourW.ext
    · rw [UnitaryFourW.fst_sq, UnitaryFourW.fst_one]
    · rw [UnitaryFourW.snd_sq, h, UnitaryFourW.snd_one]
  have ha : UnitaryFourW.fst x ≠ 0 := fun h => hn (by rw [h]; norm_num)
  have h8 : UnitaryFourW.fst x ^ 8 = 0 := by grind
  exact ha (pow_eq_zero_iff (by norm_num) |>.mp h8)

theorem natCard_eq_of_statedClassicalModel_psu_three_two_two {F : Type} [Group F]
    (hF : CFSG.Assembly.LowTwoRank.StatedClassicalModel F .PSU 3 2 2) : Nat.card F = 62400 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_four hF

theorem false_of_witness_of_statedClassicalModel_psu_three_two_two {F : Type} [Group F]
    (hF : CFSG.Assembly.LowTwoRank.StatedClassicalModel F .PSU 3 2 2) {K : Subgroup F}
    (hw : classicalInvolutionWitness K) : False := by
  have : Finite F := CFSG.RankTwoShapes.finite_of_statedClassicalModel_PSU_three_two_two hF
  have hcard := natCard_eq_of_statedClassicalModel_psu_three_two_two hF
  rcases exists_sylow_quaternion_or_dvd_of_witness hw with ⟨S, k, hk, ⟨q⟩⟩ | hdvd
  · obtain ⟨x₀, y₀, hxy⟩ := exists_isQuaternionPair_quaternionGroup k hk
    obtain ⟨U, hU⟩ := IsPGroup.exists_le_sylow (S.isPGroup'.map K.subtype)
    have hK16 : Nat.card (GaloisField 2 4) = 16 := by
      rw [GaloisField.card 2 4 (by norm_num)]
      norm_num
    obtain ⟨eW⟩ := CFSG.RankTwoShapes.nonempty_sylow_equiv_unitaryFourW hF U (GaloisField 2 4) hK16
    let ι : (S : Subgroup K) →* (U : Subgroup F) :=
      (K.subtype.comp (S : Subgroup K).subtype).codRestrict (U : Subgroup F)
        fun s => hU ⟨s, s.2, rfl⟩
    have hι : Function.Injective ι := fun a b h =>
      Subtype.ext (K.subtype_injective (congrArg (fun u : (U : Subgroup F) => (u : F)) h))
    have hΦ : Function.Injective (eW.toMonoidHom.comp ι) := eW.injective.comp hι
    exact not_isQuaternionPair_unitaryFourW _ _
      ((hxy.map q.symm.toMonoidHom q.symm.injective).map _ hΦ)
  · have h := hdvd.trans (hcard ▸ Subgroup.card_subgroup_dvd_card K)
    have := Nat.le_of_dvd (by norm_num) h
    omega

end CFSG.ClassicalInvolution
