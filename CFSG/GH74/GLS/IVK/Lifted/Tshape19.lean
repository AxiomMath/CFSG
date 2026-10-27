module

public import CFSG.GH74.GLS.IVK.L2.TShape
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DihedralSylow
public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAut

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup CFSG CFSG.GorensteinWalter CFSG.ABGLocalTools

theorem tshape_of_pgl_hom {T : Type} [Group T] [Finite T] (hT : IsPGroup 2 T) {F : Type} [Field F]
    [Finite F] (hodd : Odd (Nat.card F)) (π : T →* PGL2 F) {z : T} (hz1 : z ≠ 1) (hzz : z * z = 1)
    (hker : ∀ t, π t = 1 ↔ t = 1 ∨ t = z)
    (hcard : Nat.card T = 2 * 2 ^ (Nat.card (PGL2 F)).factorization 2)
    (Q : Subgroup T) (hzQ : z ∈ Q) (hQcard : Nat.card Q * 2 = Nat.card T)
    (hQu : ∀ x ∈ Q, x * x = 1 → x = 1 ∨ x = z)
    (hQnc : ∀ q₀ : T, ¬ Q ≤ Subgroup.zpowers q₀ ⊔ Subgroup.zpowers z) :
    (∃ n, IVK.IsQuaternionTwoGroup T n) ∨ (∃ n, IVK.IsSemidihedralTwoGroup T n) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite (PGL2 F) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk : GL (Fin 2) F →* PGL2 F)
      Matrix.ProjGenLinGroup.mk_surjective
  have hker2 := IVK.card_ker_eq_two π hz1 hzz hker
  have hrange : Nat.card π.range = 2 ^ (Nat.card (PGL2 F)).factorization 2 := by
    have h1 := Subgroup.card_ker_mul_card_range π
    rw [hker2] at h1
    omega
  let S : Sylow 2 (PGL2 F) := Sylow.ofCard π.range hrange
  obtain ⟨m, hm1, ⟨eS⟩⟩ :=
    pgl2_odd_hasDihedralSylowTwo_model F (isOddPrimePower_card_of_odd hodd) S
  have hcardP : Nat.card (PGL2 F) = Nat.card F * (Nat.card F ^ 2 - 1) := pgl2_card_formula F
  have h8 : 2 ^ 3 ∣ Nat.card (PGL2 F) := by
    rw [hcardP]
    obtain ⟨a, ha⟩ := hodd
    refine Dvd.dvd.mul_left ?_ _
    have h4 : Nat.card F ^ 2 - 1 = 4 * (a * (a + 1)) := by
      rw [ha]
      have : (2 * a + 1) ^ 2 = 4 * (a * (a + 1)) + 1 := by ring
      omega
    rw [h4]
    obtain ⟨c, hc⟩ := (Nat.even_mul_succ_self a).two_dvd
    exact ⟨c, by rw [hc]; ring⟩
  have hSdvd : 2 ^ 3 ∣ Nat.card ↥(S : Subgroup (PGL2 F)) := S.pow_dvd_card_of_pow_dvd_card h8
  have hn0 : NeZero (2 ^ m) := ⟨by positivity⟩
  have hSD : Nat.card ↥(S : Subgroup (PGL2 F)) = 2 * 2 ^ m := by
    rw [Nat.card_congr eS.toEquiv, DihedralGroup.nat_card]
  have hm2 : 2 ≤ m := by
    rw [hSD] at hSdvd
    by_contra hlt
    have hm' : m ≤ 1 := by omega
    have h4 : 2 * 2 ^ m ≤ 4 := by
      calc 2 * 2 ^ m ≤ 2 * 2 ^ 1 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hm')
        _ = 4 := by norm_num
    have := Nat.le_of_dvd (by positivity) hSdvd
    omega
  let eS' : ↥π.range ≃* DihedralGroup (2 ^ m) := eS
  let πD : T →* DihedralGroup (2 ^ m) := eS'.toMonoidHom.comp π.rangeRestrict
  have hπD : Function.Surjective πD := by
    intro d
    obtain ⟨t, ht⟩ := π.rangeRestrict_surjective (eS'.symm d)
    refine ⟨t, ?_⟩
    show eS' (π.rangeRestrict t) = d
    rw [ht]
    exact eS'.apply_symm_apply d
  have hkerD : ∀ t, πD t = 1 ↔ t = 1 ∨ t = z := by
    intro t
    rw [← hker]
    constructor
    · intro h
      have h' : π.rangeRestrict t = 1 := eS'.injective (by rw [map_one]; exact h)
      exact congrArg (fun x : ↥π.range => (x : PGL2 F)) h'
    · intro h
      have h' : π.rangeRestrict t = 1 := Subtype.ext h
      show eS' (π.rangeRestrict t) = 1
      rw [h', map_one]
  exact IVK.tshape hT hm2 πD hπD hz1 hzz hkerD Q hzQ hQcard hQu hQnc

end CFSG.GH74.GLS.IVK.Lifted
