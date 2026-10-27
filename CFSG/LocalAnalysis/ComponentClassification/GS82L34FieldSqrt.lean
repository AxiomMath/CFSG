module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWIsoModelB
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.TBLitL34PField
public import CFSG.LocalAnalysis.ComponentClassification.TBLitL34PGraph

public section

namespace CFSG.ComponentClassification.TBLit.L34P

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.L34Facts.Real
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]

theorem exists_fixed_sqrt_center
    {β : X} {K L : Subgroup X}
    (hK : ⁅K, K⁆ = K) (hL34 : IsL34Type (K ⧸ Open.fusionZStar K))
    (hβN : β ∈ normalizer (K : Set X)) (hβ2 : β * β = 1) (hLK : L ≤ K)
    (hLβ : L ≤ centralizer ({β} : Set X)) {F : Type*} [Field F] [Finite F]
    (h7 : Nat.card F = 7) (e : ↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, F))
    (hfield : HarrisLit.EndB.IsL34Field K β)
    (z : Jhat K) (hz : z ∈ center (Jhat K)) (hfix : betaHat K hβN z = z) (h2 : z ^ 2 = 1) :
    ∃ ω ∈ center (Jhat K), betaHat K hβN ω = ω ∧ ω ^ 2 = z := by
  obtain ⟨q, l, hQS, -, hzz, hinj⟩ := exists_field_frame hK hL34 hβN hβ2 hLK hLβ h7 e hfield
  rw [← hQS.ker] at hz
  obtain ⟨c, d, rfl⟩ := (WIso.mem_ker_iff_zz hQS).1 hz
  have hd : d = 0 := by
    rw [hzz] at hfix
    have h1 : zz l (c + 3 * d) (3 * d) * (zz l c d)⁻¹ = 1 := by rw [hfix, mul_inv_cancel]
    rw [zz_inv, zz_mul] at h1
    obtain ⟨h3, -⟩ := hinj _ _ h1
    have h3d : 3 * d = 0 := by linear_combination h3
    have key : ∀ x : ZMod 4, 3 * x = 0 → x = 0 := by decide
    exact key d h3d
  subst hd
  have hc : 2 * c = 0 := by
    have h1 : zz l c 0 * zz l c 0 = 1 := by rw [← pow_two]; exact h2
    rw [zz_mul] at h1
    obtain ⟨h3, -⟩ := hinj _ _ h1
    linear_combination h3
  have key2 : ∀ x : ZMod 4, 2 * x = 0 → ∃ c' : ZMod 4, 2 * c' = x := by decide
  obtain ⟨c', hc'⟩ := key2 c hc
  refine ⟨zz l c' 0, ?_, ?_, ?_⟩
  · rw [← hQS.ker]; exact zz_mem_ker hQS c' 0
  · rw [hzz]; simp
  · rw [pow_two, zz_mul, ← hc', two_mul]; simp


theorem isL34Field_of_sl2Seven
    {K L : Subgroup X} {β : X}
    (hK : ⁅K, K⁆ = K) (hOK : pPrimeCore 2 ↥K = ⊥) (hL34 : IsL34Type (↥K ⧸ Open.fusionZStar ↥K))
    (hβN : β ∈ normalizer (K : Set X)) (hβ2 : β * β = 1) (hβK : ¬ ∀ k ∈ K, β⁻¹ * k * β = k)
    (hLK : L ≤ K) (hLβ : L ≤ centralizer ({β} : Set X)) {F : Type*} [Field F] [Finite F]
    (h7 : Nat.card F = 7) (e : ↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, F)) :
    HarrisLit.EndB.IsL34Field K β := by
  have hodd : Odd (Nat.card F) := by rw [h7]; decide
  obtain ⟨q, hqS, hqsurj, hqker, h3, ρ, hρ, hβq⟩ := exists_frame hL34 hβN hβ2
  have hdvd : ∀ C : Subgroup (Equiv.Perm (Fin 42)), (imageHom hLK q).range ≤ C →
      Nat.card F * (Nat.card F ^ 2 - 1) ∣ 2 * Nat.card C := fun C hC => by
    have h := card_sl2_dvd hLK (CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd) e q
      hqker
    rw [card_sl2] at h
    exact h.trans (mul_dvd_mul_left 2 (Subgroup.card_dvd_of_le hC))
  rcases hρ with rfl | rfl | rfl | rfl | rfl
  ·
    refine (hβK fun k hk => ?_).elim
    have : Group.IsPerfect (Jhat K) := ⟨commutator_jhat hK⟩
    have hid := PerfectAutomorphisms.hom_eq_id_of_central_displacement
      (betaHat K hβN).toMonoidHom fun x => by
        rw [← hqker, MonoidHom.mem_ker, map_mul, map_inv, MulEquiv.coe_toMonoidHom, hβq x,
          one_mul, inv_one, mul_one, inv_mul_cancel]
    have h1 : jq K (conjJ K hβN ⟨k, hk⟩) = jq K ⟨k, hk⟩ := by
      rw [← betaHat_jq]
      exact DFunLike.congr_fun hid (jq K ⟨k, hk⟩)
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hOK, mem_bot,
      inv_mul_eq_one] at h1
    have h2 := congrArg Subtype.val h1
    rwa [coe_conjJ] at h2
  ·
    have h := hdvd C₁ (range_imageHom_le hLK hβN hLβ hqS hβq)
    rw [card_C₁, h7] at h
    norm_num at h
  · exact isL34Field_of_frame hβN hβ2 hqS hqsurj hqker hβq
  · exact (false_of_graph hK hβN hLK hLβ hodd e hqS hqsurj hqker h3 hβq).elim
  ·
    have h := hdvd C₄ (range_imageHom_le hLK hβN hLβ hqS hβq)
    rw [card_C₄, h7] at h
    norm_num at h

theorem exists_fixed_sqrt_center'
    {K L : Subgroup X} {β : X}
    (hK : ⁅K, K⁆ = K) (hOK : pPrimeCore 2 ↥K = ⊥) (hL34 : IsL34Type (↥K ⧸ Open.fusionZStar ↥K))
    (hβN : β ∈ normalizer (K : Set X)) (hβ2 : β * β = 1) (hβK : ¬ ∀ k ∈ K, β⁻¹ * k * β = k)
    (hLK : L ≤ K) (hLβ : L ≤ centralizer ({β} : Set X)) {F : Type*} [Field F] [Finite F]
    (h7 : Nat.card F = 7) (e : ↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, F))
    (z : Jhat K) (hz : z ∈ center (Jhat K)) (hfix : betaHat K hβN z = z) (h2 : z ^ 2 = 1) :
    ∃ ω ∈ center (Jhat K), betaHat K hβN ω = ω ∧ ω ^ 2 = z :=
  exists_fixed_sqrt_center hK hL34 hβN hβ2 hLK hLβ h7 e
    (isL34Field_of_sl2Seven hK hOK hL34 hβN hβ2 hβK hLK hLβ h7 e) z hz hfix h2

end CFSG.ComponentClassification.TBLit.L34P
