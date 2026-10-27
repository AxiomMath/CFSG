module

public import CFSG.Quasithin.Background.D2Z19
public import CFSG.Quasithin.Background.HSecTransfer

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin

theorem not_twentyFive_dvd_card_GL_zmod_two {r : ℕ} (hr : r ≤ 7) :
    ¬ 25 ∣ Nat.card (GL (Fin r) (ZMod 2)) := by
  rw [CFSG.SectionRank.Ccomm.card_GL_zmod (p := 2) r]
  interval_cases r <;> decide

theorem exists_orderOf_five_fix_commV {W : Type*} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {φ : MulAut W}
    (hd : rkIdx (fixV (Subgroup.zpowers φ)) ≤ 7)
    {P : Subgroup (MulAut W)} (hP : Nat.card P = 25)
    (hPφ : ∀ ψ ∈ P, ψ * φ = φ * ψ) :
    ∃ ψ ∈ P, orderOf ψ = 5 ∧ ∀ z ∈ commV (Subgroup.zpowers φ), ψ z = z := by
  let U : Subgroup W := commV (Subgroup.zpowers φ)
  have hUinv : ∀ ψ ∈ P, ∀ u ∈ U, ψ u ∈ U := by
    intro ψ hψ u hu
    have hconj : conjBy ψ (Subgroup.zpowers φ) = Subgroup.zpowers φ := by
      rw [conjBy, MonoidHom.map_zpowers]
      have hφ : MulAut.conj ψ φ = φ := by
        rw [MulAut.conj_apply, hPφ ψ hψ, mul_inv_cancel_right]
      exact congrArg Subgroup.zpowers hφ
    exact commV_apply_of_conjBy hconj hu
  let ρ : ↥P →* MulAut ↥U := CFSG.Quasithin.H.resHom hUinv
  have hrkU : rk U = rkIdx (fixV (Subgroup.zpowers φ)) :=
    (rkIdx_fixV_zpowers φ).symm
  have hrk7 : rk U ≤ 7 := by
    rw [hrkU]; exact hd
  have hcardU_pow : Nat.card U = 2 ^ rk U := card_eq_two_pow hW U
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (fun a b : U => mul_comm a b)
    (fun a : U => Subtype.ext (by simpa using hW (a : W))) hcardU_pow
  have hcardAut : Nat.card (MulAut ↥U) = Nat.card (GL (Fin (rk U)) (ZMod 2)) :=
    CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e
  have h25 : ¬ 25 ∣ Nat.card (MulAut ↥U) := by
    rw [hcardAut]
    exact not_twentyFive_dvd_card_GL_zmod_two hrk7
  have hrange25 : Nat.card ↥ρ.range ∣ 25 := by
    have hcard := Subgroup.card_ker_mul_card_range ρ
    rw [hP, mul_comm] at hcard
    exact ⟨Nat.card ↥ρ.ker, hcard.symm⟩
  have hrange_ne : Nat.card ↥ρ.range ≠ 25 := by
    intro h
    exact h25 (h ▸ Subgroup.card_subgroup_dvd_card ρ.range)
  obtain ⟨i, hi2, hi⟩ := (Nat.dvd_prime_pow (p := 5) (m := 2) (by norm_num)).mp hrange25
  have hrange5 : Nat.card ↥ρ.range ≤ 5 := by
    have hi1 : i ≤ 1 := by
      have hne : i ≠ 2 := by
        intro h
        exact hrange_ne (by rw [hi, h]; norm_num)
      omega
    calc Nat.card ↥ρ.range = 5 ^ i := hi
      _ ≤ 5 ^ 1 := Nat.pow_le_pow_right (by norm_num) hi1
      _ = 5 := pow_one 5
  have hker_ge : 5 ≤ Nat.card ↥ρ.ker := by
    have hcard := Subgroup.card_ker_mul_card_range ρ
    rw [hP] at hcard
    have hle : 5 * 5 ≤ Nat.card ↥ρ.ker * 5 := by
      calc 5 * 5 = 25 := by norm_num
        _ = Nat.card ↥ρ.ker * Nat.card ↥ρ.range := hcard.symm
        _ ≤ Nat.card ↥ρ.ker * 5 := Nat.mul_le_mul_left _ hrange5
    exact Nat.le_of_mul_le_mul_right hle (by norm_num)
  have hker_dvd : Nat.card ↥ρ.ker ∣ 25 := by
    have hcard := Subgroup.card_ker_mul_card_range ρ
    rw [hP] at hcard
    exact ⟨Nat.card ↥ρ.range, hcard.symm⟩
  have h5dvd : 5 ∣ Nat.card ↥ρ.ker := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (p := 5) (m := 2) (by norm_num)).mp hker_dvd
    have hj1 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hj
      omega
    rw [hj]
    exact dvd_pow_self 5 hj1
  obtain ⟨g, hg⟩ := @exists_prime_orderOf_dvd_card' _ _ _ 5 ⟨by norm_num⟩ h5dvd
  refine ⟨((g : ↥P) : MulAut W), (g : ↥P).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hg
  · intro z hz
    let u : ↥U := ⟨z, hz⟩
    have hgker : ρ (g : ↥P) = 1 := MonoidHom.mem_ker.mp g.2
    have hfix : ρ (g : ↥P) u = u := by rw [hgker]; rfl
    have hcoe : ((ρ (g : ↥P) u : ↥U) : W) = z := congrArg Subtype.val hfix
    have hcoe2 : ((ρ (g : ↥P) u : ↥U) : W) = ((g : ↥P) : MulAut W) z :=
      CFSG.Quasithin.H.coe_resHom_apply hUinv (g : ↥P) u
    exact hcoe2.symm.trans hcoe

end CFSG.GroupTheory
