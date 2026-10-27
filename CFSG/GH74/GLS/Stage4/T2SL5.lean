module

public import CFSG.GH74.GLS.Stage4.T2Interfaces
public import CFSG.GH74.GLS.Stage4.T2CentSL
public import CFSG.GH74.GLS.IVK.Lifted.Outer14
public import CFSG.GH74.GLS.Stage4.T2OddAut

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2

theorem t2oc5_comm_of_oddAut {G : Type} [Group G] [Finite G] (M : Subgroup G)
    (hall : ∀ θ : MulAut ↥M, Odd (orderOf θ) → θ = 1) (ρ : G) (hρ : Odd (orderOf ρ))
    (hnorm : ∀ φ ∈ M, ρ * φ * ρ⁻¹ ∈ M) (φ : G) (hφ : φ ∈ M) : ρ * φ = φ * ρ := by
  have hmem : ρ ∈ Subgroup.normalizer (M : Set G) := Subgroup.mem_normalizer_fintype hnorm
  have hord : orderOf (M.normalizerMonoidHom ⟨ρ, hmem⟩) ∣ orderOf ρ := by
    have := orderOf_map_dvd M.normalizerMonoidHom
      (⟨ρ, hmem⟩ : Subgroup.normalizer (M : Set G))
    rwa [Subgroup.orderOf_mk] at this
  have h1 : M.normalizerMonoidHom ⟨ρ, hmem⟩ = 1 := hall _ (Odd.of_dvd_nat hρ hord)
  have h2 := congrArg (fun α : MulAut ↥M => (α ⟨φ, hφ⟩ : G)) h1
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h2
  rw [mul_inv_eq_iff_eq_mul] at h2
  exact h2

theorem t2oc5_card_of_dihedral {M : Type} [Group M] {n : ℕ}
    (h : CFSG.GH74.GLS.IVK.IsDihedralTwoGroup M n) : Nat.card M = 2 ^ n := by
  obtain ⟨-, k, hk, hk2, ⟨d⟩⟩ := h
  have : NeZero k := ⟨by omega⟩
  rw [Nat.card_congr d.toEquiv, DihedralGroup.nat_card]
  omega

theorem t2oc5_three_le_of_le_pow {n : ℕ} (hn : 8 ≤ 2 ^ n) : 3 ≤ n := by
  by_contra h
  have h4 : 2 ^ n ≤ 4 := by
    calc 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 := by norm_num
  omega

theorem t2oc5_four_le_card_conj {Q : Type} [Group Q] [Finite Q] {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (e : Q ≃* SL2 F) (P₀ : Sylow 2 Q) :
    4 ≤ Nat.card ↥((P₀ : Subgroup Q).map (MulAut.conj : Q →* MulAut Q)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h8 : 2 ^ 3 ∣ Nat.card Q := by
    rw [Nat.card_congr e.toEquiv, t2C_card_sl2]
    obtain ⟨k, hk⟩ := hodd
    have hsq : Nat.card F ^ 2 - 1 = 4 * (k * (k + 1)) := by
      have h : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
      rw [hk, h, Nat.add_sub_cancel]
    obtain ⟨j, hj⟩ := Nat.even_mul_succ_self k
    rw [hsq, hj]
    exact ⟨Nat.card F * j, by ring⟩
  have h8P : 2 ^ 3 ∣ Nat.card (P₀ : Subgroup Q) := P₀.pow_dvd_card_of_pow_dvd_card h8
  have h8le : 2 ^ 3 ≤ Nat.card (P₀ : Subgroup Q) := Nat.le_of_dvd Nat.card_pos h8P
  let f : ↥(P₀ : Subgroup Q) →* MulAut Q :=
    (MulAut.conj : Q →* MulAut Q).comp (P₀ : Subgroup Q).subtype
  have hrange : f.range = (P₀ : Subgroup Q).map (MulAut.conj : Q →* MulAut Q) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcard : Nat.card (P₀ : Subgroup Q) = Nat.card f.range * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have hker : Nat.card f.ker ≤ 2 := by
    have hcen : ∀ x : f.ker, e x.1.1 = 1 ∨ e x.1.1 = negOne F := by
      intro x
      have hx : MulAut.conj (x.1.1 : Q) = 1 := MonoidHom.mem_ker.mp x.2
      have hz := CFSG.GH74.GLS.IVK.Lifted.mem_center_of_conj_eq_one hx
      have hz' : e x.1.1 ∈ Subgroup.center (SL2 F) := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨q, rfl⟩ := e.surjective y
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz q]
      exact (t2C_center_sl2 _).1 hz'
    let g : f.ker → Bool := fun x => decide (e x.1.1 = 1)
    have hg : Function.Injective g := by
      intro x y hxy
      have hiff : e x.1.1 = 1 ↔ e y.1.1 = 1 := decide_eq_decide.mp hxy
      have hxy' : e x.1.1 = e y.1.1 := by
        by_cases hx1 : e x.1.1 = 1
        · exact hx1.trans (hiff.mp hx1).symm
        · have hy1 : ¬ e y.1.1 = 1 := fun h => hx1 (hiff.mpr h)
          rw [(hcen x).resolve_left hx1, (hcen y).resolve_left hy1]
      exact Subtype.ext (Subtype.ext (e.injective hxy'))
    have := Nat.card_le_card_of_injective g hg
    simpa using this
  rw [← hrange]
  have hmul := Nat.mul_le_mul_left (Nat.card f.range) hker
  omega

theorem t2_oc5 : T2OC5 := by
  intro Q _ _ F _ _ hodd h3 e P₀ M hM hP₀ hf hξ ρ hρ hnorm φ hφ
  obtain ⟨-, hdih⟩ := CFSG.GH74.GLS.IVK.Lifted.sl_outer_structure hodd h3 e M hM P₀ hP₀
    (fun φ hφ _ => hf φ hφ)
  have hall : ∀ θ : MulAut ↥M, Odd (orderOf θ) → θ = 1 := by
    rcases hdih with ⟨n, hn⟩ | ⟨n, hn⟩
    ·
      have h3n : 3 ≤ n := by
        obtain ⟨ξ, hξM, hξn⟩ := hξ
        have hD4 := t2oc5_four_le_card_conj hodd e P₀
        have hDne : (P₀ : Subgroup Q).map (MulAut.conj : Q →* MulAut Q) ≠ M := by
          intro h
          have hξD : ξ ∈ (P₀ : Subgroup Q).map (MulAut.conj : Q →* MulAut Q) := by
            rw [h]
            exact hξM
          exact hξn (Subgroup.map_le_range _ _ hξD)
        have hlt : Nat.card ↥((P₀ : Subgroup Q).map (MulAut.conj : Q →* MulAut Q)) < Nat.card ↥M := by
          by_contra hge
          exact hDne (Subgroup.eq_of_le_of_card_ge hP₀ (not_lt.mp hge))
        obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hP₀
        have hc2 : 2 ≤ c := by
          by_contra hc2
          have hc1 : c ≤ 1 := by omega
          have := Nat.mul_le_mul_left
            (Nat.card ↥((P₀ : Subgroup Q).map (MulAut.conj : Q →* MulAut Q))) hc1
          omega
        have hmul := Nat.mul_le_mul_left
          (Nat.card ↥((P₀ : Subgroup Q).map (MulAut.conj : Q →* MulAut Q))) hc2
        have hM8 : 8 ≤ Nat.card ↥M := by omega
        rw [t2oc5_card_of_dihedral hn] at hM8
        exact t2oc5_three_le_of_le_pow hM8
      exact fun θ hθ => t2C_oddAut_dihedral h3n hn θ hθ
    · exact fun θ hθ => t2C_oddAut_semidihedral hn θ hθ
  exact t2oc5_comm_of_oddAut M hall ρ hρ hnorm φ hφ

end CFSG.GH74.GLS.Stage4.Rest
