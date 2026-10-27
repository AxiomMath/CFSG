module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGHVI218A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

variable {S : Type} [Group S] [Finite S] {ρ : MulAut S}

theorem FpfNonab.card_sup (h : FpfNonab S ρ) {x : S} (hx : orderOf x = 4) :
    Nat.card ↥(zpowers x ⊔ zpowers (ρ x)) = 16 := by
  have hρx : orderOf (ρ x) = 4 := by rw [MulEquiv.orderOf_eq, hx]
  have hcard := card_zpowers_sup_zpowers x (ρ x) (h.commute_rho x) 4 hx hρx
    (h.inf_zpowers_rho hx)
  rw [hcard]

theorem FpfNonab.sup_equiv (h : FpfNonab S ρ) {x : S} (hx : orderOf x = 4) :
    Nonempty (↥(zpowers x ⊔ zpowers (ρ x)) ≃* Z4Z4) := by
  have hρx : orderOf (ρ x) = 4 := by rw [MulEquiv.orderOf_eq, hx]
  exact exists_mulEquiv_Z4Z4 x (ρ x) (h.commute_rho x) hx hρx (h.inf_zpowers_rho hx)

theorem FpfNonab.sup_normal (h : FpfNonab S ρ) {x : S} (hx : orderOf x = 4) :
    (zpowers x ⊔ zpowers (ρ x)).Normal := by
  refine ⟨fun a ha g => ?_⟩
  have hmem : g * a * g⁻¹ * a⁻¹ ∈ zpowers x ⊔ zpowers (ρ x) :=
    h.center_le_sup hx (h.comm_mem g a)
  have hEq : g * a * g⁻¹ = (g * a * g⁻¹ * a⁻¹) * a := by group
  rw [hEq]
  exact (zpowers x ⊔ zpowers (ρ x)).mul_mem hmem ha

theorem FpfNonab.sup_invariant (h : FpfNonab S ρ) {x : S} (hx : orderOf x = 4) :
    ∀ a ∈ zpowers x ⊔ zpowers (ρ x), ρ a ∈ zpowers x ⊔ zpowers (ρ x) := by
  have hmap : (zpowers x ⊔ zpowers (ρ x)).map ρ.toMonoidHom ≤
      zpowers x ⊔ zpowers (ρ x) := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    apply sup_le
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers (ρ x))
    · rw [Subgroup.zpowers_le]
      change ρ (ρ x) ∈ zpowers x ⊔ zpowers (ρ x)
      have hbx : x * ρ x ∈ zpowers x ⊔ zpowers (ρ x) :=
        (zpowers x ⊔ zpowers (ρ x)).mul_mem
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers (ρ x)))
      have hburn := forall_mul_rho_rho_sq ρ h.cube h.fpf x
      have hρρ : ρ (ρ x) = (x * ρ x)⁻¹ := (mul_eq_one_iff_inv_eq.mp hburn).symm
      rw [hρρ]
      exact (zpowers x ⊔ zpowers (ρ x)).inv_mem hbx
  intro a ha
  have hmem : ρ a ∈ (zpowers x ⊔ zpowers (ρ x)).map ρ.toMonoidHom := ⟨a, ha, rfl⟩
  exact hmap hmem

theorem FpfNonab.centralizer_sup (h : FpfNonab S ρ) {x : S} (hx : orderOf x = 4) :
    centralizer ((zpowers x ⊔ zpowers (ρ x) : Subgroup S) : Set S) =
      zpowers x ⊔ zpowers (ρ x) := by
  let A : Subgroup S := zpowers x ⊔ zpowers (ρ x)
  let C : Subgroup S := centralizer (A : Set S)
  haveI hAcomm : IsMulCommutative ↥A := by
    obtain ⟨e⟩ := h.sup_equiv hx
    exact IsMulCommutative.of_comm fun a b => e.injective (by
      rw [map_mul, map_mul, mul_comm])
  have hAC : A ≤ C := Subgroup.le_centralizer A
  have hρ3 : ∀ y : S, ρ (ρ (ρ y)) = y := by
    intro y
    have hh := congrArg (fun f : MulAut S => f y) h.cube
    simpa [pow_succ, MulAut.mul_apply] using hh
  have hsupinv : ∀ a ∈ A, ρ a ∈ A := h.sup_invariant hx
  have hinv2 : ∀ a ∈ A, ρ (ρ a) ∈ A := fun a ha => hsupinv (ρ a) (hsupinv a ha)
  have hcardA : Nat.card A = 16 := h.card_sup hx
  have hinvC : ∀ c ∈ C, ρ c ∈ C := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro a ha
    have hb : ρ (ρ a) ∈ A := hinv2 a ha
    have hcb : ρ (ρ a) * c = c * ρ (ρ a) := hc (ρ (ρ a)) hb
    have h2 := congrArg ρ hcb
    simp only [map_mul] at h2
    rw [hρ3 a] at h2
    exact h2
  have hmodC : Nat.card C % 3 = 1 := card_mod_three_of_fpf ρ h.cube h.fpf C hinvC
  have hdvdC : Nat.card C ∣ 64 := by
    have hd := Subgroup.card_subgroup_dvd_card C
    rwa [h.card] at hd
  have h16dvd : 16 ∣ Nat.card C := by
    rw [← hcardA]
    exact Subgroup.card_dvd_of_le hAC
  have hdvd2 : Nat.card C ∣ 2 ^ 6 := by
    rw [show (2 : ℕ) ^ 6 = 64 by norm_num]
    exact hdvdC
  obtain ⟨k, hk6, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
  have hmodk : 2 ^ k % 3 = 1 := by rw [← hk]; exact hmodC
  have h16k : 16 ∣ 2 ^ k := by rw [← hk]; exact h16dvd
  have hC_cases : Nat.card C = 16 ∨ Nat.card C = 64 := by
    interval_cases k
    · norm_num at h16k
    · norm_num at h16k
    · norm_num at h16k
    · norm_num at h16k
    · left; rw [hk]; norm_num
    · norm_num at hmodk
    · right; rw [hk]; norm_num
  rcases hC_cases with hC16 | hC64
  · have hACeq : A = C := Subgroup.eq_of_le_of_card_ge hAC (by rw [hC16, hcardA])
    exact hACeq.symm
  · exfalso
    have htop : C = ⊤ := Subgroup.eq_top_of_card_eq (H := C) (by rw [hC64, h.card])
    have hAcen : A ≤ center S := by
      intro a ha
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ C := by rw [htop]; exact Subgroup.mem_top g
      exact ((Subgroup.mem_centralizer_iff.mp hg) a ha).symm
    have hdvd : 16 ∣ 4 := by
      rw [← hcardA, ← h.card_center]
      exact Subgroup.card_dvd_of_le hAcen
    norm_num at hdvd

theorem FpfNonab.exists_selfCentralizing_Z4Z4 (h : FpfNonab S ρ) :
    ∃ A : Subgroup S, A.Normal ∧ (∀ a ∈ A, ρ a ∈ A) ∧ Nonempty (↥A ≃* Z4Z4) ∧
      centralizer (A : Set S) = A := by
  obtain ⟨x, hx⟩ := h.exists_order_four
  exact ⟨zpowers x ⊔ zpowers (ρ x), h.sup_normal hx, h.sup_invariant hx, h.sup_equiv hx,
    h.centralizer_sup hx⟩

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
