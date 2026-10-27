module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C6Elt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C3Ord

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

open Subgroup

open scoped Pointwise

variable {G : Type} [Group G] {E B : Subgroup G} {u : MulAut ↥E}
  {A H P : Subgroup (MulAut ↥E)}

theorem HCtx.card_le_eight (hInv : Sec8T84FactInv) (S : HCtx E B u A H) (O : OddNormal H P)
    (hc : ∀ h ∈ H, h * u * h⁻¹ * u⁻¹ ∈ P) {R : Subgroup (MulAut ↥E)} (hRH : R ≤ H)
    (hR2 : ∀ r ∈ R, r * r = 1) : Nat.card ↥R ≤ 8 := by
  classical
  haveI : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [S.hE.2]; norm_num)
  haveI : Finite (MulAut ↥E) := inferInstance
  haveI : Finite ↥P := OddNormal.finite O
  let C : Subgroup (MulAut ↥E) := A ⊔ zpowers u
  have hCH : C ≤ H := sup_le S.A_H (Subgroup.zpowers_le.mpr S.u_H)
  have hAcent : A ≤ Subgroup.centralizer ({u} : Set (MulAut ↥E)) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact S.A_comm a ha
  have hZcent : Subgroup.zpowers u ≤ Subgroup.centralizer ({u} : Set (MulAut ↥E)) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hCcent : C ≤ Subgroup.centralizer ({u} : Set (MulAut ↥E)) := sup_le hAcent hZcent
  have hPC : P ⊓ C = ⊥ := by
    apply le_antisymm
    · intro p hp
      rw [Subgroup.mem_bot]
      have hcomm : p * u = u * p :=
        Subgroup.mem_centralizer_singleton_iff.mp (hCcent hp.2)
      exact HCtx.cent_P S O p hp.1 hcomm
    · exact bot_le
  have hRP : R ⊓ P = ⊥ := by
    apply le_antisymm
    · intro y hy
      rw [Subgroup.mem_bot]
      have hdvd2 : orderOf y ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hR2 y hy.1)
      have hne2 : orderOf y ≠ 2 :=
        O.odd.ne_two_of_dvd_nat (Subgroup.orderOf_dvd_natCard P hy.2)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
      · exact orderOf_eq_one_iff.mp h
      · exact absurd h hne2
    · exact bot_le
  have hRn : R ≤ Subgroup.normalizer (P : Set (MulAut ↥E)) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro p
    constructor
    · intro hp; exact O.norm r (hRH hr) p hp
    · intro hp
      have h1 := O.norm r⁻¹ (H.inv_mem (hRH hr)) (r * p * r⁻¹) hp
      have h2 : r⁻¹ * (r * p * r⁻¹) * (r⁻¹)⁻¹ = p := by group
      rwa [h2] at h1
  let RC : Subgroup (MulAut ↥E) := (R ⊔ P) ⊓ C
  have hRCn : RC ≤ Subgroup.normalizer (P : Set (MulAut ↥E)) :=
    le_trans inf_le_left (sup_le hRn Subgroup.le_normalizer)
  have hRCP : RC ⊓ P = ⊥ := by
    apply le_antisymm
    · intro y hy
      rw [Subgroup.mem_bot]
      have hyC : y ∈ C := hy.1.2
      have hyP : y ∈ P := hy.2
      have hmem : y ∈ (⊥ : Subgroup (MulAut ↥E)) := by
        rw [← hPC]
        exact ⟨hyP, hyC⟩
      exact Subgroup.mem_bot.mp hmem
    · exact bot_le
  have hcard1 : Nat.card ↥(R ⊔ P) = Nat.card ↥R * Nat.card ↥P := by
    have h := card_sup_mul_card_inf_of_le_normalizer (A := R) (B := P) hRn
    rw [hRP, Subgroup.card_bot, mul_one] at h
    exact h
  have hcard2 : Nat.card ↥(RC ⊔ P) = Nat.card ↥RC * Nat.card ↥P := by
    have h := card_sup_mul_card_inf_of_le_normalizer (A := RC) (B := P) hRCn
    rw [hRCP, Subgroup.card_bot, mul_one] at h
    exact h
  have hRle : R ≤ RC ⊔ P := by
    intro r hr
    obtain ⟨p, hp, c, hcH, hcu, hpc⟩ := S.exists_decomp O hc r (hRH hr)
    have hcC : c ∈ C := S.cent c hcH hcu
    have hcRP : c ∈ R ⊔ P := by
      have hceq : c = p⁻¹ * r := by rw [hpc]; group
      rw [hceq, show R ⊔ P = P ⊔ R from sup_comm R P]
      exact mul_mem_sup (P.inv_mem hp) hr
    have hcRC : c ∈ RC := ⟨hcRP, hcC⟩
    rw [hpc, show RC ⊔ P = P ⊔ RC from sup_comm RC P]
    exact mul_mem_sup hp hcRC
  have hsup : R ⊔ P = RC ⊔ P := by
    apply le_antisymm
    · exact sup_le hRle le_sup_right
    · exact sup_le inf_le_left le_sup_right
  have hcardEq : Nat.card ↥R = Nat.card ↥RC := by
    have h1 := hcard1
    have h2 := hcard2
    rw [hsup] at h1
    rw [h1] at h2
    exact Nat.mul_right_cancel (Nat.card_pos (α := ↥P)) h2
  have hRC2 : ∀ c ∈ RC, c * c = 1 := by
    intro c hc
    have hcC : c ∈ C := hc.2
    have hcRP : c ∈ R ⊔ P := hc.1
    have hmem : c ∈ (R : Set (MulAut ↥E)) * (P : Set (MulAut ↥E)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right R P hRn]
      exact hcRP
    obtain ⟨r, hr, p, hp, hc_eq⟩ := Set.mem_mul.mp hmem
    rw [← hc_eq] at hcC ⊢
    have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right (hR2 r hr)
    have hccP : (r * p) * (r * p) ∈ P := by
      have heq : (r * p) * (r * p) = (r * p * r⁻¹) * p := by rw [hrinv]; group
      rw [heq]
      exact P.mul_mem (O.norm r (hRH hr) p hp) hp
    have hccC : (r * p) * (r * p) ∈ C := C.mul_mem hcC hcC
    have hmem2 : (r * p) * (r * p) ∈ (⊥ : Subgroup (MulAut ↥E)) := by
      rw [← hPC]
      exact ⟨hccP, hccC⟩
    exact Subgroup.mem_bot.mp hmem2
  have hle8 : Nat.card ↥RC ≤ 8 :=
    HCtx.card_le_eight_of_le_C hInv S (show RC ≤ A ⊔ zpowers u from inf_le_right) hRC2
  rw [hcardEq]
  exact hle8

end C10

end CFSG.OddStandard.SmallF3.Omega
