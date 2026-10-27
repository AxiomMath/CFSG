module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5TypesB
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mulAut_mul_conj_mul_inv {Y : Type*} [Group Y] (α : MulAut Y) (s : Y) :
    α * MulAut.conj s * α⁻¹ = MulAut.conj (α s) := by
  ext g
  simp [MulAut.mul_apply, MulAut.conj_apply]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

theorem nonabelian_R_of_fix (hD : Foote5AutData 𝕊 Lin) {β : MulAut 𝕊} (hβ : β ∉ Lin)
    (hβ2 : β * β = 1) (hfix : ∀ ρ ∈ (h.Rbar ε : Subgroup 𝕊), β ρ = ρ) :
    ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hab
  have hab' : ∀ a ∈ S ⊓ L, ∀ b ∈ S ⊓ L, a * b = b * a := by
    intro a ha b hb
    by_contra hne
    exact hab ⟨a, ha, b, hb, hne⟩
  have hRab : ∀ a ∈ (h.Rbar ε : Subgroup 𝕊), ∀ b ∈ (h.Rbar ε : Subgroup 𝕊), a * b = b * a := by
    intro a ha b hb
    obtain ⟨r₁, hr₁, rfl⟩ := (h.mem_Rbar_iff ε).mp ha
    obtain ⟨r₂, hr₂, rfl⟩ := (h.mem_Rbar_iff ε).mp hb
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hab' _ hr₁ _ hr₂)
  set I := (h.Rbar ε : Subgroup 𝕊).map (MulAut.conj : 𝕊 →* MulAut 𝕊) with hI
  have hI2 : IsPGroup 2 I := (h.Rbar ε).isPGroup'.map _
  have hβC : β ∈ centralizer (I : Set (MulAut 𝕊)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨ρ, hρ, rfl⟩
    have h1 := mulAut_mul_conj_mul_inv β ρ
    rw [hfix ρ hρ] at h1
    calc MulAut.conj ρ * β = β * MulAut.conj ρ * β⁻¹ * β := by rw [h1]
      _ = β * MulAut.conj ρ := by group
  have hβ2' : IsPGroup 2 (zpowers β) := by
    have h1 : orderOf β ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, sq]; exact hβ2)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  have hcomm : ∀ α ∈ I, β * α * β⁻¹ = α := fun α hα => by
    rw [(mem_centralizer_iff.mp hβC α hα).symm, mul_inv_cancel_right]
  have hβN : β ∈ normalizer (I : Set (MulAut 𝕊)) := mem_normalizer_iff.mpr fun α =>
    ⟨fun hα => by rw [hcomm α hα]; exact hα, fun hα => by
      have h1 := hcomm _ hα
      have h2 : α = β * α * β⁻¹ := by
        calc α = β⁻¹ * (β * α * β⁻¹) * β := by group
          _ = β⁻¹ * (β * (β * α * β⁻¹) * β⁻¹) * β := by rw [h1]
          _ = β * α * β⁻¹ := by group
      rw [h2]
      exact hα⟩
  have hP2 : IsPGroup 2 ↥(I ⊔ zpowers β) :=
    hI2.to_sup_of_normal_left' hβ2' (zpowers_le.mpr hβN)
  have hPfix : ∀ α ∈ I ⊔ zpowers β, ∀ ρ ∈ (h.Rbar ε : Subgroup 𝕊), α ρ = ρ := by
    intro α hα
    have hle : I ⊔ zpowers β ≤ fixingSubgroup (MulAut 𝕊) ((h.Rbar ε : Subgroup 𝕊) :
        Set 𝕊) := by
      refine sup_le ?_ (zpowers_le.mpr ?_)
      · rintro _ ⟨ρ', hρ', rfl⟩
        rw [mem_fixingSubgroup_iff]
        intro ρ hρ
        rw [MulAut.smul_def, MulAut.conj_apply, hRab ρ' hρ' ρ hρ, mul_inv_cancel_right]
      · rw [mem_fixingSubgroup_iff]
        intro ρ hρ
        rw [MulAut.smul_def]
        exact hfix ρ hρ
    intro ρ hρ
    have h1 := (mem_fixingSubgroup_iff _).mp (hle hα) ρ hρ
    rwa [MulAut.smul_def] at h1
  have h4 := (hD.centralizer_sylow (h.Rbar ε) _ hP2 hPfix).2
  have hinj : Function.Injective (MulAut.conj : 𝕊 →* MulAut 𝕊) := by
    intro a b hab
    have hZ := h.center_eq_bot ε
    have h1 : b⁻¹ * a ∈ center 𝕊 := by
      rw [mem_center_iff]
      intro g
      have h2 := congrArg (fun φ : MulAut 𝕊 => φ g) hab
      simp only [MulAut.conj_apply] at h2
      calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
        _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [h2]
        _ = b⁻¹ * a * g := by group
    rw [hZ, mem_bot, inv_mul_eq_one] at h1
    exact h1.symm
  have hIcard : Nat.card I = Nat.card ↥(S ⊓ L) := by
    rw [hI, card_map_of_injective hinj, h.card_Rbar ε]
  have hβI : β ∉ I := fun hβ' => by
    obtain ⟨ρ, -, hρ⟩ := hβ'
    exact hβ (hρ ▸ hD.inn_le ⟨ρ, rfl⟩)
  have hlt : I < I ⊔ zpowers β :=
    lt_of_le_of_ne le_sup_left fun h1 => hβI (h1 ▸ mem_sup_right (mem_zpowers β))
  have hdvd := card_dvd_of_le hlt.le
  have hlt' := card_lt_of_lt hlt
  obtain ⟨k, hk⟩ := hdvd
  have hk2 : 2 ≤ k := by
    by_contra hk2
    have h1 : Nat.card ↥(I ⊔ zpowers β) ≤ Nat.card I := by
      calc Nat.card ↥(I ⊔ zpowers β) = Nat.card I * k := hk
        _ ≤ Nat.card I * 1 := Nat.mul_le_mul_left _ (by omega)
        _ = Nat.card I := mul_one _
    omega
  have h8 : 2 * Nat.card I ≤ Nat.card ↥(I ⊔ zpowers β) := by
    rw [hk, mul_comm]
    exact Nat.mul_le_mul_left _ hk2
  have hR4 := h.four_le_card_R
  omega

theorem exists_inner_action (hD : Foote5AutData 𝕊 Lin) {y : G} (hyS : y ∈ S) (hy2 : y * y = 1)
    (hnpgl : ¬ (actG L ε y ∈ Lin ∧ actG L ε y ∉ innAut5 𝕊)) :
    ∃ r₀ ∈ S ⊓ L, r₀ * r₀ = 1 ∧ ∀ r ∈ S ⊓ L, y * r * y⁻¹ = r₀ * r * r₀⁻¹ := by
  have hyN := h.S_le hyS
  have hsq : actG L ε y * actG L ε y = 1 := by rw [← actG_mul ε hyN hyN, hy2, actG_one]
  by_cases hinn : actG L ε y ∈ innAut5 𝕊
  · obtain ⟨q, hq, r₀, hr₀, rfl⟩ := h.exists_mul_of_inner ε hyS hinn
    have hqr := h.commute_Q_R hq hr₀
    have hqq : q * q = 1 := by
      have h1 : q * q * (r₀ * r₀) = 1 := by
        rw [← hy2, show q * r₀ * (q * r₀) = q * (r₀ * q) * r₀ by group, ← hqr]
        group
      have h2 : q * q ∈ Q ⊓ L := by
        refine mem_inf.mpr ⟨mul_mem hq hq, ?_⟩
        rw [eq_inv_of_mul_eq_one_left h1]
        exact inv_mem (mul_mem (mem_inf.mp hr₀).2 (mem_inf.mp hr₀).2)
      rw [h.Q_inf_L, mem_bot] at h2
      exact h2
    refine ⟨r₀, hr₀, ?_, fun r hr => ?_⟩
    · rw [← hy2, show q * r₀ * (q * r₀) = q * (r₀ * q) * r₀ by group, ← hqr,
        show q * (q * r₀) * r₀ = q * q * (r₀ * r₀) by group, hqq, one_mul]
    · have h1 : r₀ * r * r₀⁻¹ ∈ S ⊓ L := h.conj_mem_R (mem_inf.mp hr₀).1 hr
      have h2 := h.commute_Q_R hq h1
      calc q * r₀ * r * (q * r₀)⁻¹ = q * (r₀ * r * r₀⁻¹) * q⁻¹ := by group
        _ = r₀ * r * r₀⁻¹ * q * q⁻¹ := by rw [h2]
        _ = r₀ * r * r₀⁻¹ := by group
  · have hlin : actG L ε y ∉ Lin := fun h1 => hnpgl ⟨h1, hinn⟩
    obtain ⟨ρ₀, hρ₀, hρ₀2, hact⟩ :=
      hD.field_inner (h.Rbar ε) _ hlin hsq (h.actG_map_Rbar ε hyS)
    obtain ⟨r₀', hr₀, rfl⟩ := (h.mem_Rbar_iff ε).mp hρ₀
    refine ⟨r₀', hr₀, ?_, fun r hr => ?_⟩
    · have h1 : psi L ε ⟨(r₀' : G) * r₀', (mem_inf.mp (mul_mem hr₀ hr₀)).2⟩ =
          psi L ε ⟨1, one_mem _⟩ := by
        show psi L ε (r₀' * r₀') = psi L ε 1
        rw [map_mul, hρ₀2, map_one]
      exact h.eq_of_psi_eq ε (mul_mem hr₀ hr₀) (one_mem _) h1
    · have h1 := hact _ (h.psi_mem_Rbar ε hr)
      rw [actG_psi ε hyN] at h1
      have hmem : (r₀' : G) * r * (r₀' : G)⁻¹ ∈ S ⊓ L :=
        h.conj_mem_R (mem_inf.mp hr₀).1 hr
      refine h.eq_of_psi_eq ε (h.conj_mem_R hyS hr) hmem ?_
      rw [h1, ← map_inv, ← map_mul, ← map_mul]
      rfl

include ε in
theorem exists_conj_mul_t (hD : Foote5AutData 𝕊 Lin) {y : G} (hyS : y ∈ S) (hy2 : y * y = 1)
    (hyR : ∃ r ∈ S ⊓ L, r * y ≠ y * r) : ∃ c ∈ S ⊓ L, c⁻¹ * y * c = y * t := by
  have hyN := h.S_le hyS
  have hsq : actG L ε y * actG L ε y = 1 := by rw [← actG_mul ε hyN hyN, hy2, actG_one]
  by_cases hpgl : actG L ε y ∈ Lin ∧ actG L ε y ∉ innAut5 𝕊
  · obtain ⟨w, hwR, hw1, hwy, c, hcR, hc⟩ := exists_conj_mul_of_not_commute h.R_sylow.isPGroup
      hy2 (h.S_le_normalizer_R hyS) hyR
    refine ⟨c, hcR, ?_⟩
    rw [hc]
    congr 1
    have hfix2 := hD.pgl_fixed (h.Rbar ε) _ hpgl.1 hpgl.2 hsq (h.actG_map_Rbar ε hyS)
    have hfixed : ∀ r (hr : r ∈ S ⊓ L), r * y = y * r → psi L ε ⟨r, (mem_inf.mp hr).2⟩ ∈
        ((h.Rbar ε : Subgroup 𝕊) ⊓ MonoidHom.eqLocus (actG L ε y).toMonoidHom
          (MonoidHom.id 𝕊)) := by
      intro r hr hry
      refine mem_inf.mpr ⟨h.psi_mem_Rbar ε hr, ?_⟩
      show actG L ε y (psi L ε ⟨r, (mem_inf.mp hr).2⟩) = psi L ε ⟨r, (mem_inf.mp hr).2⟩
      rw [actG_psi ε hyN]
      congr 1
      apply Subtype.ext
      change y * r * y⁻¹ = r
      rw [← hry, mul_inv_cancel_right]
    by_contra hwt
    have hne1 : ∀ r (hr : r ∈ S ⊓ L), r ≠ 1 → psi L ε ⟨r, (mem_inf.mp hr).2⟩ ≠ 1 := by
      intro r hr hr1 h1
      apply hr1
      have h2 : psi L ε ⟨r, (mem_inf.mp hr).2⟩ = psi L ε ⟨1, one_mem _⟩ := by
        rw [h1]
        exact (map_one (psi L ε)).symm
      exact h.eq_of_psi_eq ε hr (one_mem _) h2
    have h3 := three_le_card_of_ne (hfixed w hwR hwy) (hfixed t h.tR (h.tZ y hyS).symm)
      (hne1 w hwR hw1) (hne1 t h.tR h.t_ne_one)
      (fun h1 => hwt (h.eq_of_psi_eq ε hwR h.tR h1))
    omega
  · obtain ⟨r₀, hr₀, hr₀2, hact⟩ := h.exists_inner_action ε hD hyS hy2 hpgl
    have hr₀i : r₀⁻¹ = r₀ := inv_eq_of_mul_eq_one_right hr₀2
    obtain ⟨r, hr, hry⟩ := hyR
    have hr₀r : r₀ * r * r₀⁻¹ ≠ r := fun h1 => hry (by
      calc r * y = y * (y⁻¹ * r * y) := by group
        _ = y * r := by
          congr 1
          have h2 := hact (y⁻¹ * r * y) (by
            have h3 := h.conj_mem_R (inv_mem hyS) hr
            rwa [inv_inv] at h3)
          rw [show y * (y⁻¹ * r * y) * y⁻¹ = r by group] at h2
          calc y⁻¹ * r * y = r₀⁻¹ * (r₀ * (y⁻¹ * r * y) * r₀⁻¹) * r₀ := by group
            _ = r₀⁻¹ * r * r₀ := by rw [← h2]
            _ = r₀⁻¹ * (r₀ * r * r₀⁻¹) * r₀ := by rw [h1]
            _ = r := by group)
    have hyinv : ∀ x ∈ S ⊓ L, y⁻¹ * x * y = r₀⁻¹ * x * r₀ := by
      intro x hx
      have h3 := h.conj_mem_R (inv_mem hyS) hx
      rw [inv_inv] at h3
      have h2 := hact _ h3
      rw [show y * (y⁻¹ * x * y) * y⁻¹ = x by group] at h2
      calc y⁻¹ * x * y = r₀⁻¹ * (r₀ * (y⁻¹ * x * y) * r₀⁻¹) * r₀ := by group
        _ = r₀⁻¹ * x * r₀ := by rw [← h2]
    obtain ⟨m, -, ⟨e⟩⟩ := h.exists_dihedral_R
    have hcomm' : (⟨r₀, hr₀⟩ : ↥(S ⊓ L)) * ⟨r, hr⟩ ≠ ⟨r, hr⟩ * ⟨r₀, hr₀⟩ := fun h1 => hr₀r (by
      have h2 : r₀ * r = r * r₀ := congrArg Subtype.val h1
      rw [h2, mul_inv_cancel_right])
    have hm2 : 2 ≤ m := by
      by_contra hm
      have hcomm : IsMulCommutative (DihedralGroup (2 ^ m)) :=
        DihedralGroup.commutative_iff.mpr (by interval_cases m <;> simp)
      apply hcomm'
      apply e.injective
      rw [map_mul, map_mul]
      exact hcomm.is_comm.comm _ _
    set d := e ⟨r₀, hr₀⟩ with hd
    have hd2 : d * d = 1 := by
      rw [hd, ← map_mul, ← map_one e]
      congr 1
      exact Subtype.ext hr₀2
    have hdc : d ∉ center (DihedralGroup (2 ^ m)) := fun hdZ => by
      apply hcomm'
      apply e.injective
      rw [map_mul, map_mul, ← hd]
      exact mem_center_iff.mp hdZ (e ⟨r, hr⟩) |>.symm
    have key := dihedral_conj_eq_mul hm2 hd2 hdc
    set ρD := DihedralGroup.r ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) with hρD
    set τD := DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) with hτD
    have hτc : τD ∈ center (DihedralGroup (2 ^ m)) := by
      have h2 : 2 ^ m ≠ 2 := by
        have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right two_pos hm2
        omega
      rw [DihedralGroup.center_eq_closure_of_even_ne_two
        (Nat.even_pow.mpr ⟨even_two, by omega⟩) h2]
      rw [show 2 ^ m / 2 = 2 ^ (m - 1) by
        rw [show m = m - 1 + 1 by omega, pow_succ, Nat.mul_div_cancel _ two_pos]; rfl]
      exact mem_zpowers _
    have hτ : ((e.symm τD : ↥(S ⊓ L)) : G) = t := by
      have hτZ : ∀ x ∈ S ⊓ L, ((e.symm τD : ↥(S ⊓ L)) : G) * x = x * (e.symm τD : ↥(S ⊓ L)) := by
        intro x hx
        have h3 := mem_center_iff.mp hτc (e ⟨x, hx⟩)
        have h4 := congrArg e.symm h3
        rw [map_mul, map_mul, e.symm_apply_apply] at h4
        exact (congrArg Subtype.val h4).symm
      rcases h.center_R ⟨r₀, hr₀, r, hr, fun h1 => hr₀r (by rw [h1, mul_inv_cancel_right])⟩
        (e.symm τD).2 hτZ with h1 | h1
      · exfalso
        have h2 : e.symm τD = 1 := Subtype.ext h1
        have h3 : τD = 1 := by rw [← e.apply_symm_apply τD, h2, map_one]
        rw [hτD, DihedralGroup.one_def] at h3
        have h4 := DihedralGroup.r.inj h3
        rw [ZMod.natCast_eq_zero_iff] at h4
        have h5 := Nat.le_of_dvd (by positivity) h4
        have : 2 ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
        omega
      · exact h1
    set c : G := ((e.symm ρD : ↥(S ⊓ L)) : G) with hc
    have hcR : c ∈ S ⊓ L := (e.symm ρD).2
    have hkey : r₀ * c * r₀⁻¹ = c * t := by
      have h3 := congrArg (fun x => ((e.symm x : ↥(S ⊓ L)) : G)) key
      simp only [map_mul, map_inv, hd, e.symm_apply_apply, coe_mul, coe_inv] at h3
      rw [← hτ]
      exact h3
    refine ⟨c, hcR, ?_⟩
    have ht2 : t * t = 1 := by rw [← sq, ← h.t2, pow_orderOf_eq_one]
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    have h5 : y⁻¹ * c⁻¹ * y = (c * t)⁻¹ := by
      rw [show y⁻¹ * c⁻¹ * y = (y⁻¹ * c * y)⁻¹ by group, hyinv c hcR, hr₀i, ← hkey, hr₀i]
    calc c⁻¹ * y * c = y * (y⁻¹ * c⁻¹ * y) * c := by group
      _ = y * t := by rw [h5, mul_inv_rev, hti]; group

end Sec5

end CFSG.ComponentClassification.Foote5
