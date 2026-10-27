module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L56L
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53E

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

theorem not_forall_commute_conjugate_Q (hD : Foote5AutData 𝕊 Lin)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) (hQ4 : Nat.card Q = 4)
    (hQsq : ∀ q ∈ Q, q * q = 1) {s : G} (hsN : s ∈ normalizer (S : Set G))
    (hbot : Q ⊓ conjugate Q s = ⊥) (hnf : ∀ v ∈ conjugate Q s, actG L ε v ∈ Lin) :
    ∃ v ∈ conjugate Q s, ∃ r ∈ S ⊓ L, v * r ≠ r * v := by
  classical
  by_contra hall
  push Not at hall
  have ht22 : t * t = 1 := by rw [← sq, ← h.t2, pow_orderOf_eq_one]
  have hnaR : ∃ a ∈ (h.Rbar ε : Subgroup 𝕊), ∃ b ∈ (h.Rbar ε : Subgroup 𝕊), a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hna
    exact ⟨_, h.psi_mem_Rbar ε ha, _, h.psi_mem_Rbar ε hb,
      fun h1 => hab ((h.psi_comm_iff ε ha hb).mp h1)⟩
  have hQsS := h.conjugate_Q_le hsN
  have hcase : ∀ v ∈ conjugate Q s, v = 1 ∨ v * t ∈ Q := by
    intro v hv
    have hvS := hQsS hv
    have hvN := h.S_le hvS
    have hv2 : v * v = 1 := conjugate_sq_eq_one hQsq hv
    have hfix : ∀ ρ ∈ (h.Rbar ε : Subgroup 𝕊), actG L ε v ρ = ρ :=
      (h.actG_fix_iff ε hvS).mpr (hall v hv)
    obtain ⟨c, hcR, hcZ, hc⟩ := hD.centralizer_sylow_lin (h.Rbar ε) hnaR _ (hnf v hv)
      ⟨1, by rw [pow_one, pow_two, ← actG_mul ε hvN hvN, hv2, actG_one]⟩ hfix
    obtain ⟨r, hr, rfl⟩ := (h.mem_Rbar_iff ε).mp hcR
    have hrZ : ∀ r' ∈ S ⊓ L, (r : G) * r' = r' * r := fun r' hr' =>
      (h.psi_comm_iff ε hr hr').mp (hcZ _ (h.psi_mem_Rbar ε hr'))
    rcases h.center_R hna hr hrZ with h1 | h1
    · left
      have hr1 : r = 1 := Subtype.ext h1
      rw [hr1, map_one, map_one] at hc
      have h2 : v ∈ Q ⊓ conjugate Q s :=
        mem_inf.mpr ⟨(h.actG_eq_one_iff_mem_Q ε hvS).mp hc, hv⟩
      rwa [hbot, mem_bot] at h2
    · right
      have hrt : r = ⟨t, h.tL⟩ := Subtype.ext h1
      rw [hrt, ← actG_of_mem_self ε h.tL] at hc
      rw [← h.actG_eq_one_iff_mem_Q ε (mul_mem hvS h.tS), actG_mul ε hvN (h.S_le h.tS), hc,
        ← actG_mul ε (h.S_le h.tS) (h.S_le h.tS), ht22, actG_one]
  have hcard : Nat.card (conjugate Q s) ≤ 2 := by
    by_cases hex : ∃ v₀ ∈ conjugate Q s, v₀ * t ∈ Q
    · obtain ⟨v₀, hv₀, hv₀t⟩ := hex
      have hsub : ∀ v ∈ conjugate Q s, v ∈ ({1, v₀} : Finset G) := by
        intro v hv
        rcases hcase v hv with h1 | h1
        · rw [h1]
          exact Finset.mem_insert_self _ _
        · have h2 : v * v₀⁻¹ ∈ Q ⊓ conjugate Q s := by
            refine mem_inf.mpr ⟨?_, mul_mem hv (inv_mem hv₀)⟩
            rw [show v * v₀⁻¹ = (v * t) * (v₀ * t)⁻¹ by group]
            exact mul_mem h1 (inv_mem hv₀t)
          rw [hbot, mem_bot, mul_inv_eq_one] at h2
          rw [h2]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      exact (SmallLocal.card_le_of_forall_mem_finset _ hsub).trans Finset.card_le_two
    · push Not at hex
      have hsub : ∀ v ∈ conjugate Q s, v ∈ ({1} : Finset G) := by
        intro v hv
        rcases hcase v hv with h1 | h1
        · rw [h1]
          exact Finset.mem_singleton_self _
        · exact absurd h1 (hex v hv)
      exact (SmallLocal.card_le_of_forall_mem_finset _ hsub).trans (by simp)
  rw [card_conjugate_eq_card, hQ4] at hcard
  omega

theorem t_mem_conjugate_Q (hD : Foote5AutData 𝕊 Lin)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) (hQ4 : Nat.card Q = 4)
    (hQsq : ∀ q ∈ Q, q * q = 1) {s : G} (hsN : s ∈ normalizer (S : Set G))
    (hbot : Q ⊓ conjugate Q s = ⊥) (hnf : ∀ v ∈ conjugate Q s, actG L ε v ∈ Lin) :
    t ∈ conjugate Q s := by
  obtain ⟨v, hv, r, hr, hvr⟩ := h.not_forall_commute_conjugate_Q ε hD hna hQ4 hQsq hsN hbot hnf
  have hQsS := h.conjugate_Q_le hsN
  have hvS := hQsS hv
  have hcN : v * r * v⁻¹ * r⁻¹ ∈ conjugate Q s ⊓ (S ⊓ L) := by
    refine mem_inf.mpr ⟨?_, mul_mem (h.conj_mem_R hvS hr) (inv_mem hr)⟩
    rw [show v * r * v⁻¹ * r⁻¹ = v * (r * v⁻¹ * r⁻¹) by group]
    exact mul_mem hv (h.conj_mem_conjugate_Q hsN (mem_inf.mp hr).1 (inv_mem hv))
  have hNne : conjugate Q s ⊓ (S ⊓ L) ≠ ⊥ := by
    intro h1
    rw [h1, mem_bot] at hcN
    apply hvr
    calc v * r = v * r * v⁻¹ * r⁻¹ * (r * v) := by group
      _ = r * v := by rw [hcN, one_mul]
  have hSN : S ≤ normalizer ((conjugate Q s ⊓ (S ⊓ L) : Subgroup G) : Set G) :=
    le_normalizer_of_conj_mem fun g hg y hy => mem_inf.mpr
      ⟨h.conj_mem_conjugate_Q hsN hg (mem_inf.mp hy).1, h.conj_mem_R hg (mem_inf.mp hy).2⟩
  obtain ⟨u, huN, hu2, huS⟩ :=
    exists_involution_center h.isPGroup_S (inf_le_left.trans hQsS) hSN hNne
  have huR : u ∈ S ⊓ L := (mem_inf.mp huN).2
  rcases h.center_R hna huR (fun r' hr' => (huS r' (mem_inf.mp hr').1).symm) with h1 | h1
  · rw [h1, orderOf_one] at hu2
    omega
  · rw [← h1]
    exact (mem_inf.mp huN).1

theorem inf_conjugate_R_eq_bot_of_t_mem (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a)
    {s : G} (hsN : s ∈ normalizer (S : Set G)) (htQs : t ∈ conjugate Q s) :
    S ⊓ L ⊓ conjugate (S ⊓ L) s = ⊥ :=
  h.inf_conjugate_R_eq_bot hna hsN fun h1 => h.t_not_mem_Q (by
    have h2 := mem_conjugate_iff.mp htQs
    rwa [h1] at h2)

include ε in
theorem nonempty_R_equiv_dihedral_four (hD : Foote5AutData 𝕊 Lin)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) (hQsq : ∀ q ∈ Q, q * q = 1) {s : G}
    (hsN : s ∈ normalizer (S : Set G)) (hRs : S ⊓ L ⊓ conjugate (S ⊓ L) s = ⊥) :
    Nonempty (↥(S ⊓ L) ≃* DihedralGroup 4) := by
  obtain ⟨m, hm1, ⟨e⟩⟩ := h.exists_dihedral_R
  have hRsS : conjugate (S ⊓ L) s ≤ S := conjugate_le_of_mem_normalizer hsN inf_le_left
  have hcent : ∀ a ∈ conjugate (S ⊓ L) s, ∀ r ∈ S ⊓ L, a * r = r * a :=
    fun a ha r hr => h.commute_of_inf_conjugate_eq_bot hsN hRs hr ha
  have hsq : ∀ a ∈ S ⊓ L, ∀ b ∈ S ⊓ L,
      a * b * a⁻¹ * b⁻¹ * (a * b * a⁻¹ * b⁻¹) = 1 := by
    intro a ha b hb
    have hconj : ∀ c ∈ S ⊓ L, s⁻¹ * c * s ∈ conjugate (S ⊓ L) s := fun c hc => by
      rw [mem_conjugate_iff, show s * (s⁻¹ * c * s) * s⁻¹ = c by group]
      exact hc
    have h1 := hQsq _ (h.commutator_mem_Q_of_centralizes ε hD hRsS hcent (hconj a ha)
      (hconj b hb))
    calc a * b * a⁻¹ * b⁻¹ * (a * b * a⁻¹ * b⁻¹) =
        s * ((s⁻¹ * a * s) * (s⁻¹ * b * s) * (s⁻¹ * a * s)⁻¹ * (s⁻¹ * b * s)⁻¹ *
          ((s⁻¹ * a * s) * (s⁻¹ * b * s) * (s⁻¹ * a * s)⁻¹ * (s⁻¹ * b * s)⁻¹)) * s⁻¹ := by
          group
      _ = 1 := by rw [h1]; group
  have hm2 : m = 2 := by
    by_contra hm
    rcases (show m = 1 ∨ 3 ≤ m by omega) with rfl | hm3
    · obtain ⟨a, ha, b, hb, hab⟩ := hna
      apply hab
      have hcomm : ∀ x y : DihedralGroup (2 ^ 1), x * y = y * x := by decide
      have h1 := hcomm (e ⟨a, ha⟩) (e ⟨b, hb⟩)
      rw [← map_mul, ← map_mul] at h1
      exact congrArg Subtype.val (e.injective h1)
    · have h1 := hsq _ (e.symm (DihedralGroup.r 1)).2 _ (e.symm (DihedralGroup.sr 0)).2
      have h2 : (DihedralGroup.r 1 * DihedralGroup.sr 0 * (DihedralGroup.r 1)⁻¹ *
          (DihedralGroup.sr 0)⁻¹ : DihedralGroup (2 ^ m)) = DihedralGroup.r 2 := by
        simp only [DihedralGroup.r_mul_sr, DihedralGroup.inv_r, DihedralGroup.sr_mul_r,
          DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr]
        congr 1
        ring
      have h3 : (DihedralGroup.r 2 * DihedralGroup.r 2 : DihedralGroup (2 ^ m)) ≠ 1 := by
        rw [DihedralGroup.r_mul_r, DihedralGroup.one_def]
        intro h4
        have h5 : ((4 : ℕ) : ZMod (2 ^ m)) = 0 := by
          have := (DihedralGroup.r.injEq _ _).mp h4
          rw [show (2 : ZMod (2 ^ m)) + 2 = ((4 : ℕ) : ZMod (2 ^ m)) by push_cast; ring]
            at this
          exact this
        rw [ZMod.natCast_eq_zero_iff] at h5
        have h6 : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
        have h7 := Nat.le_of_dvd (by norm_num) h5
        omega
      apply h3
      rw [← h2]
      apply e.symm.injective
      rw [map_one]
      apply Subtype.ext
      simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
        OneMemClass.coe_one] using h1
  subst hm2
  exact ⟨e⟩

end Sec5

end CFSG.ComponentClassification.Foote5
