module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankOneRoot

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K]

theorem gcd_sq_sub_one (q : ℕ) (hq : 1 ≤ q) :
    Nat.gcd (q ^ 2 - 1) (2 * q - 1) = Nat.gcd 3 (q + 1) := by
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have hsq : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    zify [hq, hq2]
    ring
  apply Nat.dvd_antisymm
  ·
    set d := Nat.gcd (q ^ 2 - 1) (2 * q - 1) with hd
    have h1 : d ∣ (2 * q + 1) * (2 * q - 1) := Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) _
    have h2 : d ∣ 4 * (q ^ 2 - 1) := Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) _
    have h3 : (2 * q + 1) * (2 * q - 1) = 4 * (q ^ 2 - 1) + 3 := by
      have h2q : 1 ≤ 2 * q := by omega
      zify [h2q, hq2]
      ring
    have hd3 : d ∣ 3 := by
      rw [h3] at h1
      exact (Nat.dvd_add_right h2).mp h1
    have h4 : 2 * (q + 1) = (2 * q - 1) + 3 := by omega
    have hd2 : d ∣ 2 * (q + 1) := by
      rw [h4]
      exact Nat.dvd_add (Nat.gcd_dvd_right _ _) hd3
    have hcop : Nat.Coprime d 2 := by
      have := Nat.Coprime.coprime_dvd_left hd3 (by norm_num : Nat.Coprime 3 2)
      exact this
    exact Nat.dvd_gcd hd3 (hcop.dvd_of_dvd_mul_left hd2)
  · set e := Nat.gcd 3 (q + 1) with he
    have he3 : e ∣ 3 := Nat.gcd_dvd_left _ _
    have heq : e ∣ q + 1 := Nat.gcd_dvd_right _ _
    refine Nat.dvd_gcd ?_ ?_
    · rw [hsq]
      exact Dvd.dvd.mul_right heq _
    · have h4 : 2 * q - 1 = 2 * (q + 1) - 3 := by omega
      rw [h4]
      exact Nat.dvd_sub (Dvd.dvd.mul_left heq 2) he3

section Chi

variable (h : UnitaryFieldData p f K)

theorem coe_rkOneChi (s : Kˣ) : (rkOneChi h s : K) = h.bar s ^ 2 / s := by
  change ((Units.map (h.bar : K →* K) s ^ 2 * s⁻¹ : Kˣ) : K) = _
  rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, Units.val_inv_eq_inv_val,
    div_eq_mul_inv]
  rfl

theorem norm_rkOneChi (s : Kˣ) : h.norm (rkOneChi h s : K) = h.norm s := by
  have hs : (s : K) ≠ 0 := s.ne_zero
  have hbs : h.bar (s : K) ≠ 0 := (map_ne_zero h.bar).mpr hs
  rw [coe_rkOneChi, UnitaryFieldData.norm, UnitaryFieldData.norm, map_div₀, map_pow, h.bar_bar]
  field_simp

theorem rkOneChi_eq_pow (s : Kˣ) : rkOneChi h s = s ^ (2 * p ^ f - 1) := by
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
  refine Units.ext ?_
  rw [coe_rkOneChi, UnitaryFieldData.bar_apply, Units.val_pow_eq_pow_val,
    pow_sub₀ _ s.ne_zero (by omega), pow_one, ← pow_mul, mul_comm, div_eq_mul_inv]

theorem rkOneM_eq_zpowers {g : Kˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    rkOneM h = Subgroup.zpowers (g ^ (2 * p ^ f - 1)) := by
  have hcomm : ∀ k : ℤ, (g ^ (2 * p ^ f - 1)) ^ k = (g ^ k) ^ (2 * p ^ f - 1) := fun k => by
    rw [← zpow_natCast (g ^ k), ← zpow_natCast g, ← _root_.zpow_mul, ← _root_.zpow_mul,
      mul_comm]
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg s)
    change rkOneChi h (g ^ k) ∈ _
    rw [rkOneChi_eq_pow, ← hcomm]
    exact Subgroup.zpow_mem_zpowers _ _
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine ⟨g ^ k, ?_⟩
    change rkOneChi h (g ^ k) = _
    rw [rkOneChi_eq_pow, hcomm]

theorem card_rkOneM : Nat.card (rkOneM h) = ((p ^ f) ^ 2 - 1) / rkOneDelta p f := by
  have := h.finite
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  rw [rkOneM_eq_zpowers h hg, Nat.card_zpowers, orderOf_pow' _ (by omega),
    orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, UnitaryFieldData.card_eq_sq h,
    gcd_sq_sub_one _ hq, rkOneDelta]

theorem map_norm_rkOneM : (rkOneM h).map (Units.map h.normHom) = ⊤ := by
  refine eq_top_iff.mpr fun y _ => ?_
  obtain ⟨s, rfl⟩ := (unitary_field_norm h).2.1 y
  refine ⟨rkOneChi h s, ⟨s, rfl⟩, Units.ext (Subtype.ext ?_)⟩
  simp only [Units.coe_map, UnitaryFieldData.coe_normHom]
  exact norm_rkOneChi h s

theorem card_rkOneM_inf_ker : Nat.card ↥(rkOneM h ⊓ (Units.map h.normHom).ker) =
    (p ^ f + 1) / rkOneDelta p f := by
  have := h.finite
  have hq : 2 ≤ p ^ f := two_le_q h
  set Nm : rkOneM h →* h.fixedFieldˣ := (Units.map h.normHom).comp (rkOneM h).subtype
  have hNm : Function.Surjective Nm := by
    intro y
    have hy : y ∈ (rkOneM h).map (Units.map h.normHom) := by
      rw [map_norm_rkOneM h]
      exact Subgroup.mem_top y
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup Nm.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective Nm hNm).toEquiv,
    Nat.card_units, UnitaryFieldData.card_fixedField, card_rkOneM h] at hcard
  have hker : Nat.card Nm.ker = Nat.card ↥(rkOneM h ⊓ (Units.map h.normHom).ker) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left :
      rkOneM h ⊓ (Units.map h.normHom).ker ≤ rkOneM h)).toEquiv, Subgroup.inf_subgroupOf_left]
    rfl
  rw [hker] at hcard
  have hδ : rkOneDelta p f ∣ p ^ f + 1 := Nat.gcd_dvd_right _ _
  have hsq : (p ^ f) ^ 2 - 1 = (p ^ f - 1) * (p ^ f + 1) := by
    have hq2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hq1 : 1 ≤ p ^ f := by omega
    zify [hq1, hq2]
    ring
  rw [hsq, Nat.mul_div_assoc _ hδ] at hcard
  exact (Nat.eq_of_mul_eq_mul_left (by omega) hcard).symm

end Chi

section TorusIso

variable (h : UnitaryFieldData p f K)

@[expose] noncomputable def rkOneTHom : Kˣ →* Equiv.Perm (hypIsotropicLines h 1 1) :=
  (hypProjLineAction h 1 1).comp ((hypProj h 1 1).comp (rkOneDHomSU h))

theorem rkOneTHom_apply (s : Kˣ) : rkOneTHom h s = rkOneTElt h s :=
  rfl

theorem rkOneChi_param (s : Kˣ) {a b : K} (hab : h.norm a + h.trace b = 0) :
    h.norm ((rkOneChi h s : K) * a) + h.trace (h.norm (rkOneChi h s : K) * b) = 0 := by
  have e : h.norm (s : K) = s * h.bar s := rfl
  rw [norm_rkOneChi, coe_rkOneChi, e]
  exact rkOneT_param h s.ne_zero hab

theorem rkOneTElt_conj_chi (s : Kˣ) {a b : K} (hab : h.norm a + h.trace b = 0) :
    rkOneTElt h s * rkOneU h a b hab * (rkOneTElt h s)⁻¹ =
      rkOneU h ((rkOneChi h s : K) * a) (h.norm (rkOneChi h s : K) * b)
        (rkOneChi_param h s hab) := by
  rw [rkOneTElt_conj]
  exact rkOneU_congr h _ (by rw [coe_rkOneChi]) (by rw [norm_rkOneChi]; rfl)

theorem rkOneTElt_eq_one_iff (s : Kˣ) : rkOneTElt h s = 1 ↔ rkOneChi h s = 1 := by
  constructor
  · intro ht
    obtain ⟨b, hb⟩ := exists_norm_add_trace_eq_zero h 1
    have h1 := rkOneTElt_conj_chi h s hb
    rw [ht, one_mul, inv_one, mul_one] at h1
    have h2 := (rkOneU_injective h1).1
    exact Units.ext (by rw [Units.val_one]; linear_combination -h2)
  · intro hc
    have hc' : (rkOneChi h s : K) = 1 := by rw [hc, Units.val_one]
    have hcomm : ∀ (a b : K) (hab : h.norm a + h.trace b = 0),
        rkOneTElt h s * rkOneU h a b hab = rkOneU h a b hab * rkOneTElt h s := by
      intro a b hab
      have h1 := rkOneTElt_conj_chi h s hab
      rw [rkOneU_congr h (rkOneChi_param h s hab) (by rw [hc', one_mul])
        (by rw [hc', UnitaryFieldData.norm, map_one, one_mul, one_mul])] at h1
      exact mul_inv_eq_iff_eq_mul.mp h1
    refine Equiv.ext fun L => ?_
    by_cases hL : L = infL h
    · rw [hL, rkOneTElt_infL]
      rfl
    · obtain ⟨a, b, hab, rfl⟩ := exists_rkPtL_eq L hL
      rw [← rkOneU_zeroL h hab, ← Equiv.Perm.mul_apply, hcomm, Equiv.Perm.mul_apply,
        rkOneTElt_zeroL]
      rfl

theorem ker_rkOneTHom : (rkOneTHom h).ker = (rkOneChi h).ker := by
  ext s
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, rkOneTHom_apply, rkOneTElt_eq_one_iff]

@[expose] noncomputable def rkOneTEquivM : rkOneT h ≃* rkOneM h :=
  (QuotientGroup.quotientKerEquivRange (rkOneTHom h)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (ker_rkOneTHom h)).trans
      (QuotientGroup.quotientKerEquivRange (rkOneChi h)))

theorem rkOneTEquivM_apply (s : Kˣ) :
    (rkOneTEquivM h ⟨rkOneTElt h s, ⟨s, rfl⟩⟩ : Kˣ) = rkOneChi h s := by
  have h1 : (QuotientGroup.quotientKerEquivRange (rkOneTHom h)).symm ⟨rkOneTElt h s, ⟨s, rfl⟩⟩ =
      (s : Kˣ ⧸ (rkOneTHom h).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  change ((QuotientGroup.quotientKerEquivRange (rkOneChi h))
    ((QuotientGroup.quotientMulEquivOfEq (ker_rkOneTHom h))
      ((QuotientGroup.quotientKerEquivRange (rkOneTHom h)).symm
        ⟨rkOneTElt h s, ⟨s, rfl⟩⟩)) : Kˣ) = _
  rw [h1, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

end TorusIso

theorem unitary_rank_one_torus_action (h : UnitaryFieldData p f K) :
    (∀ (s : Kˣ) (a b : K) (hab : h.norm a + h.trace b = 0),
      rkOneTElt h s * rkOneU h a b hab * (rkOneTElt h s)⁻¹ =
        rkOneU h ((rkOneChi h s : K) * a) (h.norm (rkOneChi h s : K) * b)
          (rkOneChi_param h s hab)) ∧
    (∃ e : rkOneT h ≃* rkOneM h, ∀ s : Kˣ,
      (e ⟨rkOneTElt h s, ⟨s, rfl⟩⟩ : Kˣ) = rkOneChi h s) ∧
    Nat.card (rkOneM h) = ((p ^ f) ^ 2 - 1) / rkOneDelta p f ∧
    (rkOneM h).map (Units.map h.normHom) = ⊤ ∧
    Nat.card ↥(rkOneM h ⊓ (Units.map h.normHom).ker) = (p ^ f + 1) / rkOneDelta p f ∧
    (2 < p ^ f → p ^ f - 1 < Nat.card (rkOneM h) ∧
      ∃ m ∈ rkOneM h ⊓ (Units.map h.normHom).ker, m ≠ 1) := by
  refine ⟨fun s a b hab => rkOneTElt_conj_chi h s hab,
    ⟨rkOneTEquivM h, rkOneTEquivM_apply h⟩, card_rkOneM h, map_norm_rkOneM h,
    card_rkOneM_inf_ker h, fun hq => ?_⟩
  have := h.finite
  set q := p ^ f with hqdef
  have hδ : rkOneDelta p f ∣ q + 1 := Nat.gcd_dvd_right _ _
  have hδ3 : rkOneDelta p f ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hX : 2 ≤ (q + 1) / rkOneDelta p f := by
    by_contra hX
    have h1 := Nat.div_mul_cancel hδ
    have h2 : (q + 1) / rkOneDelta p f * rkOneDelta p f ≤ 1 * 3 :=
      Nat.mul_le_mul (by omega) hδ3
    omega
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hq1 : 1 ≤ q := by omega
    zify [hq1, hq2]
    ring
  refine ⟨?_, ?_⟩
  · rw [card_rkOneM h, ← hqdef, hsq, Nat.mul_div_assoc _ hδ]
    calc q - 1 < (q - 1) * 2 := by omega
      _ ≤ (q - 1) * ((q + 1) / rkOneDelta p f) := Nat.mul_le_mul_left _ hX
  · have hcard := card_rkOneM_inf_ker h
    rw [← hqdef] at hcard
    have h1 : 1 < Nat.card ↥(rkOneM h ⊓ (Units.map h.normHom).ker) := by omega
    obtain ⟨⟨m, hm⟩, hm1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
      ((Subgroup.one_lt_card_iff_ne_bot _).mp h1)
    exact ⟨m, hm, fun h0 => hm1 (Subtype.ext h0)⟩

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
