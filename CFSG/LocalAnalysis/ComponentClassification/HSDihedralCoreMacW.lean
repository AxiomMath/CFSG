module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitMacWilliams
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreFix
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreTbar
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreTwo

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ABGLocalTools DihedralGroup
open CFSG.ComponentClassification.HarrisLit (SectionalRankLeFour exists_normal_E8)
open CFSG.ComponentClassification.HSFLit (ElemAbelianTwo)

variable {X : Type} [Group X] [Finite X] {A : Type} [Group A] [Finite A]

omit [Finite X] [Finite A] in
theorem isSylowOf_top_of_sylow (T : Sylow 2 X) : IsSylowOf 2 (T : Subgroup X) ⊤ :=
  ⟨T.subtype le_top, by rw [Sylow.coe_subtype, subgroupOf_map_subtype, inf_of_le_left le_top]⟩

namespace LocalDatum

variable {Δ : LocalDatum X A}

omit [Finite A] in
theorem Fusion.exists_Y (φ : Δ.Fusion) (hX : ¬ SectionalRankLeFour X) :
    ∃ Y : Subgroup X, Y ≤ φ.T ∧ (∀ g ∈ (φ.T : Subgroup X), ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) ∧
      ElemAbelianTwo Y ∧ Nat.card Y = 8 ∧
      ∃ v ∈ Y, v ≠ 1 ∧ v ∈ Δ.S ∧ (∀ s ∈ Δ.S, s * v = v * s) ∧ φ.x * v * φ.x⁻¹ = v := by
  obtain ⟨Y, hYT, hYn, hYc, hYs, hY8⟩ := exists_normal_E8 hX (isSylowOf_top_of_sylow φ.T)
  have hne : ∃ n ∈ Y, n ≠ 1 := by
    by_contra h
    push Not at h
    have : Y = ⊥ := (eq_bot_iff_forall Y).mpr h
    rw [this, Subgroup.card_bot] at hY8
    omega
  obtain ⟨v, hvY, hv1, -, hvc⟩ := exists_central_inv_of_normal φ.isPGroup hYT hYn hne
  have hvT : v ∈ (φ.T : Subgroup X) := hYT hvY
  have hvS : v ∈ Δ.S := Δ.mem_S_of_commute_t φ.isPGroup φ.le hvT
    (hvc _ (φ.le Δ.t_mem)).symm
  refine ⟨Y, hYT, hYn, ⟨hYc, hYs⟩, hY8, v, hvY, hv1, hvS, fun s hs => hvc s (φ.le hs), ?_⟩
  rw [hvc _ φ.mem, mul_inv_cancel_right]

omit [Finite X] [Finite A] in
theorem Tbar_facts {Tbar Dbar : Subgroup A} {m : ℕ} (e : ↥Tbar ≃* DihedralGroup m)
    (hTp : IsPGroup 2 Tbar) (hDT : Dbar ≤ Tbar) (hne : Tbar ≠ Dbar) (hD8 : 8 ≤ Nat.card Dbar)
    [Finite Tbar] : Even m ∧ 8 ≤ m := by
  have hT := Tbar_card e
  obtain ⟨j, hj⟩ := hTp.exists_card_eq
  have hdvd : Nat.card Dbar ∣ Nat.card Tbar := Subgroup.card_dvd_of_le hDT
  have hlt : Nat.card Dbar ≠ Nat.card Tbar := fun h =>
    hne (Subgroup.eq_of_le_of_card_ge hDT h.symm.le).symm
  obtain ⟨c, hc⟩ := hdvd
  have hc2 : 2 ≤ c := by
    rcases Nat.lt_or_ge c 2 with h | h
    · interval_cases c
      · rw [mul_zero] at hc
        have : 0 < Nat.card Tbar := Nat.card_pos
        omega
      · rw [mul_one] at hc
        exact absurd hc.symm hlt
    · exact h
  have h16 : 16 ≤ Nat.card Tbar := by
    rw [hc]
    calc 16 = 8 * 2 := by norm_num
      _ ≤ Nat.card Dbar * c := Nat.mul_le_mul hD8 hc2
  rw [hT] at hj h16
  rcases j with _ | j
  · rw [pow_zero] at hj
    omega
  · rw [pow_succ] at hj
    have hm : m = 2 ^ j := by omega
    refine ⟨?_, by omega⟩
    rcases j with _ | j
    · rw [pow_zero] at hm
      omega
    · exact ⟨2 ^ j, by rw [hm, pow_succ]; ring⟩

theorem false_of_normal_elem {k : A} (h2 : Δ.CaseTwo k) {Tbar : Subgroup A} {m : ℕ}
    (e : ↥Tbar ≃* DihedralGroup m) (hm : Even m) (h8 : 8 ≤ m) (hTR : Tbar ≤ Δ.R)
    (hDT : Δ.Dbar ≤ Tbar) {Y' : Subgroup X} (hY'S : Y' ≤ Δ.S)
    (hY'n : ∀ s ∈ Δ.S, ∀ y ∈ Y', s * y * s⁻¹ ∈ Y') (hY'el : ElemAbelianTwo Y')
    (hY'T : ∀ y ∈ Y', Δ.ψe y ∈ Tbar) (hz : Δ.dz ∈ Y') {y : X} (hy : y ∈ Y')
    (hy1 : Δ.ψe y ≠ 1) (hyz : Δ.ψe y ≠ Δ.ψe Δ.dz) : False := by
  have hD8 := h2.2.2.2.2.1
  set zb := Δ.ψe Δ.dz
  set eb := Δ.ψe y
  have hzT : zb ∈ Tbar := hDT (Δ.ψe_mem_Dbar Δ.dz_mem)
  have hzc : ∀ g ∈ Tbar, zb * g = g * zb := by
    intro g hg
    obtain ⟨s, hs, rfl⟩ := (Δ.mem_R_iff).mp (hTR hg)
    rw [← Δ.ψe_mul (Δ.D_le Δ.dz_mem) hs, ← Δ.ψe_mul hs (Δ.D_le Δ.dz_mem),
      (Δ.dz_comm_S hD8 hs).symm]
  have hz1 : zb ≠ 1 := fun h => Δ.dz_ne_one (Δ.eq_one_of_ψe Δ.dz_mem h)
  have hyS := hY'S hy
  have heT : eb ∈ Tbar := hY'T y hy
  have he2 : eb ^ 2 = 1 := by rw [← Δ.ψe_pow hyS, hY'el.sq_eq_one y hy, Δ.ψe_one]
  set E' : Subgroup A := (Y'.subgroupOf Δ.S).map Δ.ψ
  have hmemE' : ∀ y' ∈ Y', Δ.ψe y' ∈ E' := fun y' hy' =>
    ⟨⟨y', hY'S hy'⟩, mem_subgroupOf.mpr hy', (Δ.ψe_of_mem (hY'S hy')).symm⟩
  have hE'T : E' ≤ Tbar := by
    rintro _ ⟨⟨y', hy'S⟩, hy', rfl⟩
    rw [← Δ.ψe_of_mem hy'S]
    exact hY'T y' (mem_subgroupOf.mp hy')
  have hcard := Tbar_card_le_four e hm (by omega) hE'T (by
      rintro _ ⟨⟨y', hy'S⟩, hy', rfl⟩
      rw [← Δ.ψe_of_mem hy'S, ← Δ.ψe_pow hy'S, hY'el.sq_eq_one y' (mem_subgroupOf.mp hy'),
        Δ.ψe_one])
    (by
      rintro _ ⟨⟨a, haS⟩, ha, rfl⟩ _ ⟨⟨b, hbS⟩, hb, rfl⟩
      rw [← Δ.ψe_of_mem haS, ← Δ.ψe_of_mem hbS, ← Δ.ψe_mul haS hbS, ← Δ.ψe_mul hbS haS,
        hY'el.comm a (mem_subgroupOf.mp ha) b (mem_subgroupOf.mp hb)])
  have hez : eb * zb ∈ E' := by
    rw [← Δ.ψe_mul hyS (Δ.D_le Δ.dz_mem)]
    exact hmemE' _ (mul_mem hy hz)
  have hcomm : ∀ g ∈ Tbar, eb * g * eb⁻¹ * g⁻¹ = 1 ∨ eb * g * eb⁻¹ * g⁻¹ = zb := by
    intro g hg
    obtain ⟨s, hs, rfl⟩ := (Δ.mem_R_iff).mp (hTR hg)
    have hconj : Δ.ψe s * eb * (Δ.ψe s)⁻¹ ∈ E' := by
      rw [← Δ.ψe_conj hs hyS]
      exact hmemE' _ (hY'n s hs y hy)
    have hez1 : eb * zb ≠ 1 := fun h => hyz (by
      calc eb = eb * zb * zb⁻¹ := by group
        _ = zb⁻¹ := by rw [h, one_mul]
        _ = zb := by
          rw [inv_eq_of_mul_eq_one_right (by rw [← pow_two, ← Δ.ψe_pow (Δ.D_le Δ.dz_mem),
            Δ.dz_sq, Δ.ψe_one] : zb * zb = 1)])
    rcases eq_of_card_le_four hcard (one_mem E') (hmemE' _ hz) (hmemE' _ hy) hez
      hz1.symm hy1.symm hez1.symm hyz.symm (fun h => hy1 (by
        calc eb = eb * zb * zb⁻¹ := by group
          _ = 1 := by rw [← h, mul_inv_cancel]))
      (fun h => hz1 (by
        calc zb = eb⁻¹ * (eb * zb) := by group
          _ = 1 := by rw [← h, inv_mul_cancel])) hconj with h | h | h | h
    · exfalso
      apply hy1
      calc eb = (Δ.ψe s)⁻¹ * (Δ.ψe s * eb * (Δ.ψe s)⁻¹) * Δ.ψe s := by group
        _ = 1 := by rw [h]; group
    · exfalso
      apply hyz
      calc eb = (Δ.ψe s)⁻¹ * (Δ.ψe s * eb * (Δ.ψe s)⁻¹) * Δ.ψe s := by group
        _ = (Δ.ψe s)⁻¹ * (zb * Δ.ψe s) := by rw [h, mul_assoc]
        _ = zb := by rw [hzc _ hg]; group
    · left
      calc eb * Δ.ψe s * eb⁻¹ * (Δ.ψe s)⁻¹ =
          eb * (Δ.ψe s * eb * (Δ.ψe s)⁻¹)⁻¹ := by group
        _ = 1 := by rw [h, mul_inv_cancel]
    · right
      calc eb * Δ.ψe s * eb⁻¹ * (Δ.ψe s)⁻¹ =
          eb * (Δ.ψe s * eb * (Δ.ψe s)⁻¹)⁻¹ := by group
        _ = zb⁻¹ := by rw [h, ← hzc eb heT]; group
        _ = zb := inv_eq_of_mul_eq_one_right (by rw [← pow_two, ← Δ.ψe_pow (Δ.D_le Δ.dz_mem),
            Δ.dz_sq, Δ.ψe_one])
  rcases Tbar_eq_of_comm_mod e hm h8 hzT hzc hz1 heT he2 hcomm with h | h
  · exact hy1 h
  · exact hyz h

end LocalDatum

end CFSG.ComponentClassification.HSDihedral
