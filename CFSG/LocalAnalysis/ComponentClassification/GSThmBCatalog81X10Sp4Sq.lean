module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10Sp4Fd
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10RecChar
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10RecConf

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag CatFactsSp4
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace X10Sp4

theorem false_of_card_le_sl {X Z q : ℕ} (hq : 3 ≤ q)
    (hZ : Z * 2 = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))) (hdvd : Z ∣ X)
    (hX0 : 0 < X) (hle : X ≤ q ^ 2 * ((q ^ 2) ^ 2 - 1)) : False := by
  have hZX := Nat.le_of_dvd hX0 hdvd
  have hq2 : 9 ≤ q ^ 2 := by nlinarith
  have hq4 : q ^ 4 = q ^ 2 * q ^ 2 := by ring
  have hq22 : (q ^ 2) ^ 2 = q ^ 4 := by ring
  rw [hq22] at hle
  have h81 : 81 ≤ q ^ 4 := by nlinarith
  have hA : 8 ≤ q ^ 2 - 1 := by omega
  have hB : 0 < q ^ 4 - 1 := by omega
  have : 2 * (q ^ 2 * (q ^ 4 - 1)) < q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
    rw [hq4]
    have h1 : 2 < q ^ 2 * (q ^ 2 - 1) := by nlinarith
    have h2 : 0 < q ^ 2 * (q ^ 4 - 1) := Nat.mul_pos (by omega) hB
    nlinarith
  omega

theorem false_of_dvd_sl_sq {X Z q : ℕ} (hq : 3 ≤ q)
    (hZ : Z * 2 = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))) (hdvd : Z ∣ X)
    (hX : X * 2 = (q ^ 2) ^ 2 * (((q ^ 2) ^ 2) ^ 2 - 1)) : False := by
  obtain ⟨c, hc⟩ := hdvd
  have hq2 : 9 ≤ q ^ 2 := by nlinarith
  have hq4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hq8 : 1 ≤ q ^ 8 := Nat.one_le_pow _ _ (by omega)
  have h1 : q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) * c = q ^ 4 * (q ^ 8 - 1) := by
    have e1 : (q ^ 2) ^ 2 * (((q ^ 2) ^ 2) ^ 2 - 1) = q ^ 4 * (q ^ 8 - 1) := by ring_nf
    rw [← e1, ← hX, hc, ← hZ]
    ring
  have e2 : q ^ 8 - 1 = (q ^ 4 - 1) * (q ^ 4 + 1) := by
    zify [hq4, hq8]
    ring
  rw [e2] at h1
  have h81 : 3 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
  have hpos : 0 < q ^ 4 * (q ^ 4 - 1) := Nat.mul_pos (by omega) (by omega)
  have h3 : q ^ 4 * (q ^ 4 - 1) * ((q ^ 2 - 1) * c) = q ^ 4 * (q ^ 4 - 1) * (q ^ 4 + 1) := by
    rw [show q ^ 4 * (q ^ 4 - 1) * ((q ^ 2 - 1) * c) =
      q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) * c by ring, h1]
    ring
  have h4 := Nat.eq_of_mul_eq_mul_left hpos h3
  have hq21 : 1 ≤ q ^ 2 := by omega
  have e3 : q ^ 4 + 1 = (q ^ 2 - 1) * (q ^ 2 + 1) + 2 := by
    zify [hq21]
    ring
  have h5 : (q ^ 2 - 1) ∣ 2 := by
    have : (q ^ 2 - 1) ∣ (q ^ 2 - 1) * (q ^ 2 + 1) + 2 := by
      rw [← e3, ← h4]
      exact dvd_mul_right _ _
    exact (Nat.dvd_add_right (dvd_mul_right _ _)).mp this
  have := Nat.le_of_dvd (by norm_num) h5
  omega

theorem cf81X10RowSp4Sq :
    ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G) (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
      3 < p ^ f → X10Rec.Conf G N p f → ¬ Blueprint.LieModel ↥N .PSp 2 p (2 * f) := by
  intro G _ _ N p f hp hp2 hf hq hconf hM
  obtain ⟨hNn, hC, -, a, b, J, K, -, ha, hb, -, hJN, hJC, hJp, hJm, hbJ, -, -, -, hKN, -,
    hKC, hKp, hKm⟩ := hconf
  have : N.Normal := hNn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := GH74.Generic.lieModel_psp_data hM
  have hpow : p ^ (2 * f) = (p ^ f) ^ 2 := by rw [mul_comm, pow_mul]
  have hq3 : 3 ≤ p ^ f := hq.le
  have h9 : 9 ≤ (p ^ f) ^ 2 := by nlinarith
  have h5 : 5 ≤ p ^ (2 * f) := by omega
  have hf2 : 1 ≤ 2 * f := by omega
  obtain ⟨hα2, hα1⟩ := X10Rec.conjNormal_involutive hC ha
  obtain ⟨hβ2, hβ1⟩ := X10Rec.conjNormal_involutive hC hb
  set α := MulAut.congr e (MulAut.conjNormal a : MulAut ↥N) with hαdef
  set β := MulAut.congr e (MulAut.conjNormal b : MulAut ↥N) with hβdef
  have hα2' : α * α = 1 := by rw [hαdef, ← map_mul, hα2, map_one]
  have hβ2' : β * β = 1 := by rw [hβdef, ← map_mul, hβ2, map_one]
  have hα1' : α ≠ 1 := fun h => hα1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  have hβ1' : β ≠ 1 := fun h => hβ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  have hcα : ∀ x, e (MulAut.conjNormal a x) = α (e x) := fun x => by
    rw [hαdef, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  have hcβ : ∀ x, e (MulAut.conjNormal b x) = β (e x) := fun x => by
    rw [hβdef, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  obtain ⟨hJ₁X, hJ₁⟩ := X10Rec.fixed_pComponent_subgroupOf hJN hJC hJp
  obtain ⟨hJ₀X, hJ₀⟩ := isPComponent_map_fixOf hcα hJ₁X hJ₁
  have eJ : ↥J ≃* ↥((J.subgroupOf N).map e.toMonoidHom) := (subgroupOfEquivOfLe hJN).symm.trans
    ((J.subgroupOf N).equivMapOfInjective e.toMonoidHom e.injective)
  have hJc : Nat.card ↥((J.subgroupOf N).map e.toMonoidHom) = Nat.card (pPrimeCore 2 ↥J) *
      (p ^ (2 * f) * ((p ^ (2 * f)) ^ 2 - 1) / 2) := by
    rw [← Nat.card_congr eJ.toEquiv, (pPrimeCore 2 ↥J).card_eq_card_quotient_mul_card_subgroup,
      card_of_lieModel_psl_sq hp2 hJm, hpow]
    exact Nat.mul_comm _ _
  obtain ⟨hT, hJs⟩ := allTraces_of_card hp hp2 hf2 hF h5 hα2' hα1' hJ₀X hJ₀
    (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥J))) hJc
  have : IsSimpleGroup ↥J := by
    have := hJs
    exact eJ.isSimpleGroup
  have hOJ : pPrimeCore 2 ↥J = ⊥ := by
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 ↥J)).resolve_right fun h => ?_
    have h1 : Nat.card (↥J ⧸ pPrimeCore 2 ↥J) = 1 := by
      rw [h]
      have : Subsingleton (↥J ⧸ (⊤ : Subgroup ↥J)) := QuotientGroup.subsingleton_quotient_top
      exact Nat.card_of_subsingleton (1 : ↥J ⧸ (⊤ : Subgroup ↥J))
    rw [card_of_lieModel_psl_sq hp2 hJm] at h1
    have h81 : 81 ≤ ((p ^ f) ^ 2) ^ 2 := by nlinarith
    have : 9 * 80 ≤ (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) := Nat.mul_le_mul h9 (by omega)
    omega
  have hbc : ∀ j ∈ J, j * b = b * j := fun j hj => by
    have h1 := (UnbalancedLayer.mem_coreActionKernel.mp hbJ).2 j hj
    rw [hOJ, Subgroup.map_bot, Subgroup.mem_bot] at h1
    calc j * b = b * j * (j⁻¹ * b⁻¹ * j * b) := by group
      _ = b * j := by rw [h1, mul_one]
  have hβJ : ∀ x ∈ (J.subgroupOf N).map e.toMonoidHom, β x = x := by
    rintro _ ⟨m, hm, rfl⟩
    change β (e m) = e m
    rw [← hcβ]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, ← hbc (m : G) (mem_subgroupOf.mp hm), mul_inv_cancel_right]
  obtain ⟨hK₁X, hK₁⟩ := X10Rec.fixed_pComponent_subgroupOf hKN hKC hKp
  obtain ⟨hK₀X, hK₀⟩ := isPComponent_map_fixOf hcβ hK₁X hK₁
  have hKc : Nat.card ↥((K.subgroupOf N).map e.toMonoidHom) = Nat.card ↥K :=
    (Nat.card_congr ((K.subgroupOf N).equivMapOfInjective e.toMonoidHom
      e.injective).toEquiv).symm.trans (Nat.card_congr (subgroupOfEquivOfLe hKN).toEquiv)
  have hZ := two_mul_card_of_lieModel_psp hp2 hKm
  have hdvd : Nat.card (↥K ⧸ pPrimeCore 2 ↥K) ∣ Nat.card ↥K := Subgroup.card_quotient_dvd_card _
  rcases card_of_fix_allTraces hp hp2 hf2 hF h5 hβ2' hβ1' hT hβJ hK₀X hK₀ with h1 | h1 <;>
    rw [hKc, hpow] at h1
  · exact false_of_card_le_sl hq3 hZ hdvd Nat.card_pos h1
  · exact false_of_dvd_sl_sq hq3 hZ hdvd h1

end X10Sp4

end CFSG.ComponentClassification.GSThmB
