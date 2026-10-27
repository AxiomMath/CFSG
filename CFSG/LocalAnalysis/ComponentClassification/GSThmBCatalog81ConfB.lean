module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81ConfA
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81Conf

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup
open scoped commutatorElement

namespace ConfA

theorem props_of_facts {K₀ : Type} [Group K₀] [Finite K₀] {q : ℕ} (hq : Odd q)
    (c : Cat8.QConf K₀ q) (hF : Facts K₀ q c.a) : c.Props := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut K₀) := Finite.of_injective (fun φ : MulAut K₀ => (φ : K₀ → K₀))
    (fun φ ψ h => MulEquiv.ext (congrFun h))
  have hIn : (Cat8.Inn K₀).Normal := inn_normal K₀
  have ha2 : c.a * c.a = 1 := c.adm.sq
  have haI : c.a ∉ Cat8.Inn K₀ := c.adm.out
  have hQC := c.Q_le
  have hQS := c.Q_sylow
  have hQ2 : IsPGroup 2 c.Q := by
    obtain ⟨T, hT⟩ := hQS
    have h := T.isPGroup'
    rw [hT] at h
    exact h.of_equiv (subgroupOfEquivOfLe hQC)
  have hQa : ∀ w ∈ c.Q, w * c.a = c.a * w := fun w hw =>
    mem_centralizer_singleton_iff.mp (hQC hw).2
  have hac : ∀ w ∈ c.Q, c.a * w = w * c.a := fun w hw => (hQa w hw).symm
  have haC : c.a ∈ Cat8.innA K₀ c.a ⊓ centralizer ({c.a} : Set (MulAut K₀)) :=
    ⟨mem_sup_right (mem_zpowers c.a), mem_centralizer_singleton_iff.mpr rfl⟩
  have haQ : c.a ∈ c.Q := mem_of_central haC
    (fun y hy => (mem_centralizer_singleton_iff.mp hy.2).symm) (k := 1)
    (by rw [pow_one, pow_two]; exact ha2) hQS
  have hgN := c.g_norm
  have hconj : ∀ w ∈ c.Q, c.g⁻¹ * w * c.g ∈ c.Q := fun w hw =>
    (mem_normalizer_iff.mp hgN (c.g⁻¹ * w * c.g)).mpr
      (by rw [show c.g * (c.g⁻¹ * w * c.g) * c.g⁻¹ = w by group]; exact hw)
  have hconj' : ∀ w ∈ c.Q, c.g * w * c.g⁻¹ ∈ c.Q := fun w hw =>
    (mem_normalizer_iff.mp hgN w).mp hw
  set b := c.g⁻¹ * c.a * c.g with hb
  have hbQ : b ∈ c.Q := hconj c.a haQ
  have hbc : ∀ w ∈ c.Q, b * w = w * b := by
    intro w hw
    have h := hQa _ (hconj' w hw)
    calc b * w = c.g⁻¹ * (c.a * (c.g * w * c.g⁻¹)) * c.g := by rw [hb]; group
      _ = c.g⁻¹ * (c.g * w * c.g⁻¹ * c.a) * c.g := by rw [h]
      _ = w * b := by rw [hb]; group
  have hτ : c.tau = c.a * b := rfl
  have hτQ : c.tau ∈ c.Q := mul_mem haQ hbQ
  have hτc : ∀ w ∈ c.Q, c.tau * w = w * c.tau := by
    intro w hw
    rw [hτ, mul_assoc, hbc w hw, ← mul_assoc, hac w hw, mul_assoc]
  have hτI : c.tau ∈ Cat8.Inn K₀ := c.tau_inn
  have hb2 : b * b = 1 := by
    rw [hb]
    calc c.g⁻¹ * c.a * c.g * (c.g⁻¹ * c.a * c.g) = c.g⁻¹ * (c.a * c.a) * c.g := by group
      _ = 1 := by rw [ha2]; group
  have hτ2 : c.tau * c.tau = 1 := by
    rw [hτ]
    calc c.a * b * (c.a * b) = c.a * (b * c.a) * b := by group
      _ = c.a * (c.a * b) * b := by rw [(hac b hbQ).symm]
      _ = c.a * c.a * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]
  have hτ1 : c.tau ≠ 1 := by
    intro h1
    have hba : b = c.a := by
      have h : c.a * b = 1 := h1
      calc b = c.a * (c.a * b) := by rw [← mul_assoc, ha2, one_mul]
        _ = c.a := by rw [h, mul_one]
    have hgC : c.g ∈ Cat8.innA K₀ c.a ⊓ centralizer ({c.a} : Set (MulAut K₀)) := by
      refine ⟨mem_sup_left c.g_inn, mem_centralizer_singleton_iff.mpr ?_⟩
      have h : c.g⁻¹ * c.a * c.g = c.a := hba
      calc c.g * c.a = c.g * (c.g⁻¹ * c.a * c.g) := by rw [h]
        _ = c.a * c.g := by group
    exact c.g_not_mem (mem_of_normalizes hgC hQC hgN c.g_sq hQS)
  have hatau : c.a * c.tau = b := by rw [hτ, ← mul_assoc, ha2, one_mul]
  have hfix : ∀ x : K₀, x ∈ Eight.fixSubgroup b ↔ c.g x ∈ Eight.fixSubgroup c.a := by
    intro x
    change b x = x ↔ c.a (c.g x) = c.g x
    rw [hb]
    simp only [MulAut.mul_apply]
    constructor
    · intro h
      have := congrArg c.g h
      simpa using this
    · intro h
      rw [h]
      simp
  have hbadm : Cat8.IsAdmQ K₀ q b := by
    refine ⟨hb2, fun hbI => haI ?_, ?_⟩
    · have := hIn.conj_mem _ hbI c.g
      rwa [hb, show c.g * (c.g⁻¹ * c.a * c.g) * c.g⁻¹ = c.a by group] at this
    · rw [Nat.card_congr (Equiv.subtypeEquiv c.g.toEquiv hfix)]
      exact c.adm.dvd
  obtain ⟨hτL, hzτ⟩ := hF.type c.tau hτI (hQa _ hτQ) hτ2 hτ1 (hatau ▸ hbadm)
  have hLfix : Cat8.L0 K₀ c.a ≤ Cat8.innFix K₀ c.a := commutator_self_le _
  have hfixC : Cat8.innFix K₀ c.a ≤ Cat8.innA K₀ c.a ⊓ centralizer ({c.a} : Set (MulAut K₀)) :=
    inf_le_inf_right _ le_sup_left
  have hLC := hLfix.trans hfixC
  have hLI : Cat8.L0 K₀ c.a ≤ Cat8.Inn K₀ := hLfix.trans inf_le_left
  have hLn : ∀ x ∈ Cat8.innA K₀ c.a ⊓ centralizer ({c.a} : Set (MulAut K₀)),
      ∀ y ∈ Cat8.L0 K₀ c.a, x * y * x⁻¹ ∈ Cat8.L0 K₀ c.a := by
    intro x hx y hy
    refine conj_mem_commutator (fun w hw => ?_) hy
    refine ⟨hIn.conj_mem _ hw.1 x, mem_centralizer_singleton_iff.mpr ?_⟩
    have hxa : x * c.a = c.a * x := mem_centralizer_singleton_iff.mp hx.2
    have hwa : w * c.a = c.a * w := mem_centralizer_singleton_iff.mp hw.2
    have hxa' : x⁻¹ * c.a = c.a * x⁻¹ := by
      calc x⁻¹ * c.a = x⁻¹ * (c.a * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * c.a) * x⁻¹ := by rw [hxa]
        _ = c.a * x⁻¹ := by group
    calc x * w * x⁻¹ * c.a = x * w * (x⁻¹ * c.a) := by group
      _ = x * (w * c.a) * x⁻¹ := by rw [hxa']; group
      _ = x * (c.a * w) * x⁻¹ := by rw [hwa]
      _ = x * c.a * w * x⁻¹ := by group
      _ = c.a * (x * w * x⁻¹) := by rw [hxa]; group
  have hDcard : Nat.card c.D = 2 ^ (Cat8.ordL2 (q ^ 2)).factorization 2 := by
    rw [← hF.card_L0]
    exact card_inf_eq hQC hLC hLn hQS
  have hDQ : c.D ≤ c.Q := inf_le_left
  have hDI : c.D ≤ c.Q ⊓ Cat8.Inn K₀ := le_inf inf_le_left (inf_le_right.trans hLI)
  have hτD : c.tau ∉ c.D := fun h => hτL h.2
  have hpos : Cat8.ordL2 (q ^ 2) ≠ 0 := by
    rw [← hF.card_L0]
    exact Nat.card_pos.ne'
  obtain ⟨k, hk⟩ := (hQ2.to_le (inf_le_left : c.Q ⊓ Cat8.Inn K₀ ≤ c.Q)).exists_card_eq
  have hQIfix : c.Q ⊓ Cat8.Inn K₀ ≤ Cat8.innFix K₀ c.a :=
    le_inf inf_le_right (inf_le_left.trans (hQC.trans inf_le_right))
  have hQIdvd : Nat.card ↥(c.Q ⊓ Cat8.Inn K₀) ∣ 2 * Cat8.ordL2 (q ^ 2) :=
    (Subgroup.card_dvd_of_le hQIfix).trans hF.card_innFix
  have hle2 : Nat.card ↥(c.Q ⊓ Cat8.Inn K₀) ≤ 2 * Nat.card c.D := by
    rw [hk, hDcard, ← pow_succ']
    apply Nat.pow_le_pow_right (by norm_num)
    have h := (Nat.prime_two.pow_dvd_iff_le_factorization (Nat.mul_ne_zero two_ne_zero hpos)).mp
      (hk ▸ hQIdvd)
    rw [Nat.factorization_mul two_ne_zero hpos, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two] at h
    omega
  have hQIeq : Nat.card ↥(c.Q ⊓ Cat8.Inn K₀) = 2 * Nat.card c.D := by
    obtain ⟨j, hj⟩ := Subgroup.card_dvd_of_le hDI
    have hD0 : 0 < Nat.card c.D := Nat.card_pos
    have hj2 : j ≤ 2 := by
      have h := hle2
      rw [hj, mul_comm 2] at h
      exact Nat.le_of_mul_le_mul_left h hD0
    have hj1 : j ≠ 1 := by
      intro h1
      apply hτD
      have h : c.D = c.Q ⊓ Cat8.Inn K₀ :=
        Subgroup.eq_of_le_of_card_ge hDI (by rw [hj, h1, mul_one])
      rw [h]
      exact ⟨hτQ, hτI⟩
    have hj0 : j ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hj
      exact Nat.card_pos.ne' hj
    have : j = 2 := by omega
    rw [hj, this, mul_comm]
  have hQrel := relIndex_eq_two ha2 haI haQ (hQC.trans inf_le_left)
  have hQcard : Nat.card c.Q = 2 * Nat.card ↥(c.Q ⊓ Cat8.Inn K₀) := by
    have h1 := Subgroup.relIndex_mul_card (H := Cat8.Inn K₀) (K := c.Q)
    rw [hQrel, inf_comm] at h1
    exact h1.symm
  have hQI : c.D ⊔ zpowers c.tau = c.Q ⊓ Cat8.Inn K₀ :=
    eq_of_card_two_mul le_sup_left (sup_le hDI (zpowers_le.mpr ⟨hτQ, hτI⟩))
      (fun h => hτD (h (mem_sup_right (mem_zpowers _)))) hQIeq
  have hQeq : c.D ⊔ zpowers c.tau ⊔ zpowers c.a = c.Q := by
    rw [hQI]
    exact eq_of_card_two_mul le_sup_left (sup_le inf_le_left (zpowers_le.mpr haQ))
      (fun h => haI (h (mem_sup_right (mem_zpowers c.a))).2) hQcard
  have h8 : 8 ≤ Nat.card c.D := by
    rw [hDcard]
    have h := (Nat.prime_two.pow_dvd_iff_le_factorization hpos).mp
      (show 2 ^ 3 ∣ Cat8.ordL2 (q ^ 2) from eight_dvd_ordL2 hq)
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (Cat8.ordL2 (q ^ 2)).factorization 2 := Nat.pow_le_pow_right (by norm_num) h
  obtain ⟨hZ2, t, htD, htt, httc⟩ := hF.dihedral c.D inf_le_right (hQ2.to_le hDQ) hDcard
  have hZ : ∀ w ∈ c.D, (∀ x ∈ c.D, w * x = x * w) → w ≠ 1 → w = t * t := by
    intro w hw hwc hw1
    have hwZ : w ∈ c.D ⊓ centralizer (c.D : Set (MulAut K₀)) :=
      ⟨hw, mem_centralizer_iff.mpr fun x hx => (hwc x hx).symm⟩
    have httZ : t * t ∈ c.D ⊓ centralizer (c.D : Set (MulAut K₀)) := ⟨mul_mem htD htD, httc⟩
    obtain ⟨y, -, hyu⟩ :=
      (Nat.card_eq_two_iff' (1 : ↥(c.D ⊓ centralizer (c.D : Set (MulAut K₀))))).mp hZ2
    have e1 : (⟨w, hwZ⟩ : ↥(c.D ⊓ centralizer (c.D : Set (MulAut K₀)))) = y :=
      hyu _ (fun h => hw1 (congrArg Subtype.val h))
    have e2 : (⟨t * t, httZ⟩ : ↥(c.D ⊓ centralizer (c.D : Set (MulAut K₀)))) = y :=
      hyu _ (fun h => htt (congrArg Subtype.val h))
    exact congrArg Subtype.val (e1.trans e2.symm)
  have hsq : ∀ w ∈ c.Q, w * w ∈ c.D := by
    let M : Subgroup (MulAut K₀) :=
      { carrier := {w | ∃ d ∈ c.D, ∃ e ∈ c.Q, (∀ x ∈ c.Q, e * x = x * e) ∧ e * e = 1 ∧
          w = d * e}
        mul_mem' := by
          rintro _ _ ⟨d₁, hd₁, e₁, he₁, hc₁, hs₁, rfl⟩ ⟨d₂, hd₂, e₂, he₂, hc₂, hs₂, rfl⟩
          refine ⟨d₁ * d₂, mul_mem hd₁ hd₂, e₁ * e₂, mul_mem he₁ he₂, ?_, ?_, ?_⟩
          · intro x hx
            rw [mul_assoc, hc₂ x hx, ← mul_assoc, hc₁ x hx, mul_assoc]
          · calc e₁ * e₂ * (e₁ * e₂) = e₁ * (e₂ * e₁) * e₂ := by group
              _ = e₁ * (e₁ * e₂) * e₂ := by rw [hc₂ e₁ he₁]
              _ = e₁ * e₁ * (e₂ * e₂) := by group
              _ = 1 := by rw [hs₁, hs₂, one_mul]
          · calc d₁ * e₁ * (d₂ * e₂) = d₁ * (e₁ * d₂) * e₂ := by group
              _ = d₁ * (d₂ * e₁) * e₂ := by rw [hc₁ d₂ (hDQ hd₂)]
              _ = d₁ * d₂ * (e₁ * e₂) := by group
        one_mem' := ⟨1, one_mem _, 1, one_mem _, fun x _ => by rw [one_mul, mul_one],
          mul_one 1, (mul_one 1).symm⟩
        inv_mem' := by
          rintro _ ⟨d, hd, e, he, hc, hs, rfl⟩
          refine ⟨d⁻¹, inv_mem hd, e, he, hc, hs, ?_⟩
          have he' : e⁻¹ = e := inv_eq_of_mul_eq_one_right hs
          rw [mul_inv_rev, he', hc d⁻¹ (inv_mem (hDQ hd))] }
    have hQM : c.Q ≤ M := by
      rw [← hQeq]
      refine sup_le (sup_le (fun d hd => ?_) ?_) ?_
      · exact ⟨d, hd, 1, one_mem _, fun x _ => by rw [one_mul, mul_one], mul_one 1,
          (mul_one d).symm⟩
      · rw [zpowers_le]
        exact ⟨1, one_mem _, c.tau, hτQ, hτc, hτ2, (one_mul _).symm⟩
      · rw [zpowers_le]
        exact ⟨1, one_mem _, c.a, haQ, hac, ha2, (one_mul _).symm⟩
    intro w hw
    obtain ⟨d, hd, e, he, hc, hs, rfl⟩ := hQM hw
    have h : d * e * (d * e) = d * d := by
      calc d * e * (d * e) = d * (e * d) * e := by group
        _ = d * (d * e) * e := by rw [hc d (hDQ hd)]
        _ = d * d * (e * e) := by group
        _ = d * d := by rw [hs, mul_one]
    rw [h]
    exact mul_mem hd hd
  have hzQ : c.z ∈ c.Q := c.z_mem.1
  have hzc : ∀ w ∈ c.Q, c.z * w = w * c.z := by
    have hle : c.Q ≤ centralizer ({c.z} : Set (MulAut K₀)) := by
      rw [← hQeq]
      refine sup_le (sup_le (fun d hd => ?_) ?_) ?_
      · exact mem_centralizer_singleton_iff.mpr (c.z_comm d hd).symm
      · rw [zpowers_le]
        exact mem_centralizer_singleton_iff.mpr (hτc _ hzQ)
      · rw [zpowers_le]
        exact mem_centralizer_singleton_iff.mpr (hac _ hzQ)
    intro w hw
    exact (mem_centralizer_singleton_iff.mp (hle hw)).symm
  have hzt := hZ c.z c.z_mem c.z_comm c.z_ne
  have hzg : c.g⁻¹ * c.z * c.g ∈ c.D := by
    have h1 : c.g⁻¹ * c.z * c.g = (c.g⁻¹ * t * c.g) * (c.g⁻¹ * t * c.g) := by
      rw [hzt]
      group
    rw [h1]
    exact hsq _ (hconj t (hDQ htD))
  have hzgc : ∀ x ∈ c.D, c.g⁻¹ * c.z * c.g * x = x * (c.g⁻¹ * c.z * c.g) := by
    intro x hx
    have h := hzc _ (hconj' x (hDQ hx))
    calc c.g⁻¹ * c.z * c.g * x = c.g⁻¹ * (c.z * (c.g * x * c.g⁻¹)) * c.g := by group
      _ = c.g⁻¹ * (c.g * x * c.g⁻¹ * c.z) * c.g := by rw [h]
      _ = x * (c.g⁻¹ * c.z * c.g) := by group
  have hzg1 : c.g⁻¹ * c.z * c.g ≠ 1 := by
    intro h
    apply c.z_ne
    calc c.z = c.g * (c.g⁻¹ * c.z * c.g) * c.g⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hgz : c.g⁻¹ * c.z * c.g = c.z := by
    rw [hZ _ hzg hzgc hzg1, hzt]
  refine ⟨hQeq.symm, ?_, h8, hτc, hgz, hzτ c.z c.z_mem.2 c.z_sq c.z_ne⟩
  rw [hQcard, hQIeq]
  ring

end ConfA

end CFSG.ComponentClassification.GSThmB
