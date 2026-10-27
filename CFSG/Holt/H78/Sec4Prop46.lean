module

public import CFSG.Holt.H78.Sec4Prop46S
public import CFSG.Holt.H78.Sec4Prop46A3
public import CFSG.Holt.H78.Sec4Prop46BTypes

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open
open scoped Pointwise

section Normalizer

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω]

private theorem conj_smul_eq_of_forall {S : Set Ω} {h x : G} (hh : h ∈ stabilizer G S)
    (hx : ∀ ω ∈ S, x • ω = ω) : ∀ ω ∈ S, (h * x * h⁻¹) • ω = ω := by
  intro ω hω
  have : h⁻¹ • ω ∈ S := by
    rw [← mem_stabilizer_iff.mp (inv_mem hh)]
    exact Set.smul_mem_smul_set hω
  rw [mul_smul, mul_smul, hx _ this, smul_inv_smul]

theorem mem_normalizer_caseACentralizer_holtDelta {α β : Ω} {v g : G} (hgv : Commute g v)
    (hg : g ∈ stabilizer G ({α, β} : Set Ω)) :
    g ∈ Subgroup.normalizer (caseACentralizer G Ω α β v (holtDelta G Ω α β) : Set G) := by
  have key : ∀ h : G, Commute h v → h ∈ stabilizer G ({α, β} : Set Ω) →
      ∀ x ∈ caseACentralizer G Ω α β v (holtDelta G Ω α β),
        h * x * h⁻¹ ∈ caseACentralizer G Ω α β v (holtDelta G Ω α β) := by
    rintro h hhv hh x ⟨⟨hxv, hxα, hxβ⟩, hxΔ⟩
    have hxv' : Commute x v :=
      (Subgroup.mem_centralizer_iff.mp hxv v (Subgroup.mem_zpowers v)).symm
    have hpair := conj_smul_eq_of_forall hh (x := x) (by
      rintro ω (rfl | rfl)
      exacts [hxα, hxβ])
    refine ⟨⟨Subgroup.mem_centralizer_iff.mpr fun y hy => ?_, hpair α (Set.mem_insert α _),
      hpair β (Set.mem_insert_of_mem α rfl)⟩, (mem_fixingSubgroup_iff G).mpr
        (conj_smul_eq_of_forall (stabilizer_pair_le α β hh) ((mem_fixingSubgroup_iff G).mp hxΔ))⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (((hhv.mul_left hxv').mul_left hhv.inv_left).zpow_right k).eq.symm
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨key g hgv hg x, fun hx => ?_⟩
  have := key g⁻¹ hgv.inv_left (inv_mem hg) _ hx
  rwa [inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc, inv_mul_cancel,
    mul_one] at this

end Normalizer

section Choice

variable {G : Type} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] {α : Ω} {v : G}
  {P : Subgroup (typeLSection G Ω v)}

theorem Prop46Setup.exists_w_isPGroup (hP : Prop46Setup G Ω α v P) {b : Ω}
    (hb : b ∈ p46Orbit G Ω v P α) (hbα : b ≠ α) {τ : G} (hτ2 : τ * τ = 1) (hτv : Commute τ v)
    (hτα : τ • α = α) (hτb : τ • b = b) :
    ∃ w ∈ longInvSwap G Ω α b, Commute w v ∧ w * v ∈ longInv G Ω ∧
      ∃ T : Subgroup G, IsPGroup 2 T ∧ w ∈ T ∧ τ ∈ T ∧
        T ≤ Subgroup.normalizer (caseACentralizer G Ω α b v (holtDelta G Ω α b) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := Subgroup.centralizer (Subgroup.zpowers v : Set G) ⊓
    stabilizer G ({α, b} : Set Ω)
  have hmemH : ∀ g : G, Commute g v → g ∈ stabilizer G ({α, b} : Set Ω) → g ∈ H :=
    fun g hgv hg => Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr fun y hy => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (hgv.zpow_right k).eq.symm, hg⟩
  have hcommH : ∀ g ∈ H, Commute g v := fun g hg =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hg).1 v (Subgroup.mem_zpowers v)).symm
  obtain ⟨w₀, hw₀, hw₀v, hw₀J⟩ := hP.exists_w b hb hbα
  have hw₀S := mem_stabilizer_pair_of_mem_longInvSwap hw₀
  have hw₀H : w₀ ∈ H := hmemH w₀ hw₀v hw₀S
  have hτH : τ ∈ H := hmemH τ hτv
    (stabilizer_inf_le_stabilizer_pair α b (Subgroup.mem_inf.mpr ⟨hτα, hτb⟩))
  have h2 : ∀ {g : G}, g * g = 1 → IsPGroup 2 (Subgroup.zpowers g) := fun hg =>
    zpowers_isPGroup_two_of_pow_eq_one (n := 1) (by rw [pow_one, sq, hg])
  obtain ⟨S, hτS, hS⟩ := exists_fusionIsSylowIn_ge (h2 hτ2) (Subgroup.zpowers_le.mpr hτH)
  obtain ⟨S₀, hw₀S₀, hS₀⟩ := exists_fusionIsSylowIn_ge
    (h2 (mul_self_eq_one_of_mem_longInv hw₀.1)) (Subgroup.zpowers_le.mpr hw₀H)
  obtain ⟨k, hkH, hk⟩ := exists_mem_conj_of_fusionIsSylowIn hS₀ hS
  have hkv := hcommH k hkH
  have hkS := (Subgroup.mem_inf.mp hkH).2
  have hwS : k * w₀ * k⁻¹ ∈ S := (hk _).mpr (by
    rw [show k⁻¹ * (k * w₀ * k⁻¹) * k = w₀ by group]
    exact hw₀S₀ (Subgroup.mem_zpowers w₀))
  have hwv : Commute (k * w₀ * k⁻¹) v := (hkv.mul_left hw₀v).mul_left hkv.inv_left
  have hwvk : k * w₀ * k⁻¹ * v = k * (w₀ * v) * k⁻¹ := by
    calc k * w₀ * k⁻¹ * v = k * w₀ * (k⁻¹ * v) := by group
      _ = k * w₀ * (v * k⁻¹) := by rw [hkv.inv_left.eq]
      _ = k * (w₀ * v) * k⁻¹ := by group
  refine ⟨k * w₀ * k⁻¹, mem_longInvSwap_of_mem_stabilizer_pair (Ne.symm hbα)
      (conj_mem_longInv hw₀.1 k) (mul_mem (mul_mem hkS hw₀S) (inv_mem hkS)), hwv,
      hwvk ▸ conj_mem_longInv hw₀J k, S, hS.2.1, hwS, hτS (Subgroup.mem_zpowers τ),
      fun g hg => ?_⟩
  have hgH := hS.1 hg
  exact mem_normalizer_caseACentralizer_holtDelta (hcommH g hgH) (Subgroup.mem_inf.mp hgH).2

end Choice

section Certified

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)}

theorem Prop46Setup.exists_tau_of_isTypeBAt (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P)
    {β : Ω} (hβ : β ∈ p46Orbit G Ω v P α) (hβα : β ≠ α) (hB : IsTypeBAt G Ω α β) :
    ∃ τ : G, τ * τ = 1 ∧ Commute τ v ∧ τ • α = α ∧
      (∀ ω ∈ p46Orbit G Ω v P α, ω ≠ α → τ • ω = ω → ¬ IsTypeBAt G Ω α ω) ∧
      ∃ b ∈ p46Orbit G Ω v P α, b ≠ α ∧ τ • b = b ∧ 1 < Nat.card (holtDelta G Ω α b) ∧
        IsTypeAAt G Ω α b := by
  obtain ⟨γ, hC⟩ := hP.exists_prop46CaseB hβ hβα hB
  obtain ⟨s, -, -, -, -, τ, hτ2, hτv, -, -, hτα, -, hiff, ⟨b, hbE, hbα⟩, h3, htypes⟩ :=
    hC.exists_witness_tau_isTypeAAt hS hP
  have hbC := p46MinusSpace_subset_p46Orbit s hbE
  have hτb : τ • b = b := (hiff b hbC).mpr hbE
  exact ⟨τ, hτ2, hτv, hτα, fun ω hω hωα hτω => (htypes ω ((hiff ω hω).mp hτω) hωα).2,
    b, hbC, hbα, hτb, by have := h3 b hτb hbα; omega, (htypes b hbE hbα).1⟩

theorem Prop46Setup.nonempty_caseAStart (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P)
    (hP1 : P ≠ ⊥) : Nonempty (CaseAStart G Ω α v P) := by
  have hodd : Odd (Nat.card P) :=
    Odd.of_dvd_nat odd_card_pPrimeCore_two (Subgroup.card_dvd_of_le hP.le_oddCore)
  obtain ⟨β, hβα, hβC, h1⟩ := hS.exists_one_lt_card_holtDelta hP.typeL.orderOf_eq_two
    hP.typeL.smul_eq hP.normal hodd hP1
  rcases hP.typeAB β hβC hβα h1 with hA | hB
  · obtain ⟨X, -⟩ := hP.exists_caseAStart hβC hβα h1 hA
    exact ⟨X⟩
  · obtain ⟨-, -, -, -, -, b, hbC, hbα, -, h1b, hAb⟩ := hP.exists_tau_of_isTypeBAt hS hβC hβα hB
    obtain ⟨X, -⟩ := hP.exists_caseAStart hbC hbα h1b hAb
    exact ⟨X⟩

theorem Sec4Setting.exists_isTypeBAt_of_caseAStart (hS : Sec4Setting G Ω)
    (hP : Prop46Setup G Ω α v P) (h43 : ∀ a b : Ω, a ≠ b → IsEmpty (AltConfig G Ω a b))
    (hD : CaseAStepA7 G Ω α v P) (X₀ : CaseAStart G Ω α v P) :
    ∃ β ∈ p46Orbit G Ω v P α, β ≠ α ∧ IsTypeBAt G Ω α β := by
  obtain ⟨X, V, hVs, hVw, -⟩ := exists_isKappaMaximal hS hP X₀
  obtain ⟨r, β₁, γ₁, hout, -, hB, -⟩ := (hS.caseA_of_certificates hP h43 hD X₀).2 X V 1 hVs hVw
    (by rw [Subgroup.zpowers_one_eq_bot]; exact IsPGroup.of_bot) (one_mem _)
    (Commute.one_left v) (one_smul G α) (one_smul G X.β)
  exact ⟨β₁, hout.mem_β₁, hout.ne, hB⟩

theorem Sec4Setting.false_of_prop46Setup (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P)
    (h43 : ∀ a b : Ω, a ≠ b → IsEmpty (AltConfig G Ω a b)) (hD : CaseAStepA7 G Ω α v P)
    (hP1 : P ≠ ⊥) : False := by
  obtain ⟨X₀⟩ := hP.nonempty_caseAStart hS hP1
  have hCA := hS.caseA_of_certificates hP h43 hD X₀
  obtain ⟨β₁, hβ₁, hβ₁α, hB₁⟩ := hS.exists_isTypeBAt_of_caseAStart hP h43 hD X₀
  obtain ⟨τ, hτ2, hτv, hτα, hτB, b, hb, hbα, hτb, h1b, hAb⟩ :=
    hP.exists_tau_of_isTypeBAt hS hβ₁ hβ₁α hB₁
  obtain ⟨Xb, rfl⟩ := hP.exists_caseAStart hb hbα h1b hAb
  obtain ⟨-, -, hr, hT, hΛ⟩ := hCA.1 Xb
  obtain ⟨w, hw, hwv, hwvJ, T, hT2, hwT, hτT, hTN⟩ :=
    hP.exists_w_isPGroup hb hbα hτ2 hτv hτα hτb
  let X : CaseAStart G Ω α v P :=
    { Xb with
      w := w
      w_mem := hw
      w_comm := hwv
      wv_mem := hwvJ
      admissible := Or.inr (Or.inl ⟨hr, hT, hΛ⟩) }
  have hXΛ : X.Λ = holtDelta G Ω α X.β := hΛ
  obtain ⟨V, hVs, hTV⟩ := X.exists_sylow_le_normalizer hT2 (by rw [hXΛ]; exact hTN)
  obtain ⟨r, β₂, γ₂, hout, hτβ₂, hB₂, -⟩ := hCA.2 X V τ hVs (hTV hwT)
    (zpowers_isPGroup_two_of_pow_eq_one (n := 1) (by rw [pow_one, sq, hτ2])) (hTV hτT) hτv
    hτα hτb
  exact hτB β₂ hout.mem_β₁ hout.ne hτβ₂ hB₂

end Certified

section Main


variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω]

theorem Sec4Setting.pPrimeCore_typeLSection_eq_bot_of (hS : Sec4Setting G Ω)
    (h43 : ∀ a b : Ω, a ≠ b → IsEmpty (AltConfig G Ω a b))
    (hD : ∀ (α : Ω) (v : G) (P : Subgroup (typeLSection G Ω v)),
      Prop46Setup G Ω α v P → CaseAStepA7 G Ω α v P)
    {α : Ω} {v : G} (hv : IsTypeL G Ω α v) : CFSG.pPrimeCore 2 (typeLSection G Ω v) = ⊥ := by
  by_contra hQ
  obtain ⟨P, hPn, hP1, hPQ, hPmin⟩ := exists_normal_minimal_le CFSG.pPrimeCore_normal hQ
  have hP := hS.prop46Setup hv hPn hPmin hPQ
  exact hS.false_of_prop46Setup hP h43 (hD α v P hP) hP1

end Main

end CFSG.Holt.H78
