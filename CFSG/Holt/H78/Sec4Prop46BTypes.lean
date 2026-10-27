module

public import CFSG.Holt.H78.Sec4Prop46BRec4
public import CFSG.Holt.H78.Sec4Prop46A

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open CFSG.GH74.Uniqueness.Bender
open scoped Pointwise

section Defs

variable (G : Type) [Group G] (Ω : Type) [MulAction G Ω]

@[expose] def p46MinusSpace (v : G) (P : Subgroup (typeLSection G Ω v)) (α : Ω) (s : G) :
    Set Ω :=
  {ω | ∃ p ∈ P, ∃ a : fixSet Ω (Subgroup.zpowers v), (a : Ω) = α ∧ ((p • a : _) : Ω) = ω ∧
    s • ω = ((p⁻¹ • a : _) : Ω)}

end Defs

section Basic

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω] {v : G}
  {P : Subgroup (typeLSection G Ω v)} {α : Ω}

theorem p46MinusSpace_subset_p46Orbit (s : G) :
    p46MinusSpace G Ω v P α s ⊆ p46Orbit G Ω v P α := by
  rintro ω ⟨p, hp, a, ha, hpa, -⟩
  exact ⟨p, hp, a, ha, hpa⟩

end Basic

section Setup

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω] {α : Ω} {v : G}
  {P : Subgroup (typeLSection G Ω v)}

theorem Prop46Setup.exists_prop46CaseB (hP : Prop46Setup G Ω α v P) {β' : Ω}
    (hβ' : β' ∈ p46Orbit G Ω v P α) (hne : β' ≠ α) (hB : IsTypeBAt G Ω α β') :
    ∃ γ' : Ω, Prop46CaseB G Ω α β' γ' v P := by
  obtain ⟨γ', ⟨hγ'Δ, hγ'v⟩, hγ'u⟩ := hP.one_point β' hβ' hne
  exact ⟨γ', ⟨hP.typeL, Ne.symm hne, hP.normal, hP.minimal, hP.le_oddCore, hβ', hγ'Δ,
    fun δ hδ => ⟨fun h => hγ'u δ ⟨hδ, h⟩, fun h => h ▸ hγ'v⟩, hB.1, hB.2⟩⟩

end Setup

section Minus

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β γ : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)}

namespace Prop46CaseB

variable (hC : Prop46CaseB G Ω α β γ v P)
include hC

theorem exists_mem_P_smul_eq_inv (hS : Sec4Setting G Ω) {s : G} (hs : IsConj v s)
    (hsv : Commute s v) (hsΦ : fixedBy Ω s ≠ fixedBy Ω v) (hsα : s • α = α) :
    ∃ p ∈ P, p • (⟨α, hC.α_mem⟩ : fixSet Ω (Subgroup.zpowers v)) ≠ ⟨α, hC.α_mem⟩ ∧
      s • ((p • (⟨α, hC.α_mem⟩ : fixSet Ω (Subgroup.zpowers v)) : _) : Ω) =
        ((p⁻¹ • (⟨α, hC.α_mem⟩ : fixSet Ω (Subgroup.zpowers v)) : _) : Ω) := by
  classical
  set a : fixSet Ω (Subgroup.zpowers v) := ⟨α, hC.α_mem⟩ with ha
  by_contra hne
  push Not at hne
  have hs2 := hC.mul_self_eq_one_of_isConj hs
  set r := typeLElt (Ω := Ω) hsv with hr
  have hr2 : r * r = 1 := by
    rw [hr, typeLElt_mul]
    exact Subtype.ext (Equiv.ext fun ω => Subtype.ext (by
      change (s * s) • (ω : Ω) = ω; rw [hs2, one_smul]))
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  have hra : r • a = a := Subtype.ext hsα
  have hrsmul : ∀ ω : fixSet Ω (Subgroup.zpowers v), ((r • ω : fixSet Ω _) : Ω) = s • (ω : Ω) :=
    fun ω => rfl
  have hfix : ∀ p ∈ P, r • (p • a) = p • a := by
    intro p hp
    have hp' : p⁻¹ ∈ P := inv_mem hp
    set q := p⁻¹ * (r * p⁻¹ * r⁻¹)⁻¹ with hq
    have hqP : q ∈ P := mul_mem hp' (inv_mem (hC.normal.conj_mem _ hp' r))
    have hqinv : r • (q • a) = q⁻¹ • a := by
      have h1 : r * q = q⁻¹ * r := by
        rw [show r * q = r * p⁻¹ * r * p * r⁻¹ by rw [hq]; group,
          show q⁻¹ * r = r * p⁻¹ * r⁻¹ * p * r by rw [hq]; group, hrinv]
      rw [smul_smul, h1, ← smul_smul, hra]
    have hqa : q • a = a := by
      by_contra h
      exact hne q hqP h (by rw [← hrsmul, hqinv])
    have : (p⁻¹ * r * p * r) • a = a := by
      rw [show p⁻¹ * r * p * r = q by
        rw [hq, show p⁻¹ * (r * p⁻¹ * r⁻¹)⁻¹ = p⁻¹ * r * p * r⁻¹ by group, hrinv]]
      exact hqa
    rw [mul_smul, mul_smul, mul_smul, hra] at this
    have h2 := congrArg (fun x => p • x) this
    simp only [smul_inv_smul] at h2
    exact h2
  obtain ⟨p₀, hp₀, hp₀a⟩ := hC.exists_mem_P_smul_α_eq_β
  have hsβ : s • β = β := by
    have := congrArg Subtype.val (hfix p₀ hp₀)
    rw [hp₀a] at this
    exact this
  exact hC.false_of_witness_fix hS hC hs hsv hsΦ hsα hsβ

theorem exists_tau_isTypeAAt (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P) {s : G}
    (hs : IsConj v s) (hsv : Commute s v) (hsΦ : fixedBy Ω s ≠ fixedBy Ω v) (hsα : s • α = α) :
    ∃ τ : G, τ * τ = 1 ∧ Commute τ v ∧ Commute τ s ∧ s * τ ∈ longInvAt G Ω α ∧ τ • α = α ∧
      CFSG.pPrimeCore 2 (centralizerImage Ω (Subgroup.zpowers τ)) = ⊥ ∧
      (∀ ω ∈ p46Orbit G Ω v P α, τ • ω = ω ↔ ω ∈ p46MinusSpace G Ω v P α s) ∧
      (∃ β' ∈ p46MinusSpace G Ω v P α s, β' ≠ α) ∧
      (∀ β' : Ω, τ • β' = β' → β' ≠ α → 3 ≤ Nat.card (holtDelta G Ω α β')) ∧
      ∀ β' ∈ p46MinusSpace G Ω v P α s, β' ≠ α →
        IsTypeAAt G Ω α β' ∧ ¬ IsTypeBAt G Ω α β' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set a : fixSet Ω (Subgroup.zpowers v) := ⟨α, hC.α_mem⟩ with ha
  have hs2 := hC.mul_self_eq_one_of_isConj hs
  obtain ⟨-, Y, -, -, -, -, -, t', ht', ht's, -, ht'v, ht'C⟩ := hC.exists_Y_tau hS hs hsv hsΦ hsα
  have ht'2 := mul_self_eq_one_of_mem_longInv ht'.1
  set τ := s * t' with hτ
  have hτ2 : τ * τ = 1 := by
    rw [hτ, show s * t' * (s * t') = s * s * (t' * t') by
      rw [mul_assoc, ← mul_assoc t', ht's.eq]; group, hs2, ht'2, one_mul]
  have hτv : Commute τ v := hsv.mul_left ht'v
  have hτs : Commute τ s := (Commute.refl s).mul_left ht's
  have hsτ : s * τ ∈ longInvAt G Ω α := by rw [hτ, ← mul_assoc, hs2, one_mul]; exact ht'
  have hτα : τ • α = α := by rw [hτ, mul_smul, ht'.2, hsα]
  have hFτ : ∀ ω : Ω, s • ω = ω → τ • ω = ω → ω = α := fun ω hsω hτω => by
    have h' : t' • ω = ω := by
      rw [hτ, mul_smul, ← mul_smul, ← ht's.eq, mul_smul, hsω] at hτω
      exact hτω
    obtain ⟨ω₀, -, hω₀⟩ := ht'.1.2
    exact (hω₀ ω h').trans (hω₀ α ht'.2).symm
  have hτC : ∀ p ∈ P, τ • ((p • a : _) : Ω) = s • ((p⁻¹ • a : _) : Ω) := fun p hp => by
    rw [hτ, mul_smul, ht'C p hp]
  have hFC : ∀ ω ∈ p46Orbit G Ω v P α, τ • ω = ω ↔ ω ∈ p46MinusSpace G Ω v P α s := by
    rintro ω ⟨p, hp, a', ha', rfl⟩
    obtain rfl : a' = a := Subtype.ext ha'
    constructor
    · intro h
      refine ⟨p, hp, a, rfl, rfl, ?_⟩
      rw [hτC p hp] at h
      rw [← h, smul_smul, hs2, one_smul]
    · rintro ⟨p', hp', a'', ha'', hp'a, hsp'⟩
      obtain rfl : a'' = a := Subtype.ext ha''
      rw [← hp'a] at hsp' ⊢
      rw [hτC p' hp', ← hsp', smul_smul, hs2, one_smul]
  obtain ⟨p₁, hp₁, hp₁a, hsp₁⟩ := hC.exists_mem_P_smul_eq_inv hS hs hsv hsΦ hsα
  have hβ₀ : ((p₁ • a : _) : Ω) ∈ p46MinusSpace G Ω v P α s := ⟨p₁, hp₁, a, rfl, rfl, hsp₁⟩
  have hβ₀α : ((p₁ • a : _) : Ω) ≠ α := fun h => hp₁a (Subtype.ext h)
  have hτβ₀ : τ • ((p₁ • a : _) : Ω) = ((p₁ • a : _) : Ω) :=
    (hFC _ (p46MinusSpace_subset_p46Orbit s hβ₀)).mpr hβ₀
  have hτJ : τ ∉ longInv G Ω := fun h => by
    obtain ⟨ω, -, hω⟩ := h.2
    exact hβ₀α ((hω _ hτβ₀).trans (hω α hτα).symm)
  have hV : IsPGroup 2 (Subgroup.zpowers τ) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by rw [pow_one, sq, hτ2])
  have hmemV : ∀ {ω : Ω}, ω ∈ fixSet Ω (Subgroup.zpowers τ) ↔ τ • ω = ω := fun {ω} => by
    rw [fixSet_zpowers]; exact Iff.rfl
  have h3 : 3 ≤ Nat.card (fixSet Ω (Subgroup.zpowers τ)) := by
    rw [three_le_card_fixSet_iff hS.star.odd_card hV, Nat.card_coe_set_eq,
      Set.one_lt_ncard_iff (Set.toFinite _)]
    exact ⟨α, _, hmemV.mpr hτα, hmemV.mpr hτβ₀, Ne.symm hβ₀α⟩
  have hO := hC.pPrimeCore_centralizerImage_eq_bot hS hs hsv hsΦ hτ2 hτs hsτ.1 hτJ hsα hτα hFτ h3
  have hτ1 : τ ≠ 1 := fun h => by
    have hsJ : s ∈ longInv G Ω := by
      have := hsτ.1
      rwa [h, mul_one] at this
    obtain ⟨g, rfl⟩ := isConj_iff.mp hs
    obtain ⟨-, -, -, -, -, -, -, hvJ⟩ := hC.isTypeL
    exact hvJ ((conj_mem_longInv_iff g).mp hsJ)
  have hc : ∀ β' : Ω, τ • β' = β' → β' ≠ α → 3 ≤ Nat.card (holtDelta G Ω α β') := by
    intro β' hτβ' hne
    obtain ⟨D⟩ := hS.holtData_centralizerImage hV (Subgroup.zpowers_ne_bot.mpr hτ1) h3
    have hab : (⟨α, hmemV.mpr hτα⟩ : fixSet Ω (Subgroup.zpowers τ)) ≠ ⟨β', hmemV.mpr hτβ'⟩ :=
      fun h => hne (congrArg Subtype.val h).symm
    have h3' := D.three_le_card_holtDelta_of_ne
      (jOddCore_eq_bot_of_pPrimeCore_eq_bot (Ω := fixSet Ω (Subgroup.zpowers τ)) hO)
      (hS.star_centralizerImage hV h3) hab
    rw [Nat.card_congr (hS.holtDeltaCentralizerImageEquiv hV h3 hab), Nat.card_coe_set_eq]
      at h3'
    rw [Nat.card_coe_set_eq]
    exact h3'.trans (Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _))
  have hd : ∀ β' ∈ p46MinusSpace G Ω v P α s, β' ≠ α → ¬ IsTypeBAt G Ω α β' := by
    rintro β' hβ' hne hB
    obtain ⟨γ', hC'⟩ := hP.exists_prop46CaseB (p46MinusSpace_subset_p46Orbit s hβ') hne hB
    obtain ⟨p, hp, a', ha', hpa, hsp⟩ := hβ'
    obtain rfl : a' = ⟨α, hC'.α_mem⟩ := Subtype.ext ha'
    exact hC'.false_of_smul_eq_inv hS hs hsv hsΦ hsα hp hpa hsp
  refine ⟨τ, hτ2, hτv, hτs, hsτ, hτα, hO, hFC, ⟨_, hβ₀, hβ₀α⟩, hc, fun β' hβ' hne => ?_⟩
  have h1 := hc β' ((hFC β' (p46MinusSpace_subset_p46Orbit s hβ')).mpr hβ') hne
  have hnB := hd β' hβ' hne
  exact ⟨(hP.typeAB β' (p46MinusSpace_subset_p46Orbit s hβ') hne (by omega)).resolve_right hnB,
    hnB⟩

theorem exists_witness_smul_eq (hS : Sec4Setting G Ω) {s : G} (hs : IsConj v s)
    (hsv : Commute s v) (hsΦ : fixedBy Ω s ≠ fixedBy Ω v) :
    ∃ s' : G, IsConj v s' ∧ Commute s' v ∧ fixedBy Ω s' ≠ fixedBy Ω v ∧ s' • α = α := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs2 := hC.mul_self_eq_one_of_isConj hs
  have hsΦset : Subgroup.zpowers s ≤ stabilizer G (fixSet Ω (Subgroup.zpowers v)) :=
    Subgroup.zpowers_le.mpr (centralizer_le_stabilizer_fixSet _
      (mem_centralizer_zpowers_iff_commute.mpr hsv))
  have : Finite (fixSet Ω (Subgroup.zpowers v)) := Set.toFinite _
  obtain ⟨φ, hφΦ, hφs⟩ := exists_mem_fixSet_of_le_stabilizer
    (isPGroup_zpowers_of_pow_eq_one (k := 1) (by rw [pow_one, sq, hs2]))
    (hS.star.odd_card_fixSet (isPGroup_zpowers_of_orderOf_eq_two hC.orderOf_v)) hsΦset
  have := hC.isPretransitive_pPrimeCore hS
  obtain ⟨q, hq⟩ := exists_smul_eq (CFSG.pPrimeCore 2 (typeLSection G Ω v))
    (⟨φ, hφΦ⟩ : fixSet Ω (Subgroup.zpowers v)) ⟨α, hC.α_mem⟩
  obtain ⟨⟨c, hc⟩, hcq⟩ := (q : typeLSection G Ω v).2
  have hcv : Commute c v := mem_centralizer_zpowers_iff_commute.mp hc
  have hcφ : c • φ = α := by
    have h := congrArg Subtype.val hq
    change (((q : typeLSection G Ω v) : Equiv.Perm (fixSet Ω (Subgroup.zpowers v)))
      ⟨φ, hφΦ⟩ : Ω) = α at h
    rw [← hcq] at h
    exact h
  have hsφ : s • φ = φ := hφs s (Subgroup.mem_zpowers s)
  refine ⟨c * s * c⁻¹, hs.trans (isConj_iff.mpr ⟨c, rfl⟩), (hcv.mul_left hsv).mul_left
    hcv.inv_left, fun h => hsΦ ?_, by rw [← hcφ, mul_smul, mul_smul, inv_smul_smul, hsφ]⟩
  rw [← smul_fixedBy] at h
  rw [← inv_smul_smul c (fixedBy Ω s), h, smul_fixedBy, inv_inv, mul_assoc, ← hcv.eq,
    inv_mul_cancel_left]

end Prop46CaseB

end Minus

section B5

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β γ : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)}

namespace Prop46CaseB

variable (hC : Prop46CaseB G Ω α β γ v P)
include hC

theorem exists_witness_tau_isTypeAAt (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P) :
    ∃ s : G, IsConj v s ∧ Commute s v ∧ fixedBy Ω s ≠ fixedBy Ω v ∧ s • α = α ∧
      ∃ τ : G, τ * τ = 1 ∧ Commute τ v ∧ Commute τ s ∧ s * τ ∈ longInvAt G Ω α ∧ τ • α = α ∧
        CFSG.pPrimeCore 2 (centralizerImage Ω (Subgroup.zpowers τ)) = ⊥ ∧
        (∀ ω ∈ p46Orbit G Ω v P α, τ • ω = ω ↔ ω ∈ p46MinusSpace G Ω v P α s) ∧
        (∃ β' ∈ p46MinusSpace G Ω v P α s, β' ≠ α) ∧
        (∀ β' : Ω, τ • β' = β' → β' ≠ α → 3 ≤ Nat.card (holtDelta G Ω α β')) ∧
        ∀ β' ∈ p46MinusSpace G Ω v P α s, β' ≠ α →
          IsTypeAAt G Ω α β' ∧ ¬ IsTypeBAt G Ω α β' := by
  obtain ⟨s₀, hs₀, hs₀v, hs₀Φ⟩ := hC.exists_witness hS
  obtain ⟨s, hs, hsv, hsΦ, hsα⟩ := hC.exists_witness_smul_eq hS hs₀ hs₀v hs₀Φ
  exact ⟨s, hs, hsv, hsΦ, hsα, hC.exists_tau_isTypeAAt hS hP hs hsv hsΦ hsα⟩

end Prop46CaseB

end B5

end CFSG.Holt.H78
