module

public import CFSG.Holt.H78.Sec4Prop46BRec2
public import CFSG.Holt.H78.Sec4Prop46BRec

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open CFSG.GH74.Uniqueness.Bender
open scoped Pointwise

section Fix

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω]

theorem ncard_holtDelta_inter_fixSet_eq_three {α β : Ω} {τ : G}
    (hτP : τ ∈ stabilizer G ({α, β} : Set Ω)) [Finite (holtDelta G Ω α β)]
    (h5 : Nat.card (holtDelta G Ω α β) = 5)
    (hπ : {δ | twoPointHom G Ω α β ⟨τ, hτP⟩ δ ≠ δ}.ncard = 2) :
    (holtDelta G Ω α β ∩ fixSet Ω (Subgroup.zpowers τ)).ncard = 3 := by
  have himage : holtDelta G Ω α β ∩ fixSet Ω (Subgroup.zpowers τ) =
      Subtype.val '' {δ | twoPointHom G Ω α β ⟨τ, hτP⟩ δ ≠ δ}ᶜ := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_compl_iff, Set.mem_ofPred_eq,
      not_not, fixSet_zpowers, mem_fixedBy]
    constructor
    · rintro ⟨hΔ, hF⟩
      exact ⟨⟨ω, hΔ⟩, Subtype.ext (by rw [coe_twoPointHom_apply]; exact hF), rfl⟩
    · rintro ⟨δ, hδ, rfl⟩
      refine ⟨δ.2, ?_⟩
      have := congrArg Subtype.val hδ
      rwa [coe_twoPointHom_apply] at this
  rw [himage, Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_compl, hπ, h5]

end Fix

section Sylow

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β γ : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)}

namespace Prop46CaseB

variable (hC : Prop46CaseB G Ω α β γ v P)
include hC

theorem card_le_two_of_isPGroup (hS : Sec4Setting G Ω) {τ : G} (hτ2 : τ * τ = 1)
    (hτP : τ ∈ stabilizer G ({α, β} : Set Ω)) (h5 : Nat.card (holtDelta G Ω α β) = 5)
    (hπ : {δ | twoPointHom G Ω α β ⟨τ, hτP⟩ δ ≠ δ}.ncard = 2)
    (h3 : 3 ≤ Nat.card (fixSet Ω (Subgroup.zpowers τ)))
    (hα : α ∈ fixSet Ω (Subgroup.zpowers τ)) (hβ : β ∈ fixSet Ω (Subgroup.zpowers τ))
    (Q : Subgroup (centralizerImage Ω (Subgroup.zpowers τ))) (hQ : IsPGroup 2 Q)
    (hQab : ∀ q ∈ Q, q • (⟨α, hα⟩ : fixSet Ω (Subgroup.zpowers τ)) = ⟨α, hα⟩ ∧
      q • (⟨β, hβ⟩ : fixSet Ω (Subgroup.zpowers τ)) = ⟨β, hβ⟩) :
    Nat.card Q ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV : IsPGroup 2 (Subgroup.zpowers τ) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by rw [pow_one, sq, hτ2])
  have hab : (⟨α, hα⟩ : fixSet Ω (Subgroup.zpowers τ)) ≠ ⟨β, hβ⟩ :=
    fun h => hC.ne (congrArg Subtype.val h)
  have hmemV : ∀ {ω : Ω}, ω ∈ fixSet Ω (Subgroup.zpowers τ) ↔ τ • ω = ω := fun {ω} => by
    rw [fixSet_zpowers]; exact Iff.rfl
  have hcard : Nat.card (holtDelta (centralizerImage Ω (Subgroup.zpowers τ))
      (fixSet Ω (Subgroup.zpowers τ)) ⟨α, hα⟩ ⟨β, hβ⟩) = 3 := by
    rw [Nat.card_congr (hS.holtDeltaCentralizerImageEquiv hV h3 hab), Nat.card_coe_set_eq]
    exact ncard_holtDelta_inter_fixSet_eq_three hτP h5 hπ
  have hQs : Q ≤ stabilizer (centralizerImage Ω (Subgroup.zpowers τ))
      (holtDelta (centralizerImage Ω (Subgroup.zpowers τ)) (fixSet Ω (Subgroup.zpowers τ))
        ⟨α, hα⟩ ⟨β, hβ⟩) := fun q hq => by
    rw [mem_stabilizer_iff, smul_holtDelta, (hQab q hq).1, (hQab q hq).2]
  have hπ2 : twoPointHom G Ω α β ⟨τ, hτP⟩ * twoPointHom G Ω α β ⟨τ, hτP⟩ = 1 := by
    rw [← map_mul, show (⟨τ, hτP⟩ * ⟨τ, hτP⟩ : stabilizer G ({α, β} : Set Ω)) = 1 from
      Subtype.ext hτ2, map_one]
  refine card_le_two_of_injective hQ hcard (inducedHom Q _ hQs)
    ((injective_iff_map_eq_one _).mpr fun q hq => ?_)
  obtain ⟨c, hcV, hcq⟩ := mem_centralizerImage.mp (q : centralizerImage Ω (Subgroup.zpowers τ)).2
  have hcτ : Commute c τ := mem_centralizer_zpowers_iff_commute.mp hcV
  have hcα : c • α = α := (hcq ⟨α, hα⟩).symm.trans (congrArg Subtype.val (hQab q q.2).1)
  have hcβ : c • β = β := (hcq ⟨β, hβ⟩).symm.trans (congrArg Subtype.val (hQab q q.2).2)
  have hcP : c ∈ stabilizer G ({α, β} : Set Ω) := stabilizer_inf_le_stabilizer_pair α β
    (Subgroup.mem_inf.mpr ⟨mem_stabilizer_iff.mpr hcα, mem_stabilizer_iff.mpr hcβ⟩)
  have hρπ : twoPointHom G Ω α β ⟨c, hcP⟩ * twoPointHom G Ω α β ⟨τ, hτP⟩ =
      twoPointHom G Ω α β ⟨τ, hτP⟩ * twoPointHom G Ω α β ⟨c, hcP⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext hcτ.eq)
  have hρfix : ∀ δ : holtDelta G Ω α β, twoPointHom G Ω α β ⟨τ, hτP⟩ δ = δ →
      twoPointHom G Ω α β ⟨c, hcP⟩ δ = δ := fun δ hδ => by
    have hτδ : τ • (δ : Ω) = δ := by
      have := congrArg Subtype.val hδ
      rwa [coe_twoPointHom_apply] at this
    have hδF : (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers τ) := hmemV.mpr hτδ
    have hδΔ' : (⟨δ, hδF⟩ : fixSet Ω (Subgroup.zpowers τ)) ∈ holtDelta
        (centralizerImage Ω (Subgroup.zpowers τ)) (fixSet Ω (Subgroup.zpowers τ)) ⟨α, hα⟩
        ⟨β, hβ⟩ := (hS.mem_holtDelta_centralizerImage_iff hV h3 hab).mpr δ.2
    have h1 : inducedHom Q _ hQs q ⟨_, hδΔ'⟩ = ⟨_, hδΔ'⟩ := by rw [hq]; rfl
    have h2 : (((q : centralizerImage Ω (Subgroup.zpowers τ)) •
        (⟨δ, hδF⟩ : fixSet Ω (Subgroup.zpowers τ)) : fixSet Ω (Subgroup.zpowers τ)) : Ω) = δ :=
      congrArg (fun x => x.1.1) h1
    refine Subtype.ext ?_
    rw [coe_twoPointHom_apply]
    exact (hcq ⟨δ, hδF⟩).symm.trans h2
  have hτα : τ • α = α := hmemV.mp hα
  have hτβ : τ • β = β := hmemV.mp hβ
  obtain ⟨k, hkK, hkτ, hkc⟩ : ∃ k ∈ twoPointKernel G Ω α β, Commute k τ ∧
      ∀ ω ∈ fixSet Ω (Subgroup.zpowers τ), k • ω = c • ω := by
    rcases eq_one_or_eq_of_commute_of_fix hπ2 hπ hρπ hρfix with h | h
    · exact ⟨c, mem_twoPointKernel_of_twoPointHom_eq_one hcP hcα hcβ h, hcτ, fun ω _ => rfl⟩
    · have hcτP : c * τ ∈ stabilizer G ({α, β} : Set Ω) := mul_mem hcP hτP
      refine ⟨c * τ, mem_twoPointKernel_of_twoPointHom_eq_one hcτP
        (by rw [mul_smul, hτα, hcα]) (by rw [mul_smul, hτβ, hcβ]) ?_,
        hcτ.mul_left (Commute.refl τ), fun ω hω => by rw [mul_smul, hmemV.mp hω]⟩
      rw [show (⟨c * τ, hcτP⟩ : stabilizer G ({α, β} : Set Ω)) = ⟨c, hcP⟩ * ⟨τ, hτP⟩ from rfl,
        map_mul, h, hπ2]
  have hkC : k ∈ Subgroup.centralizer ((Subgroup.zpowers τ : Subgroup G) : Set G) :=
    mem_centralizer_zpowers_iff_commute.mpr hkτ
  have hqk : ((q : centralizerImage Ω (Subgroup.zpowers τ)) : Equiv.Perm _) =
      MulAction.toPermHom (Subgroup.centralizer ((Subgroup.zpowers τ : Subgroup G) : Set G))
        (fixSet Ω (Subgroup.zpowers τ)) ⟨k, hkC⟩ :=
    Equiv.ext fun ω => Subtype.ext ((hcq ω).trans (hkc ω ω.2).symm)
  have hodd : Odd (orderOf k) := hC.odd_card.of_dvd_nat
    ((twoPointKernel G Ω α β).orderOf_dvd_natCard hkK)
  have hodd' : Odd (orderOf q) := by
    refine hodd.of_dvd_nat ?_
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe, hqk, ← Subgroup.orderOf_mk k hkC]
    exact orderOf_map_dvd _ _
  obtain ⟨m, hm⟩ := hQ q
  have hdvd : orderOf q ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
    ((Nat.coprime_two_right.mpr hodd').pow_right m) hdvd)

end Prop46CaseB

end Sylow

section Rec

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β γ : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)}

namespace Prop46CaseB

variable (hC : Prop46CaseB G Ω α β γ v P)
include hC

theorem exists_swap_centralizerImage (hS : Sec4Setting G Ω) {τ : G} (hτ2 : τ * τ = 1)
    (hτv : Commute τ v) (hτγ : τ • γ = γ)
    (h3Δ : (holtDelta G Ω α β ∩ fixSet Ω (Subgroup.zpowers τ)).ncard = 3)
    (h3 : 3 ≤ Nat.card (fixSet Ω (Subgroup.zpowers τ)))
    (hα : α ∈ fixSet Ω (Subgroup.zpowers τ)) (hβ : β ∈ fixSet Ω (Subgroup.zpowers τ)) :
    ∃ g : centralizerImage Ω (Subgroup.zpowers τ),
      g • (⟨α, hα⟩ : fixSet Ω (Subgroup.zpowers τ)) = ⟨α, hα⟩ ∧
      g • (⟨β, hβ⟩ : fixSet Ω (Subgroup.zpowers τ)) = ⟨β, hβ⟩ ∧
      ∃ δ₁ δ₂ : holtDelta (centralizerImage Ω (Subgroup.zpowers τ))
          (fixSet Ω (Subgroup.zpowers τ)) ⟨α, hα⟩ ⟨β, hβ⟩, δ₁ ≠ δ₂ ∧
        ∀ δ : holtDelta (centralizerImage Ω (Subgroup.zpowers τ)) (fixSet Ω (Subgroup.zpowers τ))
          ⟨α, hα⟩ ⟨β, hβ⟩, g • (δ : fixSet Ω (Subgroup.zpowers τ)) = Equiv.swap δ₁ δ₂ δ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV : IsPGroup 2 (Subgroup.zpowers τ) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by rw [pow_one, sq, hτ2])
  have hab : (⟨α, hα⟩ : fixSet Ω (Subgroup.zpowers τ)) ≠ ⟨β, hβ⟩ :=
    fun h => hC.ne (congrArg Subtype.val h)
  have hmemV : ∀ {ω : Ω}, ω ∈ fixSet Ω (Subgroup.zpowers τ) ↔ τ • ω = ω := fun {ω} => by
    rw [fixSet_zpowers]; exact Iff.rfl
  have hvC : v ∈ Subgroup.centralizer ((Subgroup.zpowers τ : Subgroup G) : Set G) :=
    mem_centralizer_zpowers_iff_commute.mpr hτv.symm
  set Λ := holtDelta G Ω α β ∩ fixSet Ω (Subgroup.zpowers τ) with hΛ
  have hγΛ : γ ∈ Λ := ⟨hC.mem_holtDelta, hmemV.mpr hτγ⟩
  obtain ⟨δ₃, hδ₃, hδ₃γ⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < Λ.ncard) γ
  have hvΛ : ∀ {ω : Ω}, ω ∈ Λ → v • ω ∈ Λ := fun {ω} hω =>
    ⟨smul_mem_holtDelta_of_mem_pair hC.v_mem_pair hω.1, hmemV.mpr (by
      rw [← mul_smul, hτv.eq, mul_smul, hmemV.mp hω.2])⟩
  set δ₄ := v • δ₃ with hδ₄
  have hδ₄Λ : δ₄ ∈ Λ := hvΛ hδ₃
  have hvv : ∀ ω : Ω, v • v • ω = ω := fun ω => by rw [smul_smul, hC.v_mul_v, one_smul]
  have h34 : δ₃ ≠ δ₄ := fun h => hδ₃γ ((hC.fixed_iff δ₃ hδ₃.1).mp h.symm)
  have h4γ : δ₄ ≠ γ := fun h => hδ₃γ (by
    rw [← hvv δ₃, ← hδ₄, h, hC.smul_γ])
  have hΛeq : ∀ ω ∈ Λ, ω = γ ∨ ω = δ₃ ∨ ω = δ₄ := by
    have hsub : ({γ, δ₃, δ₄} : Set Ω) ⊆ Λ := by
      intro ω hω
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hω
      rcases hω with rfl | rfl | rfl
      exacts [hγΛ, hδ₃, hδ₄Λ]
    have hc : ({γ, δ₃, δ₄} : Set Ω).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by simp [Ne.symm hδ₃γ, Ne.symm h4γ]),
        Set.ncard_pair h34]
    have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hc, h3Δ]) (Set.toFinite _)
    intro ω hω
    rw [← heq] at hω
    simpa using hω
  have hiff := fun (δ : fixSet Ω (Subgroup.zpowers τ)) =>
    hS.mem_holtDelta_centralizerImage_iff hV h3 hab (δ := δ)
  set d₃ : holtDelta (centralizerImage Ω (Subgroup.zpowers τ)) (fixSet Ω (Subgroup.zpowers τ))
    ⟨α, hα⟩ ⟨β, hβ⟩ := ⟨⟨δ₃, hδ₃.2⟩, (hiff _).mpr hδ₃.1⟩ with hd₃
  set d₄ : holtDelta (centralizerImage Ω (Subgroup.zpowers τ)) (fixSet Ω (Subgroup.zpowers τ))
    ⟨α, hα⟩ ⟨β, hβ⟩ := ⟨⟨δ₄, hδ₄Λ.2⟩, (hiff _).mpr hδ₄Λ.1⟩ with hd₄
  have hd34 : d₃ ≠ d₄ := fun h => h34 (congrArg (fun x => x.1.1) h)
  refine ⟨centralizerImageElt hvC, Subtype.ext hC.smul_α, Subtype.ext hC.smul_β, d₃, d₄, hd34,
    fun δ => ?_⟩
  have hδΛ : (δ : fixSet Ω (Subgroup.zpowers τ)).1 ∈ Λ := ⟨(hiff _).mp δ.2, δ.1.2⟩
  refine Subtype.ext ?_
  change v • ((δ : fixSet Ω (Subgroup.zpowers τ)) : Ω) = ((Equiv.swap d₃ d₄ δ : _) : Ω)
  rcases hΛeq _ hδΛ with h | h | h
  · have h3' : δ ≠ d₃ := fun e => hδ₃γ (by rw [← h, e])
    have h4' : δ ≠ d₄ := fun e => h4γ (by rw [← h, e])
    rw [Equiv.swap_apply_of_ne_of_ne h3' h4', h, hC.smul_γ]
  · have e : δ = d₃ := Subtype.ext (Subtype.ext h)
    rw [e, Equiv.swap_apply_left]
  · have e : δ = d₄ := Subtype.ext (Subtype.ext h)
    rw [e, Equiv.swap_apply_right]
    exact hvv δ₃

theorem rec_of_smul_eq_inv (hS : Sec4Setting G Ω) {s : G} (hs : IsConj v s)
    (hsv : Commute s v) (hsΦ : fixedBy Ω s ≠ fixedBy Ω v) (hsα : s • α = α)
    {p₀ : typeLSection G Ω v} (hp₀ : p₀ ∈ P)
    (hp₀β : ((p₀ • (⟨α, hC.α_mem⟩ : fixSet Ω (Subgroup.zpowers v)) : _) : Ω) = β)
    (hH : s • β = ((p₀⁻¹ • (⟨α, hC.α_mem⟩ : fixSet Ω (Subgroup.zpowers v)) : _) : Ω)) :
    ∃ τ : G, τ * τ = 1 ∧ Commute τ v ∧ Commute τ s ∧ s * τ ∈ longInvAt G Ω α ∧ τ • α = α ∧
      τ • β = β ∧ τ • γ = γ ∧ Nat.card (holtDelta G Ω α β) = 5 ∧
      twoPointSection G Ω α β = ⊤ ∧
      (holtDelta G Ω α β ∩ fixSet Ω (Subgroup.zpowers τ)).ncard = 3 ∧
      Nat.card (fixSet Ω (Subgroup.zpowers τ)) = 5 ∧
      centralizerImage Ω (Subgroup.zpowers τ) = ⊤ ∧
      ∃ hτP : τ ∈ stabilizer G ({α, β} : Set Ω),
        {δ | twoPointHom G Ω α β ⟨τ, hτP⟩ δ ≠ δ}.ncard = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨τ, hτ2, hτv, hτs, hsτ, hτα, hτβ, hτγ, hFτ, h5, hG, hτP, hπ⟩ :=
    hC.exists_tau_of_smul_eq_inv hS hs hsv hsΦ hsα hp₀ hp₀β hH
  have h3Δ := ncard_holtDelta_inter_fixSet_eq_three hτP h5 hπ
  have hV : IsPGroup 2 (Subgroup.zpowers τ) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by rw [pow_one, sq, hτ2])
  have hmemV : ∀ {ω : Ω}, ω ∈ fixSet Ω (Subgroup.zpowers τ) ↔ τ • ω = ω := fun {ω} => by
    rw [fixSet_zpowers]; exact Iff.rfl
  have hα := hmemV.mpr hτα
  have hβ := hmemV.mpr hτβ
  have hγ := hmemV.mpr hτγ
  have hαγ : α ≠ γ := fun h => by
    have hγΔ := hC.mem_holtDelta
    rw [← h] at hγΔ
    exact left_notMem_holtDelta hC.ne hγΔ
  have hβγ : β ≠ γ := fun h => by
    have hγΔ := hC.mem_holtDelta
    rw [← h] at hγΔ
    exact right_notMem_holtDelta hC.ne hγΔ
  have h3 : 3 ≤ Nat.card (fixSet Ω (Subgroup.zpowers τ)) := by
    rw [Nat.card_coe_set_eq]
    have hsub : ({α, β, γ} : Set Ω) ⊆ fixSet Ω (Subgroup.zpowers τ) := by
      intro ω hω
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hω
      rcases hω with rfl | rfl | rfl
      exacts [hα, hβ, hγ]
    have hc : ({α, β, γ} : Set Ω).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by simp [hC.ne, hαγ]), Set.ncard_pair hβγ]
    exact hc ▸ Set.ncard_le_ncard hsub (Set.toFinite _)
  have hτ1 : τ ≠ 1 := fun h => by
    have : {δ | twoPointHom G Ω α β ⟨τ, hτP⟩ δ ≠ δ} = ∅ := by
      ext δ
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact Subtype.ext (by rw [coe_twoPointHom_apply]; exact h ▸ one_smul G (δ : Ω))
    rw [this, Set.ncard_empty] at hπ
    omega
  have hT := hS.holtData_centralizerImage hV (Subgroup.zpowers_ne_bot.mpr hτ1) h3
  have hτJ : τ ∉ longInv G Ω := fun h => by
    obtain ⟨ω, -, hω⟩ := h.2
    exact hC.ne ((hω α hτα).trans (hω β hτβ).symm)
  have hO := hC.pPrimeCore_centralizerImage_eq_bot hS hs hsv hsΦ hτ2 hτs hsτ.1 hτJ hsα hτα hFτ h3
  have hO' := jOddCore_eq_bot_of_pPrimeCore_eq_bot (Ω := fixSet Ω (Subgroup.zpowers τ)) hO
  have hab : (⟨α, hα⟩ : fixSet Ω (Subgroup.zpowers τ)) ≠ ⟨β, hβ⟩ :=
    fun h => hC.ne (congrArg Subtype.val h)
  have hcard : Nat.card (holtDelta (centralizerImage Ω (Subgroup.zpowers τ))
      (fixSet Ω (Subgroup.zpowers τ)) ⟨α, hα⟩ ⟨β, hβ⟩) = 3 := by
    rw [Nat.card_congr (hS.holtDeltaCentralizerImageEquiv hV h3 hab), Nat.card_coe_set_eq]
    exact h3Δ
  obtain ⟨h5F, htop⟩ := eq_top_of_exists_swap hT hO' hab
    (hC.card_le_two_of_isPGroup hS hτ2 hτP h5 hπ h3 hα hβ) hcard.le
    (hC.exists_swap_centralizerImage hS hτ2 hτv hτγ h3Δ h3 hα hβ)
  exact ⟨τ, hτ2, hτv, hτs, hsτ, hτα, hτβ, hτγ, h5, hG, h3Δ, by rwa [Nat.card_eq_fintype_card],
    htop, hτP, hπ⟩

end Prop46CaseB

end Rec

end CFSG.Holt.H78
