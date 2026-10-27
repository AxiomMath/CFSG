module

public import CFSG.GH74.Uniqueness.Section15LastDefs

public section

namespace CFSG.GH74.Uniqueness.Section15Last

open Subgroup MulAction
open scoped Pointwise

variable {X : Type} [Group X] {M V R₀ Mo D K : Subgroup X} {u : X} {n : ℕ}

namespace FinalHyp

@[expose] def smulMo (h : FinalHyp M V R₀ Mo D K u n) (g : ↥M) (y : ↥Mo) : ↥Mo :=
  ⟨tt u g * ((g : X) * y * (g : X)⁻¹), Mo.mul_mem (h.tt_mem g.2) (h.Mo_norm g g.2 y y.2)⟩

theorem smulMo_coe (h : FinalHyp M V R₀ Mo D K u n) (g : ↥M) (y : ↥Mo) :
    (h.smulMo g y : X) = tt u g * ((g : X) * y * (g : X)⁻¹) := rfl

theorem smulMo_mul (h : FinalHyp M V R₀ Mo D K u n) (g k : ↥M) (y : ↥Mo) :
    h.smulMo (g * k) y = h.smulMo g (h.smulMo k y) := by
  apply Subtype.ext
  rw [smulMo_coe, smulMo_coe, smulMo_coe, Subgroup.coe_mul, h.tt_mul g.2 k.2]
  group

theorem smulMo_one (h : FinalHyp M V R₀ Mo D K u n) (y : ↥Mo) : h.smulMo 1 y = y := by
  apply Subtype.ext
  rw [smulMo_coe]
  have h1 : tt u ((1 : ↥M) : X) = 1 := tt_one h.u_sq
  rw [h1]
  simp

@[expose, instance_reducible] def pointAct (h : FinalHyp M V R₀ Mo D K u n) : MulAction ↥M ↥Mo where
  smul := h.smulMo
  one_smul := h.smulMo_one
  mul_smul := h.smulMo_mul

theorem smulMo_one_apply (h : FinalHyp M V R₀ Mo D K u n) (g : ↥M) :
    (h.smulMo g 1 : X) = tt u g := by
  rw [smulMo_coe]
  simp

theorem smulMo_one_eq_one_iff (h : FinalHyp M V R₀ Mo D K u n) (g : ↥M) :
    h.smulMo g 1 = 1 ↔ tt u g = 1 := by
  constructor
  · intro h1
    have := congrArg Subtype.val h1
    rw [smulMo_one_apply] at this
    exact this
  · intro h1
    apply Subtype.ext
    rw [smulMo_one_apply]
    exact h1

theorem smulMo_of_tt_eq_one (h : FinalHyp M V R₀ Mo D K u n) {g : ↥M} (hg : tt u g = 1)
    (y : ↥Mo) : (h.smulMo g y : X) = (g : X) * y * (g : X)⁻¹ := by
  rw [smulMo_coe, hg, one_mul]

theorem exists_smulMo_eq (h : FinalHyp M V R₀ Mo D K u n) (y : ↥Mo) :
    ∃ g : ↥M, h.smulMo g 1 = y := by
  obtain ⟨r, hr, hry⟩ := h.exists_sq_eq y.2
  have hxV : u * r ∈ V := V.mul_mem h.u_mem (h.R₀_le hr)
  have hxR : u * r ∉ R₀ := by
    intro hx
    apply h.u_not_mem
    have := R₀.mul_mem hx (R₀.inv_mem hr)
    simpa using this
  obtain ⟨g, hgM, hgx⟩ := h.V_conj _ hxV hxR
  refine ⟨⟨g, hgM⟩, Subtype.ext ?_⟩
  rw [smulMo_one_apply]
  have hc : cc u g = r := by
    unfold cc
    rw [hgx, ← mul_assoc, h.u_sq, one_mul]
  unfold tt
  rw [hc, hry]

theorem smulMo_trivial_iff (h : FinalHyp M V R₀ Mo D K u n) (g : ↥M) :
    (∀ y, h.smulMo g y = y) ↔ (g : X) ∈ V := by
  constructor
  · intro hg
    have h1 : tt u g = 1 := (h.smulMo_one_eq_one_iff g).mp (hg 1)
    refine h.C_Mo g g.2 fun x hx => ?_
    have h2 := congrArg Subtype.val (hg ⟨x, hx⟩)
    rw [h.smulMo_of_tt_eq_one h1] at h2
    have h3 : (g : X) * x * (g : X)⁻¹ = x := h2
    calc (g : X) * x = (g : X) * x * (g : X)⁻¹ * g := by group
      _ = x * g := by rw [h3]
  · intro hg y
    have h1 : tt u g = 1 := h.tt_V hg
    apply Subtype.ext
    rw [h.smulMo_of_tt_eq_one h1]
    have := h.V_comm_Mo hg y.2
    calc (g : X) * y * (g : X)⁻¹ = (y : X) * g * (g : X)⁻¹ := by rw [this]
      _ = y := by group

theorem smulMo_D (h : FinalHyp M V R₀ Mo D K u n) {k : X} (hk : k ∈ D) (y : ↥Mo) :
    (h.smulMo ⟨k, h.D_le hk⟩ y : X) = k * y * k⁻¹ :=
  h.smulMo_of_tt_eq_one (g := ⟨k, h.D_le hk⟩) (h.tt_D hk) y

section Finite

variable [Finite X]

theorem exists_mul_of_tt_eq_one (h : FinalHyp M V R₀ Mo D K u n) (g : ↥M) (hg : tt u g = 1) :
    ∃ v ∈ V, ∃ d ∈ D, (g : X) = v * d := by
  let _ : MulAction ↥M ↥Mo := h.pointAct
  have hpre : IsPretransitive ↥M ↥Mo := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨g₁, hg₁⟩ := h.exists_smulMo_eq x
    obtain ⟨g₂, hg₂⟩ := h.exists_smulMo_eq y
    refine ⟨g₂ * g₁⁻¹, ?_⟩
    have e1 : g₁ • (1 : ↥Mo) = x := hg₁
    have e2 : g₂ • (1 : ↥Mo) = y := hg₂
    rw [← e1, ← e2, mul_smul, inv_smul_smul]
  let St : Subgroup ↥M := stabilizer ↥M (1 : ↥Mo)
  have hSt : ∀ g : ↥M, g ∈ St ↔ tt u g = 1 := fun g => by
    rw [show St = stabilizer ↥M (1 : ↥Mo) from rfl, mem_stabilizer_iff]
    exact h.smulMo_one_eq_one_iff g
  have hidx : St.index = 2 ^ n := by
    rw [show St = stabilizer ↥M (1 : ↥Mo) from rfl, index_stabilizer, orbit_eq_univ,
      Set.ncard_univ, h.card_Mo]
  have hcardSt : Nat.card St = 2 ^ (2 * n) * Nat.card D := by
    have h1 := Subgroup.card_mul_index St
    rw [hidx] at h1
    have hpos : 0 < 2 ^ n := by positivity
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [h1, h.card_M]
    ring
  let V' : Subgroup ↥M := V.subgroupOf M
  let D' : Subgroup ↥M := D.subgroupOf M
  have hV'n : V'.Normal := ⟨fun x hx g => h.V_norm g g.2 x hx⟩
  have hW_le : V' ⊔ D' ≤ St := sup_le (fun v hv => (hSt v).mpr (h.tt_V hv))
    (fun d hd => (hSt d).mpr (h.tt_D hd))
  have hprod : Nat.card ↥(V' ⊔ D') * Nat.card ↥(V' ⊓ D') = Nat.card V' * Nat.card D' := by
    have h1 := Subgroup.relIndex_mul_card (H := V') (K := V' ⊔ D')
    rw [Subgroup.relIndex_sup_left, inf_eq_left.mpr le_sup_left] at h1
    have h2 := Subgroup.relIndex_mul_card (H := V') (K := D')
    rw [← h1, ← h2]
    ring
  have hV'c : Nat.card V' = 2 ^ (2 * n + 1) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.V_le).toEquiv, h.card_V]
  have hD'c : Nat.card D' = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.D_le).toEquiv
  have hinf : Nat.card ↥(V' ⊓ D') ≤ 2 := by
    have hsub : ((V' ⊓ D' : Subgroup ↥M) : Set ↥M) ⊆ {1, ⟨u, h.u_mem_M⟩} := by
      intro x hx
      obtain ⟨hxV, hxD⟩ := hx
      rcases h.D_V x hxD hxV with h1 | h1
      · exact Or.inl (Subtype.ext h1)
      · exact Or.inr (Subtype.ext h1)
    calc Nat.card ↥(V' ⊓ D') = Set.ncard ((V' ⊓ D' : Subgroup ↥M) : Set ↥M) :=
          (Nat.card_coe_set_eq _).symm
      _ ≤ Set.ncard ({1, ⟨u, h.u_mem_M⟩} : Set ↥M) := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  have hWcard : 2 ^ (2 * n) * Nat.card D ≤ Nat.card ↥(V' ⊔ D') := by
    have h1 := hprod
    rw [hV'c, hD'c] at h1
    have h4 : 2 * (2 ^ (2 * n) * Nat.card D) ≤ 2 * Nat.card ↥(V' ⊔ D') := by
      calc 2 * (2 ^ (2 * n) * Nat.card D) = 2 ^ (2 * n + 1) * Nat.card D := by ring
        _ = Nat.card ↥(V' ⊔ D') * Nat.card ↥(V' ⊓ D') := h1.symm
        _ ≤ Nat.card ↥(V' ⊔ D') * 2 := Nat.mul_le_mul_left _ hinf
        _ = 2 * Nat.card ↥(V' ⊔ D') := mul_comm _ _
    exact Nat.le_of_mul_le_mul_left h4 (by norm_num)
  have hWSt : V' ⊔ D' = St :=
    Subgroup.eq_of_le_of_card_ge hW_le (by rw [hcardSt]; exact hWcard)
  have hgSt : g ∈ V' ⊔ D' := by rw [hWSt]; exact (hSt g).mpr hg
  have hset : (↑(V' ⊔ D') : Set ↥M) = (V' : Set ↥M) * (D' : Set ↥M) :=
    Subgroup.normal_mul V' D'
  have hgmem : g ∈ (V' : Set ↥M) * (D' : Set ↥M) := by rw [← hset]; exact hgSt
  obtain ⟨v, hv, d, hd, hvd⟩ := Set.mem_mul.mp hgmem
  exact ⟨v, hv, d, hd, by rw [← hvd]; rfl⟩

omit [Finite X] in
theorem exists_smulMo_two (h : FinalHyp M V R₀ Mo D K u n) {a b c d : ↥Mo} (hab : a ≠ b)
    (hcd : c ≠ d) : ∃ g : ↥M, h.smulMo g a = c ∧ h.smulMo g b = d := by
  let _ : MulAction ↥M ↥Mo := h.pointAct
  have hto1 : ∀ x : ↥Mo, ∃ g : ↥M, g • x = 1 := by
    intro x
    obtain ⟨g, hg⟩ := h.exists_smulMo_eq x
    refine ⟨g⁻¹, ?_⟩
    have e1 : g • (1 : ↥Mo) = x := hg
    rw [← e1, inv_smul_smul]
  obtain ⟨g₁, hg₁⟩ := hto1 a
  obtain ⟨g₂, hg₂⟩ := hto1 c
  have hb : g₁ • b ≠ 1 := by
    intro h1
    apply hab
    have h2 : g₁ • b = g₁ • a := by rw [h1, hg₁]
    exact (smul_left_cancel g₁ h2).symm
  have hd : g₂ • d ≠ 1 := by
    intro h1
    apply hcd
    have h2 : g₂ • d = g₂ • c := by rw [h1, hg₂]
    exact (smul_left_cancel g₂ h2).symm
  have hb' : ((g₁ • b : ↥Mo) : X) ≠ 1 := fun h1 => hb (Subtype.ext h1)
  have hd' : ((g₂ • d : ↥Mo) : X) ≠ 1 := fun h1 => hd (Subtype.ext h1)
  obtain ⟨k, hk, hkbd⟩ := h.K_trans _ (g₁ • b).2 hb' _ (g₂ • d).2 hd'
  let kM : ↥M := ⟨k, h.D_le (h.K_le hk)⟩
  have hkM1 : kM • (1 : ↥Mo) = 1 := (h.smulMo_one_eq_one_iff kM).mpr (h.tt_D (h.K_le hk))
  have hkMb : kM • (g₁ • b) = g₂ • d := Subtype.ext (by
    show (h.smulMo kM (g₁ • b) : X) = _
    rw [h.smulMo_D (h.K_le hk)]
    exact hkbd)
  refine ⟨g₂⁻¹ * kM * g₁, ?_, ?_⟩
  · show (g₂⁻¹ * kM * g₁) • a = c
    rw [mul_smul, mul_smul, hg₁, hkM1, ← hg₂, inv_smul_smul]
  · show (g₂⁻¹ * kM * g₁) • b = d
    rw [mul_smul, mul_smul, hkMb, inv_smul_smul]

end Finite

end FinalHyp

end CFSG.GH74.Uniqueness.Section15Last
