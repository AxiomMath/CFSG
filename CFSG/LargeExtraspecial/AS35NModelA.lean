module

public import CFSG.LargeExtraspecial.AS35KFixC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.Blueprint.Fischer (K)

namespace Setting

variable {H : Type} [Group H] [Finite H] (T : Setting H) {m : ℕ}

theorem QG_eq_map_Rbar (hm : 4 ≤ m) (hC : centralizer (T.zGen : Set H) = ⊥)
    (ψ : T.zGen ≃* PG m) {e : Fin m → K} (he0 : e ≠ 0) (he : herm frob e e = 0)
    (hez : tq e = ψ T.zL) :
    T.QG = ((AS35K.Rbar m e).comap ψ.toMonoidHom).map T.zGen.subtype ∧ T.width = m - 2 := by
  have := T.zGen_normal
  have hm3 : 3 ≤ m := by omega
  have hU := S14.unitaryAutFacts hm
  set R : Subgroup T.zGen := (AS35K.Rbar m e).comap ψ.toMonoidHom with hR
  set RH : Subgroup H := R.map T.zGen.subtype with hRH
  have hRcent : R ≤ centralizer {T.zL} := by
    intro y hy
    have h1 := mem_centralizer_singleton_iff.mp (AS35K.Rbar_le_centralizer he hy)
    rw [hez, MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul] at h1
    exact mem_centralizer_singleton_iff.mpr (ψ.injective h1)
  have hRnorm : ∀ c ∈ centralizer ({T.zL} : Set T.zGen), ∀ y ∈ R, c * y * c⁻¹ ∈ R := by
    intro c hc y hy
    have hc' : ψ c ∈ centralizer {tq e} := by
      rw [mem_centralizer_singleton_iff] at hc ⊢
      rw [hez, ← map_mul, ← map_mul, hc]
    have h1 := AS35K.conj_mem_Rbar hm3 he0 he hc' hy
    change ψ (c * y * c⁻¹) ∈ AS35K.Rbar m e
    rwa [map_mul, map_mul, map_inv]
  have hR2 : IsPGroup 2 R := (AS35K.isPGroup_Rbar hm3 he0 he).comap_of_injective
    ψ.toMonoidHom ψ.injective
  have hRO : R ≤ oTwoCent T.zL := le_oTwoCent hRcent hRnorm hR2
  have hRQ : RH ≤ T.QG := (map_mono hRO).trans T.map_oTwoCent_zL_le_QG
  have hzR : T.zL ∈ R := by
    change ψ T.zL ∈ AS35K.Rbar m e
    rw [← hez]
    exact AS35K.tq_mem_Rbar hm3 he0 he
  have hfixR : ∀ φ : MulAut T.zGen, (∀ y ∈ R, φ y = y) →
      (∀ x, φ x = x) ∨ ∀ x, φ x = T.zL * x * T.zL⁻¹ := by
    intro φ hφ
    refine AS35K.eq_or_eq_conj_of_transport ψ φ ?_
    rw [← hez]
    refine hU.2 e he0 he _ fun x hx => ?_
    have h1 : ψ.symm x ∈ R := by
      change ψ (ψ.symm x) ∈ AS35K.Rbar m e
      rwa [MulEquiv.apply_symm_apply]
    simp only [MulEquiv.trans_apply, hφ _ h1, MulEquiv.apply_symm_apply]
  have hCQ : ∀ c ∈ T.QG, (∀ y ∈ RH, c * y = y * c) → c = 1 ∨ c = T.z := by
    intro c hcQ hcR
    have hφ : ∀ y ∈ R, MulAut.conjNormal c y = y := by
      intro y hy
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, hcR y ⟨y, hy, rfl⟩, mul_inv_cancel_right]
    have hcent : ∀ a : H, (∀ l ∈ T.zGen, a * l * a⁻¹ = l) → a = 1 := by
      intro a ha
      have : a ∈ centralizer (T.zGen : Set H) := mem_centralizer_iff.mpr fun l hl => by
        calc l * a = a * l * a⁻¹ * a := by rw [ha l hl]
          _ = a * l := by group
      rwa [hC, mem_bot] at this
    rcases hfixR _ hφ with h | h
    · refine Or.inl (hcent c fun l hl => ?_)
      have := congrArg Subtype.val (h ⟨l, hl⟩)
      simpa only [MulAut.conjNormal_apply] using this
    · refine Or.inr ?_
      have h1 := hcent (T.z⁻¹ * c) fun l hl => by
        have h2 := congrArg Subtype.val (h ⟨l, hl⟩)
        simp only [MulAut.conjNormal_apply, coe_mul, coe_inv] at h2
        change c * l * c⁻¹ = T.z * l * T.z⁻¹ at h2
        calc T.z⁻¹ * c * l * (T.z⁻¹ * c)⁻¹ = T.z⁻¹ * (c * l * c⁻¹) * T.z := by group
          _ = l := by rw [h2]; group
      calc c = T.z * (T.z⁻¹ * c) := by group
        _ = T.z := by rw [h1, mul_one]
  set A : Subgroup T.Q := (RH.comap T.M.subtype).comap T.Q.subtype with hA
  have hcenA : center T.Q ≤ A := by
    intro q hq
    rcases T.mem_center_Q_iff.mp hq with rfl | rfl
    · exact one_mem _
    · exact ⟨T.zL, hzR, rfl⟩
  have hcard := Asc22.card_centralizer_mul_card T.extraspecial hcenA
  have hCA : Nat.card (centralizer (A : Set T.Q)) ≤ 2 := by
    have hsub : centralizer (A : Set T.Q) ≤ center T.Q := by
      intro q hq
      have hqQ : ((q : T.M) : H) ∈ T.QG := ⟨q, q.2, rfl⟩
      have h1 := hCQ _ hqQ fun y hy => by
        obtain ⟨y', hy'R, rfl⟩ := hy
        have hyQ := hRQ ⟨y', hy'R, rfl⟩
        obtain ⟨⟨y₁, hy₁⟩, hy₁Q, hy₁e⟩ := hyQ
        have hyA : (⟨⟨y₁, hy₁⟩, hy₁Q⟩ : T.Q) ∈ A := by
          change y₁ ∈ RH
          rw [show y₁ = (y' : H) from hy₁e]
          exact ⟨y', hy'R, rfl⟩
        have h2 := mem_centralizer_iff.mp hq _ hyA
        have h3 := congrArg (fun w : T.Q => ((w : T.M) : H)) h2
        simp only [coe_mul] at h3
        change ((q : T.M) : H) * (y' : H) = (y' : H) * ((q : T.M) : H)
        rw [show ((y' : T.zGen) : H) = y₁ from hy₁e.symm]
        exact h3.symm
      refine T.mem_center_Q_iff.mpr (h1.imp (fun h => ?_) fun h => ?_)
      · exact Subtype.ext (Subtype.ext h)
      · exact Subtype.ext (Subtype.ext h)
    have h1 := Subgroup.card_le_of_le hsub
    have h2 := T.extraspecial.2.2.2
    omega
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hAtop : A = ⊤ := by
    apply Subgroup.eq_top_of_le_card
    have : 0 < Nat.card (centralizer (A : Set T.Q)) := Nat.card_pos
    nlinarith
  have hQR : T.QG ≤ RH := by
    rintro _ ⟨q, hq, rfl⟩
    have h1 : (⟨q, hq⟩ : T.Q) ∈ A := hAtop ▸ mem_top _
    exact h1
  have hQeq : T.QG = RH := le_antisymm hQR hRQ
  have hcardR : Nat.card R = Nat.card (AS35K.Rbar m e) := by
    rw [← Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hR,
      Subgroup.map_comap_eq_self_of_surjective ψ.surjective]
  refine ⟨hQeq, T.width_eq ?_⟩
  rw [← T.card_QG_eq_card_Q, hQeq, hRH, Subgroup.card_map_of_injective T.zGen.subtype_injective,
    hcardR, AS35K.card_Rbar hm3 he0 he]

end Setting

end CFSG.LargeExtraspecial
