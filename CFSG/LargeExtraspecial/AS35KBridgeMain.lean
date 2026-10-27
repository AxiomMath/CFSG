module

public import CFSG.LargeExtraspecial.AS35KBridge
public import CFSG.LargeExtraspecial.AS35HSixEightB
public import CFSG.LargeExtraspecial.AS35IExtra
public import CFSG.LargeExtraspecial.AS35KCo2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.Blueprint.Fischer (K)

namespace Setting

variable {H : Type} [Group H] [Finite H] (T : Setting H)

omit [Finite H] in
@[expose] def zL : T.zGen := ⟨T.z, T.z_mem_zGen⟩

omit [Finite H] in
@[simp] theorem coe_zL : ((T.zL : T.zGen) : H) = T.z := rfl

omit [Finite H] in
theorem map_oTwoCent_zL_le_QG : (oTwoCent T.zL).map T.zGen.subtype ≤ T.QG := by
  have := T.zGen_normal
  refine T.le_QG_of_normalizes ?_ ?_ ((isPGroup_oTwoCent _).map _)
  · rintro _ ⟨y, hy, rfl⟩
    have h1 := mem_centralizer_singleton_iff.mp (oTwoCent_le_centralizer _ hy)
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val h1
  · rintro c hc _ ⟨y, hy, rfl⟩
    have hfix : MulAut.conjNormal c T.zL = T.zL := Subtype.ext (by
      rw [MulAut.conjNormal_apply]
      change c * T.z * c⁻¹ = T.z
      rw [T.mem_M_iff.mp hc, mul_inv_cancel_right])
    exact ⟨_, AS35K.mulAut_mem_oTwoCent _ hfix hy, by
      rw [Subgroup.coe_subtype, MulAut.conjNormal_apply]⟩

end Setting

namespace S14

variable {H : Type} [Group H] [Finite H] (T : Setting H) {m : ℕ}

theorem aschTwoAut_of_unitaryModel (hm : 4 ≤ m) (hU : UnitaryAutFacts m)
    (hC : centralizer (T.zGen : Set H) = ⊥) (ψ : T.zGen ≃* PG m)
    (hψ : ∀ l : T.zGen, IsConj T.zL l ↔ ψ l ∈ DG m) :
    (∀ α : H ≃* H, (∀ q ∈ T.QG, α q = q) →
      (∀ g : H, α (g * T.z * g⁻¹) = g * T.z * g⁻¹) ∨
        ∀ g : H, α (g * T.z * g⁻¹) = T.z * (g * T.z * g⁻¹) * T.z⁻¹) ∧
    (∀ g : H, ∃ l ∈ T.zGen, g * T.z * g⁻¹ = l * T.z * l⁻¹) ∧
    Nat.card (CFSG.Open.timmesfeldPSU (T.width + 2)) ≤ Nat.card T.zGen := by
  have := T.zGen_normal
  have hm3 : 3 ≤ m := by omega
  obtain ⟨e, he0, he, hez⟩ := (hψ T.zL).mp (IsConj.refl _)
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
  have hwidth : T.width = m - 2 := by
    refine T.width_eq ?_
    rw [← T.card_QG_eq_card_Q, hQeq, hRH, Subgroup.card_map_of_injective T.zGen.subtype_injective,
      hcardR, AS35K.card_Rbar hm3 he0 he]
  refine ⟨fun α hα => ?_, fun g => ?_, ?_⟩
  ·
    have hαz : α T.z = T.z := hα _ T.z_mem_QG
    refine T.conj_z_cases_of_zGen ?_
    rcases hfixR (T.zGenAut α hαz) (fun y hy => Subtype.ext (by
        rw [Setting.coe_zGenAut]
        exact hα _ (hRQ ⟨y, hy, rfl⟩))) with h | h
    · exact Or.inl fun l hl => by
        have h1 := congrArg Subtype.val (h ⟨l, hl⟩)
        simpa only [Setting.coe_zGenAut] using h1
    · exact Or.inr fun l hl => by
        have h1 := congrArg Subtype.val (h ⟨l, hl⟩)
        simpa only [Setting.coe_zGenAut, coe_mul, coe_inv, Setting.coe_zL] using h1
  ·
    have hd : ψ (MulAut.conjNormal g T.zL) ∈ DG m := by
      have h1 := hU.1 (ψ.symm.trans ((MulAut.conjNormal g).trans ψ)) (ψ T.zL)
        ((hψ _).mp (IsConj.refl _))
      simpa only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using h1
    obtain ⟨c, hc⟩ := isConj_iff.mp ((hψ _).mpr hd)
    refine ⟨c, c.2, ?_⟩
    have h1 := congrArg Subtype.val hc
    simp only [coe_mul, coe_inv, MulAut.conjNormal_apply, Setting.coe_zL] at h1
    exact h1.symm
  ·
    have hm' : T.width + 2 = m := by omega
    rw [hm']
    exact ((Nat.card_congr (AS35U.pgEquiv hm3).toEquiv).symm.trans
      (Nat.card_congr ψ.toEquiv).symm).le

theorem aschTwoAutStmt_of_model
    (hU : ∀ m, 4 ≤ m → UnitaryAutFacts m) (hId : AschTwoUnitaryModelStmt) :
    AschTwoAutStmt := by
  intro H _ _ T hw hA2
  obtain ⟨hs, hC, halt⟩ := hA2
  rcases halt with h3 | ⟨hw4, ⟨e⟩⟩
  · obtain ⟨m, hm, ψ, hψ⟩ := hId H T hw hs hC h3
    exact aschTwoAut_of_unitaryModel T hm (hU m hm) hC ψ hψ
  · exact aschTwoAut_of_co2 T hC hw4 e

end S14

end CFSG.LargeExtraspecial
