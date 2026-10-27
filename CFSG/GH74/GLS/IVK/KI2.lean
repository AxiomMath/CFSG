module

public import CFSG.GH74.GLS.IVK.L2.KI2Aux
public import CFSG.GH74.Uniqueness.SU.KInputs
public import CFSG.GH74.GLS.IVK.L2.ExistNotation

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter CFSG.ABGDGroups CFSG.ABGLocalTools

section KI2Main

theorem ki2_of_psl2_pgl2
    {H : Type} [Group H] [Finite H]
    (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hLie : CFSG.Blueprint.LieModel ↥(generalizedFitting H) .PSL 2 p f)
    (x : H) (hx2 : orderOf x = 2)
    (hPGL : CFSG.GH74.Uniqueness.SU.K.IsPGL2 ↥(generalizedFitting H ⊔ zpowers x) p f) :
    Open.pRank 2 (generalizedFitting H ⊔ zpowers x) = 2 ∧
      (∃ _ : (generalizedFitting H ⊔ zpowers x).Normal,
        IsCyclic (H ⧸ (generalizedFitting H ⊔ zpowers x))) ∧
      ∀ E₁ E₂ : Subgroup H, Open.IsElemAbelian 2 E₁ → Nat.card E₁ = 8 →
        Open.IsElemAbelian 2 E₂ → Nat.card E₂ = 8 →
          ∃ h : H, E₂ = E₁.map (MulAut.conj h).toMonoidHom := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLN : (generalizedFitting H).Normal := (CFSG.LocalCores.generalized_fitting_characteristic).2
  obtain ⟨F, hFfield, hFfin, hFcard, hne3, ⟨e⟩⟩ : ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = p ^ f ∧ p ^ f ≠ 3 ∧ Nonempty (↥(generalizedFitting H) ≃* L2 F) := by
    rcases hLie with ⟨_, hmod⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · obtain ⟨hadm, F, hf, hfin, hc, he⟩ := hmod
      refine ⟨F, hf, hfin, hc, ?_, he⟩
      intro h3
      exact hadm.2.2.2.2 (by rw [h3])
    · exact absurd h0 (by norm_num)
    · exact absurd h0 (by norm_num)
    · exact absurd h0 (by norm_num)
  have hf1 : 1 ≤ f := by
    rcases hLie with ⟨_, hmod⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact hmod.1.2.1
    · exact absurd h0 (by norm_num)
    · exact absurd h0 (by norm_num)
    · exact absurd h0 (by norm_num)
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hodd : Odd (Nat.card F) := by rw [hFcard]; exact hpodd.pow
  have h3 : 3 < Nat.card F := by
    rw [hFcard]
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    omega
  have hF : L2Field F := ⟨hodd, h3⟩
  obtain ⟨N⟩ := exists_notation hF e
  obtain ⟨U, hUP, hU4, hUC, -⟩ := ivk_1_3f_b F hF _ e N
  have hUinn : U ≤ innAut ↥(generalizedFitting H) := hUP.trans inf_le_right
  obtain ⟨F', hF'f, hF'fin, hF'card, ⟨eM⟩⟩ := hPGL
  have hF'pp : IsOddPrimePower (Nat.card F') := ⟨p, f, hp, hpodd, hf1, hF'card⟩
  let ρ : H →* MulAut ↥(generalizedFitting H) := MulAut.conjNormal
  have hρL : ∀ k : ↥(generalizedFitting H), ρ (k : H) = MulAut.conj k := fun k => MulAut.conjNormal_val
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro h hh
    rw [MonoidHom.mem_ker] at hh
    have hcent : h ∈ centralizer ((generalizedFitting H : Subgroup H) : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 : h * l * h⁻¹ = l := by
        have := congrArg (fun a : MulAut ↥(generalizedFitting H) =>
          ((a ⟨l, hl⟩ : ↥(generalizedFitting H)) : H)) hh
        simpa [ρ, MulAut.conjNormal_apply] using this
      calc l * h = (h * l * h⁻¹) * h := by rw [h1]
        _ = h * l := by group
    have hmem : h ∈ generalizedFitting H := CFSG.centralizer_generalizedFitting_le H hcent
    rw [Subgroup.mem_bot]
    have h1 : MulAut.conj (⟨h, hmem⟩ : ↥(generalizedFitting H)) = 1 := by
      have := hρL ⟨h, hmem⟩
      rw [← this]; exact hh
    have h2 := conj_injective_of_L2 e (h1.trans (map_one _).symm)
    exact congrArg Subtype.val h2
  have hρLmap : (generalizedFitting H).map ρ = innAut ↥(generalizedFitting H) := by
    ext y
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨l, hl⟩, (hρL ⟨l, hl⟩).symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨(k : H), k.2, hρL k⟩
  have hx_notin : x ∉ generalizedFitting H := by
    intro hxL
    have hsup : generalizedFitting H ⊔ zpowers x = generalizedFitting H :=
      sup_eq_left.2 ((Subgroup.zpowers_le).2 hxL)
    have hcardM : Nat.card ↥(generalizedFitting H ⊔ zpowers x) =
        Nat.card F' * (Nat.card F' ^ 2 - 1) := by
      rw [Nat.card_congr eM.toEquiv, pgl2_card_formula]
    rw [hsup] at hcardM
    have hcardL : Nat.card ↥(generalizedFitting H) = Nat.card F * (Nat.card F ^ 2 - 1) / 2 :=
      card_eq_of_L2Field e hF
    rw [hcardL, hF'card, hFcard] at hcardM
    have hq3 : 3 < p ^ f := by rw [← hFcard]; exact h3
    have hpos : 0 < p ^ f * ((p ^ f) ^ 2 - 1) := by
      apply Nat.mul_pos (by omega)
      have : 9 ≤ (p ^ f) ^ 2 := by nlinarith
      omega
    generalize p ^ f * ((p ^ f) ^ 2 - 1) = m at hcardM hpos
    omega
  have hu2 : orderOf (ρ x) = 2 := (orderOf_injective ρ hρinj x).trans hx2
  have hu_notinn : ρ x ∉ innAut ↥(generalizedFitting H) := by
    rintro ⟨k, hk⟩
    apply hx_notin
    have h1 : ρ x = ρ (k : H) := by rw [hρL]; exact hk.symm
    have h2 := hρinj h1
    rw [h2]; exact k.2
  have huD : ρ x ∈ innDiagSub e := by
    by_contra hnD
    obtain ⟨E, hEle, hEea, hE8⟩ := exists_E8_of_involution_outside e hF (ρ x) hu2 hnD
    have hMρ : (generalizedFitting H ⊔ zpowers x).map ρ =
        innAut ↥(generalizedFitting H) ⊔ zpowers (ρ x) := by
      rw [Subgroup.map_sup, hρLmap, MonoidHom.map_zpowers]
    have hEM : E ≤ (generalizedFitting H ⊔ zpowers x).map ρ := hMρ ▸ hEle
    obtain ⟨hcomm, hsq⟩ := isElementaryAbelian_two_data E hEea
    have hEρ : E ≤ ρ.range := hEM.trans (Subgroup.map_le_range _ _)
    set EH : Subgroup H := E.comap ρ with hEH
    have hEHmap : EH.map ρ = E := by
      rw [hEH, Subgroup.map_comap_eq, inf_eq_right.2 hEρ]
    have hEHle : EH ≤ generalizedFitting H ⊔ zpowers x := by
      intro y hy
      have h1 : ρ y ∈ (generalizedFitting H ⊔ zpowers x).map ρ := hEM hy
      exact (Subgroup.mem_map_iff_mem hρinj).1 h1
    have hEHcard : Nat.card ↥EH = 8 := by
      rw [← hE8, ← hEHmap, Subgroup.card_map_of_injective hρinj]
    have h4 := card_le_four_of_le_pgl2 hF'pp (generalizedFitting H ⊔ zpowers x) eM EH hEHle
      (fun a ha b hb => hρinj (by
        rw [map_mul, map_mul]
        exact hcomm _ ha _ hb))
      (fun a ha => hρinj (by
        rw [map_mul, map_one]
        exact hsq _ ha))
    omega
  have hMD : (generalizedFitting H ⊔ zpowers x).map ρ = innDiagSub e := by
    rw [Subgroup.map_sup, hρLmap, MonoidHom.map_zpowers]
    exact innAut_sup_zpowers_eq e hF huD hu_notinn
  have hMcomap : generalizedFitting H ⊔ zpowers x = (innDiagSub e).comap ρ := by
    rw [← hMD]
    exact (Subgroup.comap_map_eq_self_of_injective hρinj _).symm
  have hMN : (generalizedFitting H ⊔ zpowers x).Normal := by
    rw [hMcomap]
    have := innDiagSub_normal e
    exact Subgroup.normal_comap ρ
  have hker : generalizedFitting H ⊔ zpowers x = ((fieldProj e).comp ρ).ker := by
    rw [hMcomap]
    ext y
    rw [Subgroup.mem_comap, MonoidHom.mem_ker, MonoidHom.comp_apply, mem_innDiagSub_iff]
  have hrank : CFSG.Open.pRank 2 (generalizedFitting H ⊔ zpowers x) = 2 := by
    unfold CFSG.Open.pRank
    have hbound : ∀ k ∈ {k | ∃ E : Subgroup H, E ≤ generalizedFitting H ⊔ zpowers x ∧
        CFSG.Open.IsElemAbelian 2 E ∧ Nat.card ↥E = 2 ^ k}, k ≤ 2 := by
      rintro k ⟨E, hEM, ⟨hEc, hEs⟩, hEk⟩
      have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
        congrArg Subtype.val (hEc.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
      have hsq : ∀ a ∈ E, a * a = 1 := fun a ha => by
        have := hEs a ha
        rwa [pow_two] at this
      have h4 := card_le_four_of_le_pgl2 hF'pp (generalizedFitting H ⊔ zpowers x) eM E hEM hcomm hsq
      rw [hEk] at h4
      by_contra hlt
      push Not at hlt
      have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hlt
      omega
    have hmem2 : 2 ∈ {k | ∃ E : Subgroup H, E ≤ generalizedFitting H ⊔ zpowers x ∧
        CFSG.Open.IsElemAbelian 2 E ∧ Nat.card ↥E = 2 ^ k} := by
      obtain ⟨hUc, hUs⟩ := isElementaryAbelian_two_data U hU4.1
      have hUρ : U ≤ ρ.range := hUinn.trans (by rw [← hρLmap]; exact Subgroup.map_le_range _ _)
      refine ⟨U.comap ρ, ?_, ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩, ?_⟩
      · intro y hy
        have h1 : ρ y ∈ U := hy
        have h2 : ρ y ∈ innDiagSub e := innAut_le_innDiagSub e (hUinn h1)
        rw [hMcomap]
        exact h2
      · apply Subtype.ext
        apply hρinj
        have := hUc (ρ a) a.2 (ρ b) b.2
        simpa using this
      · have := hUs (ρ a) ha
        have h2 : ρ (a ^ 2) = 1 := by rw [pow_two, map_mul]; exact this
        exact hρinj (by rw [h2, map_one])
      · have : (U.comap ρ).map ρ = U := by rw [Subgroup.map_comap_eq, inf_eq_right.2 hUρ]
        rw [← Subgroup.card_map_of_injective hρinj, this]
        simpa using hU4.2
    apply le_antisymm
    · exact csSup_le ⟨2, hmem2⟩ hbound
    · exact le_csSup ⟨2, hbound⟩ hmem2
  have hcyc : IsCyclic (H ⧸ (generalizedFitting H ⊔ zpowers x)) := by
    have := ringAut_isCyclic F
    have e1 := QuotientGroup.quotientMulEquivOfEq hker
    exact (e1.trans (QuotientGroup.quotientKerEquivRange _)).isCyclic.mpr (Subgroup.isCyclic _)
  refine ⟨hrank, ⟨hMN, hcyc⟩, ?_⟩
  intro E₁ E₂ h₁ c₁ h₂ c₂
  have hnorm : ∀ (E : Subgroup H), CFSG.Open.IsElemAbelian 2 E → Nat.card ↥E = 8 →
      IsElementaryAbelian 2 ↥(E.map ρ) ∧ Nat.card ↥(E.map ρ) = 8 := by
    rintro E ⟨hEc, hEs⟩ hE8
    refine ⟨isElementaryAbelian_two _ ?_ ?_, by rw [Subgroup.card_map_of_injective hρinj]; exact hE8⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hEc.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul]
      have := hEs a ha
      rw [pow_two] at this
      rw [this, map_one]
  obtain ⟨hA₁, hA₁c⟩ := hnorm E₁ h₁ c₁
  obtain ⟨hA₂, hA₂c⟩ := hnorm E₂ h₂ c₂
  obtain ⟨σ₁, hσ₁1, hσ₁2, d₁, hd₁, hdE₁⟩ := E8_conj_to_E0 e hF N hUinn hU4 hUC _ hA₁ hA₁c
  obtain ⟨σ₂, hσ₂1, hσ₂2, d₂, hd₂, hdE₂⟩ := E8_conj_to_E0 e hF N hUinn hU4 hUC _ hA₂ hA₂c
  have hσ : σ₁ = σ₂ := ringEquiv_eq_of_sq_eq_one hσ₁2 hσ₂2 hσ₁1 hσ₂1
  subst hσ
  have hd : d₂⁻¹ * d₁ ∈ innDiagSub e := (innDiagSub e).mul_mem ((innDiagSub e).inv_mem hd₂) hd₁
  rw [← hMD] at hd
  obtain ⟨h, -, hh⟩ := hd
  refine ⟨h, ?_⟩
  ext y
  have key : ∀ z : MulAut ↥(generalizedFitting H), z ∈ (E₂.map ρ) ↔ (d₂⁻¹ * d₁)⁻¹ * z * (d₂⁻¹ * d₁) ∈ E₁.map ρ := by
    intro z
    have h1 : ∀ w, w ∈ U ⊔ Subgroup.zpowers (fieldAutHom e σ₁) ↔ d₁⁻¹ * w * d₁ ∈ E₁.map ρ := by
      intro w; rw [← hdE₁, mem_map_conj]
    have h2 : ∀ w, w ∈ U ⊔ Subgroup.zpowers (fieldAutHom e σ₁) ↔ d₂⁻¹ * w * d₂ ∈ E₂.map ρ := by
      intro w; rw [← hdE₂, mem_map_conj]
    have h3 := h2 (d₂ * z * d₂⁻¹)
    have h4 := h1 (d₂ * z * d₂⁻¹)
    have e1 : d₂⁻¹ * (d₂ * z * d₂⁻¹) * d₂ = z := by group
    have e2 : d₁⁻¹ * (d₂ * z * d₂⁻¹) * d₁ = (d₂⁻¹ * d₁)⁻¹ * z * (d₂⁻¹ * d₁) := by group
    rw [e1] at h3
    rw [e2] at h4
    exact h3.symm.trans h4
  have hy1 : y ∈ E₂ ↔ ρ y ∈ E₂.map ρ := (Subgroup.mem_map_iff_mem hρinj).symm
  rw [hy1, key, ← hh, mem_map_conj]
  have e3 : (ρ h)⁻¹ * ρ y * ρ h = ρ (h⁻¹ * y * h) := by simp [map_mul, map_inv]
  rw [e3, Subgroup.mem_map_iff_mem hρinj]

theorem ki2 :
    CFSG.GH74.Uniqueness.SU.K.KI2 := by
  intro H _ _ _hGH _hO p f hp hp2 hLie x hx2 hPGL
  exact ki2_of_psl2_pgl2 p f hp hp2 hLie x hx2 hPGL

end KI2Main

end CFSG.GH74.GLS.IVK
