module

public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusSplit
public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusNPlus

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG

open scoped commutatorElement

@[expose] def NQ (Q : Type) [Group Q] (W : Type) [Group W] : Subgroup W :=
  sSup {N : Subgroup W | N.Normal ∧ IsCommProd Q N}

variable {W : Type} [Group W]

theorem NQ_map_aut (Q : Type) [Group Q] (φ : MulAut W) :
    (NQ Q W).map φ.toMonoidHom = NQ Q W :=
  sSup_map_equiv W (fun _ _ N => N.Normal ∧ IsCommProd Q N)
    (fun _ _ _ _ e _ hN => ⟨hN.1.map e.toMonoidHom e.surjective, hN.2.map e⟩) φ

theorem normal_of_map_conj (N : Subgroup W) (h : ∀ g : W, N.map (MulAut.conj g).toMonoidHom = N) :
    N.Normal := by
  refine ⟨fun x hx g => ?_⟩
  have : MulAut.conj g x ∈ N.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
  rw [h g] at this
  simpa using this

theorem map_conj_eq_of_normal (N : Subgroup W) [N.Normal] (g : W) :
    N.map (MulAut.conj g).toMonoidHom = N := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using (inferInstance : N.Normal).conj_mem y hy g
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by show g * (g⁻¹ * x * g) * g⁻¹ = x; group⟩
    simpa using (inferInstance : N.Normal).conj_mem x hx g⁻¹

theorem map_eq_of_map_le [Finite W] (H : Subgroup W) (α : MulAut W)
    (h : H.map α.toMonoidHom ≤ H) : H.map α.toMonoidHom = H :=
  Subgroup.eq_of_le_of_card_ge h (by rw [Subgroup.card_map_of_injective α.injective])

theorem exists_split_NQ [Finite W] {Q : Type} [Group Q] (hQ : GoodQ Q) (h3 : pCore 3 W = ⊥)
    (X : Subgroup W) [X.Normal] (𝒜 : Set (W ≃* W))
    (hX : ∀ φ ∈ 𝒜, X.map φ.toMonoidHom = X)
    (hcomm : ∀ φ ∈ 𝒜, ∀ n ∈ NQ Q W, n⁻¹ * φ n ∈ X) :
    ∃ N0 N1 : Subgroup W, N0.Normal ∧ N1.Normal ∧ NQ Q W = N0 ⊔ N1 ∧ IsCommProd Q N0 ∧
      IsCommProd Q N1 ∧ (∀ x ∈ N0, TwoElt x → x ∈ X) ∧ (∀ φ ∈ 𝒜, ∀ n ∈ N1, φ n = n) ∧
      ∀ ψ : W ≃* W, X.map ψ.toMonoidHom = X →
        N0.map ψ.toMonoidHom = N0 ∧ N1.map ψ.toMonoidHom = N1 := by
  obtain ⟨M, hMn, ⟨S, hS, hc, hsup⟩, hmax⟩ := exists_max_commProd hQ h3
  have hNQ : NQ Q W = M :=
    le_antisymm (sSup_le fun N hN => hmax N hN.1 hN.2) (le_sSup ⟨hMn, S, hS, hc, hsup⟩)
  have hinv : ∀ ψ : W ≃* W, (S.sup id).map ψ.toMonoidHom = S.sup id := by
    intro ψ
    rw [hsup, ← hNQ]
    exact NQ_map_aut Q ψ
  obtain ⟨N0, N1, hsupN, h0, h1, h2, h3', hψ⟩ := bcore_one hQ hS hc X 𝒜 (fun φ _ => hinv φ) hX
    (by
      intro φ hφ n hn
      rw [hsup] at hn
      exact hcomm φ hφ n (hNQ ▸ hn))
  have hψ' : ∀ ψ : W ≃* W, X.map ψ.toMonoidHom = X →
      N0.map ψ.toMonoidHom = N0 ∧ N1.map ψ.toMonoidHom = N1 := fun ψ hψX => hψ ψ (hinv ψ) hψX
  refine ⟨N0, N1, ?_, ?_, by rw [hNQ, ← hsup, hsupN], h0, h1, h2, h3', hψ'⟩
  · exact normal_of_map_conj N0 fun g => (hψ' (MulAut.conj g) (map_conj_eq_of_normal X g)).1
  · exact normal_of_map_conj N1 fun g => (hψ' (MulAut.conj g) (map_conj_eq_of_normal X g)).2

section Step

variable {Y : Type} [Group Y]

@[expose] noncomputable def quotAut (α : MulAut Y) : MulAut (Y ⧸ pPrimeCore 2 Y) :=
  QuotientGroup.congr (pPrimeCore 2 Y) (pPrimeCore 2 Y) α (pPrimeCore_map_iso 2 α)

theorem subgroupOf_pPrimeCore_le [Finite Y] (D : Subgroup Y) :
    (pPrimeCore 2 Y).subgroupOf D ≤ pPrimeCore 2 ↥D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E : Subgroup ↥D := (pPrimeCore 2 Y).subgroupOf D with hE
  have hEn : E.Normal := Subgroup.normal_subgroupOf
  have hEcop : Nat.Coprime 2 (Nat.card E) := by
    have hle : E.map D.subtype ≤ pPrimeCore 2 Y := by
      rintro _ ⟨d, hd, rfl⟩
      exact hd
    have hdvd : Nat.card E ∣ Nat.card (pPrimeCore 2 Y) := by
      have hcard : Nat.card (E.map D.subtype) = Nat.card E :=
        Subgroup.card_map_of_injective D.subtype_injective
      rw [← hcard]
      exact Subgroup.card_dvd_of_le hle
    exact Nat.Coprime.coprime_dvd_right hdvd pPrimeCore_coprime_card
  exact le_sSup ⟨hEn, hEcop⟩

theorem step_split [Finite Y] (XY M' : Subgroup Y) [XY.Normal] [M'.Normal] (hXM : XY ≤ M')
    (𝒢' 𝒢 : Set (MulAut Y)) (hsub : 𝒢 ⊆ 𝒢') (hX : ∀ α ∈ 𝒢', XY.map α.toMonoidHom = XY)
    (hcomm : ∀ α ∈ 𝒢, ∀ z ∈ NPlus Y, z⁻¹ * α z ∈ XY) :
    ∃ Z0 Z1 : Subgroup Y, NPlus Y = Z0 ⊔ Z1 ∧ Z0.Normal ∧ Z1.Normal ∧ pPrimeCore 2 Y ≤ Z1 ∧
      (∀ α ∈ 𝒢', Z1.map α.toMonoidHom = Z1) ∧ (∀ z ∈ Z0, TwoElt z → z ∈ M') ∧
      (∀ α ∈ 𝒢, ∀ z ∈ Z1, z⁻¹ * α z ∈ pPrimeCore 2 Y) ∧
      (∀ D : Subgroup Y, D ≤ Z1 → Z1 ≤ D ⊔ pPrimeCore 2 Y → NPlus ↥D = ⊤) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 Y with hO
  set π := QuotientGroup.mk' O with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hW3 : pCore 3 (Y ⧸ O) = ⊥ := pCore_three_eq_bot (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  set Xb : Subgroup (Y ⧸ O) := XY.map π with hXb
  have hXbn : Xb.Normal := Subgroup.Normal.map ‹XY.Normal› π hπs
  have hcompπ : ∀ α : MulAut Y, (quotAut α).toMonoidHom.comp π = π.comp α.toMonoidHom := by
    intro α
    ext y
    rfl
  have hXφ : ∀ α ∈ 𝒢', Xb.map (quotAut α).toMonoidHom = Xb := by
    intro α hα
    rw [hXb, Subgroup.map_map, hcompπ α, ← Subgroup.map_map, hX α hα]
  let 𝒜 : Set ((Y ⧸ O) ≃* (Y ⧸ O)) := {φ | ∃ α ∈ 𝒢, φ = quotAut α}
  have hX𝒜 : ∀ φ ∈ 𝒜, Xb.map φ.toMonoidHom = Xb := by
    rintro φ ⟨α, hα, rfl⟩
    exact hXφ α (hsub hα)
  have hcommW : ∀ φ ∈ 𝒜, ∀ n ∈ NOne (Y ⧸ O) ⊔ NTwo (Y ⧸ O), n⁻¹ * φ n ∈ Xb := by
    rintro φ ⟨α, hα, rfl⟩ n hn
    obtain ⟨y, rfl⟩ := hπs n
    have hy : y ∈ NPlus Y := hn
    refine ⟨y⁻¹ * α y, hcomm α hα y hy, ?_⟩
    show π (y⁻¹ * α y) = (π y)⁻¹ * quotAut α (π y)
    rw [map_mul, map_inv]
    rfl
  obtain ⟨A0, A1, hA0n, hA1n, hAsup, hA0c, hA1c, hA0X, hA1fix, hAinv⟩ :=
    exists_split_NQ goodQ_SL23 hW3 Xb 𝒜 hX𝒜
      (fun φ hφ n hn => hcommW φ hφ n (Subgroup.mem_sup_left hn))
  obtain ⟨C0, C1, hC0n, hC1n, hCsup, hC0c, hC1c, hC0X, hC1fix, hCinv⟩ :=
    exists_split_NQ goodQ_A4 hW3 Xb 𝒜 hX𝒜
      (fun φ hφ n hn => hcommW φ hφ n (Subgroup.mem_sup_right hn))
  have hN1 : NOne (Y ⧸ O) = A0 ⊔ A1 := hAsup
  have hN2 : NTwo (Y ⧸ O) = C0 ⊔ C1 := hCsup
  have hA0Nm := hA0n
  have hA1Nm := hA1n
  have hC0Nm := hC0n
  have hC1Nm := hC1n
  refine ⟨(A0 ⊔ C0).comap π, (A1 ⊔ C1).comap π, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : NPlus Y = (NOne (Y ⧸ O) ⊔ NTwo (Y ⧸ O)).comap π := rfl
    rw [h1, hN1, hN2, sup_sup_sup_comm]
    exact (Subgroup.comap_sup_eq (f := π) _ _ hπs).symm
  · exact Subgroup.Normal.comap (Subgroup.sup_normal _ _) π
  · exact Subgroup.Normal.comap (Subgroup.sup_normal _ _) π
  · intro o ho
    have : π o = 1 := (QuotientGroup.eq_one_iff _).mpr ho
    show π o ∈ A1 ⊔ C1
    rw [this]
    exact one_mem _
  · intro α hα
    apply map_eq_of_map_le
    rintro _ ⟨y, hy, rfl⟩
    have h1 := (hAinv (quotAut α) (hXφ α hα)).2
    have h2 := (hCinv (quotAut α) (hXφ α hα)).2
    have hy' : π y ∈ A1 ⊔ C1 := hy
    show π (α y) ∈ A1 ⊔ C1
    have : π (α y) = quotAut α (π y) := rfl
    rw [this]
    have hmem : quotAut α (π y) ∈ (A1 ⊔ C1).map (quotAut α).toMonoidHom := ⟨π y, hy', rfl⟩
    rwa [Subgroup.map_sup, h1, h2] at hmem
  · intro z hz h2z
    have hπz : π z ∈ A0 ⊔ C0 := hz
    have h2π : TwoElt (π z) := h2z.map π
    have hmem := twoElt_mem_sup_of_normalizes (Subgroup.le_normalizer_of_normal)
      (Subgroup.le_normalizer_of_normal) hπz h2π
    have hle : oTwoPrimeOf A0 ⊔ oTwoPrimeOf C0 ≤ Xb :=
      sup_le (oTwoPrimeOf_le_iff.mpr hA0X) (oTwoPrimeOf_le_iff.mpr hC0X)
    obtain ⟨x, hx, hxz⟩ := hle hmem
    have hxO : x⁻¹ * z ∈ O := (QuotientGroup.eq (s := O)).mp hxz
    have hzsup : z ∈ O ⊔ XY := by
      rw [sup_comm]
      have := Subgroup.mul_mem_sup hx hxO
      rwa [show x * (x⁻¹ * z) = z by group] at this
    exact twoElt_mem_sup_odd (D := XY) (O := O) (M := M') Subgroup.le_normalizer_of_normal hOodd
      (fun d hd _ => hXM hd) hzsup h2z
  · intro α hα z hz
    have hfix : (A1 ⊔ C1) ≤ MonoidHom.eqLocus (quotAut α).toMonoidHom (MonoidHom.id (Y ⧸ O)) :=
      sup_le (fun n hn => hA1fix _ ⟨α, hα, rfl⟩ n hn) (fun n hn => hC1fix _ ⟨α, hα, rfl⟩ n hn)
    have hz' : π z ∈ A1 ⊔ C1 := hz
    have := hfix hz'
    have hq : (quotAut α) (π z) = π z := this
    have : π (z⁻¹ * α z) = 1 := by
      have e : π (z⁻¹ * α z) = (π z)⁻¹ * quotAut α (π z) := by
        rw [map_mul, map_inv]
        rfl
      rw [e, hq, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp this
  · intro D hDZ hZD
    set N1 : Subgroup (Y ⧸ O) := A1 ⊔ C1 with hN1def
    have hN1n : N1.Normal := Subgroup.sup_normal _ _
    let ρ : ↥D →* ↥N1 := (π.comp D.subtype).codRestrict N1 (fun d => hDZ d.2)
    have hρs : Function.Surjective ρ := by
      rintro ⟨n, hn⟩
      obtain ⟨y, rfl⟩ := hπs n
      have hyZ : y ∈ (A1 ⊔ C1).comap π := hn
      have hyDO : y ∈ O ⊔ D := by
        rw [sup_comm]
        exact hZD hyZ
      obtain ⟨o, ho, d, hd, rfl⟩ :=
        (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing O D
          Subgroup.le_normalizer_of_normal _).mp hyDO
      refine ⟨⟨d, hd⟩, Subtype.ext ?_⟩
      have hπo : π o = 1 := (QuotientGroup.eq_one_iff _).mpr ho
      show π d = π (o * d)
      rw [map_mul, hπo, one_mul]
    have hρker : ρ.ker ≤ pPrimeCore 2 ↥D := by
      intro d hd
      rw [MonoidHom.mem_ker] at hd
      have hdπ : π (d : Y) = 1 := congrArg Subtype.val hd
      have hdO : (d : Y) ∈ O := (QuotientGroup.eq_one_iff _).mp hdπ
      exact subgroupOf_pPrimeCore_le D hdO
    have hN1O : pPrimeCore 2 ↥N1 = ⊥ :=
      pPrimeCore_eq_bot_of_normal (pPrimeCore_quotient_pPrimeCore_eq_bot 2) N1
    have hN1top : NPlus ↥N1 = ⊤ := by
      rw [NPlus_eq_of_pPrimeCore_eq_bot hN1O]
      have hA : A1.subgroupOf N1 ≤ NOne ↥N1 :=
        le_NOne (Subgroup.Normal.subgroupOf hA1n N1) (hA1c.subgroupOf N1 le_sup_left)
      have hC : C1.subgroupOf N1 ≤ NTwo ↥N1 :=
        le_NTwo (Subgroup.Normal.subgroupOf hC1n N1) (hC1c.subgroupOf N1 le_sup_right)
      have : (A1 ⊔ C1).subgroupOf N1 = ⊤ := Subgroup.subgroupOf_self N1
      rw [Subgroup.subgroupOf_sup le_sup_left le_sup_right] at this
      exact top_le_iff.mp (this ▸ sup_le_sup hA hC)
    rw [← NPlus_comap ρ hρs hρker, hN1top, Subgroup.comap_top]

end Step

end CFSG.OddStandard.Solomon75
