module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigPiA

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Inner

variable {G : Type} [Group G]

@[expose] noncomputable def innerPart (Λ H : Subgroup G) :
    Subgroup (↥Λ ⧸ classicalInvolutionOddCore ↥Λ) :=
  ((H.subgroupOf (Subgroup.normalizer (Λ : Set G))).map (actAut Λ)).comap MulAut.conj

theorem mem_innerPart {Λ H : Subgroup G} {x : ↥Λ ⧸ classicalInvolutionOddCore ↥Λ} :
    x ∈ innerPart Λ H ↔ ∃ c : ↥(Subgroup.normalizer (Λ : Set G)), (c : G) ∈ H ∧
      actAut Λ c = MulAut.conj x := by
  simp only [innerPart, Subgroup.mem_comap, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem innerPart_mono {Λ H H' : Subgroup G} (h : H ≤ H') : innerPart Λ H ≤ innerPart Λ H' := by
  intro x hx
  rw [mem_innerPart] at hx ⊢
  obtain ⟨c, hc, hcx⟩ := hx
  exact ⟨c, h hc, hcx⟩

theorem isPGroup_innerPart {Λ H : Subgroup G}
    (hinj : Function.Injective (MulAut.conj : (↥Λ ⧸ classicalInvolutionOddCore ↥Λ) →*
      MulAut (↥Λ ⧸ classicalInvolutionOddCore ↥Λ)))
    (hH : IsPGroup 2 ↥H) : IsPGroup 2 ↥(innerPart Λ H) := by
  have h1 : IsPGroup 2 ↥(((H.subgroupOf (Subgroup.normalizer (Λ : Set G))).map
      (actAut Λ)).comap MulAut.conj) :=
    ((hH.comap_of_injective (Subgroup.normalizer (Λ : Set G)).subtype
      Subtype.val_injective).map (actAut Λ)).comap_of_injective _ hinj
  exact h1

theorem innerPart_conj_le {Λ H : Subgroup G} {k : G} (hk : k ∈ Subgroup.normalizer (Λ : Set G)) :
    (innerPart Λ H).map (actAut Λ ⟨k, hk⟩).toMonoidHom ≤ innerPart Λ (conjSub k H) := by
  intro x hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [mem_innerPart] at hy ⊢
  obtain ⟨c, hc, hcy⟩ := hy
  refine ⟨⟨k, hk⟩ * c * ⟨k, hk⟩⁻¹, ?_, ?_⟩
  · rw [show (((⟨k, hk⟩ * c * ⟨k, hk⟩⁻¹ : ↥(Subgroup.normalizer (Λ : Set G)))) : G) =
        k * (c : G) * k⁻¹ from rfl, mem_conjSub_iff]
    convert hc using 1
    group
  · rw [map_mul, map_mul, map_inv, hcy]
    ext z
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulEquiv.coe_toMonoidHom, map_mul, map_inv,
      MulAut.inv_apply, MulEquiv.apply_symm_apply]

theorem mem_innerPart_of_actsLike [Finite G] {Λ H : Subgroup G} {c w : G} (hc : c ∈ H)
    (hcN : c ∈ Subgroup.normalizer (Λ : Set G)) (hw : w ∈ Λ) (h : ActsLike Λ c w) :
    (QuotientGroup.mk (⟨w, hw⟩ : ↥Λ) : ↥Λ ⧸ classicalInvolutionOddCore ↥Λ) ∈ innerPart Λ H := by
  rw [mem_innerPart]
  exact ⟨⟨c, hcN⟩, hc, (actAut_eq_conj_iff hcN hw).mpr h⟩

theorem exists_actsLike_of_mem_innerPart [Finite G] {Λ H : Subgroup G} {w : G} (hw : w ∈ Λ)
    (h : (QuotientGroup.mk (⟨w, hw⟩ : ↥Λ) : ↥Λ ⧸ classicalInvolutionOddCore ↥Λ) ∈
      innerPart Λ H) :
    ∃ c ∈ H, c ∈ Subgroup.normalizer (Λ : Set G) ∧ ActsLike Λ c w := by
  rw [mem_innerPart] at h
  obtain ⟨c, hc, hcx⟩ := h
  exact ⟨(c : G), hc, c.2, (actAut_eq_conj_iff c.2 hw).mp hcx⟩

theorem innerPart_eq_and_isSylow [Finite G] {Λ A B H₀ : Subgroup G}
    (hinj : Function.Injective (MulAut.conj : (↥Λ ⧸ classicalInvolutionOddCore ↥Λ) →*
      MulAut (↥Λ ⧸ classicalInvolutionOddCore ↥Λ)))
    (hA : IsPGroup 2 ↥A) (hBA : B ≤ A) {k : G} (hk : k ∈ Subgroup.normalizer (Λ : Set G))
    (hH₀ : conjSub k H₀ ≤ B) {S : Subgroup (↥Λ ⧸ classicalInvolutionOddCore ↥Λ)}
    (hS : IsSylow2In S ⊤) (hSH₀ : S ≤ innerPart Λ H₀) :
    innerPart Λ B = innerPart Λ A ∧ IsSylow2In (innerPart Λ A) ⊤ := by
  have hA2 : IsPGroup 2 ↥(innerPart Λ A) := isPGroup_innerPart hinj hA
  have h1 : Nat.card ↥S ≤ Nat.card ↥(innerPart Λ H₀) := Subgroup.card_le_of_le hSH₀
  have h2 : Nat.card ↥(innerPart Λ H₀) =
      Nat.card ↥((innerPart Λ H₀).map (actAut Λ ⟨k, hk⟩).toMonoidHom) :=
    (Subgroup.card_map_of_injective (actAut Λ ⟨k, hk⟩).injective).symm
  have h3 : Nat.card ↥((innerPart Λ H₀).map (actAut Λ ⟨k, hk⟩).toMonoidHom) ≤
      Nat.card ↥(innerPart Λ (conjSub k H₀)) := Subgroup.card_le_of_le (innerPart_conj_le hk)
  have h4 : Nat.card ↥(innerPart Λ (conjSub k H₀)) ≤ Nat.card ↥(innerPart Λ B) :=
    Subgroup.card_le_of_le (innerPart_mono hH₀)
  have h5 : Nat.card ↥(innerPart Λ B) ≤ Nat.card ↥(innerPart Λ A) :=
    Subgroup.card_le_of_le (innerPart_mono hBA)
  have hSA : Nat.card ↥S ≤ Nat.card ↥(innerPart Λ A) := by
    calc Nat.card ↥S ≤ Nat.card ↥(innerPart Λ H₀) := h1
      _ = Nat.card ↥((innerPart Λ H₀).map (actAut Λ ⟨k, hk⟩).toMonoidHom) := h2
      _ ≤ Nat.card ↥(innerPart Λ (conjSub k H₀)) := h3
      _ ≤ Nat.card ↥(innerPart Λ B) := h4
      _ ≤ Nat.card ↥(innerPart Λ A) := h5
  have hSB : Nat.card ↥S ≤ Nat.card ↥(innerPart Λ B) := by
    calc Nat.card ↥S ≤ Nat.card ↥(innerPart Λ H₀) := h1
      _ = Nat.card ↥((innerPart Λ H₀).map (actAut Λ ⟨k, hk⟩).toMonoidHom) := h2
      _ ≤ Nat.card ↥(innerPart Λ (conjSub k H₀)) := h3
      _ ≤ Nat.card ↥(innerPart Λ B) := h4
  have hAS : Nat.card ↥(innerPart Λ A) ≤ Nat.card ↥S := hS.natCard_le hA2 le_top
  refine ⟨Subgroup.eq_of_le_of_card_ge (innerPart_mono hBA) (hAS.trans hSB), ?_⟩
  exact hS.of_natCard_le hA2 le_top hSA

@[expose] noncomputable def actTrivSubgroup (Λ : Subgroup G) : Subgroup G :=
  (actAut Λ).ker.map (Subgroup.normalizer (Λ : Set G)).subtype

theorem mem_actTrivSubgroup [Finite G] {Λ : Subgroup G} {c : G} :
    c ∈ actTrivSubgroup Λ ↔ ∃ _ : c ∈ Subgroup.normalizer (Λ : Set G), ActsTriv Λ c := by
  rw [actTrivSubgroup, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, (actAut_eq_one_iff x.2).mp hx⟩
  · rintro ⟨hcN, hc⟩
    exact ⟨⟨c, hcN⟩, (actAut_eq_one_iff hcN).mpr hc, rfl⟩

theorem le_normalizer_inf_actTrivSubgroup [Finite G] {Λ E : Subgroup G}
    (hE : E ≤ Subgroup.normalizer (Λ : Set G)) :
    E ≤ Subgroup.normalizer ((E ⊓ actTrivSubgroup Λ : Subgroup G) : Set G) := by
  have hconj : ∀ g ∈ E, g ∈ Subgroup.normalizer (Λ : Set G) →
      ∀ y ∈ (E ⊓ actTrivSubgroup Λ : Subgroup G), g * y * g⁻¹ ∈ E ⊓ actTrivSubgroup Λ := by
    intro g hgE hgN y hy
    obtain ⟨hyE, hyT⟩ := hy
    refine ⟨E.mul_mem (E.mul_mem hgE hyE) (E.inv_mem hgE), ?_⟩
    obtain ⟨hyN, hytriv⟩ := mem_actTrivSubgroup.mp hyT
    have hgN' : g * y * g⁻¹ ∈ Subgroup.normalizer (Λ : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hyN) (Subgroup.inv_mem _ hgN)
    have hmul : actAut Λ ⟨g * y * g⁻¹, hgN'⟩ =
        actAut Λ ⟨g, hgN⟩ * actAut Λ ⟨y, hyN⟩ * (actAut Λ ⟨g, hgN⟩)⁻¹ := by
      rw [show (⟨g * y * g⁻¹, hgN'⟩ : ↥(Subgroup.normalizer (Λ : Set G))) =
        ⟨g, hgN⟩ * ⟨y, hyN⟩ * ⟨g, hgN⟩⁻¹ from rfl]
      rw [map_mul, map_mul, map_inv]
    have hone : actAut Λ ⟨g * y * g⁻¹, hgN'⟩ = 1 := by
      rw [hmul, (actAut_eq_one_iff hyN).mpr hytriv, mul_one, mul_inv_cancel]
    exact mem_actTrivSubgroup.mpr ⟨hgN', (actAut_eq_one_iff hgN').mp hone⟩
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact hconj e he (hE he) y
  · intro hy
    have h := hconj e⁻¹ (E.inv_mem he) (Subgroup.inv_mem _ (hE he)) (e * y * e⁻¹) hy
    rwa [show e⁻¹ * (e * y * e⁻¹) * (e⁻¹)⁻¹ = y by group] at h

end Inner

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
