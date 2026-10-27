module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneInputs

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.TBLit CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def BurgOddCoreFor {L : Type} [Group L] (α : MulAut L) : Prop :=
  pPrimeCore 2 (fixedSubgroup α) = ⊥ ∧
    ∀ β : MulAut L, Odd (orderOf β) → α * β = β * α →
      (∀ x ∈ fixedSubgroup α, β x = x) → β = 1

@[expose] def BurgOddCoreRow (L : Type) [Group L] : Prop :=
  ∀ α : MulAut L, orderOf α = 2 → BurgOddCoreFor α

@[expose] def mulAutTransfer {L L' : Type} [Group L] [Group L'] (e : L ≃* L') :
    MulAut L' →* MulAut L where
  toFun α := (e.trans α).trans e.symm
  map_one' := by
    ext x
    simp
  map_mul' α β := by
    ext x
    simp

theorem mulAutTransfer_apply {L L' : Type} [Group L] [Group L'] (e : L ≃* L') (α : MulAut L')
    (x : L) : mulAutTransfer e α x = e.symm (α (e x)) :=
  rfl

theorem mulAutTransfer_injective {L L' : Type} [Group L] [Group L'] (e : L ≃* L') :
    Function.Injective (mulAutTransfer e) := by
  intro α β h
  ext y
  have h1 := congrArg (fun γ : MulAut L => γ (e.symm y)) h
  simp only [mulAutTransfer_apply, MulEquiv.apply_symm_apply] at h1
  exact e.symm.injective h1

theorem mem_fixedSubgroup_mulAutTransfer {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (α : MulAut L') (x : L) :
    x ∈ fixedSubgroup (mulAutTransfer e α) ↔ e x ∈ fixedSubgroup α := by
  change e.symm (α (e x)) = x ↔ α (e x) = e x
  constructor
  · intro h
    have h1 := congrArg e h
    rwa [MulEquiv.apply_symm_apply] at h1
  · intro h
    rw [h, MulEquiv.symm_apply_apply]

theorem burgOddCoreFor_of_mulAutTransfer {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (α : MulAut L') (h : BurgOddCoreFor (mulAutTransfer e α)) : BurgOddCoreFor α := by
  have hinj := mulAutTransfer_injective e
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun β hβ hαβ hfix => ?_⟩
  · have hmap : (fixedSubgroup (mulAutTransfer e α)).map e.toMonoidHom = fixedSubgroup α := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (mem_fixedSubgroup_mulAutTransfer e α x).1 hx
      · intro hy
        refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
        rw [SetLike.mem_coe, mem_fixedSubgroup_mulAutTransfer, MulEquiv.apply_symm_apply]
        exact hy
    let φ : fixedSubgroup (mulAutTransfer e α) ≃* fixedSubgroup α :=
      (e.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)
    have h3 := pPrimeCore_map_iso 2 φ
    rw [h1, Subgroup.map_bot] at h3
    exact h3.symm
  · have hβ' : Odd (orderOf (mulAutTransfer e β)) := by
      rwa [orderOf_injective _ hinj β]
    have hc : mulAutTransfer e α * mulAutTransfer e β =
        mulAutTransfer e β * mulAutTransfer e α := by
      rw [← map_mul, ← map_mul, hαβ]
    have hf : ∀ x ∈ fixedSubgroup (mulAutTransfer e α), mulAutTransfer e β x = x := by
      intro x hx
      rw [mulAutTransfer_apply, hfix (e x) ((mem_fixedSubgroup_mulAutTransfer e α x).1 hx),
        MulEquiv.symm_apply_apply]
    exact hinj ((h2 _ hβ' hc hf).trans (map_one _).symm)

theorem burgOddCoreRow_of_mulEquiv {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (h : BurgOddCoreRow L) : BurgOddCoreRow L' := fun α hα =>
  burgOddCoreFor_of_mulAutTransfer e α
    (h _ ((orderOf_injective _ (mulAutTransfer_injective e) α).trans hα))

theorem burgOddCoreFor_of_conj {L : Type} [Group L] (ψ α : MulAut L)
    (h : BurgOddCoreFor (ψ * α * ψ⁻¹)) : BurgOddCoreFor α := by
  refine burgOddCoreFor_of_mulAutTransfer ψ.symm α ?_
  have e : mulAutTransfer ψ.symm α = ψ * α * ψ⁻¹ := by
    ext x
    rfl
  rwa [e]

theorem burgOddCoreFor_of_inner {L : Type} [Group L] [Finite L] (hZ : Subgroup.center L = ⊥)
    {α : MulAut L} (h1 : pPrimeCore 2 (fixedSubgroup α) = ⊥)
    (h2 : ∀ β : MulAut L, Odd (orderOf β) → α * β = β * α →
      (∀ x ∈ fixedSubgroup α, β x = x) → β ∈ (MulAut.conj : L →* MulAut L).range) :
    BurgOddCoreFor α := by
  have hinj : Function.Injective (MulAut.conj : L →* MulAut L) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgZ : g ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h3 := congrArg (fun φ : MulAut L => φ x) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      calc x * g = g * x * g⁻¹ * g := by rw [h3]
        _ = g * x := by group
    rw [hZ, Subgroup.mem_bot] at hgZ
    exact hgZ
  refine ⟨h1, fun β hβ hαβ hfix => ?_⟩
  obtain ⟨g, rfl⟩ := h2 β hβ hαβ hfix
  have hgα : α g = g := by
    have h3 : MulAut.conj (α g) = α * MulAut.conj g * α⁻¹ := by
      ext x
      simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]
    have h4 : α * MulAut.conj g * α⁻¹ = MulAut.conj g := by
      rw [hαβ, mul_inv_cancel_right]
    exact hinj (h3.trans h4)
  let g' : fixedSubgroup α := ⟨g, hgα⟩
  have hg'Z : g' ∈ Subgroup.center (fixedSubgroup α) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h3 := hfix x x.2
    simp only [MulAut.conj_apply] at h3
    refine Subtype.ext ?_
    change (x : L) * g = g * x
    calc (x : L) * g = g * x * g⁻¹ * g := by rw [h3]
      _ = g * x := by group
  have hnorm : (Subgroup.zpowers g').Normal := ⟨fun y hy k => by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [Subgroup.mem_center_iff.1 (Subgroup.zpow_mem _ hg'Z n) k, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers g') n⟩
  have hodd : Nat.Coprime 2 (Nat.card (Subgroup.zpowers g')) := by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, show ((g' : L)) = g from rfl,
      ← orderOf_injective _ hinj g]
    exact Nat.coprime_two_left.2 hβ
  have hbot := (pPrimeCore_eq_bot_iff.1 h1) _ hnorm hodd
  have hg1 : g' = 1 := by
    have h3 : g' ∈ Subgroup.zpowers g' := Subgroup.mem_zpowers g'
    rw [hbot, Subgroup.mem_bot] at h3
    exact h3
  have hg : g = 1 := congrArg Subtype.val hg1
  rw [hg, map_one]

theorem oddCentralizerCore_eq_bot_of_row {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (hrow : BurgOddCoreRow (GeneralizedFitting.subgroup X)) {t : X} (ht : orderOf t = 2) :
    oddCentralizerCore t = ⊥ := by
  set L := GeneralizedFitting.subgroup X with hLdef
  have hLn : L.Normal := GeneralizedFitting.normal X
  have hZ : Subgroup.center L = ⊥ := by
    have := hsimple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have hb : b ∈ Subgroup.center L := h ▸ Subgroup.mem_top b
      exact hab ((Subgroup.mem_center_iff.1 hb) a)
  let c : X →* MulAut L := MulAut.conjNormal
  have hc : Function.Injective c := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxC : x ∈ Subgroup.centralizer (L : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 := congrArg (fun φ : MulAut L => ((φ ⟨l, hl⟩ : L) : X)) hx
      simp only [c, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc l * x = x * l * x⁻¹ * x := by rw [h1]
        _ = x * l := by group
    have hxL : x ∈ L := GeneralizedFitting.centralizer_le X hxC
    have hxZ : (⟨x, hxL⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hxC) g g.2)
    rw [hZ, Subgroup.mem_bot] at hxZ
    exact congrArg Subtype.val hxZ
  have hαo : orderOf (c t) = 2 := (orderOf_injective c hc t).trans ht
  obtain ⟨hF1, hF2⟩ := hrow (c t) hαo
  have hfixC : ∀ l : L, l ∈ fixedSubgroup (c t) → (l : X) ∈ centralizer ({t} : Set X) := by
    intro l hl
    have h1 : t * l * t⁻¹ = l := by
      have h2 := congrArg Subtype.val (show c t l = l from hl)
      simpa [c] using h2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (l : X) * t = t * l * t⁻¹ * t := by rw [h1]
      _ = t * l := by group
  rw [eq_bot_iff]
  rintro _ ⟨z, hz, rfl⟩
  have hzY : (z : X) ∈ oddCentralizerCore t := ⟨z, hz, rfl⟩
  have hzt : t * z = z * t := (Subgroup.mem_centralizer_singleton_iff.1 z.2).symm
  have hodd : Odd (orderOf (c z)) := by
    have h1 : Odd (orderOf z) := Nat.coprime_two_left.mp
      (pPrimeCore_coprime_card.coprime_dvd_right (Subgroup.orderOf_dvd_natCard _ hz))
    rw [← Subgroup.orderOf_coe] at h1
    exact Odd.of_dvd_nat h1 (orderOf_map_dvd c (z : X))
  have hcomm : c t * c z = c z * c t := by
    rw [← map_mul, ← map_mul, hzt]
  have hfix : ∀ l ∈ fixedSubgroup (c t), c z l = l := by
    intro l hl
    let φ : fixedSubgroup (c t) →* X := L.subtype.comp (fixedSubgroup (c t)).subtype
    have hφ : Function.Injective φ := Subtype.val_injective.comp Subtype.val_injective
    let W : Subgroup (fixedSubgroup (c t)) := (oddCentralizerCore t).comap φ
    have hWn : W.Normal := ⟨fun w hw k => by
      change φ (k * w * k⁻¹) ∈ oddCentralizerCore t
      rw [map_mul, map_mul, map_inv]
      exact conj_mem_oddCentralizerCore (hfixC _ k.2) hw⟩
    have hWodd : Nat.Coprime 2 (Nat.card W) := by
      rw [← Subgroup.card_map_of_injective hφ]
      exact (coprime_card_oddCentralizerCore t).coprime_dvd_right
        (Subgroup.card_dvd_of_le (Subgroup.map_comap_le _ _))
    have hW : W = ⊥ := pPrimeCore_eq_bot_iff.1 hF1 W hWn hWodd
    have hlC := hfixC l hl
    have hlt : t * l = l * t := (Subgroup.mem_centralizer_singleton_iff.1 hlC).symm
    have hwL : (z : X) * l * (z : X)⁻¹ * (l : X)⁻¹ ∈ L :=
      mul_mem (hLn.conj_mem _ l.2 _) (inv_mem l.2)
    have hwY : (z : X) * l * (z : X)⁻¹ * (l : X)⁻¹ ∈ oddCentralizerCore t := by
      have h1 : (l : X) * (z : X)⁻¹ * (l : X)⁻¹ ∈ oddCentralizerCore t :=
        conj_mem_oddCentralizerCore hlC (inv_mem hzY)
      have h2 := mul_mem hzY h1
      rwa [show (z : X) * ((l : X) * (z : X)⁻¹ * (l : X)⁻¹) =
        (z : X) * l * (z : X)⁻¹ * (l : X)⁻¹ by group] at h2
    have hwfix : (⟨_, hwL⟩ : L) ∈ fixedSubgroup (c t) := by
      change c t ⟨_, hwL⟩ = ⟨_, hwL⟩
      refine Subtype.ext ?_
      change t * ((z : X) * l * (z : X)⁻¹ * (l : X)⁻¹) * t⁻¹ = _
      have e := fun a : X => (MulAut.conj_apply t a).symm
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, MulAut.conj_apply,
        MulAut.conj_apply, hzt, hlt, mul_inv_cancel_right, mul_inv_cancel_right]
    have hw1 : (⟨⟨_, hwL⟩, hwfix⟩ : fixedSubgroup (c t)) ∈ W := hwY
    rw [hW, Subgroup.mem_bot] at hw1
    have hw2 : (z : X) * l * (z : X)⁻¹ * (l : X)⁻¹ = 1 :=
      congrArg (fun u : fixedSubgroup (c t) => ((u : L) : X)) hw1
    refine Subtype.ext ?_
    change (z : X) * l * (z : X)⁻¹ = l
    exact mul_inv_eq_one.1 hw2
  exact hc ((hF2 (c z) hodd hcomm hfix).trans (map_one c).symm)

theorem burgoyneExcOddCoreInput_of_row
    (h : ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) →
      ∀ (τ : StatedLieTag) (n p f : ℕ), τ ∈ Burgoyne.oddExceptionalTags →
        τ ∉ Burgoyne.torusExceptionalTags → p ≠ 2 → LieModel L τ n p f → BurgOddCoreRow L) :
    ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup (GeneralizedFitting.subgroup X) →
      (∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) →
      ∀ (τ : StatedLieTag) (n p f : ℕ), τ ∈ Burgoyne.oddExceptionalTags →
        τ ∉ Burgoyne.torusExceptionalTags →
        p ≠ 2 → LieModel (GeneralizedFitting.subgroup X) τ n p f →
      ∀ t : X, orderOf t = 2 → oddCentralizerCore t = ⊥ := by
  intro X _ _ hsimple hnab τ n p f hτ hτ' hp hL t ht
  exact oddCentralizerCore_eq_bot_of_row hsimple hnab (h _ hsimple hnab τ n p f hτ hτ' hp hL) ht

end CFSG.ComponentClassification.CatLeafProof
