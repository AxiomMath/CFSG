module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.Fischer.Classification.Recognition

open CFSG.Open
open scoped commutatorElement Pointwise

@[expose] def fischerComponentOrders : Set ℕ :=
  {9196830720, 64561751654400, 4089470473293004800}

variable {G H : Type*} [Group G] [Group H]

theorem IsSubnormal.map_mulEquiv (φ : G ≃* H) {A B : Subgroup G} (h : IsSubnormal A B) :
    IsSubnormal (A.map φ.toMonoidHom) (B.map φ.toMonoidHom) :=
  CFSG.Open.IsSubnormal.map φ.toMonoidHom h

theorem isQuasisimple_map_mulEquiv (φ : G ≃* H) {K : Subgroup G} (hK : Open.IsQuasisimple K) :
    Open.IsQuasisimple (K.map φ.toMonoidHom) := by
  set e : K ≃* K.map φ.toMonoidHom := K.equivMapOfInjective φ.toMonoidHom φ.injective
  obtain ⟨hp, hs⟩ := hK
  have hc : (Subgroup.center K).map (e : K →* K.map φ.toMonoidHom) =
      Subgroup.center (K.map φ.toMonoidHom) := Subgroup.map_center_eq e
  let e' := QuotientGroup.congr _ _ e hc
  refine ⟨?_, e'.symm.isSimpleGroup⟩
  rw [_root_.commutator_def] at hp ⊢
  rw [← Subgroup.map_top_of_surjective (e : K →* K.map φ.toMonoidHom) e.surjective,
    ← Subgroup.map_commutator, hp]

theorem IsComponentOf.map_mulEquiv (φ : G ≃* H) {K C : Subgroup G} (h : IsComponentOf K C) :
    IsComponentOf (K.map φ.toMonoidHom) (C.map φ.toMonoidHom) :=
  ⟨Subgroup.map_mono h.1, IsSubnormal.map_mulEquiv φ h.2.1, isQuasisimple_map_mulEquiv φ h.2.2⟩

theorem card_quotient_center_map_mulEquiv (φ : G ≃* H) (K : Subgroup G) :
    Nat.card (K.map φ.toMonoidHom ⧸ Subgroup.center (K.map φ.toMonoidHom)) =
      Nat.card (K ⧸ Subgroup.center K) := by
  set e : K ≃* K.map φ.toMonoidHom := K.equivMapOfInjective φ.toMonoidHom φ.injective
  have hc : (Subgroup.center K).map (e : K →* K.map φ.toMonoidHom) =
      Subgroup.center (K.map φ.toMonoidHom) := Subgroup.map_center_eq e
  exact (Nat.card_congr (QuotientGroup.congr _ _ e hc).toEquiv).symm

theorem map_centralizer_singleton (φ : G ≃* H) (d : G) :
    (Subgroup.centralizer ({d} : Set G)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ d} : Set H) := by
  ext h
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [← map_mul, ← map_mul, hg]
  · intro hh
    refine ⟨φ.symm h, φ.injective ?_, φ.apply_symm_apply h⟩
    simpa [map_mul] using hh

section Components

variable {X : Type*} [Group X]

theorem localCores_isQuasisimple {Q : Type*} [Group Q] (hQ : Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q :=
  ⟨⟨hQ.1⟩, hQ.2, ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q hQ⟩

theorem IsSubnormal.eq_or_le_center {A B : Subgroup X} (h : IsSubnormal A B)
    (hB : Open.IsQuasisimple B) : A = B ∨ A ≤ (Subgroup.center B).map B.subtype := by
  induction h with
  | refl A => exact Or.inl rfl
  | step hAM hn _ ih =>
    rename_i A M
    rcases ih hB with hMB | hM
    · subst hMB
      rcases CFSG.LocalCores.quasisimple_normal_subgroups (localCores_isQuasisimple hB) hn with
        h | h
      · exact Or.inl (le_antisymm hAM (Subgroup.subgroupOf_eq_top.mp h))
      · refine Or.inr fun x hx => ⟨⟨x, hAM hx⟩, h ?_, rfl⟩
        exact hx
    · exact Or.inr (hAM.trans hM)

theorem IsQuasisimple.not_le_of_comm {K A : Subgroup X} (hK : Open.IsQuasisimple K)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hKA : K ≤ A) : False := by
  have htop : Subgroup.center K = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hA _ (hKA y.2) _ (hKA x.2))
  have := hK.2
  obtain ⟨a, b, hab⟩ := ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK
  apply hab
  have h1 : ∀ z : K ⧸ Subgroup.center K, z = 1 := by
    intro z
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
    rw [QuotientGroup.eq_one_iff, htop]
    trivial
  rw [h1 a, h1 b]

theorem IsComponentOf.eq_of_isQuasisimple {K C : Subgroup X} (h : IsComponentOf K C)
    (hC : Open.IsQuasisimple C) : K = C := by
  rcases IsSubnormal.eq_or_le_center h.2.1 hC with h' | h'
  · exact h'
  · refine (IsQuasisimple.not_le_of_comm h.2.2 (A := (Subgroup.center C).map C.subtype)
      ?_ h').elim
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp ha b).symm

theorem IsSubnormal.inf_normal {A B N : Subgroup X} (h : IsSubnormal A B) (hNB : N ≤ B)
    (hN : (N.subgroupOf B).Normal) : IsSubnormal (A ⊓ N) N := by
  induction h with
  | refl A =>
    rw [inf_eq_right.mpr hNB]
    exact IsSubnormal.refl _
  | step hAM hn _ ih =>
    refine IsSubnormal.step (inf_le_inf_right N hAM) ?_ (ih hNB hN)
    rw [Subgroup.normal_subgroupOf_iff hAM] at hn
    rw [Subgroup.normal_subgroupOf_iff (inf_le_inf_right N hAM)]
    intro x g hx hg
    exact ⟨hn x g hx.1 hg.1, N.mul_mem (N.mul_mem hg.2 hx.2) (N.inv_mem hg.2)⟩

theorem IsQuasisimple.le_commutator {K : Subgroup X} (hK : Open.IsQuasisimple K) :
    K ≤ ⁅K, K⁆ := by
  have h := congrArg (Subgroup.map K.subtype) hK.1
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  intro x hx
  rw [h]
  exact hx

theorem commutatorElement_mul_mul_of_commute {z₁ z₂ l₁ l₂ : X} (h₁₁ : Commute z₁ l₁)
    (h₁₂ : Commute z₁ l₂) (h₂₁ : Commute z₂ l₁) (h₂₂ : Commute z₂ l₂) (hz : Commute z₁ z₂) :
    ⁅z₁ * l₁, z₂ * l₂⁆ = ⁅l₁, l₂⁆ := by
  have e₁ : z₁ * l₁ = l₁ * z₁ := h₁₁.eq
  have e₂ : z₂ * l₂ = l₂ * z₂ := h₂₂.eq
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev, mul_inv_rev]
  have c1 : Commute z₁ (l₁ * (z₂ * l₂) * l₁⁻¹) :=
    (h₁₁.mul_right (hz.mul_right h₁₂)).mul_right h₁₁.inv_right
  have c2 : Commute z₂ (l₁ * l₂ * l₁⁻¹ * l₂⁻¹) :=
    ((h₂₁.mul_right h₂₂).mul_right h₂₁.inv_right).mul_right h₂₂.inv_right
  calc z₁ * l₁ * (z₂ * l₂) * (l₁⁻¹ * z₁⁻¹) * (l₂⁻¹ * z₂⁻¹)
      = (z₁ * (l₁ * (z₂ * l₂) * l₁⁻¹) * z₁⁻¹) * l₂⁻¹ * z₂⁻¹ := by group
    _ = l₁ * (z₂ * l₂) * l₁⁻¹ * l₂⁻¹ * z₂⁻¹ := by rw [c1.eq, mul_inv_cancel_right]
    _ = z₂ * (l₁ * l₂ * l₁⁻¹ * l₂⁻¹) * z₂⁻¹ := by
        rw [show l₁ * (z₂ * l₂) = z₂ * (l₁ * l₂) by
          rw [← mul_assoc, ← h₂₁.eq, mul_assoc]]
        group
    _ = l₁ * l₂ * l₁⁻¹ * l₂⁻¹ := by rw [c2.eq, mul_inv_cancel_right]

theorem IsComponentOf.eq_of_sup_zpowers {K C L : Subgroup X} {d : X} (h : IsComponentOf K C)
    (hC : C = Subgroup.zpowers d ⊔ L)
    (hdL : Subgroup.zpowers d ≤ Subgroup.centralizer (L : Set X)) (hL : Open.IsQuasisimple L) :
    K = L := by
  have hLC : L ≤ C := hC ▸ le_sup_right
  have hdec : ∀ x ∈ C, ∃ z ∈ Subgroup.zpowers d, ∃ l ∈ L, z * l = x := by
    intro x hx
    rw [hC] at hx
    have hx' : x ∈ ((Subgroup.zpowers d : Set X) * (L : Set X)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _
        (hdL.trans (Subgroup.centralizer_le_normalizer _))]
      exact hx
    obtain ⟨z, hz, l, hl, rfl⟩ := hx'
    exact ⟨z, hz, l, hl, rfl⟩
  have hcomm : ∀ z ∈ Subgroup.zpowers d, ∀ l ∈ L, Commute z l := fun z hz l hl =>
    (Subgroup.mem_centralizer_iff.mp (hdL hz) l hl).symm
  have hzz : ∀ z₁ ∈ Subgroup.zpowers d, ∀ z₂ ∈ Subgroup.zpowers d, Commute z₁ z₂ := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact Commute.zpow_zpow_self d i j
  have hCC : ∀ a ∈ C, ∀ b ∈ C, ⁅a, b⁆ ∈ L := by
    intro a ha b hb
    obtain ⟨z₁, hz₁, l₁, hl₁, rfl⟩ := hdec a ha
    obtain ⟨z₂, hz₂, l₂, hl₂, rfl⟩ := hdec b hb
    rw [commutatorElement_mul_mul_of_commute (hcomm _ hz₁ _ hl₁) (hcomm _ hz₁ _ hl₂)
      (hcomm _ hz₂ _ hl₁) (hcomm _ hz₂ _ hl₂) (hzz _ hz₁ _ hz₂)]
    rw [commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem hl₁ hl₂) (L.inv_mem hl₁)) (L.inv_mem hl₂)
  have hKL : K ≤ L := by
    refine (IsQuasisimple.le_commutator h.2.2).trans ?_
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact hCC a (h.1 ha) b (h.1 hb)
  have hLn : (L.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hLC]
    intro l g hl hg
    obtain ⟨z, hz, l', hl', rfl⟩ := hdec g hg
    have : z * l' * l * (z * l')⁻¹ = l' * l * l'⁻¹ := by
      rw [mul_inv_rev, show z * l' * l * (l'⁻¹ * z⁻¹) = z * (l' * l * l'⁻¹) * z⁻¹ by group,
        ((hcomm z hz _ hl').mul_right (hcomm z hz _ hl) |>.mul_right
          (hcomm z hz _ hl').inv_right).eq, mul_inv_cancel_right]
    rw [this]
    exact L.mul_mem (L.mul_mem hl' hl) (L.inv_mem hl')
  have hsub : IsSubnormal K L := by
    have := IsSubnormal.inf_normal h.2.1 hLC hLn
    rwa [inf_eq_left.mpr hKL] at this
  rcases IsSubnormal.eq_or_le_center hsub hL with h' | h'
  · exact h'
  · refine (IsQuasisimple.not_le_of_comm h.2.2 (A := (Subgroup.center L).map L.subtype)
      ?_ h').elim
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp ha b).symm

end Components

end CFSG.Fischer.Classification.Recognition
