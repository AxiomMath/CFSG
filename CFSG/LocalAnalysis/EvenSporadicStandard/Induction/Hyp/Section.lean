module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Basic
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.EvenSporadicStandard.Solomon78
open scoped Pointwise

variable {H : Type} [Group H]

@[expose] def secPre (Q : Subgroup H) {s : H} (hs : s ∈ normalizer (Q : Set H)) :
    ↥(Q ⊔ zpowers s) →* MulAut ↥Q :=
  (normalizerMonoidHom Q).comp (Subgroup.inclusion
    (sup_le Subgroup.le_normalizer (by rw [zpowers_le]; exact hs)))

@[expose] def secGrp (Q : Subgroup H) {s : H} (hs : s ∈ normalizer (Q : Set H)) :
    Subgroup (MulAut ↥Q) :=
  (secPre Q hs).range

@[expose] def innSub (Q : Subgroup H) : Subgroup (MulAut ↥Q) :=
  (MulAut.conj : ↥Q →* MulAut ↥Q).range

variable (Q : Subgroup H) {s : H} (hs : s ∈ normalizer (Q : Set H))

theorem secPre_apply (x : ↥(Q ⊔ zpowers s)) (q : ↥Q) :
    ((secPre Q hs x q : ↥Q) : H) = (x : H) * q * (x : H)⁻¹ :=
  normalizerMonoidHom_apply_apply_coe Q _ q

include hs in
theorem secPre_eq_one_iff (x : ↥(Q ⊔ zpowers s)) :
    secPre Q hs x = 1 ↔ (x : H) ∈ centralizer (Q : Set H) := by
  rw [mem_centralizer_iff]
  constructor
  · intro h q hq
    have := secPre_apply Q hs x ⟨q, hq⟩
    rw [h] at this
    have h2 : (q : H) = (x : H) * q * (x : H)⁻¹ := this
    calc q * (x : H) = ((x : H) * q * (x : H)⁻¹) * (x : H) := by rw [← h2]
      _ = (x : H) * q := by group
  · intro h
    ext q
    rw [secPre_apply]
    have := h q q.2
    simp only [MulAut.one_apply]
    calc (x : H) * q * (x : H)⁻¹ = (q * (x : H)) * (x : H)⁻¹ := by rw [this]
      _ = q := by group

include hs in
theorem innSub_le_secGrp : innSub Q ≤ secGrp Q hs := by
  rintro _ ⟨q, rfl⟩
  refine ⟨⟨q, mem_sup_left q.2⟩, ?_⟩
  ext r
  rw [secPre_apply]
  simp [MulAut.conj_apply]

omit hs in
theorem ker_conj_eq_center : (MulAut.conj : ↥Q →* MulAut ↥Q).ker = center ↥Q := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h r
    have := congrArg (fun α : MulAut ↥Q => α r) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc r * g = (g * r * g⁻¹) * g := by rw [this]
      _ = g * r := by group
  · intro h
    ext r
    simp only [MulAut.conj_apply, MulAut.one_apply]
    exact congrArg Subtype.val (show g * r * g⁻¹ = r from by
      calc g * r * g⁻¹ = (r * g) * g⁻¹ := by rw [h r]
        _ = r := by group)

omit hs in
theorem innSub_normal : (innSub Q).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨q, rfl⟩ α
  refine ⟨α q, ?_⟩
  ext r
  simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

omit hs in
noncomputable def innSubEquiv : (↥Q ⧸ center ↥Q) ≃* ↥(innSub Q) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_conj_eq_center Q).symm).trans
    (QuotientGroup.quotientKerEquivRange (MulAut.conj : ↥Q →* MulAut ↥Q))

omit hs in
theorem innSub_simple (hq : CFSG.IsQuasisimple ↥Q) : IsSimpleGroup ↥(innSub Q) := by
  have := hq.2.1
  exact MulEquiv.isSimpleGroup (innSubEquiv Q).symm

omit hs in
theorem innSub_nonabelian (hq : CFSG.IsQuasisimple ↥Q) :
    ∃ a b : ↥(innSub Q), a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hq.2.2
  exact ⟨innSubEquiv Q a, innSubEquiv Q b, fun h => hab ((innSubEquiv Q).injective (by
    simpa [map_mul] using h))⟩

omit hs in
theorem eq_one_of_commute_conj (hperf : Group.IsPerfect ↥Q) {α : MulAut ↥Q}
    (h : ∀ q : ↥Q, α * MulAut.conj q = MulAut.conj q * α) : α = 1 := by
  have hz : ∀ q : ↥Q, q⁻¹ * α q ∈ center ↥Q := by
    intro q
    rw [Subgroup.mem_center_iff]
    intro r
    have h1 := congrArg (fun β : MulAut ↥Q => β (α.symm r)) (h q)
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply] at h1
    calc r * (q⁻¹ * α q) = q⁻¹ * ((q * r * q⁻¹) * α q) := by group
      _ = q⁻¹ * ((α q * r * (α q)⁻¹) * α q) := by rw [h1]
      _ = (q⁻¹ * α q) * r := by group
  let f : ↥Q →* ↥(center ↥Q) :=
    { toFun := fun q => ⟨q⁻¹ * α q, hz q⟩
      map_one' := by simp
      map_mul' := fun a b => by
        apply Subtype.ext
        have hza := Subgroup.mem_center_iff.1 (hz a) (b⁻¹)
        simp only [Subgroup.coe_mul, mul_inv_rev, map_mul]
        calc b⁻¹ * a⁻¹ * (α a * α b) = (b⁻¹ * (a⁻¹ * α a)) * α b := by group
          _ = ((a⁻¹ * α a) * b⁻¹) * α b := by rw [hza]
          _ = (a⁻¹ * α a) * (b⁻¹ * α b) := by group }
  ext q
  have := eq_one_of_perfect_of_comm hperf f (fun a b => Subtype.ext
    (Subgroup.mem_center_iff.1 a.2 (b : ↥Q)).symm) q
  have h2 : q⁻¹ * α q = 1 := congrArg Subtype.val this
  have h3 : α q = q := by
    calc α q = q * (q⁻¹ * α q) := by group
      _ = q := by rw [h2, mul_one]
  simpa using h3

omit hs in
theorem exists_zpow_mul_of_mem_sup {s : H} (hs : s ∈ normalizer (Q : Set H)) {x : H}
    (hx : x ∈ Q ⊔ zpowers s) : ∃ (m : ℤ) (q : H), q ∈ Q ∧ x = s ^ m * q := by
  have hle : zpowers s ≤ normalizer (Q : Set H) := by
    rw [zpowers_le]
    exact hs
  have hmem : x ∈ ((zpowers s : Set H) * (Q : Set H)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (zpowers s) Q hle]
    exact (sup_comm Q (zpowers s)) ▸ hx
  obtain ⟨a, ha, t, ht, rfl⟩ := hmem
  obtain ⟨m, rfl⟩ := ha
  exact ⟨m, t, ht, rfl⟩

section Props

variable [Finite H]

include hs in
theorem secGrp_fStarSimple (hq : CFSG.IsQuasisimple ↥Q) :
    FStarSimple ((innSub Q).subgroupOf (secGrp Q hs)) := by
  have hle := innSub_le_secGrp Q hs
  have hN : ((innSub Q).subgroupOf (secGrp Q hs)).Normal := (innSub_normal Q).subgroupOf _
  have := innSub_simple Q hq
  have hsimple : IsSimpleGroup ↥((innSub Q).subgroupOf (secGrp Q hs)) :=
    MulEquiv.isSimpleGroup (Subgroup.subgroupOfEquivOfLe hle)
  have hna : ∃ a b : ↥((innSub Q).subgroupOf (secGrp Q hs)), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := innSub_nonabelian Q hq
    exact ⟨(Subgroup.subgroupOfEquivOfLe hle).symm a, (Subgroup.subgroupOfEquivOfLe hle).symm b,
      fun h => hab ((Subgroup.subgroupOfEquivOfLe hle).symm.injective (by
        simpa [map_mul] using h))⟩
  refine fStarSimple_of_normal_simple hsimple hna fun β hβ => ?_
  have h1 : β.val = 1 := by
    refine eq_one_of_commute_conj Q hq.1 fun q => ?_
    have hn : (⟨MulAut.conj q, hle ⟨q, rfl⟩⟩ : ↥(secGrp Q hs)) ∈
        (innSub Q).subgroupOf (secGrp Q hs) := ⟨q, rfl⟩
    have := mem_centralizer_iff.1 hβ _ hn
    exact (congrArg Subtype.val this).symm
  have : β = 1 := Subtype.ext h1
  rw [this]
  exact one_mem _

omit [Finite H] in
include hs in
theorem secGrp_index_le_two (hs2 : s ^ 2 ∈ centralizer (Q : Set H)) :
    ((innSub Q).subgroupOf (secGrp Q hs)).index ≤ 2 := by
  have hN : ((innSub Q).subgroupOf (secGrp Q hs)).Normal := (innSub_normal Q).subgroupOf _
  let xs : ↥(Q ⊔ zpowers s) := ⟨s, mem_sup_right (mem_zpowers s)⟩
  let σ : ↥(secGrp Q hs) := ⟨secPre Q hs xs, ⟨xs, rfl⟩⟩
  have hσ2 : σ * σ = 1 := by
    apply Subtype.ext
    show secPre Q hs xs * secPre Q hs xs = 1
    rw [← map_mul]
    exact (secPre_eq_one_iff Q hs _).2 (by simpa [xs, sq] using hs2)
  have hcov : ∀ y : ↥(secGrp Q hs) ⧸ (innSub Q).subgroupOf (secGrp Q hs),
      y = QuotientGroup.mk 1 ∨ y = QuotientGroup.mk σ := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨β, x, hx⟩ := g
    obtain ⟨m, q, hq, hxm⟩ := exists_zpow_mul_of_mem_sup Q hs x.2
    have hxeq : x = xs ^ m * ⟨q, mem_sup_left hq⟩ := by
      apply Subtype.ext
      simp [xs, hxm]
    have hβ : (⟨β, ⟨x, hx⟩⟩ : ↥(secGrp Q hs)) =
        σ ^ m * ⟨MulAut.conj (⟨q, hq⟩ : ↥Q), innSub_le_secGrp Q hs ⟨⟨q, hq⟩, rfl⟩⟩ := by
      apply Subtype.ext
      show β = (secPre Q hs xs) ^ m * MulAut.conj (⟨q, hq⟩ : ↥Q)
      rw [← hx, hxeq, map_mul, map_zpow]
      congr 1
      ext r
      rw [secPre_apply]
      simp [MulAut.conj_apply]
    have hnn : (⟨MulAut.conj (⟨q, hq⟩ : ↥Q), innSub_le_secGrp Q hs ⟨⟨q, hq⟩, rfl⟩⟩ :
        ↥(secGrp Q hs)) ∈ (innSub Q).subgroupOf (secGrp Q hs) := ⟨⟨q, hq⟩, rfl⟩
    have hmk : (QuotientGroup.mk (σ ^ m * ⟨MulAut.conj (⟨q, hq⟩ : ↥Q),
        innSub_le_secGrp Q hs ⟨⟨q, hq⟩, rfl⟩⟩) : ↥(secGrp Q hs) ⧸
          (innSub Q).subgroupOf (secGrp Q hs)) = QuotientGroup.mk (σ ^ m) := by
      rw [QuotientGroup.eq]
      simpa using (Subgroup.inv_mem _ hnn)
    rw [hβ, hmk]
    obtain ⟨k, hk | hk⟩ := Int.even_or_odd' m
    · left
      have : σ ^ m = 1 := by
        rw [hk, zpow_mul]
        have h2 : σ ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hσ2
        rw [h2, one_zpow]
      rw [this]
    · right
      have : σ ^ m = σ := by
        rw [hk, zpow_add, zpow_mul]
        have h2 : σ ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hσ2
        rw [h2, one_zpow, one_mul, zpow_one]
      rw [this]
  have hsur : Function.Surjective (fun i : Fin 2 =>
      if i = 0 then (QuotientGroup.mk 1 : ↥(secGrp Q hs) ⧸ (innSub Q).subgroupOf (secGrp Q hs))
      else QuotientGroup.mk σ) := by
    intro y
    rcases hcov y with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  have := Nat.card_le_card_of_surjective _ hsur
  simpa [Subgroup.index] using this

include hs in
theorem secGrp_card_le (hs2 : s ^ 2 ∈ centralizer (Q : Set H)) :
    Nat.card ↥(secGrp Q hs) ≤ 2 * Nat.card ↥Q := by
  have hle := innSub_le_secGrp Q hs
  have hidx := secGrp_index_le_two Q hs hs2
  have h1 := Subgroup.index_mul_card ((innSub Q).subgroupOf (secGrp Q hs))
  have h2 : Nat.card ↥((innSub Q).subgroupOf (secGrp Q hs)) = Nat.card ↥(innSub Q) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have h3 : Nat.card ↥(innSub Q) ≤ Nat.card ↥Q :=
    Nat.card_le_card_of_surjective _ (MulAut.conj : ↥Q →* MulAut ↥Q).rangeRestrict_surjective
  rw [h2] at h1
  calc Nat.card ↥(secGrp Q hs) = ((innSub Q).subgroupOf (secGrp Q hs)).index *
        Nat.card ↥(innSub Q) := h1.symm
    _ ≤ 2 * Nat.card ↥Q := Nat.mul_le_mul hidx h3

include hs in
theorem secGrp_card_lt {N : Subgroup H} (hN : FStarSimple N) (hq : CFSG.IsQuasisimple ↥Q)
    (hQN : Q ≤ N) (hne : Q ≠ N) (hs2 : s ^ 2 ∈ centralizer (Q : Set H)) :
    Nat.card ↥(secGrp Q hs) < Nat.card H := by
  have hQb : Q ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot Q).1 (CFSG.LocalCores.isQuasisimple_nontrivial hq)
  have h3 := three_mul_card_le_of_proper hN.isSimpleGroup hQN hne hQb
  have h4 : Nat.card ↥N ≤ Nat.card H := Subgroup.card_le_card_group N
  have h5 := secGrp_card_le Q hs hs2
  have h6 : 0 < Nat.card ↥Q := Nat.card_pos
  omega

omit [Finite H] in
include hs in
theorem secGrp_kProper (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) :
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog ↥(secGrp Q hs) :=
  kProper_of_section hkp (Q ⊔ zpowers s) (secPre Q hs).rangeRestrict
    (secPre Q hs).rangeRestrict_surjective

end Props

end CFSG.EvenSporadicStandard.Induction.Hyp
