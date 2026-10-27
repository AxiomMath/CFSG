module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepHStmts

public section

namespace CFSG.OddStandard.GH71.S55

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
open scoped Pointwise

section Defs

variable {Y : Type} [Group Y]

@[expose] def RFree (r : ℕ) (y : Y) : Prop :=
  ∀ E : Subgroup Y, IsPGroup r ↥E → (∀ x ∈ E, y * x * y⁻¹ ∈ E) → E = ⊥

@[expose] def Comp5Concl (r : ℕ) (y : Y) : Prop :=
  ∃ L : Subgroup Y, L ≠ ⊤ ∧ IsQuasisimple ↥L ∧ OddChev r (↥L ⧸ center ↥L) ∧
    y ∈ normalizer (L : Set Y) ∧ ⁅L, zpowers y⁆ ≠ ⊥

end Defs

theorem comp5_of {Fd : ℕ → (Y : Type) → [Group Y] → Prop}
    (h : ∀ (r p : ℕ) (Y : Type) [Group Y] [Finite Y], r.Prime → r ≠ 2 → p.Prime → 5 ≤ p →
      r ≠ p → Fd r Y → ∀ y g : Y, orderOf y = p → RFree r y → PairSL2 p y g →
        Comp5Concl r y) :
    Comp5 Fd := h

namespace C5

noncomputable def centerQuotCongr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    A ⧸ center A ≃* B ⧸ center B :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

theorem oddChev_congr {r : ℕ} {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : OddChev r A) : OddChev r B := by
  open CFSG.LieType.CurtisTits in
  obtain ⟨hr, hr2, h⟩ := h
  refine ⟨hr, hr2, ?_⟩
  rcases h with ⟨f, hf, h⟩ | ⟨f, hf, h⟩ | ⟨f, hf, h⟩ | ⟨f, hf, h⟩ | ⟨f, hf, h⟩ | ⟨f, hf, h⟩ |
    ⟨f, hf, h8, h⟩ | ⟨f, hf, h8, h⟩ | ⟨h3, f, hf, h⟩
  · exact Or.inl ⟨f, hf, lieModel_of_mulEquiv e h⟩
  · exact Or.inr (Or.inl ⟨f, hf, lieModel_of_mulEquiv e h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f, hf, lieModel_of_mulEquiv e h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, lieModel_of_mulEquiv e h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, lieModel_of_mulEquiv e h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, lieModel_of_mulEquiv e h⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨f, hf, h8, lieModel_of_mulEquiv e h⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨f, hf, h8, lieModel_of_mulEquiv e h⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨h3, f, hf, lieModel_of_mulEquiv e h⟩)))))))

theorem mem_normalizer_of_conj_mem {Y : Type} [Group Y] [Finite Y] {U : Subgroup Y} {g : Y}
    (h : ∀ x ∈ U, g * x * g⁻¹ ∈ U) : g ∈ normalizer (U : Set Y) := by
  have hle : U.map (MulAut.conj g).toMonoidHom ≤ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : U.map (MulAut.conj g).toMonoidHom = U :=
    eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj g).injective])
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
  rw [mul_left_cancel (mul_right_cancel hyx)] at hy
  exact hy

end C5

open C5

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_conj_mem_of_not_dvd_index {p : ℕ} [hp : Fact p.Prime] {M : Subgroup Y}
    (hM : ¬ p ∣ M.index) {y : Y} (hy : orderOf y = p) : ∃ g : Y, g * y * g⁻¹ ∈ M := by
  obtain ⟨Q⟩ : Nonempty (Sylow p ↥M) := inferInstance
  have hQ : IsPGroup p ↥((Q : Subgroup ↥M).map M.subtype) := Q.isPGroup'.map M.subtype
  have hidx : ¬ p ∣ ((Q : Subgroup ↥M).map M.subtype).index := by
    rw [Subgroup.index_map_subtype]
    intro hd
    rcases (Nat.Prime.dvd_mul hp.out).mp hd with h | h
    · exact Q.not_dvd_index h
    · exact hM h
  have hy' : IsPGroup p ↥(zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨P', hP'⟩ := hy'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y P' (hQ.toSylow hidx)
  refine ⟨g, ?_⟩
  have h1 : MulAut.conj g • y ∈ MulAut.conj g • (P' : Subgroup Y) :=
    Subgroup.smul_mem_pointwise_smul y _ _ (hP' (mem_zpowers y))
  rw [← Sylow.coe_subgroup_smul, hg] at h1
  exact map_subtype_le _ (show g * y * g⁻¹ ∈ (Q : Subgroup ↥M).map M.subtype from h1)

theorem not_rFree_of_le_normalizer {p r : ℕ} [Fact p.Prime] {U M : Subgroup Y}
    (hU : IsPGroup r ↥U) (hU1 : U ≠ ⊥) (hMU : M ≤ normalizer (U : Set Y)) (hM : ¬ p ∣ M.index)
    {y : Y} (hy : orderOf y = p) : ¬ RFree r y := by
  intro hyr
  obtain ⟨g, hg⟩ := exists_conj_mem_of_not_dvd_index hM hy
  have hU' : U.map (MulAut.conj g⁻¹).toMonoidHom = ⊥ := by
    refine hyr _ (hU.map _) ?_
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨g * y * g⁻¹ * u * (g * y * g⁻¹)⁻¹,
      (mem_normalizer_iff.mp (hMU hg) u).mp hu, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  exact hU1 ((map_eq_bot_iff_of_injective _ (MulAut.conj g⁻¹).injective).mp hU')

theorem comp5Concl_of_block {p r : ℕ} [Fact p.Prime] [Fact r.Prime] {L M : Subgroup Y}
    (hM : ¬ p ∣ M.index) (hML : M ≤ normalizer (L : Set Y)) (hLt : L ≠ ⊤)
    (hq : IsQuasisimple ↥L) (hc : OddChev r (↥L ⧸ center ↥L)) (hrL : r ∣ Nat.card L)
    {y : Y} (hy : orderOf y = p) (hyr : RFree r y) : Comp5Concl r y := by
  obtain ⟨g, hg⟩ := exists_conj_mem_of_not_dvd_index hM hy
  set L' := L.map (MulAut.conj g⁻¹).toMonoidHom with hL'
  let e : ↥L ≃* ↥L' := L.equivMapOfInjective _ (MulAut.conj g⁻¹).injective
  have hcard : Nat.card L' = Nat.card L := (Nat.card_congr e.toEquiv).symm
  refine ⟨L', ?_, LocalCores.isQuasisimple_of_mulEquiv e hq, oddChev_congr (centerQuotCongr e) hc,
    mem_normalizer_of_conj_mem ?_, ?_⟩
  · intro htop
    apply hLt
    apply Subgroup.eq_top_of_card_eq
    rw [← hcard, htop, Subgroup.card_top]
  · rintro _ ⟨l, hl, rfl⟩
    refine ⟨g * y * g⁻¹ * l * (g * y * g⁻¹)⁻¹, (mem_normalizer_iff.mp (hML hg) l).mp hl, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · intro hb
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hb
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L') r (hcard ▸ hrL)
    have hxy : (x : Y) * y = y * x := by
      have := mem_centralizer_iff.mp (hb x.2) y (mem_zpowers y)
      exact this.symm
    have hE : zpowers (x : Y) = ⊥ := by
      refine hyr _ (IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx, pow_one])) ?_
      intro z hz
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
      have hc' : Commute y (x : Y) := hxy.symm
      rw [(hc'.zpow_right k).eq, mul_assoc, mul_inv_cancel, mul_one]
      exact zpow_mem (mem_zpowers _) k
    have h1 : (x : Y) = 1 := by
      have := mem_zpowers (x : Y)
      rw [hE, mem_bot] at this
      exact this
    have h2 : orderOf x = 1 := by
      rw [← Subgroup.orderOf_coe, h1, orderOf_one]
    rw [hx] at h2
    exact (Fact.out : r.Prime).one_lt.ne' h2

end CFSG.OddStandard.GH71.S55
