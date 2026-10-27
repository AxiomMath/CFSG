module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelFacts

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC.BenderCover

open scoped commutatorElement

variable {K : Type*} [Group K]

abbrev centralImage (Q : Subgroup K) : Subgroup (K ⧸ Subgroup.center K) :=
  Q.map (QuotientGroup.mk' (Subgroup.center K))

@[expose] def centerPreimage (Q : Subgroup K) : Subgroup K :=
  (centralImage Q ⊓ Subgroup.centralizer (centralImage Q : Set (K ⧸ Subgroup.center K))).comap
    (QuotientGroup.mk' (Subgroup.center K))

theorem mem_centerPreimage_iff {Q : Subgroup K} {x : K} :
    x ∈ centerPreimage Q ↔ InCenterOf (centralImage Q) (x : K ⧸ Subgroup.center K) := by
  simp only [centerPreimage, Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    InCenterOf, QuotientGroup.mk'_apply]
  rfl

theorem inCenterOf_one {G : Type*} [Group G] (Q : Subgroup G) : InCenterOf Q 1 :=
  ⟨Q.one_mem, fun q _ => Commute.one_right q⟩

theorem inCenterOf_conj {G : Type*} [Group G] {Q : Subgroup G} {d w : G}
    (hd : d ∈ Subgroup.normalizer (Q : Set G)) (hw : InCenterOf Q w) :
    InCenterOf Q (d * w * d⁻¹) := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp hd w).mp hw.1, fun q hq => ?_⟩
  have hq' : d⁻¹ * q * d ∈ Q := by
    rw [Subgroup.mem_normalizer_iff.mp hd]
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using hq
  have h := (hw.2 _ hq').eq
  show q * (d * w * d⁻¹) = d * w * d⁻¹ * q
  calc q * (d * w * d⁻¹) = d * ((d⁻¹ * q * d) * w) * d⁻¹ := by group
    _ = d * (w * (d⁻¹ * q * d)) * d⁻¹ := by rw [h]
    _ = d * w * d⁻¹ * q := by group

variable {Q : Subgroup K}

theorem mk_mem_centralImage_iff (hZQ : Subgroup.center K ≤ Q) {x : K} :
    (x : K ⧸ Subgroup.center K) ∈ centralImage Q ↔ x ∈ Q := by
  change x ∈ (centralImage Q).comap (QuotientGroup.mk' (Subgroup.center K)) ↔ x ∈ Q
  rw [Subgroup.comap_map_eq_self (by rwa [QuotientGroup.ker_mk'])]

theorem mem_normalizer_of_mk_mem (hZQ : Subgroup.center K ≤ Q) {g : K}
    (hg : (g : K ⧸ Subgroup.center K) ∈
      Subgroup.normalizer (centralImage Q : Set (K ⧸ Subgroup.center K))) :
    g ∈ Subgroup.normalizer (Q : Set K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro q
  rw [← mk_mem_centralImage_iff hZQ, ← mk_mem_centralImage_iff hZQ, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  exact Subgroup.mem_normalizer_iff.mp hg _

theorem inCenterOf_mk {x : K} (hx : x ∈ Q) (hc : ∀ q ∈ Q, Commute q x) :
    InCenterOf (centralImage Q) (x : K ⧸ Subgroup.center K) := by
  refine ⟨Subgroup.mem_map_of_mem _ hx, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  exact (hc q hq).map (QuotientGroup.mk' (Subgroup.center K))

section Torus

variable {D : Subgroup (K ⧸ Subgroup.center K)}

theorem centerPreimage_le (hZQ : Subgroup.center K ≤ Q)
    (hDN : D ≤ Subgroup.normalizer (centralImage Q : Set (K ⧸ Subgroup.center K)))
    (htrans : ∀ w w' : K ⧸ Subgroup.center K, InCenterOf (centralImage Q) w → w ≠ 1 →
      InCenterOf (centralImage Q) w' → w' ≠ 1 → ∃ d ∈ D, d⁻¹ * w * d = w')
    {w₀ : K} (hw₀Q : w₀ ∈ Q) (hw₀c : ∀ q ∈ Q, Commute q w₀)
    (hw₀Z : w₀ ∉ Subgroup.center K) {x : K} (hx : x ∈ centerPreimage Q) :
    x ∈ Q ∧ ∀ q ∈ Q, Commute q x := by
  by_cases hx1 : (x : K ⧸ Subgroup.center K) = 1
  · have hxZ := (QuotientGroup.eq_one_iff x).mp hx1
    exact ⟨hZQ hxZ, fun q _ => Subgroup.mem_center_iff.mp hxZ q⟩
  have hw₀1 : (w₀ : K ⧸ Subgroup.center K) ≠ 1 := fun h =>
    hw₀Z ((QuotientGroup.eq_one_iff w₀).mp h)
  obtain ⟨d, hdD, hd⟩ := htrans _ _ (inCenterOf_mk hw₀Q hw₀c) hw₀1
    (mem_centerPreimage_iff.mp hx) hx1
  obtain ⟨g, hgd⟩ : ∃ g : K, (g : K ⧸ Subgroup.center K) = d⁻¹ :=
    ⟨(Quotient.out d)⁻¹, by rw [QuotientGroup.mk_inv, QuotientGroup.out_eq']⟩
  have hgN : g ∈ Subgroup.normalizer (Q : Set K) :=
    mem_normalizer_of_mk_mem hZQ (hgd ▸ hDN (D.inv_mem hdD))
  have hy : InCenterOf Q (g * w₀ * g⁻¹) := inCenterOf_conj hgN ⟨hw₀Q, hw₀c⟩
  have hyx : ((g * w₀ * g⁻¹ : K) : K ⧸ Subgroup.center K) = x := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hgd, inv_inv, hd]
  have hc := QuotientGroup.eq.mp hyx
  have hxe : x = g * w₀ * g⁻¹ * ((g * w₀ * g⁻¹)⁻¹ * x) := by group
  refine ⟨hxe ▸ Q.mul_mem hy.1 (hZQ hc), fun q hq => ?_⟩
  rw [hxe]
  exact (hy.2 q hq).mul_right (Subgroup.mem_center_iff.mp hc q)

theorem mem_center_of_forall_conj_eq
    (htrans : ∀ w w' : K ⧸ Subgroup.center K, InCenterOf (centralImage Q) w → w ≠ 1 →
      InCenterOf (centralImage Q) w' → w' ≠ 1 → ∃ d ∈ D, d⁻¹ * w * d = w')
    (hcard : 4 ≤ Nat.card {w : K ⧸ Subgroup.center K // InCenterOf (centralImage Q) w})
    {x : K} (hx : x ∈ centerPreimage Q)
    (hfix : ∀ d ∈ D, d * (x : K ⧸ Subgroup.center K) * d⁻¹ = x) : x ∈ Subgroup.center K := by
  classical
  by_contra hxZ
  have hx1 : (x : K ⧸ Subgroup.center K) ≠ 1 := fun h =>
    hxZ ((QuotientGroup.eq_one_iff x).mp h)
  have hall : ∀ w : {w : K ⧸ Subgroup.center K // InCenterOf (centralImage Q) w},
      (w : K ⧸ Subgroup.center K) ≠ 1 → (w : K ⧸ Subgroup.center K) = x := by
    intro w hw
    obtain ⟨d, hdD, hd⟩ := htrans _ _ (mem_centerPreimage_iff.mp hx) hx1 w.2 hw
    rw [← hd]
    simpa only [inv_inv] using hfix d⁻¹ (D.inv_mem hdD)
  let f : {w : K ⧸ Subgroup.center K // InCenterOf (centralImage Q) w} → Bool :=
    fun w => decide ((w : K ⧸ Subgroup.center K) = 1)
  have hf : Function.Injective f := by
    intro w w' h
    apply Subtype.ext
    by_cases hw : (w : K ⧸ Subgroup.center K) = 1
    · have hw' : (w' : K ⧸ Subgroup.center K) = 1 := by
        simpa [f, hw] using h
      rw [hw, hw']
    · have hw' : (w' : K ⧸ Subgroup.center K) ≠ 1 := by
        simpa [f, hw] using h
      rw [hall w hw, hall w' hw']
  have h2 := Nat.card_le_card_of_injective f hf
  have hb : Nat.card Bool = 2 := by simp
  omega

end Torus

end CFSG.ProperTwoGeneratedCore.TheoremC.BenderCover
