module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5Types

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_of_conj_mem {S N : Subgroup G} (h : ∀ s ∈ S, ∀ y ∈ N, s * y * s⁻¹ ∈ N) :
    S ≤ normalizer (N : Set G) := fun s hs =>
  mem_normalizer_iff.mpr fun y => ⟨fun hy => h s hs y hy, fun hy => by
    have h1 := h s⁻¹ (inv_mem hs) _ hy
    rwa [inv_inv, show s⁻¹ * (s * y * s⁻¹) * s = y by group] at h1⟩

omit [Finite G] in
theorem mem_normalizer_of_conjugate_eq {Q : Subgroup G} {x : G} (h : conjugate Q x = Q) :
    x ∈ normalizer (Q : Set G) :=
  mem_normalizer_iff.mpr fun y => by rw [← mem_conjugate_iff, h]

omit [Finite G] in
theorem orderOf_conj' (x g : G) : orderOf (x * g * x⁻¹) = orderOf g := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

omit [Finite G] in
theorem conjugate_le_of_mem_normalizer {S P : Subgroup G} {x : G}
    (hx : x ∈ normalizer (S : Set G)) (hPS : P ≤ S) : conjugate P x ≤ S := by
  intro y hy
  rw [mem_conjugate_iff] at hy
  exact (mem_normalizer_iff.mp hx y).mpr (hPS hy)

omit [Finite G] in
theorem mem_zpowers_sq_of_odd {x : G} (hodd : Odd (orderOf x)) : x ∈ zpowers (x ^ 2) := by
  obtain ⟨k, hk⟩ := hodd
  refine ⟨(k + 1 : ℤ), ?_⟩
  change (x ^ 2) ^ ((k + 1 : ℕ) : ℤ) = x
  rw [zpow_natCast, ← pow_mul, show 2 * (k + 1) = orderOf x + 1 by omega, pow_succ,
    pow_orderOf_eq_one, one_mul]

omit [Finite G] in
theorem exists_finset_closure_of_conjugate {V : Subgroup G} (g : G) {n : ℕ}
    (hV : ∃ s : Finset G, s.card ≤ n ∧ closure (s : Set G) = conjugate V g) :
    ∃ s : Finset G, s.card ≤ n ∧ closure (s : Set G) = V := by
  classical
  obtain ⟨s, hs, hsV⟩ := hV
  refine ⟨s.image (MulAut.conj g), Finset.card_image_le.trans hs, ?_⟩
  have h1 : closure ((s.image (MulAut.conj g) : Finset G) : Set G) =
      (closure (s : Set G)).map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.map_closure, Finset.coe_image]
    rfl
  rw [h1, hsV, conjugate, Subgroup.map_map]
  convert Subgroup.map_id V using 2
  ext y
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply, MonoidHom.id_apply]
  group

omit [Finite G] in
theorem conj_mem_of_mem_normalizer {S : Subgroup G} {x s : G} (hx : x ∈ normalizer (S : Set G))
    (hs : s ∈ S) : x⁻¹ * s * x ∈ S := by
  have h1 := (mem_normalizer_iff.mp (inv_mem hx) s).mp hs
  rwa [inv_inv] at h1

omit [Finite G] in
theorem sq_not_mem_normalizer {Q : Subgroup G} {x : G} (hxQ : x ∉ normalizer (Q : Set G))
    (hodd : Odd (orderOf x)) : x ^ 2 ∉ normalizer (Q : Set G) := fun h2 =>
  hxQ (zpowers_le.mpr h2 (mem_zpowers_sq_of_odd hodd))

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
include h

theorem conjugate_Q_le {x : G} (hx : x ∈ normalizer (S : Set G)) : conjugate Q x ≤ S :=
  conjugate_le_of_mem_normalizer hx h.QS

theorem inf_conjugate_eq_bot {x : G} (hx : x ∈ normalizer (S : Set G))
    (hxQ : x ∉ normalizer (Q : Set G)) : Q ⊓ conjugate Q x = ⊥ := by
  by_contra hne
  have hN : S ≤ normalizer ((Q ⊓ conjugate Q x : Subgroup G) : Set G) := by
    refine le_normalizer_of_conj_mem fun s hs y hy => mem_inf.mpr ⟨h.conj_mem_Q hs hy.1, ?_⟩
    have hy2 := mem_conjugate_iff.mp (mem_inf.mp hy).2
    rw [mem_conjugate_iff]
    have hxs : x * s * x⁻¹ ∈ S := (mem_normalizer_iff.mp hx s).mp hs
    rw [show x * (s * y * s⁻¹) * x⁻¹ = (x * s * x⁻¹) * (x * y * x⁻¹) * (x * s * x⁻¹)⁻¹ by group]
    exact h.conj_mem_Q hxs hy2
  obtain ⟨u, huN, hu2, huS⟩ :=
    exists_involution_center h.isPGroup_S (inf_le_left.trans h.QS) hN hne
  have huQ : u ∈ Q := (mem_inf.mp huN).1
  have hvQ : x * u * x⁻¹ ∈ Q := mem_conjugate_iff.mp (mem_inf.mp huN).2
  have hv2 : orderOf (x * u * x⁻¹) = 2 := by rw [orderOf_conj', hu2]
  have hvS : ∀ s ∈ S, s * (x * u * x⁻¹) = x * u * x⁻¹ * s := by
    intro s hs
    have h1 := huS _ (conj_mem_of_mem_normalizer hx hs)
    calc s * (x * u * x⁻¹) = x * ((x⁻¹ * s * x) * u) * x⁻¹ := by group
      _ = x * (u * (x⁻¹ * s * x)) * x⁻¹ := by rw [h1]
      _ = x * u * x⁻¹ * s := by group
  have hu := h.repoint huQ hu2 huS
  have hv := h.repoint hvQ hv2 hvS
  have hF : footeF L₀ u = conjugate (footeF L₀ (x * u * x⁻¹)) x := by
    rw [← footeF_conj h.sec4.huniq, show x⁻¹ * (x * u * x⁻¹) * x = u by group]
  have hQx : conjugate Q x ≤ Q := by
    intro y hy
    rw [← hu.inf_coreActionKernel]
    refine mem_inf.mpr ⟨h.conjugate_Q_le hx hy, ?_⟩
    rw [hF]
    exact mem_coreActionKernel_conjugate (hv.Q_le (mem_conjugate_iff.mp hy))
  have heq : conjugate Q x = Q :=
    eq_of_le_of_card_ge hQx (card_conjugate_eq_card Q x).ge
  exact hxQ (mem_normalizer_of_conjugate_eq heq)

theorem commute_of_inf_conjugate_eq_bot {y : G} (hy : y ∈ normalizer (S : Set G))
    (hRy : S ⊓ L ⊓ conjugate (S ⊓ L) y = ⊥) {r a : G} (hr : r ∈ S ⊓ L)
    (ha : a ∈ conjugate (S ⊓ L) y) : a * r = r * a := by
  have haS : a ∈ S := conjugate_le_of_mem_normalizer hy inf_le_left ha
  have h1 : a * r * a⁻¹ * r⁻¹ ∈ S ⊓ L := mul_mem (h.conj_mem_R haS hr) (inv_mem hr)
  have h2 : a * r * a⁻¹ * r⁻¹ ∈ conjugate (S ⊓ L) y := by
    have h3 : r * a⁻¹ * r⁻¹ ∈ conjugate (S ⊓ L) y := by
      rw [mem_conjugate_iff] at ha ⊢
      have hyr : y * r * y⁻¹ ∈ S := (mem_normalizer_iff.mp hy r).mp (mem_inf.mp hr).1
      rw [show y * (r * a⁻¹ * r⁻¹) * y⁻¹ =
        (y * r * y⁻¹) * (y * a * y⁻¹)⁻¹ * (y * r * y⁻¹)⁻¹ by group]
      exact h.conj_mem_R hyr (inv_mem ha)
    rw [show a * r * a⁻¹ * r⁻¹ = a * (r * a⁻¹ * r⁻¹) by group]
    exact mul_mem ha h3
  have h4 : a * r * a⁻¹ * r⁻¹ ∈ S ⊓ L ⊓ conjugate (S ⊓ L) y := mem_inf.mpr ⟨h1, h2⟩
  rw [hRy, mem_bot] at h4
  calc a * r = a * r * a⁻¹ * r⁻¹ * (r * a) := by group
    _ = r * a := by rw [h4, one_mul]

theorem inf_conjugate_R_eq_bot (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) {y : G}
    (hy : y ∈ normalizer (S : Set G)) (hyt : y * t * y⁻¹ ≠ t) :
    S ⊓ L ⊓ conjugate (S ⊓ L) y = ⊥ := by
  by_contra hne
  have hN : S ≤ normalizer ((S ⊓ L ⊓ conjugate (S ⊓ L) y : Subgroup G) : Set G) := by
    refine le_normalizer_of_conj_mem fun s hs w hw => mem_inf.mpr ⟨h.conj_mem_R hs hw.1, ?_⟩
    have hw2 := mem_conjugate_iff.mp (mem_inf.mp hw).2
    rw [mem_conjugate_iff]
    have hys : y * s * y⁻¹ ∈ S := (mem_normalizer_iff.mp hy s).mp hs
    rw [show y * (s * w * s⁻¹) * y⁻¹ = (y * s * y⁻¹) * (y * w * y⁻¹) * (y * s * y⁻¹)⁻¹ by
      group]
    exact h.conj_mem_R hys hw2
  obtain ⟨u, huN, hu2, huS⟩ :=
    exists_involution_center h.isPGroup_S (inf_le_left.trans inf_le_left) hN hne
  have hne1 : ∀ {v : G}, orderOf v = 2 → v ≠ 1 := fun hv h1 => by
    rw [h1, orderOf_one] at hv
    omega
  have huR : u ∈ S ⊓ L := (mem_inf.mp huN).1
  have hut : u = t := by
    rcases h.center_R hna huR (fun r hr => huS r (mem_inf.mp hr).1 |>.symm) with h1 | h1
    · exact absurd h1 (hne1 hu2)
    · exact h1
  have hytR : y * t * y⁻¹ ∈ S ⊓ L := hut ▸ mem_conjugate_iff.mp (mem_inf.mp huN).2
  have hytZ : ∀ r ∈ S ⊓ L, y * t * y⁻¹ * r = r * (y * t * y⁻¹) := by
    intro r hr
    have h1 := h.tZ _ (conj_mem_of_mem_normalizer hy (mem_inf.mp hr).1)
    calc y * t * y⁻¹ * r = y * (t * (y⁻¹ * r * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * r * y) * t) * y⁻¹ := by rw [h1]
      _ = r * (y * t * y⁻¹) := by group
  rcases h.center_R hna hytR hytZ with h1 | h1
  · exact hne1 (by rw [orderOf_conj', h.t2]) h1
  · exact hyt h1

end Sec5

end CFSG.ComponentClassification.Foote5
