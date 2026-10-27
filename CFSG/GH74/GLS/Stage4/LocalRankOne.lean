module

public import CFSG.GH74.GLS.Stage4.LocalSL2

public section

namespace CFSG.GH74.GLS.Stage4

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.SL2
open scoped Pointwise

variable {G : Type} [Group G]

theorem inv_iff_of_inv {H V : Subgroup G} (hV : ∀ h ∈ H, ∀ z ∈ V, h * z * h⁻¹ ∈ V) {h : G}
    (hh : h ∈ H) (z : G) : z ∈ V ↔ h * z * h⁻¹ ∈ V := by
  refine ⟨hV h hh z, fun hz => ?_⟩
  have := hV h⁻¹ (H.inv_mem hh) _ hz
  simpa [mul_assoc] using this

@[expose] def SL2Pair (H : Subgroup G) (r : G) (Ya Yb : Subgroup G) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (p f : ℕ), p.Prime ∧ Nat.card F = p ^ f ∧
    Nat.card Ya = Nat.card F ∧ Nat.card Yb = Nat.card F ∧ Ya ≠ Yb ∧
    Nonempty (↥(Ya ⊔ Yb) ≃* SL2 F) ∧
    ∃ T : Subgroup G, T ≤ H ∧ T ≤ Ya ⊔ Yb ∧ Nat.card T = Nat.card F - 1 ∧
      r ∈ Ya ⊔ Yb ∧ r * r ∈ T ∧ ∀ x ∈ Ya, r * x * r⁻¹ ∈ Yb

@[expose] def SL2Phi (H : Subgroup G) (r : G) (Ya Yb : Subgroup G) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = Nat.card Ya ∧
    ∃ φ : SL2 F →* G, Function.Injective φ ∧ (∀ x, x ∈ Ya ↔ ∃ c, φ (sl2U c) = x) ∧
      (∀ x, x ∈ Yb ↔ ∃ c, φ (sl2L c) = x) ∧ (∀ t : Fˣ, φ (sl2D t) ∈ H) ∧
      ∃ h ∈ H, φ (sl2W F) = r * h

theorem SL2Pair.toSL2Phi {H : Subgroup G} {r : G} {Ya Yb : Subgroup G}
    (hHa : ∀ h ∈ H, ∀ x ∈ Ya, h * x * h⁻¹ ∈ Ya) (hHb : ∀ h ∈ H, ∀ x ∈ Yb, h * x * h⁻¹ ∈ Yb)
    (hP : SL2Pair H r Ya Yb) : SL2Phi H r Ya Yb := by
  obtain ⟨F, hF, hFin, p, f, hp, hcard, hYa, hYb, hne, ⟨e⟩, T, hTH, hTK, hTc, hrK, hrT, hrY⟩ :=
    hP
  set K : Subgroup G := Ya ⊔ Yb with hK
  have hYaK : Ya ≤ K := le_sup_left
  have hYbK : Yb ≤ K := le_sup_right
  have hXc : Nat.card (Ya.subgroupOf K) = Nat.card F := by
    rw [← hYa]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYaK).toEquiv
  have hX'c : Nat.card (Yb.subgroupOf K) = Nat.card F := by
    rw [← hYb]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYbK).toEquiv
  have hXne : Ya.subgroupOf K ≠ Yb.subgroupOf K := by
    intro h
    apply hne
    have h1 := congrArg (Subgroup.map K.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hYaK, Subgroup.map_subgroupOf_eq_of_le hYbK] at h1
  have hTc' : Nat.card (T.subgroupOf K) = Nat.card F - 1 := by
    rw [← hTc]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv
  have hTnorm : T.subgroupOf K ≤ normalizer ((Ya.subgroupOf K : Subgroup K) : Set K) ⊓
      normalizer ((Yb.subgroupOf K : Subgroup K) : Set K) := by
    intro x hx
    have hxT : (x : G) ∈ T := hx
    have hxH : (x : G) ∈ H := hTH hxT
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [mem_normalizer_iff]
      intro y
      exact inv_iff_of_inv hHa hxH (y : G)
    · rw [mem_normalizer_iff]
      intro y
      exact inv_iff_of_inv hHb hxH (y : G)
  have hwT : (⟨r, hrK⟩ : K) * (⟨r, hrK⟩ : K) ∈ T.subgroupOf K := hrT
  have hwX : ∀ x ∈ Ya.subgroupOf K, (⟨r, hrK⟩ : K) * x * (⟨r, hrK⟩ : K)⁻¹ ∈ Yb.subgroupOf K := by
    intro x hx
    exact hrY (x : G) hx
  obtain ⟨φ, hφU, hφL, hφD, t, ht, hφW⟩ := exists_rankOne hp hcard e hXc hX'c hXne hTnorm hTc'
    hwT hwX
  have key : ∀ (Y : Subgroup G) (hYK : Y ≤ K) (S : Subgroup (SL2 F)),
      S.map φ.toMonoidHom = Y.subgroupOf K → ∀ x : G, x ∈ Y ↔ ∃ s ∈ S, (φ s : G) = x := by
    intro Y hYK S hS x
    constructor
    · intro hx
      have hxK : x ∈ K := hYK hx
      have : (⟨x, hxK⟩ : K) ∈ S.map φ.toMonoidHom := by rw [hS]; exact hx
      obtain ⟨s, hs, hsx⟩ := this
      exact ⟨s, hs, congrArg Subtype.val hsx⟩
    · rintro ⟨s, hs, rfl⟩
      have : φ s ∈ S.map φ.toMonoidHom := ⟨s, hs, rfl⟩
      rw [hS] at this
      exact this
  refine ⟨F, hF, hFin, hYa.symm, K.subtype.comp φ.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · exact K.subtype_injective.comp φ.injective
  · intro x
    rw [key Ya hYaK _ hφU x]
    constructor
    · rintro ⟨s, hs, hsx⟩
      obtain ⟨c, rfl⟩ := (mem_upperSub_iff s).1 hs
      exact ⟨c, hsx⟩
    · rintro ⟨c, hc⟩
      exact ⟨sl2U c, (mem_upperSub_iff _).2 ⟨c, rfl⟩, hc⟩
  · intro x
    rw [key Yb hYbK _ hφL x]
    constructor
    · rintro ⟨s, hs, hsx⟩
      obtain ⟨c, rfl⟩ := (mem_lowerSub_iff s).1 hs
      exact ⟨c, hsx⟩
    · rintro ⟨c, hc⟩
      exact ⟨sl2L c, (mem_lowerSub_iff _).2 ⟨c, rfl⟩, hc⟩
  · intro d
    have h1 : φ (sl2D d) ∈ (diagSub F).map φ.toMonoidHom :=
      ⟨sl2D d, (mem_diagSub_iff _).2 ⟨d, rfl⟩, rfl⟩
    rw [hφD] at h1
    exact hTH h1
  · refine ⟨(t : G), hTH ht, ?_⟩
    have := congrArg Subtype.val hφW
    simpa using this


theorem SL2Phi.bruhat {H : Subgroup G} {r : G} {Ya Yb : Subgroup G} (hP : SL2Phi H r Ya Yb)
    (hr : ∀ h ∈ H, r * h * r⁻¹ ∈ H) :
    ∀ y ∈ Yb, y ≠ 1 → y ∈ (Ya : Set G) * (H : Set G) * {r} * (Ya : Set G) := by
  obtain ⟨F, hF, hFin, hc, φ, hinj, hU, hL, hD, h, hh, hW⟩ := hP
  intro y hy hy1
  obtain ⟨c, hc⟩ := (hL y).1 hy
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hy1
    rw [← hc, sl2L_zero, map_one]
  have hxU : φ (sl2U c⁻¹) ∈ Ya := (hU _).2 ⟨c⁻¹, rfl⟩
  have hd : φ (sl2D (Units.mk0 (-c) (neg_ne_zero.2 hc0))) ∈ H := hD _
  have hy' : y = φ (sl2U c⁻¹) * (r * (h * φ (sl2D (Units.mk0 (-c) (neg_ne_zero.2 hc0))))) *
      φ (sl2U c⁻¹) := by
    rw [← hc, sl2L_eq c hc0]
    simp only [map_mul]
    rw [hW]
    group
  have hh' : r * (h * φ (sl2D (Units.mk0 (-c) (neg_ne_zero.2 hc0)))) * r⁻¹ ∈ H :=
    hr _ (H.mul_mem hh hd)
  have e : y = φ (sl2U c⁻¹) * (r * (h * φ (sl2D (Units.mk0 (-c) (neg_ne_zero.2 hc0)))) * r⁻¹) * r *
      φ (sl2U c⁻¹) := by
    rw [hy']; group
  rw [e]
  exact Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul hxU hh') (Set.mem_singleton r)) hxU

theorem SL2Phi.toSL2At {H N : Subgroup G} {r : G} {root : ℤ → Subgroup G} {i : ℤ}
    (hP : SL2Phi H r (root i) (root (-i))) (hrN : r ∈ N) (hHN : H ≤ N) : SL2At H N root i := by
  obtain ⟨F, hF, hFin, hc, φ, hinj, hU, hL, hD, h, hh, hW⟩ := hP
  refine ⟨F, hF, hFin, hc, φ, hinj, hU, hL, hD, ?_⟩
  rw [hW]
  exact N.mul_mem hrN (hHN hh)

end CFSG.GH74.GLS.Stage4
