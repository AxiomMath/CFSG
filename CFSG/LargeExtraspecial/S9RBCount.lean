module

public import CFSG.LargeExtraspecial.S9RBType
public import CFSG.LargeExtraspecial.S9RBPa
public import CFSG.LargeExtraspecial.S9RAAbs
public import CFSG.LargeExtraspecial.S9TwoB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9.RB

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

section Count

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hA6 : A6Case H C ht ht1 hVQ)
  (hR : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ = t)

include H C ht ht1 hVQ hA6 hR in
theorem IsConjCent.fix_commSpace_of_commute {σ : S.O} (hσ : IsConjCent S t σ) {k : S.O}
    (hk : k ∈ N0bar S g t) (hkσ : k * σ = σ * k) :
    ∀ v ∈ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt), (k : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  intro v hv
  have hfix := hσ.fix_Vt H C ht ht1 hVQ hA6.transitive hR
  have h1 := N0bar_apply_sub_mem_Vt_a6 H C ht ht1 hVQ hA6 hk (commSpace_le_Wt_of_fix hfix hv)
  have h2 : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
    have e : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) =
        (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
          (k : S.Qt ≃ₗ[ZMod 2] S.Qt) w := by
      rw [map_sub, ← coe_mul_apply, hkσ, coe_mul_apply]
    rw [e]
    exact sub_mem (sub_mem_commSpace _ _) (sub_mem_commSpace _ _)
  have h3 : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈
      Vt S g t ⊓ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) := ⟨h1, h2⟩
  rw [hσ.inf_eq_bot H C ht ht1 hVQ hA6.transitive hR, Submodule.mem_bot, sub_eq_zero] at h3
  exact h3

include hCE H hNo C ht ht1 hVQ hA6 hR in
theorem four_mul_card_centralizer_le {σ : S.O} (hσ : IsConjCent S t σ) {k : S.M}
    (hk : S.ρ k ∈ Rbar S g t) :
    4 * Nat.card ↥((S.Lbar ((k : G) * g) ⊓ Nbar S g t) ⊓ (S2.fixGroup
      (commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓
        S.clSub (S.QG ⊓ S.Qa ((k : G) * g)))).comap S.O.subtype) ≤
      Nat.card (S.Lbar ((k : G) * g) ⊓ Nbar S g t : Subgroup S.O) := by
  have hth := mem_Lbar_mul_of_mem_Rbar H ht hk
  have hcard := card_Abar_mul_four_a6 hCE H hNo C ht ht1 hVQ hA6
  have hw := H.two_lt_width
  have hA : Nat.card (S.Lbar ((k : G) * g) ⊓ Nbar S g t : Subgroup S.O) * 8 = 2 ^ S.width := by
    rw [card_Lbar_mul_inf_Nbar H hk]
    obtain ⟨m, hm⟩ : ∃ m, S.width = m + 1 := ⟨S.width - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel] at hcard
    rw [hm, pow_succ, ← hcard]
    ring
  have hV3 := finrank_clSub_inf_Vt (H.mul k) (C.mul k) hth ht1 (not_V_le_Qa_mul H hVQ hk)
  rw [Vt_mul, hA6.finrank_eq] at hV3
  have f := hσ.finrank_commSpace H C ht ht1 hVQ
  rw [hA6.finrank_eq] at f
  have hσ2 := two_le_finrank_commSpace_inf_clSub (H.mul k) (C.mul k) (hσ.mem_Mbar ht)
    (hσ.fix_Vt H C ht ht1 hVQ hA6.transitive hR _ (cl_mem_Vt hth)) f
  exact four_mul_card_le (H.mul k) (C.mul k) hA (by omega) hσ2
    (hσ.inf_eq_bot H C ht ht1 hVQ hA6.transitive hR)

include hCE H hNo C ht ht1 hVQ hA6 hR in
theorem four_le_card_nOrbit_Abar {σ : S.O} (hσ : IsConjCent S t σ) :
    4 ≤ Nat.card (nOrbit (S.Lbar g ⊓ Nbar S g t) σ) := by
  have h4 := four_mul_card_centralizer_le hCE H hNo C ht ht1 hVQ hA6 hR hσ (k := 1)
    (by rw [map_one]; exact one_mem _)
  simp only [OneMemClass.coe_one, one_mul] at h4
  set A := S.Lbar g ⊓ Nbar S g t with hA
  set K := A ⊓ (S2.fixGroup (commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓
    S.clSub (S.QG ⊓ S.Qa g))).comap S.O.subtype with hK
  rw [nat_card_nOrbit]
  have hle : centralizer {σ} ⊓ A ≤ K := by
    rintro k ⟨hkc, hkA⟩
    refine ⟨hkA, S2.mem_fixGroup.mpr fun v hv => ?_⟩
    exact hσ.fix_commSpace_of_commute H C ht ht1 hVQ hA6 hR (Lbar_inf_Nbar_le_N0bar hkA)
      (mem_centralizer_singleton_iff.mp hkc) v hv.1
  have h1 : K.relIndex A ∣ (centralizer {σ}).relIndex A := by
    rw [← Subgroup.inf_relIndex_right (centralizer {σ}) A]
    exact Subgroup.relIndex_dvd_of_le_left A hle
  have h2 := Subgroup.relIndex_mul_card K A
  rw [inf_eq_left.mpr inf_le_left] at h2
  have hpos : 0 < Nat.card K := Nat.card_pos
  have h3 : 4 ≤ K.relIndex A := Nat.le_of_mul_le_mul_right (by rw [h2]; exact h4) hpos
  have h5 : (centralizer {σ}).relIndex A ≠ 0 := Subgroup.index_ne_zero_of_finite
  exact h3.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero h5) h1)

include hCE H hNo C ht ht1 hVQ hA6 hR in
theorem exists_conj_not_mem {σ : S.O} (hσ : IsConjCent S t σ) {h : S.M}
    (hh : S.ρ h ∈ Rbar S g t) (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g) :
    ∃ β ∈ S.Lbar ((h : G) * g) ⊓ Nbar S g t,
      β * σ * β⁻¹ ∉ nOrbit (S.Lbar g ⊓ Nbar S g t) σ := by
  have haQ := H.conj_mem
  have hbQ := conj_mem_QG' S h.2 haQ
  have h4 := four_mul_card_centralizer_le hCE H hNo C ht ht1 hVQ hA6 hR hσ hh
  set B := S.Lbar ((h : G) * g) ⊓ Nbar S g t with hB
  set Kb := B ⊓ (S2.fixGroup (commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓
    S.clSub (S.QG ⊓ S.Qa ((h : G) * g)))).comap S.O.subtype with hKb
  have hne : ¬ B ≤ Kb := by
    intro hle
    have := Subgroup.card_le_of_le hle
    have : 0 < Nat.card B := Nat.card_pos
    omega
  obtain ⟨β, hβB, hβK⟩ := IsConcreteLE.not_le_iff_exists.mp hne
  have hex : ∃ p ∈ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓
      S.clSub (S.QG ⊓ S.Qa ((h : G) * g)), (β : S.Qt ≃ₗ[ZMod 2] S.Qt) p ≠ p := by
    by_contra hcon
    push Not at hcon
    exact hβK ⟨hβB, S2.mem_fixGroup.mpr hcon⟩
  obtain ⟨p, hp, hβp⟩ := hex
  refine ⟨β, hβB, ?_⟩
  rintro ⟨α, hα, hαβ⟩
  have hk : α⁻¹ * β ∈ N0bar S g t :=
    mul_mem (inv_mem (Lbar_inf_Nbar_le_N0bar hα)) (Lbar_mul_inf_Nbar_le_N0bar hh hβB)
  have hkσ : α⁻¹ * β * σ = σ * (α⁻¹ * β) := by
    calc α⁻¹ * β * σ = α⁻¹ * (β * σ * β⁻¹) * β := by group
      _ = α⁻¹ * (α * σ * α⁻¹) * β := by rw [hαβ]
      _ = σ * (α⁻¹ * β) := by group
  have hfixk := hσ.fix_commSpace_of_commute H C ht ht1 hVQ hA6 hR hk hkσ p hp.1
  have hβα : (β : S.Qt ≃ₗ[ZMod 2] S.Qt) p = (α : S.Qt ≃ₗ[ZMod 2] S.Qt) p := by
    have := congrArg (α : S.Qt ≃ₗ[ZMod 2] S.Qt) hfixk
    rwa [coe_mul_apply, apply_inv_apply_O] at this
  have hpW : p ∈ Wt S g t :=
    commSpace_le_Wt_of_fix (hσ.fix_Vt H C ht ht1 hVQ hA6.transitive hR) hp.1
  rcases mem_span_cl_iff.mp (Lbar_apply_sub_mem_span' hbQ hp.2 hβB.1) with h0 | h0
  · exact hβp (sub_eq_zero.mp h0)
  · have h2 := apply_sub_mem_clSub_of_mem_Wt C (cl_a_mem_Vt ht) haQ hpW hα.1
    rw [← hβα, h0] at h2
    exact cl_b_not_mem H hb h2

include hCE H hNo C ht ht1 hVQ hA6 hR in
theorem four_lt_card_nOrbit {σ : S.O} (hσ : IsConjCent S t σ) {h : S.M}
    (hh : S.ρ h ∈ Rbar S g t) (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
    {N : Subgroup S.O} (hAN : S.Lbar g ⊓ Nbar S g t ≤ N)
    (hBN : S.Lbar ((h : G) * g) ⊓ Nbar S g t ≤ N) : 4 < Nat.card (nOrbit N σ) := by
  have h1 := four_le_card_nOrbit_Abar hCE H hNo C ht ht1 hVQ hA6 hR hσ
  obtain ⟨β, hβ, hβn⟩ := exists_conj_not_mem hCE H hNo C ht ht1 hVQ hA6 hR hσ hh hb
  have hsub : nOrbit (S.Lbar g ⊓ Nbar S g t) σ ⊂ nOrbit N σ :=
    ⟨fun x ⟨n, hn, e⟩ => ⟨n, hAN hn, e⟩, fun hle => hβn (hle ⟨β, hBN hβ, rfl⟩)⟩
  have := Set.ncard_lt_ncard hsub (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at this
  omega

end Count

end CFSG.LargeExtraspecial.S9.RB
