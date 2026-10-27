module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.Delta
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.Descend

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G] {L A T : Subgroup G} {z t : G} {W : Subgroup G}

@[expose] def E3Facts.deltaRestrict (h2 : E2Facts L A z) (h3 : E3Facts A z W) : W →* A :=
  (deltaHom h2.conj_mem).comp (Subgroup.inclusion h3.le_R₀)

@[simp]
theorem E3Facts.coe_deltaRestrict (h2 : E2Facts L A z) (h3 : E3Facts A z W) (w : W) :
    ((E3Facts.deltaRestrict h2 h3 w : A) : G) = delta z (w : G) :=
  rfl

theorem E3Facts.relIndex_W_R₀ (h2 : E2Facts L A z) (h3 : E3Facts A z W) :
    W.relIndex (R₀ A z) = 2 := by
  have h := Subgroup.relIndex_mul_card (H := W) (K := R₀ A z)
  rw [inf_eq_left.mpr h3.le_R₀, h3.card, h2.card_R₀] at h
  have hpow : (2 : ℕ) ^ 21 = 2 * 2 ^ 20 := by ring
  rw [hpow] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h

theorem E3Facts.deltaRestrict_surjective (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) : Function.Surjective (E3Facts.deltaRestrict h2 h3) := by
  intro a
  obtain ⟨r, hrR, hrd⟩ := h2.exists_delta_eq (G := G) (a := (a : G)) a.2
  by_cases hrW : r ∈ W
  · exact ⟨⟨r, hrW⟩, Subtype.ext hrd⟩
  · have hzR : z ∈ R₀ A z :=
      h.B_le_R₀ (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
    have hz1 : delta z z = 1 := by
      rw [delta]
      group
    have hzinv1 : delta z z⁻¹ = 1 := by
      rw [h.z_inv]
      exact hz1
    have hrel : W.relIndex (R₀ A z) = 2 := E3Facts.relIndex_W_R₀ h2 h3
    have hsub : (W.subgroupOf (R₀ A z)).index = 2 := by
      simpa [Subgroup.relIndex] using hrel
    have hzinvW : z⁻¹ ∉ W := by
      intro hmem
      exact h3.z_not_mem (by simpa using W.inv_mem hmem)
    let zK : R₀ A z := ⟨z⁻¹, (R₀ A z).inv_mem hzR⟩
    let rK : R₀ A z := ⟨r, hrR⟩
    have hzKnot : zK ∉ W.subgroupOf (R₀ A z) := by
      simpa [zK, Subgroup.mem_subgroupOf] using hzinvW
    have hrKnot : rK ∉ W.subgroupOf (R₀ A z) := by
      simpa [rK, Subgroup.mem_subgroupOf] using hrW
    have hprod : zK * rK ∈ W.subgroupOf (R₀ A z) := by
      rw [Subgroup.mul_mem_iff_of_index_two hsub]
      exact iff_of_false hzKnot hrKnot
    refine ⟨⟨((zK * rK : R₀ A z) : G), by simpa [Subgroup.mem_subgroupOf] using hprod⟩, ?_⟩
    apply Subtype.ext
    show delta z (((zK * rK : R₀ A z) : G)) = (a : G)
    show delta z (z⁻¹ * r) = (a : G)
    rw [h2.delta_mul ((R₀ A z).inv_mem hzR) hrR, hzinv1, one_mul, hrd]

theorem E3Facts.deltaRestrict_ker (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) : (E3Facts.deltaRestrict h2 h3).ker = A.subgroupOf W := by
  have hsurj := E3Facts.deltaRestrict_surjective (W := W) h h2 h3
  have hrange : (E3Facts.deltaRestrict h2 h3).range = ⊤ :=
    MonoidHom.range_eq_top.mpr hsurj
  have hcardRange : Nat.card (E3Facts.deltaRestrict h2 h3).range = 2 ^ 10 := by
    rw [hrange, Subgroup.card_top, h.jc.module.card]
  have hcardKer : Nat.card (E3Facts.deltaRestrict h2 h3).ker = 2 ^ 10 := by
    have h := Subgroup.card_ker_mul_card_range (E3Facts.deltaRestrict h2 h3)
    rw [h3.card, hcardRange] at h
    have hpow : (2 : ℕ) ^ 20 = 2 ^ 10 * 2 ^ 10 := by ring
    rw [hpow] at h
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h
  have hAle : A.subgroupOf W ≤ (E3Facts.deltaRestrict h2 h3).ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    have hxG : (x : G) ∈ A := by simpa [Subgroup.mem_subgroupOf] using hx
    have hxL : (x : G) ∈ L := h.jc.le hxG
    have hcomm : (x : G) * z = z * (x : G) := h.commute_of_mem hxL
    show delta z (x : G) = 1
    rw [delta, hcomm]
    group
  have hcardSub : Nat.card (A.subgroupOf W) = 2 ^ 10 := by
    calc Nat.card (A.subgroupOf W) = Nat.card A :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe h3.A_le).toEquiv
      _ = 2 ^ 10 := h.jc.module.card
  have hEq : A.subgroupOf W = (E3Facts.deltaRestrict h2 h3).ker := by
    refine Subgroup.eq_of_le_of_card_ge hAle ?_
    rw [hcardKer, hcardSub]
  exact hEq.symm

theorem E3Facts.deltaRestrict_eq_one_iff (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (w : W) :
    E3Facts.deltaRestrict h2 h3 w = 1 ↔ (w : G) ∈ A := by
  have hker := E3Facts.deltaRestrict_ker (W := W) h h2 h3
  rw [← Subgroup.mem_subgroupOf (H := A) (K := W), ← hker, MonoidHom.mem_ker]

noncomputable def E3Facts.deltaSection (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (a : A) : W :=
  Classical.choose (E3Facts.deltaRestrict_surjective (W := W) h h2 h3 a)

theorem E3Facts.deltaSection_spec (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (a : A) :
    E3Facts.deltaRestrict h2 h3 (E3Facts.deltaSection h h2 h3 a) = a :=
  Classical.choose_spec (E3Facts.deltaRestrict_surjective (W := W) h h2 h3 a)

theorem E3Facts.deltaSection_val (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (a : A) :
    delta z (((E3Facts.deltaSection h h2 h3 a : W) : G)) = (a : G) :=
  congrArg Subtype.val (E3Facts.deltaSection_spec (W := W) h h2 h3 a)

theorem Hyp.A_mul_comm (h : Hyp G L A T z t) {a b : G} (ha : a ∈ A) (hb : b ∈ A) :
    a * b = b * a := by
  haveI : IsMulCommutative A := h.jc.module.elemAb.toIsMulCommutative
  exact Subgroup.mul_comm_of_mem_isMulCommutative (H := A) ha hb

theorem E3Facts.A_commute_W (h3 : E3Facts A z W) {a w : G} (ha : a ∈ A) (hw : w ∈ W) :
    a * w = w * a :=
  Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (h3.le_R₀ hw)).2 a ha

theorem E3Facts.commutator_mem_W (h3 : E3Facts A z W) {v w : W} :
    ⁅(v : G), (w : G)⁆ ∈ A := by
  simpa [commutatorElement_def] using h3.commutator_mem (v : G) v.2 (w : G) w.2

private theorem commutator_left_of_commute (s t ω : G) (h : ω * t = t * ω) :
    ⁅s * ω, t⁆ = ⁅s, t⁆ := by
  have h' : ω * t * ω⁻¹ = t := by rw [h, mul_inv_cancel_right]
  calc
    ⁅s * ω, t⁆ = s * (ω * t * ω⁻¹) * s⁻¹ * t⁻¹ := by
      rw [commutatorElement_def]
      group
    _ = ⁅s, t⁆ := by rw [h', commutatorElement_def]

private theorem commutator_right_of_commute (s t ω : G) (h : ω * s = s * ω) :
    ⁅s, t * ω⁆ = ⁅s, t⁆ := by
  rw [← commutatorElement_inv (t * ω) s, commutator_left_of_commute t s ω h,
    commutatorElement_inv]

private theorem wedge_commutator_mul_left (h : Hyp G L A T z t) (h3 : E3Facts A z W)
    {v v' u : W} :
    ⁅((v * v' : W) : G), (u : G)⁆ = ⁅(v : G), (u : G)⁆ * ⁅(v' : G), (u : G)⁆ := by
  change ⁅(v : G) * (v' : G), (u : G)⁆ = ⁅(v : G), (u : G)⁆ * ⁅(v' : G), (u : G)⁆
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hcA : ⁅(v' : G), (u : G)⁆ ∈ A := E3Facts.commutator_mem_W h3
  have hconj : (v : G) * ⁅(v' : G), (u : G)⁆ * (v : G)⁻¹ = ⁅(v' : G), (u : G)⁆ := by
    rw [(E3Facts.A_commute_W h3 hcA v.2).symm, mul_assoc, mul_inv_cancel, mul_one]
  rw [hconj]
  exact Hyp.A_mul_comm h hcA (E3Facts.commutator_mem_W h3)

private theorem wedge_commutator_mul_right (h3 : E3Facts A z W) {u v v' : W} :
    ⁅(u : G), ((v * v' : W) : G)⁆ = ⁅(u : G), (v : G)⁆ * ⁅(u : G), (v' : G)⁆ := by
  change ⁅(u : G), (v : G) * (v' : G)⁆ = ⁅(u : G), (v : G)⁆ * ⁅(u : G), (v' : G)⁆
  rw [commutatorElement_mul_right_eq_mul_conj]
  have hcA : ⁅(u : G), (v' : G)⁆ ∈ A := E3Facts.commutator_mem_W h3
  have hconj : (v : G) * ⁅(u : G), (v' : G)⁆ * (v : G)⁻¹ = ⁅(u : G), (v' : G)⁆ := by
    rw [(E3Facts.A_commute_W h3 hcA v.2).symm, mul_assoc, mul_inv_cancel, mul_one]
  calc
    ⁅(u : G), (v : G)⁆ * (v : G) * ⁅(u : G), (v' : G)⁆ * (v : G)⁻¹
        = ⁅(u : G), (v : G)⁆ * ((v : G) * ⁅(u : G), (v' : G)⁆ * (v : G)⁻¹) := by
          simp only [mul_assoc]
    _ = ⁅(u : G), (v : G)⁆ * ⁅(u : G), (v' : G)⁆ := by rw [hconj]

private theorem wedge_commutator_eq_of_delta_eq_left (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) {c c' u : W}
    (hδ : E3Facts.deltaRestrict h2 h3 c = E3Facts.deltaRestrict h2 h3 c') :
    ⁅(c' : G), (u : G)⁆ = ⁅(c : G), (u : G)⁆ := by
  have hmem : c⁻¹ * c' ∈ (E3Facts.deltaRestrict h2 h3).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hδ, inv_mul_cancel]
  rw [E3Facts.deltaRestrict_ker h h2 h3] at hmem
  have hdA : (((c⁻¹ * c' : W) : G)) ∈ A := by
    simpa [Subgroup.mem_subgroupOf] using hmem
  have hdu : (((c⁻¹ * c' : W) : G)) * (u : G) = (u : G) * (((c⁻¹ * c' : W) : G)) :=
    E3Facts.A_commute_W h3 hdA u.2
  have hc'eq : (c' : G) = (c : G) * (((c⁻¹ * c' : W) : G)) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  calc
    ⁅(c' : G), (u : G)⁆ = ⁅(c : G) * (((c⁻¹ * c' : W) : G)), (u : G)⁆ := by rw [hc'eq]
    _ = ⁅(c : G), (u : G)⁆ := commutator_left_of_commute (c : G) (u : G) _ hdu

private theorem wedge_commutator_eq_of_delta_eq_right (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) {c u u' : W}
    (hδ : E3Facts.deltaRestrict h2 h3 u = E3Facts.deltaRestrict h2 h3 u') :
    ⁅(c : G), (u' : G)⁆ = ⁅(c : G), (u : G)⁆ := by
  have hmem : u⁻¹ * u' ∈ (E3Facts.deltaRestrict h2 h3).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hδ, inv_mul_cancel]
  rw [E3Facts.deltaRestrict_ker h h2 h3] at hmem
  have hdA : (((u⁻¹ * u' : W) : G)) ∈ A := by
    simpa [Subgroup.mem_subgroupOf] using hmem
  have hdc : (((u⁻¹ * u' : W) : G)) * (c : G) = (c : G) * (((u⁻¹ * u' : W) : G)) :=
    E3Facts.A_commute_W h3 hdA c.2
  have hu'eq : (u' : G) = (u : G) * (((u⁻¹ * u' : W) : G)) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  calc
    ⁅(c : G), (u' : G)⁆ = ⁅(c : G), (u : G) * (((u⁻¹ * u' : W) : G))⁆ := by rw [hu'eq]
    _ = ⁅(c : G), (u : G)⁆ := commutator_right_of_commute (c : G) (u : G) _ hdc

private noncomputable def wedgeForm (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (a b : A) : A :=
  ⟨⁅((E3Facts.deltaSection h h2 h3 a : W) : G),
    ((E3Facts.deltaSection h h2 h3 b : W) : G)⁆,
    E3Facts.commutator_mem_W h3⟩

private theorem wedgeForm_mul_left (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (a b c : A) :
    wedgeForm h h2 h3 (a * b) c = wedgeForm h h2 h3 a c * wedgeForm h h2 h3 b c := by
  apply Subtype.ext
  have hδ : E3Facts.deltaRestrict h2 h3 (E3Facts.deltaSection h h2 h3 (a * b)) =
      E3Facts.deltaRestrict h2 h3
        (E3Facts.deltaSection h h2 h3 a * E3Facts.deltaSection h h2 h3 b) := by
    rw [map_mul, E3Facts.deltaSection_spec, E3Facts.deltaSection_spec,
      E3Facts.deltaSection_spec]
  calc
    ⁅((E3Facts.deltaSection h h2 h3 (a * b) : W) : G),
        ((E3Facts.deltaSection h h2 h3 c : W) : G)⁆
        = ⁅((E3Facts.deltaSection h h2 h3 a * E3Facts.deltaSection h h2 h3 b : W) : G),
            ((E3Facts.deltaSection h h2 h3 c : W) : G)⁆ :=
          wedge_commutator_eq_of_delta_eq_left h h2 h3 hδ.symm
    _ = ⁅((E3Facts.deltaSection h h2 h3 a : W) : G),
          ((E3Facts.deltaSection h h2 h3 c : W) : G)⁆ *
        ⁅((E3Facts.deltaSection h h2 h3 b : W) : G),
          ((E3Facts.deltaSection h h2 h3 c : W) : G)⁆ :=
          wedge_commutator_mul_left h h3

private theorem wedgeForm_mul_right (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (a b c : A) :
    wedgeForm h h2 h3 a (b * c) = wedgeForm h h2 h3 a b * wedgeForm h h2 h3 a c := by
  apply Subtype.ext
  have hδ : E3Facts.deltaRestrict h2 h3 (E3Facts.deltaSection h h2 h3 (b * c)) =
      E3Facts.deltaRestrict h2 h3
        (E3Facts.deltaSection h h2 h3 b * E3Facts.deltaSection h h2 h3 c) := by
    rw [map_mul, E3Facts.deltaSection_spec, E3Facts.deltaSection_spec,
      E3Facts.deltaSection_spec]
  calc
    ⁅((E3Facts.deltaSection h h2 h3 a : W) : G),
        ((E3Facts.deltaSection h h2 h3 (b * c) : W) : G)⁆
        = ⁅((E3Facts.deltaSection h h2 h3 a : W) : G),
            ((E3Facts.deltaSection h h2 h3 b * E3Facts.deltaSection h h2 h3 c : W) : G)⁆ :=
          wedge_commutator_eq_of_delta_eq_right h h2 h3 hδ.symm
    _ = ⁅((E3Facts.deltaSection h h2 h3 a : W) : G),
          ((E3Facts.deltaSection h h2 h3 b : W) : G)⁆ *
        ⁅((E3Facts.deltaSection h h2 h3 a : W) : G),
          ((E3Facts.deltaSection h h2 h3 c : W) : G)⁆ :=
          wedge_commutator_mul_right h3

private theorem wedgeForm_self (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (a : A) : wedgeForm h h2 h3 a a = 1 := by
  apply Subtype.ext
  simp [wedgeForm]

private theorem wedgeForm_equivariant (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (g : MulAut A) (hg : g ∈ autImage L A) (a b : A) :
    wedgeForm h h2 h3 (g a) (g b) = g (wedgeForm h h2 h3 a b) := by
  obtain ⟨x, hx⟩ := exists_toAutImage_eq (L := L) (A := A) ⟨g, hg⟩
  have hxval : (toAutImage x : MulAut A) = g := congrArg Subtype.val hx
  have hxL : (x : G) ∈ L := x.2.1
  have hxNorm : (x : G) ∈ normalizer (A : Set G) := x.2.2
  have hxM : (x : G) ∈ M A z := h.le_M ⟨hxL, hxNorm⟩
  have hxN : (x : G) ∈ normalizer (W : Set G) := h3.M_le hxM
  have hxW : ∀ w : W, (x : G) * (w : G) * (x : G)⁻¹ ∈ W := by
    intro w
    exact (Subgroup.mem_normalizer_iff.mp hxN (w : G)).mp w.2
  let v : W := E3Facts.deltaSection h h2 h3 a
  let w : W := E3Facts.deltaSection h h2 h3 b
  let xv : W := ⟨(x : G) * (v : G) * (x : G)⁻¹, hxW v⟩
  let xw : W := ⟨(x : G) * (w : G) * (x : G)⁻¹, hxW w⟩
  have hg_apply : ∀ c : A, ((g c : A) : G) = (x : G) * (c : G) * (x : G)⁻¹ := by
    intro c
    rw [← hxval]
    exact conjN_apply x c
  have hδv : E3Facts.deltaRestrict h2 h3 xv = g a := by
    apply Subtype.ext
    show delta z ((x : G) * (v : G) * (x : G)⁻¹) = ((g a : A) : G)
    rw [h.delta_conj hxL, E3Facts.deltaSection_val, hg_apply]
  have hδw : E3Facts.deltaRestrict h2 h3 xw = g b := by
    apply Subtype.ext
    show delta z ((x : G) * (w : G) * (x : G)⁻¹) = ((g b : A) : G)
    rw [h.delta_conj hxL, E3Facts.deltaSection_val, hg_apply]
  have hδv' : E3Facts.deltaRestrict h2 h3 (E3Facts.deltaSection h h2 h3 (g a)) =
      E3Facts.deltaRestrict h2 h3 xv :=
    (E3Facts.deltaSection_spec h h2 h3 (g a)).trans hδv.symm
  have hδw' : E3Facts.deltaRestrict h2 h3 (E3Facts.deltaSection h h2 h3 (g b)) =
      E3Facts.deltaRestrict h2 h3 xw :=
    (E3Facts.deltaSection_spec h h2 h3 (g b)).trans hδw.symm
  apply Subtype.ext
  have h1 : ⁅(xv : G), (xw : G)⁆ =
      ⁅(E3Facts.deltaSection h h2 h3 (g a) : G),
        (E3Facts.deltaSection h h2 h3 (g b) : G)⁆ := by
    calc
      ⁅(xv : G), (xw : G)⁆ =
          ⁅(E3Facts.deltaSection h h2 h3 (g a) : G), (xw : G)⁆ :=
            wedge_commutator_eq_of_delta_eq_left h h2 h3
              (c := E3Facts.deltaSection h h2 h3 (g a)) (c' := xv)
              (u := xw) hδv'
      _ = ⁅(E3Facts.deltaSection h h2 h3 (g a) : G),
            (E3Facts.deltaSection h h2 h3 (g b) : G)⁆ :=
            wedge_commutator_eq_of_delta_eq_right h h2 h3
              (c := E3Facts.deltaSection h h2 h3 (g a))
              (u := E3Facts.deltaSection h h2 h3 (g b)) (u' := xw) hδw'
  calc
    ⁅((E3Facts.deltaSection h h2 h3 (g a) : W) : G),
        ((E3Facts.deltaSection h h2 h3 (g b) : W) : G)⁆
        = ⁅(xv : G), (xw : G)⁆ := h1.symm
    _ = (x : G) * ⁅(v : G), (w : G)⁆ * (x : G)⁻¹ :=
          (conjugate_commutatorElement (v : G) (w : G) (x : G)).symm
    _ = ((g (wedgeForm h h2 h3 a b) : A) : G) := by
          rw [hg_apply]
          rfl

private theorem wedgeForm_trivial (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (a b : A) : wedgeForm h h2 h3 a b = 1 :=
  h.jc.module.noWedge (wedgeForm h h2 h3) (wedgeForm_mul_left h h2 h3)
    (wedgeForm_mul_right h h2 h3) (wedgeForm_self h h2 h3)
    (fun g hg a b => wedgeForm_equivariant h h2 h3 g hg a b) a b

theorem Hyp.commute_of_e3Facts (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    {W : Subgroup G} (h3 : E3Facts A z W) : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v := by
  intro v hv w hw
  let vW : W := ⟨v, hv⟩
  let wW : W := ⟨w, hw⟩
  have hβ := wedgeForm_trivial h h2 h3 (E3Facts.deltaRestrict h2 h3 vW)
    (E3Facts.deltaRestrict h2 h3 wW)
  have hβval : ⁅((E3Facts.deltaSection h h2 h3 (E3Facts.deltaRestrict h2 h3 vW) : W) : G),
      ((E3Facts.deltaSection h h2 h3 (E3Facts.deltaRestrict h2 h3 wW) : W) : G)⁆ = 1 :=
    congrArg Subtype.val hβ
  have h1 : ⁅((E3Facts.deltaSection h h2 h3 (E3Facts.deltaRestrict h2 h3 vW) : W) : G),
      ((E3Facts.deltaSection h h2 h3 (E3Facts.deltaRestrict h2 h3 wW) : W) : G)⁆ =
      ⁅(vW : G), ((E3Facts.deltaSection h h2 h3 (E3Facts.deltaRestrict h2 h3 wW) : W) : G)⁆ :=
    wedge_commutator_eq_of_delta_eq_left h h2 h3
      (c := vW) (c' := E3Facts.deltaSection h h2 h3 (E3Facts.deltaRestrict h2 h3 vW))
      (u := E3Facts.deltaSection h h2 h3 (E3Facts.deltaRestrict h2 h3 wW))
      (E3Facts.deltaSection_spec h h2 h3 (E3Facts.deltaRestrict h2 h3 vW)).symm
  have h2' : ⁅(vW : G),
      ((E3Facts.deltaSection h h2 h3 (E3Facts.deltaRestrict h2 h3 wW) : W) : G)⁆ =
      ⁅(vW : G), (wW : G)⁆ :=
    wedge_commutator_eq_of_delta_eq_right h h2 h3
      (c := vW) (u := wW)
      (u' := E3Facts.deltaSection h h2 h3 (E3Facts.deltaRestrict h2 h3 wW))
      (E3Facts.deltaSection_spec h h2 h3 (E3Facts.deltaRestrict h2 h3 wW)).symm
  have hcomm : ⁅(vW : G), (wW : G)⁆ = 1 := by
    rw [← h2', ← h1]
    exact hβval
  exact commutatorElement_eq_one_iff_mul_comm.mp hcomm

private def squareHom (h3 : E3Facts A z W)
    (hcomm : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v) : W →* A where
  toFun w := ⟨(w : G) * (w : G), h3.mul_self_mem (w : G) w.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' v w := by
    apply Subtype.ext
    have hvw : (v : G) * (w : G) = (w : G) * (v : G) := hcomm (v : G) v.2 (w : G) w.2
    change (v : G) * (w : G) * ((v : G) * (w : G)) =
      (v : G) * (v : G) * ((w : G) * (w : G))
    calc
      (v : G) * (w : G) * ((v : G) * (w : G)) =
          (v : G) * ((w : G) * (v : G)) * (w : G) := by group
      _ = (v : G) * ((v : G) * (w : G)) * (w : G) := by rw [← hvw]
      _ = (v : G) * (v : G) * ((w : G) * (w : G)) := by group

private theorem squareHom_ker_le (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hcomm : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v) :
    (E3Facts.deltaRestrict h2 h3).ker ≤ (squareHom h3 hcomm).ker := by
  intro w hw
  rw [MonoidHom.mem_ker] at hw ⊢
  have hwA : (w : G) ∈ A := (E3Facts.deltaRestrict_eq_one_iff h h2 h3 w).mp hw
  apply Subtype.ext
  haveI : IsElementaryAbelian 2 A := h.jc.module.elemAb
  simpa [squareHom, pow_two] using
    elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) (w : G) hwA

private noncomputable def sigma (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hcomm : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v) : A →* A :=
  MonoidHom.liftOfRightInverse (f := E3Facts.deltaRestrict h2 h3)
    (f_inv := E3Facts.deltaSection h h2 h3)
    (hf := E3Facts.deltaSection_spec h h2 h3)
    ⟨squareHom h3 hcomm, squareHom_ker_le h h2 h3 hcomm⟩

private theorem sigma_delta (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hcomm : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v) (w : W) :
    sigma h h2 h3 hcomm (E3Facts.deltaRestrict h2 h3 w) = squareHom h3 hcomm w :=
  MonoidHom.liftOfRightInverse_comp_apply
    (f := E3Facts.deltaRestrict h2 h3)
    (f_inv := E3Facts.deltaSection h h2 h3)
    (hf := E3Facts.deltaSection_spec h h2 h3)
    (g := ⟨squareHom h3 hcomm, squareHom_ker_le h h2 h3 hcomm⟩) (x := w)

private theorem sigma_equivariant (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hcomm : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v)
    (g : MulAut A) (hg : g ∈ autImage L A) (a : A) :
    sigma h h2 h3 hcomm (g a) = g (sigma h h2 h3 hcomm a) := by
  obtain ⟨x, hx⟩ := exists_toAutImage_eq (L := L) (A := A) ⟨g, hg⟩
  have hxval : (toAutImage x : MulAut A) = g := congrArg Subtype.val hx
  let v : W := E3Facts.deltaSection h h2 h3 a
  have hxL : (x : G) ∈ L := x.2.1
  have hxM : (x : G) ∈ M A z := h.le_M x.2
  have hxN : (x : G) ∈ normalizer (W : Set G) := h3.M_le hxM
  have hxW : (x : G) * (v : G) * (x : G)⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp hxN (v : G)).mp v.2
  let xv : W := ⟨(x : G) * (v : G) * (x : G)⁻¹, hxW⟩
  have hg_apply : ∀ c : A, ((g c : A) : G) = (x : G) * (c : G) * (x : G)⁻¹ := by
    intro c
    rw [← hxval]
    exact conjN_apply x c
  have hδ : E3Facts.deltaRestrict h2 h3 xv = g a := by
    apply Subtype.ext
    show delta z ((x : G) * (v : G) * (x : G)⁻¹) = ((g a : A) : G)
    rw [h.delta_conj hxL, E3Facts.deltaSection_val, hg_apply]
  have hσa : sigma h h2 h3 hcomm a = squareHom h3 hcomm v := by
    rw [← E3Facts.deltaSection_spec h h2 h3 a]
    exact sigma_delta h h2 h3 hcomm v
  calc
    sigma h h2 h3 hcomm (g a) = sigma h h2 h3 hcomm (E3Facts.deltaRestrict h2 h3 xv) := by
      rw [hδ]
    _ = squareHom h3 hcomm xv := sigma_delta h h2 h3 hcomm xv
    _ = g (squareHom h3 hcomm v) := by
      apply Subtype.ext
      change ((x : G) * (v : G) * (x : G)⁻¹) *
          ((x : G) * (v : G) * (x : G)⁻¹) = ((g (squareHom h3 hcomm v) : A) : G)
      rw [hg_apply]
      rw [show ((squareHom h3 hcomm v : A) : G) = (v : G) * (v : G) from rfl]
      group
    _ = g (sigma h h2 h3 hcomm a) := by rw [hσa]

private theorem sigma_comm_derived (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hcomm : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v) :
    ∀ g ∈ ⁅autImage L A, autImage L A⁆, ∀ a : A,
      sigma h h2 h3 hcomm (g a) = g (sigma h h2 h3 hcomm a) := by
  let C : Subgroup (MulAut A) :=
    { carrier := {g | ∀ a : A, sigma h h2 h3 hcomm (g a) = g (sigma h h2 h3 hcomm a)}
      one_mem' := by
        intro a
        simp
      mul_mem' := by
        intro g k gC kC a
        show sigma h h2 h3 hcomm ((g * k) a) = (g * k) (sigma h h2 h3 hcomm a)
        calc
          sigma h h2 h3 hcomm ((g * k) a) = sigma h h2 h3 hcomm (g (k a)) := rfl
          _ = g (sigma h h2 h3 hcomm (k a)) := gC (k a)
          _ = g (k (sigma h h2 h3 hcomm a)) := by rw [kC a]
          _ = (g * k) (sigma h h2 h3 hcomm a) := rfl
      inv_mem' := by
        intro g gC a
        have h1 : sigma h h2 h3 hcomm a = g (sigma h h2 h3 hcomm (g⁻¹ a)) := by
          simpa using gC (g⁻¹ a)
        calc
          sigma h h2 h3 hcomm (g⁻¹ a) = g⁻¹ (g (sigma h h2 h3 hcomm (g⁻¹ a))) := by simp
          _ = g⁻¹ (sigma h h2 h3 hcomm a) := by rw [← h1] }
  have hQ : autImage L A ≤ C := by
    intro g hg
    exact sigma_equivariant h h2 h3 hcomm g hg
  have hder : ⁅autImage L A, autImage L A⁆ ≤ C := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    have hgC : g ∈ C := hQ hg
    have hhC : h ∈ C := hQ hh
    simpa [commutatorElement_def] using
      C.mul_mem (C.mul_mem (C.mul_mem hgC hhC) (C.inv_mem hgC)) (C.inv_mem hhC)
  intro g hg a
  exact hder hg a

theorem Hyp.isElementaryAbelian_of_e3Facts (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    {W : Subgroup G} (h3 : E3Facts A z W) : IsElementaryAbelian 2 W := by
  classical
  have hcomm : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v := Hyp.commute_of_e3Facts h h2 h3
  letI : IsMulCommutative W :=
    IsMulCommutative.of_setLike_mul_comm (fun v hv w hw => hcomm v hv w hw)
  have hNle : L ⊓ normalizer (A : Set G) ≤ Subgroup.normalizer (W : Set G) := by
    intro x hx
    exact h3.M_le (h.le_M hx)
  let ρ0 : ↥(L ⊓ normalizer (A : Set G)) →* MulAut W :=
    (Subgroup.normalizerMonoidHom (H := W)).comp (Subgroup.inclusion hNle)
  have hρ0_apply : ∀ (x : ↥(L ⊓ normalizer (A : Set G))) (w : W),
      ((ρ0 x) w : G) = (x : G) * (w : G) * (x : G)⁻¹ := by
    intro x w
    simp [ρ0]
  have hρ0_ker : ∀ x, conjN L A x = 1 → ρ0 x = 1 := by
    intro x hx
    have hxA : (x : G) ∈ A := (conjN_eq_one_iff h.jc.centralizer_eq x).mp hx
    ext w
    change ((ρ0 x) w : G) = (w : G)
    rw [hρ0_apply, E3Facts.A_commute_W h3 hxA w.2]
    group
  let ρ : ↥(autImage L A) →* MulAut W := descendHom ρ0 hρ0_ker
  have hρ_conj : ∀ (x : ↥(L ⊓ normalizer (A : Set G))) (w : W),
      ((ρ (toAutImage x)) w : G) = (x : G) * (w : G) * (x : G)⁻¹ := by
    intro x w
    rw [descendHom_toAutImage]
    exact hρ0_apply x w
  have hρ_equiv : ∀ (g : ↥(autImage L A)) (a : A),
      ρ g (Subgroup.inclusion h3.A_le a) =
        Subgroup.inclusion h3.A_le ((g : MulAut A) a) := by
    intro g a
    obtain ⟨x, hx⟩ := exists_toAutImage_eq (L := L) (A := A) g
    apply Subtype.ext
    rw [← hx, hρ_conj]
    exact (conjN_apply x a).symm
  rcases h.jc.module.endo_derived (sigma h h2 h3 hcomm) (sigma_comm_derived h h2 h3 hcomm) with
    hσ1 | hσid
  · have hsq : ∀ w : W, w * w = 1 := by
      intro w
      have h := sigma_delta h h2 h3 hcomm w
      rw [hσ1] at h
      have h' : squareHom h3 hcomm w = 1 := h.symm
      apply Subtype.ext
      simpa [squareHom] using congrArg Subtype.val h'
    refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
    · exact IsMulCommutative.of_setLike_mul_comm (fun v hv w hw => hcomm v hv w hw)
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
      intro w
      simpa [pow_two] using hsq w
  · exfalso
    have hsq_eq : ∀ w : W, squareHom h3 hcomm w = E3Facts.deltaRestrict h2 h3 w := by
      intro w
      have h := sigma_delta h h2 h3 hcomm w
      rw [hσid] at h
      simpa using h.symm
    have hsq : ∀ v : W, ∃ a : A, v ^ 2 = Subgroup.inclusion h3.A_le a := by
      intro v
      refine ⟨squareHom h3 hcomm v, ?_⟩
      apply Subtype.ext
      simp [pow_two, squareHom]
    have hsq1 : ∀ v : W, v ^ 2 = 1 → ∃ a : A, v = Subgroup.inclusion h3.A_le a := by
      intro v hv
      have hvA : squareHom h3 hcomm v = 1 := by
        apply Subtype.ext
        have hv' : (v : G) * (v : G) = 1 := by
          simpa [pow_two] using congrArg Subtype.val hv
        simpa [squareHom] using hv'
      have hδ1 : E3Facts.deltaRestrict h2 h3 v = 1 := by
        rw [← hsq_eq]
        exact hvA
      have hvmem : (v : G) ∈ A :=
        (E3Facts.deltaRestrict_eq_one_iff h h2 h3 v).mp hδ1
      exact ⟨⟨(v : G), hvmem⟩, rfl⟩
    have hsq_surj : ∀ a : A, ∃ v : W, v ^ 2 = Subgroup.inclusion h3.A_le a := by
      intro a
      obtain ⟨v, hv⟩ := E3Facts.deltaRestrict_surjective (W := W) h h2 h3 a
      refine ⟨v, ?_⟩
      apply Subtype.ext
      have hval : squareHom h3 hcomm v = a := by
        rw [hsq_eq, hv]
      simpa [pow_two, squareHom] using congrArg Subtype.val hval
    exact (h.jc.module.noZ4 W ρ (Subgroup.inclusion h3.A_le)
      (Subgroup.inclusion_injective h3.A_le) hρ_equiv hsq hsq1 hsq_surj).elim

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
