module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.Delta
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.Descend

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G] {L A T : Subgroup G} {z t : G}

private theorem e3_zpows_le_centralizer_A (h : Hyp G L A T z t) :
    zpowers z ≤ centralizer (A : Set G) := by
  rw [zpowers_le, mem_centralizer_iff]
  intro a ha
  exact h.commute_of_mem (h.jc.le ha)

private theorem e3_z_not_mem_A (h : Hyp G L A T z t) : z ∉ A := by
  intro hz
  exact h.not_conj z (h.jc.le hz) (IsConj.refl z)

private theorem e3_elemAb_B (h : Hyp G L A T z t) : IsElementaryAbelian 2 ↥(B A z) := by
  letI : IsElementaryAbelian 2 ↥A := h.jc.module.elemAb
  letI : IsElementaryAbelian 2 ↥(zpowers z) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) (by rw [pow_two]; exact h.set.z_sq)
  exact IsElementaryAbelian.sup_of_le_centralizer (e3_zpows_le_centralizer_A h)

private theorem e3_card_B (h : Hyp G L A T z t) : Nat.card (B A z) = 2 ^ 11 := by
  have hd : Disjoint A (zpowers z) := h.set.disjoint.mono_left h.jc.le
  have hcard := Nat.card_congr (mulEquivProdSup (e3_zpows_le_centralizer_A h) hd).toEquiv
  rw [Nat.card_prod, h.jc.module.card, Nat.card_zpowers,
    orderOf_eq_prime (by rw [pow_two]; exact h.set.z_sq) h.set.z_ne] at hcard
  change Nat.card ↥(A ⊔ zpowers z) = 2 ^ 11
  rw [← hcard]
  norm_num

private theorem e3_z_mem_B (h : Hyp G L A T z t) : z ∈ B A z :=
  mem_sup_right (mem_zpowers z)

private theorem e3_z_mem_R₀ (h : Hyp G L A T z t) : z ∈ R₀ A z :=
  h.B_le_R₀ (e3_z_mem_B h)

private theorem e3_mem_B_eq (h : Hyp G L A T z t) {b : G} (hb : b ∈ B A z) :
    b ∈ A ∨ ∃ a ∈ A, b = a * z := by
  obtain ⟨a, ha, c, hc, hbc⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (e3_zpows_le_centralizer_A h) hb
  rcases eq_one_or_eq_of_mem_zpowers h.set.z_sq hc with hc1 | hcz
  · left
    rw [hbc, hc1, mul_one]
    exact ha
  · right
    exact ⟨a, ha, by rw [hbc, hcz]⟩

private theorem e3_mem_B_not_A (h : Hyp G L A T z t) {b : G} (hb : b ∈ B A z)
    (hbA : b ∉ A) : ∃ a ∈ A, b = a * z := by
  rcases e3_mem_B_eq h hb with h | ⟨a, ha, rfl⟩
  · exact absurd h hbA
  · exact ⟨a, ha, rfl⟩

theorem Hyp.commutator_mem_B (h : Hyp G L A T z t) (h2 : E2Facts L A z) {r s : G}
    (hr : r ∈ R₀ A z) (hs : s ∈ R₀ A z) : ⁅r, s⁆ ∈ B A z := by
  have hmemR : ⁅r, s⁆ ∈ R₀ A z := by
    have hc := Subgroup.commutator_mem_commutator (H₁ := R₀ A z) (H₂ := R₀ A z) hr hs
    simpa using (Subgroup.commutator_le_sup (R₀ A z) (R₀ A z)) hc
  refine (h.deltaHom_eq_one_iff h2 ⟨⁅r, s⁆, hmemR⟩).mp ?_
  have hone : (⟨⁅r, s⁆, hmemR⟩ : ↥(R₀ A z)) =
      ⁅(⟨r, hr⟩ : ↥(R₀ A z)), (⟨s, hs⟩ : ↥(R₀ A z))⁆ := by
    apply Subtype.ext
    rfl
  rw [hone]
  have hmap := map_commutatorElement (f := deltaHom h2.conj_mem)
    (g₁ := (⟨r, hr⟩ : ↥(R₀ A z))) (g₂ := (⟨s, hs⟩ : ↥(R₀ A z)))
  rw [hmap]
  haveI : IsMulCommutative A := h.jc.module.elemAb.toIsMulCommutative
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' _ _)

theorem Hyp.commutator_mem_A_of_mem_B_R₀ (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    {b r : G} (hb : b ∈ B A z) (hr : r ∈ R₀ A z) : ⁅b, r⁆ ∈ A := by
  rcases e3_mem_B_eq h hb with hbA | ⟨a, ha, rfl⟩
  · have hcomm : b * r = r * b := mem_centralizer_iff.1 hr.2 b hbA
    have h1 : b * r * b⁻¹ * r⁻¹ = 1 := by rw [hcomm]; group
    rw [commutatorElement_def, h1]
    exact one_mem A
  · have hzr : ⁅z, r⁆ = delta z r := by
      have hzrz : z * r * z⁻¹ = delta z r * r := by
        have h1 := mul_delta z r
        have hzz : z * (z * delta z r) = delta z r := by
          rw [← mul_assoc, h.set.z_sq, one_mul]
        have h2' : delta z r = z * (r * z * r⁻¹) := by
          have := congrArg (fun x => z * x) h1
          rwa [hzz] at this
        calc z * r * z⁻¹ = z * (r * z * r⁻¹) * r := by rw [h.z_inv]; group
          _ = delta z r * r := by rw [← h2']
      rw [commutatorElement_def, hzrz]
      group
    have hcomm := commutatorElement_mul_left_eq_conj_mul a z r
    rw [hcomm, hzr]
    have har : ⁅a, r⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (mem_centralizer_iff.1 hr.2 a ha)
    rw [har, mul_one]
    exact mul_mem (mul_mem ha (h2.delta_mem hr)) (inv_mem ha)

private theorem e3_commutator_mem_A_of_mem_R₀_B (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    {r b : G} (hr : r ∈ R₀ A z) (hb : b ∈ B A z) : ⁅r, b⁆ ∈ A := by
  have h1 : ⁅b, r⁆ ∈ A := h.commutator_mem_A_of_mem_B_R₀ h2 hb hr
  rw [(commutatorElement_inv (g₁ := b) (g₂ := r)).symm]
  exact inv_mem h1

private noncomputable def e3g : Multiplicative (ZMod 2) := Multiplicative.ofAdd (1 : ZMod 2)

private theorem e3g_ne_one : e3g ≠ 1 := by
  intro h
  have h0 : (1 : ZMod 2) = 0 := congrArg Multiplicative.toAdd h
  exact one_ne_zero h0

private theorem e3g_mul_self : e3g * e3g = 1 := by
  unfold e3g
  decide

private noncomputable def e3tauG (h : Hyp G L A T z t) (x : G) : Multiplicative (ZMod 2) := by
  classical
  exact if x ∈ A then 1 else e3g

private theorem e3tauG_eq_one_iff (h : Hyp G L A T z t) {x : G} (hx : x ∈ B A z) :
    e3tauG h x = 1 ↔ x ∈ A := by
  rw [e3tauG]
  by_cases hxA : x ∈ A
  · simp [hxA]
  · simp [hxA, e3g_ne_one]

private theorem e3tauG_mul (h : Hyp G L A T z t) {b c : G} (hb : b ∈ B A z)
    (hc : c ∈ B A z) : e3tauG h (b * c) = e3tauG h b * e3tauG h c := by
  by_cases hbA : b ∈ A
  · by_cases hcA : c ∈ A
    · have hbcA : b * c ∈ A := mul_mem hbA hcA
      simp [e3tauG, hbA, hcA, hbcA]
    · have hbcA : b * c ∉ A := by
        intro hmem
        apply hcA
        have hc_eq : c = b⁻¹ * (b * c) := by group
        rw [hc_eq]
        exact mul_mem (inv_mem hbA) hmem
      simp [e3tauG, hbA, hcA, hbcA]
  · by_cases hcA : c ∈ A
    · have hbcA : b * c ∉ A := by
        intro hmem
        apply hbA
        have hb_eq : b = (b * c) * c⁻¹ := by group
        rw [hb_eq]
        exact mul_mem hmem (inv_mem hcA)
      simp [e3tauG, hbA, hcA, hbcA]
    · obtain ⟨a₁, ha₁, hb_eq⟩ := e3_mem_B_not_A h hb hbA
      obtain ⟨a₂, ha₂, hc_eq⟩ := e3_mem_B_not_A h hc hcA
      have hbcA : b * c ∈ A := by
        have heqbc : b * c = a₁ * a₂ := by
          rw [hb_eq, hc_eq]
          have hcomm : z * a₂ = a₂ * z := (h.commute_of_mem (h.jc.le ha₂)).symm
          calc a₁ * z * (a₂ * z) = a₁ * (z * a₂) * z := by group
            _ = a₁ * (a₂ * z) * z := by rw [hcomm]
            _ = (a₁ * a₂) * (z * z) := by group
            _ = a₁ * a₂ := by rw [h.set.z_sq, mul_one]
        rw [heqbc]
        exact mul_mem ha₁ ha₂
      simp [e3tauG, hbA, hcA, hbcA, e3g_mul_self]

private noncomputable def e3tau (h : Hyp G L A T z t) :
    ↥(B A z) →* Multiplicative (ZMod 2) where
  toFun b := e3tauG h b
  map_one' := by
    show e3tauG h (1 : G) = 1
    exact (e3tauG_eq_one_iff h (one_mem (B A z))).mpr (one_mem A)
  map_mul' b c := e3tauG_mul h b.2 c.2

private theorem e3tau_apply (h : Hyp G L A T z t) (b : ↥(B A z)) :
    e3tau h b = e3tauG h b := rfl

private theorem e3tau_eq_one_iff (h : Hyp G L A T z t) (b : ↥(B A z)) :
    e3tau h b = 1 ↔ (b : G) ∈ A := e3tauG_eq_one_iff h b.2

private theorem e3_conj_R₀_B_mem_B (h : Hyp G L A T z t) (h2 : E2Facts L A z) {r b : G}
    (hr : r ∈ R₀ A z) (hb : b ∈ B A z) : r * b * r⁻¹ ∈ B A z := by
  have hmemA : r * b * r⁻¹ * b⁻¹ ∈ A :=
    e3_commutator_mem_A_of_mem_R₀_B h h2 hr hb
  have heq : r * b * r⁻¹ = (r * b * r⁻¹ * b⁻¹) * b := by group
  rw [heq]
  exact mul_mem (mem_sup_left hmemA) hb

private theorem e3tauG_conj_R₀ (h : Hyp G L A T z t) (h2 : E2Facts L A z) {r b : G}
    (hr : r ∈ R₀ A z) (hb : b ∈ B A z) : e3tauG h (r * b * r⁻¹) = e3tauG h b := by
  have hmemA : r * b * r⁻¹ * b⁻¹ ∈ A :=
    e3_commutator_mem_A_of_mem_R₀_B h h2 hr hb
  have heq : r * b * r⁻¹ = (r * b * r⁻¹ * b⁻¹) * b := by group
  rw [heq, e3tauG_mul h (mem_sup_left hmemA) hb]
  rw [show e3tauG h (r * b * r⁻¹ * b⁻¹) = 1 from
    (e3tauG_eq_one_iff h (mem_sup_left hmemA)).mpr hmemA, one_mul]

private theorem e3_conj_N_B_mem_A (h : Hyp G L A T z t) (h2 : E2Facts L A z) {x b : G}
    (hx : x ∈ L ⊓ normalizer (A : Set G)) (hb : b ∈ B A z) :
    x * b * x⁻¹ * b⁻¹ ∈ A := by
  rcases e3_mem_B_eq h hb with hbA | ⟨a, ha, rfl⟩
  · have hxA : x * b * x⁻¹ ∈ A := (mem_normalizer_iff.1 hx.2 b).1 hbA
    exact mul_mem hxA (inv_mem hbA)
  · have hxa : x * a * x⁻¹ ∈ A := (mem_normalizer_iff.1 hx.2 a).1 ha
    have hcA : z⁻¹ * (x * z * x⁻¹) ∈ A := h2.conj_mem x (h.le_M hx)
    have hza : z * a⁻¹ = a⁻¹ * z :=
      (h.commute_of_mem (h.jc.le (inv_mem ha))).symm
    have hzc' : z * (z⁻¹ * (x * z * x⁻¹)) = x * z * x⁻¹ := by group
    have hzinv : (a * z)⁻¹ = z * a⁻¹ := by rw [mul_inv_rev, h.z_inv]
    have hfinal : x * (a * z) * x⁻¹ * (a * z)⁻¹ =
        (x * a * x⁻¹) * (z⁻¹ * (x * z * x⁻¹)) * a⁻¹ := by
      calc x * (a * z) * x⁻¹ * (a * z)⁻¹
          = (x * a * x⁻¹) * (x * z * x⁻¹) * (z * a⁻¹) := by rw [hzinv]; group
        _ = (x * a * x⁻¹) * (z * (z⁻¹ * (x * z * x⁻¹))) * (z * a⁻¹) := by rw [hzc']
        _ = (x * a * x⁻¹) * (z⁻¹ * (x * z * x⁻¹)) * a⁻¹ := by
              have hu : z * (z⁻¹ * (x * z * x⁻¹)) =
                  (z⁻¹ * (x * z * x⁻¹)) * z :=
                (h.commute_of_mem (h.jc.le hcA)).symm
              calc (x * a * x⁻¹) * (z * (z⁻¹ * (x * z * x⁻¹))) * (z * a⁻¹)
                  = (x * a * x⁻¹) * (z⁻¹ * (x * z * x⁻¹)) * (z * (z * a⁻¹)) := by
                    rw [hu]; group
                _ = (x * a * x⁻¹) * (z⁻¹ * (x * z * x⁻¹)) * a⁻¹ := by
                    rw [show z * (z * a⁻¹) = a⁻¹ by
                      rw [← mul_assoc, h.set.z_sq, one_mul]]
    rw [hfinal]
    exact mul_mem (mul_mem hxa hcA) (inv_mem ha)

private noncomputable def e3deltaSection (h2 : E2Facts L A z) (a : ↥A) : ↥(R₀ A z) :=
  ⟨Classical.choose (h2.exists_delta_eq a.2),
    (Classical.choose_spec (h2.exists_delta_eq a.2)).1⟩

private theorem e3deltaSection_spec (h2 : E2Facts L A z) (a : ↥A) :
    deltaHom h2.conj_mem (e3deltaSection h2 a) = a := by
  apply Subtype.ext
  exact (Classical.choose_spec (h2.exists_delta_eq a.2)).2

private theorem e3deltaSection_val (h2 : E2Facts L A z) (a : ↥A) :
    delta z ((e3deltaSection h2 a : ↥(R₀ A z)) : G) = (a : G) :=
  congrArg Subtype.val (e3deltaSection_spec h2 a)

private noncomputable def e3betaG (h : Hyp G L A T z t) (h2 : E2Facts L A z) :
    ↥A → ↥A → ZMod 2 :=
  fun a b =>
    (e3tauG h ⁅((e3deltaSection h2 a : ↥(R₀ A z)) : G),
      ((e3deltaSection h2 b : ↥(R₀ A z)) : G)⁆).toAdd

private theorem e3tauG_commutator_eq_left (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    {r r' s : G} (hr : r ∈ R₀ A z) (hr' : r' ∈ R₀ A z) (hs : s ∈ R₀ A z)
    (hδ : delta z r' = delta z r) : e3tauG h ⁅r', s⁆ = e3tauG h ⁅r, s⁆ := by
  let b₁ : G := r' * r⁻¹
  have hb₁R : b₁ ∈ R₀ A z := mul_mem hr' (inv_mem hr)
  have hb₁B : b₁ ∈ B A z := by
    apply (h.delta_eq_one_iff h2 hb₁R).mp
    have h1 : delta z (r' * r⁻¹) = delta z r' * delta z r⁻¹ :=
      h2.delta_mul hr' (inv_mem hr)
    rw [h1, hδ, delta_inv_of_conj_mem h2.conj_mem hr, mul_inv_cancel]
  have hr'eq : r' = b₁ * r := by
    simp only [b₁]
    group
  have hcommA : ⁅b₁, s⁆ ∈ A := h.commutator_mem_A_of_mem_B_R₀ h2 hb₁B hs
  have hcommB : ⁅r, s⁆ ∈ B A z := h.commutator_mem_B h2 hr hs
  have hcommB₁ : ⁅b₁, s⁆ ∈ B A z := mem_sup_left hcommA
  have hexp : ⁅r', s⁆ = b₁ * ⁅r, s⁆ * b₁⁻¹ * ⁅b₁, s⁆ := by
    rw [hr'eq, commutatorElement_mul_left_eq_conj_mul]
  have hconj : e3tauG h (b₁ * ⁅r, s⁆ * b₁⁻¹) = e3tauG h ⁅r, s⁆ :=
    e3tauG_conj_R₀ h h2 hb₁R hcommB
  rw [hexp, e3tauG_mul h (e3_conj_R₀_B_mem_B h h2 hb₁R hcommB) hcommB₁, hconj,
    show e3tauG h ⁅b₁, s⁆ = 1 from
      (e3tauG_eq_one_iff h hcommB₁).mpr hcommA, mul_one]

private theorem e3tauG_commutator_eq_right (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    {r s s' : G} (hr : r ∈ R₀ A z) (hs : s ∈ R₀ A z) (hs' : s' ∈ R₀ A z)
    (hδ : delta z s' = delta z s) : e3tauG h ⁅r, s'⁆ = e3tauG h ⁅r, s⁆ := by
  let b₂ : G := s' * s⁻¹
  have hb₂R : b₂ ∈ R₀ A z := mul_mem hs' (inv_mem hs)
  have hb₂B : b₂ ∈ B A z := by
    apply (h.delta_eq_one_iff h2 hb₂R).mp
    have h1 : delta z (s' * s⁻¹) = delta z s' * delta z s⁻¹ :=
      h2.delta_mul hs' (inv_mem hs)
    rw [h1, hδ, delta_inv_of_conj_mem h2.conj_mem hs, mul_inv_cancel]
  have hs'eq : s' = b₂ * s := by
    simp only [b₂]
    group
  have hcommA : ⁅r, b₂⁆ ∈ A := e3_commutator_mem_A_of_mem_R₀_B h h2 hr hb₂B
  have hcommB : ⁅r, s⁆ ∈ B A z := h.commutator_mem_B h2 hr hs
  have hexp : ⁅r, s'⁆ = ⁅r, b₂⁆ * (b₂ * ⁅r, s⁆ * b₂⁻¹) := by
    rw [hs'eq, commutatorElement_mul_right_eq_mul_conj]
    simp only [mul_assoc]
  have hconj : e3tauG h (b₂ * ⁅r, s⁆ * b₂⁻¹) = e3tauG h ⁅r, s⁆ :=
    e3tauG_conj_R₀ h h2 hb₂R hcommB
  rw [hexp, e3tauG_mul h (mem_sup_left hcommA) (e3_conj_R₀_B_mem_B h h2 hb₂R hcommB),
    show e3tauG h ⁅r, b₂⁆ = 1 from
      (e3tauG_eq_one_iff h (mem_sup_left hcommA)).mpr hcommA, one_mul, hconj]

private theorem e3betaG_eq (h : Hyp G L A T z t) (h2 : E2Facts L A z) {a b : ↥A} {r s : G}
    (hr : r ∈ R₀ A z) (hs : s ∈ R₀ A z)
    (hrδ : delta z r = (a : G)) (hsδ : delta z s = (b : G)) :
    (e3tauG h ⁅r, s⁆).toAdd = e3betaG h h2 a b := by
  have hb₁ : delta z ((e3deltaSection h2 b : ↥(R₀ A z)) : G) = delta z s :=
    (e3deltaSection_val h2 b).trans hsδ.symm
  have h₁ : (e3tauG h ⁅r, s⁆).toAdd =
      (e3tauG h ⁅r, ((e3deltaSection h2 b : ↥(R₀ A z)) : G)⁆).toAdd := by
    rw [e3tauG_commutator_eq_right h h2 hr hs (e3deltaSection h2 b).2 hb₁]
  have ha₁ : delta z r = delta z ((e3deltaSection h2 a : ↥(R₀ A z)) : G) :=
    hrδ.trans (e3deltaSection_val h2 a).symm
  have h₂ : (e3tauG h ⁅r, ((e3deltaSection h2 b : ↥(R₀ A z)) : G)⁆).toAdd =
      (e3tauG h ⁅((e3deltaSection h2 a : ↥(R₀ A z)) : G),
        ((e3deltaSection h2 b : ↥(R₀ A z)) : G)⁆).toAdd := by
    rw [e3tauG_commutator_eq_left h h2 (e3deltaSection h2 a).2 hr (e3deltaSection h2 b).2 ha₁]
  exact h₁.trans h₂

private theorem e3betaG_mul_left (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (a₁ a₂ b : ↥A) :
    e3betaG h h2 (a₁ * a₂) b = e3betaG h h2 a₁ b + e3betaG h h2 a₂ b := by
  let r₁ : G := ((e3deltaSection h2 a₁ : ↥(R₀ A z)) : G)
  let r₂ : G := ((e3deltaSection h2 a₂ : ↥(R₀ A z)) : G)
  let s : G := ((e3deltaSection h2 b : ↥(R₀ A z)) : G)
  have hr₁ : r₁ ∈ R₀ A z := (e3deltaSection h2 a₁).2
  have hr₂ : r₂ ∈ R₀ A z := (e3deltaSection h2 a₂).2
  have hs : s ∈ R₀ A z := (e3deltaSection h2 b).2
  have hδ₁ : delta z r₁ = (a₁ : G) := e3deltaSection_val h2 a₁
  have hδ₂ : delta z r₂ = (a₂ : G) := e3deltaSection_val h2 a₂
  have hδs : delta z s = (b : G) := e3deltaSection_val h2 b
  have hr₁₂ : r₁ * r₂ ∈ R₀ A z := mul_mem hr₁ hr₂
  have hδ₁₂ : delta z (r₁ * r₂) = ((a₁ * a₂ : ↥A) : G) := by
    rw [h2.delta_mul hr₁ hr₂, hδ₁, hδ₂]
    rfl
  have hbeta₁₂ : e3betaG h h2 (a₁ * a₂) b =
      (e3tauG h ⁅r₁ * r₂, s⁆).toAdd :=
    (e3betaG_eq h h2 hr₁₂ hs hδ₁₂ hδs).symm
  have hb₁ : e3betaG h h2 a₁ b = (e3tauG h ⁅r₁, s⁆).toAdd :=
    (e3betaG_eq h h2 hr₁ hs hδ₁ hδs).symm
  have hb₂ : e3betaG h h2 a₂ b = (e3tauG h ⁅r₂, s⁆).toAdd :=
    (e3betaG_eq h h2 hr₂ hs hδ₂ hδs).symm
  have hcomm₁ : ⁅r₂, s⁆ ∈ B A z := h.commutator_mem_B h2 hr₂ hs
  have hcomm₂ : ⁅r₁, s⁆ ∈ B A z := h.commutator_mem_B h2 hr₁ hs
  have hconj : r₁ * ⁅r₂, s⁆ * r₁⁻¹ ∈ B A z :=
    e3_conj_R₀_B_mem_B h h2 hr₁ hcomm₁
  have htau : e3tauG h ⁅r₁ * r₂, s⁆ =
      e3tauG h ⁅r₂, s⁆ * e3tauG h ⁅r₁, s⁆ := by
    have hexp : ⁅r₁ * r₂, s⁆ = (r₁ * ⁅r₂, s⁆ * r₁⁻¹) * ⁅r₁, s⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul]
    rw [hexp, e3tauG_mul h hconj hcomm₂,
      e3tauG_conj_R₀ h h2 hr₁ hcomm₁]
  calc e3betaG h h2 (a₁ * a₂) b = (e3tauG h ⁅r₁ * r₂, s⁆).toAdd := hbeta₁₂
    _ = (e3tauG h ⁅r₂, s⁆ * e3tauG h ⁅r₁, s⁆).toAdd := by rw [htau]
    _ = (e3tauG h ⁅r₂, s⁆).toAdd + (e3tauG h ⁅r₁, s⁆).toAdd :=
          toAdd_mul _ _
    _ = e3betaG h h2 a₂ b + e3betaG h h2 a₁ b := by rw [hb₂, hb₁]
    _ = e3betaG h h2 a₁ b + e3betaG h h2 a₂ b := add_comm _ _

private theorem e3betaG_mul_right (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (a b₁ b₂ : ↥A) :
    e3betaG h h2 a (b₁ * b₂) = e3betaG h h2 a b₁ + e3betaG h h2 a b₂ := by
  let r : G := ((e3deltaSection h2 a : ↥(R₀ A z)) : G)
  let s₁ : G := ((e3deltaSection h2 b₁ : ↥(R₀ A z)) : G)
  let s₂ : G := ((e3deltaSection h2 b₂ : ↥(R₀ A z)) : G)
  have hr : r ∈ R₀ A z := (e3deltaSection h2 a).2
  have hs₁ : s₁ ∈ R₀ A z := (e3deltaSection h2 b₁).2
  have hs₂ : s₂ ∈ R₀ A z := (e3deltaSection h2 b₂).2
  have hδr : delta z r = (a : G) := e3deltaSection_val h2 a
  have hδ₁ : delta z s₁ = (b₁ : G) := e3deltaSection_val h2 b₁
  have hδ₂ : delta z s₂ = (b₂ : G) := e3deltaSection_val h2 b₂
  have hs₁₂ : s₁ * s₂ ∈ R₀ A z := mul_mem hs₁ hs₂
  have hδ₁₂ : delta z (s₁ * s₂) = ((b₁ * b₂ : ↥A) : G) := by
    rw [h2.delta_mul hs₁ hs₂, hδ₁, hδ₂]
    rfl
  have hbeta₁₂ : e3betaG h h2 a (b₁ * b₂) =
      (e3tauG h ⁅r, s₁ * s₂⁆).toAdd :=
    (e3betaG_eq h h2 hr hs₁₂ hδr hδ₁₂).symm
  have hb₁ : e3betaG h h2 a b₁ = (e3tauG h ⁅r, s₁⁆).toAdd :=
    (e3betaG_eq h h2 hr hs₁ hδr hδ₁).symm
  have hb₂ : e3betaG h h2 a b₂ = (e3tauG h ⁅r, s₂⁆).toAdd :=
    (e3betaG_eq h h2 hr hs₂ hδr hδ₂).symm
  have hcomm₁ : ⁅r, s₁⁆ ∈ B A z := h.commutator_mem_B h2 hr hs₁
  have hcomm₂ : ⁅r, s₂⁆ ∈ B A z := h.commutator_mem_B h2 hr hs₂
  have hconj : s₁ * ⁅r, s₂⁆ * s₁⁻¹ ∈ B A z :=
    e3_conj_R₀_B_mem_B h h2 hs₁ hcomm₂
  have htau : e3tauG h ⁅r, s₁ * s₂⁆ =
      e3tauG h ⁅r, s₁⁆ * e3tauG h ⁅r, s₂⁆ := by
    have hexp : ⁅r, s₁ * s₂⁆ = ⁅r, s₁⁆ * (s₁ * ⁅r, s₂⁆ * s₁⁻¹) := by
      rw [commutatorElement_mul_right_eq_mul_conj]
      simp only [mul_assoc]
    rw [hexp, e3tauG_mul h hcomm₁ hconj,
      e3tauG_conj_R₀ h h2 hs₁ hcomm₂]
  calc e3betaG h h2 a (b₁ * b₂) = (e3tauG h ⁅r, s₁ * s₂⁆).toAdd := hbeta₁₂
    _ = (e3tauG h ⁅r, s₁⁆ * e3tauG h ⁅r, s₂⁆).toAdd := by rw [htau]
    _ = (e3tauG h ⁅r, s₁⁆).toAdd + (e3tauG h ⁅r, s₂⁆).toAdd :=
          toAdd_mul _ _
    _ = e3betaG h h2 a b₁ + e3betaG h h2 a b₂ := by rw [hb₁, hb₂]

private theorem e3_conj_mem_R₀ (h : Hyp G L A T z t) {x r : G}
    (hx : x ∈ L ⊓ normalizer (A : Set G)) (hr : r ∈ R₀ A z) :
    x * r * x⁻¹ ∈ R₀ A z := by
  refine ⟨?_, ?_⟩
  · exact (M A z).mul_mem ((M A z).mul_mem (h.le_M hx) hr.1) ((M A z).inv_mem (h.le_M hx))
  · show x * r * x⁻¹ ∈ centralizer (A : Set G)
    rw [mem_centralizer_iff]
    intro a ha
    have hxa : x⁻¹ * a * x ∈ A := by
      simpa using (mem_normalizer_iff.1 (inv_mem hx.2) a).1 ha
    have hcomm : (x⁻¹ * a * x) * r = r * (x⁻¹ * a * x) :=
      mem_centralizer_iff.1 hr.2 (x⁻¹ * a * x) hxa
    calc a * (x * r * x⁻¹) = x * ((x⁻¹ * a * x) * r) * x⁻¹ := by group
      _ = x * (r * (x⁻¹ * a * x)) * x⁻¹ := by rw [hcomm]
      _ = (x * r * x⁻¹) * a := by group

private theorem e3tauG_conj_N (h : Hyp G L A T z t) (h2 : E2Facts L A z) {x b : G}
    (hx : x ∈ L ⊓ normalizer (A : Set G)) (hb : b ∈ B A z) :
    e3tauG h (x * b * x⁻¹) = e3tauG h b := by
  have hmemA : x * b * x⁻¹ * b⁻¹ ∈ A := e3_conj_N_B_mem_A h h2 hx hb
  have heq : x * b * x⁻¹ = (x * b * x⁻¹ * b⁻¹) * b := by group
  rw [heq, e3tauG_mul h (mem_sup_left hmemA) hb]
  rw [show e3tauG h (x * b * x⁻¹ * b⁻¹) = 1 from
    (e3tauG_eq_one_iff h (mem_sup_left hmemA)).mpr hmemA, one_mul]

private theorem e3betaG_invariant (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (g : ↥(autImage L A)) (a b : ↥A) :
    e3betaG h h2 ((g : MulAut ↥A) a) ((g : MulAut ↥A) b) = e3betaG h h2 a b := by
  obtain ⟨x, rfl⟩ := exists_toAutImage_eq g
  let r : G := ((e3deltaSection h2 a : ↥(R₀ A z)) : G)
  let s : G := ((e3deltaSection h2 b : ↥(R₀ A z)) : G)
  have hr : r ∈ R₀ A z := (e3deltaSection h2 a).2
  have hs : s ∈ R₀ A z := (e3deltaSection h2 b).2
  have hr' : x * r * x⁻¹ ∈ R₀ A z := e3_conj_mem_R₀ h x.2 hr
  have hs' : x * s * x⁻¹ ∈ R₀ A z := e3_conj_mem_R₀ h x.2 hs
  have hδr' : delta z (x * r * x⁻¹) = (((toAutImage x) : MulAut ↥A) a : G) := by
    calc delta z ((x : G) * r * (x : G)⁻¹) =
        (x : G) * delta z r * (x : G)⁻¹ :=
          h.delta_conj (x := (x : G)) (r := r) x.2.1
      _ = (x : G) * (a : G) * (x : G)⁻¹ := by rw [e3deltaSection_val h2 a]
      _ = (((toAutImage x) : MulAut ↥A) a : G) := by
          simpa [coe_toAutImage] using (conjN_apply x a).symm
  have hδs' : delta z (x * s * x⁻¹) = (((toAutImage x) : MulAut ↥A) b : G) := by
    calc delta z ((x : G) * s * (x : G)⁻¹) =
        (x : G) * delta z s * (x : G)⁻¹ :=
          h.delta_conj (x := (x : G)) (r := s) x.2.1
      _ = (x : G) * (b : G) * (x : G)⁻¹ := by rw [e3deltaSection_val h2 b]
      _ = (((toAutImage x) : MulAut ↥A) b : G) := by
          simpa [coe_toAutImage] using (conjN_apply x b).symm
  have h₁ : e3betaG h h2 (((toAutImage x) : MulAut ↥A) a) (((toAutImage x) : MulAut ↥A) b) =
      (e3tauG h ⁅x * r * x⁻¹, x * s * x⁻¹⁆).toAdd :=
    (e3betaG_eq h h2 hr' hs' hδr' hδs').symm
  have h₂ : e3betaG h h2 a b = (e3tauG h ⁅r, s⁆).toAdd :=
    (e3betaG_eq h h2 hr hs (e3deltaSection_val h2 a) (e3deltaSection_val h2 b)).symm
  rw [h₁, h₂]
  congr 1
  have hconj : ⁅↑x * r * ↑x⁻¹, ↑x * s * ↑x⁻¹⁆ = ↑x * ⁅r, s⁆ * ↑x⁻¹ := by
    simpa only [Subgroup.coe_inv] using
      (conjugate_commutatorElement (g₁ := r) (g₂ := s) (g₃ := (x : G))).symm
  rw [hconj]
  simpa only [Subgroup.coe_inv] using
    e3tauG_conj_N h h2 x.2 (h.commutator_mem_B h2 hr hs)

theorem Hyp.commutator_mem_A_of_mem_R₀ (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    {r s : G} (hr : r ∈ R₀ A z) (hs : s ∈ R₀ A z) : ⁅r, s⁆ ∈ A := by
  have hzero := congrFun (congrFun (h.jc.module.noBilin (e3betaG h h2)
      (e3betaG_mul_left h h2) (e3betaG_mul_right h h2)
      (fun g hg a b => e3betaG_invariant h h2 ⟨g, hg⟩ a b))
      ⟨delta z r, h2.delta_mem hr⟩) ⟨delta z s, h2.delta_mem hs⟩
  have hrep : (e3tauG h ⁅r, s⁆).toAdd =
      e3betaG h h2 ⟨delta z r, h2.delta_mem hr⟩ ⟨delta z s, h2.delta_mem hs⟩ :=
    e3betaG_eq h h2 hr hs rfl rfl
  have hzero' : (e3tauG h ⁅r, s⁆).toAdd = 0 := by rwa [← hrep] at hzero
  have htau : e3tauG h ⁅r, s⁆ = 1 := (toAdd_eq_zero).mp hzero'
  exact (e3tauG_eq_one_iff h (h.commutator_mem_B h2 hr hs)).mp htau

private theorem e3_mul_self_mem_A_of_mem_B (h : Hyp G L A T z t) {b : G}
    (hb : b ∈ B A z) : b * b ∈ A := by
  letI : IsElementaryAbelian 2 ↥(B A z) := e3_elemAb_B h
  have h1 : b ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) b hb
  rw [pow_two] at h1
  rw [h1]
  exact one_mem A

private theorem e3_sq_mem_B (h : Hyp G L A T z t) (h2 : E2Facts L A z) {r : G}
    (hr : r ∈ R₀ A z) : r * r ∈ B A z := by
  have hr2R : r * r ∈ R₀ A z := mul_mem hr hr
  apply (h.delta_eq_one_iff h2 hr2R).mp
  rw [h2.delta_mul hr hr]
  letI : IsElementaryAbelian 2 ↥A := h.jc.module.elemAb
  have h1 : (delta z r) ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian (p := 2) (delta z r) (h2.delta_mem hr)
  simpa [pow_two] using h1

private theorem e3_sq_mul_sq_inv_mem_A (h : Hyp G L A T z t) (h2 : E2Facts L A z) {r s : G}
    (hr : r ∈ R₀ A z) (hs : s ∈ R₀ A z) :
    (r * s) * (r * s) * (r * r * (s * s))⁻¹ ∈ A := by
  let c : G := r⁻¹ * s * r * s⁻¹
  have hcA : c ∈ A := by
    have hcm := h.commutator_mem_A_of_mem_R₀ h2 (inv_mem hr) hs
    simpa [c, commutatorElement_def] using hcm
  have hcs : r⁻¹ * s * r = c * s := by
    simp only [c]
    group
  have hcr : c * r = r * c := mem_centralizer_iff.1 hr.2 c hcA
  have hrc : r * r * c = c * (r * r) := by
    rw [mul_assoc, ← hcr, ← mul_assoc, ← hcr, mul_assoc]
  have hcalc : (r * s) * (r * s) = r * r * (r⁻¹ * s * r) * s := by group
  have hfinal : (r * s) * (r * s) = c * (r * r * (s * s)) := by
    rw [hcalc, hcs]
    calc r * r * (c * s) * s = (r * r * c) * (s * s) := by group
      _ = (c * (r * r)) * (s * s) := by rw [hrc]
      _ = c * (r * r * (s * s)) := by group
  have hcancel : c * (r * r * (s * s)) * (r * r * (s * s))⁻¹ = c := by
    rw [mul_assoc, mul_inv_cancel, mul_one]
  rw [hfinal, hcancel]
  exact hcA

private theorem e3_sq_mem_A_iff (h : Hyp G L A T z t) (h2 : E2Facts L A z) {r r' : G}
    (hr : r ∈ R₀ A z) (hr' : r' ∈ R₀ A z) (hδ : delta z r' = delta z r) :
    r' * r' ∈ A ↔ r * r ∈ A := by
  let b : G := r' * r⁻¹
  have hbR : b ∈ R₀ A z := mul_mem hr' (inv_mem hr)
  have hbB : b ∈ B A z := by
    apply (h.delta_eq_one_iff h2 hbR).mp
    have h1 : delta z (r' * r⁻¹) = delta z r' * delta z r⁻¹ :=
      h2.delta_mul hr' (inv_mem hr)
    rw [h1, hδ, delta_inv_of_conj_mem h2.conj_mem hr, mul_inv_cancel]
  have hr'eq : r' = b * r := by
    simp only [b]
    group
  have hcong := e3_sq_mul_sq_inv_mem_A h h2 hbR hr
  have hbbA : b * b ∈ A := e3_mul_self_mem_A_of_mem_B h hbB
  have hrel : (b * r) * (b * r) ∈ A ↔ r * r ∈ A := by
    have hx : (b * r) * (b * r) =
        ((b * r) * (b * r) * (b * b * (r * r))⁻¹) * (b * b * (r * r)) := by group
    rw [hx]
    constructor
    · intro hmem
      have h1 : ((b * r) * (b * r) * (b * b * (r * r))⁻¹)⁻¹ *
          (((b * r) * (b * r) * (b * b * (r * r))⁻¹) * (b * b * (r * r))) ∈ A :=
        mul_mem (inv_mem hcong) hmem
      rw [inv_mul_cancel_left] at h1
      have h2' : (b * b)⁻¹ * (b * b * (r * r)) ∈ A := mul_mem (inv_mem hbbA) h1
      rwa [inv_mul_cancel_left] at h2'
    · intro hmem
      exact mul_mem hcong (mul_mem hbbA hmem)
  rw [hr'eq]
  exact hrel

private noncomputable def e3q (h : Hyp G L A T z t) (h2 : E2Facts L A z) (a : ↥A) :
    Multiplicative (ZMod 2) :=
  e3tauG h (((e3deltaSection h2 a : ↥(R₀ A z)) : G) *
    ((e3deltaSection h2 a : ↥(R₀ A z)) : G))

private theorem e3tauG_eq_g_of_not_mem (h : Hyp G L A T z t) {x : G} (hx : x ∈ B A z)
    (hxA : x ∉ A) : e3tauG h x = e3g := by
  simp [e3tauG, hxA]

private theorem e3q_eq_of_delta (h : Hyp G L A T z t) (h2 : E2Facts L A z) {a : ↥A} {r : G}
    (hr : r ∈ R₀ A z) (hδ : delta z r = (a : G)) :
    e3q h h2 a = e3tauG h (r * r) := by
  let r₀ : G := ((e3deltaSection h2 a : ↥(R₀ A z)) : G)
  have hr₀ : r₀ ∈ R₀ A z := (e3deltaSection h2 a).2
  have hδ₀ : delta z r₀ = (a : G) := e3deltaSection_val h2 a
  have hiff : r₀ * r₀ ∈ A ↔ r * r ∈ A :=
    e3_sq_mem_A_iff h h2 (r := r) (r' := r₀) hr hr₀ (hδ₀.trans hδ.symm)
  have hsqB₀ : r₀ * r₀ ∈ B A z := e3_sq_mem_B h h2 hr₀
  have hsqB : r * r ∈ B A z := e3_sq_mem_B h h2 hr
  have hq : e3q h h2 a = e3tauG h (r₀ * r₀) := rfl
  rw [hq]
  by_cases hA : r * r ∈ A
  · have hA₀ : r₀ * r₀ ∈ A := hiff.mpr hA
    rw [show e3tauG h (r₀ * r₀) = 1 from (e3tauG_eq_one_iff h hsqB₀).mpr hA₀,
      show e3tauG h (r * r) = 1 from (e3tauG_eq_one_iff h hsqB).mpr hA]
  · have hA₀ : r₀ * r₀ ∉ A := fun hc => hA (hiff.mp hc)
    rw [show e3tauG h (r₀ * r₀) = e3g from e3tauG_eq_g_of_not_mem h hsqB₀ hA₀,
      show e3tauG h (r * r) = e3g from e3tauG_eq_g_of_not_mem h hsqB hA]

private theorem e3q_mul (h : Hyp G L A T z t) (h2 : E2Facts L A z) (a b : ↥A) :
    e3q h h2 (a * b) = e3q h h2 a * e3q h h2 b := by
  let r : G := ((e3deltaSection h2 a : ↥(R₀ A z)) : G)
  let s : G := ((e3deltaSection h2 b : ↥(R₀ A z)) : G)
  have hr : r ∈ R₀ A z := (e3deltaSection h2 a).2
  have hs : s ∈ R₀ A z := (e3deltaSection h2 b).2
  have hδr : delta z r = (a : G) := e3deltaSection_val h2 a
  have hδs : delta z s = (b : G) := e3deltaSection_val h2 b
  have hrs : r * s ∈ R₀ A z := mul_mem hr hs
  have hδrs : delta z (r * s) = ((a * b : ↥A) : G) := by
    rw [h2.delta_mul hr hs, hδr, hδs]
    rfl
  rw [e3q_eq_of_delta h h2 hrs hδrs, e3q_eq_of_delta h h2 hr hδr,
    e3q_eq_of_delta h h2 hs hδs]
  have hcong := e3_sq_mul_sq_inv_mem_A h h2 hr hs
  have hrsB : (r * s) * (r * s) ∈ B A z := e3_sq_mem_B h h2 hrs
  have hrB : r * r ∈ B A z := e3_sq_mem_B h h2 hr
  have hsB : s * s ∈ B A z := e3_sq_mem_B h h2 hs
  have hcongB : r * r * (s * s) ∈ B A z := mul_mem hrB hsB
  have htauEq : e3tauG h ((r * s) * (r * s)) = e3tauG h (r * r * (s * s)) := by
    have hx : (r * s) * (r * s) =
        ((r * s) * (r * s) * (r * r * (s * s))⁻¹) * (r * r * (s * s)) := by group
    rw [hx, e3tauG_mul h (mem_sup_left hcong) hcongB]
    rw [show e3tauG h ((r * s) * (r * s) * (r * r * (s * s))⁻¹) = 1 from
      (e3tauG_eq_one_iff h (mem_sup_left hcong)).mpr hcong, one_mul]
  rw [htauEq, e3tauG_mul h hrB hsB]

private noncomputable def e3qHom (h : Hyp G L A T z t) (h2 : E2Facts L A z) :
    ↥A →* Multiplicative (ZMod 2) where
  toFun a := e3q h h2 a
  map_one' := by
    show e3q h h2 1 = 1
    rw [e3q_eq_of_delta h h2 (e3deltaSection h2 (1 : ↥A)).2 (e3deltaSection_val h2 1)]
    have hbB : ((e3deltaSection h2 (1 : ↥A) : ↥(R₀ A z)) : G) ∈ B A z :=
      (h.delta_eq_one_iff h2 (e3deltaSection h2 (1 : ↥A)).2).mp
        (e3deltaSection_val h2 1)
    exact (e3tauG_eq_one_iff h
      (e3_sq_mem_B h h2 (e3deltaSection h2 (1 : ↥A)).2)).mpr
      (e3_mul_self_mem_A_of_mem_B h hbB)
  map_mul' a b := e3q_mul h h2 a b

private theorem e3q_toAutImage (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (x : ↥(L ⊓ normalizer (A : Set G))) (a : ↥A) :
    e3q h h2 (((toAutImage x) : MulAut ↥A) a) = e3q h h2 a := by
  let r : G := ((e3deltaSection h2 a : ↥(R₀ A z)) : G)
  have hr : r ∈ R₀ A z := (e3deltaSection h2 a).2
  let r' : G := (x : G) * r * (x : G)⁻¹
  have hr' : r' ∈ R₀ A z := e3_conj_mem_R₀ h x.2 hr
  have hδr' : delta z r' = ((((toAutImage x) : MulAut ↥A) a : ↥A) : G) := by
    show delta z ((x : G) * r * (x : G)⁻¹) = ((((toAutImage x) : MulAut ↥A) a : ↥A) : G)
    rw [h.delta_conj (x := (x : G)) (r := r) x.2.1,
      show delta z r = (a : G) from e3deltaSection_val h2 a]
    simpa [coe_toAutImage] using (conjN_apply x a).symm
  rw [e3q_eq_of_delta h h2 hr' hδr', e3q_eq_of_delta h h2 hr (e3deltaSection_val h2 a)]
  have hsq : r' * r' = (x : G) * (r * r) * (x : G)⁻¹ := by
    show ((x : G) * r * (x : G)⁻¹) * ((x : G) * r * (x : G)⁻¹) =
      (x : G) * (r * r) * (x : G)⁻¹
    group
  rw [hsq]
  exact e3tauG_conj_N h h2 x.2 (e3_sq_mem_B h h2 hr)

private theorem e3qHom_ker_invariant (h : Hyp G L A T z t) (h2 : E2Facts L A z) :
    ∀ g ∈ ⁅autImage L A, autImage L A⁆, ∀ u ∈ (e3qHom h h2).ker,
      (g : MulAut ↥A) u ∈ (e3qHom h h2).ker := by
  intro g hg u hu
  have hgQ : g ∈ autImage L A := by
    have hle : ⁅autImage L A, autImage L A⁆ ≤ autImage L A := by
      simpa using (Subgroup.commutator_le_sup (autImage L A) (autImage L A))
    exact hle hg
  obtain ⟨x, hx⟩ := exists_toAutImage_eq ⟨g, hgQ⟩
  rw [MonoidHom.mem_ker] at hu ⊢
  have hgu : (g : MulAut ↥A) u = ((toAutImage x) : MulAut ↥A) u := by
    have h := congrArg (fun y : ↥(autImage L A) => (y : MulAut ↥A) u) hx
    simpa using h.symm
  rw [hgu]
  change e3q h h2 (((toAutImage x) : MulAut ↥A) u) = 1
  rw [e3q_toAutImage h h2 x u]
  simpa [e3qHom] using hu

theorem Hyp.mul_self_mem_A_of_mem_R₀ (h : Hyp G L A T z t) (h2 : E2Facts L A z) {r : G}
    (hr : r ∈ R₀ A z) : r * r ∈ A := by
  have hU := h.jc.module.irreducible_derived (e3qHom h h2).ker (e3qHom_ker_invariant h h2)
  rcases hU with hbot | htop
  · exfalso
    have hcard := Subgroup.card_ker_mul_card_range (e3qHom h h2)
    rw [hbot, Subgroup.card_bot, one_mul] at hcard
    have hle : Nat.card (e3qHom h h2).range ≤ 2 := by
      calc Nat.card (e3qHom h h2).range ≤ Nat.card (Multiplicative (ZMod 2)) :=
            Nat.card_le_card_of_injective
              (fun x : ↥((e3qHom h h2).range) => (x.1 : Multiplicative (ZMod 2)))
              (fun x y hxy => Subtype.ext hxy)
        _ = 2 := by
            rw [Nat.card_eq_fintype_card]
            change Fintype.card (ZMod 2) = 2
            rw [ZMod.card]
    have hA2 : Nat.card A = 2 ^ 10 := h.jc.module.card
    rw [hA2] at hcard
    have h1024 : 2 ^ 10 ≤ 2 := by
      rw [← hcard]
      exact hle
    norm_num at h1024
  · have hq1 : e3qHom h h2 = 1 := by
      ext a
      have ha : a ∈ (e3qHom h h2).ker := by rw [htop]; exact Subgroup.mem_top a
      simpa using ha
    have hδ : delta z r ∈ A := h2.delta_mem hr
    have hq : e3q h h2 ⟨delta z r, hδ⟩ = 1 := by
      have h := congrFun (congrArg (fun f : ↥A →* Multiplicative (ZMod 2) =>
        (f : ↥A → Multiplicative (ZMod 2))) hq1) ⟨delta z r, hδ⟩
      simpa [e3qHom] using h
    rw [e3q_eq_of_delta h h2 hr rfl] at hq
    exact (e3tauG_eq_one_iff h (e3_sq_mem_B h h2 hr)).mp hq

private theorem e3_A_le_R₀ (h : Hyp G L A T z t) : A ≤ R₀ A z :=
  fun _ ha => h.B_le_R₀ (mem_sup_left ha)

private theorem e3_A_subgroupOf_le_center (h : Hyp G L A T z t) :
    A.subgroupOf (R₀ A z) ≤ Subgroup.center (R₀ A z) := by
  intro a ha
  rw [Subgroup.mem_center_iff]
  intro r
  apply Subtype.ext
  exact (mem_centralizer_iff.1 r.2.2 (a : G) ha).symm

private instance e3_normal_A_subgroupOf_R₀ :
    (A.subgroupOf (R₀ A z)).Normal :=
  Subgroup.normal_of_le_center (by
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro r
    apply Subtype.ext
    exact (mem_centralizer_iff.1 r.2.2 (a : G) ha).symm)

private theorem e3_elemAb_quotR₀ (h : Hyp G L A T z t) (h2 : E2Facts L A z) :
    IsElementaryAbelian 2 (↥(R₀ A z) ⧸ (A.subgroupOf (R₀ A z))) := by
  classical
  letI : (A.subgroupOf (R₀ A z)).Normal :=
    Subgroup.normal_of_le_center (e3_A_subgroupOf_le_center h)
  have hcomm : ∀ x y : ↥(R₀ A z) ⧸ (A.subgroupOf (R₀ A z)), x * y = y * x := by
    intro x y
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    show ((r * s)⁻¹ * (s * r) : ↥(R₀ A z)) ∈ A.subgroupOf (R₀ A z)
    rw [Subgroup.mem_subgroupOf]
    change ((r : G) * (s : G))⁻¹ * ((s : G) * (r : G)) ∈ A
    have hc : ⁅((r : G))⁻¹, (s : G)⁆ ∈ A :=
      h.commutator_mem_A_of_mem_R₀ h2 (inv_mem r.2) s.2
    have hsc : ⁅((r : G))⁻¹, (s : G)⁆ * (s : G) = (s : G) * ⁅((r : G))⁻¹, (s : G)⁆ :=
      mem_centralizer_iff.1 s.2.2 ⁅((r : G))⁻¹, (s : G)⁆ hc
    have hEq : ((r : G) * (s : G))⁻¹ * ((s : G) * (r : G)) =
        (s : G)⁻¹ * ⁅((r : G))⁻¹, (s : G)⁆ * (s : G) := by
      rw [commutatorElement_def]
      group
    rw [hEq]
    have hcent : (s : G)⁻¹ * ⁅((r : G))⁻¹, (s : G)⁆ * (s : G) = ⁅((r : G))⁻¹, (s : G)⁆ := by
      calc (s : G)⁻¹ * ⁅((r : G))⁻¹, (s : G)⁆ * (s : G) =
          (s : G)⁻¹ * (⁅((r : G))⁻¹, (s : G)⁆ * (s : G)) := by group
        _ = (s : G)⁻¹ * ((s : G) * ⁅((r : G))⁻¹, (s : G)⁆) := by rw [hsc]
        _ = ⁅((r : G))⁻¹, (s : G)⁆ := by group
    rw [hcent]
    exact hc
  have hexp : Monoid.exponent (↥(R₀ A z) ⧸ (A.subgroupOf (R₀ A z))) ∣ 2 := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro q
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow]
    refine (QuotientGroup.eq_one_iff (r ^ 2 : ↥(R₀ A z))).mpr ?_
    rw [Subgroup.mem_subgroupOf]
    simpa [pow_two] using h.mul_self_mem_A_of_mem_R₀ h2 r.2
  exact { is_comm := ⟨hcomm⟩, exponent_dvd_p := hexp }

private theorem e3f_zero (f : Additive (↥(R₀ A z) ⧸ (A.subgroupOf (R₀ A z))) → ZMod 2)
    (hfadd : ∀ x y, f (x + y) = f x + f y) : f 0 = 0 := by
  have h := hfadd 0 0
  rw [zero_add] at h
  have h2 : f 0 + f 0 = 0 := CharTwo.add_self_eq_zero _
  rwa [h2] at h

private noncomputable def e3phi (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (f : Additive (↥(R₀ A z) ⧸ (A.subgroupOf (R₀ A z))) → ZMod 2)
    (hfadd : ∀ x y, f (x + y) = f x + f y) :
    ↥(R₀ A z) →* Multiplicative (ZMod 2) where
  toFun r :=
    Multiplicative.ofAdd
      (f (Additive.ofMul (QuotientGroup.mk' (A.subgroupOf (R₀ A z)) r)))
  map_one' := by
    show Multiplicative.ofAdd
      (f (Additive.ofMul (QuotientGroup.mk' (A.subgroupOf (R₀ A z)) 1))) = 1
    rw [map_one, ofMul_one, e3f_zero f hfadd, ofAdd_zero]
  map_mul' r s := by
    show Multiplicative.ofAdd
        (f (Additive.ofMul (QuotientGroup.mk' (A.subgroupOf (R₀ A z)) (r * s)))) =
      Multiplicative.ofAdd
        (f (Additive.ofMul (QuotientGroup.mk' (A.subgroupOf (R₀ A z)) r))) *
      Multiplicative.ofAdd
        (f (Additive.ofMul (QuotientGroup.mk' (A.subgroupOf (R₀ A z)) s)))
    rw [map_mul, ofMul_mul, hfadd, ofAdd_add]

private theorem e3phi_A (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (f : Additive (↥(R₀ A z) ⧸ (A.subgroupOf (R₀ A z))) → ZMod 2)
    (hfadd : ∀ x y, f (x + y) = f x + f y) {a : G} (ha : a ∈ A) :
    e3phi h h2 f hfadd ⟨a, e3_A_le_R₀ h ha⟩ = 1 := by
  show Multiplicative.ofAdd
    (f (Additive.ofMul (QuotientGroup.mk' (A.subgroupOf (R₀ A z)) ⟨a, e3_A_le_R₀ h ha⟩))) = 1
  have hmk : QuotientGroup.mk' (A.subgroupOf (R₀ A z)) ⟨a, e3_A_le_R₀ h ha⟩ = 1 :=
    (QuotientGroup.eq_one_iff (⟨a, e3_A_le_R₀ h ha⟩ : ↥(R₀ A z))).mpr
      (by rw [Subgroup.mem_subgroupOf]; exact ha)
  rw [hmk, ofMul_one, e3f_zero f hfadd, ofAdd_zero]

private theorem e3phi_z (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (f : Additive (↥(R₀ A z) ⧸ (A.subgroupOf (R₀ A z))) → ZMod 2)
    (hfadd : ∀ x y, f (x + y) = f x + f y)
    (hf : f (Additive.ofMul
      (QuotientGroup.mk' (A.subgroupOf (R₀ A z)) ⟨z, e3_z_mem_R₀ h⟩)) = 1) :
    e3phi h h2 f hfadd ⟨z, e3_z_mem_R₀ h⟩ = e3g := by
  show Multiplicative.ofAdd
    (f (Additive.ofMul (QuotientGroup.mk' (A.subgroupOf (R₀ A z)) ⟨z, e3_z_mem_R₀ h⟩))) = e3g
  rw [hf]
  rfl

private theorem e3_exists_phi (h : Hyp G L A T z t) (h2 : E2Facts L A z) :
    ∃ φ : ↥(R₀ A z) →* Multiplicative (ZMod 2),
      (∀ a : ↥A, φ ⟨a, e3_A_le_R₀ h a.2⟩ = 1) ∧
      φ ⟨z, e3_z_mem_R₀ h⟩ = e3g := by
  classical
  letI : IsElementaryAbelian 2 (↥(R₀ A z) ⧸ (A.subgroupOf (R₀ A z))) :=
    e3_elemAb_quotR₀ h h2
  let Q := ↥(R₀ A z) ⧸ (A.subgroupOf (R₀ A z))
  let v : Additive Q :=
    Additive.ofMul (QuotientGroup.mk' (A.subgroupOf (R₀ A z)) ⟨z, e3_z_mem_R₀ h⟩)
  have hv : v ≠ 0 := by
    intro h0
    have hmk : QuotientGroup.mk' (A.subgroupOf (R₀ A z)) ⟨z, e3_z_mem_R₀ h⟩ = 1 := by
      apply Additive.ofMul.injective
      simpa only [ofMul_one] using h0
    have hmem : (⟨z, e3_z_mem_R₀ h⟩ : ↥(R₀ A z)) ∈ A.subgroupOf (R₀ A z) :=
      (QuotientGroup.eq_one_iff _).mp hmk
    exact e3_z_not_mem_A h (Subgroup.mem_subgroupOf.mp hmem)
  let b := Module.Basis.ofVectorSpace (ZMod 2) (Additive Q)
  have hrepr : b.repr v ≠ 0 := by
    intro h0
    apply hv
    have hlin := b.linearCombination_repr v
    rw [h0] at hlin
    simpa using hlin.symm
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hrepr
  have hvi : b.repr v i ≠ 0 := by
    rwa [Finsupp.mem_support_iff] at hi
  have hvi1 : b.repr v i = 1 := by
    have hlt := ZMod.val_lt (b.repr v i)
    have hne : (b.repr v i).val ≠ 0 := by
      intro h0
      exact hvi ((ZMod.val_eq_zero _).mp h0)
    have hval : (b.repr v i).val = 1 := by omega
    rwa [ZMod.val_eq_one (by norm_num)] at hval
  let F : Additive Q →ₗ[ZMod 2] ZMod 2 := Module.Basis.coord b i
  have hF : F v = 1 := by
    show Module.Basis.coord b i v = 1
    rw [Module.Basis.coord_apply, hvi1]
  refine ⟨e3phi h h2 (fun x => F x) (fun x y => F.map_add x y), ?_, ?_⟩
  · intro a
    exact e3phi_A h h2 (fun x => F x) (fun x y => F.map_add x y) a.2
  · exact e3phi_z h h2 (fun x => F x) (fun x y => F.map_add x y) hF

private noncomputable def e3psi (φ : ↥(R₀ A z) →* Multiplicative (ZMod 2))
    (r : ↥(R₀ A z)) : ZMod 2 := (φ r).toAdd

private theorem e3psi_mul (φ : ↥(R₀ A z) →* Multiplicative (ZMod 2))
    (r s : ↥(R₀ A z)) : e3psi φ (r * s) = e3psi φ r + e3psi φ s := by
  show (φ (r * s)).toAdd = (φ r).toAdd + (φ s).toAdd
  rw [map_mul, toAdd_mul]

private theorem e3psi_A (h : Hyp G L A T z t) (φ : ↥(R₀ A z) →* Multiplicative (ZMod 2))
    (hφA : ∀ a : ↥A, φ ⟨a, e3_A_le_R₀ h a.2⟩ = 1) {c : G} (hc : c ∈ A) :
    e3psi φ ⟨c, e3_A_le_R₀ h hc⟩ = 0 := by
  show (φ ⟨c, e3_A_le_R₀ h hc⟩).toAdd = 0
  rw [show φ ⟨c, e3_A_le_R₀ h hc⟩ = 1 from by simpa using hφA ⟨c, hc⟩, toAdd_one]

private noncomputable def e3conjR (h : Hyp G L A T z t)
    (x : ↥(L ⊓ normalizer (A : Set G))) (r : ↥(R₀ A z)) : ↥(R₀ A z) :=
  ⟨(x : G)⁻¹ * (r : G) * (x : G), by
    simpa using e3_conj_mem_R₀ h (inv_mem x.2) r.2⟩

private theorem e3conjR_mul (h : Hyp G L A T z t)
    (x : ↥(L ⊓ normalizer (A : Set G))) (r s : ↥(R₀ A z)) :
    e3conjR h x (r * s) = e3conjR h x r * e3conjR h x s := by
  apply Subtype.ext
  simp only [e3conjR, Subgroup.coe_mul]
  group

private noncomputable def e3psiConj (h : Hyp G L A T z t)
    (φ : ↥(R₀ A z) →* Multiplicative (ZMod 2))
    (x : ↥(L ⊓ normalizer (A : Set G))) (r : ↥(R₀ A z)) : ZMod 2 :=
  e3psi φ (e3conjR h x r)

private theorem e3psiConj_mul (h : Hyp G L A T z t)
    (φ : ↥(R₀ A z) →* Multiplicative (ZMod 2))
    (x : ↥(L ⊓ normalizer (A : Set G))) (r s : ↥(R₀ A z)) :
    e3psiConj h φ x (r * s) = e3psiConj h φ x r + e3psiConj h φ x s := by
  unfold e3psiConj
  rw [e3conjR_mul, e3psi_mul]

private theorem e3psiConj_A (h : Hyp G L A T z t)
    (φ : ↥(R₀ A z) →* Multiplicative (ZMod 2))
    (hφA : ∀ a : ↥A, φ ⟨a, e3_A_le_R₀ h a.2⟩ = 1)
    (x : ↥(L ⊓ normalizer (A : Set G))) {c : G} (hc : c ∈ A) :
    e3psiConj h φ x ⟨c, e3_A_le_R₀ h hc⟩ = 0 := by
  unfold e3psiConj
  have hc' : (x : G)⁻¹ * c * (x : G) ∈ A := by
    simpa only [Subgroup.coe_inv, inv_inv] using
      (mem_normalizer_iff.1 (inv_mem x.2.2) c).1 hc
  exact e3psi_A h φ hφA hc'

private noncomputable def e3gammaAt (h : Hyp G L A T z t)
    (φ : ↥(R₀ A z) →* Multiplicative (ZMod 2))
    (x : ↥(L ⊓ normalizer (A : Set G))) (r : ↥(R₀ A z)) : ZMod 2 :=
  e3psiConj h φ x r + e3psi φ r

private noncomputable def e3gamma (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (φ : ↥(R₀ A z) →* Multiplicative (ZMod 2))
    (x : ↥(L ⊓ normalizer (A : Set G))) (a : ↥A) : ZMod 2 :=
  e3gammaAt h φ x (e3deltaSection h2 a)

private theorem e3gammaAt_eq_of_delta (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (φ : ↥(R₀ A z) →* Multiplicative (ZMod 2))
    (hφA : ∀ a : ↥A, φ ⟨a, e3_A_le_R₀ h a.2⟩ = 1)
    (x : ↥(L ⊓ normalizer (A : Set G))) {r r' : ↥(R₀ A z)}
    (hδ : delta z (r' : G) = delta z (r : G)) :
    e3gammaAt h φ x r' = e3gammaAt h φ x r := by
  let b : G := (r' : G) * (r : G)⁻¹
  have hbR : b ∈ R₀ A z := mul_mem r'.2 (inv_mem r.2)
  have hbB : b ∈ B A z := by
    apply (h.delta_eq_one_iff h2 hbR).mp
    have h1 : delta z ((r' : G) * (r : G)⁻¹) =
        delta z (r' : G) * delta z (r : G)⁻¹ := h2.delta_mul r'.2 (inv_mem r.2)
    rw [h1, hδ, delta_inv_of_conj_mem h2.conj_mem r.2, mul_inv_cancel]
  have hr'eq : (r' : G) = b * (r : G) := by
    simp only [b]
    group
  let xb : G := (x : G)⁻¹ * b * (x : G)
  have hxbA : xb * b⁻¹ ∈ A := by
    simpa [xb] using e3_conj_N_B_mem_A h h2 (inv_mem x.2) hbB
  have hxbB : xb ∈ B A z := by
    have heq : xb = (xb * b⁻¹) * b := by group
    rw [heq]
    exact mul_mem (mem_sup_left hxbA) hbB
  have hxbR : xb ∈ R₀ A z := h.B_le_R₀ hxbB
  unfold e3gammaAt
  have h1 : e3psiConj h φ x r' = e3psi φ ⟨xb, hxbR⟩ + e3psiConj h φ x r := by
    unfold e3psiConj
    have hEq : e3conjR h x r' = ⟨xb, hxbR⟩ * e3conjR h x r := by
      apply Subtype.ext
      simp only [e3conjR, Subgroup.coe_mul, xb]
      rw [hr'eq]
      group
    rw [hEq, e3psi_mul]
  have h2' : e3psi φ r' = e3psi φ ⟨b, hbR⟩ + e3psi φ r := by
    rw [← e3psi_mul φ ⟨b, hbR⟩ r]
    congr 1
    apply Subtype.ext
    exact hr'eq
  have h3 : e3psi φ ⟨xb, hxbR⟩ = e3psi φ ⟨b, hbR⟩ := by
    have heq : xb = (xb * b⁻¹) * b := by group
    have hmemB : (xb * b⁻¹) * b ∈ B A z := mul_mem (mem_sup_left hxbA) hbB
    calc e3psi φ ⟨xb, hxbR⟩
        = e3psi φ ⟨(xb * b⁻¹) * b, h.B_le_R₀ hmemB⟩ := by
            congr 1
            apply Subtype.ext
            exact heq
      _ = e3psi φ (⟨xb * b⁻¹, h.B_le_R₀ (mem_sup_left hxbA)⟩ * ⟨b, hbR⟩) := rfl
      _ = e3psi φ ⟨xb * b⁻¹, h.B_le_R₀ (mem_sup_left hxbA)⟩ + e3psi φ ⟨b, hbR⟩ :=
            e3psi_mul φ _ _
      _ = 0 + e3psi φ ⟨b, hbR⟩ := by rw [e3psi_A h φ hφA hxbA]
      _ = e3psi φ ⟨b, hbR⟩ := zero_add _
  rw [h1, h2', h3]
  ring_nf
  rw [show (2 : ZMod 2) = 0 from by decide]
  simp

private theorem e3gamma_eq_of_delta (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (φ : ↥(R₀ A z) →* Multiplicative (ZMod 2))
    (hφA : ∀ a : ↥A, φ ⟨a, e3_A_le_R₀ h a.2⟩ = 1)
    (x : ↥(L ⊓ normalizer (A : Set G))) {a : ↥A} {r : ↥(R₀ A z)}
    (hδ : delta z (r : G) = (a : G)) :
    e3gamma h h2 φ x a = e3gammaAt h φ x r := by
  unfold e3gamma
  exact e3gammaAt_eq_of_delta h h2 φ hφA x (by rw [e3deltaSection_val]; exact hδ.symm)

private theorem e3gamma_add (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (φ : ↥(R₀ A z) →* Multiplicative (ZMod 2))
    (hφA : ∀ a : ↥A, φ ⟨a, e3_A_le_R₀ h a.2⟩ = 1)
    (x : ↥(L ⊓ normalizer (A : Set G))) (a b : ↥A) :
    e3gamma h h2 φ x (a * b) = e3gamma h h2 φ x a + e3gamma h h2 φ x b := by
  let r : ↥(R₀ A z) := e3deltaSection h2 a
  let s : ↥(R₀ A z) := e3deltaSection h2 b
  have hδrs : delta z ((r * s : ↥(R₀ A z)) : G) = ((a * b : ↥A) : G) := by
    show delta z ((r : G) * (s : G)) = _
    rw [h2.delta_mul r.2 s.2, e3deltaSection_val h2 a, e3deltaSection_val h2 b]
    rfl
  rw [e3gamma_eq_of_delta h h2 φ hφA x hδrs,
    e3gamma_eq_of_delta h h2 φ hφA x (e3deltaSection_val h2 a),
    e3gamma_eq_of_delta h h2 φ hφA x (e3deltaSection_val h2 b)]
  unfold e3gammaAt
  rw [e3psiConj_mul, e3psi_mul φ _ _]
  have hr : e3deltaSection h2 a = r := rfl
  have hs : e3deltaSection h2 b = s := rfl
  rw [hr, hs]
  ring_nf

private theorem e3gamma_cocycle (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (φ : ↥(R₀ A z) →* Multiplicative (ZMod 2))
    (hφA : ∀ a : ↥A, φ ⟨a, e3_A_le_R₀ h a.2⟩ = 1)
    (x y : ↥(L ⊓ normalizer (A : Set G))) (a : ↥A) :
    e3gamma h h2 φ (x * y) a =
      e3gamma h h2 φ x a + e3gamma h h2 φ y (((toAutImage x : MulAut ↥A)⁻¹) a) := by
  let r : ↥(R₀ A z) := e3deltaSection h2 a
  let s : ↥(R₀ A z) := e3conjR h x r
  have hxinv : (toAutImage x : MulAut ↥A)⁻¹ = toAutImage (x⁻¹) := by
    have hh : toAutImage x * toAutImage (x⁻¹) = 1 := by
      rw [← toAutImage_mul, mul_inv_cancel, toAutImage_one]
    have hh' : (toAutImage x : MulAut ↥A) * (toAutImage (x⁻¹) : MulAut ↥A) = 1 := by
      simpa using congrArg Subtype.val hh
    exact inv_eq_of_mul_eq_one_right hh'
  have hδs : delta z (s : G) = ((((toAutImage x : MulAut ↥A)⁻¹) a : ↥A) : G) := by
    show delta z ((x : G)⁻¹ * (r : G) * (x : G)) = _
    have hdc : delta z ((x : G)⁻¹ * (r : G) * (x : G)) =
        (x : G)⁻¹ * delta z (r : G) * (x : G) := by
      simpa only [inv_inv] using
        (h.delta_conj (x := (x : G)⁻¹) (r := r) (inv_mem x.2).1)
    rw [hdc, e3deltaSection_val h2 a, hxinv]
    simpa [coe_toAutImage] using (conjN_apply (x⁻¹) a).symm
  have hδsec : delta z (((e3deltaSection h2 a) : ↥(R₀ A z)) : G) = (a : G) :=
    e3deltaSection_val h2 a
  rw [e3gamma_eq_of_delta h h2 φ hφA (x * y) hδsec,
    e3gamma_eq_of_delta h h2 φ hφA y hδs,
    e3gamma_eq_of_delta h h2 φ hφA x hδsec]
  unfold e3gammaAt e3psiConj
  have hxyEq : e3conjR h (x * y) r = e3conjR h y s := by
    apply Subtype.ext
    simp only [e3conjR, s, Subgroup.coe_mul]
    group
  have hsEq : e3conjR h x r = s := rfl
  rw [hxyEq, hsEq]
  ring_nf
  rw [show (2 : ZMod 2) = 0 from by decide]
  simp

private theorem e3gamma_eq_of_conjN (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (φ : ↥(R₀ A z) →* Multiplicative (ZMod 2))
    (hφA : ∀ a : ↥A, φ ⟨a, e3_A_le_R₀ h a.2⟩ = 1)
    {x y : ↥(L ⊓ normalizer (A : Set G))} (hxy : conjN L A x = conjN L A y)
    (a : ↥A) : e3gamma h h2 φ x a = e3gamma h h2 φ y a := by
  have hker : conjN L A (x⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, hxy]
    group
  have hmem : (((x⁻¹ * y : ↥(L ⊓ normalizer (A : Set G))) : G)) ∈ A :=
    (conjN_eq_one_iff h.jc.centralizer_eq (x⁻¹ * y)).mp hker
  let a0 : G := (((x⁻¹ * y : ↥(L ⊓ normalizer (A : Set G))) : G))
  have ha0A : a0 ∈ A := hmem
  have hy_eq : (y : G) = (x : G) * a0 := by
    change (y : G) = (x : G) * (((x⁻¹ * y : ↥(L ⊓ normalizer (A : Set G))) : G))
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  let r : ↥(R₀ A z) := e3deltaSection h2 a
  rw [e3gamma_eq_of_delta h h2 φ hφA x (e3deltaSection_val h2 a),
    e3gamma_eq_of_delta h h2 φ hφA y (e3deltaSection_val h2 a)]
  unfold e3gammaAt e3psiConj
  have hcomm' : a0 * ((x : G)⁻¹ * (r : G) * (x : G)) =
      ((x : G)⁻¹ * (r : G) * (x : G)) * a0 := by
    simpa only [inv_inv] using
      (mem_centralizer_iff.1 (e3_conj_mem_R₀ h (inv_mem x.2) r.2).2 a0 ha0A)
  have hyr : (y : G)⁻¹ * (r : G) * (y : G) = (x : G)⁻¹ * (r : G) * (x : G) := by
    rw [hy_eq]
    calc ((x : G) * a0)⁻¹ * (r : G) * ((x : G) * a0)
        = a0⁻¹ * ((x : G)⁻¹ * (r : G) * (x : G)) * a0 := by group
      _ = ((x : G)⁻¹ * (r : G) * (x : G)) := by
          rw [show a0⁻¹ * ((x : G)⁻¹ * (r : G) * (x : G)) * a0 =
              a0⁻¹ * (((x : G)⁻¹ * (r : G) * (x : G)) * a0) by group]
          rw [← hcomm']
          group
  have hyrEq : e3conjR h y r = e3conjR h x r := by
    apply Subtype.ext
    simp only [e3conjR]
    exact hyr
  rw [hyrEq]

private noncomputable def e3gamma' (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (φ : ↥(R₀ A z) →* Multiplicative (ZMod 2)) :
    ↥(autImage L A) → ↥A → ZMod 2 :=
  descend (fun x => e3gamma h h2 φ x)

private theorem e3gamma'_toAutImage (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (φ : ↥(R₀ A z) →* Multiplicative (ZMod 2))
    (hφA : ∀ a : ↥A, φ ⟨a, e3_A_le_R₀ h a.2⟩ = 1)
    (x : ↥(L ⊓ normalizer (A : Set G))) :
    e3gamma' h h2 φ (toAutImage x) = e3gamma h h2 φ x :=
  descend_toAutImage (fun x => e3gamma h h2 φ x)
    (fun x y hxy => funext (fun a => e3gamma_eq_of_conjN h h2 φ hφA hxy a)) x

private theorem e3gamma'_add (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (φ : ↥(R₀ A z) →* Multiplicative (ZMod 2))
    (hφA : ∀ a : ↥A, φ ⟨a, e3_A_le_R₀ h a.2⟩ = 1)
    (g : ↥(autImage L A)) (a b : ↥A) :
    e3gamma' h h2 φ g (a * b) = e3gamma' h h2 φ g a + e3gamma' h h2 φ g b := by
  obtain ⟨x, rfl⟩ := exists_toAutImage_eq g
  rw [e3gamma'_toAutImage h h2 φ hφA x]
  exact e3gamma_add h h2 φ hφA x a b

private theorem e3gamma'_cocycle (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (φ : ↥(R₀ A z) →* Multiplicative (ZMod 2))
    (hφA : ∀ a : ↥A, φ ⟨a, e3_A_le_R₀ h a.2⟩ = 1)
    (g g' : ↥(autImage L A)) (a : ↥A) :
    e3gamma' h h2 φ (g * g') a =
      e3gamma' h h2 φ g a + e3gamma' h h2 φ g' (((g : MulAut ↥A)⁻¹) a) := by
  obtain ⟨x, rfl⟩ := exists_toAutImage_eq g
  obtain ⟨y, rfl⟩ := exists_toAutImage_eq g'
  rw [← toAutImage_mul, e3gamma'_toAutImage h h2 φ hφA (x * y),
    e3gamma'_toAutImage h h2 φ hφA x, e3gamma'_toAutImage h h2 φ hφA y]
  exact e3gamma_cocycle h h2 φ hφA x y a

private theorem e3f_one (f : ↥A → ZMod 2) (hfadd : ∀ a b, f (a * b) = f a + f b) :
    f 1 = 0 := by
  have h := hfadd 1 1
  rw [mul_one] at h
  have h2 : f 1 + f 1 = 0 := CharTwo.add_self_eq_zero _
  rwa [h2] at h

private noncomputable def e3phi' (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (φ : ↥(R₀ A z) →* Multiplicative (ZMod 2)) (f : ↥A → ZMod 2)
    (r : ↥(R₀ A z)) : ZMod 2 :=
  e3psi φ r + f ⟨delta z (r : G), h2.delta_mem r.2⟩

private theorem e3phi'_add (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (φ : ↥(R₀ A z) →* Multiplicative (ZMod 2)) (f : ↥A → ZMod 2)
    (hfadd : ∀ a b, f (a * b) = f a + f b) (r s : ↥(R₀ A z)) :
    e3phi' h h2 φ f (r * s) = e3phi' h h2 φ f r + e3phi' h h2 φ f s := by
  unfold e3phi'
  rw [e3psi_mul]
  change e3psi φ r + e3psi φ s +
      f ⟨delta z ((r : G) * (s : G)), h2.delta_mem (mul_mem r.2 s.2)⟩ =
    e3psi φ r + f ⟨delta z (r : G), h2.delta_mem r.2⟩ +
      (e3psi φ s + f ⟨delta z (s : G), h2.delta_mem s.2⟩)
  have hδeq : (⟨delta z ((r : G) * (s : G)), h2.delta_mem (mul_mem r.2 s.2)⟩ : ↥A) =
      ⟨delta z (r : G), h2.delta_mem r.2⟩ * ⟨delta z (s : G), h2.delta_mem s.2⟩ := by
    apply Subtype.ext
    exact h2.delta_mul r.2 s.2
  rw [hδeq, hfadd]
  ring_nf

private theorem e3phi'_A (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (φ : ↥(R₀ A z) →* Multiplicative (ZMod 2))
    (hφA : ∀ a : ↥A, φ ⟨a, e3_A_le_R₀ h a.2⟩ = 1)
    (f : ↥A → ZMod 2) (hfadd : ∀ a b, f (a * b) = f a + f b) {a : G} (ha : a ∈ A) :
    e3phi' h h2 φ f ⟨a, e3_A_le_R₀ h ha⟩ = 0 := by
  unfold e3phi'
  have hψ : e3psi φ ⟨a, e3_A_le_R₀ h ha⟩ = 0 := e3psi_A h φ hφA ha
  have hδ : delta z a = 1 :=
    (h.delta_eq_one_iff h2 (e3_A_le_R₀ h ha)).mpr (mem_sup_left ha)
  have hδ' : (⟨delta z a, h2.delta_mem (e3_A_le_R₀ h ha)⟩ : ↥A) = 1 := by
    apply Subtype.ext
    show delta z a = ((1 : ↥A) : G)
    rw [hδ]
    rfl
  rw [hψ, hδ', e3f_one f hfadd, add_zero]

private theorem e3phi'_z (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (φ : ↥(R₀ A z) →* Multiplicative (ZMod 2))
    (hφz : φ ⟨z, e3_z_mem_R₀ h⟩ = e3g)
    (f : ↥A → ZMod 2) (hfadd : ∀ a b, f (a * b) = f a + f b) :
    e3phi' h h2 φ f ⟨z, e3_z_mem_R₀ h⟩ = 1 := by
  unfold e3phi'
  have hψ : e3psi φ ⟨z, e3_z_mem_R₀ h⟩ = 1 := by
    show (φ ⟨z, e3_z_mem_R₀ h⟩).toAdd = 1
    rw [hφz]
    rfl
  have hδ : delta z ((⟨z, e3_z_mem_R₀ h⟩ : ↥(R₀ A z)) : G) = 1 := by
    show delta z z = 1
    rw [delta]
    group
  have hδ' : (⟨delta z ((⟨z, e3_z_mem_R₀ h⟩ : ↥(R₀ A z)) : G),
      h2.delta_mem (e3_z_mem_R₀ h)⟩ : ↥A) = 1 := by
    apply Subtype.ext
    show delta z ((⟨z, e3_z_mem_R₀ h⟩ : ↥(R₀ A z)) : G) = ((1 : ↥A) : G)
    rw [hδ]
    rfl
  rw [hψ, hδ', e3f_one f hfadd, add_zero]

private theorem e3phi'_invariant (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (φ : ↥(R₀ A z) →* Multiplicative (ZMod 2))
    (hφA : ∀ a : ↥A, φ ⟨a, e3_A_le_R₀ h a.2⟩ = 1)
    (f : ↥A → ZMod 2)
    (hf : ∀ g a, e3gamma' h h2 φ g a = f ((((g : MulAut ↥A)⁻¹) a)) + f a)
    (x : ↥(L ⊓ normalizer (A : Set G))) (r : ↥(R₀ A z)) :
    e3phi' h h2 φ f ⟨(x : G)⁻¹ * (r : G) * (x : G), by
      simpa using e3_conj_mem_R₀ h (inv_mem x.2) r.2⟩ = e3phi' h h2 φ f r := by
  let r' : ↥(R₀ A z) := ⟨(x : G)⁻¹ * (r : G) * (x : G), by
    simpa using e3_conj_mem_R₀ h (inv_mem x.2) r.2⟩
  let a : ↥A := ⟨delta z (r : G), h2.delta_mem r.2⟩
  have hxinv : (toAutImage x : MulAut ↥A)⁻¹ = toAutImage (x⁻¹) := by
    have hh : toAutImage x * toAutImage (x⁻¹) = 1 := by
      rw [← toAutImage_mul, mul_inv_cancel, toAutImage_one]
    have hh' : (toAutImage x : MulAut ↥A) * (toAutImage (x⁻¹) : MulAut ↥A) = 1 := by
      simpa using congrArg Subtype.val hh
    exact inv_eq_of_mul_eq_one_right hh'
  have hδr' : delta z (r' : G) = ((((toAutImage x : MulAut ↥A)⁻¹) a : ↥A) : G) := by
    show delta z ((x : G)⁻¹ * (r : G) * (x : G)) = _
    have hdc : delta z ((x : G)⁻¹ * (r : G) * (x : G)) =
        (x : G)⁻¹ * delta z (r : G) * (x : G) := by
      simpa only [inv_inv] using
        (h.delta_conj (x := (x : G)⁻¹) (r := r) (inv_mem x.2).1)
    rw [hdc, hxinv]
    simpa [coe_toAutImage] using (conjN_apply (x⁻¹) a).symm
  have hγ : e3gamma h h2 φ x a = e3gamma' h h2 φ (toAutImage x) a := by
    rw [e3gamma'_toAutImage h h2 φ hφA x]
  have hdual : e3gamma h h2 φ x a =
      f ((((toAutImage x : MulAut ↥A)⁻¹) a)) + f a := by
    rw [hγ]
    exact hf (toAutImage x) a
  have hgammaAt : e3gammaAt h φ x r = e3gamma h h2 φ x a :=
    (e3gamma_eq_of_delta h h2 φ hφA x rfl).symm
  have hpsi : e3psi φ r' + e3psi φ r = e3gammaAt h φ x r := rfl
  have hpsi' : e3psi φ r' = e3gammaAt h φ x r + e3psi φ r := by
    calc e3psi φ r' = e3psi φ r' + (e3psi φ r + e3psi φ r) := by
          rw [CharTwo.add_self_eq_zero, add_zero]
      _ = (e3psi φ r' + e3psi φ r) + e3psi φ r := by ring
      _ = e3gammaAt h φ x r + e3psi φ r := by rw [hpsi]
  have hδr'' : (⟨delta z (r' : G), h2.delta_mem r'.2⟩ : ↥A) =
      (((toAutImage x : MulAut ↥A)⁻¹) a) := by
    apply Subtype.ext
    exact hδr'
  unfold e3phi'
  rw [hpsi', hgammaAt, hdual, hδr'']
  rw [show (⟨delta z (r : G), h2.delta_mem r.2⟩ : ↥A) = a from rfl]
  ring_nf
  rw [show (2 : ZMod 2) = 0 from by decide]
  simp

private noncomputable def e3phi'Hom (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (φ : ↥(R₀ A z) →* Multiplicative (ZMod 2))
    (f : ↥A → ZMod 2) (hfadd : ∀ a b, f (a * b) = f a + f b) :
    ↥(R₀ A z) →* Multiplicative (ZMod 2) where
  toFun r := Multiplicative.ofAdd (e3phi' h h2 φ f r)
  map_one' := by
    show Multiplicative.ofAdd (e3phi' h h2 φ f 1) = 1
    have h : e3phi' h h2 φ f (1 : ↥(R₀ A z)) = 0 := by
      unfold e3phi'
      have hψ : e3psi φ (1 : ↥(R₀ A z)) = 0 := by
        show (φ 1).toAdd = 0
        rw [map_one, toAdd_one]
      have hδ : delta z ((1 : ↥(R₀ A z)) : G) = 1 := by
        show delta z 1 = 1
        simp [delta]
      have hδ' : (⟨delta z ((1 : ↥(R₀ A z)) : G),
          h2.delta_mem (one_mem (R₀ A z))⟩ : ↥A) = 1 := by
        apply Subtype.ext
        show delta z ((1 : ↥(R₀ A z)) : G) = ((1 : ↥A) : G)
        rw [hδ]
        rfl
      rw [hψ, hδ', e3f_one f hfadd, add_zero]
    rw [h, ofAdd_zero]
  map_mul' r s := by
    show Multiplicative.ofAdd (e3phi' h h2 φ f (r * s)) =
      Multiplicative.ofAdd (e3phi' h h2 φ f r) * Multiplicative.ofAdd (e3phi' h h2 φ f s)
    rw [e3phi'_add h h2 φ f hfadd, ofAdd_add]

private noncomputable def e3W (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (φ : ↥(R₀ A z) →* Multiplicative (ZMod 2))
    (f : ↥A → ZMod 2) (hfadd : ∀ a b, f (a * b) = f a + f b) : Subgroup G :=
  ((e3phi'Hom h h2 φ f hfadd).ker).map (R₀ A z).subtype

theorem Hyp.exists_e3Facts {G : Type} [Group G] [Finite G] {L A T : Subgroup G} {z t : G}
    (h : Hyp G L A T z t) (h2 : E2Facts L A z) : ∃ W : Subgroup G, E3Facts A z W := by
  classical
  obtain ⟨φ, hφA, hφz⟩ := e3_exists_phi h h2
  obtain ⟨f, hfadd, hf⟩ := h.jc.module.dual_cocycle (e3gamma' h h2 φ)
    (e3gamma'_add h h2 φ hφA) (e3gamma'_cocycle h h2 φ hφA)
  let W : Subgroup G := e3W h h2 φ f hfadd
  have hmemW : ∀ w : G, w ∈ W ↔
      ∃ r : ↥(R₀ A z), r ∈ (e3phi'Hom h h2 φ f hfadd).ker ∧ (r : G) = w := by
    intro w
    change w ∈ ((e3phi'Hom h h2 φ f hfadd).ker).map (R₀ A z).subtype ↔ _
    exact Subgroup.mem_map
  refine ⟨W, ?_⟩
  refine { A_le := ?_, le_R₀ := ?_, card := ?_, z_not_mem := ?_, M_le := ?_,
           mul_self_mem := ?_, commutator_mem := ?_ }
  · intro a ha
    rw [hmemW]
    refine ⟨⟨a, e3_A_le_R₀ h ha⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    change Multiplicative.ofAdd (e3phi' h h2 φ f ⟨a, e3_A_le_R₀ h ha⟩) = 1
    rw [e3phi'_A h h2 φ hφA f hfadd ha, ofAdd_zero]
  · intro w hw
    rw [hmemW] at hw
    obtain ⟨r, -, rfl⟩ := hw
    exact r.2
  · have hcardmap : Nat.card W = Nat.card (e3phi'Hom h h2 φ f hfadd).ker :=
      Subgroup.card_map_of_injective (R₀ A z).subtype_injective
    rw [hcardmap]
    have hcard := Subgroup.card_ker_mul_card_range (e3phi'Hom h h2 φ f hfadd)
    have hrange2 : Nat.card (e3phi'Hom h h2 φ f hfadd).range = 2 := by
      have hzmem : e3g ∈ ((e3phi'Hom h h2 φ f hfadd).range :
          Subgroup (Multiplicative (ZMod 2))) := by
        refine ⟨⟨z, e3_z_mem_R₀ h⟩, ?_⟩
        change Multiplicative.ofAdd (e3phi' h h2 φ f ⟨z, e3_z_mem_R₀ h⟩) = e3g
        rw [e3phi'_z h h2 φ hφz f hfadd]
        rfl
      haveI : Nontrivial ↥((e3phi'Hom h h2 φ f hfadd).range) := by
        refine ⟨⟨⟨1, one_mem _⟩, ⟨e3g, hzmem⟩, ?_⟩⟩
        intro hEq
        have hval := congrArg Subtype.val hEq
        exact e3g_ne_one (by simpa using hval.symm)
      have hle : Nat.card (e3phi'Hom h h2 φ f hfadd).range ≤ 2 := by
        calc Nat.card (e3phi'Hom h h2 φ f hfadd).range ≤ Nat.card (Multiplicative (ZMod 2)) :=
              Nat.card_le_card_of_injective
                (fun x : ↥((e3phi'Hom h h2 φ f hfadd).range) =>
                  (x.1 : Multiplicative (ZMod 2)))
                (fun x y hxy => Subtype.ext hxy)
          _ = 2 := by
              rw [Nat.card_eq_fintype_card]
              change Fintype.card (ZMod 2) = 2
              rw [ZMod.card]
      have hlt : 1 < Nat.card (e3phi'Hom h h2 φ f hfadd).range := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.one_lt_card
      omega
    rw [h2.card_R₀, hrange2] at hcard
    have hpow : (2 : ℕ) ^ 21 = 2 * 2 ^ 20 := by ring
    rw [hpow, mul_comm (2 : ℕ) (2 ^ 20)] at hcard
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) hcard
  · intro hzW
    rw [hmemW] at hzW
    obtain ⟨r, hrker, hrz⟩ := hzW
    rw [MonoidHom.mem_ker] at hrker
    have hrz' : r = ⟨z, e3_z_mem_R₀ h⟩ := Subtype.ext hrz
    rw [hrz'] at hrker
    have hzero : e3phi' h h2 φ f ⟨z, e3_z_mem_R₀ h⟩ = 0 := by
      have := congrArg Multiplicative.toAdd hrker
      simpa [e3phi'Hom] using this
    have hone := e3phi'_z h h2 φ hφz f hfadd
    rw [hone] at hzero
    exact one_ne_zero hzero
  · have hRnorm : R₀ A z ≤ normalizer (W : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro r hr w hw
      rw [hmemW] at hw
      obtain ⟨k, hk, rfl⟩ := hw
      rw [hmemW]
      refine ⟨⟨r * k * r⁻¹, mul_mem (mul_mem hr k.2) (inv_mem hr)⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker] at hk ⊢
      have hmap : e3phi'Hom h h2 φ f hfadd
          ⟨r * k * r⁻¹, mul_mem (mul_mem hr k.2) (inv_mem hr)⟩ =
          e3phi'Hom h h2 φ f hfadd ⟨r, hr⟩ * e3phi'Hom h h2 φ f hfadd k *
            (e3phi'Hom h h2 φ f hfadd ⟨r, hr⟩)⁻¹ := by
        rw [show (⟨r * k * r⁻¹, mul_mem (mul_mem hr k.2) (inv_mem hr)⟩ :
            ↥(R₀ A z)) = ⟨r, hr⟩ * k * ⟨r, hr⟩⁻¹ from rfl,
          map_mul, map_mul, map_inv]
      rw [hmap, hk, mul_one]
      exact mul_inv_cancel _
    have hNnorm : L ⊓ normalizer (A : Set G) ≤ normalizer (W : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro x hx w hw
      rw [hmemW] at hw
      obtain ⟨k, hk, rfl⟩ := hw
      rw [hmemW]
      have hxinv : x⁻¹ ∈ L ⊓ normalizer (A : Set G) :=
        (L ⊓ normalizer (A : Set G)).inv_mem hx
      have hxkR : x * k * x⁻¹ ∈ R₀ A z := by
        have h := e3_conj_mem_R₀ h hx (r := (k : G)) k.2
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
      refine ⟨⟨x * k * x⁻¹, hxkR⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker] at hk ⊢
      change Multiplicative.ofAdd
        (e3phi' h h2 φ f ⟨x * k * x⁻¹, hxkR⟩) = 1
      have hinv := e3phi'_invariant h h2 φ hφA f hf ⟨x⁻¹, hxinv⟩ k
      have hk' : e3phi' h h2 φ f k = 0 := by
        have := congrArg Multiplicative.toAdd hk
        simpa [e3phi'Hom] using this
      rw [show e3phi' h h2 φ f ⟨x * k * x⁻¹, hxkR⟩ = e3phi' h h2 φ f k from by
        simpa only [Subgroup.coe_inv, inv_inv] using hinv, hk', ofAdd_zero]
    intro m hm
    obtain ⟨r, hr, x, hx, rfl⟩ := h.exists_mul_of_mem_M h2 hm
    exact (normalizer (W : Set G)).mul_mem (hRnorm hr) (hNnorm hx)
  · intro w hw
    rw [hmemW] at hw
    obtain ⟨r, -, rfl⟩ := hw
    exact h.mul_self_mem_A_of_mem_R₀ h2 r.2
  · intro v hv w hw
    rw [hmemW] at hv hw
    obtain ⟨r, -, rfl⟩ := hv
    obtain ⟨s, -, rfl⟩ := hw
    exact h.commutator_mem_A_of_mem_R₀ h2 r.2 s.2

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
