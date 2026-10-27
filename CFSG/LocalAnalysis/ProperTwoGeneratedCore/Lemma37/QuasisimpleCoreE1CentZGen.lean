module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1FusionIndex
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1SigmaRBound

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

theorem map_inf_centralizer_e1EBar : (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)) ⊓
    Subgroup.centralizer (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)) =
      e1EBar (Subgroup.center J) u m y x := by
  have hb := d.caseC3BCD
  refine le_antisymm (fun s ⟨hs, hc⟩ => hb.mem_e1EBar_of_forall_commute hs fun t ht =>
    (Subgroup.mem_centralizer_iff.mp hc t ht).symm) fun s hs => ⟨hb.e1RBar_le
      (hb.e1EBar_le_e1RBar hs), Subgroup.mem_centralizer_iff.mpr fun t ht =>
        hb.commute_of_mem_e1EBar ht hs⟩

variable (htype : ∀ s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)),
  s ∉ (partCSylow T).map (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
    CaseC3.Genuine (Subgroup.center J) s)
include htype

theorem index_sup_centralizer_e1EBar :
    ((Subgroup.centralizer (e1EBar (Subgroup.center J) u m y x :
        Set (J ⧸ Subgroup.center J))).subgroupOf
      (Subgroup.normalizer (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J))) ⊔
      ((S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J))).subgroupOf
        (Subgroup.normalizer (e1EBar (Subgroup.center J) u m y x :
          Set (J ⧸ Subgroup.center J)))).index = 3 := by
  have hb := d.caseC3BCD
  have h1 : ((Subgroup.centralizer (e1EBar (Subgroup.center J) u m y x :
      Set (J ⧸ Subgroup.center J))).subgroupOf (Subgroup.normalizer
        (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)))).relIndex
      ((Subgroup.centralizer (e1EBar (Subgroup.center J) u m y x :
        Set (J ⧸ Subgroup.center J))).subgroupOf (Subgroup.normalizer
          (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J))) ⊔
        ((S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J))).subgroupOf
          (Subgroup.normalizer (e1EBar (Subgroup.center J) u m y x :
            Set (J ⧸ Subgroup.center J)))) = 8 := by
    rw [Subgroup.relIndex_sup_left, Subgroup.relIndex_subgroupOf d.map_le_normalizer_e1EBar,
      ← Subgroup.inf_relIndex_right, inf_comm, d.map_inf_centralizer_e1EBar]
    have h := Subgroup.relIndex_mul_card (e1EBar (Subgroup.center J) u m y x)
      ((S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)))
    rw [inf_eq_left.mpr (hb.e1EBar_le_e1RBar.trans hb.e1RBar_le), hb.card_e1EBar,
      hb.card_map_top] at h
    omega
  have h2 := Subgroup.relIndex_mul_index (le_sup_left : (Subgroup.centralizer
    (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J))).subgroupOf
      (Subgroup.normalizer (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J))) ≤
        _ ⊔ ((S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J))).subgroupOf
          (Subgroup.normalizer (e1EBar (Subgroup.center J) u m y x :
            Set (J ⧸ Subgroup.center J))))
  have h3 := d.relIndex_centralizer_normalizer_e1EBar htype
  rw [h1] at h2
  rw [Subgroup.relIndex] at h3
  omega

theorem exists_eq_pow_mul_of_mem_normalizer {τ : J ⧸ Subgroup.center J}
    (hτN : τ ∈ Subgroup.normalizer (e1EBar (Subgroup.center J) u m y x :
      Set (J ⧸ Subgroup.center J))) (hτa : ∃ a : ℕ, τ ^ 3 ^ a = 1)
    (hτC : τ ^ 3 ∈ Subgroup.centralizer (e1EBar (Subgroup.center J) u m y x :
      Set (J ⧸ Subgroup.center J)))
    (hτu : τ * (u : J ⧸ Subgroup.center J) * τ⁻¹ ≠ u) {n : J ⧸ Subgroup.center J}
    (hn : n ∈ Subgroup.normalizer (e1EBar (Subgroup.center J) u m y x :
      Set (J ⧸ Subgroup.center J))) :
    ∃ k : ℕ, k < 3 ∧ ∃ s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)),
      ∃ c ∈ Subgroup.centralizer (e1EBar (Subgroup.center J) u m y x :
        Set (J ⧸ Subgroup.center J)), n = τ ^ k * s * c := by
  have hb := d.caseC3BCD
  set E := e1EBar (Subgroup.center J) u m y x with hE
  set N := Subgroup.normalizer (E : Set (J ⧸ Subgroup.center J)) with hN
  set C := Subgroup.centralizer (E : Set (J ⧸ Subgroup.center J)) with hC
  set Sb := (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)) with hSb
  set K := C.subgroupOf N with hK
  set H := K ⊔ Sb.subgroupOf N with hH
  have hidx : H.index = 3 := d.index_sup_centralizer_e1EBar htype
  have hmem : ∀ h : N, h ∈ H → ∃ s ∈ Sb, ∃ c ∈ C, (h : J ⧸ Subgroup.center J) = s * c := by
    intro h hh
    rw [hH, sup_comm] at hh
    obtain ⟨s, hs, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hh
    exact ⟨s, hs, c, hc, rfl⟩
  have h4 : ∀ h : N, h ∈ H → h ^ 4 ∈ K := by
    intro h hh
    rw [hH, sup_comm] at hh
    obtain ⟨s, hs, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hh
    have hs4 : s ^ 4 = 1 :=
      Subtype.ext (by simpa using hb.pow_four_eq_one (Subgroup.mem_subgroupOf.mp hs))
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff c).mpr hc, mul_one, ← QuotientGroup.mk_pow, hs4,
      QuotientGroup.mk_one]
  obtain ⟨a, ha⟩ := hτa
  let τN : N := ⟨τ, hτN⟩
  have hτK : τN ∉ K := fun h => hτu (by
    have hc : (u : J ⧸ Subgroup.center J) * τ = τ * u :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp h) _ d.mem_e1EBar_gens.1
    rw [← hc, mul_inv_cancel_right])
  have hτH : τN ∉ H := by
    intro h
    refine hτK ?_
    obtain ⟨α, β, hαβ⟩ : IsCoprime ((4 : ℕ) : ℤ) ((3 ^ a : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right _ (by norm_num))
    have h1 : ((4 : ℕ) : ℤ) * α + ((3 ^ a : ℕ) : ℤ) * β = 1 := by linear_combination hαβ
    have hτa' : τN ^ 3 ^ a = 1 := Subtype.ext (by simpa using ha)
    have hτ : τN = (τN ^ 4) ^ α * (τN ^ 3 ^ a) ^ β :=
      calc τN = τN ^ (((4 : ℕ) : ℤ) * α + ((3 ^ a : ℕ) : ℤ) * β) := by rw [h1, zpow_one]
        _ = _ := by rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
    rw [hτ, hτa', one_zpow, mul_one]
    exact K.zpow_mem (h4 τN h) α
  have hτ3H : τN ^ 3 ∈ H :=
    Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr (by simpa [τN] using hτC))
  have hτ2H : τN ^ 2 ∉ H := fun h => hτH (by
    rw [show τN = (τN ^ 2) ^ 2 * (τN ^ 3)⁻¹ by group]
    exact H.mul_mem (H.pow_mem h 2) (H.inv_mem hτ3H))
  have key : ∀ k : ℕ, k % 3 ≠ 0 → τN ^ k ∉ H := by
    intro k hk hkH
    rw [show τN ^ k = (τN ^ 3) ^ (k / 3) * τN ^ (k % 3) by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]] at hkH
    have h2 := H.mul_mem (H.inv_mem (H.pow_mem hτ3H (k / 3))) hkH
    rw [inv_mul_cancel_left] at h2
    rcases (by omega : k % 3 = 1 ∨ k % 3 = 2) with h | h <;> rw [h] at h2
    · exact hτH (by simpa using h2)
    · exact hτ2H h2
  let f : Fin 3 → N ⧸ H := fun k => QuotientGroup.mk (τN ^ (k : ℕ))
  have hf : Function.Injective f := by
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have hij' := QuotientGroup.eq.mp hij
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · rw [show τN ^ (j : ℕ) = τN ^ (i : ℕ) * τN ^ ((j : ℕ) - i) by
        rw [← pow_add, Nat.add_sub_cancel' h.le], inv_mul_cancel_left] at hij'
      exact key _ (by omega) hij'
    · rw [show τN ^ (i : ℕ) = τN ^ (j : ℕ) * τN ^ ((i : ℕ) - j) by
        rw [← pow_add, Nat.add_sub_cancel' h.le], mul_inv_rev, mul_assoc, inv_mul_cancel,
        mul_one, inv_mem_iff] at hij'
      exact key _ (by omega) hij'
  have hbij := hf.bijective_of_nat_card_le (by
    rw [show Nat.card (N ⧸ H) = 3 from hidx]
    simp)
  obtain ⟨k, hk⟩ := hbij.2 (QuotientGroup.mk ⟨n, hn⟩)
  obtain ⟨s, hs, c, hc, hsc⟩ := hmem _ (QuotientGroup.eq.mp hk)
  refine ⟨k, k.isLt, s, hs, c, hc, ?_⟩
  simp only [τN, Subgroup.coe_mul, Subgroup.coe_inv, SubmonoidClass.coe_pow] at hsc
  rw [mul_assoc, ← hsc]
  group

theorem exists_eq_pow_mul_of_mem_e1NBar {τ : J ⧸ Subgroup.center J}
    (hτ : τ ∈ e1NBar (Subgroup.center J) u m y x)
    (hτN : τ ∈ Subgroup.normalizer (e1EBar (Subgroup.center J) u m y x :
      Set (J ⧸ Subgroup.center J))) (hτa : ∃ a : ℕ, τ ^ 3 ^ a = 1)
    (hτK : τ ∉ e1KBar (Subgroup.center J) u m y x) {n : J ⧸ Subgroup.center J}
    (hn : n ∈ Subgroup.normalizer (e1EBar (Subgroup.center J) u m y x :
      Set (J ⧸ Subgroup.center J))) :
    ∃ k : ℕ, k < 3 ∧ ∃ s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)),
      ∃ c ∈ Subgroup.centralizer (e1EBar (Subgroup.center J) u m y x :
        Set (J ⧸ Subgroup.center J)), n = τ ^ k * s * c := by
  have hb := d.caseC3BCD
  obtain ⟨a, ha⟩ := hτa
  have h3 := hb.commute_pow_three_of_odd_typeD htype S rfl (Odd.pow (by decide : Odd 3)) ha
    (CaseC3BCD.conj_mem_of_mem_e1NBar hτ)
  have huR := hb.e1EBar_le_e1RBar d.mem_e1EBar_gens.1
  have huz : (u : J ⧸ Subgroup.center J) ≠ caseC3Word (Subgroup.center J) u m y x 40 := by
    rw [← CaseC3BCD.caseC3Word_thirtytwo (Z := Subgroup.center J) (m := m) (y := y) (x := x), Ne,
      hb.caseC3Word_inj]
    decide
  exact d.exists_eq_pow_mul_of_mem_normalizer htype hτN ⟨a, ha⟩
    (Subgroup.mem_centralizer_iff.mpr fun s hs => (h3 s (hb.e1EBar_le_e1RBar hs)).symm)
    (hb.conj_ne_of_not_mem_e1KBar_typeD htype S rfl hτ hτK huR hb.mk_ne_one.1 huz).1 hn

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
