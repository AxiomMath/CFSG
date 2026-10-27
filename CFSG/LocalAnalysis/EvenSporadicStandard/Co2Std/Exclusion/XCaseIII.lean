module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.XN0e
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup

variable {V : Type*} [Group V] {X : Type*} [Group X] {ρ : X →* MulAut V} {Q : Subgroup X}
  {V₁ V₂ : Subgroup V} {z : X} {Q₁ : Subgroup (MulAut ↥V₁)} {t₁ : ↥V₁}

theorem XHyp.concl_of_layer_eq_bot [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁)
    (hX : zpowers z ⊔ Q ≠ ⊤) (hE : layer X = ⊥) : XConcl ρ Q V₁ V₂ z := by
  classical
  let F : Subgroup X := fittingSubgroup X
  have hFnormal : F.Normal := fittingSubgroup_normal
  haveI : F.Normal := hFnormal
  have hFnil : Group.IsNilpotent F := inferInstance
  have hgen : generalizedFitting X = F := by
    rw [generalizedFitting.eq_sup, hE, sup_bot_eq]
  have hbender : Subgroup.centralizer (F : Set X) ≤ F := by
    have hb := CFSG.centralizer_generalizedFitting_le X
    rwa [hgen] at hb
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [h.card_V]; norm_num)
  have hnotdvd : ¬ 2 ∣ Nat.card F := by
    obtain ⟨P⟩ : Nonempty (Sylow 2 F) := inferInstance
    have hPnorm : (P : Subgroup F).Normal :=
      Group.IsNilpotent.sylow_normal hFnil 2 P
    have hPchar : (P : Subgroup F).Characteristic :=
      Sylow.characteristic_of_normal P hPnorm
    haveI : (P : Subgroup F).Characteristic := hPchar
    have hmap_normal : (P.map F.subtype).Normal := inferInstance
    have hmapP : IsPGroup 2 (P.map F.subtype) := P.isPGroup'.map F.subtype
    have hPmap_bot : P.map F.subtype = ⊥ := h.eq_bot_of_isPGroup hX hmap_normal hmapP
    have hPbot : (P : Subgroup F) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxmap : (x : X) ∈ P.map F.subtype := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rw [hPmap_bot] at hxmap
      exact Subtype.ext (Subgroup.mem_bot.mp hxmap)
    have hcardP : Nat.card (P : Subgroup F) = 1 := by
      rw [hPbot, Subgroup.card_bot]
    have hcardF : Nat.card F = (P : Subgroup F).index := by
      have hc := (P : Subgroup F).card_mul_index
      rw [hcardP, one_mul] at hc
      exact hc.symm
    rw [hcardF]
    exact P.not_dvd_index
  have hodd : Odd (Nat.card F) :=
    Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using hnotdvd)
  have hFC_bot : F ⊓ centralizer ({z} : Set X) = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    rw [Subgroup.mem_inf] at hf
    obtain ⟨hfF, hfC⟩ := hf
    rw [Subgroup.mem_bot]
    have hzf : z * f = f * z := by
      rw [Subgroup.mem_centralizer_iff] at hfC
      exact hfC z (by simp)
    have hconj : z * f * z⁻¹ = f⁻¹ := h.conj_eq_inv_of_odd hFnormal hodd hfF
    have hf_inv : f = f⁻¹ := by
      rw [← hconj, hzf]
      group
    have hf2 : f * f = 1 := by
      nth_rewrite 2 [hf_inv]
      exact mul_inv_cancel f
    have hdvd2 : orderOf f ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]
      exact hf2
    have hodd_order : Odd (orderOf f) := by
      rw [← Nat.not_even_iff_odd] at hodd ⊢
      intro he
      exact hodd (even_iff_two_dvd.mpr
        ((even_iff_two_dvd.mp he).trans (Subgroup.orderOf_dvd_natCard F hfF)))
    have hnot2 : ¬ 2 ∣ orderOf f := fun h2 =>
      (Nat.not_even_iff_odd.mpr hodd_order) (even_iff_two_dvd.mpr h2)
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd2 with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · exact absurd (h1 ▸ dvd_rfl) hnot2
  have hFC_top : F ⊔ centralizer ({z} : Set X) = ⊤ := by
    apply le_antisymm le_top
    intro x _
    let a : X := x * z * x⁻¹
    let c : X := a * z
    have ha_inv : ∀ f ∈ F, a * f * a⁻¹ = f⁻¹ := by
      intro f hf
      have hmem : x⁻¹ * f * x ∈ F := by
        simpa using hFnormal.conj_mem f hf x⁻¹
      have hz' : z * (x⁻¹ * f * x) * z⁻¹ = (x⁻¹ * f * x)⁻¹ :=
        h.conj_eq_inv_of_odd hFnormal hodd hmem
      change (x * z * x⁻¹) * f * (x * z * x⁻¹)⁻¹ = f⁻¹
      calc (x * z * x⁻¹) * f * (x * z * x⁻¹)⁻¹
          = x * (z * (x⁻¹ * f * x) * z⁻¹) * x⁻¹ := by group
        _ = x * (x⁻¹ * f * x)⁻¹ * x⁻¹ := by rw [hz']
        _ = f⁻¹ := by group
    have hz_inv : ∀ f ∈ F, z * f * z⁻¹ = f⁻¹ :=
      fun f hf => h.conj_eq_inv_of_odd hFnormal hodd hf
    have hc_cent : c ∈ centralizer (F : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have h1 : c * f * c⁻¹ = f := by
        change (a * z) * f * (a * z)⁻¹ = f
        calc (a * z) * f * (a * z)⁻¹ = a * (z * f * z⁻¹) * a⁻¹ := by group
          _ = a * f⁻¹ * a⁻¹ := by rw [hz_inv f hf]
          _ = f := by
            rw [show a * f⁻¹ * a⁻¹ = (a * f * a⁻¹)⁻¹ by group, ha_inv f hf, inv_inv]
      have h2 : f * c = c * f := by
        have h3 := congrArg (fun t => t * c) h1
        simpa [mul_assoc] using h3.symm
      exact h2
    have hcF : c ∈ F := hbender hc_cent
    have hodd' : Odd (Nat.card F) := hodd
    obtain ⟨k, hk⟩ := hodd'
    let d : X := c ^ (k + 1)
    have hd_mem : d ∈ F := F.pow_mem hcF (k + 1)
    have hc_card : c ^ Nat.card F = 1 := by
      have hpc : ((⟨c, hcF⟩ : F) : X) ^ Nat.card F = 1 :=
        congrArg (fun y : F => (y : X))
          (pow_card_eq_one' (G := F) (x := (⟨c, hcF⟩ : F)))
      simpa using hpc
    have hd_sq : d * d = c := by
      change c ^ (k + 1) * c ^ (k + 1) = c
      rw [← pow_add]
      have hk' : (k + 1) + (k + 1) = Nat.card F + 1 := by omega
      rw [hk', pow_succ, hc_card, one_mul]
    have hz2 : z⁻¹ = z := (inv_eq_iff_mul_eq_one).mpr h.mul_self
    have hdz : z * d * z⁻¹ = d⁻¹ := h.conj_eq_inv_of_odd hFnormal hodd hd_mem
    have hdzd : d * z * d⁻¹ = a := by
      have hdz'' : z * d * z = d⁻¹ := by rwa [hz2] at hdz
      have hdz' : d * z = z * d⁻¹ := by
        have hc := congrArg (fun t => z * t) hdz''
        have hL : z * (z * d * z) = d * z := by
          rw [mul_assoc z d z, ← mul_assoc z z (d * z), h.mul_self, one_mul]
        rwa [hL] at hc
      calc d * z * d⁻¹ = (z * d⁻¹) * d⁻¹ := by rw [hdz']
        _ = z * (d⁻¹ * d⁻¹) := by rw [mul_assoc]
        _ = z * (d * d)⁻¹ := by rw [mul_inv_rev]
        _ = z * c⁻¹ := by rw [hd_sq]
        _ = a := by
          change z * (a * z)⁻¹ = a
          have ha2 : a⁻¹ = a := by
            rw [inv_eq_iff_mul_eq_one]
            change (x * z * x⁻¹) * (x * z * x⁻¹) = 1
            have h2 : (x * z * x⁻¹) * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
            rw [h2, h.mul_self]
            group
          rw [mul_inv_rev, hz2, ha2, ← mul_assoc, h.mul_self, one_mul]
    have hmem : d⁻¹ * x ∈ centralizer ({z} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hconj : (d⁻¹ * x) * z * (d⁻¹ * x)⁻¹ = z := by
        calc (d⁻¹ * x) * z * (d⁻¹ * x)⁻¹ = d⁻¹ * (x * z * x⁻¹) * d := by group
          _ = d⁻¹ * a * d := by rfl
          _ = z := by
            rw [← hdzd]
            group
      have h2 : (d⁻¹ * x) * z = z * (d⁻¹ * x) := by
        have h3 := congrArg (fun t => t * (d⁻¹ * x)) hconj
        simpa [mul_assoc] using h3
      exact h2
    have hx_eq : x = d * (d⁻¹ * x) := by group
    rw [hx_eq]
    exact Subgroup.mul_mem_sup hd_mem hmem
  have hcompl : F.IsComplement' (centralizer ({z} : Set X)) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hFC_bot) ?_
    rw [← Subgroup.normal_mul F (centralizer ({z} : Set X)), hFC_top]
    rfl
  have hFindex : F.index = Nat.card (centralizer ({z} : Set X)) := hcompl.symm.index_eq_card
  have hCindex : (centralizer ({z} : Set X)).index = Nat.card F := hcompl.index_eq_card
  have hodd_index : ¬ 2 ∣ (centralizer ({z} : Set X)).index := by
    rw [hCindex]
    exact hnotdvd
  have hFQ_bot : F ⊓ Q = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    rw [Subgroup.mem_inf] at hf
    obtain ⟨hfF, hfQ⟩ := hf
    have hfC : f ∈ centralizer ({z} : Set X) := h.le_centralizer hfQ
    have hmem : f ∈ F ⊓ centralizer ({z} : Set X) := ⟨hfF, hfC⟩
    rwa [hFC_bot] at hmem
  have hrelQ : F.relIndex Q = Nat.card Q := by
    change (F.subgroupOf Q).index = Nat.card Q
    rw [(Subgroup.subgroupOf_eq_bot).mpr (disjoint_iff.mpr hFQ_bot), Subgroup.index_bot]
  have hrel : F.relIndex (F ⊔ Q) = Nat.card Q := by
    rw [Subgroup.relIndex_sup_left, hrelQ]
  have hX0index : (F ⊔ Q).index = 2 := by
    have h1 := Subgroup.relIndex_mul_index (H := F) (K := F ⊔ Q) (le_sup_left : F ≤ F ⊔ Q)
    rw [hrel, hFindex, h.card_centralizer, h.card_Q] at h1
    omega
  have hz_notin : z ∉ F ⊔ Q := by
    intro hz
    have hC_le : centralizer ({z} : Set X) ≤ F ⊔ Q := by
      rw [h.centralizer_eq]
      exact sup_le (Subgroup.zpowers_le.mpr hz) le_sup_right
    have htop : F ⊔ Q = ⊤ := by
      apply top_unique
      rw [← hFC_top]
      exact sup_le le_sup_left hC_le
    have hindex1 : (F ⊔ Q).index = 1 := by
      rw [htop, Subgroup.index_top]
    omega
  unfold XConcl
  exact ⟨⟨F ⊔ Q, Subgroup.normal_of_index_eq_two hX0index, hX0index, hz_notin⟩,
    h.exists_sylow_of_odd hodd_index⟩

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
