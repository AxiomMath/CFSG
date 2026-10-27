module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FixLift
public import CFSG.Monster.B.CTIB.Action
public import CFSG.Monster.B.CTIB.Census
public import CFSG.Monster.B.CTIB.CoreCensus
public import CFSG.Monster.B.CTIB.TableSix
public import CFSG.Monster.B.CTIB.FourClasses
public import CFSG.Monster.Existence.BabyW3Count

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.Monster.B CFSG.Monster.B.CTIB CFSG.Blueprint

section Basic

theorem babyQ_comm_mem {e f : Sbp} (he : e ∈ Qs) (hf : f ∈ Qs) :
    e * f * e⁻¹ * f⁻¹ ∈ zpowers xs := by
  have h1 : e⁻¹ ∈ Qs := Qs.inv_mem he
  have h2 : psiS ((e⁻¹)⁻¹ * f * e⁻¹) = psiS f := psiS_conj_Qs h1 hf
  rw [inv_inv] at h2
  have h3 : e * f * e⁻¹ ∈ Qs := Qs.mul_mem (Qs.mul_mem he hf) h1
  rcases eq_of_psiS_eq h3 hf h2 with h | h
  · rw [h, mul_inv_cancel]
    exact one_mem _
  · rw [h, mul_inv_cancel_right]
    exact mem_zpowers xs

theorem babyQ_sq_mem {e : Sbp} (he : e ∈ Qs) : e * e ∈ zpowers xs := by
  rcases sq_mem he with h | h
  · rw [h]
    exact one_mem _
  · rw [h]
    exact mem_zpowers xs

theorem babyQ_card_zpowers_xs : Nat.card (zpowers xs) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact xs_mul_self) xs_ne_one

end Basic

section Seven

theorem babyQ_exists_elem_of_cent {t : Sbp} (hx : xs * t = t * xs)
    (hcard : 2 ^ 12 ≤ Nat.card ↥(Qs ⊓ centralizer ({t} : Set Sbp))) :
    ∃ V : Subgroup Sbp, V ≤ Qs ⊓ centralizer ({t} : Set Sbp) ∧ IsElementaryAbelian 2 V ∧
      ∃ k, 6 ≤ k ∧ Nat.card V = 2 ^ k := by
  let Zp : Subgroup ↥Qs := (zpowers xs).subgroupOf Qs
  let Np : Subgroup ↥Qs := (Qs ⊓ centralizer ({t} : Set Sbp)).subgroupOf Qs
  have hxz : zpowers xs ≤ Qs := (zpowers_le).2 xs_mem
  have hZc : Zp ≤ center ↥Qs := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hz)
    have hc : Commute xs (y : Sbp) := xs_comm y.2
    show (y : Sbp) * (z : Sbp) = (z : Sbp) * (y : Sbp)
    rw [← hm]
    exact ((hc.zpow_left m).symm).eq
  have hZN : Zp ≤ Np := by
    intro z hz
    have hz' := Subgroup.mem_subgroupOf.1 hz
    refine Subgroup.mem_subgroupOf.2 ⟨z.2, ?_⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hz'
    rw [← hm]
    show xs ^ m ∈ centralizer ({t} : Set Sbp)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have hc : Commute xs t := hx
    exact ((hc.zpow_left m).symm).eq
  have hsq : ∀ e : ↥Qs, e * e ∈ Zp := fun e => Subgroup.mem_subgroupOf.2 (babyQ_sq_mem e.2)
  have hcomm : ∀ e f : ↥Qs, e * f * e⁻¹ * f⁻¹ ∈ Zp := fun e f =>
    Subgroup.mem_subgroupOf.2 (babyQ_comm_mem e.2 f.2)
  have hZ2 : Nat.card Zp = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hxz).toEquiv]
    exact babyQ_card_zpowers_xs
  have hN : 2 ^ 12 ≤ Nat.card Np := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left :
      Qs ⊓ centralizer ({t} : Set Sbp) ≤ Qs)).toEquiv]
    exact hcard
  obtain ⟨A, hAN, hA, k, hk, hAk⟩ := exists_elemAbelian_of_ext Zp Np hZc hZN hsq hcomm hZ2 hN
  refine ⟨A.map Qs.subtype, ?_, ?_, k, hk, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hAN ha)
  · refine isElementaryAbelian_of_sq_eq_one _ ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have := hA.toIsMulCommutative.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩
      exact congrArg (fun z : A => ((z : ↥Qs) : Sbp)) this
    · rintro _ ⟨a, ha, rfl⟩
      have h1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a ha
      simpa [pow_two] using congrArg (fun z : ↥Qs => (z : Sbp)) h1
  · rw [← hAk]
    exact (Nat.card_congr (A.equivMapOfInjective Qs.subtype Qs.subtype_injective).toEquiv).symm

theorem babyQ_ncard_class_le_two {t : Sbp} (ht : t ∈ Qs) : (qClass t).ncard ≤ 2 := by
  have hsub : qClass t ⊆ {t, xs * t} := by
    rintro _ ⟨g, hg, rfl⟩
    have h1 : psiS (g⁻¹ * t * g) = psiS t := psiS_conj_Qs hg ht
    have h2 : g⁻¹ * t * g ∈ Qs := Qs.mul_mem (Qs.mul_mem (Qs.inv_mem hg) ht) hg
    rcases eq_of_psiS_eq h2 ht h1 with h | h
    · exact Or.inl h
    · exact Or.inr h
  calc (qClass t).ncard ≤ ({t, xs * t} : Set Sbp).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)

end Seven

section Three

theorem babyQ_card_cent_ge {t : Sbp} (hc : (qClass t).ncard ≤ 2 ^ 11) :
    2 ^ 12 ≤ Nat.card ↥(Qs ⊓ centralizer ({t} : Set Sbp)) := by
  have h := CFSG.Monster.Existence.ncard_conj_mul_natCard_inf_centralizer Qs t
  rw [natCard_Qs] at h
  by_contra hlt
  push Not at hlt
  have h1 : {u : Sbp | ∃ g ∈ Qs, u = g⁻¹ * t * g}.ncard ≤ 2 ^ 11 := hc
  have h2 : Nat.card ↥(Qs ⊓ centralizer ({t} : Set Sbp)) * 2 ^ 11 < 2 ^ 12 * 2 ^ 11 :=
    Nat.mul_lt_mul_of_pos_right hlt (by norm_num)
  have h3 : {u : Sbp | ∃ g ∈ Qs, u = g⁻¹ * t * g}.ncard *
      Nat.card ↥(Qs ⊓ centralizer ({t} : Set Sbp)) ≤
      2 ^ 11 * Nat.card ↥(Qs ⊓ centralizer ({t} : Set Sbp)) :=
    Nat.mul_le_mul_right _ h1
  omega

end Three

section ThirtyTwo

theorem babyQ_exists_elem_rs {i : ℕ} (hi : i ∈ [1, 0, 5, 3]) :
    ∃ V : Subgroup Sbp, V ≤ centralizer ({rs i} : Set Sbp) ∧ IsElementaryAbelian 2 V ∧
      ∃ k, 6 ≤ k ∧ Nat.card V = 2 ^ k := by
  have key : ∀ {t : Sbp}, xs * t = t * xs →
      2 ^ 12 ≤ Nat.card ↥(Qs ⊓ centralizer ({t} : Set Sbp)) →
      ∃ V : Subgroup Sbp, V ≤ centralizer ({t} : Set Sbp) ∧ IsElementaryAbelian 2 V ∧
        ∃ k, 6 ≤ k ∧ Nat.card V = 2 ^ k := by
    intro t hx hc
    obtain ⟨V, hV, hE, k, hk, hVk⟩ := babyQ_exists_elem_of_cent hx hc
    exact ⟨V, hV.trans inf_le_right, hE, k, hk, hVk⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · rw [rs1_eq]
    exact key (xs_comm (qS_mem 1))
      (babyQ_card_cent_ge ((babyQ_ncard_class_le_two (qS_mem 1)).trans (by norm_num)))
  · rw [rs0_eq]
    refine key rfl ?_
    have : Qs ⊓ centralizer ({xs} : Set Sbp) = Qs := by
      refine inf_eq_left.2 fun e he => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact xs_comm he
    rw [this, natCard_Qs]
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  · have h6 := native_table_six_classes
    have hmem : ((5, 6, 32768, 128, 2158, 5) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) ∈ tableSixRows := by
      unfold tableSixRows
      decide
    obtain ⟨hJ, -, -, -, hq, -, -⟩ := h6.2.2.2 5 6 32768 128 2158 5 hmem
    have hx : xs * rs 5 = rs 5 * xs := by
      have h := conj_xs hJ
      calc xs * rs 5 = rs 5 * ((rs 5)⁻¹ * xs * rs 5) := by
            rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
        _ = rs 5 * xs := by rw [h]
    exact key hx (babyQ_card_cent_ge (by rw [hq]; norm_num))
  · rw [rs3_eq]
    exact key (xs_comm (qS_mem 7))
      (babyQ_card_cent_ge ((babyQ_ncard_class_le_two (qS_mem 7)).trans (by norm_num)))

theorem babyElem6 {s : Sbp} (hs1 : s ≠ 1) (hs2 : s * s = 1) :
    ∃ V : Subgroup Sbp, (∀ v ∈ V, ∀ w ∈ V, v * w = w * v) ∧ (∀ v ∈ V, v * v = 1) ∧
      2 ^ 6 ≤ Nat.card V ∧ ∀ v ∈ V, v * s = s * v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf s = 2 := orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1
  obtain ⟨i, ⟨hi, hconj⟩, -⟩ := (native_four_involution_classes.1 s hord)
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  obtain ⟨V₀, hV₀, hA, k, hk, hVk⟩ := babyQ_exists_elem_rs hi
  have hsq : ∀ v ∈ V₀, v * v = 1 := fun v hv => by
    have h1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V₀) v hv
    simpa [pow_two] using h1
  have hcomm : ∀ v ∈ V₀, ∀ w ∈ V₀, v * w = w * v := fun v hv w hw => by
    have := hA.toIsMulCommutative.is_comm.comm (⟨v, hv⟩ : V₀) ⟨w, hw⟩
    exact congrArg Subtype.val this
  refine ⟨V₀.map (MulAut.conj c⁻¹).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    show c⁻¹ * v * c⁻¹⁻¹ * (c⁻¹ * w * c⁻¹⁻¹) = c⁻¹ * w * c⁻¹⁻¹ * (c⁻¹ * v * c⁻¹⁻¹)
    calc c⁻¹ * v * c⁻¹⁻¹ * (c⁻¹ * w * c⁻¹⁻¹) = c⁻¹ * (v * w) * c⁻¹⁻¹ := by group
      _ = c⁻¹ * (w * v) * c⁻¹⁻¹ := by rw [hcomm v hv w hw]
      _ = _ := by group
  · rintro _ ⟨v, hv, rfl⟩
    show c⁻¹ * v * c⁻¹⁻¹ * (c⁻¹ * v * c⁻¹⁻¹) = 1
    calc c⁻¹ * v * c⁻¹⁻¹ * (c⁻¹ * v * c⁻¹⁻¹) = c⁻¹ * (v * v) * c⁻¹⁻¹ := by group
      _ = 1 := by rw [hsq v hv]; group
  · rw [Nat.card_congr (V₀.equivMapOfInjective (MulAut.conj c⁻¹).toMonoidHom
      (MulAut.conj c⁻¹).injective).toEquiv.symm, hVk]
    exact Nat.pow_le_pow_right (by norm_num) hk
  · rintro _ ⟨v, hv, rfl⟩
    have hvc : v * rs i = rs i * v := by
      have := hV₀ hv
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      exact this
    show c⁻¹ * v * c⁻¹⁻¹ * s = s * (c⁻¹ * v * c⁻¹⁻¹)
    have hs : s = c⁻¹ * rs i * c := by rw [← hc]; group
    rw [hs]
    calc c⁻¹ * v * c⁻¹⁻¹ * (c⁻¹ * rs i * c) = c⁻¹ * (v * rs i) * c := by group
      _ = c⁻¹ * (rs i * v) * c := by rw [hvc]
      _ = _ := by group

theorem babyElem6_of_equiv {Y : Type*} [Group Y] (e : Y ≃* NativeSporadic.B) {s : Y}
    (hs1 : s ≠ 1) (hs2 : s * s = 1) :
    ∃ V : Subgroup Y, (∀ v ∈ V, ∀ w ∈ V, v * w = w * v) ∧ (∀ v ∈ V, v * v = 1) ∧
      2 ^ 6 ≤ Nat.card V ∧ ∀ v ∈ V, v * s = s * v := by
  let e' : Y ≃* Sbp := e.trans iotaEquiv
  have h1 : e' s ≠ 1 := fun h => hs1 (e'.injective (h.trans (map_one e').symm))
  have h2 : e' s * e' s = 1 := by rw [← map_mul, hs2, map_one]
  obtain ⟨V, hc, hsq, hcard, hcs⟩ := babyElem6 h1 h2
  refine ⟨V.map e'.symm.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    show e'.symm v * e'.symm w = e'.symm w * e'.symm v
    rw [← map_mul, ← map_mul, hc v hv w hw]
  · rintro _ ⟨v, hv, rfl⟩
    show e'.symm v * e'.symm v = 1
    rw [← map_mul, hsq v hv, map_one]
  · rw [Nat.card_congr (V.equivMapOfInjective e'.symm.toMonoidHom e'.symm.injective).toEquiv.symm]
    exact hcard
  · rintro _ ⟨v, hv, rfl⟩
    show e'.symm v * s = s * e'.symm v
    apply e'.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hcs v hv

end ThirtyTwo

end CFSG.EvenSporadicStandard.Induction.Hyp
