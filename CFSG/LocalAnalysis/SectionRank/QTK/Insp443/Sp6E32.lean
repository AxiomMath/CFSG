module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Sp6Model
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PermSix

public section

namespace CFSG.SectionRank.QTK.Insp443.Sp6

open Equiv CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier.Co3 CFSG.Quasithin.KGC31
  CFSG.Quasithin.KGC31.Native CFSG.SectionRank.QTK.Insp443.PermKit
  CFSG.SectionRank.QTK.Insp443.PermKit.Native


section Tabs

variable {ws : List Table} {ds : List (List Table)} {hs : List Table} {aT gT hT : Table}

theorem offender_of_check (hc : sixCheckE 36 ws ds hs aT gT hT = true)
    (haS : siftOK aT = true) (hwb : EBasis (permB 36 ws)) (hwH : ∀ i, permB 36 ws i ∈ co3X36) :
    ∃ a ∈ Subgroup.normalizer (eSub (liftB_basis hwH hwb) : Set co3X36), a * a = 1 ∧
      Nat.card (eSub (liftB_basis hwH hwb)) =
        2 * Nat.card {v : eSub (liftB_basis hwH hwb) // a * (v : co3X36) * a⁻¹ = v} := by
  simp only [sixCheckE, Bool.and_eq_true, beq_iff_eq, and_assoc, Bool.not_eq_true'] at hc
  obtain ⟨hwt, -, hwl, -, -, -, hht, hhb, hhl, hhW, htabs, hai, haW, hah, haw, -⟩ := hc
  simp only [tabsOK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at htabs
  have hws := forall₂_permB hwt
  obtain ⟨g, hgX, haT⟩ : ∃ g : Perm (Fin 36), g ∈ co3X36 ∧ Rep 36 aT g :=
    ⟨tabPerm 36 aT, mem_of_siftOK (rep_tabPerm htabs.1) haS, rep_tabPerm htabs.1⟩
  set a : co3X36 := ⟨g, hgX⟩ with ha_def
  set W' := eSub (liftB_basis hwH hwb) with hW'
  have haN : a ∈ Subgroup.normalizer (W' : Set co3X36) := by
    rw [mem_normalizer_liftB_iff hwH hwb]
    exact (normAll_iff hn36 hwb hws haT).mp haW
  have ha2 : a * a = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_one]
    exact mul_self_of_invoOK haT hai)
  refine ⟨a, haN, ha2, ?_⟩
  let C : Subgroup co3X36 := W' ⊓ Subgroup.centralizer ({a} : Set co3X36)
  have hCcard : Nat.card {v : W' // a * (v : co3X36) * a⁻¹ = v} = Nat.card C := by
    refine Nat.card_congr ⟨fun v => ⟨v, v.1.2, ?_⟩, fun c => ⟨⟨c, c.2.1⟩, ?_⟩, fun _ => rfl,
      fun _ => rfl⟩
    · show ((v : W') : co3X36) ∈ Subgroup.centralizer ({a} : Set co3X36)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := v.2
      calc ((v : W') : co3X36) * a = a * v * a⁻¹ * a := by rw [this]
        _ = a * (v : W') := by group
    · have h' : (c : co3X36) ∈ Subgroup.centralizer ({a} : Set co3X36) := c.2.2
      have := Subgroup.mem_centralizer_singleton_iff.mp h'
      calc a * (c : co3X36) * a⁻¹ = c * a * a⁻¹ := by rw [this]
        _ = c := by group
  have hWcard : Nat.card W' = 32 := by rw [card_eSub, hwl]; rfl
  have hhsb : EBasis (permB 36 hs) := ebasis_permB hn36 hht hhb
  have hhss := forall₂_permB hht
  have hhle : eSub hhsb ≤ eSub hwb :=
    eSub_le_of_inSpan hn36 hhsb hwb hhss hws fun b hb => by
      rw [List.all_eq_true] at hhW
      exact hhW b hb
  have hhH : ∀ i, permB 36 hs i ∈ co3X36 := fun i => by
    have h1 := hhle (mem_eSub hhsb i)
    rw [← eSub_liftB_map hwH hwb] at h1
    obtain ⟨x, -, hx⟩ := h1
    rw [← hx]
    exact x.2
  have hHC : eSub (liftB_basis hhH hhsb) ≤ C := by
    intro x hx
    have hxh : (x : Perm (Fin 36)) ∈ eSub hhsb := (mem_eSub_liftB_iff hhH hhsb x).mp hx
    have hxW : x ∈ W' := (mem_eSub_liftB_iff hwH hwb x).mpr (hhle hxh)
    have h1 : a ∈ Subgroup.centralizer (eSub (liftB_basis hhH hhsb) : Set co3X36) := by
      rw [mem_centralizer_liftB_iff hhH hhsb]
      exact (commAllT_iff hhss haT).mp hah
    have hxa : x ∈ Subgroup.centralizer ({a} : Set co3X36) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Subgroup.mem_centralizer_iff.mp h1) x hx)
    exact ⟨hxW, hxa⟩
  have h16 : 16 ≤ Nat.card C := by
    have h1 := Subgroup.card_le_of_le hHC
    rwa [card_eSub, hhl] at h1
  have hCW : C ≤ W' := inf_le_left
  have hCne : Nat.card C ≠ 32 := by
    intro h32
    have hCeq : C = W' := Subgroup.eq_of_le_of_card_ge hCW (by rw [hWcard, h32])
    have htrue : commAllT 36 ws aT = true := by
      rw [commAllT_iff hws haT]
      intro i
      have h1 : liftB (permB 36 ws) hwH i ∈ C := by rw [hCeq]; exact mem_eSub _ i
      have h1' : liftB (permB 36 ws) hwH i ∈ Subgroup.centralizer ({a} : Set co3X36) := h1.2
      have h2 := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp h1')
      rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_liftB] at h2
      exact h2.symm
    rw [htrue] at haw
    exact absurd haw (by decide)
  have hdvd : Nat.card C ∣ 32 := by rw [← hWcard]; exact Subgroup.card_dvd_of_le hCW
  have h16' : Nat.card C = 16 := by
    obtain ⟨k, hk, hck⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Nat.card C ∣ 2 ^ 5 from hdvd)
    interval_cases k <;> rw [hck] at h16 hCne ⊢ <;> omega
  rw [hCcard, h16', hWcard]

theorem mem_gh_of_check (hc : sixCheckE 36 ws ds hs aT gT hT = true) (hgS : siftOK gT = true)
    (hhS : siftOK hT = true) : tabPerm 36 gT ∈ co3X36 ∧ tabPerm 36 hT ∈ co3X36 := by
  simp only [sixCheckE, Bool.and_eq_true, beq_iff_eq, and_assoc, Bool.not_eq_true'] at hc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, htabs, -⟩ := hc
  simp only [tabsOK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at htabs
  exact ⟨mem_of_siftOK (rep_tabPerm htabs.2.1) hgS, mem_of_siftOK (rep_tabPerm htabs.2.2) hhS⟩

theorem length_of_check (hc : sixCheckE 36 ws ds hs aT gT hT = true) : ws.length = 5 := by
  simp only [sixCheckE, Bool.and_eq_true, beq_iff_eq, and_assoc, Bool.not_eq_true'] at hc
  exact hc.2.2.1

theorem conclK_e32 {L V MK : Subgroup co3X36} (h : KConfig co3X36 L V MK)
    (hc : sixCheckE 36 ws ds hs aT gT hT = true) (haS : siftOK aT = true)
    (hgS : siftOK gT = true) (hhS : siftOK hT = true) (hwb : EBasis (permB 36 ws))
    (hwH : ∀ i, permB 36 ws i ∈ co3X36)
    (hC : ∀ x : co3X36, ¬ ((∀ i, (x : Perm (Fin 36)) * permB 36 ws i =
      permB 36 ws i * x) ∧ (x : Perm (Fin 36)) ∉ eSub hwb))
    (hS : ∀ x : co3X36, ¬ ((x : Perm (Fin 36)) ∈ eNorm hwb ∧
      (¬ (∀ r < 6, ∃ s < 6, ConjInto (x : Perm (Fin 36)) (dB 36 ds r) (dB 36 ds s)) ∨
        ((∀ r < 6, ConjInto (x : Perm (Fin 36)) (dB 36 ds r) (dB 36 ds r)) ∧
          (x : Perm (Fin 36)) ∉ eSub hwb))))
    (hV : V = eSub (liftB_basis hwH hwb)) : ConclK co3X36 L V MK := by
  obtain ⟨hgH, hhH⟩ := mem_gh_of_check hc hgS hhS
  obtain ⟨hdb, hdH, hd⟩ := exists_sixData hn36 hc hwb hwH (fun g hg => hS ⟨g, hg⟩) hgH hhH
  obtain ⟨a, haN, ha2, hfix⟩ := offender_of_check hc haS hwb hwH
  subst hV
  have hCV : Subgroup.centralizer (eSub (liftB_basis hwH hwb) : Set co3X36) ≤
      eSub (liftB_basis hwH hwb) := fun x hx => by
    rw [mem_centralizer_liftB_iff hwH hwb] at hx
    by_contra hxV
    exact hC x ⟨hx, fun hm => hxV ((mem_eSub_liftB_iff hwH hwb x).mpr hm)⟩
  exact h.conclK_of_sixData hCV hd haN ha2 hfix

theorem false_e16 {L V MK : Subgroup co3X36} (h : KConfig co3X36 L V MK)
    (hc : sixCheckE 36 ws ds hs aT gT hT = true) (hgS : siftOK gT = true)
    (hhS : siftOK hT = true) (hwb : EBasis (permB 36 ws)) (hwH : ∀ i, permB 36 ws i ∈ co3X36)
    (hS : ∀ x : co3X36, ¬ ((x : Perm (Fin 36)) ∈ eNorm hwb ∧
      (¬ (∀ r < 6, ∃ s < 6, ConjInto (x : Perm (Fin 36)) (dB 36 ds r) (dB 36 ds s)) ∨
        ((∀ r < 6, ConjInto (x : Perm (Fin 36)) (dB 36 ds r) (dB 36 ds r)) ∧
          (x : Perm (Fin 36)) ∉ eSub hwb))))
    {us : List Table} (hub : EBasis (permB 36 us)) (huH : ∀ i, permB 36 us i ∈ co3X36)
    (hCU : ∀ x : co3X36, ¬ ((∀ i, (x : Perm (Fin 36)) * permB 36 us i =
      permB 36 us i * x) ∧ (x : Perm (Fin 36)) ∉ eSub hwb))
    (hsub : subOK 36 us ws = true) {r : ℕ} (hr : r < 6)
    (hUr : spanEq 36 us (ds.getD r []) = true)
    (hV : V = eSub (liftB_basis huH hub)) : False := by
  obtain ⟨hgH, hhH⟩ := mem_gh_of_check hc hgS hhS
  obtain ⟨hdb, hdH, hd⟩ := exists_sixData hn36 hc hwb hwH (fun g hg => hS ⟨g, hg⟩) hgH hhH
  simp only [subOK, Bool.and_eq_true, List.all_eq_true] at hsub
  obtain ⟨⟨⟨⟨⟨hut, -⟩, hwt⟩, -⟩, hUW⟩, -⟩ := hsub
  have hus := forall₂_permB hut
  have hws := forall₂_permB hwt
  set W' := eSub (liftB_basis hwH hwb) with hW'
  have hUle : eSub hub ≤ eSub hwb :=
    eSub_le_of_inSpan hn36 hub hwb hus hws fun b hb => hUW b hb
  subst hV
  have hVW : eSub (liftB_basis huH hub) ≤ W' := fun x hx =>
    (mem_eSub_liftB_iff hwH hwb x).mpr (hUle ((mem_eSub_liftB_iff huH hub x).mp hx))
  have hCV : Subgroup.centralizer (eSub (liftB_basis huH hub) : Set co3X36) = W' := by
    refine le_antisymm (fun x hx => ?_) fun x hx => ?_
    · rw [mem_centralizer_liftB_iff huH hub] at hx
      by_contra hxW
      exact hCU x ⟨hx, fun hm => hxW ((mem_eSub_liftB_iff hwH hwb x).mpr hm)⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact eSub_comm _ y x (hVW hy) hx
  have hW2 : IsPGroup 2 ↥W' :=
    IsPGroup.of_card (n := 5) (by rw [card_eSub, length_of_check hc])
  refine h.false_of_sixData hCV hW2 hd (r := ⟨r, hr⟩) ?_
  apply Subgroup.map_injective (co3X36.subtype_injective)
  rw [eSub_liftB_map huH hub, eSub_liftB_map]
  exact spanEq_iff hn36 hub (hdb ⟨r, hr⟩) hus (forall₂_permB (by
    simp only [sixCheckE, Bool.and_eq_true, beq_iff_eq, and_assoc, Bool.not_eq_true',
      List.all_eq_true] at hc
    obtain ⟨-, -, -, hdl, hdall, -⟩ := hc
    exact (hdall _ (getD_mem (by rw [hdl]; exact hr))).1)) hUr

end Tabs

end CFSG.SectionRank.QTK.Insp443.Sp6

end
