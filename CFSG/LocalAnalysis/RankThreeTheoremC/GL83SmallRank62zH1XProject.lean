module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH1XComp
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH1YProject
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH1Basic
import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {f : ℕ} {X Q : Subgroup G}

@[expose] def k631aPre (f : ℕ) (X : Subgroup G) (T : Subgroup (↥X ⧸ GLAPPrimeCore f ↥X)) :
    Subgroup G :=
  (T.comap (QuotientGroup.mk' (GLAPPrimeCore f ↥X))).map X.subtype

omit [Finite G] in
theorem k631a_mem_pre {T : Subgroup (↥X ⧸ GLAPPrimeCore f ↥X)} {w : G} :
    w ∈ k631aPre f X T ↔ ∃ hw : w ∈ X, k631aMk f X w hw ∈ T := by
  unfold k631aPre
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, hz⟩
  · rintro ⟨hw, hT⟩
    exact ⟨⟨w, hw⟩, hT, rfl⟩

omit [Finite G] in
theorem k631a_mem_normalizer_pre {T : Subgroup (↥X ⧸ GLAPPrimeCore f ↥X)} {x : G} (hx : x ∈ X)
    (hxT : k631aMk f X x hx ∈ normalizer (T : Set (↥X ⧸ GLAPPrimeCore f ↥X))) :
    x ∈ normalizer (k631aPre f X T : Set G) := by
  rw [mem_normalizer_iff]
  intro w
  have hconj : ∀ hw : w ∈ X, k631aMk f X (x * w * x⁻¹)
      (X.mul_mem (X.mul_mem hx hw) (X.inv_mem hx)) =
        k631aMk f X x hx * k631aMk f X w hw * (k631aMk f X x hx)⁻¹ := by
    intro hw
    rw [k631a_mk_mul (X.mul_mem hx hw) (X.inv_mem hx), k631a_mk_mul hx hw, k631a_mk_inv hx]
  constructor
  · intro hw
    obtain ⟨hwX, hwT⟩ := k631a_mem_pre.1 hw
    refine k631a_mem_pre.2 ⟨X.mul_mem (X.mul_mem hx hwX) (X.inv_mem hx), ?_⟩
    rw [hconj hwX]
    exact (mem_normalizer_iff.mp hxT _).mp hwT
  · intro hw
    obtain ⟨hwX', hwT'⟩ := k631a_mem_pre.1 hw
    have hwX : w ∈ X := by
      have e : w = x⁻¹ * (x * w * x⁻¹) * x := by group
      rw [e]
      exact X.mul_mem (X.mul_mem (X.inv_mem hx) hwX') hx
    refine k631a_mem_pre.2 ⟨hwX, ?_⟩
    rw [hconj hwX] at hwT'
    exact (mem_normalizer_iff.mp hxT _).mpr hwT'

omit [Finite G] in
theorem k631a_card_pre (T : Subgroup (↥X ⧸ GLAPPrimeCore f ↥X)) :
    Nat.card (k631aPre f X T) = Nat.card (GLAPPrimeCore f ↥X) * Nat.card T := by
  unfold k631aPre
  rw [Subgroup.card_map_of_injective X.subtype_injective]
  exact QuotientGroup.card_preimage_mk (GLAPPrimeCore f ↥X) (T : Set (↥X ⧸ GLAPPrimeCore f ↥X))

theorem k631a_project (hInn : KFactInnerAction) (hL : LayerHyp f X Q) {Y V : Subgroup G}
    (hYX : Y ≤ X) (hY2 : IsPGroup 2 Y) (hY1 : Y ≠ ⊥) (hVQ : V ≤ Q)
    (hVY : V ≤ normalizer (Y : Set G)) (hYV : ⁅Y, V⁆ = Y) :
    ∃ J : Subgroup G, GLAPComponent f X J ∧ ∃ Y₁ : Subgroup G, Y₁ ≠ ⊥ ∧ IsPGroup 2 Y₁ ∧
      (∃ e ∈ Q ⊓ J, e ≠ 1 ∧ e ∈ normalizer (Y₁ : Set G)) ∧
      Q ⊓ k631Triv (GLAPPrimeCoreOf f X) J ≤ normalizer (Y₁ : Set G) := by
  have hX := k631a_hyp_of_layer hL
  have hB := k631a_bhyp_barX hX
  have hf := hL.prime
  have hVX : V ≤ X := hVQ.trans hL.le
  have hYb : IsPGroup 2 ↥(barX f X Y) :=
    (hY2.of_equiv (Subgroup.subgroupOfEquivOfLe hYX).symm).map (QuotientGroup.mk' _)
  have hOcop : Nat.Coprime 2 (Nat.card (GLAPPrimeCoreOf f X)) := Nat.coprime_two_left.mpr hL.odd
  have hYb1 : barX f X Y ≠ ⊥ := by
    intro hbot
    apply hY1
    rw [eq_bot_iff]
    intro y hy
    have hyX := hYX hy
    have h1 : k631aMk f X y hyX ∈ barX f X Y := k631a_mk_mem_barX hyX hy
    rw [hbot, Subgroup.mem_bot] at h1
    have hyO := (k631a_mem_core_iff hyX).2 h1
    exact (Subgroup.mem_bot).2 (k631a_eq_one_of_mem_inf hY2 hOcop hy hyO)
  have hVb : barX f X V ≤ barX f X Q := barX_mono f hVQ
  have hVn : barX f X V ≤ normalizer (barX f X Y : Set (↥X ⧸ GLAPPrimeCore f ↥X)) :=
    barX_le_normalizer hVY
  have hcomm : ⁅barX f X Y, barX f X V⁆ = barX f X Y := by
    rw [← barX_commutator f hYX hVX, hYV]
  obtain ⟨Jb, hJb, T, hTJ, hT1, hT2, sb, hsb, hsb1, hsbT⟩ :=
    k631a_project_Y hInn hB hYb hYb1 hVb hVn hcomm
  obtain ⟨J, hJ, hJbar⟩ :=
    exists_glaPComponent_barX_eq (p := f) X ((CFSG.isComponent_iff_open Jb).1 hJb)
  obtain ⟨e, heX, heQ, heJ, he⟩ := k631a_lift hX hJ hsb.1 (by rw [hJbar]; exact hsb.2)
  have he1 : e ≠ 1 := by
    intro h1
    subst h1
    exact hsb1 (he.symm.trans (map_one _))
  set W := k631aPre f X T with hW
  have hcentral : ∀ q ∈ Q ⊓ k631Triv (GLAPPrimeCoreOf f X) J, ∃ hqX : q ∈ X,
      k631aMk f X q hqX ∈ normalizer (T : Set (↥X ⧸ GLAPPrimeCore f ↥X)) := by
    intro q hq
    have hqX : q ∈ X := hL.le hq.1
    have hqN : q ∈ normalizer (J : Set G) := k631a_normalized hX hJ hq.1
    have hc := (k631a_mem_triv_iff hJ.1 hqX hqN).1 hq.2
    refine ⟨hqX, ?_⟩
    set a := k631aMk f X q hqX with ha
    rw [mem_normalizer_iff]
    intro t
    have hcT : ∀ t' ∈ T, a * t' = t' * a := fun t' ht' => hc t' (by rw [hJbar]; exact hTJ ht')
    constructor
    · intro ht
      rw [hcT t ht]
      simpa using ht
    · intro ht
      have h1 := hcT _ ht
      have h2 : a * (a * t * a⁻¹) = a * t := by
        calc a * (a * t * a⁻¹) = (a * t * a⁻¹) * a := h1
          _ = a * t := by group
      have h3 : a * t * a⁻¹ = t := mul_left_cancel h2
      rwa [h3] at ht
  set R : Subgroup G := (Q ⊓ k631Triv (GLAPPrimeCoreOf f X) J) ⊔ Subgroup.zpowers e with hR
  have hRQ : R ≤ Q := sup_le inf_le_left (Subgroup.zpowers_le.2 heQ)
  have hRpg : IsPGroup f R := hX.pgroup.to_le hRQ
  have hRW : R ≤ normalizer (W : Set G) := by
    refine sup_le (fun q hq => ?_) (Subgroup.zpowers_le.2 ?_)
    · obtain ⟨hqX, hqT⟩ := hcentral q hq
      exact k631a_mem_normalizer_pre hqX hqT
    · exact k631a_mem_normalizer_pre heX (by rw [he]; exact hsbT)
  have hOcard : ¬ f ∣ Nat.card (GLAPPrimeCore f ↥X) := by
    have h1 : Nat.card (GLAPPrimeCoreOf f X) = Nat.card (GLAPPrimeCore f ↥X) :=
      Subgroup.card_map_of_injective X.subtype_injective
    rw [← h1]
    exact not_dvd_card_glaPPrimeCoreOf hf X
  have hTcard : ¬ f ∣ Nat.card T := by
    obtain ⟨k, hk⟩ := hT2.exists_card_eq
    rw [hk]
    intro hd
    exact hL.ne_two ((Nat.prime_dvd_prime_iff_eq hf Nat.prime_two).mp (hf.dvd_of_dvd_pow hd))
  have hWcard : ¬ f ∣ Nat.card W := by
    rw [hW, k631a_card_pre]
    exact hf.not_dvd_mul hOcard hTcard
  obtain ⟨P, hPW, hP2, hPidx, hRP⟩ :=
    k631a_exists_normalized_sylow hf Nat.prime_two hRpg hRW hWcard
  have hPne : P ≠ ⊥ := by
    intro hbot
    have h2T : 2 ∣ Nat.card T := by
      obtain ⟨k, hk⟩ := hT2.exists_card_eq
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · exfalso
        apply hT1
        rw [h0] at hk
        exact Subgroup.eq_bot_of_card_eq T (by simpa using hk)
      · rw [hk]
        exact dvd_pow_self 2 hpos.ne'
    have h2W : 2 ∣ Nat.card W := by
      rw [hW, k631a_card_pre]
      exact Dvd.dvd.mul_left h2T _
    apply hPidx
    rw [hbot, Subgroup.bot_subgroupOf, Subgroup.index_bot]
    exact h2W
  exact ⟨J, hJ, P, hPne, hP2, ⟨e, ⟨heQ, heJ⟩, he1,
    hRP (Subgroup.mem_sup_right (Subgroup.mem_zpowers e))⟩,
    fun q hq => hRP (Subgroup.mem_sup_left hq)⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
