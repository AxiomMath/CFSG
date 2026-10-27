module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.FactsAtlas
public import CFSG.Sporadic.Bridge.Fi22Surj
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.Fi

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.PartTwo.Sec4.Census

theorem oddCore_le_center_of_even_quotient {X : Type} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) (heven : Even (Nat.card (X ⧸ center X))) :
    CFSG.oddCore X ≤ center X := by
  refine sSup_le fun M hM => ?_
  obtain ⟨hMn, hModd⟩ := hM
  have hs : IsSimpleGroup (X ⧸ center X) := hq.2.1
  have hn : (M.map (QuotientGroup.mk' (center X))).Normal :=
    hMn.map _ (QuotientGroup.mk'_surjective _)
  rcases hn.eq_bot_or_eq_top with h | h
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · exfalso
    have hd : Nat.card (M.map (QuotientGroup.mk' (center X))) ∣ Nat.card M :=
      Subgroup.card_map_dvd _ _
    rw [h, Subgroup.card_top] at hd
    exact (Nat.not_even_iff_odd.2 (hModd.of_dvd_nat hd)) heven

theorem fi22EvenCover_proved
    (hSM : SporadicMultipliers) : Fi22EvenCover := by
  intro X _ _ hq hS hev
  obtain ⟨e⟩ := hS
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  obtain ⟨cq⟩ := fi23D_cq
  let ε : X ⧸ center X ≃* Spor .Fi22 := e.trans b
  let q : X →* Spor .Fi22 := CFSG.GH74.Generic.centralQuotientMap ε
  have hqs : Function.Surjective q := CFSG.GH74.Generic.centralQuotientMap_surjective ε
  have hqk : q.ker = center X := CFSG.GH74.Generic.centralQuotientMap_ker ε
  have hJcard : Nat.card (Spor .Fi22) = 64561751654400 := by
    rw [← fi23D_card_quotient, Nat.card_congr (cq.trans b).toEquiv.symm]
  have hevenQ : Even (Nat.card (X ⧸ center X)) := by
    rw [Nat.card_congr ε.toEquiv, hJcard]
    exact ⟨32280875827200, by norm_num⟩
  have hOZ : CFSG.oddCore X ≤ center X := oddCore_le_center_of_even_quotient hq hevenQ
  have hOk : CFSG.oddCore X ≤ q.ker := hqk ▸ hOZ
  let p : (X ⧸ CFSG.oddCore X) →* Spor .Fi22 := QuotientGroup.lift _ q fun x hx => hOk hx
  have hps : Function.Surjective p := fun y => by
    obtain ⟨x, rfl⟩ := hqs y
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hpk : ∀ x : X, p (QuotientGroup.mk x) = q x := fun x => rfl
  have hpc : p.ker ≤ center (X ⧸ CFSG.oddCore X) := by
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hx : x ∈ center X := by
      rw [← hqk, MonoidHom.mem_ker, ← hpk]
      exact hy
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro z
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective z
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hx w]
  have hOodd : Odd (Nat.card (CFSG.oddCore X)) :=
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd (G := X)
  have hp2 : IsPGroup 2 p.ker := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (y : X ⧸ CFSG.oddCore X)
    have hxZ : x ∈ center X := by
      rw [← hqk, MonoidHom.mem_ker, ← hpk, hx]
      exact y.2
    obtain ⟨a, r, hrodd, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨a, ?_⟩
    have hw : orderOf (x ^ 2 ^ a) = r := by
      rw [orderOf_pow' _ (pow_ne_zero a two_ne_zero), hord,
        Nat.gcd_eq_right (dvd_mul_right _ _), Nat.mul_div_cancel_left _ (by positivity)]
    have hcen : zpowers (x ^ 2 ^ a) ≤ center X :=
      (zpowers_le).2 ((center X).pow_mem hxZ _)
    have hnorm : (zpowers (x ^ 2 ^ a)).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have := Subgroup.mem_center_iff.1 (hcen hn) g
      rw [this, mul_assoc, mul_inv_cancel, mul_one]
      exact hn
    have hodd : Odd (Nat.card (zpowers (x ^ 2 ^ a))) := by
      rw [Nat.card_zpowers, hw]
      exact hrodd
    have hle : zpowers (x ^ 2 ^ a) ≤ CFSG.oddCore X :=
      le_sSup (show zpowers (x ^ 2 ^ a) ∈
        {N : Subgroup X | N.Normal ∧ Odd (Nat.card N)} from ⟨hnorm, hodd⟩)
    have hwO : x ^ 2 ^ a ∈ CFSG.oddCore X := hle (mem_zpowers _)
    have h1 : (QuotientGroup.mk (x ^ 2 ^ a) : X ⧸ CFSG.oddCore X) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hwO
    apply Subtype.ext
    show (y : X ⧸ CFSG.oddCore X) ^ 2 ^ a = 1
    rw [← hx, ← QuotientGroup.mk_pow]
    exact h1
  let p₀ : Fi23D →* Spor .Fi22 := CFSG.GH74.Generic.centralQuotientMap (cq.trans b)
  have hp₀s : Function.Surjective p₀ :=
    CFSG.GH74.Generic.centralQuotientMap_surjective (cq.trans b)
  have hp₀k : p₀.ker = center Fi23D := CFSG.GH74.Generic.centralQuotientMap_ker (cq.trans b)
  have hXperf : Group.IsPerfect X := hq.1
  have hYperf : Group.IsPerfect (X ⧸ CFSG.oddCore X) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (CFSG.oddCore X))
  have h6 : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (Spor .Fi22)) = 6 := by
    rw [hSM.1 .Fi22]
    decide
  obtain ⟨α, hαs, -⟩ := CFSG.GH74.Generic.exists_lift_of_odd_index fi23D_isQuasisimple.1 hYperf
    p₀ hp₀s hp₀k.le p hps hpc hp2 3 (by decide) (by rw [h6, hp₀k, fi23D_card_center])
  have hJpos : 0 < Nat.card (Spor .Fi22) := by rw [hJcard]; norm_num
  have hXc : Nat.card X = Nat.card (Spor .Fi22) * Nat.card (center X) := by
    rw [CFSG.GH74.Generic.card_eq_card_mul_card_ker q hqs, hqk]
  have hYc : Nat.card (X ⧸ CFSG.oddCore X) = Nat.card (Spor .Fi22) * Nat.card p.ker :=
    CFSG.GH74.Generic.card_eq_card_mul_card_ker p hps
  have hXO : Nat.card X = Nat.card (X ⧸ CFSG.oddCore X) * Nat.card (CFSG.oddCore X) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore X)
  have hZ : Nat.card (center X) = Nat.card p.ker * Nat.card (CFSG.oddCore X) := by
    apply Nat.eq_of_mul_eq_mul_left hJpos
    rw [← hXc, hXO, hYc, mul_assoc]
  have hker2 : 2 ≤ Nat.card p.ker := by
    have hkerEven : Even (Nat.card p.ker) := by
      by_contra h
      rw [Nat.not_even_iff_odd] at h
      exact (Nat.not_even_iff_odd.2 (hZ ▸ h.mul hOodd)) hev
    obtain ⟨k, hk⟩ := hkerEven
    have := Nat.card_pos (α := p.ker)
    omega
  have hcardD : Nat.card Fi23D = 2 * Nat.card (Spor .Fi22) := by
    rw [fi23D_card, hJcard]
  have hge : Nat.card Fi23D ≤ Nat.card (X ⧸ CFSG.oddCore X) := by
    rw [hYc, hcardD, mul_comm]
    exact Nat.mul_le_mul_left _ hker2
  exact ⟨(MulEquiv.ofBijective α (hαs.bijective_of_nat_card_le hge)).symm⟩

end CFSG.EvenSporadicStandard.Induction.Fi
