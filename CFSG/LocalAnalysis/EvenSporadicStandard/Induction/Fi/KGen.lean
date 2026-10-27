module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.OddQuot
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiCoverMore
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzONAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3Parts
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction.Fi

open Subgroup Cover CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp

variable {D X Y : Type} [Group D] [Group X] [Group Y]

theorem oddCentralExt_perfect (h : IsOddCentralExt D X) : Group.IsPerfect X := h.1.1

theorem oddCentralExt_card_center [Finite X] (h : IsOddCentralExt D X) :
    ∃ k : ℕ, Odd k ∧ Nat.card (center X) = k * Nat.card (center D) := by
  obtain ⟨hq, π, hπs, hπc, hπo⟩ := h
  have := hq.1
  exact ⟨Nat.card π.ker, hπo, card_center_eq_of_cover π hπs hπc⟩

theorem oddCentralExt_even_card_center [Finite X] (hD : Even (Nat.card (center D)))
    (h : IsOddCentralExt D X) : Even (Nat.card (center X)) := by
  obtain ⟨k, -, hk⟩ := oddCentralExt_card_center h
  rw [hk]
  exact (Nat.even_mul).2 (Or.inr hD)

theorem oddCentralExt_mulEquiv (h : IsOddCentralExt D X) (hO : CFSG.oddCore X = ⊥) :
    Nonempty (X ≃* D) := by
  obtain ⟨-, π, hπs, hπc, hπo⟩ := h
  have hker : π.ker = ⊥ := by
    have h1 : π.ker ≤ CFSG.oddCore X := le_oddCore_of_normal_odd inferInstance hπo
    rw [hO] at h1
    exact le_bot_iff.1 h1
  exact ⟨MulEquiv.ofBijective π ⟨(MonoidHom.ker_eq_bot_iff π).1 hker, hπs⟩⟩

theorem oddCentralExt_kIso (hX : IsOddCentralExt D X) (hY : IsOddCentralExt D Y)
    (hOX : CFSG.oddCore X = ⊥) (hOY : CFSG.oddCore Y = ⊥) : Nonempty (X ≃* Y) := by
  obtain ⟨e⟩ := oddCentralExt_mulEquiv hX hOX
  obtain ⟨f⟩ := oddCentralExt_mulEquiv hY hOY
  exact ⟨e.trans f.symm⟩

theorem oddCentralExt_cqEquiv (h : IsOddCentralExt D X) :
    Nonempty ((X ⧸ center X) ≃* (D ⧸ center D)) := by
  obtain ⟨hq, π, hπs, hπc, -⟩ := h
  have := hq.1
  exact cqEquiv_of_cover π hπs hπc

theorem oddCentralExt_cq_cq (hX : IsOddCentralExt D X) (hY : IsOddCentralExt D Y) :
    Nonempty ((X ⧸ center X) ≃* (Y ⧸ center Y)) := by
  obtain ⟨e⟩ := oddCentralExt_cqEquiv hX
  obtain ⟨f⟩ := oddCentralExt_cqEquiv hY
  exact ⟨e.trans f.symm⟩

theorem oddCentralExt_quot [Finite X] (hD : CFSG.oddCore D = ⊥) (h : IsOddCentralExt D X) :
    IsOddCentralExt D (X ⧸ CFSG.oddCore X) := by
  obtain ⟨hq, π, hπs, hπc, hπo⟩ := h
  have hOX : CFSG.oddCore X ≤ π.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hn : (Subgroup.map π (CFSG.oddCore X)).Normal := Subgroup.Normal.map inferInstance π hπs
    have hodd : Odd (Nat.card (Subgroup.map π (CFSG.oddCore X))) :=
      (odd_card_oddCore' X).of_dvd_nat
        (Subgroup.card_dvd_of_surjective (MonoidHom.subgroupMap_surjective π _))
    have h1 := le_oddCore_of_normal_odd hn hodd
    rw [hD] at h1
    exact Subgroup.mem_bot.1 (h1 ⟨x, hx, rfl⟩)
  let ψ : X ⧸ CFSG.oddCore X →* D := QuotientGroup.lift (CFSG.oddCore X) π hOX
  have hψ : ∀ x : X, ψ (QuotientGroup.mk x) = π x := fun x => rfl
  refine ⟨isQuasisimple_of_cover hq (QuotientGroup.mk' (CFSG.oddCore X))
    QuotientGroup.mk_surjective (by rw [QuotientGroup.ker_mk']; exact oddCore_le_center hq),
    ψ, ?_, ?_, ?_⟩
  · intro d
    obtain ⟨x, rfl⟩ := hπs d
    exact ⟨QuotientGroup.mk x, hψ x⟩
  · intro w hw
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    have hx : x ∈ π.ker := by
      rw [MonoidHom.mem_ker, ← hψ]
      exact hw
    refine Subgroup.mem_center_iff.2 fun g' => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g'
    show QuotientGroup.mk (g * x) = QuotientGroup.mk (x * g)
    rw [Subgroup.mem_center_iff.1 (hπc hx) g]
  · let f : ↥π.ker →* ↥ψ.ker :=
      ((QuotientGroup.mk' (CFSG.oddCore X)).comp π.ker.subtype).codRestrict ψ.ker (fun k => by
        rw [MonoidHom.mem_ker]
        exact (hψ k).trans k.2)
    have hf : Function.Surjective f := by
      rintro ⟨w, hw⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
      have hx : x ∈ π.ker := by
        rw [MonoidHom.mem_ker, ← hψ]
        exact hw
      exact ⟨⟨x, hx⟩, rfl⟩
    exact hπo.of_dvd_nat (Subgroup.card_dvd_of_surjective hf)

theorem fiLoc_of_oddCentralExt_quot {H : Type} [Group H] [Finite H] {n : ℕ}
    (hZ : Nat.card (center D) = 2) (hnc : ¬ IsMulCommutative D) (hn : n ≤ Nat.card D)
    {L K : Subgroup H} (hKL : K ≤ L) (hKq : CFSG.IsQuasisimple ↥K)
    (hK : IsOddCentralExt D (↥K ⧸ CFSG.oddCore ↥K)) : ∃ u : H, fiLoc n H L K u := by
  obtain ⟨e⟩ := oddCentralExt_mulEquiv hK (oddCore_quotient_eq_bot (A := ↥K))
  have hZ2 : Nat.card (center (↥K ⧸ CFSG.oddCore ↥K)) = 2 := by
    rw [card_center_of_mulEquiv' e]
    exact hZ
  have hnc' : ¬ IsMulCommutative (↥K ⧸ CFSG.oddCore ↥K) := by
    intro hcomm
    apply hnc
    refine ⟨⟨fun a b => ?_⟩⟩
    have h := hcomm.is_comm.comm (e.symm a) (e.symm b)
    simpa using congrArg e h
  have hO : CFSG.oddCore ↥K ≤ center ↥K := oddCore_le_center_of_quasisimple hKq hnc'
  have : Group.IsPerfect ↥K := hKq.1
  obtain ⟨u, huc, hu2⟩ := exists_central_involution hO hZ2
  refine ⟨(u : H), hKL u.2, ?_, hKL, ?_, hKq, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact hu2
  · intro k hk
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 huc ⟨k, hk⟩)
  · rw [Nat.card_congr e.toEquiv]
    exact hn

theorem isOddCentralExt_of_cover {H : Type} [Group H] [Finite H] {L K : Subgroup H}
    (hodd : Odd (Nat.card (center ↥L))) (hKL : K ≤ L) (hKq : CFSG.IsQuasisimple ↥K)
    (e : ↥((K.subgroupOf L).map (q ↥L)) ≃* D) : IsOddCentralExt D ↥K := by
  obtain ⟨π, hs, hc, ho⟩ := exists_oddCentralCover hodd hKL
  have hker : (e.toMonoidHom.comp π).ker = π.ker := by
    ext x
    simp [MonoidHom.mem_ker]
  refine ⟨hKq, e.toMonoidHom.comp π, e.surjective.comp hs, ?_, ?_⟩
  · rw [hker]
    exact hc
  · rw [hker]
    exact ho

theorem not_isMulCommutative_of_quasisimple {X : Type} [Group X] (hq : CFSG.IsQuasisimple X) :
    ¬ IsMulCommutative X := by
  intro hcomm
  obtain ⟨a, b, hab⟩ := hq.2.2
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm.is_comm.comm a b])

theorem oddCentralExt_of_mulEquiv (hq : CFSG.IsQuasisimple X) (e : X ≃* D) :
    IsOddCentralExt D X := by
  refine ⟨hq, e.toMonoidHom, e.surjective, ?_, ?_⟩
  · have : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 e.injective
    rw [this]
    exact bot_le
  · have : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 e.injective
    rw [this, Subgroup.card_bot]
    exact odd_one

theorem fiLoc_restrict {n : ℕ} {H : Type} [Group H] {L K : Subgroup H} {u : H} [Finite ↥L]
    (h : fiLoc n H L K u) : fiLoc n ↥L ⊤ (K.subgroupOf L) ⟨u, h.1⟩ := by
  obtain ⟨huL, hu2, hKL, hKu, hKq, hn⟩ := h
  let e : ↥(K.subgroupOf L) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKL
  refine ⟨Subgroup.mem_top _, by rw [Subgroup.orderOf_mk]; exact hu2, le_top, ?_,
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hKq, ?_⟩
  · intro k hk
    exact Subtype.ext (hKu k hk)
  · obtain ⟨f⟩ := oddQuot_equiv_of_surj e.toMonoidHom e.surjective (by
      have : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 e.injective
      rw [this, Subgroup.card_bot]
      exact odd_one)
    rw [Nat.card_congr f.toEquiv]
    exact hn

theorem three_le_pRank_of_subgroup_fixes {H : Type} [Group H] [Finite H] {K : Subgroup H}
    {n : ℕ} (hn : 8 ≤ n) (h : InvolutionFixesElem ↥K n)
    (hev : Even (Nat.card (↥K ⧸ center ↥K))) : 3 ≤ CFSG.pRank 2 H := by
  obtain ⟨α, hα1, hα2⟩ := exists_involutory_aut_of_even hev
  obtain ⟨E, -, hsq, hc, hcard⟩ := h α hα1 hα2
  refine three_le_pRank_of_elemAbelian (E.map K.subtype) ?_ ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hsq y hy)
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    exact congrArg Subtype.val (hc y hy z hz)
  · rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact hn.trans hcard

theorem oddCover_top_of_simple {s : TauCeti.SporadicName} (hfin : Finite (Carrier s))
    (hs : IsSimpleGroup (Carrier s)) (hnc : ∃ a b : Carrier s, a * b ≠ b * a) :
    OddCover s (⊤ : Subgroup (Carrier s)) := by
  have hZ : center (Carrier s) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (Carrier s)) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)
  refine ⟨(fStarSimple_top (Carrier s) hnc).isQuasisimple, ?_, ?_⟩
  · rw [card_center_of_mulEquiv' (Subgroup.topEquiv (G := Carrier s)), hZ, Subgroup.card_bot]
    exact odd_one
  · exact ⟨(quotientCenterEquiv' (Subgroup.topEquiv (G := Carrier s))).trans
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)⟩

theorem involutionFixesElem_of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K') {n : ℕ}
    (h : InvolutionFixesElem K n) : InvolutionFixesElem K' n := by
  intro α hα1 hα2
  have hβ1 : (MulAut.congr e).symm α ≠ 1 := fun h1 =>
    hα1 ((MulAut.congr e).symm.map_eq_one_iff.1 h1)
  have hβ2 : (MulAut.congr e).symm α * (MulAut.congr e).symm α = 1 := by
    rw [← map_mul, hα2, map_one]
  obtain ⟨S, hS1, hS2, hS3, hS4⟩ := h _ hβ1 hβ2
  refine ⟨S.map e.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have h2 : α (e x) = e ((MulAut.congr e).symm α x) := by
      rw [MulAut.congr_symm_apply]
      exact (e.apply_symm_apply _).symm
    show α (e x) = e x
    rw [h2, hS1 x hx]
  · rintro _ ⟨x, hx, rfl⟩
    show e x * e x = 1
    rw [← map_mul, hS2 x hx, map_one]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show e x * e y = e y * e x
    rw [← map_mul, ← map_mul, hS3 x hx y hy]
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hS4

theorem oddCore_eq_bot_of_center_two {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X)
    (hZ : Nat.card (center X) = 2) (heven : Even (Nat.card (X ⧸ center X))) :
    CFSG.oddCore X = ⊥ := by
  refine le_bot_iff.1 (sSup_le fun M hM => ?_)
  obtain ⟨hMn, hModd⟩ := hM
  have hs : IsSimpleGroup (X ⧸ center X) := hq.2.1
  have hMc : M ≤ center X := by
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
  have hdvd : Nat.card M ∣ 2 := hZ ▸ Subgroup.card_dvd_of_le hMc
  have h1 : Nat.card M = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact h
    · rw [h] at hModd
      exact absurd hModd (by decide)
  exact le_of_eq (Subgroup.eq_bot_of_card_eq _ h1)

theorem cover_pair_quotient {H : Type} [Group H] [Finite H] {s : TauCeti.SporadicName}
    {L K : Subgroup H} {u : H} {n : ℕ} (hcov : OddCover s L) (hQ : fiLoc n H L K u) :
    ∃ huL : u ∈ L, orderOf ((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L) = 2 ∧
      (∀ k ∈ bar (K.subgroupOf L), k * ((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L) =
        ((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L) * k) ∧ n ≤ Nat.card (bar (K.subgroupOf L)) := by
  obtain ⟨huL, hu2, hKL, hKu, hKq, hsz⟩ := hQ
  refine ⟨huL, ?_, ?_, hsz.trans (card_quotient_oddCore_le_bar hcov.odd_center hKL)⟩
  · have hu1 := sq_of_orderOf_two huL hu2
    have hnc : (⟨u, huL⟩ : ↥L) ∉ center ↥L := fun hz =>
      hcov.not_mem_centralizer_of_orderOf_two huL hu2 (mem_centralizer_iff.2 fun l hl =>
        congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨l, hl⟩))
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← QuotientGroup.mk_mul, hu1]
      rfl
    · intro h
      exact hnc ((QuotientGroup.eq_one_iff _).1 h)
  · intro k hk
    obtain ⟨k', hk', rfl⟩ := mem_bar.1 hk
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, central_subgroupOf huL hKu k' hk']

theorem card_quotient_oddCore_of_mulEquiv {X D : Type} [Group X] [Finite X] [Group D]
    (e : X ≃* D) (hD : CFSG.oddCore D = ⊥) : Nat.card (X ⧸ CFSG.oddCore X) = Nat.card D := by
  obtain ⟨f⟩ := oddQuot_equiv_of_surj e.toMonoidHom e.surjective (by
    have : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 e.injective
    rw [this, Subgroup.card_bot]
    exact odd_one)
  rw [Nat.card_congr f.toEquiv]
  exact Nat.card_congr
    ((QuotientGroup.quotientMulEquivOfEq hD).trans QuotientGroup.quotientBot).toEquiv

theorem center_top_eq_bot_of_simple {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hnc : ∃ a b : G, a * b ≠ b * a) : center ↥(⊤ : Subgroup G) = ⊥ := by
  have hZ : center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)
  have h1 := card_center_of_mulEquiv' (Subgroup.topEquiv (G := G))
  rw [hZ, Subgroup.card_bot] at h1
  exact Subgroup.eq_bot_of_card_eq _ h1

end CFSG.EvenSporadicStandard.Induction.Fi
