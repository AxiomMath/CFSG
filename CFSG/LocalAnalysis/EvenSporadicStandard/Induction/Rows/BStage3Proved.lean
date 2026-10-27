module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BRow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BRowFacts
public import CFSG.Milestones.CL_LIT_Monster_existence_Griess_Conway
public import CFSG.Monster.B.Fischer.Fi22Order

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.Monster.Existence CFSG.Monster.Existence.Compat
  CFSG.Open CFSG.Monster.GMS CFSG.EvenSporadicStandard.Induction.Hyp

section Proved

attribute [local irreducible] CFSG.Blueprint.NativeSporadic.carrierGroup in
theorem bPair_card_center (F : TwoAFacts) (hf : BabyCoverFacts) {u : Carrier .B}
    {K : Subgroup (Carrier .B)} (h : PairShape (· = 2 * ordTwistedE6 2) (Carrier .B) ⊤ K u) :
    Nat.card (center ↥K) = 2 := by
  have := finite_carrier_b F
  have hcov := hf.cover (Carrier .B) ⊤ K u ⟨Subgroup.topEquiv⟩ h
  obtain ⟨-, -, -, hKu, -⟩ := h
  have hKC : K ≤ ⊤ ⊓ centralizer ({u} : Set (Carrier .B)) := fun k hk =>
    ⟨mem_top _, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
  rw [← card_center_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hKC)]
  exact hcov.card_center

attribute [local irreducible] CFSG.Blueprint.NativeSporadic.carrierGroup in
theorem bIsKPinned_card (F : TwoAFacts) (hf : BabyCoverFacts) {X : Type} [Group X]
    (hX : IsKPinned .B (· = 2 * ordTwistedE6 2) X) :
    Nat.card (center X) = 2 ∧ Nat.card X = 2 * ordTwistedE6 2 := by
  obtain ⟨u, K, hP, ⟨e⟩⟩ := hX
  refine ⟨?_, ?_⟩
  · rw [card_center_of_mulEquiv' e]
    exact bPair_card_center F hf hP
  · rw [Nat.card_congr e.toEquiv]
    exact hP.2.2.2.2

theorem b_fit_proved (F : TwoAFacts) (hf : BabyCoverFacts) (t3 : BabyTableIII)
    (G : Type) [Group G] [Finite G] (L K : Subgroup G) (hL : IsSporadic ↥L .B) (hKL : K ≤ L)
    (hKq : CFSG.IsQuasisimple ↥K) (hO : CFSG.oddCore ↥K ≤ center ↥K)
    (hK : IsKPinned .B (· = 2 * ordTwistedE6 2) (↥K ⧸ CFSG.oddCore ↥K)) :
    Nat.card ↥K = 2 * ordTwistedE6 2 := by
  obtain ⟨hZ2, hquot⟩ := bIsKPinned_card F hf hK
  have : Group.IsPerfect ↥K := hKq.1
  obtain ⟨u, huc, hu2⟩ := exists_central_involution hO hZ2
  obtain ⟨e⟩ := hL
  have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore ↥K)
  rw [hquot] at h4
  have hOodd : Odd (Nat.card (CFSG.oddCore ↥K)) := odd_card_oddCore' ↥K
  have hfin := finite_carrier_b F
  let lB : Carrier .B := e ⟨(u : G), hKL u.2⟩
  have hlB2 : orderOf lB = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, Subgroup.orderOf_coe]
    exact hu2
  have hle : (K.subgroupOf L).map e.toMonoidHom ≤ centralizer ({lB} : Set (Carrier .B)) := by
    rintro _ ⟨x, hx, rfl⟩
    refine mem_centralizer_singleton_iff.2 ?_
    show e x * e ⟨(u : G), hKL u.2⟩ = e ⟨(u : G), hKL u.2⟩ * e x
    rw [← map_mul, ← map_mul]
    refine congrArg e (Subtype.ext ?_)
    exact congrArg (Subtype.val : ↥K → G)
      (Subgroup.mem_center_iff.1 huc ⟨(x : G), mem_subgroupOf.1 hx⟩)
  have hdvd : Nat.card ↥K ∣ Nat.card ↥(centralizer ({lB} : Set (Carrier .B))) := by
    have h5 := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv] at h5
  obtain ⟨k, -, hkC⟩ := t3.1 lB hlB2
  have hCk : Nat.card ↥(centralizer ({lB} : Set (Carrier .B))) = babyCentOrder k := hkC
  have hordpos : 0 < ordTwistedE6 2 := by unfold ordTwistedE6; norm_num
  have hKge : 2 * ordTwistedE6 2 ≤ Nat.card ↥K := by
    rw [h4]
    exact Nat.le_mul_of_pos_right _ Nat.card_pos
  have hk0 : k = 0 := by
    apply eq_zero_of_le_babyCentOrder
    rw [← hCk]
    exact (by omega : ordTwistedE6 2 ≤ Nat.card ↥K).trans (Nat.le_of_dvd Nat.card_pos hdvd)
  subst hk0
  rw [hCk, babyCentOrder_zero, h4] at hdvd
  have h6 : Nat.card (CFSG.oddCore ↥K) ∣ 2 := by
    refine Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < 2 * ordTwistedE6 2) ?_
    rw [show 2 * ordTwistedE6 2 * 2 = 4 * ordTwistedE6 2 by ring]
    exact hdvd
  have h7 : Nat.card (CFSG.oddCore ↥K) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h6 with h | h
    · exact h
    · rw [h] at hOodd
      exact absurd hOodd (by decide)
  rw [h4, h7, mul_one]

theorem orderOf_eq_of_isConj' {G : Type} [Group G] {a b : G} (h : IsConj a b) :
    orderOf a = orderOf b := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  rw [← hc]
  have := MulEquiv.orderOf_eq (MulAut.conj c) a
  rw [MulAut.conj_apply] at this
  exact this.symm

theorem comm_of_orderOf_two {G : Type} [Group G] {α β : G} (hα : orderOf α = 2)
    (hβ : orderOf β = 2) (hαβ : orderOf (α * β) = 2) : α * β = β * α := by
  have h1 : α * α = 1 := by rw [← pow_two, ← hα]; exact pow_orderOf_eq_one α
  have h2 : β * β = 1 := by rw [← pow_two, ← hβ]; exact pow_orderOf_eq_one β
  have h3 : (α * β) * (α * β) = 1 := by rw [← pow_two, ← hαβ]; exact pow_orderOf_eq_one _
  have hinvα : α⁻¹ = α := inv_eq_of_mul_eq_one_right h1
  have hinvβ : β⁻¹ = β := inv_eq_of_mul_eq_one_right h2
  have h4 : (α * β)⁻¹ = α * β := inv_eq_of_mul_eq_one_right h3
  rw [mul_inv_rev, hinvα, hinvβ] at h4
  exact h4.symm

theorem eq_one_or_self_of_mem_zpowers {G : Type} [Group G] {α x : G} (hα : orderOf α = 2)
    (hx : x ∈ zpowers α) : x = 1 ∨ x = α := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  have h := zpow_mod_orderOf α k
  rw [hα] at h
  simp only [Nat.cast_ofNat] at h
  rcases Int.emod_two_eq_zero_or_one k with h1 | h1
  · left
    rw [← h, h1, zpow_zero]
  · right
    rw [← h, h1, zpow_one]

theorem exists_pair_of_quotient {C B' : Type} [Group C] [Group B']
    (ψ : C ⧸ center C ≃* B') (H : Subgroup C) (b : C) (hZ : Nat.card (center C) = 2)
    (hZH : center C ≤ H) (hbb : b * b = 1) (hb : b ∉ center C)
    (hHb : ∀ x ∈ H, x * b = b * x) :
    ∃ (u : B') (K : Subgroup B'), orderOf u = 2 ∧ (∀ k ∈ K, k * u = u * k) ∧
      2 * Nat.card ↥K = Nat.card ↥H := by
  let f : C →* B' := ψ.toMonoidHom.comp (QuotientGroup.mk' (center C))
  have hfker : f.ker = center C := by
    ext x
    rw [MonoidHom.mem_ker]
    show ψ (QuotientGroup.mk x) = 1 ↔ x ∈ center C
    rw [map_eq_one_iff ψ ψ.injective, QuotientGroup.eq_one_iff]
  refine ⟨f b, H.map f, ?_, ?_, ?_⟩
  · refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, pow_two, hbb, map_one]
    · intro h
      exact hb (hfker ▸ h)
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, hHb x hx]
  · have h1 := Subgroup.card_ker_mul_card_range (f.comp H.subtype)
    have hker : (f.comp H.subtype).ker = (center C).subgroupOf H := by
      rw [← MonoidHom.comap_ker, hfker]
      rfl
    have hrange : (f.comp H.subtype).range = H.map f := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hker, hrange, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZH).toEquiv, hZ] at h1
    exact h1

theorem bTwoAPair_of_existence {G : Type} [Group G] (hE : MonsterExistenceStatement G)
    (F : TwoAFacts) : BTwoAPair := by
  obtain ⟨⟨hfin, -, -, -⟩, a, z, ha, hz, hnc, hinv, hA, hBz, hgraph⟩ := hE
  obtain ⟨-, c, -, -, hc1, -, -, -, hocc, hshape, -⟩ := hgraph
  obtain ⟨α, β, hα, hβ, hαβ⟩ := hocc 1
  have h1 := hshape α β 1 hα hβ hαβ
  unfold TwoPointShape at h1
  obtain ⟨N, hNn, hNe, hNc, hlie⟩ := h1
  have hαβ' : IsConj a (α * β) := hc1.trans hαβ.symm
  have hαo : orderOf α = 2 := (orderOf_eq_of_isConj' hα).symm.trans ha
  have hβo : orderOf β = 2 := (orderOf_eq_of_isConj' hβ).symm.trans ha
  have hαβo : orderOf (α * β) = 2 := (orderOf_eq_of_isConj' hαβ').symm.trans ha
  have hcomm : α * β = β * α := comm_of_orderOf_two hαo hβo hαβo
  have hββ : β * β = 1 := by rw [← pow_two, ← hβo]; exact pow_orderOf_eq_one β
  have hαα : α * α = 1 := by rw [← pow_two, ← hαo]; exact pow_orderOf_eq_one α
  have hβC : β ∈ cent α := mem_centralizer_singleton_iff.2 hcomm.symm
  obtain ⟨-, hcen, ⟨ψ⟩⟩ := hA α hα
  have hcardH : Nat.card ↥(cent2 α β) = 4 * ordTwistedE6 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [F.e6_card _ hlie, hNc, show (2 : ℕ) ^ 2 = 4 by norm_num] at h1
    omega
  have hZ2 : Nat.card (center ↥(cent α)) = 2 := by
    rw [← Subgroup.card_map_of_injective (cent α).subtype_injective, hcen, Nat.card_zpowers, hαo]
  let H' : Subgroup ↥(cent α) := (cent2 α β).subgroupOf (cent α)
  have hcardH' : Nat.card ↥H' = Nat.card ↥(cent2 α β) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : cent2 α β ≤ cent α)).toEquiv
  have hmemZ : ∀ x : ↥(cent α), x ∈ center ↥(cent α) → (x : G) ∈ zpowers α := fun x hx => by
    rw [← hcen]
    exact ⟨x, hx, rfl⟩
  have hZH : center ↥(cent α) ≤ H' := by
    intro x hx
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hmemZ x hx)
    refine mem_subgroupOf.2 ⟨x.2, mem_centralizer_singleton_iff.2 ?_⟩
    rw [← hk]
    exact (Commute.zpow_left (show Commute α β from hcomm) k).eq
  have hbb : (⟨β, hβC⟩ : ↥(cent α)) * ⟨β, hβC⟩ = 1 := Subtype.ext hββ
  have hb : (⟨β, hβC⟩ : ↥(cent α)) ∉ center ↥(cent α) := by
    intro hmem
    rcases eq_one_or_self_of_mem_zpowers hαo (hmemZ _ hmem) with h1 | h1
    · have : β = 1 := h1
      rw [this, orderOf_one] at hβo
      omega
    · have : β = α := h1
      rw [this, hαα, orderOf_one] at hαβo
      omega
  have hbH : ∀ x ∈ H', x * ⟨β, hβC⟩ = ⟨β, hβC⟩ * x := fun x hx =>
    Subtype.ext (mem_centralizer_singleton_iff.1 (mem_inf.1 (mem_subgroupOf.1 hx)).2)
  have ψ' : ↥(cent α) ⧸ center ↥(cent α) ≃* Carrier .B := ψ
  obtain ⟨u, K, hu, hKu, hK⟩ := exists_pair_of_quotient ψ' H' ⟨β, hβC⟩ hZ2 hZH hbb hb hbH
  exact ⟨u, K, mem_top _, hu, le_top, hKu, by omega⟩

end Proved

section Pinned


theorem bTwoAPair_pinned : BTwoAPair :=
  bTwoAPair_of_existence (G := MGriess) CFSG.Milestones.cl_lit_monster_existence_griess_conway
    twoARemaining.toFacts

theorem b_fit_pinned (hf : BabyCoverFacts) (G : Type) [Group G] [Finite G] (L K : Subgroup G)
    (hL : IsSporadic ↥L .B) (hKL : K ≤ L) (hKq : CFSG.IsQuasisimple ↥K)
    (hO : CFSG.oddCore ↥K ≤ center ↥K)
    (hK : IsKPinned .B (· = 2 * ordTwistedE6 2) (↥K ⧸ CFSG.oddCore ↥K)) :
    Nat.card ↥K = 2 * ordTwistedE6 2 :=
  b_fit_proved twoARemaining.toFacts hf babyTableIII G L K hL hKL hKq hO hK

noncomputable def stage3Row_b_proved (hf : BabyCoverFacts) (hmult : OddMultTrivial .B)
    (hfix : BFixesElem) : Stage3Row [.B] (fun _ => BPair) :=
  stage3Row_of_pinned bPair_eq (bPinnedFacts hf) hmult (lemma36DataQ_b hf hmult hfix)
    (le_refl 8) bTwoAPair_pinned
    (fun G _ _ L K hL hKL hKq hO hK => b_fit_pinned hf G L K hL hKL hKq hO hK)

structure BHyp31InputsNoPair : Prop where
  cover : BabyCoverFacts
  mult : OddMultTrivial .B
  quotient : BabyQuotient
  bRank : BCoverRank
  e6Rank : E6CoverRank
  e6Fixed : E6InvolutionFixed
  e6Four : E6FourNoEvenCover
  noCover : MonsterNoCover
  evenB : EvenCoverOutHered [.M] .B

theorem BHyp31InputsNoPair.toInputs (h : BHyp31InputsNoPair) : BHyp31Inputs :=
  ⟨h.cover, h.mult, bTwoAPair_pinned, h.quotient, h.bRank, h.e6Rank, h.e6Fixed, h.e6Four,
    h.noCover, h.evenB⟩

end Pinned

end CFSG.EvenSporadicStandard.Induction
