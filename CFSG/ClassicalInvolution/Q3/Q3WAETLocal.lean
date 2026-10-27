module

public import CFSG.ClassicalInvolution.Q3.Q3WAEDict
public import CFSG.ClassicalInvolution.Q3.Q3WANoA1

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement


structure ETCtx3 (tY : StatedLieTag) (nY : ℕ) {G : Type} [Group G] (Ω : Set (Subgroup G))
    (K : Subgroup G) (z : G) where
  hΩ : InClass3 Ω
  hex : ExactMembers3 Ω
  hK : K ∈ Ω
  hz : IsClassicalMember3 K z
  hP1 : LocalOddCentral Ω {z}
  hO3 : LocalOddThreeFree3 Ω z
  d : ShapeDictT 3 1 tY nY Ω z
  hY : YData3 tY nY

namespace ETCtx3

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag} {nY : ℕ}
  {K : Subgroup G} (c : ETCtx3 tY nY Ω K z)

include c

theorem hKz : K ∈ centralizingMembers Ω {z} := ⟨c.hK, isSubnormal_le c.hz.subnormal⟩

theorem ker_cop : ∀ n ∈ c.d.ψ.ker, ¬ 3 ∣ orderOf n := fun n hn => c.hY.cop n (c.d.ker_le hn)

variable [Finite G]

theorem locImg_self_le_Q₀ : locImg Ω z K ≤ c.d.Q₀ := by
  have hmem : locImg Ω z K ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨K, c.hKz, rfl⟩
  rcases c.d.fam_cases _ hmem with h | ⟨R, hR, hRK⟩
  · exact h
  · exfalso
    have hzY : z ∈ locLayer Ω z := le_centralizingLayer c.hKz c.hz.mem
    have hzK : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) ⟨z, hzY⟩ ∈
        locImg Ω z K := ⟨⟨z, hzY⟩, Subgroup.mem_subgroupOf.mpr c.hz.mem, rfl⟩
    rw [hRK] at hzK
    obtain ⟨r, hrR, hr⟩ := hzK
    have hrc : r ∈ Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K := by
      have := c.hY.perfK
      refine mem_center_of_comm_mem_center fun s => c.d.ker_le ?_
      rw [MonoidHom.mem_ker, map_commutatorElement, hr]
      rw [commutatorElement_def, ← mk_involution_central3 Ω z hzY (c.d.ψ s), mul_inv_cancel_right,
        mul_inv_cancel]
    have hr1 : r = 1 := c.hY.central R hR r hrR hrc
    rw [hr1, map_one] at hr
    exact mk_involution_ne_one3 Ω c.hz.orderOf_eq_two hzY hr.symm

theorem eq_of_locImg_le_Q₀ {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hLQ : locImg Ω z L ≤ c.d.Q₀) : L = K := by
  have hKQ := c.locImg_self_le_Q₀
  have hcL := card_locImg3 c.hΩ c.hex hL
  have hcK := card_locImg3 c.hΩ c.hex c.hKz
  have hcard := c.d.card_le
  rw [card_sl2_gf3] at hcard
  have e1 : locImg Ω z L = c.d.Q₀ := Subgroup.eq_of_le_of_card_ge hLQ (by rw [hcL]; exact hcard)
  have e2 : locImg Ω z K = c.d.Q₀ := Subgroup.eq_of_le_of_card_ge hKQ (by rw [hcK]; exact hcard)
  exact locImg_injOn3 c.hΩ c.hex c.hP1 c.hO3 hL c.hKz (e1.trans e2.symm)

theorem exists_fund_of_ne {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z}) (hLK : L ≠ K) :
    ∃ R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
      locImg Ω z L = R.map c.d.ψ := by
  have hmem : locImg Ω z L ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨L, hL, rfl⟩
  rcases c.d.fam_cases _ hmem with h | h
  · exact absurd (c.eq_of_locImg_le_Q₀ hL h) hLK
  · exact h

theorem exists_member_of_fund {R : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D) :
    ∃ L ∈ centralizingMembers Ω {z}, L ≠ K ∧ locImg Ω z L = R.map c.d.ψ := by
  obtain ⟨L, hL, hLR⟩ := mem_locFamily_iff.mp (c.d.mem_fam R hR)
  refine ⟨L, hL, fun hLK => ?_, hLR⟩
  subst hLK
  have h1 : Commutes (locImg Ω z L) (locImg Ω z L) := by
    intro a ha b hb
    have hb' : b ∈ c.d.ψ.range := by
      rw [hLR] at hb
      obtain ⟨x, _, rfl⟩ := hb
      exact ⟨x, rfl⟩
    exact c.d.commutes a (c.locImg_self_le_Q₀ ha) b hb'
  exact not_commutes_self3 c.hz (commutes_of_commutes_locImg3 c.hΩ c.hex c.hP1 c.hO3 hL hL h1)

theorem commutes_K_of_ne {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z}) (hLK : L ≠ K) :
    Commutes K L := by
  obtain ⟨R, hR, hLR⟩ := c.exists_fund_of_ne hL hLK
  refine commutes_of_commutes_locImg3 c.hΩ c.hex c.hP1 c.hO3 c.hKz hL ?_
  intro a ha b hb
  rw [hLR] at hb
  exact c.d.commutes a (c.locImg_self_le_Q₀ ha) b (by obtain ⟨x, _, rfl⟩ := hb; exact ⟨x, rfl⟩)

theorem eq_of_locImg_eq {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z}) (h : locImg Ω z L = locImg Ω z L') : L = L' :=
  locImg_injOn3 c.hΩ c.hex c.hP1 c.hO3 hL hL' h

omit [Finite G] in
theorem commutes_of_commutes_map {R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (h : Commutes (R.map c.d.ψ) (R'.map c.d.ψ)) : Commutes R R' := by
  intro a ha b hb
  exact (commutes_of_map_commute_exponent3 c.d.ψ (hker := c.d.ker_le) c.ker_cop
    (A := R') (L := R) (c.hY.pow3 R hR)
    (fun a' ha' l hl => (h _ ⟨l, hl, rfl⟩ _ ⟨a', ha', rfl⟩).symm) b hb a ha).symm

theorem commutes_iff_fund {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z})
    {R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hLR : locImg Ω z L = R.map c.d.ψ) (hLR' : locImg Ω z L' = R'.map c.d.ψ) :
    Commutes L L' ↔ Commutes R R' := by
  constructor
  · intro h
    have h1 := commutes_locImg_of_commutes (x := z) (Ω := Ω) h
    rw [hLR, hLR'] at h1
    exact c.commutes_of_commutes_map hR h1
  · intro h
    refine commutes_of_commutes_locImg3 c.hΩ c.hex c.hP1 c.hO3 hL hL' ?_
    rw [hLR, hLR']
    exact commutes_map_of_commutes _ h

theorem stdPair_of_fund {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z})
    {R R' W : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hW : LinearBlockStandardPair (GaloisField 3 1) W R R')
    (hLR : locImg Ω z L = R.map c.d.ψ) (hLR' : locImg Ω z L' = R'.map c.d.ψ) :
    ∃ W' : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W' L L' := by
  have := linearBlockStandardPair_map_central hW c.d.ψ c.d.ker_le
  rw [← hLR, ← hLR'] at this
  exact linearBlockStandardPair_of_locImg3' c.hΩ c.hex c.hP1 c.hO3 hL hL' this

theorem exists_nodes {r : ℕ} (R : Fin r → Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K)
    (hR : ∀ a, R a ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (adj : Fin r → Fin r → Prop)
    (hcomm : ∀ a b, a ≠ b → ¬ adj a b → ¬ adj b a → Commutes (R a) (R b))
    (hstd : ∀ a b, adj a b → ∃ W : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K,
      LinearBlockStandardPair (GaloisField 3 1) W (R a) (R b)) :
    ∃ j : Fin r → Subgroup G, (∀ a, j a ∈ centralizingMembers Ω {z} ∧ j a ≠ K ∧
        locImg Ω z (j a) = (R a).map c.d.ψ) ∧
      (∀ a b, a ≠ b → ¬ adj a b → ¬ adj b a → Commutes (j a) (j b)) ∧
      (∀ a b, adj a b →
        ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W (j a) (j b)) ∧
      (∀ a, Commutes K (j a)) := by
  choose j hj using fun a => c.exists_member_of_fund (hR a)
  refine ⟨j, fun a => ⟨(hj a).1, (hj a).2.1, (hj a).2.2⟩, ?_, ?_, ?_⟩
  · intro a b hab h1 h2
    exact (c.commutes_iff_fund (hj a).1 (hj b).1 (hR a) (hj a).2.2 (hj b).2.2).mpr
      (hcomm a b hab h1 h2)
  · intro a b hadj
    obtain ⟨W, hW⟩ := hstd a b hadj
    exact c.stdPair_of_fund (hj a).1 (hj b).1 hW (hj a).2.2 (hj b).2.2
  · intro a
    exact c.commutes_K_of_ne (hj a).1 (hj a).2.1

theorem exists_partner_transport (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {M : Subgroup G}
    (hM : M ∈ Ω) (hMK : M ≠ K) (hKM : Commutes K M) :
    ∃ β ∈ Ω, (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K β) ∧
      Commutes β M := by
  obtain ⟨g, hg⟩ := hsingle M hM
  have hw : g * z * g⁻¹ ∈ M := hg ▸ conj_mem_conjSub c.hz.mem
  have hK'm : conjSub g⁻¹ K ∈ centralizingMembers Ω {z} :=
    conjSub_inv_mem_centralizingMembers c.hΩ.conjInvariant c.hK hw hKM
  have hK'ne : conjSub g⁻¹ K ≠ K := by
    intro h
    apply hMK
    calc M = conjSub g K := hg
      _ = conjSub g (conjSub g⁻¹ K) := by rw [h]
      _ = K := conjSub_conjSub_inv g K
  obtain ⟨R₀, hR₀, hKR₀⟩ := c.exists_fund_of_ne hK'm hK'ne
  obtain ⟨R', hR', W, hW⟩ := c.hY.std R₀ hR₀
  obtain ⟨β', hβ'm, hβ'K, hβ'img⟩ := c.exists_member_of_fund hR'
  obtain ⟨W', hW'⟩ := c.stdPair_of_fund hK'm hβ'm hW hKR₀ hβ'img
  refine ⟨conjSub g β', c.hΩ.conjInvariant g β' hβ'm.1, ⟨conjSub g W', ?_⟩, ?_⟩
  · have h : LinearBlockStandardPair (GaloisField 3 1) (conjSub g W') (conjSub g (conjSub g⁻¹ K))
        (conjSub g β') := ModelFacts.linearBlockStandardPair_map_conj hW' g
    rwa [conjSub_conjSub_inv] at h
  · rw [hg]
    exact (commutes_conjSub_iff g).mpr (c.commutes_K_of_ne hβ'm hβ'K).symm

end ETCtx3

end CFSG.ClassicalInvolution.Q3.Q3W
