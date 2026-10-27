module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSecXg
public import CFSG.ClassicalInvolution.Q3.TL3T19

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace TwinThin

section Fam

variable {G : Type} [Group G] [Finite G]

@[expose] def fam (K X' : Subgroup G) : Set (Subgroup G) :=
  {L | ∃ x : ↥X', conjSub (x : G) K = L}

theorem mem_fam {K X' : Subgroup G} {x : G} (hx : x ∈ X') : conjSub x K ∈ fam K X' :=
  ⟨⟨x, hx⟩, rfl⟩

theorem pSpan_fam {K X' : Subgroup G} (h : (⨆ x : ↥X', conjSub (x : G) K) = X') :
    pSpan (fam K X') = X' := by
  have : pSpan (fam K X') = ⨆ x : ↥X', conjSub (x : G) K := by
    apply le_antisymm
    · refine iSup₂_le fun I hI => ?_
      obtain ⟨x, rfl⟩ := hI
      exact le_iSup (fun x : ↥X' => conjSub (x : G) K) x
    · exact iSup_le fun x => le_iSup₂_of_le (conjSub (x : G) K) ⟨x, rfl⟩ le_rfl
  rw [this, h]

theorem fam_inv {K X' : Subgroup G} : ∀ L ∈ fam K X', ∀ x ∈ X', conjSub x L ∈ fam K X' := by
  rintro _ ⟨a, rfl⟩ x hx
  rw [← conjSub_mul]
  exact mem_fam (X'.mul_mem hx a.2)

theorem fam_trans {K X' : Subgroup G} : ∀ L ∈ fam K X', ∀ L' ∈ fam K X',
    ∃ x ∈ X', conjSub x L = L' := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  refine ⟨(b : G) * (a : G)⁻¹, X'.mul_mem b.2 (X'.inv_mem a.2), ?_⟩
  rw [← conjSub_mul, mul_assoc, inv_mul_cancel, mul_one]

theorem fam_subset {Ω : Set (Subgroup G)} (hF : GraphFam Ω (nbrAdj Ω)) {K X' : Subgroup G}
    (hK : K ∈ Ω) : fam K X' ⊆ Ω := by
  rintro _ ⟨x, rfl⟩
  exact hF.conjMem K hK x

@[expose] def DOutcome (P : Set (Subgroup G)) : Prop :=
  (∃ E : Subgroup G, E8Struct (pSpan P) E) ∨
    Nonempty (AEIdentOn P 7 AE.e64Sets AE.e64Sub) ∨
    (∃ m : ℕ, 5 ≤ m ∧ Nonempty (AEIdent P m)) ∨
    Nonempty (AEIdentOn P 8 AE.e29Sets AE.e29Sub)

end Fam

section Thin

variable {G : Type} [Group G] [Finite G]

theorem eq_of_mem_Qz' {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    (h8 : ∀ J ∈ Ω, Nat.card J = 8) {M N : Subgroup G} (hN : N ∈ Ω) (hth : ThinAt Ω M N)
    {z u : G} (hz : IsUniqueInvolution M z) (hu : IsUniqueInvolution N u) {x : G} (hxN : x ∈ N)
    (hxQ : x ∈ Qz z) : x = 1 ∨ x = u := by
  by_cases hx2 : x * x = 1
  · exact hu.unique x hxN hx2
  · exfalso
    apply hth.2 z hz
    have hxord : orderOf x = 4 := by
      have hdvd : orderOf x ∣ 8 := by
        rw [← h8 N hN]
        exact Subgroup.orderOf_dvd_natCard N hxN
      have hx1 : x ≠ 1 := fun h => hx2 (by rw [h, one_mul])
      have hne2 : orderOf x ≠ 2 := fun h => hx2 (by rw [← pow_two, ← h, pow_orderOf_eq_one])
      have hne1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
      have hne8 : orderOf x ≠ 8 := by
        intro h
        obtain ⟨-, P, hPN, hPnc⟩ := hΩ.omega1 N hN
        have hzN : Subgroup.zpowers x = N := by
          refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxN) ?_
          rw [Nat.card_zpowers, h, h8 N hN]
        apply hPnc
        refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
        have ha : (a : G) ∈ Subgroup.zpowers x := hzN ▸ hPN.1 a.2
        have hb : (b : G) ∈ Subgroup.zpowers x := hzN ▸ hPN.1 b.2
        obtain ⟨i, hi⟩ := ha
        obtain ⟨j, hj⟩ := hb
        show (a : G) * b = b * a
        rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
      have : orderOf x ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have hdiv : Nat.divisors 8 = {1, 2, 4, 8} := by decide
      rw [hdiv] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      omega
    have hUcard : Nat.card ↥(Subgroup.zpowers x) = 4 := by rw [Nat.card_zpowers, hxord]
    have hNR : N ∈ RSet Ω := mem_RSet_of_isPGroup hN (h2 N hN)
    have hUU : Subgroup.zpowers x ∈ USet Ω := by
      refine ⟨N, hNR, Subgroup.zpowers_le.mpr hxN, inferInstance, ?_⟩
      have h1 := Subgroup.relIndex_mul_card (Subgroup.zpowers x) N
      rw [inf_eq_left.mpr (Subgroup.zpowers_le.mpr hxN), hUcard, h8 N hN] at h1
      omega
    exact uAt_of_le_Qz hUU (Subgroup.zpowers_le.mpr hxN) (Subgroup.zpowers_le.mpr hxQ)

theorem isNormalTwoIn_pCore {X : Subgroup G} {w : G}
    (hXw : X ≤ Subgroup.centralizer ({w} : Set G))
    (hXn : (X.subgroupOf (Subgroup.centralizer ({w} : Set G))).Normal) :
    IsNormalTwoIn (pCoreOf 2 X) w := by
  have hN := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_subgroupOf 2 X
    (Subgroup.centralizer ({w} : Set G)) hXw hXn
  have hQC : pCoreOf 2 X ≤ Subgroup.centralizer ({w} : Set G) :=
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 X).trans hXw
  refine ⟨hQC, CFSG.RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 X, ?_⟩
  intro c hc p hp
  have := hN.conj_mem ⟨p, hQC hp⟩ (Subgroup.mem_subgroupOf.mpr hp) ⟨c, hc⟩
  exact Subgroup.mem_subgroupOf.mp this

theorem normalTwo_le_Qz {X Q : Subgroup G} {w : G} (hXw : X ≤ Subgroup.centralizer ({w} : Set G))
    (hXn : (X.subgroupOf (Subgroup.centralizer ({w} : Set G))).Normal) (hQX : Q ≤ X)
    (hQn : ∀ x ∈ X, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) (hQ2 : IsPGroup 2 ↥Q) : Q ≤ Qz w := by
  have hQnorm : (Q.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQX]
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hQn x hx y hy, fun hy => ?_⟩
    have := hQn x⁻¹ (X.inv_mem hx) _ hy
    simpa [mul_assoc] using this
  have hQP : Q ≤ pCoreOf 2 X :=
    CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 Q X hQX hQnorm hQ2
  exact hQP.trans (le_Qz (isNormalTwoIn_pCore hXw hXn))

end Thin

section Setting

variable {G : Type} [Group G] [Finite G]

theorem maxAdj_of_mem_maxOrb {Ω : Set (Subgroup G)} (hF : GraphFam Ω (nbrAdj Ω))
    {M : Subgroup G} {π' : Set (Subgroup G)} (h : π' ∈ maxOrbs (nbrAdj Ω) M) {L : Subgroup G}
    (hL : L ∈ π') : MaxAdj (nbrAdj Ω) M L :=
  ⟨adj_of_mem_isMaxOrb hF h hL, by rw [orbOf_eq_of_mem_isMaxOrb h hL]; exact h⟩

structure Setting (K₀ K K' : Subgroup G) (z : G) (π : Set (Subgroup G)) (g : G) : Prop where
  hs : TwinGraphStd K₀
  hK : K ∈ CoreAssembly.conjClass K₀
  hK' : K' ∈ twinSet (CoreAssembly.conjClass K₀) K
  hne : K' ≠ K
  hq8 : Nonempty (↥K ≃* QuaternionGroup 2)
  hA : AEmpty (CoreAssembly.conjClass K₀) K
  hz : IsUniqueInvolution K z
  hπ : π ∈ maxOrbs (nbrAdj (CoreAssembly.conjClass K₀)) K
  hH1 : NoCentralInv π
  hg : conjSub g K ∈ π
  hO : classicalInvolutionOddCore ↥(conjSub g (piGen π)) = ⊥
  thin : ∀ M N : Subgroup G, MaxAdj (nbrAdj (CoreAssembly.conjClass K₀)) M N →
    ThinAt (CoreAssembly.conjClass K₀) M N

variable {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)} {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem hos : OrbitStd (CoreAssembly.conjClass K₀) := S.hs.orbitStd

theorem hKX : K ≤ conjSub g (piGen π) := S.hos.le_conj_piGen S.hπ S.hg

theorem fam_gen : pSpan (TwinThin.fam K (conjSub g (piGen π))) = conjSub g (piGen π) :=
  pSpan_fam (TwinSecXg.sec_gen S.hos S.hπ S.hg)

theorem card8 : ∀ J ∈ CoreAssembly.conjClass K₀, Nat.card J = 8 := by
  intro J hJ
  rw [TwinSecXg.card_eq_of_mem_conjClass S.hK hJ, Nat.card_congr S.hq8.some.toEquiv]
  simp [Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem aEmpty : ∀ J ∈ CoreAssembly.conjClass K₀, AEmpty (CoreAssembly.conjClass K₀) J :=
  Asc77.T3.aEmpty_forall_of_transitive' S.hs.hyp.conjInvariant (TwinSecXg.conj_trans_of_mem_conjClass S.hK) S.hA

theorem le_cent : conjSub g (piGen π) ≤ Subgroup.centralizer ({g * z * g⁻¹} : Set G) :=
  (S.hos.conj_piGen_le_centralizer S.hK S.hπ S.hH1 S.hz g).1

theorem normal_cent :
    ((conjSub g (piGen π)).subgroupOf (Subgroup.centralizer ({g * z * g⁻¹} : Set G))).Normal :=
  S.hos.conj_piGen_normal S.hK S.hπ S.hH1 S.hz g

theorem mem_fam_self : K ∈ fam K (conjSub g (piGen π)) := by
  have := mem_fam (K := K) (X' := conjSub g (piGen π)) (Subgroup.one_mem _)
  rwa [conjSub_one] at this

theorem twin_mem_fam : K' ∈ fam K (conjSub g (piGen π)) := by
  obtain ⟨a, ha, hKa⟩ := TwinSecXg.twin_conj S.hos S.hK S.hπ S.hH1 S.hg S.hK'
  rw [← hKa]
  exact mem_fam ha

theorem maxAdj_fam {L : Subgroup G} (hL : L ∈ fam K (conjSub g (piGen π))) :
    MaxAdj (nbrAdj (CoreAssembly.conjClass K₀)) (conjSub g K) L := by
  obtain ⟨x, rfl⟩ := hL
  have hπ' : conjSub g '' π ∈ maxOrbs (nbrAdj (CoreAssembly.conjClass K₀)) (conjSub g K) :=
    isMaxOrb_conj S.hos.graph S.hπ g
  refine maxAdj_of_mem_maxOrb S.hos.graph hπ' ?_
  have hKmem : K ∈ conjSub g '' π := S.hos.mem_conj_image_of_mem S.hπ S.hg
  have hx : (x : G) ∈ piGen (conjSub g '' π) := by
    rw [piGen_conj]
    exact x.2
  exact stable_of_maxOrb S.hos.graph hπ' (x : G) hx K hKmem

theorem exists_normalTwo {L : Subgroup G} (hL : L ∈ fam K (conjSub g (piGen π))) {u : G}
    (hu : IsUniqueInvolution L u) :
    ∃ Q : Subgroup G, Q ≤ conjSub g (piGen π) ∧
      (∀ x ∈ conjSub g (piGen π), ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧ IsPGroup 2 ↥Q ∧ u ∈ Q := by
  have hth := S.thin _ _ (S.maxAdj_fam hL)
  obtain ⟨Q, ⟨hQC, hQ2, hQn⟩, huQ⟩ := hth.1 (g * z * g⁻¹) u (S.hz.conj g) hu
  have hLX : L ≤ conjSub g (piGen π) := by
    obtain ⟨x, rfl⟩ := hL
    have := conjSub_mono (n := (x : G)) S.hKX
    rwa [conjSub_eq_self_of_mem x.2] at this
  refine ⟨Q ⊓ conjSub g (piGen π), inf_le_right, fun x hx q hq => ?_, hQ2.to_le inf_le_left,
    Subgroup.mem_inf.mpr ⟨huQ, hLX hu.mem⟩⟩
  exact Subgroup.mem_inf.mpr ⟨hQn x (S.le_cent hx) q (Subgroup.mem_inf.mp hq).1,
    (conjSub g (piGen π)).mul_mem ((conjSub g (piGen π)).mul_mem hx (Subgroup.mem_inf.mp hq).2)
      ((conjSub g (piGen π)).inv_mem hx)⟩

theorem thin_inf {L : Subgroup G} (hL : L ∈ fam K (conjSub g (piGen π))) {u : G}
    (hu : IsUniqueInvolution L u) {Q : Subgroup G} (hQX : Q ≤ conjSub g (piGen π))
    (hQn : ∀ x ∈ conjSub g (piGen π), ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) (hQ2 : IsPGroup 2 ↥Q) {x : G}
    (hxL : x ∈ L) (hxQ : x ∈ Q) : x = 1 ∨ x = u := by
  have hLΩ : L ∈ CoreAssembly.conjClass K₀ :=
    fam_subset S.hos.graph S.hK hL
  exact eq_of_mem_Qz' S.hs.hyp S.hs.two S.card8 hLΩ (S.thin _ _ (S.maxAdj_fam hL))
    (S.hz.conj g) hu hxL
    (normalTwo_le_Qz S.le_cent S.normal_cent hQX hQn hQ2 hxQ)

theorem outcomes {n : ℕ} (hD : ThmDGenBelow 3 n)
    (hXn : Nat.card ↥(conjSub g (piGen π)) < n) :
    DOutcome (fam K (conjSub g (piGen π))) := by
  have hP : pSpan (fam K (conjSub g (piGen π))) = conjSub g (piGen π) := S.fam_gen
  have hPΩ : fam K (conjSub g (piGen π)) ⊆ CoreAssembly.conjClass K₀ :=
    fam_subset S.hos.graph S.hK
  have hcard : Nat.card ↥(pSpan (fam K (conjSub g (piGen π)))) < n := by rw [hP]; exact hXn
  have htrans : ∀ L ∈ fam K (conjSub g (piGen π)), ∀ L' ∈ fam K (conjSub g (piGen π)),
      ∃ x ∈ pSpan (fam K (conjSub g (piGen π))), conjSub x L = L' := by
    rw [hP]; exact fam_trans
  have hinv : ∀ L ∈ fam K (conjSub g (piGen π)), ∀ x ∈ pSpan (fam K (conjSub g (piGen π))),
      conjSub x L ∈ fam K (conjSub g (piGen π)) := by
    rw [hP]; exact fam_inv
  have hodd : classicalInvolutionOddCore ↥(pSpan (fam K (conjSub g (piGen π)))) = ⊥ := by
    rw [hP]; exact S.hO
  have hE2 : ∀ L ∈ fam K (conjSub g (piGen π)), ∀ u : G, IsUniqueInvolution L u →
      ∃ Q : Subgroup G, Q ≤ pSpan (fam K (conjSub g (piGen π))) ∧
        (∀ x ∈ pSpan (fam K (conjSub g (piGen π))), ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧ IsPGroup 2 Q ∧
          u ∈ Q := by
    rw [hP]; exact fun L hL u hu => S.exists_normalTwo hL hu
  have hthin : ∀ L ∈ fam K (conjSub g (piGen π)), ∀ u : G, IsUniqueInvolution L u →
      ∀ Q : Subgroup G, Q ≤ pSpan (fam K (conjSub g (piGen π))) →
        (∀ x ∈ pSpan (fam K (conjSub g (piGen π))), ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) → IsPGroup 2 Q →
          ∀ x ∈ L, x ∈ Q → x = 1 ∨ x = u := by
    rw [hP]; exact fun L hL u hu Q hQX hQn hQ2 x hxL hxQ => S.thin_inf hL hu hQX hQn hQ2 hxL hxQ
  have h8 := S.card8
  rcases hD G (CoreAssembly.conjClass K₀) S.hs.hyp S.hs.two
      (fun J hJ => by rw [h8 J hJ]; norm_num) S.aEmpty _ hPΩ hcard htrans hinv hodd hE2 with
    hsing | ⟨W, hW⟩ | ⟨E, hE⟩ | h64 | hAE | h29
  · exact absurd (hsing _ S.twin_mem_fam _ S.mem_fam_self) S.hne
  · exact (false_of_WIn_eq S.hs.hyp S.hs.two h8 hPΩ ⟨K, S.mem_fam_self⟩ hinv hthin hW).elim
  · exact Or.inl ⟨E, hE⟩
  · exact Or.inr (Or.inl h64)
  · exact Or.inr (Or.inr (Or.inl hAE))
  · exact Or.inr (Or.inr (Or.inr h29))

end Setting

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
