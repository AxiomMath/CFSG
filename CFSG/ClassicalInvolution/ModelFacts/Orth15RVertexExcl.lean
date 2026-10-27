module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinT
public import CFSG.ClassicalInvolution.RouteD.G2D4T3D4
public import CFSG.ClassicalInvolution.Generic.StepPerfect

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.G2D4Models
open CFSG.Open (IsElemAbelian classicalInvolutionOddCore)
open scoped MatrixGroups

section Params

variable {p f : ℕ} [Fact p.Prime]

theorem ne_two_of_isClassicalMember {G : Type} [Group G] [Finite G] {M : Subgroup G} {b : G}
    (hM : IsClassicalMember p f M b) : p ≠ 2 := by
  intro hp2
  subst hp2
  obtain ⟨e⟩ := hM.nonempty_equiv
  have cM := isCentralInvolution_of_isClassicalMember hM
  obtain ⟨bm, hbm⟩ : ∃ bm : ↥M, (bm : G) = b := ⟨⟨b, hM.mem⟩, rfl⟩
  set w := e (QuotientGroup.mk bm) with hw
  have hw1 : w ≠ 1 := by
    intro h
    have h1 : QuotientGroup.mk bm = (1 : ↥M ⧸ classicalInvolutionOddCore ↥M) :=
      e.injective (h.trans (map_one e).symm)
    have h2 : bm ∈ classicalInvolutionOddCore ↥M := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : orderOf bm ∣ Nat.card (classicalInvolutionOddCore ↥M) :=
      Subgroup.orderOf_dvd_natCard _ h2
    have h4 : orderOf bm = 2 := by
      rw [← Subgroup.orderOf_coe, hbm]
      exact hM.orderOf_eq_two
    rw [h4] at h3
    have hodd := CFSG.ComponentClassification.OddCore.odd_card ↥M
    exact absurd (hodd.of_dvd_nat h3) (by decide)
  have hwc : w ∈ Subgroup.center SL(2, GaloisField 2 f) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨x, rfl⟩ := e.surjective g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    have hcomm : bm * y = y * bm := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hbm]
      exact cM.central y.1 y.2)
    rw [hw, ← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm]
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hwc
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have h2 : (2 : GaloisField 2 f) = 0 := CharP.cast_eq_zero (GaloisField 2 f) 2
  have hr1 : r = 1 := by
    have h0 : (r + 1) ^ 2 = 0 := by
      linear_combination hr2 + (r + 1) * h2
    have := pow_eq_zero_iff (two_ne_zero) |>.mp h0
    linear_combination this - h2
  apply hw1
  ext i j
  rw [← hrA]
  simp [hr1]

theorem params_of_isClassicalMember {G : Type} [Group G] [Finite G] {M : Subgroup G} {b : G}
    (hM : IsClassicalMember p f M b) (hf : 0 < f) : p ≠ 2 ∧ 5 ≤ p ^ f := by
  have hp2 := ne_two_of_isClassicalMember hM
  refine ⟨hp2, ?_⟩
  obtain ⟨e⟩ := hM.nonempty_equiv
  have : Group.IsPerfect ↥M := hM.perfect
  have : Nontrivial ↥M := by
    refine ⟨⟨⟨b, hM.mem⟩, 1, fun h => ?_⟩⟩
    have h1 : b = 1 := congrArg Subtype.val h
    have := hM.orderOf_eq_two
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  exact five_le_pow_of_nonsolvable_witness hp2 hf e (Group.IsPerfect.not_isSolvable ↥M)

end Params

section D4

variable {p f : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

omit [Finite X] in
theorem false_of_twin_trialityD4 (hp : p ≠ 2) (hΦ : HypOmega p f Φ) (D : OmegaLie p f Φ)
    {i : Fin D.card} (ht : D.tag i = .trialityD4) {R R' : Subgroup (D.model i).K}
    (hR : R ∈ fundamentalSubgroups (D.tag i) (D.model i).D)
    (hR' : R' ∈ fundamentalSubgroups (D.tag i) (D.model i).D)
    (hK : R.map (D.hom i) ∈ Φ) (hK' : R'.map (D.hom i) ∈ Φ) {z : X}
    (hzK : IsUniqueInvolution (R.map (D.hom i)) z)
    (hzK' : IsUniqueInvolution (R'.map (D.hom i)) z)
    (hne : R.map (D.hom i) ≠ R'.map (D.hom i)) : False := by
  set ψ := D.hom i with hψ
  have hi : D.tag i = .G2 ∨ D.tag i = .trialityD4 := Or.inr ht
  have hinj : Function.Injective ψ := hom_injective_of_g2d4 hp D hi
  obtain ⟨c, hcz, hc⟩ := isUniqueInvolution_of_map hinj hzK
  obtain ⟨c', hc'z, hc'⟩ := isUniqueInvolution_of_map hinj hzK'
  have hcc : c' = c := hinj (hc'z.trans hcz.symm)
  rw [hcc] at hc'
  have hneR : R' ≠ R := fun e => hne (by rw [e])
  by_cases hconj : ∃ g, R' = R.map (MulAut.conj g).toMonoidHom
  · obtain ⟨g, hg⟩ := hconj
    have hg' : R' = conjSub g R := hg
    rw [hg'] at hc' hneR
    exact hneR (noTwinsFund_of_td4_tag hp ht (D.admissible i) R hR c hc g hc')
  · have hcardR : Nat.card R = Nat.card SL(2, GaloisField p f) := by
      rw [← Subgroup.card_map_of_injective hinj]
      exact natCard_member hΦ hK
    have hcardR' : Nat.card R' = Nat.card SL(2, GaloisField p f) := by
      rw [← Subgroup.card_map_of_injective hinj]
      exact natCard_member hΦ hK'
    exact d4OrdersDiffer p (D.tag i) (D.rank i) (D.exp i) ht (D.admissible i) R hR R' hR'
      hconj (hcardR.trans hcardR'.symm)

end D4

section Vertex

variable {p f : ℕ} [Fact p.Prime]

theorem twin_pair_in_sec (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {G : Type} [Group G] [Finite G]
    {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod p f Ω) {c : G}
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (D : LocalLieSystemAt p f (exactFamily Ω c) c)
    (j : Fin D.card) {M M' : Subgroup G} {b : G} (hM : M ∈ tqMembers Ω c)
    (hM' : M' ∈ tqMembers Ω c) (hMb : IsClassicalMember p f M b)
    (hM'b : IsClassicalMember p f M' b) (hne : M' ≠ M)
    (hMj : modOdd c (exactCore c M) ≤
      (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range)
    (hM'j : modOdd c (exactCore c M') ≤
      (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range) :
    ∃ (R R' : Subgroup (compModel D j).K)
      (z : ↥(centralizingLayer (exactFamily Ω c) {c}) ⧸
        classicalInvolutionOddCore ↥(centralizingLayer (exactFamily Ω c) {c})),
      R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D ∧
      R' ∈ fundamentalSubgroups (D.tag j) (compModel D j).D ∧
      R.map (D.hom j) ∈ secFam Ω c ∧ R'.map (D.hom j) ∈ secFam Ω c ∧
      IsUniqueInvolution (R.map (D.hom j)) z ∧ IsUniqueInvolution (R'.map (D.hom j)) z ∧
      R.map (D.hom j) ≠ R'.map (D.hom j) := by
  classical
  have hs' : SecData p f c (exactFamily Ω c) :=
    secData_exactFamily hΩ.conjInvariant hΩ.classical hc2 ⟨M, hM⟩
  have hmem : ∀ N ∈ tqMembers Ω c, exactCore c N ∈ centMembers (exactFamily Ω c) c :=
    fun N hN => ⟨exactCore_mem_exactFamily hN, exactCore_le_centralizer c N⟩
  obtain ⟨R, hR, hRM⟩ := exists_fundamental_of_modOdd_le_sec hs' D j (hmem M hM) hMj
  obtain ⟨R', hR', hRM'⟩ := exists_fundamental_of_modOdd_le_sec hs' D j (hmem M' hM') hM'j
  obtain ⟨hbY, hK, hK', hneK, hzK, hzK'⟩ := secFam_twin hp hq hΩ hc2 hM hM' hMb hM'b hne
  have hRφ := map_hom_eq_modOddIn hs' D j (hmem M hM) hRM
  have hR'φ := map_hom_eq_modOddIn hs' D j (hmem M' hM') hRM'
  refine ⟨R, R', QuotientGroup.mk' (classicalInvolutionOddCore
    ↥(centralizingLayer (exactFamily Ω c) {c})) ⟨b, hbY⟩, hR, hR', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hRφ]; exact hK
  · rw [hR'φ]; exact hK'
  · rw [hRφ]; exact hzK
  · rw [hR'φ]; exact hzK'
  · rw [hRφ, hR'φ]; exact hneK

theorem false_of_trialityD4_sec (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {G : Type} [Group G] [Finite G]
    {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod p f Ω) {c : G}
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (D : LocalLieSystemAt p f (exactFamily Ω c) c)
    (j : Fin D.card) (hD4 : D.tag j = .trialityD4) {M M' : Subgroup G} {b : G}
    (hM : M ∈ tqMembers Ω c) (hM' : M' ∈ tqMembers Ω c) (hMb : IsClassicalMember p f M b)
    (hM'b : IsClassicalMember p f M' b) (hne : M' ≠ M)
    (hMj : modOdd c (exactCore c M) ≤
      (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range)
    (hM'j : modOdd c (exactCore c M') ≤
      (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range) : False := by
  have hs' : SecData p f c (exactFamily Ω c) :=
    secData_exactFamily hΩ.conjInvariant hΩ.classical hc2 ⟨M, hM⟩
  obtain ⟨R, R', z, hR, hR', hKR, hK'R', hzKR, hzK'R', hneR⟩ :=
    twin_pair_in_sec hp hq hΩ hc2 D j hM hM' hMb hM'b hne hMj hM'j
  exact false_of_twin_trialityD4 hp (hypOmega_secFam hp hq hΩ hc2 hs' D)
    (LieSystemData.toOmegaLie D (omegaGen_secFam hs')) (i := j) hD4 hR hR' hKR hK'R' hzKR hzK'R'
    hneR

@[expose] def G2VertexExcl (p f : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (hΩ : HypOmegaMod p f Ω),
      (∀ M ∈ Ω, AEmpty Ω M) → ∀ c : G, IsPGroup 2 (Subgroup.zpowers c) →
        ∀ (D : LocalLieSystemAt p f (exactFamily Ω c) c) (j : Fin D.card), D.tag j = .G2 →
          ∀ (M M' : Subgroup G) (b : G), M ∈ tqMembers Ω c → M' ∈ tqMembers Ω c →
            IsClassicalMember p f M b → IsClassicalMember p f M' b → M' ≠ M →
              modOdd c (exactCore c M) ≤
                (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range →
              modOdd c (exactCore c M') ≤
                (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range →
                False

theorem g2d4VertexExcl_of_g2 (h : G2VertexExcl p f) : G2D4VertexExcl p f := by
  intro G _ _ Ω hΩ hA c hc2 D j hj M M' b hM hM' hMb hM'b hne hMj hM'j
  have hf : 0 < f := by
    have h1 : 1 ≤ D.exp j := (D.admissible j).2.1
    rcases D.exp_eq j with h2 | ⟨-, h2⟩ <;> omega
  obtain ⟨hp, hq⟩ := params_of_isClassicalMember hMb hf
  rcases hj with hG2 | hD4
  · exact h hp hq G Ω hΩ hA c hc2 D j hG2 M M' b hM hM' hMb hM'b hne hMj hM'j
  · exact false_of_trialityD4_sec hp hq hΩ hc2 D j hD4 hM hM' hMb hM'b hne hMj hM'j

end Vertex

end CFSG.ClassicalInvolution.Asc77
