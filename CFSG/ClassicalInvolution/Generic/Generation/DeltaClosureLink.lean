module

public import CFSG.ClassicalInvolution.Generic.Generation.DeltaClosureMain
import CFSG.ClassicalInvolution.Generic.InductionLocal
import CFSG.ClassicalInvolution.Generic.StepMember

public section

namespace CFSG.ClassicalInvolution.Generic.DeltaClosure

open CFSG.Open CFSG.ClassicalInvolution
open CFSG.ClassicalInvolution.Balance (oddCoreIn odd_card_oddCoreIn oddCoreIn_le)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {A : Subgroup G} {S : Set (Subgroup G)}

omit [Finite G] in
theorem SingleClassComponents.of_tags {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData p f X Φ)
    (hD : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4)
    (hmodel : ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n e : ℕ), IsFundTag t → t ≠ .G2 →
      t ≠ .trialityD4 → FundamentalSingleClass t (modelUniv t n p e Fact.out).D) :
    SingleClassComponents p f D :=
  fun i => hmodel (D.tag i) (D.rank i) (D.exp i) (D.isFundTag i) (hD i).1 (hD i).2

theorem odd_card_galoisField (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    Odd (Nat.card (GaloisField p f)) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  rw [GaloisField.card p f hf]
  exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow

omit [Finite G] in
theorem exists_conj_modOddIn {a : G} (D : LieSystemData p f (LocalQuot Ω a) (localFamily Ω a))
    (hD : SingleClassComponents p f D) {M K : Subgroup G}
    (hM : M ∈ centralizingMembers Ω {a}) (hK : K ∈ centralizingMembers Ω {a})
    (hnc : ∃ x ∈ M, ∃ y ∈ K, x * y * x⁻¹ * y⁻¹ ∉ oddCoreIn (centralizingLayer Ω {a})) :
    ∃ w ∈ centralizingLayer Ω {a}, modOddIn (centralizingLayer Ω {a}) K =
      modOddIn (centralizingLayer Ω {a}) (conjSub w M) := by
  set Y := centralizingLayer Ω {a} with hY
  have hMY : M ≤ Y := le_centralizingLayer hM
  have hKY : K ≤ Y := le_centralizingLayer hK
  have hMfam : modOddIn Y M ∈ localFamily Ω a := ⟨M.subgroupOf Y, ⟨M, hM, hMY, rfl⟩, rfl⟩
  have hKfam : modOddIn Y K ∈ localFamily Ω a := ⟨K.subgroupOf Y, ⟨K, hK, hKY, rfl⟩, rfl⟩
  obtain ⟨i, R, hR, hMR⟩ := D.fundamental _ hMfam
  obtain ⟨j, R', hR', hKR'⟩ := D.fundamental _ hKfam
  have hij : i = j := by
    by_contra hne
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    have hxY : x ∈ Y := hMY hx
    have hyY : y ∈ Y := hKY hy
    have hx' : QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨x, hxY⟩ ∈ modOddIn Y M :=
      ⟨⟨x, hxY⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have hy' : QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨y, hyY⟩ ∈ modOddIn Y K :=
      ⟨⟨y, hyY⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    rw [hMR] at hx'
    rw [hKR'] at hy'
    obtain ⟨r, -, hr⟩ := hx'
    obtain ⟨r', -, hr'⟩ := hy'
    have hcomm := D.commute i j hne r r'
    rw [hr, hr'] at hcomm
    exact hxy ((mk_comm_eq_iff hxY hyY).mp hcomm)
  subst hij
  obtain ⟨g, hg⟩ := hD i R hR R' hR'
  obtain ⟨wT, hwT⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥Y) (D.hom i g)
  refine ⟨(wT : G), wT.2, ?_⟩
  calc modOddIn Y K = R'.map (D.hom i) := hKR'
    _ = (conjSub g R).map (D.hom i) := by rw [hg]
    _ = conjSub (D.hom i g) (R.map (D.hom i)) := (conjSub_map _ _ _).symm
    _ = conjSub (D.hom i g) (modOddIn Y M) := by rw [← hMR]
    _ = conjSub (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) wT) (modOddIn Y M) := by
        rw [hwT]
    _ = (conjSub wT (M.subgroupOf Y)).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) :=
        conjSub_map _ _ _
    _ = ((conjSub (wT : G) M).subgroupOf Y).map
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) := by
        rw [conjSub_subgroupOf]
    _ = modOddIn Y (conjSub (wT : G) M) := rfl


theorem involutionLink_of_lie (hL : LocalHypotheses p f Ω A) {a : G} (haA : a ∈ A) (ha1 : a ≠ 1)
    (hS : S ⊆ Ω) (hinv : ∀ K ∈ S, ∃ z ∈ A, IsClassicalMember p f K z)
    (hcover : FrameCoversModO Ω S a) : InvolutionLink p f Ω A S a := by
  intro M hMmem z hz
  have hΩ := hL.inClass.conjInvariant
  have hodd := odd_card_galoisField hL.odd hL.five
  obtain ⟨K', hK'S, hK'a, hnc⟩ := hcover M hMmem
  have hK'mem : K' ∈ centralizingMembers Ω {a} := ⟨hS hK'S, hK'a⟩
  obtain ⟨D⟩ := hL.lie {a} (fun h => hL.noncentral a haA ha1 (h rfl))
  obtain ⟨w, hwY, hmod⟩ := exists_conj_modOddIn D (hL.single a haA ha1 D) hMmem hK'mem hnc
  obtain ⟨z', hz'A, hK'z'⟩ := hinv K' hK'S
  have hK'' : IsClassicalMember p f (conjSub w M) (w * z * w⁻¹) := hz.conj w
  have hwC : w ∈ Subgroup.centralizer ({a} : Set G) := centralizingLayer_le_centralizer Ω {a} hwY
  have hK''Y : conjSub w M ≤ centralizingLayer Ω {a} :=
    le_centralizingLayer (conjSub_mem_centralizingMembers hΩ hwC hMmem)
  have hU := mul_mem_oddCoreIn_of_modOddIn_eq hodd hK'z' hK'' (le_centralizingLayer hK'mem)
    hK''Y hmod
  obtain ⟨o, ho, hoz⟩ := exists_conj_of_mul_mem (sq_eq_one hK'') (sq_eq_one hK'z')
    (odd_card_oddCoreIn _) hU
  have hoY : o ∈ centralizingLayer Ω {a} := oddCoreIn_le _ ho
  refine ⟨K', hK'S, z', hz'A, hK'z', w⁻¹ * o⁻¹, mul_mem (inv_mem hwY) (inv_mem hoY), ?_⟩
  rw [hoz]
  group

theorem FrameSide.of_cover (hL : LocalHypotheses p f Ω A) (hA : IsElemAbelian 2 A)
    (h16 : 16 ≤ Nat.card A) (hS : S ⊆ Ω) (hne : S.Nonempty)
    (hinv : ∀ K ∈ S, ∃ z ∈ A, IsClassicalMember p f K z)
    (hgen : ∀ a ∈ A, IsFrameInvolution p f S a → CentralizerGenerationModO Ω A a)
    (hcover : ∀ a ∈ A, IsFrameInvolution p f S a → FrameCoversModO Ω S a) :
    FrameSide p f Ω A S where
  elem := hA
  card := h16
  subset := hS
  nonempty := hne
  involution := hinv
  generation := hgen
  link := fun a ha hfa => by
    obtain ⟨K, hKS, hK⟩ := hfa
    exact involutionLink_of_lie hL ha hK.ne_one hS hinv (hcover a ha ⟨K, hKS, hK⟩)

theorem fusionGenerated_of_lie (hL : LocalHypotheses p f Ω A) (hA : IsElemAbelian 2 A)
    (h16 : 16 ≤ Nat.card A) (hS : S ⊆ Ω) (hne : S.Nonempty)
    (hinv : ∀ K ∈ S, ∃ z ∈ A, IsClassicalMember p f K z)
    (hgen : ∀ a ∈ A, IsFrameInvolution p f S a → CentralizerGenerationModO Ω A a)
    (hcover : ∀ a ∈ A, IsFrameInvolution p f S a → FrameCoversModO Ω S a)
    (hconn : OmegaConnected Ω) : CFSG.ClassicalInvolution.Balance.FusionGenerated A :=
  fusionGenerated_of_deltaClosure hL.inClass
    (FrameSide.of_cover hL hA h16 hS hne hinv hgen hcover) hconn

end CFSG.ClassicalInvolution.Generic.DeltaClosure
