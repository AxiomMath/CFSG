module

public import CFSG.ClassicalInvolution.RouteD.TwinYP1Main

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

section Statement

variable (p f : ℕ) [Fact p.Prime]

@[expose] def TwinYGenByX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (tY : StatedLieTag) (nY : ℕ),
      TwinRow tY nY → LocalShapeT p f 2 tY nY (𝒞 K) z → ∀ T : Subgroup G,
      IsTwinAt (𝒞 K) K T z → IsClassicalMember p f T z → ∀ e : TwinElt K T z,
      ∀ J ∈ centralizingMembers (𝒞 K) {z}, J ≠ K → J ≠ T →
        ∀ M ∈ centralizingMembers (𝒞 K) {e.u},
          locImg (𝒞 K) e.u M ≤
            Subgroup.normalClosure (locImg (𝒞 K) e.u J : Set (locQuot (𝒞 K) e.u))

end Statement

section Gen

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {u : G}

theorem genSection_of_loc (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hA : ∀ L ∈ Ω, AEmpty Ω L) : GenSection p f (locFamily Ω u) := by
  have hS := genSection_layerHull hp hq hΩ hA (Subgroup.centralizer ({u} : Set G))
  rw [layerHull_centralizer_eq, locFamily_eq] at hS
  exact hS

theorem normalClosure_le_centralizer_of_not_conj (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hA : ∀ L ∈ Ω, AEmpty Ω L) (hn : CITBelowU p f (Nat.card G))
    (hu : ¬ ({u} : Set G) ⊆ Subgroup.center G) {J M : Subgroup (locQuot Ω u)}
    (hJ : J ∈ locFamily Ω u) (hM : M ∈ locFamily Ω u)
    (hno : ∀ g : locQuot Ω u, conjSub g J ≠ M) :
    Subgroup.normalClosure (J : Set (locQuot Ω u)) ≤
      Subgroup.centralizer (M : Set (locQuot Ω u)) := by
  have hS := genSection_of_loc (u := u) hp hq hΩ hA
  have h4 : Thm4Below p f (Nat.card G) := thm4Below_of_citBelow hn
  have hlt := card_locQuot_lt (Ω := Ω) hu
  have hcomm : ∀ g : locQuot Ω u, Commutes (conjSub g J) M := by
    intro g
    refine h4 hp hq (locQuot Ω u) hlt (locFamily Ω u) hS.hyp hS.oddCore hS.aEmpty
      (conjSub g J) (hS.hyp.conjInvariant g J hJ) M hM ?_
    rintro ⟨h, hh⟩
    exact hno (h * g) (by rw [conjSub_mul]; exact hh)
  unfold Subgroup.normalClosure
  rw [Subgroup.closure_le]
  intro b hb
  obtain ⟨a, ha, hab⟩ := Group.mem_conjugatesOfSet_iff.mp hb
  obtain ⟨c, hc⟩ := isConj_iff.mp hab
  have hbmem : b ∈ conjSub c J := by
    rw [← hc]
    exact conj_mem_conjSub ha
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro m hm
  exact (hcomm c b hbmem m hm).symm

end Gen

section Trans

variable {p f : ℕ} [Fact p.Prime]

theorem twinYTransitive_of_genByX (hΩall : HypOmegaModAll p f) (hAall : AEmptyAll p f)
    (hGen : TwinYGenByX p f) : TwinYTransitive p f := by
  intro G _ _ _ hnab K z S tY nY hrow hshape T hT clsT e K₁ hK₁ L hL
  have hΩ : HypOmegaMod p f (𝒞 K) := hΩall G hnab S.odd S.five K z S.cls S.below
  have hA : ∀ M ∈ 𝒞 K, AEmpty (𝒞 K) M := hAall G hnab S.odd S.five K z S.cls S.below
  obtain ⟨J, J', t, hJ, hJK, hJT, -, -, -, -, -⟩ :=
    exists_frameMembers hnab S hrow hshape hT clsT e
  have hKT : Commutes K T := hT.comm_K T hT.mem hT.ne
  have hJKc : Commutes J K := (hT.comm_K J hJ hJK).symm
  have hJTc : Commutes J T := (hT.comm_T J hJ hJT).symm
  have hJu : J ∈ centralizingMembers (𝒞 K) {e.u} := e.mem_centralizingMembers_u hJ.1 hJKc hJTc
  obtain ⟨-, hunc⟩ := twinElt_u_not_central hnab S e hKT
  have hJΦ : locImg (𝒞 K) e.u J ∈ locFamily (𝒞 K) e.u := mem_locFamily_iff.mpr ⟨J, hJu, rfl⟩
  have key : ∀ M ∈ locFamily (𝒞 K) e.u,
      ∃ g : locQuot (𝒞 K) e.u, conjSub g (locImg (𝒞 K) e.u J) = M := by
    intro M hM
    by_contra hno
    push Not at hno
    obtain ⟨M₀, hM₀, rfl⟩ := mem_locFamily_iff.mp hM
    have hle := normalClosure_le_centralizer_of_not_conj S.odd S.five hΩ hA S.below hunc hJΦ hM hno
    have hMN := hGen G hnab K z S tY nY hrow hshape T hT clsT e J hJ hJK hJT M₀ hM₀
    apply locImg_not_commutative S.inClass S.exact hM₀
    intro a ha b hb
    exact Subgroup.mem_centralizer_iff.mp (hle (hMN hb)) a ha
  obtain ⟨g₁, hg₁⟩ := key K₁ hK₁
  obtain ⟨g₂, hg₂⟩ := key L hL
  refine ⟨g₂ * g₁⁻¹, ?_⟩
  rw [← hg₁, ← conjSub_mul, inv_mul_cancel_right]
  exact hg₂

theorem twinYGenByX_of_transitive (hTrans : TwinYTransitive p f) : TwinYGenByX p f := by
  intro G _ _ _ hnab K z S tY nY hrow hshape T hT clsT e J hJ hJK hJT M hM
  have hJKc : Commutes J K := (hT.comm_K J hJ hJK).symm
  have hJTc : Commutes J T := (hT.comm_T J hJ hJT).symm
  have hJu : J ∈ centralizingMembers (𝒞 K) {e.u} := e.mem_centralizingMembers_u hJ.1 hJKc hJTc
  obtain ⟨g, hg⟩ := hTrans G hnab K z S tY nY hrow hshape T hT clsT e _
    (mem_locFamily_iff.mpr ⟨J, hJu, rfl⟩) _ (mem_locFamily_iff.mpr ⟨M, hM, rfl⟩)
  rw [← hg]
  intro x hx
  rw [mem_conjSub_iff] at hx
  have h := (Subgroup.normalClosure_normal (s := (locImg (𝒞 K) e.u J : Set _))).conj_mem _
    (Subgroup.subset_normalClosure hx) g
  simpa [mul_assoc] using h

theorem twinYSingle_of_genByX (hΩall : HypOmegaModAll p f) (hAall : AEmptyAll p f)
    (hP4 : Ih8G2D4 p f) (hGen : TwinYGenByX p f) : TwinYSingle p f :=
  twinYSingle_of_transitive hΩall hAall hP4 (twinYTransitive_of_genByX hΩall hAall hGen)

theorem twinYP1_of_genByX (hΩall : HypOmegaModAll p f) (hAall : AEmptyAll p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hGenT : TwinYGenT p f)
    (hGen : TwinYGenByX p f) : TwinYP1 p f :=
  twinYP1_of_inputs hΩall hAall hP4 hH hGenT (twinYTransitive_of_genByX hΩall hAall hGen)

theorem twinYType_of_genByX (hΩall : HypOmegaModAll p f) (hAall : AEmptyAll p f)
    (hP4 : Ih8G2D4 p f) (hGen : TwinYGenByX p f) (hRank : TwinYRank p f) : TwinYType p f :=
  twinYType_of_inputs hΩall hAall hP4 (twinYTransitive_of_genByX hΩall hAall hGen) hRank

end Trans

end CFSG.ClassicalInvolution.RouteD.TwinY
