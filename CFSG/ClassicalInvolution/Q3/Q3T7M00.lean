module

public import CFSG.ClassicalInvolution.Q3.Q3T8Bridge
public import CFSG.ClassicalInvolution.Q3.Q3T7EStmt
public import CFSG.ClassicalInvolution.Q3.Q3T6LinEquiv
public import CFSG.ClassicalInvolution.Q3.Q3T7T2Mem

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7M

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement MatrixGroups

abbrev HM {G : Type} [Group G] (Ω : Set (Subgroup G)) : Prop := HypOmegaModU (.sl2 3 1) Ω

namespace HM

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem toGen [Finite G] (hΩ : HM Ω) : HypOmegaGen Ω :=
  hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΩ

instance [Finite G] : Coe (HM Ω) (HypOmegaGen Ω) := ⟨toGen⟩

theorem exists_uniqueInvolution [Finite G] (hΩ : HM Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    ∃ z : G, IsUniqueInvolution K z :=
  Sec6Gen.exists_uniqueInvolution hΩ.toGen hK

theorem isQuatSub_of_mem_RSet [Finite G] (hΩ : HM Ω) {R : Subgroup G}
    (hR : R ∈ RSet Ω) : IsQuatSub R :=
  Sec6Gen.isQuatSub_of_mem_RSet hΩ.toGen hR

theorem eight_le_of_mem_RSet [Finite G] (hΩ : HM Ω) {R : Subgroup G}
    (hR : R ∈ RSet Ω) : 8 ≤ Nat.card R :=
  Sec6Gen.eight_le_of_mem_RSet hΩ.toGen hR

theorem center_two [Finite G] (hΩ : HM Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {z : G} (hz : IsUniqueInvolution K z) :
    ∀ w ∈ K, IsPGroup 2 (Subgroup.zpowers w) → (∀ y ∈ K, ⁅w, y⁆ ∈ oddCoreOf K) →
      w = 1 ∨ w = z :=
  Sec6Gen.center_two hΩ.toGen hK hz

theorem exists_noncentral [Finite G] (hΩ : HM Ω) {J : Subgroup G}
    (hJ : J ∈ Ω) {A : Subgroup G} (hAJ : A ≤ J) (hA2 : IsPGroup 2 A) (hA3 : 3 ≤ Nat.card A) :
    ∃ v ∈ A, ¬ ∀ w ∈ J, v * w = w * v :=
  Sec6Gen.exists_noncentral hΩ.toGen hJ hAJ hA2 hA3

theorem card_le_two_of_le_inf [Finite G] (hΩ : HM Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {A : Subgroup G} (hA : IsPGroup 2 A) (hAK : A ≤ K)
    (hAJ : A ≤ J) : Nat.card A ≤ 2 :=
  Sec6Gen.card_le_two_of_le_inf hΩ.toGen hK hJ hKJ hA hAK hAJ

theorem eq_of_le_of_le [Finite G] (hΩ : HM Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) {A : Subgroup G} (hA : IsPGroup 2 A) (h4 : 4 ≤ Nat.card A)
    (hAK : A ≤ K) (hAJ : A ≤ J) : K = J :=
  Sec6Gen.eq_of_le_of_le hΩ.toGen hK hJ hA h4 hAK hAJ

theorem le_normalizer_of_le_centralizer [Finite G] (hΩ : HM Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G}
    (hz : IsUniqueInvolution K z) {A : Subgroup G} (hAJ : A ≤ J) (hA2 : IsPGroup 2 A)
    (hA3 : 3 ≤ Nat.card A) (hAc : A ≤ Subgroup.centralizer ({z} : Set G)) :
    A ≤ Subgroup.normalizer (K : Set G) :=
  Sec6Gen.le_normalizer_of_le_centralizer hΩ.toGen hK hJ hKJ hz hAJ hA2 hA3 hAc

theorem comm_le_oddCore_of_twin [Finite G] (hΩ : HM Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G} (hzK : IsUniqueInvolution K z)
    (hzJ : IsUniqueInvolution J z) : ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J :=
  Sec6Gen.comm_le_oddCore_of_twin hΩ.toGen hK hJ hKJ hzK hzJ

theorem le_normalizer_of_twin [Finite G] (hΩ : HM Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G} (hzK : IsUniqueInvolution K z)
    (hzJ : IsUniqueInvolution J z) : K ≤ Subgroup.normalizer (J : Set G) :=
  Sec6Gen.le_normalizer_of_twin hΩ.toGen hK hJ hKJ hzK hzJ

theorem commutes_of_twin_of_isPGroup [Finite G] (hΩ : HM Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G}
    (hzK : IsUniqueInvolution K z) (hzJ : IsUniqueInvolution J z) {A B : Subgroup G}
    (hA : A ≤ K) (hB : B ≤ J) (hAB : IsPGroup 2 ↥(A ⊔ B)) : Commutes A B :=
  Sec6Gen.commutes_of_twin_of_isPGroup hΩ.toGen hK hJ hKJ hzK hzJ hA hB hAB

theorem exists_data_of_mem_USet [Finite G] (hΩ : HM Ω) {U : Subgroup G}
    (hU : U ∈ USet Ω) :
    ∃ R ∈ RSet Ω, ∃ J ∈ Ω, IsSylow2In R J ∧ U ≤ R ∧ IsCyclic ↥U ∧
      Nat.card R = 2 * Nat.card U ∧ 4 ≤ Nat.card U :=
  Sec6Gen.exists_data_of_mem_USet hΩ.toGen hU

theorem isPGroup_of_mem_USet [Finite G] (hΩ : HM Ω) {U : Subgroup G}
    (hU : U ∈ USet Ω) : IsPGroup 2 U :=
  Sec6Gen.isPGroup_of_mem_USet hΩ.toGen hU

theorem exists_member_of_mem_USet [Finite G] (hΩ : HM Ω) {U : Subgroup G}
    (hU : U ∈ USet Ω) : ∃ K ∈ Ω, U ≤ K :=
  Sec6Gen.exists_member_of_mem_USet hΩ.toGen hU

theorem eq_of_mem_USet [Finite G] (hΩ : HM Ω) {U : Subgroup G}
    (hU : U ∈ USet Ω) {K K' : Subgroup G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hUK : U ≤ K)
    (hUK' : U ≤ K') : K = K' :=
  Sec6Gen.eq_of_mem_USet hΩ.toGen hU hK hK' hUK hUK'

theorem natCard_eq_of_mem_USet [Finite G] (hΩ : HM Ω) {K U V : Subgroup G} (hK : K ∈ Ω)
    (hU : U ∈ USet Ω) (hV : V ∈ USet Ω) (hUK : U ≤ K) (hVK : V ≤ K) :
    Nat.card U = Nat.card V :=
  Sec6Gen.natCard_eq_of_mem_USet hΩ.toGen hK hU hV hUK hVK

theorem oddGen [Finite G] (hΩ : HM Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} = K := by
  obtain ⟨z, hz⟩ := hΩ.classical K hK
  obtain ⟨e⟩ := hz.nonempty_equiv_sl2Three
    (MemberType.isSolvableType_sl2.mpr (by norm_num))
  obtain ⟨π, hπs, hπk⟩ := Q3T7T2.exists_proj e
  exact Q3T7T2.odd_closure_of_proj π hπs hπk

theorem nonempty_equiv_sl2 (hΩ : HM Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    Nonempty (↥K ⧸ classicalInvolutionOddCore ↥K ≃* SL(2, GaloisField 3 1)) := by
  obtain ⟨z, hz⟩ := hΩ.classical K hK
  exact hz.nonempty_equiv_sl2

end HM

end CFSG.ClassicalInvolution.Q3.Q3T7M

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Disc3
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement MatrixGroups

section Vocab


structure EInputs : Prop where
  simple : ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), Q3T7M.HM Ω →
    CITBelowT (.sl2 3 1) (Nat.card G) → classicalInvolutionOddCore G = ⊥ →
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable ↥N → N = ⊥) → (⨆ J ∈ Ω, J) = ⊤ →
    ∀ K ∈ Ω, (∀ J ∈ Ω, ∃ g : G, conjSub g K = J) →
      ∃ F : Subgroup G, F.Normal ∧ IsSimpleGroup ↥F ∧ (∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x) ∧
        Subgroup.centralizer (F : Set G) = ⊥

structure EStand {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (S : Sylow 2 G) (R W : Subgroup G) : Prop where
  hyp : Q3T7M.HM Ω
  below : CITBelowT (.sl2 3 1) (Nat.card G)
  ih : IH8T 3 1 (Nat.card G)
  mem : K ∈ Ω
  aEmpty : AEmpty Ω K
  twin : ∃ K' ∈ twinSet Ω K, K' ≠ K ∧ ∃ R' ∈ RSet Ω, R' ≤ K' ∧ R' ≤ (S : Subgroup G)
  hR : R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G)
  hW : W ∈ WSet Ω ∧ W ≤ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), conjSub s W = W
  ob : EInputs

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {S : Sylow 2 G}
  {R W : Subgroup G}

theorem ih8T_mono {m n : ℕ} (hmn : m ≤ n) (h : IH8T 3 1 n) : IH8T 3 1 m :=
  Q3T7E.ih8T_mono hmn h

theorem EStand.modU (h : EStand Ω K S R W) : HypOmegaModU (.sl2 3 1) Ω := h.hyp

theorem EStand.hypGen (h : EStand Ω K S R W) : HypOmegaGen Ω :=
  hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) h.hyp

theorem EStand.of_stand3 (ob : EInputs) (h : Q3T7E.EStand3 Ω K S R W) : EStand Ω K S R W where
  ob := ob
  hyp := h.hyp
  below := h.below
  ih := h.ih
  mem := h.mem
  aEmpty := h.aEmpty
  twin := h.twin
  hR := h.hR
  hW := h.hW

theorem EStand.toStand3 (h : EStand Ω K S R W) : Q3T7E.EStand3 Ω K S R W where
  hyp := h.hyp
  below := h.below
  ih := h.ih
  mem := h.mem
  aEmpty := h.aEmpty
  twin := h.twin
  hR := h.hR
  hW := h.hW

end Vocab

@[expose] def Thm4Below (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ (Ω : Set (Subgroup G)),
    HypOmegaModU (.sl2 3 1) Ω → classicalInvolutionOddCore G = ⊥ → (∀ K ∈ Ω, AEmpty Ω K) →
      ∀ K ∈ Ω, ∀ J ∈ Ω, (¬ ∃ g : G, conjSub g K = J) → Commutes K J

@[expose] def Thm2Below (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ (Ω : Set (Subgroup G)),
    HypOmegaModU (.sl2 3 1) Ω → classicalInvolutionOddCore G = ⊥ → (⨆ J ∈ Ω, J) = ⊤ → ∀ K ∈ Ω,
      (∀ J ∈ Ω, ∃ g : G, conjSub g K = J) →
        ∀ z : G, IsUniqueInvolution K z → (∃ N : Subgroup G, N.Normal ∧ IsPGroup 2 N ∧ z ∈ N) →
          K.Normal

@[expose] def Thm2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)),
    HypOmegaModU (.sl2 3 1) Ω → classicalInvolutionOddCore G = ⊥ → (⨆ J ∈ Ω, J) = ⊤ → ∀ K ∈ Ω,
      (∀ J ∈ Ω, ∃ g : G, conjSub g K = J) →
        ∀ z : G, IsUniqueInvolution K z → (∃ N : Subgroup G, N.Normal ∧ IsPGroup 2 N ∧ z ∈ N) →
          K.Normal

section IH


theorem thm4Below_of_ih {n : ℕ} (h : IH8T 3 1 n) : Thm4Below n :=
  fun G _ _ hG Ω hΩ hO hA => h.thm4 (by norm_num) (by norm_num) G hG Ω hΩ hO hA

theorem thm2Below_of_ih {n : ℕ} (h : IH8T 3 1 n) : Thm2Below n :=
  fun G _ _ hG Ω hΩ hO hgen K hK htr z hz hN =>
    h.thm2 (by norm_num) (by norm_num) G hG Ω hΩ hO hgen K hK htr z hz hN

end IH

section Six

variable {G : Type} [Group G]

@[expose] def L6_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod Ω →
    ∀ R ∈ RSet Ω, ∀ Y X : Subgroup G, R ≤ Y → X ≤ Y → (∀ y ∈ Y, conjSub y X = X) →
      R ⊓ X = ⊥ →
        (⨆ R' ∈ {R' : Subgroup G | (∃ y ∈ Y, R' = conjSub y R) ∧ R' ≤ R ⊔ X}, R') ≤
            R ⊔ oddCoreOf X ∧
          ⁅R, X⁆ ≤ oddCoreOf X

end Six

section Coe

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

instance modU_coe_gen : Coe (HypOmegaModU (.sl2 3 1) Ω) (HypOmegaGen Ω) :=
  ⟨hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1)⟩

end Coe

section ExactHyp

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

structure HypOmega (Ω : Set (Subgroup G)) : Prop where
  conjInvariant : ConjInvariant Ω
  classical : ∀ L ∈ Ω, ∃ z : G, IsClassicalMemberU (.sl2 3 1) L z
  exact : ExactMembers Ω
  omega4 : ∀ K ∈ Ω, ∀ J ∈ Ω, K ≠ J →
    padicValNat 2 (Nat.card ↥(K ⊓ J)) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(K ⊓ J)) = 1 → Commutes K J)
  omega5 : ∀ K ∈ Ω, ∀ J ∈ Ω, K ≠ J → ∀ z : G, IsUniqueInvolution K z → ∀ v ∈ J,
    (¬ ∀ w ∈ J, v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * z = z * v →
      v ∈ Subgroup.normalizer (K : Set G)

theorem HypOmega.toModU (h : HypOmega Ω) : HypOmegaModU (.sl2 3 1) Ω where
  conjInvariant := h.conjInvariant
  classical := h.classical
  omega4 K hK J hJ hKJ := by
    refine ⟨(h.omega4 K hK J hJ hKJ).1, fun he => ?_⟩
    have hc := (h.omega4 K hK J hJ hKJ).2 he
    refine le_trans (Subgroup.commutator_le.mpr fun g hg x hx => ?_) bot_le
    have : g * x = x * g := hc g hg x hx
    simp [commutatorElement_def, this]
  omega5 := h.omega5

theorem HypOmega.toMod (h : HypOmega Ω) : Q3T7M.HM Ω := h.toModU

theorem HypOmega.toGen [Finite G] (h : HypOmega Ω) : HypOmegaGen Ω :=
  hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) h.toModU

theorem HypOmega.commutes_of_twin [Finite G] (hΩ : HypOmega Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G} (hzK : IsUniqueInvolution K z)
    (hzJ : IsUniqueInvolution J z) : Commutes K J := by
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzK.sq) hzK.ne_one
  have hdvd : 2 ∣ Nat.card ↥(K ⊓ J) := by
    have := Subgroup.orderOf_dvd_natCard (K ⊓ J) (x := z) ⟨hzK.mem, hzJ.mem⟩
    rwa [hz2] at this
  have hN : Nat.card ↥(K ⊓ J) ≠ 0 := Nat.card_pos.ne'
  have h1 := one_le_padicValNat_of_dvd hN hdvd
  obtain ⟨h2, h3⟩ := hΩ.omega4 K hK J hJ hKJ
  exact h3 (le_antisymm h2 h1)

theorem HypOmega.nonempty_equiv_sl2 (hΩ : HypOmega Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    Nonempty (↥K ≃* SL(2, GaloisField 3 1)) := by
  obtain ⟨z, hz⟩ := hΩ.classical K hK
  exact IsClassicalMemberU.nonempty_equiv_sl2 hz |>.map fun e =>
    ((QuotientGroup.quotientMulEquivOfEq (hΩ.exact K hK)).trans
      QuotientGroup.quotientBot).symm.trans e

theorem HypOmega.center_eq (hΩ : HypOmega Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) :
    (∀ w ∈ K, z * w = w * z) ∧
      ∀ w ∈ K, (∀ y ∈ K, w * y = y * w) → w = 1 ∨ w = z := by
  obtain ⟨e⟩ := hΩ.nonempty_equiv_sl2 hK
  have hodd := odd_natCard_galoisField_of_pos (p := 3) (f := 1) (by norm_num) (by norm_num)
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have hzK : orderOf (⟨z, hz.mem⟩ : K) = 2 := by rw [Subgroup.orderOf_mk]; exact hz2
  have hez : e ⟨z, hz.mem⟩ = -1 := by
    have := (orderOf_eq_two_iff_of_equiv_sl2 hodd e ⟨z, hz.mem⟩).mp hzK
    rw [this]
    simp
  constructor
  · intro w hw
    have hc : e ⟨z, hz.mem⟩ ∈ Subgroup.center SL(2, GaloisField 3 1) := by
      rw [hez]
      exact (mem_center_sl2_iff _).mpr (Or.inr rfl)
    have hc' : (⟨z, hz.mem⟩ : K) ∈ Subgroup.center K :=
      (mem_center_iff_of_equiv_sl2 e _).mpr hc
    have := Subgroup.mem_center_iff.mp hc' ⟨w, hw⟩
    exact congrArg Subtype.val this.symm
  · intro w hw hcentral
    have hc : (⟨w, hw⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcentral g g.2).symm
    have hc' := (mem_center_iff_of_equiv_sl2 e _).mp hc
    rcases (mem_center_sl2_iff _).mp hc' with h1 | h1
    · left
      have : (⟨w, hw⟩ : K) = 1 := e.injective (by rw [h1, map_one])
      exact congrArg Subtype.val this
    · right
      have : (⟨w, hw⟩ : K) = ⟨z, hz.mem⟩ := e.injective (by rw [h1, hez])
      exact congrArg Subtype.val this

end ExactHyp

section ModelStmt


@[expose] def E189Model3 : Prop :=
  ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ), Generic.IsFundTag t →
    CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1 → E189ModelAt 3 1 t n

end ModelStmt

section Comm

@[expose] def commE {G : Type} [Group G] (δ x : G) : G := x * (δ * x * δ⁻¹)⁻¹

end Comm

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

namespace CFSG.ClassicalInvolution.Q3.Q3T7M

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Asc77

section Six3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem omegaNbr_subset_kPerp_of_twin (hΩ : HypOmegaGen Ω) {K L : Subgroup G} (hL : L ∈ Ω)
    {z : G} (hzK : IsUniqueInvolution K z) (hzL : IsUniqueInvolution L z) :
    omegaNbr Ω K ⊆ KPerp Ω L := by
  rintro J ⟨hJ, hJK, R, hR, hRJ, hRN⟩
  by_cases hJL : J = L
  · exact Set.mem_insert_iff.mpr (Or.inl hJL)
  · refine Set.mem_insert_iff.mpr (Or.inr ⟨hJ, hJL, R, hR, hRJ, ?_⟩)
    obtain ⟨J', -, hRJ'⟩ := exists_isSylow2In_of_mem_RSet hR
    exact Sec6Gen.le_normalizer_of_le_centralizer hΩ hL hJ (Ne.symm hJL) hzL hRJ hRJ'.2.1
      (by have := Sec6Gen.eight_le_of_mem_RSet hΩ hR; omega)
      (le_centralizer_of_le_normalizer hzK hRN)

theorem mem_kPerp_of_twin (hΩ : HypOmegaGen Ω) {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ Ω)
    {z : G} (hzK : IsUniqueInvolution K z) (hzL : IsUniqueInvolution L z) : K ∈ KPerp Ω L := by
  by_cases hKL : K = L
  · exact Set.mem_insert_iff.mpr (Or.inl hKL)
  · refine Set.mem_insert_iff.mpr (Or.inr ⟨hK, hKL, ?_⟩)
    obtain ⟨R, hR, hRK, -⟩ := exists_mem_RSet_ge hK (isPGroup_two_bot (G := G)) bot_le
    exact ⟨R, hR, hRK.1, fun x hx =>
      Sec6Gen.le_normalizer_of_twin hΩ hK hL hKL hzK hzL (hRK.1 hx)⟩

theorem omegaStarDiff_subset_of_twin (hΩ : HypOmegaGen Ω) {K L : Subgroup G} (hK : K ∈ Ω)
    (hL : L ∈ Ω) {z : G} (hzK : IsUniqueInvolution K z) (hzL : IsUniqueInvolution L z) :
    omegaStarNbr Ω K \ omegaNbr Ω K ⊆ omegaStarNbr Ω L \ omegaNbr Ω L := by
  rintro J ⟨⟨hJ, hJK, U, hU, hUJ, hUN⟩, hJnot⟩
  have hJL : J ≠ L := by
    rintro rfl
    by_cases hJK' : J = K
    · exact hJK hJK'
    · apply hJnot
      have := mem_kPerp_of_twin hΩ hL hK hzL hzK
      exact (Set.mem_insert_iff.mp this).resolve_left hJK'
  refine ⟨⟨hJ, hJL, U, hU, hUJ, ?_⟩, fun h => ?_⟩
  · have h4 := Sec6Gen.exists_data_of_mem_USet hΩ hU
    obtain ⟨R, -, J', -, hRJ', hUR, -, -, h4⟩ := h4
    exact Sec6Gen.le_normalizer_of_le_centralizer hΩ hL hJ (Ne.symm hJL) hzL hUJ
      (hRJ'.2.1.to_le hUR) (by omega) (le_centralizer_of_le_normalizer hzK hUN)
  · have := omegaNbr_subset_kPerp_of_twin hΩ hK hzL hzK h
    exact hJnot ((Set.mem_insert_iff.mp this).resolve_left hJK)

theorem l6_3 (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (hΩ : HypOmegaGen Ω)
    (K : Subgroup G) (hK : K ∈ Ω) (L : Subgroup G) (hL : L ∈ twinSet Ω K) :
    KPerp Ω K = KPerp Ω L ∧
      omegaStarNbr Ω K \ omegaNbr Ω K = omegaStarNbr Ω L \ omegaNbr Ω L := by
  obtain ⟨hLΩ, z, hzK, hzL⟩ := hL
  have hKL := omegaNbr_subset_kPerp_of_twin hΩ hLΩ hzK hzL
  have hLK := omegaNbr_subset_kPerp_of_twin hΩ hK hzL hzK
  have hK' := mem_kPerp_of_twin hΩ hK hLΩ hzK hzL
  have hL' := mem_kPerp_of_twin hΩ hLΩ hK hzL hzK
  refine ⟨Set.Subset.antisymm ?_ ?_, Set.Subset.antisymm ?_ ?_⟩
  · exact Set.insert_subset hK' hKL
  · exact Set.insert_subset hL' hLK
  · exact omegaStarDiff_subset_of_twin hΩ hK hLΩ hzK hzL
  · exact omegaStarDiff_subset_of_twin hΩ hLΩ hK hzL hzK

end Six3

section OddGen

variable {G : Type} [Group G]

theorem le_of_sq_mem_of_oddGen {K L : Subgroup G}
    (hK : Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} = K) (h : ∀ x ∈ K, x * x ∈ L) :
    K ≤ L := by
  rw [← hK]
  refine (Subgroup.closure_le L).mpr fun x hx => ?_
  obtain ⟨k, hk⟩ := hx.2
  have hpow : x ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
  have hx2 : x = x ^ (k + 1) * x ^ (k + 1) := by
    rw [← pow_add]
    calc x = x ^ (2 * k + 1) * x := by rw [hpow, one_mul]
      _ = x ^ (k + 1 + (k + 1)) := by rw [← pow_succ]; congr 1; ring
  rw [hx2]
  exact h _ (K.pow_mem hx.1 _)

theorem odd_mem_of_mem_sup_central {N K : Subgroup G} [N.Normal] (hNc : N ≤ Subgroup.center G)
    (hN2 : IsPGroup 2 ↥N) (hKN : K ⊓ N = ⊥) {x : G} (hx : x ∈ K ⊔ N)
    (ho : Odd (orderOf x)) : x ∈ K := by
  obtain ⟨k, hk, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  have hcomm : Commute k n := Subgroup.mem_center_iff.mp (hNc hn) k
  have hm : (k * n) ^ orderOf (k * n) = 1 := pow_orderOf_eq_one _
  rw [hcomm.mul_pow] at hm
  have hnm : n ^ orderOf (k * n) ∈ K ⊓ N := by
    refine ⟨?_, N.pow_mem hn _⟩
    have : n ^ orderOf (k * n) = (k ^ orderOf (k * n))⁻¹ := eq_inv_of_mul_eq_one_right hm
    rw [this]
    exact K.inv_mem (K.pow_mem hk _)
  rw [hKN, Subgroup.mem_bot] at hnm
  have hdvd : orderOf n ∣ orderOf (k * n) := orderOf_dvd_of_pow_eq_one hnm
  obtain ⟨j, hj⟩ := hN2.exists_orderOf_eq_pow ⟨n, hn⟩
  have hj' : orderOf n = 2 ^ j := by rwa [Subgroup.orderOf_mk] at hj
  have hodd : Odd (orderOf n) := ho.of_dvd_nat hdvd
  rw [hj'] at hodd
  have hj0 : j = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  rw [hj0, pow_zero] at hj'
  rw [orderOf_eq_one_iff.mp hj', mul_one]
  exact hk

theorem oddGen_conjSub {K : Subgroup G}
    (hK : Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} = K) (u : G) :
    Subgroup.closure {x : G | x ∈ conjSub u K ∧ Odd (orderOf x)} = conjSub u K := by
  refine le_antisymm ((Subgroup.closure_le _).mpr fun x hx => hx.1) ?_
  intro y hy
  rw [mem_conjSub_iff] at hy
  have hy' : u⁻¹ * y * u ∈ Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} := by rwa [hK]
  have hconj : ∀ w ∈ Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)},
      u * w * u⁻¹ ∈ Subgroup.closure {x : G | x ∈ conjSub u K ∧ Odd (orderOf x)} := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      refine Subgroup.subset_closure ⟨conj_mem_conjSub hx.1, ?_⟩
      have : orderOf (u * x * u⁻¹) = orderOf x := by
        simpa using (MulAut.conj u).orderOf_eq x
      rw [this]
      exact hx.2
    | one => simp
    | mul a b _ _ ha hb =>
      have : u * (a * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have : u * a⁻¹ * u⁻¹ = (u * a * u⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ ha
  have := hconj _ hy'
  simpa [mul_assoc] using this

end OddGen

section Sl2Three

open scoped MatrixGroups

private theorem exists_order_four_sl2Three :
    ∃ s : SL(2, ZMod 3), s ^ 4 = 1 ∧ ¬ s ^ 2 = 1 := by decide +kernel

theorem normal_cases3 {P : Type} [Group P] (e : P ≃* SL(2, GaloisField 3 1)) (E : Subgroup P)
    [hE : E.Normal] : E = ⊥ ∨ E = Subgroup.center P ∨ ∃ u ∈ E, orderOf u = 4 := by
  obtain ⟨e₃⟩ := nonempty_mulEquiv_sl2Three_of_natCard_eq_three
    (F := GaloisField 3 1) (by simpa using GaloisField.card 3 1 one_ne_zero)
  set f : P ≃* SL(2, ZMod 3) := e.trans e₃ with hf
  obtain ⟨s, hs4, hs2⟩ := exists_order_four_sl2Three
  have hord : orderOf s = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := s) (by simpa using hs2)
      (by simpa using hs4)
    simpa using this
  have hsc : s ∈ commutator SL(2, ZMod 3) :=
    CFSG.ClassicalInvolution.Q3.Q3T6.sl2Three_mem_commutator_iff.mpr hs4
  have hsmap : s ∈ (commutator P).map f.toMonoidHom := by
    rw [CFSG.ClassicalInvolution.Q3.Q3T6.map_commutator_of_surjective f.toMonoidHom f.surjective]
    exact hsc
  obtain ⟨x, hx, hfx⟩ := Subgroup.mem_map.mp hsmap
  have hxo : orderOf x = 4 := by
    rw [← hord, ← hfx]
    exact (f.orderOf_eq x).symm
  rcases CFSG.ClassicalInvolution.Q3.Q3T6.normal_cases_of_equiv_sl2Three f E hE with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨x, h ▸ hx, hxo⟩)
  · exact Or.inr (Or.inr ⟨x, h ▸ Subgroup.mem_top x, hxo⟩)

end Sl2Three

end CFSG.ClassicalInvolution.Q3.Q3T7M

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Generic

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Uniform
open CFSG.Open
open scoped MatrixGroups

variable {Y : Type} [Group Y]

theorem IsClassicalMember.conj {L : Subgroup Y} {z : Y} (h : IsClassicalMember L z) (g : Y) :
    IsClassicalMember (conjSub g L) (g * z * g⁻¹) :=
  IsClassicalMemberU.conj h g

theorem IsClassicalMember.subgroupOf {L : Subgroup Y} {z : Y} (h : IsClassicalMember L z)
    {H : Subgroup Y} (hLH : L ≤ H) :
    IsClassicalMember (L.subgroupOf H) (⟨z, hLH h.mem⟩ : H) :=
  IsClassicalMemberU.subgroupOf h hLH

theorem IsClassicalMember.nonempty_equiv_sl2 {L : Subgroup Y} {z : Y} (h : IsClassicalMember L z)
    (hL : classicalInvolutionOddCore L = ⊥) : Nonempty (L ≃* SL(2, GaloisField 3 1)) := by
  obtain ⟨e⟩ := IsClassicalMemberU.nonempty_equiv_sl2 h
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hL).trans QuotientGroup.quotientBot).symm.trans e⟩

end CFSG.ClassicalInvolution.Q3.Q3T8.Generic
