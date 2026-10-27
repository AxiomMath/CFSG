module

public import CFSG.ClassicalInvolution.SmallCases.Exclusion
public import CFSG.Foundations.Basic
public import CFSG.Open.AschbacherProperTwoGeneratedCoreMilestoneDefs
public import CFSG.Open.WalterAbelianSylowTwoMilestoneDefs
public import CFSG.Walter.J1.Defs
import CFSG.GH74.Uniqueness.Gamma
import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingSolvable
import CFSG.Walter.J1Props.Hyp

public section

namespace CFSG.ClassicalInvolution

@[expose] def AschbacherProperTwoGeneratedCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ S : Sylow 2 G, 3 ≤ CFSG.Open.pRank 2 (S : Subgroup G) →
      CFSG.Open.properTwoGenCoreGamma (S : Subgroup G) 2 ≠ ⊤ →
        CFSG.Open.properTwoGenCoreGamma (S : Subgroup G) 1 ≠ ⊤ ∨
          Nonempty (G ≃* CFSG.Open.properTwoGenCoreJ1)

@[expose] def HasNonsolvableClassical (G : Type*) [Group G] : Prop :=
  ∃ (z : G) (J : Subgroup G), orderOf z = 2 ∧ z ∈ J ∧
    CFSG.Open.IsSubnormal J (Subgroup.centralizer ({z} : Set G)) ∧
    CFSG.Open.classicalInvolutionWitness J ∧ ¬ Group.IsSolvable J

theorem hasNonsolvableClassical_iff (G : Type*) [Group G] :
    HasNonsolvableClassical G ↔ ¬ NoNonsolvableClassical G := by
  constructor
  · rintro ⟨z, J, hz, hzJ, hJ, hw, hns⟩ h
    exact h z hz J hzJ hJ hw hns
  · intro h
    by_contra h'
    apply h
    intro z hz J hzJ hJ hw hns
    exact h' ⟨z, J, hz, hzJ, hJ, hw, hns⟩

theorem HasNonsolvableClassical.nonabelian {G : Type*} [Group G] (h : HasNonsolvableClassical G) :
    ∃ a b : G, a * b ≠ b * a := by
  obtain ⟨z, J, -, -, -, -, hns⟩ := h
  by_contra hcomm
  push Not at hcomm
  have : Group.IsSolvable G := Group.isSolvable_of_comm hcomm
  exact hns (Group.isSolvable_of_isSolvable_injective J.subtype_injective)

theorem centralizer_le_of_isStronglyEmbedded {G : Type*} [Group G] [Finite G] {M : Subgroup G}
    (hM : CFSG.IsStronglyEmbedded M) {x : G} (hxM : x ∈ M) (hx : orderOf x = 2) :
    Subgroup.centralizer ({x} : Set G) ≤ M := by
  intro c hc
  by_contra hcM
  have hodd := hM.2.2 c hcM
  have hxc : x ∈ CFSG.conjugate M c := by
    refine ⟨x, hxM, ?_⟩
    have hcomm : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc c⁻¹ * x * c = c⁻¹ * (c * x) := by rw [hcomm]; group
      _ = x := by group
  have hle : Subgroup.zpowers x ≤ M ⊓ CFSG.conjugate M c := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.mpr ⟨hxM, hxc⟩
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [Nat.card_zpowers, hx] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem exists_conj_mem_sylow {G : Type*} [Group G] [Finite G] {z : G} (hz : orderOf z = 2)
    (S : Sylow 2 G) : ∃ g : G, g⁻¹ * z * g ∈ (S : Subgroup G) := by
  have hz2 : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  obtain ⟨P, hP⟩ := hz2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
  refine ⟨g, ?_⟩
  have hzP : z ∈ (P : Subgroup G) := hP (Subgroup.mem_zpowers z)
  rw [← hg] at hzP
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hzP
  simpa [MulAut.conj_apply, mul_assoc] using hzP

theorem false_of_gamma_one_ne_top {G : Type} [Group G] [Finite G] (S : Sylow 2 G)
    (h3 : 3 ≤ CFSG.Open.pRank 2 (S : Subgroup G))
    (h1 : CFSG.Open.properTwoGenCoreGamma (S : Subgroup G) 1 ≠ ⊤)
    {z : G} {K : Subgroup G} (hz : orderOf z = 2)
    (hKz : K ≤ Subgroup.centralizer ({z} : Set G)) (hns : ¬ Group.IsSolvable K) : False := by
  set M := CFSG.Open.properTwoGenCoreGamma (S : Subgroup G) 1 with hMdef
  have hSM : (S : Subgroup G) ≤ M := CFSG.ProperTwoGeneratedCore.sylow_le_gamma S (by omega)
  have hM : CFSG.IsStronglyEmbedded M :=
    CFSG.GH74.Uniqueness.isStronglyEmbedded_gamma_one S (by omega) h1
  have hrank : 2 ≤ CFSG.Open.twoRank G :=
    le_trans (by omega) (CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 2 (by norm_num)
      (le_top : (S : Subgroup G) ≤ ⊤))
  have hsolv : Group.IsSolvable M :=
    CFSG.ComponentClassification.AschbacherStrongEmbedding.strongly_embedded_solvable G M hM hrank
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow hz S
  have hz' : orderOf (g⁻¹ * z * g) = 2 := by
    have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective z
    simpa [MulAut.conj_apply, hz] using this
  have hC := centralizer_le_of_isStronglyEmbedded hM (hSM hg) hz'
  have hKM : K.map (MulAut.conj g⁻¹).toMonoidHom ≤ M := by
    rintro _ ⟨k, hk, rfl⟩
    apply hC
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hk' := Subgroup.mem_centralizer_singleton_iff.mp (hKz hk)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * k * g * (g⁻¹ * z * g) = g⁻¹ * (k * z) * g := by group
      _ = g⁻¹ * (z * k) * g := by rw [hk']
      _ = g⁻¹ * z * g * (g⁻¹ * k * g) := by group
  have hKs : Group.IsSolvable ↥(K.map (MulAut.conj g⁻¹).toMonoidHom) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKM)
  exact hns (Group.isSolvable_of_isSolvable_injective
    (f := (K.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective).toMonoidHom)
    (K.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).injective)

theorem index_F_eq_two {G : Type} [Group G] [Finite G] (h : CFSG.Walter.J1.JankoHyp G) :
    (h.F.subgroupOf (Subgroup.centralizer ({h.t} : Set G))).index = 2 := by
  have hcard := Subgroup.card_mul_index (h.F.subgroupOf (Subgroup.centralizer ({h.t} : Set G)))
  have h1 : Nat.card (h.F.subgroupOf (Subgroup.centralizer ({h.t} : Set G))) = 60 := by
    rw [← h.card_F]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le_centralizer).toEquiv
  rw [h1, h.card_centralizer] at hcard
  omega

theorem noNonsolvableClassical_of_jankoHyp {G : Type} [Group G] [Finite G]
    (h : CFSG.Walter.J1.JankoHyp G) : NoNonsolvableClassical G := by
  refine NoNonsolvableClassical.of_conj_reps {h.t} (fun z hz => ?_) ?_
  · obtain ⟨g, hg⟩ := h.exists_conj_eq_t hz
    exact ⟨h.t, rfl, (isConj_iff.mpr ⟨g, hg⟩).symm⟩
  · intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact NoNonsolvableClassicalAt.of_index_two h.F
      (Subgroup.normal_of_index_eq_two (index_F_eq_two h)) (index_F_eq_two h) h.t_not_mem

theorem properTwoGenCoreJ1_eq_walterJ1 :
    CFSG.Open.properTwoGenCoreJ1 = CFSG.Open.walterJ1 := by
  unfold CFSG.Open.walterJ1 CFSG.Open.properTwoGenCoreJ1
  congr 1

theorem noNonsolvableClassical_properTwoGenCoreJ1 :
    NoNonsolvableClassical ↥CFSG.Open.properTwoGenCoreJ1 := by
  have h := noNonsolvableClassical_of_jankoHyp CFSG.Walter.J1Props.jankoHyp
  rw [← properTwoGenCoreJ1_eq_walterJ1] at h
  exact h

theorem gamma_two_eq_top (hA : AschbacherProperTwoGeneratedCore) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hcl : HasNonsolvableClassical G) (S : Sylow 2 G)
    (h3 : 3 ≤ CFSG.Open.pRank 2 (S : Subgroup G)) :
    CFSG.Open.properTwoGenCoreGamma (S : Subgroup G) 2 = ⊤ := by
  by_contra hne
  rcases hA G hcl.nonabelian S h3 hne with h1 | ⟨⟨e⟩⟩
  · obtain ⟨z, J, hz, -, hJ, -, hns⟩ := hcl
    exact false_of_gamma_one_ne_top S h3 h1 hz (CFSG.ClassicalInvolution.isSubnormal_le hJ) hns
  · exact (hasNonsolvableClassical_iff G).mp hcl
      (NoNonsolvableClassical.of_mulEquiv e noNonsolvableClassical_properTwoGenCoreJ1)

end CFSG.ClassicalInvolution
