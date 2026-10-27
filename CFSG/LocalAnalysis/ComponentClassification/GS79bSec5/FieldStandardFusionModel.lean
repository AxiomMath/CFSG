module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.ModelFacts
public import CFSG.RankThree.OddKernel.OddLift
public import CFSG.GroupTheory.PerfectCoverProduct
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNoncentralPairActionCentralQuotient

public section

namespace CFSG.ComponentClassification.GS79bSec5

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.LinearThree
open CFSG.ProperTwoGeneratedCore.LocalCriterionNoncentralPairAction

universe u

private abbrev fusionN {G : Type u} [Group G] (A : Subgroup G) : Subgroup G :=
  normalizer (A : Set G)

private abbrev fusionA {G : Type u} [Group G] (A : Subgroup G) : Subgroup (fusionN A) :=
  A.subgroupOf (fusionN A)

private abbrev fusionC {G : Type u} [Group G] (A : Subgroup G) : Subgroup (fusionN A) :=
  centralizer (fusionA A : Set (fusionN A))

private abbrev fusionZ {G : Type u} [Group G] (A : Subgroup G) : Subgroup (fusionN A) :=
  fusionA A ⊓ fusionC A

private theorem fusionA_normal {G : Type u} [Group G] (A : Subgroup G) :
    (fusionA A).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (show A ≤ fusionN A from le_normalizer)).mpr
    le_rfl

attribute [local instance] fusionA_normal

private theorem fusionC_normal {G : Type u} [Group G] (A : Subgroup G) :
    (fusionC A).Normal :=
  Subgroup.normal_centralizer

attribute [local instance] fusionC_normal

private theorem fusionZ_normal {G : Type u} [Group G] (A : Subgroup G) :
    (fusionZ A).Normal :=
  Subgroup.normal_inf_normal (fusionA A) (fusionC A)

private theorem center_map_inclusion_eq_fusionZ {G : Type u} [Group G] (A : Subgroup G) :
    (Subgroup.center A).map
        (Subgroup.inclusion (show A ≤ fusionN A from le_normalizer)) = fusionZ A := by
  classical
  let φ : A →* fusionN A := Subgroup.inclusion (show A ≤ fusionN A from le_normalizer)
  have htop : (⊤ : Subgroup A).map φ = fusionA A := by
    ext x
    constructor
    · rintro ⟨a, -, rfl⟩
      exact a.2
    · intro hx
      exact ⟨⟨x.1, hx⟩, trivial, rfl⟩
  have hcenterEq : (⊤ ⊓ centralizer ((⊤ : Subgroup A) : Set A)) = Subgroup.center A := by
    ext x
    constructor
    · rintro ⟨-, hx⟩
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subgroup.mem_centralizer_iff.mp hx y trivial
    · intro hx
      exact ⟨trivial, Subgroup.mem_centralizer_iff.mpr fun y _ =>
        Subgroup.mem_center_iff.mp hx y⟩
  have h := map_inf_centralizer (G := fusionN A) (φ := φ)
    (Subgroup.inclusion_injective (show A ≤ fusionN A from le_normalizer)) (⊤ : Subgroup A)
  rw [hcenterEq, htop] at h
  exact h

private theorem fusionZ_centralizes {G : Type u} [Group G] (A : Subgroup G) :
    ∀ z ∈ fusionZ A, ∀ y ∈ fusionA A, y * z = z * y :=
  fun _ hz _ hy => Subgroup.mem_centralizer_iff.mp hz.2 _ hy

private theorem fusionZ_odd {G : Type u} [Group G] (A : Subgroup G)
    (hZ : Odd (Nat.card (Subgroup.center A))) : Odd (Nat.card (fusionZ A)) := by
  rw [← center_map_inclusion_eq_fusionZ,
    Subgroup.card_map_of_injective
      (Subgroup.inclusion_injective (show A ≤ fusionN A from le_normalizer))]
  exact hZ

private abbrev fusionH {G : Type u} [Group G] (A : Subgroup G)
    [_hZ : (fusionZ A).Normal] : Type u :=
  fusionN A ⧸ fusionZ A

private abbrev fusionP {G : Type u} [Group G] (A : Subgroup G)
    [hZ : (fusionZ A).Normal] : fusionN A →* fusionH A :=
  QuotientGroup.mk' (fusionZ A)

private abbrev fusionAbar {G : Type u} [Group G] (A : Subgroup G)
    [hZ : (fusionZ A).Normal] : Subgroup (fusionH A) :=
  (fusionA A).map (fusionP A)

private abbrev fusionPhi {G : Type u} [Group G] (A : Subgroup G) : A →* fusionN A :=
  Subgroup.inclusion (show A ≤ fusionN A from le_normalizer)

private abbrev fusionR {G : Type u} [Group G] (A : Subgroup G)
    [hZ : (fusionZ A).Normal] : A →* fusionH A :=
  (fusionP A).comp (Subgroup.inclusion (show A ≤ fusionN A from le_normalizer))

private theorem fusionR_range {G : Type u} [Group G] (A : Subgroup G)
    [hZ : (fusionZ A).Normal] : (fusionR A).range = fusionAbar A := by
  have hφ : (Subgroup.inclusion (show A ≤ fusionN A from le_normalizer)).range = fusionA A := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact a.2
    · intro hx
      exact ⟨⟨x.1, hx⟩, rfl⟩
  rw [fusionR, MonoidHom.range_comp, hφ]

private theorem fusionR_ker {G : Type u} [Group G] (A : Subgroup G)
    [hZ : (fusionZ A).Normal] : (fusionR A).ker = Subgroup.center A := by
  ext a
  constructor
  · intro ha
    have hp : fusionP A (Subgroup.inclusion (show A ≤ fusionN A from le_normalizer) a) = 1 := ha
    have hmem : Subgroup.inclusion (show A ≤ fusionN A from le_normalizer) a ∈ fusionZ A :=
      (QuotientGroup.eq_one_iff _).1 hp
    rw [← center_map_inclusion_eq_fusionZ A] at hmem
    obtain ⟨c, hc, hca⟩ := hmem
    have hca' : c = a :=
      Subgroup.inclusion_injective (show A ≤ fusionN A from le_normalizer) hca
    simpa [hca'] using hc
  · intro ha
    have hmem : Subgroup.inclusion (show A ≤ fusionN A from le_normalizer) a ∈ fusionZ A := by
      rw [← center_map_inclusion_eq_fusionZ A]
      exact ⟨a, ha, rfl⟩
    exact (QuotientGroup.eq_one_iff _).2 hmem

private noncomputable def fusionEbar {G : Type u} [Group G] {F : Type} [Field F]
    (A : Subgroup G) [hZ : (fusionZ A).Normal]
    (e : (A ⧸ Subgroup.center A) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F) :
    fusionAbar A ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F :=
  let rbar : A →* fusionAbar A :=
    (fusionR A).codRestrict (fusionAbar A) fun a => by
      rw [← fusionR_range A]
      exact ⟨a, rfl⟩
  let hsurj : Function.Surjective rbar := by
    intro x
    have hx : (x : fusionH A) ∈ (fusionR A).range := by
      rw [fusionR_range A]
      exact x.2
    obtain ⟨a, ha⟩ := (MonoidHom.mem_range).1 hx
    exact ⟨a, Subtype.ext ha⟩
  have hker : rbar.ker = Subgroup.center A := by
    have h1 : rbar.ker = (fusionR A).ker := by
      ext a
      exact Subtype.ext_iff
    rw [h1, fusionR_ker A]
  let qe : (A ⧸ Subgroup.center A) ≃* fusionAbar A :=
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective rbar hsurj)
  qe.symm.trans e

private theorem fusionAbar_normal {G : Type u} [Group G] (A : Subgroup G)
    [hZ : (fusionZ A).Normal] : (fusionAbar A).Normal :=
  Subgroup.Normal.map (fusionA_normal A) (fusionP A) (QuotientGroup.mk'_surjective (fusionZ A))

section LocalInstances
variable {G : Type u} [Group G] {A : Subgroup G}
attribute [local instance] fusionZ_normal
attribute [local instance] fusionAbar_normal
attribute [local instance] Fintype.ofFinite

private theorem comap_centralizer_fusionAbar {G : Type u} [Group G] [Finite G]
    {A : Subgroup G} [Group.IsPerfect A] [hZ : (fusionZ A).Normal] :
    (Subgroup.centralizer (fusionAbar A : Set (fusionH A))).comap (fusionP A) = fusionC A := by
  classical
  have hφσ : ∀ (n : fusionN A) (a : A),
      fusionPhi A ((Subgroup.normalizerMonoidHom A n) a) =
        n * fusionPhi A a * n⁻¹ := by
    intro n a
    apply Subtype.ext
    change (↑((A.normalizerMonoidHom n) a) : G) = (↑n : G) * ↑a * (↑n : G)⁻¹
    exact Subgroup.normalizerMonoidHom_apply_apply_coe A n a
  ext n
  constructor
  · intro hn
    have hpn : fusionP A n ∈
        Subgroup.centralizer (fusionAbar A : Set (fusionH A)) := hn
    have hσ : ∀ a : A,
        QuotientGroup.mk' (Subgroup.center A)
            ((Subgroup.normalizerMonoidHom A n) a) =
          QuotientGroup.mk' (Subgroup.center A) a := by
      intro a
      have hmemAbar : fusionP A (fusionPhi A a) ∈ fusionAbar A :=
        Subgroup.mem_map_of_mem (fusionP A) a.2
      have hcomm : fusionP A (fusionPhi A a) * fusionP A n =
          fusionP A n * fusionP A (fusionPhi A a) :=
        Subgroup.mem_centralizer_iff.mp hpn _ hmemAbar
      have hconj : fusionP A (fusionPhi A
            ((Subgroup.normalizerMonoidHom A n) a)) =
          fusionP A (fusionPhi A a) := by
        rw [hφσ n a, map_mul, map_mul, map_inv]
        calc fusionP A n * fusionP A (fusionPhi A a) * (fusionP A n)⁻¹ =
            fusionP A (fusionPhi A a) * fusionP A n * (fusionP A n)⁻¹ := by rw [← hcomm]
          _ = fusionP A (fusionPhi A a) := by group
      have hmem : (fusionPhi A ((Subgroup.normalizerMonoidHom A n) a))⁻¹ *
            fusionPhi A a ∈ fusionZ A :=
        QuotientGroup.eq.1 hconj
      rw [← center_map_inclusion_eq_fusionZ A] at hmem
      obtain ⟨c, hc, hca⟩ := hmem
      have hca' : c = ((Subgroup.normalizerMonoidHom A n) a)⁻¹ * a :=
        Subgroup.inclusion_injective (show A ≤ fusionN A from le_normalizer) hca
      exact (QuotientGroup.eq).2 (by rw [← hca']; exact hc)
    have hσid := central_quotient_trivial_hom_eq_id (Subgroup.center A)
      (le_rfl : Subgroup.center A ≤ Subgroup.center A)
      (Subgroup.normalizerMonoidHom A n).toMonoidHom hσ
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    let a : A := ⟨y.1, by
      simpa [fusionA, Subgroup.mem_subgroupOf] using hy⟩
    have hy' : fusionPhi A a = y := Subtype.ext rfl
    have hb : (Subgroup.normalizerMonoidHom A n) a = a :=
      congrArg (fun f : A →* A => f a) hσid
    have hfix : fusionPhi A ((Subgroup.normalizerMonoidHom A n) a) = fusionPhi A a :=
      congrArg (fusionPhi A) hb
    have hfix' : n * fusionPhi A a * n⁻¹ = fusionPhi A a := by
      rw [← hφσ n a]
      exact hfix
    have hny : n * fusionPhi A a = fusionPhi A a * n := by
      calc n * fusionPhi A a = (n * fusionPhi A a * n⁻¹) * n := by group
        _ = fusionPhi A a * n := by rw [hfix']
    rw [← hy']
    exact hny.symm
  · intro hn
    change fusionP A n ∈ Subgroup.centralizer (fusionAbar A : Set (fusionH A))
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    have hcomm : a * n = n * a := Subgroup.mem_centralizer_iff.mp hn a ha
    rw [← map_mul, ← map_mul, hcomm]

private theorem fusionC_eq_subgroupOf {G : Type u} [Group G] (A : Subgroup G) :
    fusionC A = (Subgroup.centralizer (A : Set G)).subgroupOf (fusionN A) := by
  ext n
  constructor
  · intro hn
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro a ha
    have hmem : fusionPhi A ⟨a, ha⟩ ∈ fusionA A := by
      simpa [fusionA, Subgroup.mem_subgroupOf] using ha
    have h := Subgroup.mem_centralizer_iff.mp hn (fusionPhi A ⟨a, ha⟩) hmem
    exact congrArg Subtype.val h
  · intro hn
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y.1 ∈ A := by
      simpa [fusionA, Subgroup.mem_subgroupOf] using hy
    have hmem : n.1 ∈ Subgroup.centralizer (A : Set G) := by
      simpa [Subgroup.mem_subgroupOf] using hn
    have h := Subgroup.mem_centralizer_iff.mp hmem y.1 hy'
    exact Subtype.ext h

private theorem map_fusionA {G : Type u} [Group G] (A : Subgroup G) :
    (fusionA A).map (fusionN A).subtype = A := by
  rw [show fusionA A = A.subgroupOf (fusionN A) from rfl, Subgroup.subgroupOf_map_subtype]
  exact inf_eq_left.mpr (show A ≤ fusionN A from le_normalizer)

private theorem map_fusionC {G : Type u} [Group G] (A : Subgroup G) :
    (fusionC A).map (fusionN A).subtype = Subgroup.centralizer (A : Set G) := by
  rw [fusionC_eq_subgroupOf, Subgroup.subgroupOf_map_subtype]
  exact inf_eq_left.mpr (Subgroup.centralizer_le_normalizer (A : Set G))

private theorem map_fusion_join {G : Type u} [Group G] (A : Subgroup G) :
    (fusionA A ⊔ fusionC A).map (fusionN A).subtype =
      A ⊔ Subgroup.centralizer (A : Set G) := by
  rw [Subgroup.map_sup, map_fusionA, map_fusionC]

private noncomputable def fusionCentEquiv {G : Type u} [Group G] (A : Subgroup G) :
    fusionC A ≃* Subgroup.centralizer (A : Set G) :=
  (MulEquiv.subgroupCongr (fusionC_eq_subgroupOf A)).trans
    (Subgroup.subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer (A : Set G)))

private theorem cyclic_sylow_fusionC {G : Type u} [Group G] [Finite G] (A : Subgroup G)
    (hcyc : ∀ S : Sylow 2 (Subgroup.centralizer (A : Set G)), IsCyclic ↥S) :
    ∀ S : Sylow 2 (fusionC A), IsCyclic ↥S :=
  CFSG.OddStandard.Seitz77.cyclic_sylow_of_surjective
    (fusionCentEquiv (A := A)).symm.toMonoidHom
    (fusionCentEquiv (A := A)).symm.surjective hcyc

private theorem map_centralizer_fusionAbar {G : Type u} [Group G] [Finite G]
    {A : Subgroup G} [Group.IsPerfect A] [hZ : (fusionZ A).Normal] :
    (fusionC A).map (fusionP A) =
      Subgroup.centralizer (fusionAbar A : Set (fusionH A)) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    have hcomm : a * c = c * a := Subgroup.mem_centralizer_iff.mp hc a ha
    rw [← map_mul, ← map_mul, hcomm]
  · intro x hx
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (fusionZ A) x
    have hn : n ∈ (Subgroup.centralizer (fusionAbar A : Set (fusionH A))).comap (fusionP A) :=
      hx
    rw [comap_centralizer_fusionAbar (A := A)] at hn
    exact ⟨n, hn, rfl⟩

private noncomputable def fusionPC {G : Type u} [Group G] [Finite G]
    {A : Subgroup G} [Group.IsPerfect A] [hZ : (fusionZ A).Normal] :
    fusionC A →* Subgroup.centralizer (fusionAbar A : Set (fusionH A)) :=
  ((fusionP A).comp (fusionC A).subtype).codRestrict _ fun c => by
    rw [← map_centralizer_fusionAbar (A := A)]
    exact ⟨c, c.2, rfl⟩

private theorem fusionPC_surjective {G : Type u} [Group G] [Finite G]
    {A : Subgroup G} [Group.IsPerfect A] [hZ : (fusionZ A).Normal] :
    Function.Surjective (fusionPC (A := A)) := by
  intro x
  have hx : (x : fusionH A) ∈ (fusionC A).map (fusionP A) := by
    rw [map_centralizer_fusionAbar (A := A)]
    exact x.2
  obtain ⟨c, hc, hpc⟩ := hx
  exact ⟨⟨c, hc⟩, Subtype.ext hpc⟩

private theorem cyclic_sylow_centralizer_fusionAbar {G : Type u} [Group G] [Finite G]
    {A : Subgroup G} [Group.IsPerfect A] [hZ : (fusionZ A).Normal]
    (hcyc : ∀ S : Sylow 2 (Subgroup.centralizer (A : Set G)), IsCyclic ↥S) :
    ∀ T : Sylow 2 (Subgroup.centralizer (fusionAbar A : Set (fusionH A))), IsCyclic ↥T :=
  CFSG.OddStandard.Seitz77.cyclic_sylow_of_surjective (fusionPC (A := A)) (fusionPC_surjective (A := A))
    (cyclic_sylow_fusionC (A := A) hcyc)

private theorem comap_fusionP_fusionAbar {G : Type u} [Group G] (A : Subgroup G)
    [hZ : (fusionZ A).Normal] :
    (fusionAbar A).comap (fusionP A) = fusionA A := by
  rw [← show (fusionA A).map (fusionP A) = fusionAbar A from rfl,
    Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  exact sup_eq_left.mpr inf_le_left

private theorem comap_fusionP_join {G : Type u} [Group G] [Finite G]
    {A : Subgroup G} [Group.IsPerfect A] [hZ : (fusionZ A).Normal] :
    (fusionAbar A ⊔ Subgroup.centralizer (fusionAbar A : Set (fusionH A))).comap
        (fusionP A) =
      fusionA A ⊔ fusionC A := by
  have hmap : (fusionA A ⊔ fusionC A).map (fusionP A) =
      fusionAbar A ⊔ Subgroup.centralizer (fusionAbar A : Set (fusionH A)) := by
    rw [Subgroup.map_sup, map_centralizer_fusionAbar (A := A)]
  rw [← hmap, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  exact sup_eq_left.mpr (le_trans inf_le_right le_sup_right)

private theorem fusionP_injective_on_two {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) [hZ : (fusionZ A).Normal]
    (hZodd : Odd (Nat.card (fusionZ A))) {P : Subgroup (fusionN A)} (hP : IsPGroup 2 P) :
    Function.Injective ((fusionP A).comp P.subtype) :=
  CFSG.RankThree.OddKernel.injective_restrict_of_odd (fusionP A) (by
    rw [QuotientGroup.ker_mk']
    exact hZodd) hP

private theorem invol_conj_of_mulEquiv
    {G : Type u} [Group G] [Finite G]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (A : Subgroup G) [Group.IsPerfect A]
    (hZ : Odd (Nat.card (Subgroup.center A)))
    (e : (A ⧸ Subgroup.center A) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F) :
    ∀ x ∈ A, ∀ y ∈ A, orderOf x = 2 → orderOf y = 2 →
      ∃ a ∈ A, a * x * a⁻¹ = y := by
  classical
  have hZodd : Odd (Nat.card (fusionZ A)) := fusionZ_odd A hZ
  let ebar := fusionEbar (A := A) e
  intro x hx y hy hx2 hy2
  let xa : A := ⟨x, hx⟩
  let ya : A := ⟨y, hy⟩
  have hx2A : orderOf xa = 2 := by
    rw [← Subgroup.orderOf_coe xa, hx2]
  have hy2A : orderOf ya = 2 := by
    rw [← Subgroup.orderOf_coe ya, hy2]
  have hx2N : orderOf (fusionPhi A xa) = 2 :=
    (orderOf_injective (fusionPhi A)
      (Subgroup.inclusion_injective (show A ≤ fusionN A from le_normalizer)) xa).trans hx2A
  have hy2N : orderOf (fusionPhi A ya) = 2 :=
    (orderOf_injective (fusionPhi A)
      (Subgroup.inclusion_injective (show A ≤ fusionN A from le_normalizer)) ya).trans hy2A
  have hxbar2 : orderOf (fusionP A (fusionPhi A xa)) = 2 :=
    CFSG.RankThree.OddKernel.orderOf_mk_eq_two (fusionZ A) hZodd hx2N
  have hybar2 : orderOf (fusionP A (fusionPhi A ya)) = 2 :=
    CFSG.RankThree.OddKernel.orderOf_mk_eq_two (fusionZ A) hZodd hy2N
  have hxAbar : fusionP A (fusionPhi A xa) ∈ fusionAbar A :=
    Subgroup.mem_map_of_mem (fusionP A) xa.2
  have hyAbar : fusionP A (fusionPhi A ya) ∈ fusionAbar A :=
    Subgroup.mem_map_of_mem (fusionP A) ya.2
  obtain ⟨bbar, hbbar, hconjbar⟩ :=
    CFSG.LocalAnalysis.EvenBN.LinearThree.exists_conj_of_mulEquiv ebar hxAbar hyAbar
      hxbar2 hybar2
  obtain ⟨b0, hb0, hb0eq⟩ := (Subgroup.mem_map).1 hbbar
  let r : fusionN A := b0 * fusionPhi A xa * b0⁻¹
  have hr2 : orderOf r = 2 := by
    have h := (MulEquiv.orderOf_eq (MulAut.conj b0) (fusionPhi A xa)).trans hx2N
    simpa [MulAut.conj_apply, r] using h
  have hquot : (r : fusionH A) = (fusionPhi A ya : fusionH A) := by
    change fusionP A r = fusionP A (fusionPhi A ya)
    rw [show fusionP A r = fusionP A b0 * fusionP A (fusionPhi A xa) * (fusionP A b0)⁻¹ by
      simp [r, map_mul, map_inv]]
    rw [hb0eq, hconjbar]
  obtain ⟨m, hm, hmconj⟩ :=
    CFSG.RankThree.OddKernel.isConj_of_mk_eq (fusionZ A) hZodd hr2 hy2N hquot
  let bN : fusionN A := m * b0
  have hbN : bN ∈ fusionA A := (fusionA A).mul_mem hm.1 hb0
  have hconjN : bN * fusionPhi A xa * bN⁻¹ = fusionPhi A ya := by
    have hb : bN * fusionPhi A xa * bN⁻¹ = m * r * m⁻¹ := by
      dsimp [bN, r]
      group
    rw [hb, hmconj]
  let a : A := ⟨bN.1, by
    simpa [fusionA, Subgroup.mem_subgroupOf] using hbN⟩
  have hφa : fusionPhi A a = bN := Subtype.ext rfl
  refine ⟨a, a.2, ?_⟩
  have hG := congrArg (fun z : fusionN A => (z : G)) hconjN
  simpa [hφa, xa, ya, fusionPhi] using hG

private theorem elem_inner_of_mulEquiv
    {G : Type u} [Group G] [Finite G]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (A : Subgroup G) [Group.IsPerfect A]
    (hZ : Odd (Nat.card (Subgroup.center A)))
    (e : (A ⧸ Subgroup.center A) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)
    (E : Subgroup G) (hEN : E ≤ fusionN A) (hE : IsElemAbelian 2 E)
    (hcard : 4 * Nat.card F * Nat.card ↥(E ⊓ centralizer (A : Set G)) < Nat.card E) :
    E ≤ A ⊔ centralizer (A : Set G) := by
  classical
  have hZodd : Odd (Nat.card (fusionZ A)) := fusionZ_odd A hZ
  obtain ⟨n, -, hFcard⟩ := FiniteField.card F 2
  let f : ℕ := n
  have hf : 1 ≤ f := n.pos
  have hK : Nat.card F = 2 ^ f := by
    rw [Nat.card_eq_fintype_card, hFcard]
  let E_N : Subgroup (fusionN A) := E.subgroupOf (fusionN A)
  have hE_N : IsElemAbelian 2 E_N :=
    CFSG.LocalAnalysis.EvenBN.LinearThree.isElemAbelian_comap
      (Subgroup.subtype_injective (fusionN A)) hE
  let Ebar : Subgroup (fusionH A) := E_N.map (fusionP A)
  have hEbar : IsElemAbelian 2 Ebar :=
    CFSG.LocalAnalysis.EvenBN.LinearThree.isElemAbelian_map (fusionP A) hE_N
  have hE_N_p : IsPGroup 2 E_N := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    simpa using hE_N.2 x x.2
  have hEbar_card : Nat.card Ebar = Nat.card E_N := by
    have hinj : Function.Injective ((fusionP A).comp E_N.subtype) :=
      fusionP_injective_on_two (A := A) hZodd hE_N_p
    have hmap : (⊤ : Subgroup E_N).map ((fusionP A).comp E_N.subtype) = Ebar := by
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        exact ⟨y, y.2, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, trivial, rfl⟩
    rw [← hmap, Subgroup.card_map_of_injective hinj]
    simp [E_N]
  have hE_N_card : Nat.card E_N = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv
  have hmap_inf : (E_N ⊓ fusionC A).map (fusionP A) =
      Ebar ⊓ Subgroup.centralizer (fusionAbar A : Set (fusionH A)) := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyE, hyC⟩, rfl⟩
      refine ⟨⟨y, hyE, rfl⟩, ?_⟩
      rw [← map_centralizer_fusionAbar (A := A)]
      exact Subgroup.mem_map_of_mem (fusionP A) hyC
    · rintro ⟨hxE, hxC⟩
      obtain ⟨y, hyE, rfl⟩ := hxE
      have hyC : y ∈ fusionC A := by
        rw [← comap_centralizer_fusionAbar (A := A)]
        exact hxC
      exact ⟨y, ⟨hyE, hyC⟩, rfl⟩
  have hE_N_inf_p : IsPGroup 2 ↥(E_N ⊓ fusionC A) := hE_N_p.to_le inf_le_left
  have hEbar_inf_card : Nat.card ↥(Ebar ⊓
      Subgroup.centralizer (fusionAbar A : Set (fusionH A))) =
      Nat.card ↥(E_N ⊓ fusionC A) := by
    have hinj : Function.Injective
        ((fusionP A).comp (E_N ⊓ fusionC A).subtype) :=
      fusionP_injective_on_two (A := A) hZodd hE_N_inf_p
    have hmap : (⊤ : Subgroup ↥(E_N ⊓ fusionC A)).map
        ((fusionP A).comp (E_N ⊓ fusionC A).subtype) =
        Ebar ⊓ Subgroup.centralizer (fusionAbar A : Set (fusionH A)) := by
      rw [← hmap_inf]
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        exact ⟨y, y.2, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, trivial, rfl⟩
    rw [← hmap, Subgroup.card_map_of_injective hinj]
    simp
  have hmapG : (E_N ⊓ fusionC A).map (fusionN A).subtype =
      E ⊓ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.map_inf E_N (fusionC A) (fusionN A).subtype
      (Subgroup.subtype_injective (fusionN A))]
    congr 1
    · rw [show E_N = E.subgroupOf (fusionN A) from rfl, Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.mpr hEN
    · rw [fusionC_eq_subgroupOf, Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.mpr (Subgroup.centralizer_le_normalizer (A : Set G))
  have hE_N_inf_card : Nat.card ↥(E_N ⊓ fusionC A) =
      Nat.card ↥(E ⊓ centralizer (A : Set G)) := by
    rw [← hmapG, Subgroup.card_map_of_injective (Subgroup.subtype_injective (fusionN A))]
  have hbound : 4 * Nat.card F * Nat.card ↥(Ebar ⊓
      Subgroup.centralizer (fusionAbar A : Set (fusionH A))) < Nat.card Ebar := by
    rw [hEbar_card, hE_N_card, hEbar_inf_card, hE_N_inf_card]
    exact hcard
  have hEbar_le : Ebar ≤ fusionAbar A ⊔
      Subgroup.centralizer (fusionAbar A : Set (fusionH A)) :=
    CFSG.LocalAnalysis.EvenBN.LinearThree.elem_inner_of_mulEquiv (A := fusionAbar A)
      (K := F) (G := fusionH A) hf hK (fusionEbar (A := A) e)
      (E := Ebar) (by rw [Subgroup.normalizer_eq_top (fusionAbar A)]; exact le_top) hEbar hbound
  have hEN_le : E_N ≤ fusionA A ⊔ fusionC A := by
    intro x hx
    have hpx : fusionP A x ∈ Ebar := Subgroup.mem_map_of_mem (fusionP A) hx
    have hjoin : fusionP A x ∈ fusionAbar A ⊔
        Subgroup.centralizer (fusionAbar A : Set (fusionH A)) := hEbar_le hpx
    rw [← comap_fusionP_join (A := A)]
    exact hjoin
  intro x hx
  have hxN : (⟨x, hEN hx⟩ : fusionN A) ∈ E_N := hx
  have hjoin := hEN_le hxN
  rw [← map_fusion_join A]
  exact Subgroup.mem_map_of_mem (fusionN A).subtype hjoin

private abbrev fusionV {G : Type u} [Group G] (A : Subgroup G) (V : Subgroup G) :
    Subgroup (fusionN A) :=
  V.subgroupOf (fusionN A)

private abbrev fusionVbar {G : Type u} [Group G] (A : Subgroup G) [hZ : (fusionZ A).Normal]
    (V : Subgroup G) : Subgroup (fusionH A) :=
  (fusionV A V).map (fusionP A)

private theorem isSylowOf_fusionVbar {G : Type u} [Group G] [Finite G]
    {A : Subgroup G} [hZ : (fusionZ A).Normal] {V : Subgroup G}
    (hV : IsSylowOf 2 V A) : IsSylowOf 2 (fusionVbar A V) (fusionAbar A) := by
  classical
  obtain ⟨Q, hQ⟩ := hV
  have hQmap : (Q : Subgroup A).map
      (Subgroup.inclusion (show A ≤ fusionN A from le_normalizer)) = fusionV A V := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hQ ▸ Subgroup.mem_map_of_mem A.subtype hq
    · intro hx
      have hxV : (x : G) ∈ V := hx
      rw [← hQ] at hxV
      obtain ⟨q, hq, hqx⟩ := hxV
      exact ⟨q, hq, Subtype.ext hqx⟩
  let eAN : A ≃* fusionA A :=
    (Subgroup.subgroupOfEquivOfLe (show A ≤ fusionN A from le_normalizer)).symm
  let pA : fusionA A →* fusionAbar A := (fusionP A).subgroupMap (fusionA A)
  have hpA : Function.Surjective pA :=
    MonoidHom.subgroupMap_surjective (fusionP A) (fusionA A)
  let ψ : A →* fusionAbar A := pA.comp eAN.toMonoidHom
  have hψ : Function.Surjective ψ := hpA.comp eAN.surjective
  refine ⟨Q.mapSurjective (f := ψ) hψ, ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map]
  have hcomp : (fusionAbar A).subtype.comp ψ =
      (fusionP A).comp (Subgroup.inclusion (show A ≤ fusionN A from le_normalizer)) := by
    ext x
    rfl
  rw [hcomp, ← Subgroup.map_map, hQmap]

private theorem cent_sylow_of_mulEquiv
    {G : Type u} [Group G] [Finite G]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (A : Subgroup G) [Group.IsPerfect A]
    (hZ : Odd (Nat.card (Subgroup.center A)))
    (e : (A ⧸ Subgroup.center A) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)
    {V : Subgroup G} (hV : IsSylowOf 2 V A) :
    fusionN A ⊓ centralizer (V : Set G) ≤
      (V ⊓ centralizer (V : Set G)) ⊔ centralizer (A : Set G) := by
  classical
  have hZodd : Odd (Nat.card (fusionZ A)) := fusionZ_odd A hZ
  let ebar := fusionEbar (A := A) e
  have hVbar : IsSylowOf 2 (fusionVbar A V) (fusionAbar A) :=
    isSylowOf_fusionVbar (A := A) hV
  let C_H : Subgroup (fusionH A) :=
    Subgroup.centralizer (fusionAbar A : Set (fusionH A))
  intro n hn
  let nN : fusionN A := ⟨n, hn.1⟩
  have hnV : n ∈ Subgroup.centralizer (V : Set G) := hn.2
  have hpn_normalizer : fusionP A nN ∈
      normalizer (fusionAbar A : Set (fusionH A)) := by
    rw [Subgroup.normalizer_eq_top (fusionAbar A)]
    exact mem_top _
  have hpn_V : fusionP A nN ∈
      Subgroup.centralizer (fusionVbar A V : Set (fusionH A)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨v, hv, rfl⟩ := hx
    have hvG : (v : G) ∈ V := by
      simpa [fusionV, Subgroup.mem_subgroupOf] using hv
    have hcomm : (v : G) * n = n * (v : G) :=
      Subgroup.mem_centralizer_iff.mp hnV (v : G) hvG
    change fusionP A v * fusionP A nN = fusionP A nN * fusionP A v
    rw [← map_mul, ← map_mul]
    exact congrArg (fusionP A) (Subtype.ext hcomm)
  have hpn_join : fusionP A nN ∈
      (fusionVbar A V ⊓
        Subgroup.centralizer (fusionVbar A V : Set (fusionH A))) ⊔ C_H :=
    CFSG.LocalAnalysis.EvenBN.LinearThree.cent_sylow_of_mulEquiv ebar hVbar
      ⟨hpn_normalizer, hpn_V⟩
  have hcomm_factor : ∀ z ∈ fusionVbar A V ⊓
      Subgroup.centralizer (fusionVbar A V : Set (fusionH A)),
      ∀ k ∈ C_H, z * k = k * z := by
    intro z hz k hk
    have hVA : fusionV A V ≤ fusionA A := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hV.le (Subgroup.mem_subgroupOf.mp hx))
    have hzA : z ∈ fusionAbar A := Subgroup.map_mono hVA hz.1
    exact Subgroup.mem_centralizer_iff.mp hk z hzA
  obtain ⟨zbar, hzbar, kbar, hkbar, hfactor⟩ :=
    CFSG.OddStandard.Seitz77.mem_sup_of_commute hcomm_factor hpn_join
  obtain ⟨z, hzV, hzp⟩ := hzbar.1
  let zV : fusionV A V := ⟨z, hzV⟩
  have hV_N_p : IsPGroup 2 (fusionV A V) :=
    IsPGroup.of_equiv hV.isPGroup
      (Subgroup.subgroupOfEquivOfLe (show V ≤ fusionN A from
        hV.le.trans (show A ≤ fusionN A from le_normalizer))).symm
  have hzinj : Function.Injective ((fusionP A).comp (fusionV A V).subtype) :=
    fusionP_injective_on_two (A := A) hZodd hV_N_p
  have hzV_center : ∀ v : fusionV A V, v * zV = zV * v := by
    intro v
    apply hzinj
    change fusionP A (v.1 * zV.1) = fusionP A (zV.1 * v.1)
    rw [map_mul, map_mul, hzp]
    exact Subgroup.mem_centralizer_iff.mp hzbar.2 (fusionP A v.1)
      (Subgroup.mem_map_of_mem (fusionP A) v.2)
  have hzV_G : (z : G) ∈ V ⊓ Subgroup.centralizer (V : Set G) := by
    refine ⟨hzV, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro v hv
    let vN : fusionN A := ⟨v, le_normalizer (hV.le hv)⟩
    have hvN : vN ∈ fusionV A V := hv
    have hcommN : vN * zV.1 = zV.1 * vN :=
      congrArg Subtype.val (hzV_center ⟨vN, hvN⟩)
    simpa using congrArg Subtype.val hcommN
  have hzk : zV.1⁻¹ * nN ∈ fusionC A := by
    rw [← comap_centralizer_fusionAbar (A := A)]
    change fusionP A (zV.1⁻¹ * nN) ∈ C_H
    have hpk : fusionP A (zV.1⁻¹ * nN) = kbar := by
      rw [map_mul, map_inv, hzp, hfactor]
      group
    rw [hpk]
    exact hkbar
  have hnN_join : nN ∈
      (fusionV A V ⊓ Subgroup.centralizer (fusionV A V : Set (fusionN A))) ⊔ fusionC A := by
    have hzV_in : zV.1 ∈ fusionV A V := zV.2
    have hzV_center' : zV.1 ∈
        Subgroup.centralizer (fusionV A V : Set (fusionN A)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact congrArg Subtype.val (hzV_center ⟨v, hv⟩)
    rw [show nN = zV.1 * (zV.1⁻¹ * nN) by group]
    exact Subgroup.mul_mem_sup ⟨hzV_in, hzV_center'⟩ hzk
  have hmapVcenter : ((fusionV A V ⊓
      Subgroup.centralizer (fusionV A V : Set (fusionN A))).map
        (fusionN A).subtype) ≤
      V ⊓ Subgroup.centralizer (V : Set G) := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨by simpa [fusionV, Subgroup.mem_subgroupOf] using hw.1,
      Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro v hv
    let vN : fusionN A := ⟨v, le_normalizer (hV.le hv)⟩
    have hvN : vN ∈ fusionV A V := hv
    have hcommN : vN * w = w * vN :=
      Subgroup.mem_centralizer_iff.mp hw.2 vN hvN
    simpa using congrArg Subtype.val hcommN
  have hmapJ : (((fusionV A V ⊓
      Subgroup.centralizer (fusionV A V : Set (fusionN A))) ⊔ fusionC A).map
        (fusionN A).subtype) ≤
      (V ⊓ Subgroup.centralizer (V : Set G)) ⊔
        Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.map_sup]
    exact sup_le (le_trans hmapVcenter le_sup_left)
      (le_trans (le_of_eq (map_fusionC A)) le_sup_right)
  exact hmapJ (Subgroup.mem_map_of_mem (fusionN A).subtype hnN_join)

private theorem outer_fuse_of_mulEquiv
    {G : Type u} [Group G] [Finite G]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (A : Subgroup G) [Group.IsPerfect A]
    (hZ : Odd (Nat.card (Subgroup.center A)))
    (e : (A ⧸ Subgroup.center A) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)
    {y : G} (hyN : y ∈ fusionN A) (hy2 : y * y = 1)
    (hout : y ∉ A ⊔ Subgroup.centralizer (A : Set G))
    {c : G} (hc : c ∈ A ⊓ Subgroup.centralizer ({y} : Set G)) (hc2 : c * c = 1) :
    ∃ b ∈ A, b * y * b⁻¹ = y * c := by
  classical
  have hZodd : Odd (Nat.card (fusionZ A)) := fusionZ_odd A hZ
  let ebar := fusionEbar (A := A) e
  let yN : fusionN A := ⟨y, hyN⟩
  let cN : fusionN A := ⟨c, le_normalizer hc.1⟩
  have hy2N : yN * yN = 1 := Subtype.ext hy2
  have hc2N : cN * cN = 1 := Subtype.ext hc2
  have hcA : cN ∈ fusionA A := hc.1
  have hcomm : cN * yN = yN * cN := by
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp hc.2
  have hyc2 : (yN * cN) * (yN * cN) = 1 := by
    calc (yN * cN) * (yN * cN) = yN * (cN * yN) * cN := by group
      _ = yN * (yN * cN) * cN := by rw [hcomm]
      _ = (yN * yN) * (cN * cN) := by group
      _ = 1 := by rw [hy2N, hc2N, one_mul]
  obtain ⟨n, -, hFcard⟩ := FiniteField.card F 2
  let f : ℕ := n
  have hf : 1 ≤ f := n.pos
  have hK : Nat.card F = 2 ^ f := by
    rw [Nat.card_eq_fintype_card, hFcard]
  have hpy_out : fusionP A yN ∉
      fusionAbar A ⊔ Subgroup.centralizer (fusionAbar A : Set (fusionH A)) := by
    intro h
    have hy_join : yN ∈ fusionA A ⊔ fusionC A := by
      rw [← comap_fusionP_join (A := A)]
      exact h
    have hyG : y ∈ A ⊔ Subgroup.centralizer (A : Set G) := by
      rw [← map_fusion_join A]
      exact Subgroup.mem_map_of_mem (fusionN A).subtype hy_join
    exact hout hyG
  have hpy_norm : fusionP A yN ∈ normalizer (fusionAbar A : Set (fusionH A)) := by
    rw [Subgroup.normalizer_eq_top (fusionAbar A)]
    exact mem_top _
  have hpy2 : fusionP A yN * fusionP A yN = 1 := by
    rw [← map_mul, hy2N, map_one]
  have hpcA : fusionP A cN ∈ fusionAbar A :=
    Subgroup.mem_map_of_mem (fusionP A) hcA
  have hpyc2 : fusionP A (yN * cN) * fusionP A (yN * cN) = 1 := by
    rw [← map_mul, hyc2, map_one]
  obtain ⟨bbar, hbbar, hconjbar⟩ :=
    CFSG.LocalAnalysis.EvenBN.LinearThree.outer_fuse_of_mulEquiv
      (A := fusionAbar A) (K := F) (f := f) hf hK ebar
      (y := fusionP A yN) hpy_norm hpy2 hpy_out (c := fusionP A cN) hpcA hpyc2
  obtain ⟨b0, hb0, hb0eq⟩ := (Subgroup.mem_map).1 hbbar
  let r : fusionN A := b0 * yN * b0⁻¹
  have hyN_ne : yN ≠ 1 := by
    intro h
    apply hout
    have hy1 : y = 1 := by
      have hval := congrArg Subtype.val h
      simpa [yN] using hval
    rw [hy1]
    exact Subgroup.mem_sup_left (A.one_mem)
  have hyN_order : orderOf yN = 2 :=
    orderOf_eq_prime (by rwa [pow_two]) hyN_ne
  have hr2 : orderOf r = 2 := by
    have h := (MulEquiv.orderOf_eq (MulAut.conj b0) yN).trans hyN_order
    simpa [MulAut.conj_apply, r] using h
  have hs_ne : yN * cN ≠ 1 := by
    intro h
    apply hout
    have hy_eq : yN = cN⁻¹ := mul_eq_one_iff_eq_inv.mp h
    have hy_eq' : y = c⁻¹ := by
      have := congrArg Subtype.val hy_eq
      simpa [yN, cN] using this
    rw [hy_eq']
    exact Subgroup.mem_sup_left (A.inv_mem hc.1)
  have hs2 : orderOf (yN * cN) = 2 :=
    orderOf_eq_prime (by rwa [pow_two]) hs_ne
  have hquot : (r : fusionH A) = (yN * cN : fusionH A) := by
    change fusionP A r = fusionP A (yN * cN)
    rw [show fusionP A r = fusionP A b0 * fusionP A yN * (fusionP A b0)⁻¹ by
      simp [r, map_mul, map_inv]]
    rw [hb0eq, hconjbar]
    rfl
  obtain ⟨m, hm, hmconj⟩ :=
    CFSG.RankThree.OddKernel.isConj_of_mk_eq (fusionZ A) hZodd hr2 hs2 hquot
  let bN : fusionN A := m * b0
  have hbN : bN ∈ fusionA A := (fusionA A).mul_mem hm.1 hb0
  have hconjN : bN * yN * bN⁻¹ = yN * cN := by
    have hb : bN * yN * bN⁻¹ = m * r * m⁻¹ := by
      dsimp [bN, r]
      group
    rw [hb, hmconj]
  let b : A := ⟨bN.1, by
    simpa [fusionA, Subgroup.mem_subgroupOf] using hbN⟩
  have hφb : fusionPhi A b = bN := Subtype.ext rfl
  refine ⟨b, b.2, ?_⟩
  have hG := congrArg (fun z : fusionN A => (z : G)) hconjN
  simpa [hφb, yN, cN, fusionPhi] using hG

private theorem perfect_inv_of_mulEquiv
    {G : Type u} [Group G] [Finite G]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (A : Subgroup G) [Group.IsPerfect A]
    (e : (A ⧸ Subgroup.center A) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)
    (hcyc : ∀ S : Sylow 2 (Subgroup.centralizer (A : Set G)), IsCyclic ↥S) :
    ∀ D : Subgroup G, D ≤ fusionN A → ⁅D, D⁆ = D → ∀ c ∈ D, c * c = 1 → c ∈ A := by
  classical
  let ebar := fusionEbar (A := A) e
  intro D hDN hD c hcD hc2
  let D_N : Subgroup (fusionN A) := D.subgroupOf (fusionN A)
  let cN : fusionN A := ⟨c, hDN hcD⟩
  let Dbar : Subgroup (fusionH A) := D_N.map (fusionP A)
  have hDmap : D_N.map (fusionN A).subtype = D := by
    rw [show D_N = D.subgroupOf (fusionN A) from rfl, Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr hDN
  have hD_N_perf : ⁅D_N, D_N⁆ = D_N := by
    rw [← Subgroup.comap_map_eq_self_of_injective
      (Subgroup.subtype_injective (fusionN A)) ⁅D_N, D_N⁆]
    rw [Subgroup.map_commutator, hDmap, hD]
    rw [← hDmap, Subgroup.comap_map_eq_self_of_injective
      (Subgroup.subtype_injective (fusionN A))]
  have hDbar_perf : ⁅Dbar, Dbar⁆ = Dbar := by
    rw [show Dbar = D_N.map (fusionP A) from rfl,
      ← Subgroup.map_commutator D_N D_N (fusionP A), hD_N_perf]
  have hDbarN : Dbar ≤ normalizer (fusionAbar A : Set (fusionH A)) := by
    rw [Subgroup.normalizer_eq_top (fusionAbar A)]
    exact le_top
  have hcDN : cN ∈ D_N := hcD
  have hpcD : fusionP A cN ∈ Dbar := Subgroup.mem_map_of_mem (fusionP A) hcDN
  have hc2N : cN * cN = 1 := Subtype.ext hc2
  have hpc2 : fusionP A cN * fusionP A cN = 1 := by
    rw [← map_mul, hc2N, map_one]
  have hcycH := cyclic_sylow_centralizer_fusionAbar (A := A) hcyc
  have hpcAbar : fusionP A cN ∈ fusionAbar A :=
    CFSG.LocalAnalysis.EvenBN.LinearThree.perfect_inv_of_mulEquiv ebar hcycH
      (D := Dbar) hDbarN hDbar_perf hpcD hpc2
  change cN ∈ (fusionAbar A).comap (fusionP A) at hpcAbar
  rw [comap_fusionP_fusionAbar (A := A)] at hpcAbar
  simpa [cN, fusionA, Subgroup.mem_subgroupOf] using hpcAbar

private theorem outer_perfect_of_mulEquiv
    {G : Type u} [Group G] [Finite G]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : 16 ≤ Nat.card F) (A : Subgroup G) [Group.IsPerfect A]
    (hZ : Odd (Nat.card (Subgroup.center A)))
    (e : (A ⧸ Subgroup.center A) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)
    {y : G} (hyN : y ∈ fusionN A) (hy2 : y * y = 1)
    (hout : y ∉ A ⊔ Subgroup.centralizer (A : Set G)) :
    ∃ D : Subgroup G, D ≤ A ⊓ Subgroup.centralizer ({y} : Set G) ∧
      ⁅D, D⁆ = D ∧ ∃ c ∈ D, orderOf c = 2 := by
  classical
  have hZodd : Odd (Nat.card (fusionZ A)) := fusionZ_odd A hZ
  let ebar := fusionEbar (A := A) e
  let yN : fusionN A := ⟨y, hyN⟩
  have hy2N : yN * yN = 1 := Subtype.ext hy2
  obtain ⟨n, -, hFcard⟩ := FiniteField.card F 2
  let f : ℕ := n
  have hK : Nat.card F = 2 ^ f := by
    rw [Nat.card_eq_fintype_card, hFcard]
  have hf3 : 3 ≤ f := by
    have h4 : 4 ≤ f := by
      apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
      have h : 2 ^ 4 ≤ Nat.card F := by
        rw [show (2:ℕ)^4 = 16 by norm_num]
        exact hF
      rwa [hK] at h
    omega
  have hpy_out : fusionP A yN ∉
      fusionAbar A ⊔ Subgroup.centralizer (fusionAbar A : Set (fusionH A)) := by
    intro h
    have hy_join : yN ∈ fusionA A ⊔ fusionC A := by
      rw [← comap_fusionP_join (A := A)]
      exact h
    have hyG : y ∈ A ⊔ Subgroup.centralizer (A : Set G) := by
      rw [← map_fusion_join A]
      exact Subgroup.mem_map_of_mem (fusionN A).subtype hy_join
    exact hout hyG
  have hpy_norm : fusionP A yN ∈ normalizer (fusionAbar A : Set (fusionH A)) := by
    rw [Subgroup.normalizer_eq_top (fusionAbar A)]
    exact mem_top _
  have hpy2 : fusionP A yN * fusionP A yN = 1 := by
    rw [← map_mul, hy2N, map_one]
  obtain ⟨Dbar, hDbar_le, hDbar_perf, cbar, hcbarD, hcbar_order⟩ :=
    CFSG.LocalAnalysis.EvenBN.LinearThree.outer_perfect_of_mulEquiv
      (A := fusionAbar A) (K := F) (f := f) hf3 hK ebar
      (y := fusionP A yN) hpy_norm hpy2 hpy_out
  let T : Subgroup (fusionN A) := Dbar.comap (fusionP A)
  let fT : T →* Dbar :=
    ((fusionP A).comp T.subtype).codRestrict Dbar fun t => t.2
  have hfT_surj : Function.Surjective fT := by
    intro x
    obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective (fusionZ A) (x : fusionH A)
    refine ⟨⟨n, ?_⟩, Subtype.ext ?_⟩
    · change fusionP A n ∈ Dbar
      rw [hn]
      exact x.2
    · exact hn
  have hT_le_A : T ≤ fusionA A := by
    intro t ht
    rw [← comap_fusionP_fusionAbar (A := A)]
    exact (Subgroup.mem_comap).2 (hDbar_le (Subgroup.mem_comap.mp ht)).1
  have hker_center : fT.ker ≤ Subgroup.center T := by
    intro t ht
    rw [Subgroup.mem_center_iff]
    intro u
    apply Subtype.ext
    have htZ : t.1 ∈ fusionZ A := by
      have hpt : fusionP A t.1 = 1 := by
        have hval := MonoidHom.mem_ker.mp ht
        exact congrArg Subtype.val hval
      exact (QuotientGroup.eq_one_iff _).1 hpt
    exact fusionZ_centralizes A t.1 htZ u.1 (hT_le_A u.2)
  have htop_perf : Group.IsPerfect ↥(⊤ : Subgroup Dbar) :=
    Group.IsPerfect.top_iff.mpr (Subgroup.isPerfect_iff.mpr hDbar_perf)
  have hL : ⁅(⊤ : Subgroup Dbar), ⊤⁆ = ⊤ :=
    @Subgroup.commutator_eq_self Dbar _ (⊤ : Subgroup Dbar) htop_perf
  let D_T : Subgroup T := ⁅(⊤ : Subgroup T), ⊤⁆
  have hDT_perf : ⁅D_T, D_T⁆ = D_T := by
    have htop : (⊤ : Subgroup Dbar).comap fT = ⊤ := by
      ext x
      simp
    have hperf0 := CFSG.GroupTheory.PerfectCover.isPerfect_commutator_comap
      (π := fT) hfT_surj hker_center (L := ⊤) hL
    rw [htop] at hperf0
    exact Subgroup.isPerfect_iff.mp (by simpa [D_T] using hperf0)
  have hmap_DT : D_T.map fT = ⊤ := by
    have htop : (⊤ : Subgroup Dbar).comap fT = ⊤ := by
      ext x
      simp
    have hmap0 := CFSG.GroupTheory.PerfectCover.map_commutator_comap
      (π := fT) hfT_surj (L := ⊤) hL
    rw [htop] at hmap0
    simpa [D_T] using hmap0
  let D_N : Subgroup (fusionN A) := D_T.map T.subtype
  have hD_N_perf : ⁅D_N, D_N⁆ = D_N := by
    rw [show D_N = D_T.map T.subtype from rfl,
      ← Subgroup.map_commutator D_T D_T T.subtype, hDT_perf]
  have hD_N_le_A : D_N ≤ fusionA A := by
    rintro _ ⟨x, -, rfl⟩
    exact hT_le_A x.2
  have hD_N_map_p : D_N.map (fusionP A) = Dbar := by
    have hcomp : Dbar.subtype.comp fT = (fusionP A).comp T.subtype := by
      ext x
      rfl
    calc D_N.map (fusionP A) = D_T.map ((fusionP A).comp T.subtype) := by
          rw [Subgroup.map_map]
      _ = D_T.map (Dbar.subtype.comp fT) := by rw [hcomp]
      _ = (D_T.map fT).map Dbar.subtype := by rw [Subgroup.map_map]
      _ = (⊤ : Subgroup Dbar).map Dbar.subtype := by rw [hmap_DT]
      _ = Dbar := by
          ext x
          constructor
          · rintro ⟨y, -, rfl⟩
            exact y.2
          · intro hx
            exact ⟨⟨x, hx⟩, trivial, rfl⟩
  have hyC : fusionP A yN ∈
      Subgroup.centralizer (Dbar : Set (fusionH A)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact Subgroup.mem_centralizer_singleton_iff.mp (hDbar_le hd).2
  have hconj_mem : ∀ (g : fusionN A),
      fusionP A g ∈ Subgroup.centralizer (Dbar : Set (fusionH A)) →
      ∀ t : fusionN A, t ∈ T → g * t * g⁻¹ ∈ T := by
    intro g hg t ht
    change fusionP A (g * t * g⁻¹) ∈ Dbar
    rw [map_mul, map_mul, map_inv]
    have hcomm := Subgroup.mem_centralizer_iff.mp hg (fusionP A t)
      (Subgroup.mem_comap.mp ht)
    have heq : fusionP A g * fusionP A t * (fusionP A g)⁻¹ = fusionP A t := by
      calc fusionP A g * fusionP A t * (fusionP A g)⁻¹ =
          fusionP A t * fusionP A g * (fusionP A g)⁻¹ := by rw [← hcomm]
        _ = fusionP A t := by group
    rw [heq]
    exact Subgroup.mem_comap.mp ht
  have hyT : yN ∈ normalizer (T : Set (fusionN A)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · exact hconj_mem yN hyC t
    · intro ht
      have h := hconj_mem yN⁻¹ (Subgroup.inv_mem _ hyC) (yN * t * yN⁻¹) ht
      have h' : yN⁻¹ * (yN * t * yN⁻¹) * yN⁻¹⁻¹ = t := by group
      rwa [h'] at h
  let coyT : MulAut T := Subgroup.normalizerMonoidHom T ⟨yN, hyT⟩
  have hDT_map : D_T.map coyT.toMonoidHom = D_T := by
    rw [show D_T = ⁅(⊤ : Subgroup T), ⊤⁆ from rfl, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective coyT.toMonoidHom coyT.surjective]
  let σ : MulAut D_T :=
    (D_T.equivMapOfInjective coyT.toMonoidHom coyT.injective).trans
      (MulEquiv.subgroupCongr hDT_map)
  let R : Subgroup D_T :=
    ((fusionP A).comp (T.subtype.comp D_T.subtype)).ker
  have hR_center : R ≤ Subgroup.center D_T := by
    intro r hr
    rw [Subgroup.mem_center_iff]
    intro u
    apply Subtype.ext
    apply Subtype.ext
    have hrZ : r.1.1 ∈ fusionZ A := by
      have hpr : fusionP A r.1.1 = 1 := MonoidHom.mem_ker.mp hr
      exact (QuotientGroup.eq_one_iff _).1 hpr
    exact fusionZ_centralizes A r.1.1 hrZ u.1.1 (hT_le_A u.1.2)
  have hσ_value : ∀ x : D_T, (σ x).1.1 = yN * x.1.1 * yN⁻¹ := by
    intro x
    change (coyT x.1 : T).1 = yN * x.1.1 * yN⁻¹
    exact Subgroup.normalizerMonoidHom_apply_apply_coe T ⟨yN, hyT⟩ x.1
  have hσ_quot : ∀ x : D_T,
      QuotientGroup.mk' R (σ x) = QuotientGroup.mk' R x := by
    intro x
    have hpxD : fusionP A x.1.1 ∈ Dbar := Subgroup.mem_comap.mp x.1.2
    have hpx : fusionP A (σ x).1.1 = fusionP A x.1.1 := by
      rw [hσ_value x, map_mul, map_mul, map_inv]
      have hcomm := Subgroup.mem_centralizer_iff.mp hyC (fusionP A x.1.1) hpxD
      calc fusionP A yN * fusionP A x.1.1 * (fusionP A yN)⁻¹ =
          fusionP A x.1.1 * fusionP A yN * (fusionP A yN)⁻¹ := by rw [← hcomm]
        _ = fusionP A x.1.1 := by group
    have hmem : σ x * x⁻¹ ∈ R := by
      change fusionP A ((σ x).1.1 * (x.1.1)⁻¹) = 1
      rw [map_mul, map_inv, hpx, mul_inv_cancel]
    have hq : QuotientGroup.mk' R (σ x * x⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hmem
    have hq' : QuotientGroup.mk' R (σ x) * (QuotientGroup.mk' R x)⁻¹ = 1 := by
      simpa [map_mul, map_inv] using hq
    exact mul_inv_eq_one.mp hq'
  have hσid := @central_quotient_trivial_hom_eq_id D_T _
    (Subgroup.isPerfect_iff.mpr hDT_perf) R (inferInstance) hR_center σ.toMonoidHom hσ_quot
  have hDT_central : ∀ d : T, d ∈ D_T →
      d.1 ∈ Subgroup.centralizer ({yN} : Set (fusionN A)) := by
    intro d hd
    have hfix : σ.toMonoidHom ⟨d, hd⟩ = MonoidHom.id D_T ⟨d, hd⟩ :=
      congrArg (fun f : D_T →* D_T => f ⟨d, hd⟩) hσid
    have hfix' : (σ ⟨d, hd⟩ : D_T) = ⟨d, hd⟩ := by simpa using hfix
    have hfixN : ((σ ⟨d, hd⟩).1 : fusionN A) = d.1 :=
      congrArg (fun z : D_T => (z.1 : fusionN A)) hfix'
    have hvalN : d.1 = yN * d.1 * yN⁻¹ := by
      have h := hσ_value ⟨d, hd⟩
      simpa [hfix'] using h
    have hyN_inv : yN⁻¹ = yN := inv_eq_of_mul_eq_one_right hy2N
    have hcommN : d.1 * yN = yN * d.1 := by
      calc d.1 * yN = (yN * d.1 * yN⁻¹) * yN := congrArg (fun x => x * yN) hvalN
        _ = (yN * d.1 * yN) * yN := by rw [hyN_inv]
        _ = yN * d.1 * (yN * yN) := by group
        _ = yN * d.1 := by rw [hy2N, mul_one]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcommN
  have hD_N_central : D_N ≤ Subgroup.centralizer ({yN} : Set (fusionN A)) := by
    intro d hd
    obtain ⟨t, ht, rfl⟩ := hd
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hDT_central t ht))
  let D : Subgroup G := D_N.map (fusionN A).subtype
  have hD_le : D ≤ A ⊓ Subgroup.centralizer ({y} : Set G) := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := hx
    refine ⟨?_, ?_⟩
    · have hmem := Subgroup.mem_map_of_mem (fusionN A).subtype (hD_N_le_A hd)
      rwa [map_fusionA A] at hmem
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hD_N_central hd)))
  have hD_perf : ⁅D, D⁆ = D := by
    rw [show D = D_N.map (fusionN A).subtype from rfl,
      ← Subgroup.map_commutator D_N D_N (fusionN A).subtype, hD_N_perf]
  have h2dvd : 2 ∣ Nat.card D_N := by
    have h2 : 2 ∣ Nat.card Dbar := by
      rw [← hcbar_order]
      exact Subgroup.orderOf_dvd_natCard Dbar hcbarD
    exact h2.trans (hD_N_map_p ▸ Subgroup.card_map_dvd D_N (fusionP A))
  obtain ⟨c_N, hc_N⟩ := exists_prime_orderOf_dvd_card (G := D_N) 2 (by
    rw [← Nat.card_eq_fintype_card]
    exact h2dvd)
  refine ⟨D, hD_le, hD_perf, ?_⟩
  refine ⟨(c_N : fusionN A), ?_, ?_⟩
  · exact ⟨c_N, c_N.2, rfl⟩
  · have hinj : Function.Injective ((fusionN A).subtype.comp D_N.subtype) :=
      (Subgroup.subtype_injective (fusionN A)).comp (Subgroup.subtype_injective D_N)
    simpa using (orderOf_injective ((fusionN A).subtype.comp D_N.subtype) hinj c_N).trans hc_N

private theorem odd_inf_of_odd_center
    {G : Type u} [Group G] [Finite G] {A : Subgroup G}
    (hZ : Odd (Nat.card (Subgroup.center A))) :
    Odd (Nat.card ↥(A ⊓ centralizer (A : Set G))) := by
  rw [← CFSG.OddStandard.Seitz77.map_center_subtype_eq_inf_centralizer (P := A),
    Subgroup.card_map_of_injective A.subtype_injective]
  exact hZ

theorem fusionFacts_of_odd_central_psl_three
    {G : Type u} [Group G] [Finite G]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : 16 ≤ Nat.card F) (A : Subgroup G) [Group.IsPerfect A]
    (hZ : Odd (Nat.card (Subgroup.center A)))
    (e : (A ⧸ Subgroup.center A) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)
    (hcyc : ∀ S : Sylow 2 (Subgroup.centralizer (A : Set G)), IsCyclic ↥S) :
    CFSG.LocalAnalysis.EvenBN.LinearThree.FusionFacts A (Nat.card F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact odd_inf_of_odd_center hZ
  · exact invol_conj_of_mulEquiv A hZ e
  · intro E hEN hE hcard
    exact elem_inner_of_mulEquiv A hZ e E hEN hE hcard
  · intro V hV
    exact cent_sylow_of_mulEquiv A hZ e hV
  · intro y hyN hy2 hout c hc hc2
    exact outer_fuse_of_mulEquiv A hZ e hyN hy2 hout hc hc2
  · intro y hyN hy2 hout
    exact outer_perfect_of_mulEquiv hF A hZ e hyN hy2 hout
  · intro D hDN hD c hcD hc2
    exact perfect_inv_of_mulEquiv A e hcyc D hDN hD c hcD hc2

end LocalInstances

end CFSG.ComponentClassification.GS79bSec5

