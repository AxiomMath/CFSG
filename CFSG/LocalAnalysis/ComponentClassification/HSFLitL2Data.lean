module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Harada
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2Model
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitExclusion
public import CFSG.LocalAnalysis.ComponentClassification.TBLitIntrinsicTypes
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallAbelianModels
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X]

structure L2Data (t : X) (L : Subgroup X) where
  config : Config t L
  syl : Sylow 2 ↥(centralizer ({t} : Set X))
  ψ : ↥(Config.sylowIn syl) →* Perm (ZMod 8)
  ψ_eq_one_iff : ∀ g : ↥(Config.sylowIn syl), ψ g = 1 ↔ (g : X) ∈ coreActionKernel L
  ψ_mem_R8 : ∀ g : ↥(Config.sylowIn syl), (g : X) ∈ L → ψ g ∈ R8
  ψ_mem_H8 : ∀ g : ↥(Config.sylowIn syl), ψ g ∈ H8
  exists_ψ_eq : ∀ σ ∈ R8, ∃ g : ↥(Config.sylowIn syl), (g : X) ∈ L ∧ ψ g = σ
  τ : ↥(centralizer ({t} : Set X)) →* Multiplicative (ZMod 2 × ZMod 2)
  τ_eq : ∀ g : ↥(Config.sylowIn syl),
    τ ⟨g, Config.sylowIn_le syl g.2⟩ = type8 ⟨ψ g, ψ_mem_H8 g⟩

namespace L2Data

variable {t : X} {L : Subgroup X} (A : L2Data t L)

abbrev T : Subgroup X := Config.sylowIn A.syl

abbrev R : Subgroup X := A.T ⊓ L

abbrev K : Subgroup X := A.T ⊓ coreActionKernel L

include A in
theorem orderOf_t : orderOf t = 2 := A.config.orderOf_eq

theorem t_mem_T : t ∈ A.T := A.config.mem_sylow A.syl

theorem t_mem_K : t ∈ A.K := A.config.mem_inf_kernel A.syl

instance isCyclic_K : IsCyclic A.K := A.config.isCyclic_inf_kernel A.syl

theorem card_R [Finite X] : Nat.card A.R = 8 := A.config.card_inf_L A.syl

theorem T_le_centralizer : A.T ≤ centralizer ({t} : Set X) := Config.sylowIn_le _

theorem isPGroup_T : IsPGroup 2 A.T := Config.isPGroup_sylowIn _

theorem commute_of_mem_R_of_mem_K [Finite X] {r k : X} (hr : r ∈ A.R) (hk : k ∈ A.K) :
    r * k = k * r :=
  Config.commute_inf_L_inf_kernel A.syl hr hk

theorem commute_t {g : X} (hg : g ∈ A.T) : g * t = t * g :=
  mem_centralizer_singleton_iff.mp (A.T_le_centralizer hg)

theorem K_inf_L [Finite X] : A.K ⊓ L = ⊥ := A.config.inf_kernel_inf_L A.syl

theorem mem_K_iff {g : X} (hg : g ∈ A.T) : g ∈ A.K ↔ A.ψ ⟨g, hg⟩ = 1 := by
  rw [A.ψ_eq_one_iff]
  exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩

theorem ψ_mem_R8' {g : X} (hg : g ∈ A.R) : A.ψ ⟨g, hg.1⟩ ∈ R8 := A.ψ_mem_R8 _ hg.2

theorem eq_of_ψ_eq [Finite X] {g₁ g₂ : X} (h₁ : g₁ ∈ A.R) (h₂ : g₂ ∈ A.R)
    (h : A.ψ ⟨g₁, h₁.1⟩ = A.ψ ⟨g₂, h₂.1⟩) : g₁ = g₂ := by
  have hm : g₁⁻¹ * g₂ ∈ A.R := mul_mem (inv_mem h₁) h₂
  have hK : g₁⁻¹ * g₂ ∈ A.K := by
    rw [A.mem_K_iff hm.1]
    have : (⟨g₁⁻¹ * g₂, hm.1⟩ : A.T) = (⟨g₁, h₁.1⟩ : A.T)⁻¹ * ⟨g₂, h₂.1⟩ := rfl
    rw [this, map_mul, map_inv, h, inv_mul_cancel]
  have : g₁⁻¹ * g₂ ∈ A.K ⊓ L := ⟨hK, hm.2⟩
  rw [A.K_inf_L, mem_bot, inv_mul_eq_one] at this
  exact this

theorem exists_mem_R_ψ_eq {σ : Perm (ZMod 8)} (hσ : σ ∈ R8) :
    ∃ r : X, ∃ hr : r ∈ A.R, A.ψ ⟨r, hr.1⟩ = σ := by
  obtain ⟨g, hgL, hgσ⟩ := A.exists_ψ_eq σ hσ
  exact ⟨g, ⟨g.2, hgL⟩, hgσ⟩

theorem card_T_eq : Nat.card A.T = Nat.card A.ψ.range * Nat.card A.K := by
  have hker : A.ψ.ker = A.K.subgroupOf A.T := by
    ext g
    rw [MonoidHom.mem_ker, A.ψ_eq_one_iff, mem_subgroupOf]
    exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
  rw [← Subgroup.card_mul_index A.ψ.ker, Subgroup.index_ker, hker,
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : A.K ≤ A.T)).toEquiv, mul_comm]

theorem R8_le_range : R8 ≤ A.ψ.range := by
  intro σ hσ
  obtain ⟨g, -, hg⟩ := A.exists_ψ_eq σ hσ
  exact ⟨g, hg⟩

theorem range_le_H8 : A.ψ.range ≤ H8 := by
  rintro _ ⟨g, rfl⟩
  exact A.ψ_mem_H8 g

variable [Finite X]

theorem eq_t_of_mem_K {k : X} (hk : k ∈ A.K) (hk2 : k ^ 2 = 1) (hk1 : k ≠ 1) : k = t := by
  classical
  have : Fintype A.K := Fintype.ofFinite _
  have ho : orderOf k = 2 := orderOf_eq_prime hk2 hk1
  have hk' : orderOf (⟨k, hk⟩ : A.K) = 2 := by rw [Subgroup.orderOf_mk, ho]
  have ht' : orderOf (⟨t, A.t_mem_K⟩ : A.K) = 2 := by rw [Subgroup.orderOf_mk, A.orderOf_t]
  have hd : 2 ∣ Fintype.card A.K := by
    rw [← hk', ← Nat.card_eq_fintype_card]
    exact orderOf_dvd_natCard _
  have h1 := IsCyclic.card_orderOf_eq_totient hd
  rw [Nat.totient_two] at h1
  have := Finset.card_le_one.mp h1.le ⟨k, hk⟩ (by simp [hk']) ⟨t, A.t_mem_K⟩ (by simp [ht'])
  exact congrArg Subtype.val this

@[expose] noncomputable def ψH : A.T →* H8 := A.ψ.codRestrict H8 A.ψ_mem_H8

@[expose] noncomputable def ψlin : A.T →* (ZMod 8)ˣ := lin8.comp A.ψH

omit [Finite X] in
theorem ψH_coe (g : A.T) : (A.ψH g : Perm (ZMod 8)) = A.ψ g := rfl

omit [Finite X] in
theorem exists_finset_closure_eq_of_le_T {U : Subgroup X} (hU : U ≤ A.T) :
    ∃ s : Finset X, s.card ≤ 4 ∧ closure (s : Set X) = U := by
  classical
  set U' : Subgroup A.T := U.subgroupOf A.T with hU'
  obtain ⟨s, hs, hsU⟩ := exists_finset_closure_eq_of_card_le (U'.map A.ψlin) (k := 2) (by
    calc Nat.card (U'.map A.ψlin) ≤ Nat.card (ZMod 8)ˣ := Subgroup.card_le_card_group _
      _ = 2 ^ 2 := by rw [card_units_zmod_eight]; norm_num)
  set V : Subgroup A.T := U' ⊓ A.ψlin.ker with hV
  have hVC : V.map A.ψ ≤ C8 := by
    rintro _ ⟨g, hg, rfl⟩
    have h1 : A.ψlin g = 1 := (mem_inf.mp hg).2
    exact (lin8_eq_one_iff (A.ψH g)).mp h1
  have : IsCyclic (V.map A.ψ) := Subgroup.isCyclic_of_le hVC
  obtain ⟨s₁, hs₁, hs₁V⟩ := exists_finset_closure_eq_of_isCyclic (V.map A.ψ)
  have hKc : IsCyclic (A.K.subgroupOf A.T) :=
    (subgroupOfEquivOfLe (inf_le_left : A.K ≤ A.T)).isCyclic.mpr A.isCyclic_K
  have hle : V ⊓ A.ψ.ker ≤ A.K.subgroupOf A.T := by
    intro g hg
    exact ⟨g.2, (A.ψ_eq_one_iff g).mp (mem_inf.mp hg).2⟩
  have : IsCyclic (V ⊓ A.ψ.ker : Subgroup A.T) := Subgroup.isCyclic_of_le hle
  obtain ⟨r₁, hr₁, hr₁V⟩ := exists_finset_closure_eq_of_isCyclic (V ⊓ A.ψ.ker)
  obtain ⟨v, hv, hvV⟩ := exists_finset_closure_eq_of_map A.ψ V hs₁ hs₁V hr₁ hr₁V
  obtain ⟨u, hu, huU⟩ := exists_finset_closure_eq_of_map A.ψlin U' hs hsU hv hvV
  refine ⟨u.image A.T.subtype, Finset.card_image_le.trans hu, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, huU, hU', subgroupOf_map_subtype,
    inf_of_le_left hU]

theorem gen4_of_coe_sylow_eq (S : Sylow 2 X) (hS : (S : Subgroup X) = A.T) (P : Subgroup X)
    (hP : IsPGroup 2 P) : ∃ s : Finset X, s.card ≤ 4 ∧ closure (s : Set X) = P :=
  exists_finset_closure_eq_of_sylow S (fun _ hU => A.exists_finset_closure_eq_of_le_T (hS ▸ hU))
    P hP

theorem exists_sylow_eq_of_fix (hfix : ∀ w : X, w ∈ normalizer (A.T : Set X) → w * t * w⁻¹ = t) :
    ∃ S : Sylow 2 X, (S : Subgroup X) = A.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  push Not at hne
  obtain ⟨w, hwN, hwT, hwp⟩ := exists_mem_normalizer_not_mem A.isPGroup_T hne
  have hwC : w ∈ centralizer ({t} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    have := hfix w hwN
    calc w * t = w * t * w⁻¹ * w := by group
      _ = t * w := by rw [this]
  have hle : A.T ⊔ zpowers w ≤ centralizer ({t} : Set X) :=
    sup_le A.T_le_centralizer (zpowers_le.mpr hwC)
  have hQ : IsPGroup 2 ((A.T ⊔ zpowers w).subgroupOf (centralizer ({t} : Set X))) :=
    hwp.comap_of_injective _ (subtype_injective _)
  have hsyl : (A.syl : Subgroup _) ≤ (A.T ⊔ zpowers w).subgroupOf (centralizer ({t} : Set X)) := by
    intro c hc
    exact le_sup_left (a := A.T) ⟨c, hc, rfl⟩
  have heq := A.syl.is_maximal' hQ hsyl
  have hw' : (⟨w, hwC⟩ : centralizer ({t} : Set X)) ∈
      (A.T ⊔ zpowers w).subgroupOf (centralizer ({t} : Set X)) :=
    le_sup_right (a := A.T) (mem_zpowers w)
  rw [heq] at hw'
  exact hwT ⟨_, hw', rfl⟩

theorem gen4_of_fix (hfix : ∀ w : X, w ∈ normalizer (A.T : Set X) → w * t * w⁻¹ = t)
    (P : Subgroup X) (hP : IsPGroup 2 P) :
    ∃ s : Finset X, s.card ≤ 4 ∧ closure (s : Set X) = P := by
  obtain ⟨S, hS⟩ := A.exists_sylow_eq_of_fix hfix
  exact A.gen4_of_coe_sylow_eq S hS P hP

omit [Finite X] in
theorem conj_mem_T {w g : X} (hw : w ∈ normalizer (A.T : Set X)) (hg : g ∈ A.T) :
    w * g * w⁻¹ ∈ A.T :=
  (mem_normalizer_iff.mp hw g).mp hg

omit [Finite X] in
theorem conj_inv_mem_T {w g : X} (hw : w ∈ normalizer (A.T : Set X)) (hg : g ∈ A.T) :
    w⁻¹ * g * w ∈ A.T := by
  have := A.conj_mem_T (inv_mem hw) hg
  rwa [inv_inv] at this

omit [Finite X] in
include A in
theorem conj_t_sq (w : X) : (w * t * w⁻¹) ^ 2 = 1 := by
  rw [conj_pow, ← A.orderOf_t, pow_orderOf_eq_one, mul_one, mul_inv_cancel]

omit [Finite X] in
include A in
theorem conj_t_ne_one (w : X) : w * t * w⁻¹ ≠ 1 := by
  intro h
  have : t = 1 := by
    calc t = w⁻¹ * (w * t * w⁻¹) * w := by group
      _ = 1 := by rw [h]; group
  have h2 := A.orderOf_t
  rw [this, orderOf_one] at h2
  exact absurd h2 (by norm_num)

end L2Data

end CFSG.ComponentClassification.HSFLit
