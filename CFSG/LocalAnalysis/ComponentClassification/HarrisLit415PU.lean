module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415PL
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinSubnormal
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.GH74.Generic.Front.Final
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Generic.S1.LinFull
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Outer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415K2
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415K2U
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma412
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46d
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Lift
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAllInvolutionFourGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import Certificates.Certificate3085Base

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd

namespace L415

theorem eq_of_layerIn_eq {G : Type*} [Group G] [Finite G] {A K J : Subgroup G}
    (hK : IsTwoComponentIn K A) (hL : GSThmB.layerIn A = K) (hJ : IsTwoComponentIn J A) :
    J = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKc := (isTwoComponentIn_iff hK.1).mp hK
  have hJc := (isTwoComponentIn_iff hJ.1).mp hJ
  have hle : J.subgroupOf A ≤ K.subgroupOf A := by
    have h1 : J.subgroupOf A ≤ pLayer ↥A 2 :=
      le_sSup (s := {L : Subgroup ↥A | IsPComponent 2 L}) hJc
    have h2 : (GSThmB.layerIn A).subgroupOf A = pLayer ↥A 2 := subgroupOf_map_subtype_eq _
    rwa [← h2, hL] at h1
  have h3 := CatalogueBPrimeJoin.eq_of_le 2 _ _ hJc hKc hle
  have h4 := congrArg (fun H => H.map A.subtype) h3
  simp only [subgroupOf_map_subtype, inf_eq_left.mpr hJ.1, inf_eq_left.mpr hK.1] at h4
  exact h4

theorem eq_barOf_of_unique {X : Type} [Group X] [Finite X] {m b : X}
    (hbm : b ∈ centralizer ({m} : Set X)) (hb : orderOf b = 2) {J₀ : Subgroup X}
    (huniq : ∀ J : Subgroup X, IsTwoComponentIn J (centralizer {m} ⊓ centralizer {b}) → J = J₀)
    (J' : Subgroup ↥(centralizer {(QuotientGroup.mk ⟨b, hbm⟩ : MBar m)}))
    (hJ' : IsPComponent 2 J') :
    J' = (barOf (centralizer {m}) J₀).subgroupOf
      (centralizer {(QuotientGroup.mk ⟨b, hbm⟩ : MBar m)}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let M := centralizer ({m} : Set X)
  let b' : ↥M := ⟨b, hbm⟩
  let π := QuotientGroup.mk' (pPrimeCore 2 ↥M)
  let C := centralizer ({b'} : Set ↥M)
  have hb'2 : b' * b' = 1 := Subtype.ext (by
    change b * b = 1
    rw [← sq, ← hb, pow_orderOf_eq_one])
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥M)) := by
    have h2 := GSThmB.OddQuot.not_two_dvd_card_ker (H := ↥M)
    rw [QuotientGroup.ker_mk'] at h2
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)
  have hCmap : C.map π = centralizer {(QuotientGroup.mk ⟨b, hbm⟩ : MBar m)} :=
    map_centralizer_eq hodd hb'2
  let φ : ↥C →* ↥(centralizer ({(QuotientGroup.mk ⟨b, hbm⟩ : MBar m)} : Set (MBar m))) :=
    (π.comp C.subtype).codRestrict _ (fun x => hCmap ▸ mem_map_of_mem π x.2)
  have hφs : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [← hCmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hφk : ¬ 2 ∣ Nat.card φ.ker := by
    have hle : φ.ker.map C.subtype ≤ pPrimeCore 2 ↥M := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : π (x : ↥M) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hx'
    have hc : Nat.card φ.ker ∣ Nat.card (pPrimeCore 2 ↥M) := by
      rw [← Subgroup.card_map_of_injective C.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    intro h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans hc))
  obtain ⟨hbij, -, -⟩ :=
    CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection φ hφs hφk
  have hCX : C.map M.subtype = centralizer {m} ⊓ centralizer {b} := by
    rw [map_subtype_centralizer hbm, inf_comm]
  let eC : ↥C ≃* ↥(centralizer ({m} : Set X) ⊓ centralizer {b}) :=
    (C.equivMapOfInjective M.subtype M.subtype_injective).trans (MulEquiv.subgroupCongr hCX)
  obtain ⟨J, hJ, rfl⟩ := hbij.surjOn hJ'
  have hJA : IsTwoComponentIn ((J.map eC.toMonoidHom).map
      (centralizer ({m} : Set X) ⊓ centralizer {b}).subtype)
      (centralizer {m} ⊓ centralizer {b}) := by
    rw [isTwoComponentIn_iff (map_subtype_le _), subgroupOf_map_subtype_eq]
    exact isPComponent_map_mulEquiv eC hJ
  have hJ0 := huniq _ hJA
  have hJ₀A : J₀ ≤ centralizer {m} ⊓ centralizer {b} := hJ0 ▸ map_subtype_le _
  have hJeq : J = (J₀.subgroupOf (centralizer {m} ⊓ centralizer {b})).map
      eC.symm.toMonoidHom := by
    rw [← hJ0, subgroupOf_map_subtype_eq, map_map,
      show eC.symm.toMonoidHom.comp eC.toMonoidHom = MonoidHom.id _ by ext; simp, map_id]
  rw [hJeq]
  have hJb : ∀ x ∈ J₀, x * b = b * x := fun x hx =>
    mem_centralizer_singleton_iff.mp (mem_inf.mp (hJ₀A hx)).2
  ext ⟨y, hy⟩
  constructor
  · rintro ⟨c, hc, hcy⟩
    rw [SetLike.mem_coe, Subgroup.mem_map_equiv, MulEquiv.symm_symm] at hc
    refine ⟨(c : ↥M), hc, ?_⟩
    exact congrArg Subtype.val hcy
  · rintro ⟨x, hx, hxy⟩
    have hxC : x ∈ C := by
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext (hJb _ hx)
    refine ⟨⟨x, hxC⟩, ?_, Subtype.ext hxy⟩
    rw [SetLike.mem_coe, Subgroup.mem_map_equiv, MulEquiv.symm_symm]
    exact hx

end L415

variable {X : Type} [Group X] [Finite X]
  {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X} {w z : X} {V : Subgroup X}
  {i j : ℕ} {z₁ τ α : X} {K₂ W 𝒱 : Subgroup X}

namespace Data415B

variable (hD : Data415B t L p f S w z V i j z₁ τ α K₂ W 𝒱)
include hD

theorem eq_K₂ {J : Subgroup X}
    (hJ : IsTwoComponentIn J
      (centralizer {z₁} ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})) : J = K₂ :=
  L415.eq_of_layerIn_eq hD.fd.isTwoComponentIn_K₂ hD.fd.layerIn_K₂ hJ

theorem pComponent_betaF_eq
    (J' : Subgroup ↥(centralizer {(QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j,
      hD.beta_mem_F⟩ : MBar z₁)}))
    (hJ' : IsPComponent 2 J') :
    J' = (barOf (centralizer {z₁}) K₂).subgroupOf
      (centralizer {(QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j, hD.beta_mem_F⟩ :
        MBar z₁)}) :=
  L415.eq_barOf_of_unique hD.beta_mem_F hD.orderOf_beta (fun _ hJ => hD.eq_K₂ hJ) J' hJ'

end Data415B

end CFSG.ComponentClassification.HarrisLit
