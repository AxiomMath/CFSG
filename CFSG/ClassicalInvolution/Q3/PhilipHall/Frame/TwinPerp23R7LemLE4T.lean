module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7E4Tr

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7

@[expose] def E4S3TwinW (M : Type) [Group M] : Prop :=
  ∀ (K K' : Subgroup M) (s : M), Nonempty (↥K ≃* QuaternionGroup 2) → IsUniqueInvolution K s →
    (∀ c ∈ Subgroup.centralizer ({s} : Set M), conjSub c K = K ∨
      ∀ x ∈ K, ∀ y ∈ conjSub c K, x * y = y * x) →
    K' ∈ CoreAssembly.conjClass K → K' ≠ K → K' ≤ Subgroup.normalizer (K : Set M) →
    (∀ J ∈ CoreAssembly.conjClass K, J ≠ K → J ≤ Subgroup.normalizer (K : Set M) → J = K') →
    ∀ a : M, K ≤ Subgroup.centralizer ({a} : Set M) → K' ≤ Subgroup.centralizer ({a} : Set M) →
      ¬ HasS3Quot ↥(Ea (CoreAssembly.conjClass K) a)

@[expose] def E4S3TwinModel : Prop :=
  ∀ (M : Type) [Group M] [Finite M],
    (CFSG.Blueprint.LieModel M .PSp 3 2 1 ∨ CFSG.Blueprint.LieModel M .POmegaPlus 4 2 1) → E4S3TwinW M

section Tr

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)}

theorem false_of_twinE4_twin (hmodel : E4S3TwinModel) (F : Q8Pre G Φ) {K₁ : Subgroup G}
    (hK₁ : K₁ ∈ Φ) {t₁ : G} (ht₁ : IsUniqueInvolution K₁ t₁) (hno : ¬ TightInO2 t₁)
    (hE : TwinE4 G) {K K' : Subgroup G} (hK : K ∈ Φ) (hK' : K' ∈ Φ) {z : G}
    (hz : IsUniqueInvolution K z) (hne : K' ≠ K) (hle : K' ≤ Subgroup.normalizer (K : Set G))
    (hperp : ∀ J ∈ Φ, J ≠ K → J ≤ Subgroup.normalizer (K : Set G) → J = K')
    {a : G} (haK : K ≤ Subgroup.centralizer ({a} : Set G))
    (haK' : K' ≤ Subgroup.centralizer ({a} : Set G)) (ha : HasS3Quot ↥(Ea Φ a)) : False := by
  obtain ⟨Q, hQ, f, hfs, hker, hM⟩ := hE
  have hN2 : IsPGroup 2 ↥f.ker := hker
  have hzN : ∀ J ∈ Φ, ∀ u : G, IsUniqueInvolution J u → u ∉ f.ker := by
    intro J hJ u hu huN
    obtain ⟨g, rfl⟩ := F.trans K₁ hK₁ J hJ
    have hu' : g * t₁ * g⁻¹ = u := (ht₁.conj g).eq hu
    apply hno
    refine ⟨f.ker, inferInstance, hN2, ?_⟩
    have h3 := (inferInstance : f.ker.Normal).conj_mem u huN g⁻¹
    rw [← hu'] at h3
    simpa [mul_assoc] using h3
  have hmeet : ∀ J ∈ Φ, J ⊓ f.ker = ⊥ := fun J hJ => TwinDisc.ExitE4.inf_eq_bot F.two F.hyp hzN hJ
  have hNc : f.ker ≤ Subgroup.center G :=
    TwinDisc.ExitE4.center_of_meet F.hyp F.two F.gen hN2 hmeet
  have hc : CentQuotGen Φ f.ker := TwinDisc.ExitE4.centQuotGen F.hyp F.two hNc hmeet
  have hΦ : CoreAssembly.conjClass K = Φ := conjClass_eq F hK
  let e : (G ⧸ f.ker) ≃* Q := QuotientGroup.quotientKerEquivOfSurjective f hfs
  have hMq : CFSG.Blueprint.LieModel (G ⧸ f.ker) .PSp 3 2 1 ∨
      CFSG.Blueprint.LieModel (G ⧸ f.ker) .POmegaPlus 4 2 1 :=
    hM.imp (fun h => CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)
      (fun h => CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)
  have hinvK : IsUniqueInvolution (K.map (QuotientGroup.mk' f.ker)) (QuotientGroup.mk' f.ker z) :=
    AscQuot.isUniqueInvolution_map_mk (hmeet K hK) hz
  have hq8K : Nonempty (↥(K.map (QuotientGroup.mk' f.ker)) ≃* QuaternionGroup 2) := by
    obtain ⟨eK⟩ := F.q8 K hK
    exact ⟨(AscQuot.quotRestrictEquiv (hmeet K hK)).symm.trans eK⟩
  have htw := twin_clause_map F hNc hK hz
  have hqf : quotFamily Φ f.ker = CoreAssembly.conjClass (K.map (QuotientGroup.mk' f.ker)) := by
    rw [← hΦ]
    exact QuaternionBridge.image_conjClass K
  have hK'cls : K'.map (QuotientGroup.mk' f.ker) ∈
      CoreAssembly.conjClass (K.map (QuotientGroup.mk' f.ker)) := by
    rw [← hqf]
    exact map_mem_quotFamily hK'
  have hK'ne : K'.map (QuotientGroup.mk' f.ker) ≠ K.map (QuotientGroup.mk' f.ker) :=
    hc.map_ne_of_ne hK hK' hne
  have hK'le : K'.map (QuotientGroup.mk' f.ker) ≤
      Subgroup.normalizer ((K.map (QuotientGroup.mk' f.ker) : Subgroup (G ⧸ f.ker)) :
        Set (G ⧸ f.ker)) := by
    rintro _ ⟨u, hu, rfl⟩
    exact Subgroup.le_normalizer_map _ ⟨u, hle hu, rfl⟩
  have hperp' : ∀ J ∈ CoreAssembly.conjClass (K.map (QuotientGroup.mk' f.ker)),
      J ≠ K.map (QuotientGroup.mk' f.ker) →
      J ≤ Subgroup.normalizer ((K.map (QuotientGroup.mk' f.ker) : Subgroup (G ⧸ f.ker)) :
        Set (G ⧸ f.ker)) → J = K'.map (QuotientGroup.mk' f.ker) := by
    intro J hJ hJne hJle
    rw [← hqf] at hJ
    obtain ⟨J₀, hJ₀, rfl⟩ := hJ
    have hJ₀ne : J₀ ≠ K := fun h => hJne (by rw [h])
    have hJ₀le : J₀ ≤ Subgroup.normalizer (K : Set G) := fun u hu =>
      hc.normalizer_of_map K hK u (hJle (Subgroup.mem_map_of_mem _ hu))
    rw [hperp J₀ hJ₀ hJ₀ne hJ₀le]
  have hS3 : HasS3Quot ↥((Ea Φ a).map (QuotientGroup.mk' f.ker)) := by
    refine HasS3Quot.of_surjective ((QuotientGroup.mk' f.ker).subgroupMap (Ea Φ a))
      (MonoidHom.subgroupMap_surjective _ _) (fun x hx => ?_) ha
    have h1 : QuotientGroup.mk' f.ker (x : G) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      simpa using this
    have hxN : (x : G) ∈ f.ker := (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨k, hk⟩ := hker ⟨(x : G), hxN⟩
    refine ⟨k, Subtype.ext ?_⟩
    have := congrArg (fun y : ↥f.ker => (y : G)) hk
    simpa using this
  exact hmodel (G ⧸ f.ker) hMq (K.map (QuotientGroup.mk' f.ker)) (K'.map (QuotientGroup.mk' f.ker))
    (QuotientGroup.mk' f.ker z) hq8K hinvK htw hK'cls hK'ne hK'le hperp' (QuotientGroup.mk' f.ker a)
    (map_le_centralizer_singleton _ haK) (map_le_centralizer_singleton _ haK')
    (by rw [← hqf, Ea_quotFamily hc a]; exact hS3)

end Tr

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
