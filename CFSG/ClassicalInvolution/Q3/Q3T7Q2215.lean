module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q2214

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
open scoped commutatorElement MatrixGroups
namespace C22N
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22N
set_option linter.unusedSectionVars false
section Layer
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ K₄ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem layer1_neg [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.OddCoreLayerNeg3] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.C22G.PsuLayerApi3] [IsSimpleGroup G]
    (h22 : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃)
    (hα : alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) = ⊥)
    (hL : Q3T8.Asc77.LayerOrthType Ω (u₁ * u₂) 6 false) (hK₄ : K₄ ∈ twinSet Ω K) (h41 : K₄ ≠ K)
    (h42 : K₄ ≠ K') (h43 : K₄ ≠ K₃) {R R' : Subgroup G} {b b' y : G}
    (hF : Q3T8.Asc77.C22P.FrameData Ω K₃ K₄ z (u₁ * u₂) R R' b b' y) :
    ExactMembers Ω ∧
      (∃ W, Phan.UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W K₃ (conjSub y K₃)) ∧
      K₄ ≤ Q3T8.Asc77.ExactLayer.exactLayer Ω (u₁ * u₂) ∧
        Q3T8.Asc77.ExactLayer.exactLayer Ω (u₁ * u₂) = conjSub y K₄ ⊔ K₃ ⊔ conjSub y K₃ := by
  classical
  have hs : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃ := h22.setting
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  have hK : K ∈ Ω := hs.stand.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hK₃Ω : K₃ ∈ Ω := hs.hK₃.1
  have hK₄Ω : K₄ ∈ Ω := hK₄.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hzK' : IsUniqueInvolution K' z := hs.hzK'
  have hzK₃ : IsUniqueInvolution K₃ z := hs.hzK₃
  have hzK₄ : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet hz hK₄
  have hcls : ∀ M ∈ Ω, ∃ z', Q3T8.Generic.IsClassicalMember M z' := hΩ.classical
  set u : G := u₁ * u₂ with hu
  have hu2 : u * u = 1 := hs.sq_12
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) := Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one
      hu2
  have hu1 : u ≠ 1 :=
    (Q3T8.Asc77.T7S22.mul_ne_one_of_twins hΩ hK hK' hs.hne.symm hz hs.hu₁.1 hs.hu₂.1 hs.hu₂.2).1
  
  have hu₁K₃ : u₁ ∈ trivialOnQuot K₃ :=
    Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hK hK₃Ω hs.hK₃K.symm hz hzK₃ hs.hu₁.1
  have hu₂K₃ : u₂ ∈ trivialOnQuot K₃ :=
    Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hK' hK₃Ω hs.hK₃K'.symm hzK' hzK₃ hs.hu₂.1
  have hK₃t : K₃ ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω u := ⟨hK₃Ω, Subgroup.mul_mem _ hu₁K₃ hu₂K₃⟩
  have hex₃ : IsSylow2In R (Q3T8.Asc77.ExactLayer.exactCore u K₃) :=
    (Q3T8.Asc77.ExactLayer.isSylow2In_exactCore_iff hΩ hc2 hK₃Ω hK₃t.2).mpr ⟨hF.hR, hF.hRc⟩
  have hzY : z ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω u := by
    have hb : b ∈ Q3T8.Asc77.ExactLayer.exactCore u K₃ := hex₃.1 hF.hbR
    have : z ∈ Q3T8.Asc77.ExactLayer.exactCore u K₃ := hF.hbz ▸ (Q3T8.Asc77.ExactLayer.exactCore u
        K₃).mul_mem hb hb
    exact Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hK₃t this
  
  have hOc : classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u) = ⊥ := by
    refine Q3T8.Asc77.C22N.oddCore_layer_eq_bot_neg h22 hu1 hα hL hzY hzK₃.sq ?_
    intro hall
    have h1 := hall y hF.hy
    apply hF.htz
    rw [← hF.hyz, h1]
    group
  have hex : ExactMembers Ω := Q3T8.Asc77.C22P.exactMembers_S hs hα hOc hL
  
  have hKV : K ∈ twinSet Ω K := mem_twinSet_self hK hz
  have cKK₃ : Commutes K K₃ := Q3T8.Asc77.C22P.commutes_of_twins hs.stand hz hKV hs.hK₃
      hs.hK₃K.symm hex
  have cKK₄ : Commutes K K₄ := Q3T8.Asc77.C22P.commutes_of_twins hs.stand hz hKV hK₄ h41.symm hex
  have cK'K₃ : Commutes K' K₃ := Q3T8.Asc77.C22P.commutes_of_twins hs.stand hz hs.hK' hs.hK₃
      hs.hK₃K'.symm hex
  have cK'K₄ : Commutes K' K₄ := Q3T8.Asc77.C22P.commutes_of_twins hs.stand hz hs.hK' hK₄ h42.symm
      hex
  have cK₃K₄ : Commutes K₃ K₄ := Q3T8.Asc77.C22P.commutes_of_twins hs.stand hz hs.hK₃ hK₄ h43.symm
      hex
  have hcen : ∀ {M : Subgroup G}, Commutes K M → Commutes K' M →
      M ≤ Subgroup.centralizer ({u} : Set G) := by
    intro M h1 h2 x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e1 : x * u₁ = u₁ * x := (h1 u₁ hs.hu₁.1 x hx).symm
    have e2 : x * u₂ = u₂ * x := (h2 u₂ hs.hu₂.1 x hx).symm
    calc x * (u₁ * u₂) = (x * u₁) * u₂ := by group
      _ = u₁ * (x * u₂) := by rw [e1]; group
      _ = u₁ * (u₂ * x) := by rw [e2]
      _ = (u₁ * u₂) * x := by group
  have hK₃c : K₃ ≤ Subgroup.centralizer ({u} : Set G) := hcen cKK₃ cK'K₃
  have hK₄c : K₄ ≤ Subgroup.centralizer ({u} : Set G) := hcen cKK₄ cK'K₄
  have hyc : y ∈ Subgroup.centralizer ({u} : Set G) :=
      Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω u hF.hy
  have hJc : conjSub y K₃ ≤ Subgroup.centralizer ({u} : Set G) :=
    C22P.conjSub_le_centralizer_of_mem hyc hK₃c
  have hJ'c : conjSub y K₄ ≤ Subgroup.centralizer ({u} : Set G) :=
    C22P.conjSub_le_centralizer_of_mem hyc hK₄c
  have hJΩ : conjSub y K₃ ∈ Ω := hΩ.conjInvariant y K₃ hK₃Ω
  have hJ'Ω : conjSub y K₄ ∈ Ω := hΩ.conjInvariant y K₄ hK₄Ω
  have hK₃Φ : K₃ ∈ Q3T8.Asc77.ExactLayer.exactFamily Ω u :=
      Q3T8.Asc77.ExactLayer.centMembers_subset_exactFamily hcls ⟨hK₃Ω, hK₃c⟩
  have hK₄Φ : K₄ ∈ Q3T8.Asc77.ExactLayer.exactFamily Ω u :=
      Q3T8.Asc77.ExactLayer.centMembers_subset_exactFamily hcls ⟨hK₄Ω, hK₄c⟩
  have hJΦ : conjSub y K₃ ∈ Q3T8.Asc77.ExactLayer.exactFamily Ω u :=
    Q3T8.Asc77.ExactLayer.centMembers_subset_exactFamily hcls ⟨hJΩ, hJc⟩
  have hJ'Φ : conjSub y K₄ ∈ Q3T8.Asc77.ExactLayer.exactFamily Ω u :=
    Q3T8.Asc77.ExactLayer.centMembers_subset_exactFamily hcls ⟨hJ'Ω, hJ'c⟩
  have htJ : IsUniqueInvolution (conjSub y K₃) (b * b' * u) := hF.hyz ▸ hzK₃.conj y
  have htJ' : IsUniqueInvolution (conjSub y K₄) (b * b' * u) := hF.hyz ▸ hzK₄.conj y
  obtain ⟨hKJ, hKJc⟩ := Q3T8.Asc77.C22P.not_commutes_of_involution_S hs hs.hK₃ hJΩ htJ hF.htz
  obtain ⟨hKJ', hKJc'⟩ := Q3T8.Asc77.C22P.not_commutes_of_involution_S hs hs.hK₃ hJ'Ω htJ' hF.htz
  obtain ⟨P⟩ := Q3T8.Asc77.C22N.nonempty_psuLayer_of_layerOrth hOc hL
  obtain ⟨RK, hRK, hKR⟩ := P.fund K₃ hK₃Φ
  obtain ⟨RK', hRK', hKR'⟩ := P.fund K₄ hK₄Φ
  obtain ⟨RJ, hRJ, hJR⟩ := P.fund _ hJΦ
  obtain ⟨RJ', hRJ', hJ'R⟩ := P.fund _ hJ'Φ
  have hbK₃ : b ∈ K₃ := hF.hR.1 hF.hbR
  have hb'K₄ : b' ∈ K₄ := hF.hR'.1 hF.hb'R'
  have hle : ∀ {M : Subgroup G}, M ∈ Q3T8.Asc77.ExactLayer.exactFamily Ω u → M ≤ omegaGen
      (Q3T8.Asc77.ExactLayer.exactFamily Ω u) :=
    fun hM => le_omegaGen hM
  have he : u ∈ omegaGen (Q3T8.Asc77.ExactLayer.exactFamily Ω u) := by
    have h1 : b * b' ∈ omegaGen (Q3T8.Asc77.ExactLayer.exactFamily Ω u) :=
      Subgroup.mul_mem _ (hle hK₃Φ hbK₃) (hle hK₄Φ hb'K₄)
    have h2 : b * b' * u ∈ omegaGen (Q3T8.Asc77.ExactLayer.exactFamily Ω u) := hle hJΦ htJ.mem
    have h3 : (b * b')⁻¹ * (b * b' * u) ∈ omegaGen (Q3T8.Asc77.ExactLayer.exactFamily Ω u) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) h2
    have e : (b * b')⁻¹ * (b * b' * u) = u := by group
    rwa [e] at h3
  have hec : ∀ y' ∈ omegaGen (Q3T8.Asc77.ExactLayer.exactFamily Ω u), u * y' = y' * u := by
    intro y' hy'
    have hy'' : y' ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω u := (Q3T8.Asc77.T7Z.exactLayer_eq_omegaGen
        Ω u) ▸ hy'
    exact (Subgroup.mem_centralizer_singleton_iff.mp
        (Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω u hy'')).symm
  have htab : b * b' * u = b * b' * u := rfl
  obtain ⟨h1, h2⟩ := (Fact.out : Q3T8.Asc77.C22G.PsuLayerApi3).pair P hRK hRJ hKR hKR' hJR hzK₃ htJ
    hbK₃ hb'K₄ hF.hbz cK₃K₄ he hec htab hKJ hKJc
  obtain ⟨h1', -⟩ := (Fact.out : Q3T8.Asc77.C22G.PsuLayerApi3).pair P hRK hRJ' hKR hKR' hJ'R hzK₃
      htJ'
    hbK₃ hb'K₄ hF.hbz cK₃K₄ he hec htab hKJ' hKJc'
  have hK₄le : K₄ ≤ Q3T8.Asc77.ExactLayer.exactLayer Ω u := (Q3T8.Asc77.T7Z.exactLayer_eq_omegaGen
      Ω u) ▸ hle hK₄Φ
  refine ⟨hex, h2, hK₄le, ?_⟩
  obtain ⟨W₁, hW₁⟩ := h1'
  have hgen := (Fact.out : Q3T8.Asc77.C22G.PsuLayerApi3).sup P hRJ' hKR hJR hJ'R
    ⟨W₁, Generic.unitaryBlockStandardPair_symm hW₁⟩ h1 (cK₃K₄.conjSub y)
  rw [Q3T8.Asc77.T7Z.exactLayer_eq_omegaGen Ω u]
  exact hgen.symm
end Layer
end C22N
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement MatrixGroups
namespace C22N
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22N
set_option linter.unusedSectionVars false
section Layer
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ K₄ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem layer2_neg [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.OddCoreLayerNeg3] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.C22G.PsuLayerApi3] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51z] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51u]
    (h22 : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃)
    (hex : ExactMembers Ω) (hπ : piSign 3 1 = false)
    (hα : alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) = ⊥) (hK₄ : K₄ ∈ twinSet Ω K)
    (h41 : K₄ ≠ K) (h42 : K₄ ≠ K') (h43 : K₄ ≠ K₃)
    (hV : ∀ M ∈ twinSet Ω K, M = K ∨ M = K' ∨ M = K₃ ∨ M = K₄) {R R' : Subgroup G}
    {b b' y : G} (hF : Q3T8.Asc77.C22P.FrameData Ω K₃ K₄ z (u₁ * u₂) R R' b b' y)
    (hP1 : ∃ W, Phan.UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W K₃ (conjSub y K₃)) :
    (∃ W, Phan.UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W K (conjSub y K₃)) ∧
      (∃ W, Phan.UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W K' (conjSub y K₃)) ∧
      conjSub y K₄ ≤ Q3T8.Asc77.ExactLayer.exactLayer Ω (b * b') ∧
      Q3T8.Asc77.ExactLayer.exactLayer Ω (b * b') = K' ⊔ conjSub y K₃ ⊔ K ∧
      classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω (b * b')) = ⊥ := by
  classical
  have hs : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃ := h22.setting
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  have hKΩ : K ∈ Ω := hs.stand.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hK₃Ω : K₃ ∈ Ω := hs.hK₃.1
  have hK₄Ω : K₄ ∈ Ω := hK₄.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hzK' : IsUniqueInvolution K' z := hs.hzK'
  have hzK₃ : IsUniqueInvolution K₃ z := hs.hzK₃
  have hzK₄ : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet hz hK₄
  have hcls : ∀ M ∈ Ω, ∃ z', Q3T8.Generic.IsClassicalMember M z' := hΩ.classical
  set u : G := u₁ * u₂ with hu
  have hu2 : u * u = 1 := hs.sq_12
  have hbK₃ : b ∈ K₃ := hF.hR.1 hF.hbR
  have hb'K₄ : b' ∈ K₄ := hF.hR'.1 hF.hb'R'
  have hbb : b * b' = b' * b := hF.hRR' b hF.hbR b' hF.hb'R'
  have hbb2 : (b * b') * (b * b') = 1 := by
    calc (b * b') * (b * b') = b * (b' * b) * b' := by group
      _ = b * (b * b') * b' := by rw [← hbb]
      _ = (b * b) * (b' * b') := by group
      _ = 1 := by rw [hF.hbz, hF.hb'z]; exact hzK₃.sq
  have hbb1 : b * b' ≠ 1 :=
    (Q3T8.Asc77.T7S22.mul_ne_one_of_twins hΩ hK₃Ω hK₄Ω h43.symm hzK₃ hbK₃ hb'K₄ hF.hb'4).1
  have hc2' : IsPGroup 2 (Subgroup.zpowers (b * b')) :=
      Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hbb2
  
  have hKV : K ∈ twinSet Ω K := mem_twinSet_self hKΩ hz
  have cKK' : Commutes K K' := Q3T8.Asc77.C22P.commutes_of_twins hs.stand hz hKV hs.hK' hs.hne.symm
      hex
  have cKK₃ : Commutes K K₃ := Q3T8.Asc77.C22P.commutes_of_twins hs.stand hz hKV hs.hK₃
      hs.hK₃K.symm hex
  have cKK₄ : Commutes K K₄ := Q3T8.Asc77.C22P.commutes_of_twins hs.stand hz hKV hK₄ h41.symm hex
  have cK'K₃ : Commutes K' K₃ := Q3T8.Asc77.C22P.commutes_of_twins hs.stand hz hs.hK' hs.hK₃
      hs.hK₃K'.symm hex
  have cK'K₄ : Commutes K' K₄ := Q3T8.Asc77.C22P.commutes_of_twins hs.stand hz hs.hK' hK₄ h42.symm
      hex
  have cK₃K₄ : Commutes K₃ K₄ := Q3T8.Asc77.C22P.commutes_of_twins hs.stand hz hs.hK₃ hK₄ h43.symm
      hex
  have hK₃c : K₃ ≤ Subgroup.centralizer ({u} : Set G) :=
    C22P.le_centralizer_mul hs.hu₁.1 hs.hu₂.1 cKK₃ cK'K₃
  have hK₄c : K₄ ≤ Subgroup.centralizer ({u} : Set G) :=
    C22P.le_centralizer_mul hs.hu₁.1 hs.hu₂.1 cKK₄ cK'K₄
  have hKc' : K ≤ Subgroup.centralizer ({b * b'} : Set G) :=
    C22P.le_centralizer_mul hbK₃ hb'K₄ cKK₃.symm cKK₄.symm
  have hK'c' : K' ≤ Subgroup.centralizer ({b * b'} : Set G) :=
    C22P.le_centralizer_mul hbK₃ hb'K₄ cK'K₃.symm cK'K₄.symm
  have hyc : y ∈ Subgroup.centralizer ({u} : Set G) :=
      Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω u hF.hy
  have hJc : conjSub y K₃ ≤ Subgroup.centralizer ({u} : Set G) :=
    C22P.conjSub_le_centralizer_of_mem hyc hK₃c
  have hJ'c : conjSub y K₄ ≤ Subgroup.centralizer ({u} : Set G) :=
    C22P.conjSub_le_centralizer_of_mem hyc hK₄c
  have hJΩ : conjSub y K₃ ∈ Ω := hΩ.conjInvariant y K₃ hK₃Ω
  have hJ'Ω : conjSub y K₄ ∈ Ω := hΩ.conjInvariant y K₄ hK₄Ω
  have htJ : IsUniqueInvolution (conjSub y K₃) (b * b' * u) := hF.hyz ▸ hzK₃.conj y
  have htJ' : IsUniqueInvolution (conjSub y K₄) (b * b' * u) := hF.hyz ▸ hzK₄.conj y
  
  have hcentJ : ∀ {M : Subgroup G} {t : G}, IsUniqueInvolution M t →
      M ≤ Subgroup.centralizer ({u} : Set G) → t = b * b' * u →
        M ≤ Subgroup.centralizer ({b * b'} : Set G) := by
    intro M t ht hMu htt x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e1 : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp (hMu hx)
    have e2 : x * t = t * x := (ht.commute_of_mem hx).symm
    rw [htt] at e2
    have e3 : b * b' = (b * b' * u) * u := by
      calc b * b' = b * b' * (u * u) := by rw [hu2, mul_one]
        _ = (b * b' * u) * u := by group
    calc x * (b * b') = x * ((b * b' * u) * u) := by rw [← e3]
      _ = (x * (b * b' * u)) * u := by group
      _ = (b * b' * u) * (x * u) := by rw [e2]; group
      _ = (b * b' * u) * (u * x) := by rw [e1]
      _ = ((b * b' * u) * u) * x := by group
      _ = (b * b') * x := by rw [← e3]
  have hJc' : conjSub y K₃ ≤ Subgroup.centralizer ({b * b'} : Set G) := hcentJ htJ hJc rfl
  have hJ'c' : conjSub y K₄ ≤ Subgroup.centralizer ({b * b'} : Set G) := hcentJ htJ' hJ'c rfl
  have hKΦ : K ∈ Q3T8.Asc77.ExactLayer.exactFamily Ω (b * b') :=
      Q3T8.Asc77.ExactLayer.centMembers_subset_exactFamily hcls ⟨hKΩ, hKc'⟩
  have hK'Φ : K' ∈ Q3T8.Asc77.ExactLayer.exactFamily Ω (b * b') :=
      Q3T8.Asc77.ExactLayer.centMembers_subset_exactFamily hcls ⟨hK'Ω, hK'c'⟩
  have hJΦ : conjSub y K₃ ∈ Q3T8.Asc77.ExactLayer.exactFamily Ω (b * b') :=
    Q3T8.Asc77.ExactLayer.centMembers_subset_exactFamily hcls ⟨hJΩ, hJc'⟩
  have hJ'Φ : conjSub y K₄ ∈ Q3T8.Asc77.ExactLayer.exactFamily Ω (b * b') :=
    Q3T8.Asc77.ExactLayer.centMembers_subset_exactFamily hcls ⟨hJ'Ω, hJ'c'⟩
  have hle : ∀ {M : Subgroup G}, M ∈ Q3T8.Asc77.ExactLayer.exactFamily Ω (b * b') →
      M ≤ omegaGen (Q3T8.Asc77.ExactLayer.exactFamily Ω (b * b')) := fun hM => le_omegaGen hM
  
  obtain ⟨R₁, R₂, R₃, hR₁, hR₂, -, hu₁R, hu₂R, -, c12, c13, c23⟩ :=
      Q3T8.Asc77.T7J.exists_sylow_triple hs
  have hu₁Ω : u₁ * u₁ = z := sq_eq_involution_of_orderOf_four hz hs.hu₁.1 hs.hu₁.2
  have hu₂Ω : u₂ * u₂ = z := sq_eq_involution_of_orderOf_four hzK' hs.hu₂.1 hs.hu₂.2
  
  have hBelow : Q3T8.Generic.CITBelowU (Nat.card G) := hs.stand.below
  have hMz : Q3T8.Generic.IsClassicalMember K₃ z := Q3T8.Asc77.isClassicalMember_of_twin hΩ hK₃Ω
      hzK₃
  have hnc : ¬ ({b * b'} : Set G) ⊆ Subgroup.center G :=
    Balance.not_subset_center_of_ne_one (Q3T8.Asc77.exists_noncomm_of_isClassicalMember hMz) hbb1
  have hKt : K ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (b * b') := ⟨hKΩ,
      mem_trivialOnQuot_of_le_centralizer hKc'⟩
  have hK't : K' ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (b * b') := ⟨hK'Ω,
      mem_trivialOnQuot_of_le_centralizer hK'c'⟩
  have hJt : conjSub y K₃ ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (b * b') :=
    ⟨hJΩ, mem_trivialOnQuot_of_le_centralizer hJc'⟩
  have hb'K₃ : b' ∈ trivialOnQuot K₃ :=
    Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hK₄Ω hK₃Ω h43 hzK₄ hzK₃ hb'K₄
  have hbK₄ : b ∈ trivialOnQuot K₄ :=
    Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hK₃Ω hK₄Ω h43.symm hzK₃ hzK₄ hbK₃
  have hnotK₃ : K₃ ∉ Q3T8.Asc77.ExactLayer.tqMembers Ω (b * b') :=
    Q3T8.Asc77.T7J.not_mem_tqMembers_of_mul hΩ hK₃Ω hzK₃ hbK₃ hF.hb4 hb'K₃ rfl
  have hnotK₄ : K₄ ∉ Q3T8.Asc77.ExactLayer.tqMembers Ω (b * b') :=
    Q3T8.Asc77.T7J.not_mem_tqMembers_of_mul hΩ hK₄Ω hzK₄ hb'K₄ hF.hb'4 hbK₄ hbb
  have hperp : ∀ J₀ ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (b * b'), J₀ ∈ KPerp Ω K → J₀ = K ∨ J₀ = K'
      := by
    intro J₀ hJt₀ hJperp
    rw [hs.perp] at hJperp
    rcases hV J₀ hJperp with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · rw [h] at hJt₀
      exact absurd hJt₀ hnotK₃
    · rw [h] at hJt₀
      exact absurd hJt₀ hnotK₄
  have hperp' : ∀ J₀ ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (b * b'), J₀ ∈ KPerp Ω K' → J₀ = K' ∨ J₀ =
      K := by
    intro J₀ hJt₀ hJperp
    rw [Q3T8.Asc77.T7S22.perp_of_twin hs hs.hK', twinSet_eq_of_mem_twinSet hz hs.hK'] at hJperp
    rcases hV J₀ hJperp with h | h | h | h
    · exact Or.inr h
    · exact Or.inl h
    · rw [h] at hJt₀
      exact absurd hJt₀ hnotK₃
    · rw [h] at hJt₀
      exact absurd hJt₀ hnotK₄
  have hR₁c : R₁ ≤ Subgroup.centralizer ({b * b'} : Set G) := hR₁.1.trans hKc'
  have hR₂c : R₂ ≤ Subgroup.centralizer ({b * b'} : Set G) := hR₂.1.trans hK'c'
  have hex₁ : IsSylow2In R₁ (Q3T8.Asc77.ExactLayer.exactCore (b * b') K) :=
    (Q3T8.Asc77.ExactLayer.isSylow2In_exactCore_iff hΩ hc2' hKΩ hKt.2).mpr ⟨hR₁, hR₁c⟩
  have hex₂ : IsSylow2In R₂ (Q3T8.Asc77.ExactLayer.exactCore (b * b') K') :=
    (Q3T8.Asc77.ExactLayer.isSylow2In_exactCore_iff hΩ hc2' hK'Ω hK't.2).mpr ⟨hR₂, hR₂c⟩
  have hu_comm : u * (b * b') = (b * b') * u := by
    have e1 : b * u = u * b := Subgroup.mem_centralizer_singleton_iff.mp (hK₃c hbK₃)
    have e2 : b' * u = u * b' := Subgroup.mem_centralizer_singleton_iff.mp (hK₄c hb'K₄)
    calc u * (b * b') = (u * b) * b' := by group
      _ = (b * u) * b' := by rw [e1]
      _ = b * (u * b') := by group
      _ = b * (b' * u) := by rw [e2]
      _ = (b * b') * u := by group
  have hL2 : Q3T8.Asc77.LayerOrthType Ω (b * b') 6 false := by
    have h := Q3T8.Asc77.T7J.layer_orth_six_weak_proved hΩ hBelow hbb2 hnc hKt hK't hJt hz hzK'
      hperp hperp' htJ hF.hzt hF.htz hex₁ hex₂ c12 (hex₁.1 hu₁R) (hex₂.1 hu₂R) hu₁Ω hu₂Ω
      hu_comm.symm
    rwa [hπ] at h
  
  have hKtw₃ : K ∈ twinSet Ω K₃ := by
    rw [twinSet_eq_of_mem_twinSet hz hs.hK₃]
    exact hKV
  have hK₄tw₃ : K₄ ∈ twinSet Ω K₃ := by
    rw [twinSet_eq_of_mem_twinSet hz hs.hK₃]
    exact hK₄
  have hD' : Q3T8.Asc77.Hyp22Setting Ω K₃ K₄ K z b b' u₁ :=
    Q3T8.Asc77.S22.hyp22Setting_of_sylows (hs.stand.of_mem hK₃Ω) hzK₃ hK₄tw₃ h43
      (Q3T8.Asc77.T7S22.perp_of_twin hs hs.hK₃) hKtw₃ hs.hK₃K.symm h41.symm hF.hR hF.hR' hR₁ hF.hRR'
      (fun x hx w hw => (cKK₃ w (hR₁.1 hw) x (hF.hR.1 hx)).symm)
      (fun x hx w hw => (cKK₄ w (hR₁.1 hw) x (hF.hR'.1 hx)).symm) hF.hbR hF.hb'R' hu₁R hF.hb4
      hF.hb'4 hs.hu₁.2
  have hαeq := Q3T8.Asc77.S22.alpha_eq_of_datum (Q3T8.Asc77.S22.c22_2S) hs hD'
      (Q3T8.Asc77.S22.Big.of_four hs hK₄ h41 h42 h43)
  have hα' : alphaOf (Subgroup.closure ({b * b', z} : Set G)) = ⊥ := hαeq.symm.trans hα
  
  have hKle : K ≤ Q3T8.Asc77.ExactLayer.exactLayer Ω (b * b') :=
      (Q3T8.Asc77.T7Z.exactLayer_eq_omegaGen Ω (b * b')) ▸ hle hKΦ
  have hzY' : z ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω (b * b') := hKle hz.mem
  have hJY : conjSub y K₃ ≤ Q3T8.Asc77.ExactLayer.exactLayer Ω (b * b') :=
    (Q3T8.Asc77.T7Z.exactLayer_eq_omegaGen Ω (b * b')) ▸ hle hJΦ
  have hJ'Y : conjSub y K₄ ≤ Q3T8.Asc77.ExactLayer.exactLayer Ω (b * b') :=
    (Q3T8.Asc77.T7Z.exactLayer_eq_omegaGen Ω (b * b')) ▸ hle hJ'Φ
  have hf1 : 1 ≤ 1 := le_refl 1
  have hK2 : Nat.card (GaloisField 3 2) = (3) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 3 1 hf1
  have hOc' : classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω (b * b')) = ⊥ := by
    refine Q3T8.Asc77.C22N.oddCore_layer_eq_bot_neg h22 hbb1 hα' hL2 hzY' hzK₃.sq ?_
    intro hall
    obtain ⟨W, hW⟩ := hP1
    have h1 : z = 1 := Q3T8.Asc77.C22G.UnitaryBlockStandardPair.eq_one_of_centralizes3 hW hzK₃.mem
        (fun w hw => (hall w (hJY hw)).symm)
    exact hzK₃.ne_one h1
  
  obtain ⟨P⟩ := Q3T8.Asc77.C22N.nonempty_psuLayer_of_layerOrth hOc' hL2
  obtain ⟨RK, hRK, hKR⟩ := P.fund K hKΦ
  obtain ⟨RK', hRK', hK'R⟩ := P.fund K' hK'Φ
  obtain ⟨RJ, hRJ, hJR⟩ := P.fund _ hJΦ
  have hu₁K : u₁ ∈ K := hs.hu₁.1
  have hu₂K' : u₂ ∈ K' := hs.hu₂.1
  have he : b * b' ∈ omegaGen (Q3T8.Asc77.ExactLayer.exactFamily Ω (b * b')) := by
    have h1 : u ∈ omegaGen (Q3T8.Asc77.ExactLayer.exactFamily Ω (b * b')) :=
      Subgroup.mul_mem _ (hle hKΦ hu₁K) (hle hK'Φ hu₂K')
    have h2 : b * b' * u ∈ omegaGen (Q3T8.Asc77.ExactLayer.exactFamily Ω (b * b')) := hle hJΦ
        htJ.mem
    have h3 : (b * b' * u) * u⁻¹ ∈ omegaGen (Q3T8.Asc77.ExactLayer.exactFamily Ω (b * b')) :=
      Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ h1)
    have e : (b * b' * u) * u⁻¹ = b * b' := by group
    rwa [e] at h3
  have hec : ∀ y' ∈ omegaGen (Q3T8.Asc77.ExactLayer.exactFamily Ω (b * b')), (b * b') * y' = y' *
      (b * b') := by
    intro y' hy'
    have hy'' : y' ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω (b * b') :=
        (Q3T8.Asc77.T7Z.exactLayer_eq_omegaGen Ω (b * b')) ▸ hy'
    exact (Subgroup.mem_centralizer_singleton_iff.mp
      (Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω (b * b') hy'')).symm
  have htab : b * b' * u = u₁ * u₂ * (b * b') := hu_comm.symm
  have htab' : b * b' * u = u₂ * u₁ * (b * b') := by
    rw [htab, hs.comm₁₂]
  obtain ⟨hKJ, hKJc⟩ := Q3T8.Asc77.C22P.not_commutes_of_involution_S hs (mem_twinSet_self hKΩ hz)
      hJΩ htJ
    hF.htz
  obtain ⟨hK'J, hK'Jc⟩ := Q3T8.Asc77.C22P.not_commutes_of_involution_S hs hs.hK' hJΩ htJ hF.htz
  obtain ⟨h1, h2⟩ := (Fact.out : Q3T8.Asc77.C22G.PsuLayerApi3).pair P hRK hRJ hKR hK'R hJR hz htJ
      hu₁K
    hu₂K' hu₁Ω cKK' he hec htab hKJ hKJc
  obtain ⟨h1', h2'⟩ := (Fact.out : Q3T8.Asc77.C22G.PsuLayerApi3).pair P hRK' hRJ hK'R hKR hJR hzK'
      htJ
    hu₂K' hu₁K hu₂Ω cKK'.symm he hec htab' hK'J hK'Jc
  refine ⟨h2, h2', hJ'Y, ?_, hOc'⟩
  obtain ⟨W₁, hW₁⟩ := h1
  have hgen := (Fact.out : Q3T8.Asc77.C22G.PsuLayerApi3).sup P hRK' hJR hKR hK'R h1'
    ⟨W₁, Generic.unitaryBlockStandardPair_symm hW₁⟩ cKK'
  rw [Q3T8.Asc77.T7Z.exactLayer_eq_omegaGen Ω (b * b')]
  exact hgen.symm
end Layer
end C22N
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.Timmesfeld (edgeD)
open scoped commutatorElement MatrixGroups
namespace C22N
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22N
set_option linter.unusedSectionVars false
section Chain
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem alpha_eq_bot_neg [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.C22G.PsuLayerApi3] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51z] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51u] [Fact Q3T7E.ThmEWithSylow3] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S16.M11NoInverted3] (hq3 : 3 % 4 = 3) (hs :
    Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃)
    (hW : ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W)
    (hG : (⨆ M ∈ twinSet Ω K, M) ⊔ rLayer Ω (u₁ * u₂) = ⊤) :
    alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) = ⊥ := by
  obtain ⟨K₄, hK₄, h41, h42, h43, -⟩ := Q3T8.Asc77.C22P.fourTwins_S hs hW
  have hbig : S22.Big Ω K := Q3T8.Asc77.S22.Big.of_four hs hK₄ h41 h42 h43
  have h2 := Q3T8.Asc77.S22.c22_2S G Ω K K' K₃ z u₁ u₂ u₃ hs hbig
  have hCz := Q3T8.Asc77.S22.centralizer_le_normalizer_alpha (Q3T8.Asc77.S22.c22_2S) hs hbig
  have hY := Q3T8.Asc77.C22G.normY_of_hyp22Setting_psu hq3 hs
  have hle : (⨆ M ∈ twinSet Ω K, M) ⊔ rLayer Ω (u₁ * u₂) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
    refine sup_le (iSup₂_le fun M hM m hm => ?_) hY
    apply hCz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (e189_commute_of_mem (isUniqueInvolution_of_mem_twinSet hs.hz hM) hm).symm
  rw [hG] at hle
  exact T7B.eq_bot_of_normalizer_eq_top h2.1 (top_le_iff.mp hle) (T7B.two_dvd_natCard hs.hz)

theorem chain_of_alpha_neg [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.OddCoreLayerNeg3] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.C22G.PsuLayerApi3] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51z] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51u] (hq3 : 3 % 4 = 3)
    (h22 : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) (hW : ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W)
    (hL : Q3T8.Asc77.LayerOrthType Ω (u₁ * u₂) 6 (piSign 3 1))
    (hG : (⨆ M ∈ twinSet Ω K, M) ⊔ rLayer Ω (u₁ * u₂) = ⊤)
    (hα : alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) = ⊥) :
    ∃ U : Fin 4 → Subgroup G, (∀ k, U k ∈ Ω) ∧
      (∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i → Commutes (U i) (U j)) ∧
      (∀ i j : Fin 4, edgeD 4 i j →
        ∃ W, Phan.UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W (U i) (U j)) ∧
      ⨆ k, U k = ⊤ ∧ ¬ 3 ∣ Nat.card (Subgroup.center ↥(U 0 ⊔ U 1 ⊔ U 2)) := by
  classical
  have hs : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃ := h22.setting
  have hπ : piSign 3 1 = false := by simp [piSign, hq3]
  rw [hπ] at hL
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  obtain ⟨K₄, hK₄, h41, h42, h43, hV⟩ := Q3T8.Asc77.C22P.fourTwins_S hs hW
  obtain ⟨R, R', b, b', y, hFd⟩ := (Q3T8.Asc77.C22P.frame_at hs hK₄ h41 h42 h43 hW).exists_data
  obtain ⟨hex, hP1, hK₄le, hgen1⟩ := Q3T8.Asc77.C22N.layer1_neg h22 hα hL hK₄ h41 h42 h43 hFd
  obtain ⟨hPK, hPK', hJ'le, hgen2, hOcY⟩ := Q3T8.Asc77.C22N.layer2_neg h22 hex hπ hα hK₄ h41 h42 h43
      hV hFd hP1
  have hKΩ : K ∈ Ω := hs.stand.mem
  have hz : IsUniqueInvolution K z := hs.hz
  have hKV : K ∈ twinSet Ω K := mem_twinSet_self hKΩ hz
  have cKK' : Commutes K K' := Q3T8.Asc77.C22P.commutes_of_twins hs.stand hz hKV hs.hK' hs.hne.symm
      hex
  have cKK₃ : Commutes K K₃ := Q3T8.Asc77.C22P.commutes_of_twins hs.stand hz hKV hs.hK₃
      hs.hK₃K.symm hex
  have cK'K₃ : Commutes K' K₃ := Q3T8.Asc77.C22P.commutes_of_twins hs.stand hz hs.hK' hs.hK₃
      hs.hK₃K'.symm hex
  have hJΩ : conjSub y K₃ ∈ Ω := hΩ.conjInvariant y K₃ hs.hK₃.1
  refine ⟨![K, conjSub y K₃, K', K₃], ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    fin_cases k
    · exact hKΩ
    · exact hJΩ
    · exact hs.hK'.1
    · exact hs.hK₃.1
  · intro i j hij hn1 hn2
    fin_cases i <;> fin_cases j <;> simp [edgeD] at hij hn1 hn2 ⊢
    · exact cKK'
    · exact cKK₃
    · exact cKK'.symm
    · exact cK'K₃
    · exact cKK₃.symm
    · exact cK'K₃.symm
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [edgeD] at hij ⊢
    · exact hPK
    · obtain ⟨W, hW⟩ := hPK'
      exact ⟨W, Generic.unitaryBlockStandardPair_symm hW⟩
    · obtain ⟨W, hW⟩ := hP1
      exact ⟨W, Generic.unitaryBlockStandardPair_symm hW⟩
  · have hH : ∀ k : Fin 4, ![K, conjSub y K₃, K', K₃] k ≤ ⨆ k, ![K, conjSub y K₃, K', K₃] k :=
      fun k => le_iSup (fun k => ![K, conjSub y K₃, K', K₃] k) k
    have hKH : K ≤ ⨆ k, ![K, conjSub y K₃, K', K₃] k := hH 0
    have hJH : conjSub y K₃ ≤ ⨆ k, ![K, conjSub y K₃, K', K₃] k := hH 1
    have hK'H : K' ≤ ⨆ k, ![K, conjSub y K₃, K', K₃] k := hH 2
    have hK₃H : K₃ ≤ ⨆ k, ![K, conjSub y K₃, K', K₃] k := hH 3
    have hY' : Q3T8.Asc77.ExactLayer.exactLayer Ω (b * b') ≤ ⨆ k, ![K, conjSub y K₃, K', K₃] k := by
      rw [hgen2]
      exact sup_le (sup_le hK'H hJH) hKH
    have hJ'H : conjSub y K₄ ≤ ⨆ k, ![K, conjSub y K₃, K', K₃] k := hJ'le.trans hY'
    have hY : Q3T8.Asc77.ExactLayer.exactLayer Ω (u₁ * u₂) ≤ ⨆ k, ![K, conjSub y K₃, K', K₃] k := by
      rw [hgen1]
      exact sup_le (sup_le hJ'H hK₃H) hJH
    have hK₄H : K₄ ≤ ⨆ k, ![K, conjSub y K₃, K', K₃] k := hK₄le.trans hY
    refine top_le_iff.mp ?_
    rw [← hG]
    refine sup_le (iSup₂_le fun M hM => ?_) ?_
    · rcases hV M hM with h | h | h | h <;> rw [h]
      · exact hKH
      · exact hK'H
      · exact hK₃H
      · exact hK₄H
    · exact (Q3T8.Asc77.rLayer_le_exactLayer hΩ hs.sq_12).trans hY
  · have hsup : ![K, conjSub y K₃, K', K₃] 0 ⊔ ![K, conjSub y K₃, K', K₃] 1 ⊔
        ![K, conjSub y K₃, K', K₃] 2 = Q3T8.Asc77.ExactLayer.exactLayer Ω (b * b') := by
      rw [hgen2]
      show K ⊔ conjSub y K₃ ⊔ K' = K' ⊔ conjSub y K₃ ⊔ K
      ac_rfl
    rw [hsup]
    exact Q3T8.Asc77.C22G.not_three_dvd_card_center_of_oddCore_eq_bot hOcY
end Chain
end C22N
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
set_option linter.unusedSectionVars false
section Final

theorem R31.c22_phanChainNeg_proved [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.C22G.PsuLayerApi3]
    [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51z] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51u] [Fact Q3T7E.ThmEWithSylow3] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S16.M11NoInverted3] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.OddCoreLayerNeg3] : Q3T8.Asc77.R31.C22_phanChainNeg := by
  intro hq3 G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h22 hW hLG
  have hs := h22.setting
  exact Q3T8.Asc77.C22N.chain_of_alpha_neg hq3 h22 hW hLG.1 hLG.2
    (Q3T8.Asc77.C22N.alpha_eq_bot_neg hq3 hs hW hLG.2)
end Final
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
