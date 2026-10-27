module

public import CFSG.ClassicalInvolution.Asc77.AscC22P4
public import CFSG.ClassicalInvolution.Asc77.AscC22P2
public import CFSG.ClassicalInvolution.Asc77.AscC22P3
public import CFSG.ClassicalInvolution.Asc77.AscT7S22Sigma

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped commutatorElement MatrixGroups

namespace C22P

set_option linter.unusedSectionVars false

section Basic

variable {G : Type} [Group G] [Finite G]

structure FrameData (Ω : Set (Subgroup G)) (K₃ K₄ : Subgroup G) (z c : G) (R R' : Subgroup G)
    (b b' y : G) : Prop where
  hR : IsSylow2In R K₃
  hR' : IsSylow2In R' K₄
  hRR' : Commutes R R'
  hRc : R ≤ Subgroup.centralizer ({c} : Set G)
  hR'c : R' ≤ Subgroup.centralizer ({c} : Set G)
  hbR : b ∈ R
  hb'R' : b' ∈ R'
  hb4 : orderOf b = 4
  hb'4 : orderOf b' = 4
  hbz : b * b = z
  hb'z : b' * b' = z
  hy : y ∈ exactLayer Ω c
  hyz : y * z * y⁻¹ = b * b' * c
  htz : b * b' * c ≠ z
  hzt : z * (b * b' * c) = (b * b' * c) * z

theorem FrameS.exists_data {Ω : Set (Subgroup G)} {K₃ K₄ : Subgroup G} {z c : G}
    (h : FrameS Ω K₃ K₄ z c) :
    ∃ (R R' : Subgroup G) (b b' y : G), FrameData Ω K₃ K₄ z c R R' b b' y := by
  obtain ⟨R, R', b, b', y, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨R, R', b, b', y, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩⟩

omit [Finite G] in
theorem conjSub_le_centralizer_of_mem {c y : G} (hy : y ∈ Subgroup.centralizer ({c} : Set G))
    {L : Subgroup G} (hL : L ≤ Subgroup.centralizer ({c} : Set G)) :
    conjSub y L ≤ Subgroup.centralizer ({c} : Set G) := by
  have h := conjSub_le_centralizer_conj y hL
  have hyc : y * c * y⁻¹ = c := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hy
    calc y * c * y⁻¹ = (c * y) * y⁻¹ := by rw [← this]
      _ = c := by group
  rwa [hyc] at h

end Basic

section Layer

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ K₄ : Subgroup G} {z u₁ u₂ u₃ : G}


theorem not_commutes_of_involution_S (hs : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃)
    {M L : Subgroup G} {t : G} (hM : M ∈ twinSet Ω K) (hLΩ : L ∈ Ω)
    (htL : IsUniqueInvolution L t) (htz : t ≠ z) : M ≠ L ∧ ¬ Commutes M L := by
  have hzM : IsUniqueInvolution M z := isUniqueInvolution_of_mem_twinSet hs.hz hM
  have hne : M ≠ L := by
    rintro rfl
    exact htz (htL.eq hzM)
  refine ⟨hne, fun h => ?_⟩
  have hmem : L ∈ omegaNbr Ω M := MuTab.mem_omegaNbr_of_commutes hLΩ hne.symm h
  have hperp : L ∈ KPerp Ω M := Or.inr hmem
  rw [T7S22.perp_of_twin hs hM, twinSet_eq_of_mem_twinSet hs.hz hM] at hperp
  exact htz (htL.eq (isUniqueInvolution_of_mem_twinSet hs.hz hperp))

theorem layer1 (hodd : T7Z.OddCenterClassical) (hs : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃)
    (hα : alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) = ⊥)
    (hL : LayerOrthType p f Ω (u₁ * u₂) 6 true) (hK₄ : K₄ ∈ twinSet Ω K) (h41 : K₄ ≠ K)
    (h42 : K₄ ≠ K') (h43 : K₄ ≠ K₃) {R R' : Subgroup G} {b b' y : G}
    (hF : FrameData Ω K₃ K₄ z (u₁ * u₂) R R' b b' y) :
    ExactMembers Ω ∧ (∃ W, LinearBlockStandardPair (GaloisField p f) W K₃ (conjSub y K₃)) ∧
      K₄ ≤ exactLayer Ω (u₁ * u₂) ∧ exactLayer Ω (u₁ * u₂) = conjSub y K₄ ⊔ K₃ ⊔ conjSub y K₃ := by
  classical
  have hp2 : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hK₃Ω : K₃ ∈ Ω := hs.hK₃.1
  have hK₄Ω : K₄ ∈ Ω := hK₄.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hzK' : IsUniqueInvolution K' z := hs.hzK'
  have hzK₃ : IsUniqueInvolution K₃ z := hs.hzK₃
  have hzK₄ : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet hz hK₄
  have hcls : ∀ M ∈ Ω, ∃ z', IsClassicalMember p f M z' := hΩ.classical
  set u : G := u₁ * u₂ with hu
  have hu2 : u * u = 1 := hs.sq_12
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) := isPGroup_zpowers_of_sq_eq_one hu2
  have hu1 : u ≠ 1 :=
    (T7S22.mul_ne_one_of_twins hΩ hK hK' hs.hne.symm hz hs.hu₁.1 hs.hu₂.1 hs.hu₂.2).1
  have hu₁K₃ : u₁ ∈ trivialOnQuot K₃ :=
    T7J.twin_le_trivialOnQuot hΩ hK hK₃Ω hs.hK₃K.symm hz hzK₃ hs.hu₁.1
  have hu₂K₃ : u₂ ∈ trivialOnQuot K₃ :=
    T7J.twin_le_trivialOnQuot hΩ hK' hK₃Ω hs.hK₃K'.symm hzK' hzK₃ hs.hu₂.1
  have hK₃t : K₃ ∈ tqMembers Ω u := ⟨hK₃Ω, Subgroup.mul_mem _ hu₁K₃ hu₂K₃⟩
  have hex₃ : IsSylow2In R (exactCore u K₃) :=
    (isSylow2In_exactCore_iff hΩ hc2 hK₃Ω hK₃t.2).mpr ⟨hF.hR, hF.hRc⟩
  have hzY : z ∈ exactLayer Ω u := by
    have hb : b ∈ exactCore u K₃ := hex₃.1 hF.hbR
    have : z ∈ exactCore u K₃ := hF.hbz ▸ (exactCore u K₃).mul_mem hb hb
    exact exactCore_le_exactLayer hK₃t this
  have hOc : classicalInvolutionOddCore ↥(exactLayer Ω u) = ⊥ := by
    refine oddCore_layer_eq_bot hodd hp2 hq hΩ.conjInvariant hu1 hα hL hzY hzK₃.sq ?_
    intro hall
    have h1 := hall y hF.hy
    apply hF.htz
    rw [← hF.hyz, h1]
    group
  have hex : ExactMembers Ω := exactMembers_S hs hα hOc hL
  have hKV : K ∈ twinSet Ω K := mem_twinSet_self hK hz
  have cKK₃ : Commutes K K₃ := commutes_of_twins hs.stand hz hKV hs.hK₃ hs.hK₃K.symm hex
  have cKK₄ : Commutes K K₄ := commutes_of_twins hs.stand hz hKV hK₄ h41.symm hex
  have cK'K₃ : Commutes K' K₃ := commutes_of_twins hs.stand hz hs.hK' hs.hK₃ hs.hK₃K'.symm hex
  have cK'K₄ : Commutes K' K₄ := commutes_of_twins hs.stand hz hs.hK' hK₄ h42.symm hex
  have cK₃K₄ : Commutes K₃ K₄ := commutes_of_twins hs.stand hz hs.hK₃ hK₄ h43.symm hex
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
  have hyc : y ∈ Subgroup.centralizer ({u} : Set G) := exactLayer_le_centralizer Ω u hF.hy
  have hJc : conjSub y K₃ ≤ Subgroup.centralizer ({u} : Set G) :=
    conjSub_le_centralizer_of_mem hyc hK₃c
  have hJ'c : conjSub y K₄ ≤ Subgroup.centralizer ({u} : Set G) :=
    conjSub_le_centralizer_of_mem hyc hK₄c
  have hJΩ : conjSub y K₃ ∈ Ω := hΩ.conjInvariant y K₃ hK₃Ω
  have hJ'Ω : conjSub y K₄ ∈ Ω := hΩ.conjInvariant y K₄ hK₄Ω
  have hK₃Φ : K₃ ∈ exactFamily Ω u := centMembers_subset_exactFamily hcls ⟨hK₃Ω, hK₃c⟩
  have hK₄Φ : K₄ ∈ exactFamily Ω u := centMembers_subset_exactFamily hcls ⟨hK₄Ω, hK₄c⟩
  have hJΦ : conjSub y K₃ ∈ exactFamily Ω u :=
    centMembers_subset_exactFamily hcls ⟨hJΩ, hJc⟩
  have hJ'Φ : conjSub y K₄ ∈ exactFamily Ω u :=
    centMembers_subset_exactFamily hcls ⟨hJ'Ω, hJ'c⟩
  have htJ : IsUniqueInvolution (conjSub y K₃) (b * b' * u) := hF.hyz ▸ hzK₃.conj y
  have htJ' : IsUniqueInvolution (conjSub y K₄) (b * b' * u) := hF.hyz ▸ hzK₄.conj y
  obtain ⟨hKJ, hKJc⟩ := not_commutes_of_involution_S hs hs.hK₃ hJΩ htJ hF.htz
  obtain ⟨hKJ', hKJc'⟩ := not_commutes_of_involution_S hs hs.hK₃ hJ'Ω htJ' hF.htz
  have hexeq := nonempty_equiv_sl2_of_exact hs.stand hex
  obtain ⟨P⟩ := nonempty_pslLayer_of_layerOrth hOc hL
  obtain ⟨RK, hRK, hKR⟩ := P.fund K₃ hK₃Φ
  obtain ⟨RK', hRK', hKR'⟩ := P.fund K₄ hK₄Φ
  obtain ⟨RJ, hRJ, hJR⟩ := P.fund _ hJΦ
  obtain ⟨RJ', hRJ', hJ'R⟩ := P.fund _ hJ'Φ
  have hbK₃ : b ∈ K₃ := hF.hR.1 hF.hbR
  have hb'K₄ : b' ∈ K₄ := hF.hR'.1 hF.hb'R'
  have hle : ∀ {M : Subgroup G}, M ∈ exactFamily Ω u → M ≤ omegaGen (exactFamily Ω u) :=
    fun hM => le_omegaGen hM
  have he : u ∈ omegaGen (exactFamily Ω u) := by
    have h1 : b * b' ∈ omegaGen (exactFamily Ω u) :=
      Subgroup.mul_mem _ (hle hK₃Φ hbK₃) (hle hK₄Φ hb'K₄)
    have h2 : b * b' * u ∈ omegaGen (exactFamily Ω u) := hle hJΦ htJ.mem
    have h3 : (b * b')⁻¹ * (b * b' * u) ∈ omegaGen (exactFamily Ω u) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) h2
    have e : (b * b')⁻¹ * (b * b' * u) = u := by group
    rwa [e] at h3
  have hec : ∀ y' ∈ omegaGen (exactFamily Ω u), u * y' = y' * u := by
    intro y' hy'
    have hy'' : y' ∈ exactLayer Ω u := (T7Z.exactLayer_eq_omegaGen Ω u) ▸ hy'
    exact (Subgroup.mem_centralizer_singleton_iff.mp (exactLayer_le_centralizer Ω u hy'')).symm
  have htab : b * b' * u = b * b' * u := rfl
  obtain ⟨h1, h2⟩ := pair_of_member' hp2 hq P hRK hRJ hKR hKR' hJR (hexeq K₃ hK₃Ω)
    (hexeq _ hJΩ) hzK₃ htJ hbK₃ hb'K₄ hF.hbz cK₃K₄ he hec htab hKJ hKJc
  obtain ⟨h1', -⟩ := pair_of_member' hp2 hq P hRK hRJ' hKR hKR' hJ'R (hexeq K₃ hK₃Ω)
    (hexeq _ hJ'Ω) hzK₃ htJ' hbK₃ hb'K₄ hF.hbz cK₃K₄ he hec htab hKJ' hKJc'
  have hK₄le : K₄ ≤ exactLayer Ω u := (T7Z.exactLayer_eq_omegaGen Ω u) ▸ hle hK₄Φ
  refine ⟨hex, h2, hK₄le, ?_⟩
  obtain ⟨W₁, hW₁⟩ := h1'
  have hgen := T7Z.PSLLayer.sup_eq_omegaGen hp2 hq P hRJ' hKR hJR hJ'R
    ⟨W₁, linearBlockStandardPair_symm hW₁⟩ h1 (cK₃K₄.conjSub y)
  rw [T7Z.exactLayer_eq_omegaGen Ω u]
  exact hgen.symm

end Layer

end C22P

end CFSG.ClassicalInvolution.Asc77
