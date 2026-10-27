module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415PM
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415PU
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma36Derive
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs56X
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEnd413
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415PE

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd

namespace L415

theorem fixedPoints_conjNormal {G : Type} [Group G] {M : Subgroup G} [M.Normal] (b : G) :
    fixedPoints (MulAut.conjNormal b : MulAut ↥M) = (M ⊓ centralizer {b}).subgroupOf M := by
  ext x
  rw [mem_fixedPoints, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 := congrArg Subtype.val h
    rw [MulAut.conjNormal_apply] at h1
    refine ⟨x.2, ?_⟩
    calc (x : G) * b = b * x * b⁻¹ * b := by rw [h1]
      _ = b * x := by group
  · rintro ⟨-, h⟩
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    calc b * (x : G) * b⁻¹ = x * b * b⁻¹ := by rw [h]
      _ = x := by group

theorem isTwoComponentIn_fixedPoints_iff {G : Type} [Group G] [Finite G] {M : Subgroup G}
    [M.Normal] (b : G) {K : Subgroup ↥M}
    (hK : K ≤ fixedPoints (MulAut.conjNormal b : MulAut ↥M)) :
    IsTwoComponentIn K (fixedPoints (MulAut.conjNormal b : MulAut ↥M)) ↔
      IsPComponent 2 ((K.map M.subtype).subgroupOf (M ⊓ centralizer {b})) := by
  rw [isTwoComponentIn_iff hK, fixedPoints_conjNormal,
    ← UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff'
      (inf_le_left : M ⊓ centralizer {b} ≤ M) 2 Nat.prime_two, subgroupOf_map_subtype_eq]

theorem orderOf_conjNormal {G : Type} [Group G] [Finite G] {M : Subgroup G} [M.Normal]
    (hq : IsQuasisimple ↥M) {b : G} (hb : b * b = 1) {K : Subgroup G} (hKM : K < M)
    (hKpc : IsPComponent 2 (K.subgroupOf (M ⊓ centralizer {b})))
    (hKab : ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x) :
    orderOf (MulAut.conjNormal b : MulAut ↥M) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [sq, ← map_mul, hb, map_one]
  · intro h1
    have hMC : M ⊓ centralizer {b} = M := by
      refine inf_eq_left.mpr fun x hx => ?_
      have h2 := congrArg Subtype.val (DFunLike.congr_fun h1 ⟨x, hx⟩)
      rw [MulAut.conjNormal_apply, MulAut.one_apply] at h2
      have h3 : b * x * b⁻¹ = x := h2
      rw [mem_centralizer_singleton_iff]
      calc x * b = b * x * b⁻¹ * b := by rw [h3]
        _ = b * x := by group
    rw [hMC] at hKpc
    have hsn : (K.subgroupOf M).IsSubnormal := hKpc.choose_spec.2.1
    obtain ⟨x, hx, y, hy, hxy⟩ := hKab
    rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hq hsn with h | h
    · refine hKM.not_ge fun m hm => ?_
      have : (⟨m, hm⟩ : ↥M) ∈ K.subgroupOf M := by rw [h]; trivial
      exact this
    · apply hxy
      have h3 : (⟨x, hKM.le hx⟩ : ↥M) ∈ center ↥M := h (show (⟨x, hKM.le hx⟩ : ↥M) ∈
        K.subgroupOf M from hx)
      exact (congrArg Subtype.val (mem_center_iff.mp h3 ⟨y, hKM.le hy⟩)).symm

theorem conjNormal_mem_innAut {G : Type} [Group G] {M : Subgroup G} [M.Normal]
    (hO : pPrimeCore 2 ↥M = ⊥) {b : G} (hb : b ∈ GrSLit.withKernel M) :
    (MulAut.conjNormal b : MulAut ↥M) ∈ innAut ↥M := by
  have hb' : b ∈ ((M ⊔ coreActionKernel M : Subgroup G) : Set G) := hb
  rw [Subgroup.normal_mul, Set.mem_mul] at hb'
  obtain ⟨m, hm, c, hc, rfl⟩ := hb'
  have hc' := (mem_coreActionKernel.mp hc).2
  rw [hO, Subgroup.map_bot] at hc'
  have hcm : ∀ x ∈ M, c * x * c⁻¹ = x := by
    intro x hx
    have h1 := hc' x hx
    rw [mem_bot] at h1
    have h2 : c⁻¹ * x * c = x := by
      calc c⁻¹ * x * c = x * (x⁻¹ * c⁻¹ * x * c) := by group
        _ = x := by rw [h1, mul_one]
    calc c * x * c⁻¹ = c * (c⁻¹ * x * c) * c⁻¹ := by rw [h2]
      _ = x := by group
  refine MonoidHom.mem_range.mpr ⟨⟨m, hm⟩, MulEquiv.ext fun x => Subtype.ext ?_⟩
  change m * (x : G) * m⁻¹ = (MulAut.conjNormal (m * c) x : G)
  rw [MulAut.conjNormal_apply,
    show m * c * (x : G) * (m * c)⁻¹ = m * (c * x * c⁻¹) * m⁻¹ by group, hcm x x.2]

theorem twoPart_top_le {G : Type} [Group G] [Finite G] {M V : Subgroup G} [M.Normal] {b : G}
    (hsyl : IsSylowOf 2 (V ⊓ M) M)
    (hcard : Nat.card ↥(V ⊓ M) ≤ 2 * Nat.card ↥(V ⊓ M ⊓ centralizer {b})) :
    twoPart (⊤ : Subgroup ↥M) ≤
      2 * twoPart (fixedPoints (MulAut.conjNormal b : MulAut ↥M)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : twoPart (⊤ : Subgroup ↥M) = Nat.card ↥(V ⊓ M) := by
    rw [hsyl.card_eq]
    change 2 ^ (Nat.card ↥(⊤ : Subgroup ↥M)).factorization 2 = _
    rw [Subgroup.card_top]
  have hle : V ⊓ M ⊓ centralizer {b} ≤ M := inf_le_left.trans inf_le_right
  have hP : (V ⊓ M ⊓ centralizer {b}).subgroupOf M ≤
      fixedPoints (MulAut.conjNormal b : MulAut ↥M) := by
    rw [fixedPoints_conjNormal]
    intro x hx
    exact ⟨x.2, (mem_inf.mp hx).2⟩
  have hP2 : IsPGroup 2 ↥((V ⊓ M ⊓ centralizer {b}).subgroupOf M) :=
    (hsyl.isPGroup.to_le inf_le_left).of_equiv (subgroupOfEquivOfLe hle).symm
  have h2 := card_le_twoPart hP2 hP
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv] at h2
  rw [h1]
  exact hcard.trans (Nat.mul_le_mul_left _ h2)

end L415

variable {X : Type} [Group X] [Finite X]
  {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X} {w z : X} {V : Subgroup X}
  {i j : ℕ} {z₁ τ α : X} {K₂ W 𝒱 : Subgroup X}

namespace Data415B

variable (hD : Data415B t L p f S w z V i j z₁ τ α K₂ W 𝒱)
include hD

theorem isSimpleGroup_layer [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X) (hcat : ¬ Blueprint.Catalog X)
    (h39 : Harris82TheoremOneKProper)
    (h36 : Harris81Lemma36NonsimpleInput) (hJ2 : TwoJ2OuterInvolutionIndexFact)
    (hHS : TwoHSInnerInvolutionIndexFact)
    (hL34 : GrSLit.L34OuterInvolutionCentralizerFact)
    (hnβ : ∀ g : X, g * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g⁻¹ ≠ z₁)
    {M : Subgroup (MBar z₁)} (hM : IsComponent M) (hMeq : layer (MBar z₁) = M)
    (hF : IsOfType (HarrisF p) ↥M)
    (hZ : center ↥M ≠ ⊥ → (QuotientGroup.mk ⟨z₁, mem_centralizer_singleton_iff.mpr rfl⟩ :
      MBar z₁) ∈ (center ↥M).map M.subtype)
    (hlt : barOf (centralizer {z₁}) K₂ < M)
    (hKpc : IsPComponent 2 ((barOf (centralizer {z₁}) K₂).subgroupOf (M ⊓ centralizer
      {(QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j, hD.beta_mem_F⟩ : MBar z₁)})))
    (hsyl : IsSylowOf 2 (barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ⊓ M) M)
    (hcard : Nat.card ↥(barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ⊓ M) ≤
      (barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁} ⊓
        centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})).relIndex
        (barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁})) *
      Nat.card ↥(barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ⊓ M ⊓
        centralizer {(QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j,
          hD.beta_mem_F⟩ : MBar z₁)})) :
    IsSimpleGroup ↥M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hMeq
  have hMn : (layer (MBar z₁)).Normal := by
    have := LocalCores.layer_characteristic (G := MBar z₁)
    infer_instance
  by_contra hns
  have hq : IsQuasisimple ↥(layer (MBar z₁)) := hM.1
  obtain ⟨hO, hZs⟩ := oddCore_fusionZStar_component hM
  have hZne : center ↥(layer (MBar z₁)) ≠ ⊥ := by
    intro hbot
    apply hns
    have : IsSimpleGroup (↥(layer (MBar z₁)) ⧸ center ↥(layer (MBar z₁))) := hq.2.1
    exact ((QuotientGroup.quotientMulEquivOfEq hbot).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  have hz₁E : betaBar z₁ ∈ layer (MBar z₁) := by
    obtain ⟨c, -, hc⟩ := Subgroup.mem_map.mp (hZ hZne)
    change (QuotientGroup.mk ⟨z₁, mem_centralizer_singleton_iff.mpr rfl⟩ : MBar z₁) ∈ _
    rw [← hc]
    exact c.2
  have hnM := hD.not_isMType hnab hK hcat h39 hq hz₁E
  obtain ⟨hKC, -, -⟩ := L415.isPComponent_barOf hD.beta_mem_F hD.orderOf_beta
    hD.fd.isTwoComponentIn_K₂
  have hτ := L415.orderOf_conjNormal hq hD.betaF_mul_betaF hlt hKpc
    (by
      obtain ⟨k, hk, hkz⟩ := hD.exists_not_comm_z₂F
      exact ⟨k, hk, _, hD.z₂F_mem, hkz⟩)
  have hKM := hlt.le
  have hKfix : (barOf (centralizer {z₁}) K₂).subgroupOf (layer (MBar z₁)) ≤
      fixedPoints (MulAut.conjNormal (QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j,
        hD.beta_mem_F⟩ : MBar z₁) : MulAut ↥(layer (MBar z₁))) := by
    rw [L415.fixedPoints_conjNormal]
    intro x hx
    exact ⟨x.2, hKC hx⟩
  have hKc : IsTwoComponentIn ((barOf (centralizer {z₁}) K₂).subgroupOf (layer (MBar z₁)))
      (fixedPoints (MulAut.conjNormal (QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j,
        hD.beta_mem_F⟩ : MBar z₁) : MulAut ↥(layer (MBar z₁)))) := by
    rw [L415.isTwoComponentIn_fixedPoints_iff _ hKfix, subgroupOf_map_subtype,
      inf_of_le_left hKM]
    exact hKpc
  have huniq : ∀ K' : Subgroup ↥(layer (MBar z₁)), IsTwoComponentIn K'
      (fixedPoints (MulAut.conjNormal (QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j,
        hD.beta_mem_F⟩ : MBar z₁) : MulAut ↥(layer (MBar z₁)))) →
      K' = (barOf (centralizer {z₁}) K₂).subgroupOf (layer (MBar z₁)) := by
    intro K' hK'
    have h1 := (L415.isTwoComponentIn_fixedPoints_iff _ hK'.1).mp hK'
    have hle : K'.map (layer (MBar z₁)).subtype ≤ layer (MBar z₁) ⊓ centralizer
        {(QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j, hD.beta_mem_F⟩ : MBar z₁)} := by
      rintro _ ⟨x, hx, rfl⟩
      have h2 := hK'.1 hx
      rw [L415.fixedPoints_conjNormal] at h2
      exact h2
    have h3 := UnbalancedCorr.isPComponent_subgroupOf_of_isSubnormal hle inf_le_right
      (by rw [inf_subgroupOf_right]; exact Subgroup.Normal.isSubnormal inferInstance) h1
    have h4 := (Subgroup.subgroupOf_inj).mp (hD.pComponent_betaF_eq _ h3)
    rw [inf_of_le_left (hle.trans inf_le_right), inf_of_le_left hKC] at h4
    rw [← subgroupOf_map_subtype_eq K', h4]
  have hKL : Blueprint.LieModel
      (↥((barOf (centralizer {z₁}) K₂).subgroupOf (layer (MBar z₁))) ⧸
        pPrimeCore 2 ↥((barOf (centralizer {z₁}) K₂).subgroupOf (layer (MBar z₁))))
      .PSL 2 p (f / 2) := by
    obtain ⟨e⟩ := hD.nonempty_K₂F_equiv
    exact lieModel_psl2_of_mulEquiv ((UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (subgroupOfEquivOfLe hKM)).trans e) (hD.hs.lieModel_KBar hD.h412)
  have hrel := hD.relIndex_W₀F_le_two hnβ
  have hbound := L415.twoPart_top_le hsyl (hcard.trans (Nat.mul_le_mul_right _ hrel))
  have hpos : 0 < twoPart (fixedPoints (MulAut.conjNormal (QuotientGroup.mk
      ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j, hD.beta_mem_F⟩ : MBar z₁) :
        MulAut ↥(layer (MBar z₁)))) := pow_pos two_pos _
  rcases h36 ↥(layer (MBar z₁)) hq hO p hD.hs.prime_p hD.hs.p_ne_two
      (L36.isOfType_chev_of_harrisF hF) _ hτ (f / 2) hD.hs.one_le_half hD.hs.sixteen_dvd _ hKc
      huniq hKL hns hnM with
    ⟨hJ2', hZ2, hout⟩ | ⟨hHS', hZ2, hFst, hin⟩ | ⟨hL34', -, hout⟩ | ⟨k, hk, hL⟩
  ·
    have := hJ2 _ hq hJ2' hZ2 _ hτ hout
    omega
  ·
    have := hHS _ hq hHS' hZ2 _ hτ hin hFst
    omega
  ·
    have hperf : ⁅layer (MBar z₁), layer (MBar z₁)⁆ = layer (MBar z₁) := by
      have h' := congrArg (map (layer (MBar z₁)).subtype) (Group.isPerfect_def.1 hq.1)
      rwa [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at h'
    have hIsL : GrSLit.IsL34Type (↥(layer (MBar z₁)) ⧸ Open.fusionZStar ↥(layer (MBar z₁))) :=
      GSThmB.OddQuot.lieModel_of_equiv (QuotientGroup.quotientMulEquivOfEq hZs.symm) hL34'
    have hVN : barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ≤
        normalizer ((layer (MBar z₁) : Subgroup (MBar z₁)) : Set (MBar z₁)) := by
      rw [normalizer_eq_top]
      exact le_top
    have h4 : 4 * Nat.card ↥(barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ⊓
        centralizer {(QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j,
          hD.beta_mem_F⟩ : MBar z₁)}) ≤
        Nat.card ↥(barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁})) :=
      hL34 (MBar z₁) (layer (MBar z₁)) (barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}))
      (barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ⊓ layer (MBar z₁))
      (QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j, hD.beta_mem_F⟩) hperf hIsL
      ⟨hsyl.le, hsyl.exists_sylow_eq_subgroupOf⟩ inf_le_left hD.isSylowOf_V₀F.isPGroup hVN
      (mk_mem_barOf hD.beta_mem_F hD.beta_mem_V₀) hD.betaF_mul_betaF
      (fun h => hout (L415.conjNormal_mem_innAut hO h))
    have h5 : Nat.card ↥(barOf (centralizer {z₁})
        (𝒱 ⊓ centralizer {z₁} ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})) ≤
        Nat.card ↥(barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ⊓
          centralizer {(QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j,
            hD.beta_mem_F⟩ : MBar z₁)}) :=
      Subgroup.card_le_of_le (le_inf W₀F_le_V₀F hD.W₀F_le_centralizer)
    have h6 := Subgroup.relIndex_mul_card (barOf (centralizer {z₁})
      (𝒱 ⊓ centralizer {z₁} ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}))
      (barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}))
    rw [inf_of_le_left W₀F_le_V₀F] at h6
    have h7 : 0 < Nat.card ↥(barOf (centralizer {z₁})
        (𝒱 ⊓ centralizer {z₁} ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})) :=
      Nat.card_pos
    have h8 : Nat.card ↥(barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁})) ≤
        2 * Nat.card ↥(barOf (centralizer {z₁})
          (𝒱 ⊓ centralizer {z₁} ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})) := by
      rw [← h6]
      exact Nat.mul_le_mul_right _ hrel
    omega
  ·
    obtain ⟨hnL, hnU⟩ := hD.not_lieModel_L4U4 hnβ hM k
      (by have := hD.hs.one_le_half; omega)
    rcases hL with h1 | h1
    · exact hnL h1
    · exact hnU h1

end Data415B

end CFSG.ComponentClassification.HarrisLit
