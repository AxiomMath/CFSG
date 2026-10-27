module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf5Trans
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSecNoExit
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Path
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf4Layer
public import CFSG.ClassicalInvolution.SmallCases.A7T22ZStar

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)

section Odd

variable {H : Type} [Group H] [Finite H]

theorem le_of_isPGroup_of_le_sup_odd {M N : Subgroup H} [M.Normal] [N.Normal]
    (hN : Odd (Nat.card N)) {A : Subgroup H} (hA : IsPGroup 2 A) (h : A ≤ M ⊔ N) : A ≤ M := by
  have hmap : A.map (QuotientGroup.mk' M) ≤ N.map (QuotientGroup.mk' M) := by
    have h1 := Subgroup.map_mono (f := QuotientGroup.mk' M) h
    have hM : M.map (QuotientGroup.mk' M) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      simpa using hx
    rwa [Subgroup.map_sup, hM, bot_sup_eq] at h1
  have hp : IsPGroup 2 ↥(A.map (QuotientGroup.mk' M)) := hA.map _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hd : Nat.card ↥(A.map (QuotientGroup.mk' M)) ∣ Nat.card N :=
    (Subgroup.card_dvd_of_le hmap).trans (Subgroup.card_map_dvd N _)
  have hk0 : k = 0 := by
    by_contra hk0
    have h2 : 2 ∣ Nat.card N :=
      (dvd_pow_self 2 hk0).trans (hk ▸ hd)
    exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h2)
  have hbot : A.map (QuotientGroup.mk' M) = ⊥ := by
    rw [← Subgroup.card_eq_one, hk, hk0, pow_zero]
  intro a ha
  have : QuotientGroup.mk' M a ∈ A.map (QuotientGroup.mk' M) := Subgroup.mem_map_of_mem _ ha
  rw [hbot, Subgroup.mem_bot] at this
  simpa using this

end Odd

section UniqueInv

variable {G : Type} [Group G] [Finite G]

theorem isUniqueInvolution_of_isSylow2In {K P : Subgroup G} {z : G} (hK : IsUniqueInvolution K z)
    (hP : IsSylow2In P K) (h2 : 2 ≤ Nat.card P) : IsUniqueInvolution P z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.2.1.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    omega
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 (hk ▸ dvd_pow_self 2 hk0)
  have hu' : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
  have hu2 : (u : G) * u = 1 := by
    rw [← sq]; exact orderOf_dvd_iff_pow_eq_one.mp hu'.dvd
  have hu1 : (u : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hu'
    omega
  have huz : (u : G) = z := (hK.unique _ (hP.1 u.2) hu2).resolve_left hu1
  exact ⟨huz ▸ u.2, hK.ne_one, hK.sq, fun y hy hy2 => hK.unique y (hP.1 hy) hy2⟩

end UniqueInv

section Layer





variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

variable (Ω c) in
@[expose] noncomputable def secImgR (R : Subgroup G) :
    Subgroup (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) :=
  ((R.subgroupOf (Subgroup.centralizer ({c} : Set G))).subgroupOf (coreHull Ω c)).map
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c)))

theorem map_map_subtype_secImgR {R : Subgroup G} (hRc : R ≤ Subgroup.centralizer ({c} : Set G))
    (hRH : R.subgroupOf (Subgroup.centralizer ({c} : Set G)) ≤ coreHull Ω c) :
    (((R.subgroupOf (Subgroup.centralizer ({c} : Set G))).subgroupOf (coreHull Ω c)).map
      (coreHull Ω c).subtype).map (Subgroup.centralizer ({c} : Set G)).subtype = R := by
  rw [Subgroup.map_subgroupOf_eq_of_le hRH, Subgroup.map_subgroupOf_eq_of_le hRc]

theorem rLayer_le_iSup_of_secImgR (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)) {R₃ : Subgroup G}
    (h : ∀ M ∈ TwinDisc.secFam Ω c, M ≤ ⨆ x : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c),
      conjSub x (secImgR Ω c R₃)) :
    rLayer Ω c ≤ ⨆ x : ↥(rLayer Ω c), conjSub (x : G) R₃ := by
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set H := coreHull Ω c with hH
  set N := classicalInvolutionOddCore ↥H with hNdef
  have hN : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card ↥H
  set P₃ : Subgroup ↥H := (R₃.subgroupOf C).subgroupOf H with hP₃
  set M₀ : Subgroup ↥H := ⨆ g : ↥H, conjSub g P₃ with hM₀
  have hM₀n : ∀ g : ↥H, conjSub g M₀ ≤ M₀ := by
    intro g
    rw [hM₀, conjSub, Subgroup.map_iSup]
    refine iSup_le fun k => ?_
    rw [← conjSub, ← conjSub_mul]
    exact le_iSup (fun g => conjSub g P₃) (g * k)
  have : M₀.Normal := ⟨fun a ha g => by
    have := hM₀n g (conj_mem_conjSub ha)
    exact this⟩
  have hS : (⨆ x : ↥H ⧸ N, conjSub x (secImgR Ω c R₃)) ≤ M₀.map (QuotientGroup.mk' N) := by
    refine iSup_le fun x => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    have e : conjSub (QuotientGroup.mk' N g) (secImgR Ω c R₃) =
        (conjSub g P₃).map (QuotientGroup.mk' N) := (AscQuot.map_conjSub _ g P₃).symm
    rw [e]
    exact Subgroup.map_mono (le_iSup (fun g => conjSub g P₃) g)
  set Pn : Subgroup G := ⨆ x : ↥(rLayer Ω c), conjSub (x : G) R₃ with hPn
  have hM₀Pn : ∀ y : ↥H, (((y : ↥C)) : G) ∈ Pn → True := fun _ _ => trivial
  have hM₀le : M₀ ≤ Pn.comap (C.subtype.comp H.subtype) := by
    refine iSup_le fun g => ?_
    intro x hx
    have hx' : g⁻¹ * x * g ∈ P₃ := mem_conjSub_iff.mp hx
    have hx'' : (g⁻¹ * x * g : ↥H) ∈ P₃ := hx'
    have h3 : ((((g⁻¹ * x * g : ↥H) : ↥C)) : G) ∈ R₃ :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hx'')
    have hg : (((g : ↥C)) : G) ∈ rLayer Ω c :=
      coreHull_map_le_rLayer hΩ hc2 ⟨((g : ↥C)), g.2, rfl⟩
    have h4 : (((x : ↥C)) : G) ∈ conjSub ((((g : ↥C)) : G)) R₃ := by
      rw [mem_conjSub_iff]
      exact h3
    exact le_iSup (fun y : ↥(rLayer Ω c) => conjSub (y : G) R₃) ⟨_, hg⟩ h4
  unfold rLayer
  refine iSup₂_le fun R' hR' => iSup_le fun hRc => ?_
  obtain ⟨J, hJΩ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR'
  have hJ : J ∈ tqMembers3 Ω c :=
    ⟨hJΩ, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJΩ ⟨R', hRJ, hRc⟩⟩
  have hRs : IsSylow2In R' (TwinADescent.coreAt c J) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hJ.2).mpr ⟨hRJ, hRc⟩
  have hsP : IsSylow2In ((R'.subgroupOf C).subgroupOf H)
      (((TwinADescent.coreAt c J).subgroupOf C).subgroupOf H) :=
    (hRs.subgroupOf (TwinADescent.coreAt_le_centralizer c J)).subgroupOf (le_coreHull hJ)
  have h1 : ((R'.subgroupOf C).subgroupOf H).map (QuotientGroup.mk' N) ≤
      M₀.map (QuotientGroup.mk' N) :=
    (Subgroup.map_mono hsP.1).trans ((h (secImg Ω c J) (secImg_mem_secFam hJ)).trans hS)
  have h2' : (R'.subgroupOf C).subgroupOf H ≤ M₀ ⊔ N := by
    intro a ha
    have h3 := h1 (Subgroup.mem_map_of_mem (QuotientGroup.mk' N) ha)
    have h4 := (Subgroup.mem_comap).mpr h3
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h4
  have hP'' : (R'.subgroupOf C).subgroupOf H ≤ M₀ :=
    le_of_isPGroup_of_le_sup_odd hN hsP.2.1 h2'
  intro a ha
  have haC : a ∈ C := hRc ha
  have haH : (⟨a, haC⟩ : ↥C) ∈ H := le_coreHull hJ (Subgroup.mem_subgroupOf.mpr (hRs.1 ha))
  have hmem : (⟨⟨a, haC⟩, haH⟩ : ↥H) ∈ (R'.subgroupOf C).subgroupOf H :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr ha)
  exact hM₀le (hP'' hmem)

theorem exists_conj_of_secImgR {R₃ R₄ : Subgroup G} (h3 : IsPGroup 2 R₃) (h4 : IsPGroup 2 R₄)
    (hR3c : R₃ ≤ Subgroup.centralizer ({c} : Set G))
    (hR3H : R₃.subgroupOf (Subgroup.centralizer ({c} : Set G)) ≤ coreHull Ω c)
    (hR4c : R₄ ≤ Subgroup.centralizer ({c} : Set G))
    (hR4H : R₄.subgroupOf (Subgroup.centralizer ({c} : Set G)) ≤ coreHull Ω c)
    :
    ∀ x : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c),
      conjSub x (secImgR Ω c R₃) = secImgR Ω c R₄ →
    ∃ g : ↥(coreHull Ω c), conjSub (((g : ↥(Subgroup.centralizer ({c} : Set G))) : G)) R₃ = R₄ := by
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set H := coreHull Ω c with hH
  set N := classicalInvolutionOddCore ↥H with hNdef
  have hN : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card ↥H
  set P₃ : Subgroup ↥H := (R₃.subgroupOf C).subgroupOf H with hP₃
  set P₄ : Subgroup ↥H := (R₄.subgroupOf C).subgroupOf H with hP₄
  intro x hx
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective N x
  rw [← hy] at hx
  have hpC3 : IsPGroup 2 ↥(R₃.subgroupOf C) := h3.of_equiv (Subgroup.subgroupOfEquivOfLe hR3c).symm
  have hpC4 : IsPGroup 2 ↥(R₄.subgroupOf C) := h4.of_equiv (Subgroup.subgroupOfEquivOfLe hR4c).symm
  have hp3 : IsPGroup 2 ↥P₃ := hpC3.of_equiv (Subgroup.subgroupOfEquivOfLe hR3H).symm
  have hp4 : IsPGroup 2 ↥P₄ := hpC4.of_equiv (Subgroup.subgroupOfEquivOfLe hR4H).symm
  have hmap : (conjSub y P₃).map (QuotientGroup.mk' N) = P₄.map (QuotientGroup.mk' N) := by
    rw [AscQuot.map_conjSub]
    exact hx
  have hpg : IsPGroup 2 ↥(conjSub y P₃) := isPGroup_conjSub _ hp3
  obtain ⟨n, -, hn⟩ := exists_conj_of_isPGroup_map_eq hN hpg hp4 hmap
  have hfin : conjSub (n * y) P₃ = P₄ := by rw [conjSub_mul, hn]
  refine ⟨n * y, ?_⟩
  have e3 : (P₃.map H.subtype).map C.subtype = R₃ :=
    map_map_subtype_secImgR (Ω := Ω) (c := c) hR3c hR3H
  have e4 : (P₄.map H.subtype).map C.subtype = R₄ :=
    map_map_subtype_secImgR (Ω := Ω) (c := c) hR4c hR4H
  rw [← e4, ← hfin, AscQuot.map_conjSub, AscQuot.map_conjSub, e3]
  rfl

section Named

variable {n : ℕ}

@[expose] def V3LayerTrans (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y), V3Std n Y R S t K K' K₃ u₁ u₂ u₃ →
      ∀ K₄ : Subgroup Y,
        FourthTwin (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ K₄ →
          SecNoExitAt (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) →
            (∀ J ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂), IsPGroup 2 J) →
            HasLifts (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) →
            ExactSylow (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) →
            Nonempty (OmegaLieU 3 1 (liftFam (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R))
              (u₁ * u₂)))) →
              ∀ R₃ R₄ : Subgroup Y, IsSylow2In R₃ K₃ → IsSylow2In R₄ K₄ →
                R₃ ≤ Subgroup.centralizer ({u₁ * u₂} : Set Y) →
                R₄ ≤ Subgroup.centralizer ({u₁ * u₂} : Set Y) →
                  (∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
                    M ≤ ⨆ x : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) ⧸
                      classicalInvolutionOddCore
                        ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
                      conjSub x (secImgR (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) R₃)) ∧
                    ∃ x : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) ⧸
                        classicalInvolutionOddCore
                          ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
                      conjSub x (secImgR (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) R₃) =
                        secImgR (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) R₄

end Named

section Assemble

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ K₄ : Subgroup Y} {u₁ u₂ u₃ : Y}

theorem v3_tq_members (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃)
    (hF : FourthTwin (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ K₄) :
    K₃ ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) ∧
      K₄ ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) := by
  have hd := hStd.datum
  have hΩ := hd.hyp
  have hz4 : IsUniqueInvolution K₄ t := isUniqueInvolution_of_mem_twinSet hd.hz hF.1
  refine ⟨⟨hd.hK₃.1, ?_⟩, ⟨hF.1.1, ?_⟩⟩
  · have t13 : u₁ ∈ trivialOnQuot K₃ :=
      A7T22.le_trivialOnQuot_of_twin hΩ hd.mem hd.hK₃.1 hd.hK₃K.symm hd.hz hd.hzK₃ hd.hu₁.1
    have t23 : u₂ ∈ trivialOnQuot K₃ :=
      A7T22.le_trivialOnQuot_of_twin hΩ hd.hK'.1 hd.hK₃.1 hd.hK₃K'.symm hd.hzK' hd.hzK₃ hd.hu₂.1
    exact (trivialOnQuot K₃).mul_mem t13 t23
  · have t14 : u₁ ∈ trivialOnQuot K₄ :=
      A7T22.le_trivialOnQuot_of_twin hΩ hd.mem hF.1.1 hF.2.1.symm hd.hz hz4 hd.hu₁.1
    have t24 : u₂ ∈ trivialOnQuot K₄ :=
      A7T22.le_trivialOnQuot_of_twin hΩ hd.hK'.1 hF.1.1 hF.2.2.1.symm hd.hzK' hz4 hd.hu₂.1
    exact (trivialOnQuot K₄).mul_mem t14 t24

theorem v3LayerGen_of_trans (hT : V3LayerTrans n) : V3LayerGen n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ hStd K₄ hF hno h2' hl hex hLie R₃ R₄ h3 h4 c3 c4
  obtain ⟨hgen, x, hx⟩ := hT Y R S t K K' K₃ u₁ u₂ u₃ hStd K₄ hF hno h2' hl hex hLie R₃ R₄ h3 h4 c3 c4
  have hd := hStd.datum
  have hΩ := hd.hyp
  have hC := CoreData.of_S hStd.perp.core
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.sq_12
  have hz4 : IsUniqueInvolution K₄ t := isUniqueInvolution_of_mem_twinSet hd.hz hF.1
  obtain ⟨hmem, hmem4⟩ := v3_tq_members hStd hF
  have h2 : ∀ M ∈ CoreAssembly.conjClass (tightCore R),
      IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hs3 : IsSylow2In R₃ (TwinADescent.coreAt (u₁ * u₂) K₃) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hmem.2).mpr ⟨h3, c3⟩
  have hs4 : IsSylow2In R₄ (TwinADescent.coreAt (u₁ * u₂) K₄) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hmem4.2).mpr ⟨h4, c4⟩
  have hR3H : R₃.subgroupOf (Subgroup.centralizer ({u₁ * u₂} : Set Y)) ≤
      coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) := fun a ha =>
    le_coreHull hmem (Subgroup.mem_subgroupOf.mpr (hs3.1 (Subgroup.mem_subgroupOf.mp ha)))
  have hR4H : R₄.subgroupOf (Subgroup.centralizer ({u₁ * u₂} : Set Y)) ≤
      coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) := fun a ha =>
    le_coreHull hmem4 (Subgroup.mem_subgroupOf.mpr (hs4.1 (Subgroup.mem_subgroupOf.mp ha)))
  have hR3L : R₃ ≤ rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) := by
    unfold rLayer
    exact le_iSup₂_of_le R₃ (mem_RSet_of_isSylow2In hd.hK₃.1 h3)
      (le_iSup (fun _ : R₃ ≤ Subgroup.centralizer ({u₁ * u₂} : Set Y) => R₃) c3)
  refine ⟨le_antisymm ?_ (rLayer_le_iSup_of_secImgR hΩ hc2 h2 hgen), ?_⟩
  · refine iSup_le fun y => ?_
    intro a ha
    have hy : (y : Y) ∈ rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) := y.2
    have h1 := hR3L (mem_conjSub_iff.mp ha)
    have := (rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)).mul_mem
      ((rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)).mul_mem hy h1)
      ((rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)).inv_mem hy)
    simpa [mul_assoc] using this
  · obtain ⟨g, hg⟩ := exists_conj_of_secImgR h3.2.1 h4.2.1 c3 hR3H c4 hR4H x hx
    have hgL : (((g : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y)) ∈
        rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) :=
      coreHull_map_le_rLayer hΩ hc2 ⟨(g : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))), g.2, rfl⟩
    have e3 := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hd.hK₃.1 h3)
    have e4 := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hF.1.1 h4)
    exact ⟨⟨⟨_, hgL⟩, hg⟩, t, isUniqueInvolution_of_isSylow2In hd.hzK₃ h3 (by omega),
      isUniqueInvolution_of_isSylow2In hz4 h4 (by omega)⟩

end Assemble

end Layer

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
