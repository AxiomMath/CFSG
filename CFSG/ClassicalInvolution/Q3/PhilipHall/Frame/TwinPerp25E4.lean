module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25E3
public import CFSG.RankThree.PartTwo.Sec8.TransferExtremal
public import CFSG.ClassicalInvolution.Q3.Q3T7P25YMB01
public import CFSG.ClassicalInvolution.Q3.Q3T7P25YMH02
public import CFSG.ClassicalInvolution.Q3.Q3T6LinSp
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R.EndL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.C5O (Om5Data Om5Centerless Om5InvFixFour Om5Interchange Om5ZSwap
  Om5USwapNotZ Om5ExcClass ModelFacts TwinShare M8GFacts Om5TwinComm Om5TwinCommSwap HasBigFix)
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Asc77.ExactLayer (isPGroup_zpowers_of_sq_eq_one)
open scoped commutatorElement


section Gen

variable {G : Type} [Group G]

theorem conjSub_inf' (g : G) (A B : Subgroup G) :
    conjSub g (A ⊓ B) = conjSub g A ⊓ conjSub g B :=
  Subgroup.map_inf A B (MulAut.conj g).toMonoidHom (MulAut.conj g).injective

theorem conjSub_centralizer_singleton' (g c : G) :
    conjSub g (Subgroup.centralizer ({c} : Set G)) = Subgroup.centralizer ({g * c * g⁻¹} : Set G) := by
  ext y
  rw [mem_conjSub_iff, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = (g * c * g⁻¹) * y := by group
  · intro h
    calc g⁻¹ * y * g * c = g⁻¹ * (y * (g * c * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * c * g⁻¹) * y) * g := by rw [h]
      _ = c * (g⁻¹ * y * g) := by group

variable [Finite G]

theorem conjSub_coreAt_gen (g c : G) (J : Subgroup G) :
    conjSub g (TwinADescent.coreAt c J) = TwinADescent.coreAt (g * c * g⁻¹) (conjSub g J) := by
  unfold TwinADescent.coreAt
  rw [conjSub_tightCore, conjSub_inf', conjSub_centralizer_singleton']

theorem coreAt_mul_eq {L : Subgroup G} {z : G} (hL : L ≤ Subgroup.centralizer ({z} : Set G)) (a : G) :
    TwinADescent.coreAt (a * z) L = TwinADescent.coreAt a L := by
  unfold TwinADescent.coreAt
  congr 1
  ext k
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hk, h⟩
    refine ⟨hk, ?_⟩
    have hkz : k * z = z * k := Subgroup.mem_centralizer_singleton_iff.mp (hL hk)
    have : k * a * z = a * k * z := by
      calc k * a * z = k * (a * z) := by group
        _ = a * z * k := h
        _ = a * (z * k) := by group
        _ = a * (k * z) := by rw [hkz]
        _ = a * k * z := by group
    exact mul_right_cancel this
  · rintro ⟨hk, h⟩
    refine ⟨hk, ?_⟩
    have hkz : k * z = z * k := Subgroup.mem_centralizer_singleton_iff.mp (hL hk)
    calc k * (a * z) = k * a * z := by group
      _ = a * k * z := by rw [h]
      _ = a * (k * z) := by group
      _ = a * (z * k) := by rw [hkz]
      _ = a * z * k := by group

end Gen

section Layer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem conjSub_layerX_eq (hΩ : HypOmegaGen Ω) {c c' g : G} (hg : g * c * g⁻¹ = c') :
    conjSub g (layerX Ω c) = layerX Ω c' := by
  rw [← hg, layerX_conj hΩ g c]


theorem conj_mem_layerX (hΩ : HypOmegaGen Ω) {c c' g : G} (hg : g * c * g⁻¹ = c')
    {y : G} (hy : y ∈ layerX Ω c) : g * y * g⁻¹ ∈ layerX Ω c' := by
  rw [← conjSub_layerX_eq hΩ hg]
  exact conj_mem_conjSub hy


@[expose] noncomputable def conjLayer (hΩ : HypOmegaGen Ω) {c c' g : G}
    (hg : g * c * g⁻¹ = c') : ↥(layerX Ω c) ≃* ↥(layerX Ω c') :=
  (Subgroup.equivMapOfInjective (layerX Ω c) (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr (conjSub_layerX_eq hΩ hg))


@[expose] noncomputable def layerIso (hΩ : HypOmegaGen Ω) {c c' g : G}
    (hg : g * c * g⁻¹ = c') : (↥(layerX Ω c) ⧸ classicalInvolutionOddCore
        ↥(layerX Ω c)) ≃*
      (↥(layerX Ω c') ⧸ classicalInvolutionOddCore ↥(layerX Ω c')) :=
  QuotientGroup.congr _ _ (conjLayer hΩ hg)
    (CFSG.ComponentClassification.OddCore.equiv_invariant (conjLayer hΩ hg))


theorem layerIso_mk (hΩ : HypOmegaGen Ω) {c c' g : G} (hg : g * c * g⁻¹ = c')
    (y : ↥(layerX Ω c)) :
    layerIso hΩ hg (QuotientGroup.mk y) =
      QuotientGroup.mk ⟨g * y * g⁻¹, conj_mem_layerX hΩ hg y.2⟩ :=
  rfl


theorem map_imgK_layerIso (hΩ : HypOmegaGen Ω) {c c' g : G} (hg : g * c * g⁻¹ = c')
    (K : Subgroup G) :
    (imgK Ω c K).map (layerIso hΩ hg).toMonoidHom = imgK Ω c' (conjSub g K) := by
  have hcore : TwinADescent.coreAt c' (conjSub g K) = conjSub g (TwinADescent.coreAt c K) := by
    rw [← hg]
    exact (conjSub_coreAt_gen g c K).symm
  have hg' : g⁻¹ * c' * g⁻¹⁻¹ = c := by rw [← hg]; group
  ext e
  constructor
  · rintro ⟨e₀, he₀, rfl⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp he₀
    refine Subgroup.mem_map.mpr ⟨⟨g * y * g⁻¹, conj_mem_layerX hΩ hg y.2⟩, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf, hcore]
    exact conj_mem_conjSub (Subgroup.mem_subgroupOf.mp hy)
  · intro he
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp he
    have hy' : (y : G) ∈ conjSub g (TwinADescent.coreAt c K) := by
      rw [← hcore]
      exact Subgroup.mem_subgroupOf.mp hy
    refine ⟨QuotientGroup.mk ⟨g⁻¹ * y * g⁻¹⁻¹, conj_mem_layerX hΩ hg' y.2⟩,
      Subgroup.mem_map.mpr ⟨⟨g⁻¹ * y * g⁻¹⁻¹, conj_mem_layerX hΩ hg' y.2⟩, ?_, rfl⟩, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      have := (mem_conjSub_iff).mp hy'
      simpa using this
    · show layerIso hΩ hg (QuotientGroup.mk _) = QuotientGroup.mk' _ y
      rw [layerIso_mk]
      congr 1
      apply Subtype.ext
      show g * (g⁻¹ * y.1 * g⁻¹⁻¹) * g⁻¹ = y.1
      group

theorem layerAut_conj (hΩ : HypOmegaGen Ω) {c c' g y : G} (hg : g * c * g⁻¹ = c')
    (hy : conjSub y (layerX Ω c) = layerX Ω c)
    (hy' : conjSub (g * y * g⁻¹) (layerX Ω c') = layerX Ω c')
    (e : (↥(layerX Ω c') ⧸ classicalInvolutionOddCore ↥(layerX Ω
        c'))) :
    C25Y.layerAut (layerX Ω c') hy' e =
      layerIso hΩ hg (C25Y.layerAut (layerX Ω c) hy ((layerIso hΩ hg).symm e)) := by
  obtain ⟨e₀, rfl⟩ := (layerIso hΩ hg).surjective e
  rw [MulEquiv.symm_apply_apply]
  induction e₀ using QuotientGroup.induction_on with
  | H w =>
    rw [layerIso_mk, C25Y.layerAut_mk, C25Y.layerAut_mk, layerIso_mk]
    congr 1
    apply Subtype.ext
    show g * y * g⁻¹ * (g * w.1 * g⁻¹) * (g * y * g⁻¹)⁻¹ = g * (y * w.1 * y⁻¹) * g⁻¹
    group

end Layer

section Transfer

variable {G : Type} [Group G] [Finite G]

theorem false_of_extremal_layer {Ω : Set (Subgroup G)}
    {K : Subgroup G} (hs : AscStand Ω K) {J R X N : Subgroup G} (hJ : J ∈ Ω) (hR : IsSylow2In R J)
    (hN : Odd (Nat.card N)) (hRX : R ≤ ⁅X, X⁆ ⊔ N)
    (P : Sylow 2 G) {H : Subgroup G}
    (habel : ∀ y ∈ (P : Subgroup G), ∀ w ∈ (P : Subgroup G), y * w * y⁻¹ * w⁻¹ ∈ H)
    {x : G} (hx : x ∈ (P : Subgroup G)) (hxH : x ∉ H) (hx2 : x ^ 2 = 1)
    (hfus : ∀ g : G,
      (∀ y ∈ (P : Subgroup G) ⊓ Subgroup.centralizer {x}, g⁻¹ * y * g ∈ (P : Subgroup G)) →
        x⁻¹ * (g⁻¹ * x * g) ∈ H) : False := by
  classical
  set U : Subgroup (P : Subgroup G) := H.subgroupOf P with hU
  have hUn : U.Normal := ⟨fun u hu y => by
    rw [hU, Subgroup.mem_subgroupOf] at hu ⊢
    have h := H.mul_mem (habel y y.2 u u.2) hu
    rwa [inv_mul_cancel_right] at h⟩
  have hcomm : ∀ a b : (P : Subgroup G) ⧸ U, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H y =>
    induction b using QuotientGroup.induction_on with
    | H w =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    refine Subgroup.mem_subgroupOf.mpr ?_
    have := habel (w : G)⁻¹ (Subgroup.inv_mem _ w.2) (y : G)⁻¹ (Subgroup.inv_mem _ y.2)
    simpa [mul_assoc] using this
  let : CommGroup ((P : Subgroup G) ⧸ U) :=
    { QuotientGroup.Quotient.group U with mul_comm := hcomm }
  let ϕ : (P : Subgroup G) →* (P : Subgroup G) ⧸ U := QuotientGroup.mk' U
  have hT : ϕ.transfer x = ϕ ⟨x, hx⟩ ^ (P : Subgroup G).index := by
    refine CFSG.RankThree.PartTwo.Sec8.transfer_eq_pow_index_of_extremal P ϕ hx hx2
      fun t hD ht => ?_
    change (QuotientGroup.mk' U _ : _) = QuotientGroup.mk' U _
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hfus t hD)
  have hne : ϕ ⟨x, hx⟩ ≠ 1 := fun h =>
    hxH (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h))
  have hpow : ϕ ⟨x, hx⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨x, hx⟩ : (P : Subgroup G)) ^ 2 = 1 := Subtype.ext (by simp [hx2])
    rw [this, map_one]
  have hP2 : IsPGroup 2 ((P : Subgroup G) ⧸ U) := P.isPGroup'.to_quotient U
  have hker : ⁅X, X⁆ ⊔ N ≤ ϕ.transfer.ker := by
    refine sup_le ?_ ?_
    · have hc : ⁅X, X⁆ ≤ commutator G := by
        rw [commutator_def]
        exact Subgroup.commutator_mono le_top le_top
      exact hc.trans (Abelianization.commutator_subset_ker ϕ.transfer)
    · intro n hn
      rw [MonoidHom.mem_ker]
      have h1 : n ^ Nat.card N = 1 := by
        have h := congrArg (fun y : ↥N => (y : G)) (pow_card_eq_one' (G := ↥N) (x := ⟨n, hn⟩))
        simp only [Subgroup.coe_pow, Subgroup.coe_one] at h
        exact h
      have h2 : (ϕ.transfer n) ^ Nat.card N = 1 := by rw [← map_pow, h1, map_one]
      obtain ⟨k, hk⟩ := hP2 (ϕ.transfer n)
      have h3 : orderOf (ϕ.transfer n) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
      have h4 : orderOf (ϕ.transfer n) ∣ Nat.card N := orderOf_dvd_of_pow_eq_one h2
      have hcop : Nat.Coprime (2 ^ k) (Nat.card N) :=
        Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hN)
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h3 h4)
  have hV : ϕ.transfer = 1 :=
    T7C.hom_eq_one_of_sylow hs hJ hR ϕ.transfer
      (fun y hy => MonoidHom.mem_ker.mp (hker (hRX hy)))
  have h1 : ϕ.transfer x = 1 := by rw [hV]; rfl
  rw [hT] at h1
  have hdvd := orderOf_dvd_of_pow_eq_one h1
  rw [orderOf_eq_prime hpow hne] at hdvd
  exact P.not_dvd_index hdvd

theorem le_commutator_sup_oddCore (X : Subgroup G)
    (hperf : Group.IsPerfect (↥X ⧸ classicalInvolutionOddCore ↥X)) :
    X ≤ ⁅X, X⁆ ⊔ oddCoreIn X := by
  intro x hx
  have h1 : (QuotientGroup.mk ⟨x, hx⟩ : ↥X ⧸ classicalInvolutionOddCore ↥X) ∈
      commutator (↥X ⧸ classicalInvolutionOddCore ↥X) := hperf.mem_commutator
  have hsurj : Function.Surjective (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) :=
    QuotientGroup.mk'_surjective _
  have h2 : commutator (↥X ⧸ classicalInvolutionOddCore ↥X) =
      Subgroup.map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X))
        ⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hsurj]
  rw [h2] at h1
  obtain ⟨c, hc, hce⟩ := h1
  have hco : ((c⁻¹ * ⟨x, hx⟩ : ↥X) : G) ∈ oddCoreIn X := by
    refine (mk_eq_one_iff X _).mp ?_
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have : (QuotientGroup.mk c : ↥X ⧸ classicalInvolutionOddCore ↥X) = QuotientGroup.mk ⟨x, hx⟩ :=
      hce
    rw [this, inv_mul_cancel]
  have hcm : (c : G) ∈ ⁅X, X⁆ := by
    have : Subgroup.map X.subtype ⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆ = ⁅X, X⁆ := by
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← this]
    exact ⟨c, hc, rfl⟩
  have e : x = (c : G) * ((c⁻¹ * ⟨x, hx⟩ : ↥X) : G) := by
    simp
  rw [e]
  exact Subgroup.mul_mem_sup hcm hco

end Transfer

section Main

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ a : G}

namespace Ctx

theorem layer_perfect (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) : Group.IsPerfect (layerBar Ω a) := by
  obtain ⟨hz, hu₁, hu₂, A, A', -, -, hD, -, -⟩ := C.om5
  obtain ⟨fr⟩ := Q3T8.Asc77.C5O.M.exists_frame hD
  haveI := Q3T6.isPerfect_sp4_of_three_le (K := GaloisField 3 1)
    Q3T7P25.natCard_gf3.ge
  exact Group.IsPerfect.ofSurjective fr.surj

theorem exists_conj_mem_S (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) {w : G}
    (hwa : w * a = a * w) (hwz : w * z = z * w) (hw2 : IsPGroup 2 (Subgroup.zpowers w)) :
    ∃ g ∈ Subgroup.normalizer
      (((S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :
        Subgroup G) : Set G), g⁻¹ * w * g ∈ (S : Subgroup G) := by
  set A₀ := (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) with hA₀
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (A₀ : Set G) := fun s hs =>
    Generic.mem_normalizer_of_conjSub_eq (cA_normal C.hyp hs)
  have hSsyl : IsSylow2In (S : Subgroup G) (Subgroup.normalizer (A₀ : Set G)) :=
    ⟨hSN, S.isPGroup', fun V' _ hV' hle => S.is_maximal' hV' hle⟩
  have hfixA : ∀ h ∈ A₀, w * h * w⁻¹ = h := by
    intro h hh
    rcases C.hA0 h hh with e | e | e | e <;> rw [e]
    · group
    · rw [hwa]; group
    · rw [hwz]; group
    · calc w * (a * z) * w⁻¹ = (w * a) * z * w⁻¹ := by group
        _ = a * (w * z) * w⁻¹ := by rw [hwa]; group
        _ = a * z := by rw [hwz]; group
  have hwN : Subgroup.zpowers w ≤ Subgroup.normalizer (A₀ : Set G) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun hh => ?_,
      fun hh => ?_⟩)
    · rw [hfixA h hh]; exact hh
    · have e1 := hfixA _ hh
      have e2 : h = w * h * w⁻¹ := by
        calc h = w⁻¹ * (w * h * w⁻¹) * w := by group
          _ = w⁻¹ * (w * (w * h * w⁻¹) * w⁻¹) * w := by rw [e1]
          _ = w * h * w⁻¹ := by group
      rw [e2]; exact hh
  obtain ⟨V, hV, hVle⟩ := IsSylow2In.exists_ge hw2 hwN
  obtain ⟨g, hg, hVeq⟩ := IsSylow2Of.exists_conj (show IsSylow2Of _ _ from hSsyl)
    (show IsSylow2Of _ _ from hV)
  refine ⟨g, hg, ?_⟩
  have h := hVle (Subgroup.mem_zpowers w)
  rw [hVeq] at h
  exact mem_conjSubgroup_iff.mp h

theorem mk_swaps (hM : ModelFacts)
    (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) {τ σ hτ hσ : G}
    (hhτX : hτ ∈ layerX Ω (a * z)) (hhτ : hτ * z * hτ⁻¹ = τ) (hτz : τ * z = z * τ)
    (hτK : conjSub τ K = K') (hτn : ∀ h : G, h * a = a * h → h * z * h⁻¹ ≠ τ)
    (haτ : ¬ ∃ g : G, g * z * g⁻¹ = a * τ) (hhσX : hσ ∈ layerX Ω a)
    (hhσ : hσ * z * hσ⁻¹ = σ) (hσz : σ * z = z * σ)
    (hσn : ∀ h : G, h * (a * z) = (a * z) * h → h * z * h⁻¹ ≠ σ)
    (haσ : ¬ ∃ g : G, g * z * g⁻¹ = (a * z) * σ) :
    Swaps Ω K K' W S R R' z t u₁ u₂ a τ σ := by
  obtain ⟨hzY, -, -, -, -, A, A', -⟩ := C.om5'
  obtain ⟨hzY', -, -, -, -, A, A', -⟩ := C.swap.om5'
  have hτX : τ ∈ layerX Ω (a * z) := by
    rw [← hhτ]; exact mul_mem (mul_mem hhτX hzY') (inv_mem hhτX)
  have hσX : σ ∈ layerX Ω a := by
    rw [← hhσ]; exact mul_mem (mul_mem hhσX hzY) (inv_mem hhσX)
  have hτaz : τ * (a * z) = (a * z) * τ :=
    Subgroup.mem_centralizer_singleton_iff.mp (layerX_le_centralizer Ω (a * z) hτX)
  have hτa : τ * a = a * τ := by
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right C.hz2
    calc τ * a = τ * (a * z) * z⁻¹ := by group
      _ = (a * z) * τ * z⁻¹ := by rw [hτaz]
      _ = (a * z) * (τ * z) := by rw [hzi]; group
      _ = (a * z) * (z * τ) := by rw [hτz]
      _ = a * τ := by rw [← mul_assoc, C.mul_z_mul_z]
  have hσa : σ * a = a * σ :=
    Subgroup.mem_centralizer_singleton_iff.mp (layerX_le_centralizer Ω a hσX)
  exact ⟨C, ⟨hτ, hhτ⟩, hτa, hτz, hτn, haτ, hτX, hτK, ⟨hσ, hhσ⟩, hσa, hσz, hσn, haσ, hσX,
    C.swap.interchange hM hhτX hhτ hτz hτK⟩

theorem exists_swaps (hM : ModelFacts)
    (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) :
    (∃ τ σ : G, Swaps Ω K K' W S R R' z t u₁ u₂ a τ σ ∧ τ ∈ (S : Subgroup G)) ∨
      ∃ τ σ : G, Swaps Ω K K' W S R R' z t u₁ u₂ (a * z) τ σ ∧ τ ∈ (S : Subgroup G) := by
  classical
  have hs : Hyp23Setting Ω K K' z := C.hyp.std.setting
  have hΩ : HypOmegaGen Ω := C.hΩ
  have hz2 := C.hz2
  have hazz := C.mul_z_mul_z
  obtain ⟨t₀, ⟨h₀, hh₀X, hh₀⟩, ht₀z, -, ht₀K, -, ht₀n⟩ := C.swap.refSwap hM
  obtain ⟨s₀, ⟨k₀, hk₀X, hk₀⟩, hs₀z, -, hs₀K, -, hs₀n⟩ := C.refSwap hM
  have has₀ := C.not_conj_az_swap hM hk₀X hk₀ hs₀z hs₀K
  have hat₀ := C.swap.not_conj_az_swap hM hh₀X hh₀ ht₀z ht₀K
  rw [hazz] at hat₀
  have ht₀n' : ∀ h : G, h * a = a * h → h * z * h⁻¹ ≠ t₀ := by
    intro h hh hhz
    apply ht₀n h hhz
    rw [hazz]; exact hh
  have hs₀n' : ∀ h : G, h * (a * z) = (a * z) * h → h * z * h⁻¹ ≠ s₀ :=
    fun h hh hhz => hs₀n h hhz hh
  obtain ⟨hzY, -, -, -, -, A, A', -⟩ := C.om5'
  obtain ⟨hzY', -, -, -, -, A, A', -⟩ := C.swap.om5'
  have ht₀X : t₀ ∈ layerX Ω (a * z) := by
    rw [← hh₀]; exact mul_mem (mul_mem hh₀X hzY') (inv_mem hh₀X)
  have ht₀az : t₀ * (a * z) = (a * z) * t₀ :=
    Subgroup.mem_centralizer_singleton_iff.mp (layerX_le_centralizer Ω (a * z) ht₀X)
  have ht₀a : t₀ * a = a * t₀ := by
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    calc t₀ * a = t₀ * (a * z) * z⁻¹ := by group
      _ = (a * z) * t₀ * z⁻¹ := by rw [ht₀az]
      _ = (a * z) * (t₀ * z) := by rw [hzi]; group
      _ = (a * z) * (z * t₀) := by rw [ht₀z]
      _ = a * t₀ := by rw [← mul_assoc, hazz]
  have ht₀2 : t₀ * t₀ = 1 := by
    rw [← hh₀]
    calc h₀ * z * h₀⁻¹ * (h₀ * z * h₀⁻¹) = h₀ * (z * z) * h₀⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  obtain ⟨g, hg, hgS⟩ := C.exists_conj_mem_S ht₀a ht₀z (isPGroup_zpowers_of_sq_eq_one ht₀2)
  have hgi := Subgroup.inv_mem _ hg
  have hgz : g⁻¹ * z * g = z := by
    have := C.norm_fix_z hgi
    rwa [inv_inv] at this
  set t₁ := g⁻¹ * t₀ * g with ht₁
  have ht₁z : t₁ * z = z * t₁ := by
    calc t₁ * z = g⁻¹ * (t₀ * (g * z * g⁻¹)) * g := by rw [ht₁]; group
      _ = g⁻¹ * (t₀ * z) * g := by
          rw [show g * z * g⁻¹ = z by
            calc g * z * g⁻¹ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hgz]
              _ = z := by group]
      _ = g⁻¹ * (z * t₀) * g := by rw [ht₀z]
      _ = (g⁻¹ * z * g) * t₁ := by rw [ht₁]; group
      _ = z * t₁ := by rw [hgz]
  have hgzc : g * z * g⁻¹ = z := by
    calc g * z * g⁻¹ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hgz]
      _ = z := by group
  have ht₁K : conjSub t₁ K = K' := by
    have ht₀K' : conjSub t₀ K' = K := by
      rw [← ht₀K, ← conjSub_mul, ht₀2, conjSub_one]
    rw [ht₁, conjSub_mul, conjSub_mul]
    rcases P25S.conjSub_pair_of_central hs hgzc with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, ht₀K, ← e2, ← conjSub_mul, inv_mul_cancel, conjSub_one, e2]
    · rw [e1, ht₀K', ← e2, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  have hpull : ∀ (b w : G), (∀ h : G, h * b = b * h → h * z * h⁻¹ ≠ w) →
      ∀ h : G, h * (g⁻¹ * b * g) = (g⁻¹ * b * g) * h → h * z * h⁻¹ ≠ g⁻¹ * w * g := by
    intro b w hn h hh hhz
    apply hn (g * h * g⁻¹)
    · calc g * h * g⁻¹ * b = g * (h * (g⁻¹ * b * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * b * g) * h) * g⁻¹ := by rw [hh]
        _ = b * (g * h * g⁻¹) := by group
    · calc g * h * g⁻¹ * z * (g * h * g⁻¹)⁻¹ = g * (h * (g⁻¹ * z * g) * h⁻¹) * g⁻¹ := by group
        _ = g * (g⁻¹ * w * g) * g⁻¹ := by rw [hgz, hhz]
        _ = w := by group
  have hpullG : ∀ b : G, (¬ ∃ g' : G, g' * z * g'⁻¹ = b * t₀) →
      ¬ ∃ g' : G, g' * z * g'⁻¹ = (g⁻¹ * b * g) * t₁ := by
    rintro b hn ⟨g', hg'⟩
    apply hn ⟨g * g', ?_⟩
    calc g * g' * z * (g * g')⁻¹ = g * (g' * z * g'⁻¹) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * t₁) * g⁻¹ := by rw [hg']
      _ = b * t₀ := by rw [ht₁]; group
  have hh₁ : (g⁻¹ * h₀ * g) * z * (g⁻¹ * h₀ * g)⁻¹ = t₁ := by
    calc (g⁻¹ * h₀ * g) * z * (g⁻¹ * h₀ * g)⁻¹ = g⁻¹ * (h₀ * (g * z * g⁻¹) * h₀⁻¹) * g := by group
      _ = t₁ := by rw [hgzc, hh₀, ht₁]
  have hconjX : ∀ c : G, g⁻¹ * h₀ * g ∈ layerX Ω (g⁻¹ * c * g) ↔
      h₀ ∈ layerX Ω c := by
    intro c
    have e := layerX_conj hΩ g⁻¹ c
    rw [inv_inv] at e
    rw [e, mem_conjSub_iff, inv_inv]
    constructor <;> intro h <;> simpa [mul_assoc] using h
  rcases C.norm_a_cases hgi with hga | hga <;> rw [inv_inv] at hga
  ·
    left
    have hgaz : g⁻¹ * (a * z) * g = a * z := by
      calc g⁻¹ * (a * z) * g = (g⁻¹ * a * g) * (g⁻¹ * z * g) := by group
        _ = a * z := by rw [hga, hgz]
    have hX1 : g⁻¹ * h₀ * g ∈ layerX Ω (a * z) := by
      rw [← hgaz]; exact (hconjX (a * z)).mpr hh₀X
    refine ⟨t₁, s₀, C.mk_swaps hM hX1 hh₁ ht₁z ht₁K ?_ ?_ hk₀X hk₀ hs₀z hs₀n' has₀, hgS⟩
    · have := hpull a t₀ ht₀n'
      rwa [hga] at this
    · have := hpullG a hat₀
      rwa [hga] at this
  ·
    right
    have hgaz : g⁻¹ * (a * z) * g = a * z * z := by
      calc g⁻¹ * (a * z) * g = (g⁻¹ * a * g) * (g⁻¹ * z * g) := by group
        _ = a * z * z := by rw [hga, hgz]
    have hX1 : g⁻¹ * h₀ * g ∈ layerX Ω (a * z * z) := by
      rw [← hgaz]; exact (hconjX (a * z)).mpr hh₀X
    refine ⟨t₁, t₀, C.swap.mk_swaps hM hX1 hh₁ ht₁z ht₁K ?_ ?_ hh₀X hh₀ ht₀z ?_ ?_, hgS⟩
    · have := hpull a t₀ ht₀n'
      rwa [hga] at this
    · have := hpullG a hat₀
      rwa [hga] at this
    · intro h hh hhz
      apply ht₀n' h _ hhz
      rw [hazz] at hh; exact hh
    · rw [hazz]; exact hat₀

end Ctx

namespace Swaps
variable {τ σ : G}

theorem false_of_comm (D : Swaps Ω K K' W S R R' z t u₁ u₂ a τ σ)
    (hT1 : ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x * y * x⁻¹ * y⁻¹ ∈
      hBig D.ctx.hΩ z a τ σ D.τC D.σC) (hM : ModelFacts) : False := by
  have C := D.ctx
  have haS : a ∈ (S : Subgroup G) := C.haA.1
  obtain ⟨t', hT⟩ := T7T.exists_hyp25T C.hyp
  have hRX : R ≤ ⁅layerX Ω a, layerX Ω a⁆ ⊔ oddCoreIn (layerX Ω a) :=
    C.R_le.trans (le_commutator_sup_oddCore (layerX Ω a) C.layer_perfect)
  refine false_of_extremal_layer C.hyp.std.1.stand C.hyp.std.1.stand.mem hT.hRsyl
    (odd_card_oddCoreIn _) hRX S hT1 haS (D.a_not_mem_hBig hM)
    (by rw [pow_two]; exact C.ha2) (fun g hg => ?_)
  have hgS : g⁻¹ * a * g ∈ (S : Subgroup G) :=
    hg a ⟨haS, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  exact D.extremal_mem_hBig hM (C.hyp.hzS _ hgS)

end Swaps

end Main

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R.EndL
