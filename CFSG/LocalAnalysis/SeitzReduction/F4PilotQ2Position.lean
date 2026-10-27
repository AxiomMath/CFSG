module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2Fusion
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7Nonsplit
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionAut
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCentralizerTU
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPositionCore
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPositionTransport

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree (ReeTag)
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono le_perfectCore_of_perfect
  perfectCore_perfect perfectCore_eq_self_of_perfect)
open scoped commutatorElement

section PerfectCore

variable {G : Type*} [Group G]

theorem commutatorElement_mul_mul_eq_right_of_commute {a₁ a₂ d₁ d₂ : G} (h12 : Commute a₁ a₂)
    (h11 : Commute a₁ d₁) (h1₂ : Commute a₁ d₂) (h21 : Commute a₂ d₁) (h22 : Commute a₂ d₂) :
    ⁅a₁ * d₁, a₂ * d₂⁆ = ⁅d₁, d₂⁆ := by
  have hX : Commute a₁ (d₁ * a₂ * d₂ * d₁⁻¹) :=
    ((h11.mul_right h12).mul_right h1₂).mul_right h11.inv_right
  have hY : Commute a₂ (d₂ * d₁⁻¹ * d₂⁻¹) := (h22.mul_right h21.inv_right).mul_right h22.inv_right
  rw [commutatorElement_def, commutatorElement_def]
  calc a₁ * d₁ * (a₂ * d₂) * (a₁ * d₁)⁻¹ * (a₂ * d₂)⁻¹
      = (a₁ * (d₁ * a₂ * d₂ * d₁⁻¹) * a₁⁻¹) * d₂⁻¹ * a₂⁻¹ := by group
    _ = d₁ * (a₂ * (d₂ * d₁⁻¹ * d₂⁻¹) * a₂⁻¹) := by rw [hX.eq, mul_inv_cancel_right]; group
    _ = d₁ * d₂ * d₁⁻¹ * d₂⁻¹ := by rw [hY.eq, mul_inv_cancel_right]; group

theorem perfectCore_sup_eq_of_le_centralizer [Finite G] {A D : Subgroup G}
    (hA : A ≤ centralizer (A : Set G)) (hAD : A ≤ centralizer (D : Set G)) (hD : ⁅D, D⁆ = D) :
    perfectCore (A ⊔ D) = D := by
  refine le_antisymm ?_ (le_perfectCore_of_perfect le_sup_right hD)
  have hcomm : ⁅A ⊔ D, A ⊔ D⁆ ≤ D := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have hAN : A ≤ normalizer (D : Set G) := hAD.trans (centralizer_le_normalizer _)
    have hg₁' : g₁ ∈ ((A ⊔ D : Subgroup G) : Set G) := hg₁
    have hg₂' : g₂ ∈ ((A ⊔ D : Subgroup G) : Set G) := hg₂
    rw [coe_mul_of_left_le_normalizer_right _ _ hAN] at hg₁' hg₂'
    obtain ⟨a₁, ha₁, d₁, hd₁, rfl⟩ := Set.mem_mul.1 hg₁'
    obtain ⟨a₂, ha₂, d₂, hd₂, rfl⟩ := Set.mem_mul.1 hg₂'
    have hc : ∀ {a d : G}, a ∈ A → d ∈ D → Commute a d := fun ha hd =>
      (mem_centralizer_iff.1 (hAD ha) _ hd).symm
    rw [commutatorElement_mul_mul_eq_right_of_commute
      ((mem_centralizer_iff.1 (hA ha₁) _ ha₂).symm) (hc ha₁ hd₁) (hc ha₁ hd₂) (hc ha₂ hd₁)
      (hc ha₂ hd₂)]
    exact Subgroup.commutator_mem_commutator hd₁ hd₂ |> fun h => hD ▸ h
  calc perfectCore (A ⊔ D) = ⁅perfectCore (A ⊔ D), perfectCore (A ⊔ D)⁆ :=
        (perfectCore_perfect _).symm
    _ ≤ ⁅A ⊔ D, A ⊔ D⁆ := commutator_mono (perfectCore_le _) (perfectCore_le _)
    _ ≤ D := hcomm

theorem perfectCore_centralizer_map_mulAut [Finite G] (α : MulAut G) (H : Subgroup G) :
    perfectCore (centralizer ((H.map α.toMonoidHom : Subgroup G) : Set G)) =
      (perfectCore (centralizer (H : Set G))).map α.toMonoidHom := by
  rw [centralizer_map_mulAut, CFSG.Quasithin.map_perfectCore]

theorem nonempty_perfectCore_centralizer_map_mulAut [Finite G] (α : MulAut G) (H : Subgroup G) :
    Nonempty (perfectCore (centralizer ((H.map α.toMonoidHom : Subgroup G) : Set G)) ≃*
      perfectCore (centralizer (H : Set G))) := by
  rw [perfectCore_centralizer_map_mulAut]
  exact ⟨((perfectCore (centralizer (H : Set G))).equivMapOfInjective _ α.injective).symm⟩

theorem exists_le_map_eq_of_le_map (α : MulAut G) {H Y : Subgroup G}
    (hY : Y ≤ H.map α.toMonoidHom) : ∃ Y' : Subgroup G, Y' ≤ H ∧ Y'.map α.toMonoidHom = Y := by
  refine ⟨Y.comap α.toMonoidHom, fun y hy => ?_, map_comap_eq_self_of_surjective α.surjective Y⟩
  obtain ⟨h, hh, hhy⟩ := hY (show α y ∈ Y from hy)
  rwa [← α.injective hhy]

theorem isCyclic_map_mulAut (α : MulAut G) {Y : Subgroup G} (hY : IsCyclic Y) :
    IsCyclic (Y.map α.toMonoidHom) :=
  isCyclic_of_surjective (α.toMonoidHom.subgroupMap Y) (α.toMonoidHom.subgroupMap_surjective Y)

end PerfectCore

section F6


variable {K : Type} [Field K]

theorem finite_adjointGroup_F4 [Finite K] : Finite (adjointGroup .F4 K) := by
  have : Finite (ModGL .F4 K) := finite_modGL
  infer_instance

theorem commutator_C3Levi_eq_self [Finite K] [CharP K 2] : ⁅C3Levi K, C3Levi K⁆ = C3Levi K := by
  have h := congrArg (Subgroup.map (C3Levi K).subtype)
    (Group.isPerfect_def.1 (isQuasisimple_C3Levi (K := K)).1)
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact h

theorem perfectCore_centralizer_nonsplit [Finite K] [CharP K 2]
    {Y : Subgroup (adjointGroup .F4 K)}
    (hYJ : Y ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic Y)
    (hY : Nat.card Y = Nat.card K + 1) :
    perfectCore (centralizer (Y : Set (adjointGroup .F4 K))) = C3Levi K := by
  have := finite_adjointGroup_F4 (K := K)
  obtain ⟨hcen, -, hYD⟩ := centralizer_nonsplit hYJ hcyc hY
  rw [hcen]
  exact perfectCore_sup_eq_of_le_centralizer (le_centralizer_self_of_isCyclic hcyc) hYD
    commutator_C3Levi_eq_self

theorem nonempty_perfectCore_centralizer_of_le_rootSL2 [Finite K] [CharP K 2]
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) {Y : Subgroup (adjointGroup .F4 K)}
    (hYJ : Y ≤ rootSL2 K γ) (hcyc : IsCyclic Y) (hY : Nat.card Y = Nat.card K + 1) :
    Nonempty (perfectCore (centralizer (Y : Set (adjointGroup .F4 K))) ≃* C3Levi K) := by
  have := finite_adjointGroup_F4 (K := K)
  have step : ∀ α : MulAut (adjointGroup .F4 K),
      (rootSL2 K γ).map α.toMonoidHom = rootSL2 K rootR →
      Nonempty (perfectCore (centralizer (Y : Set (adjointGroup .F4 K))) ≃* C3Levi K) := by
    intro α hα
    have hYα : Y.map α.toMonoidHom ≤ rootSL2 K rootR := hα ▸ map_mono hYJ
    have hYα' : Nat.card (Y.map α.toMonoidHom) = Nat.card K + 1 := by
      rw [card_map_of_injective α.injective, hY]
    have hJ : Y.map α.toMonoidHom ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) := by
      rw [highestRootRankOne_eq_rootSL2R]
      exact hYα
    obtain ⟨e2⟩ := nonempty_perfectCore_centralizer_map_mulAut α Y
    rw [perfectCore_centralizer_nonsplit hJ (isCyclic_map_mulAut α hcyc) hYα'] at e2
    exact ⟨e2.symm⟩
  have hcomp : ∀ a b : MulAut (adjointGroup .F4 K), (a * b).toMonoidHom =
      a.toMonoidHom.comp b.toMonoidHom := fun a b => MonoidHom.ext fun x => rfl
  rcases iform_self_eq_two_or_four hγ with hs | hl
  · obtain ⟨w, hw⟩ := exists_smul_eq_rootS hγ hs
    have : CharP K ReeTag.F4.prime := ‹CharP K 2›
    refine step ((graphAutF4 K)⁻¹ * MulAut.conj (weylRepC K w)) ?_
    rw [hcomp, ← Subgroup.map_map, map_conj_weylRepC_rootSL2 w hγ, hw,
      ← map_graphAutF4_rootSL2R, Subgroup.map_map, ← hcomp, inv_mul_cancel]
    exact Subgroup.map_id _
  · obtain ⟨w, hw⟩ := exists_smul_eq_rootR hγ hl
    refine step (MulAut.conj (weylRepC K w)) ?_
    rw [map_conj_weylRepC_rootSL2 w hγ, hw]

theorem nonempty_perfectCore_centralizer_of_le_mem_leviRootSL2s [Finite K] [CharP K 2]
    {κ : TwoCentral} {J Y : Subgroup (adjointGroup .F4 K)} (hJ : J ∈ leviRootSL2s K κ)
    (hYJ : Y ≤ J) (hcyc : IsCyclic Y) (hY : Nat.card Y = Nat.card K + 1) :
    Nonempty (perfectCore (centralizer (Y : Set (adjointGroup .F4 K))) ≃* C3Levi K) := by
  have := finite_adjointGroup_F4 (K := K)
  obtain ⟨γ, hγ, m, -, rfl⟩ := hJ
  obtain ⟨Y', hY'J, rfl⟩ := exists_le_map_eq_of_le_map (MulAut.conj m) hYJ
  have hcyc' : IsCyclic Y' :=
    (MulEquiv.isCyclic (Y'.equivMapOfInjective _ (MulAut.conj m).injective)).2 hcyc
  have hY' : Nat.card Y' = Nat.card K + 1 := by
    rw [← hY, card_map_of_injective (MulAut.conj m).injective]
  obtain ⟨e1⟩ := nonempty_perfectCore_centralizer_of_le_rootSL2 hγ.1 hY'J hcyc' hY'
  obtain ⟨e2⟩ := nonempty_perfectCore_centralizer_map_mulAut (MulAut.conj m) Y'
  exact ⟨e2.trans e1⟩

end F6

section LeviTwo


variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def leviQ2 : TwoCentral → Subgroup (adjointGroup .F4 K)
  | .t => levi K .t
  | .u => levi K .u
  | .tu => closure {c : adjointGroup .F4 K | c ∈ levi K .tu ∧ Odd (orderOf c)}

variable (K) in
@[expose] def FactF3PerfectTwo : Prop :=
  ∀ κ : TwoCentral, κ ≠ .tu →
    ⁅centralizer ({yRep K κ} : Set (adjointGroup .F4 K)),
        centralizer ({yRep K κ} : Set (adjointGroup .F4 K))⁆ =
      centralizer ({yRep K κ} : Set (adjointGroup .F4 K))

variable (K) in
@[expose] def FactF3TUTwo : Prop :=
  ∃ Q : Subgroup (adjointGroup .F4 K), IsPGroup 2 Q ∧
    perfectCore (centralizer ({yRep K .tu} : Set (adjointGroup .F4 K))) = Q ⊔ leviQ2 K .tu ∧
    Disjoint Q (leviQ2 K .tu) ∧ leviQ2 K .tu ≤ normalizer (Q : Set (adjointGroup .F4 K)) ∧
    ∀ N : Subgroup (leviQ2 K .tu), N.Normal → IsPGroup 2 N → N = ⊥

variable (K) in
@[expose] def FactZ3RootTUTwo : Prop :=
  ∀ Y : Subgroup (adjointGroup .F4 K), Y ≤ leviQ2 K .tu → Nat.card Y = 3 →
    ∃ J ∈ leviRootSL2s K .tu, Y ≤ J

theorem exists_decomp_leviQ2 [Finite K] [CharP K 2] (hF3p : FactF3PerfectTwo K)
    (hF3tu : FactF3TUTwo K) (κ : TwoCentral) :
    ∃ Q : Subgroup (adjointGroup .F4 K), IsPGroup 2 Q ∧
      perfectCore (centralizer ({yRep K κ} : Set (adjointGroup .F4 K))) = Q ⊔ leviQ2 K κ ∧
      Disjoint Q (leviQ2 K κ) ∧ leviQ2 K κ ≤ normalizer (Q : Set (adjointGroup .F4 K)) ∧
      ∀ N : Subgroup (leviQ2 K κ), N.Normal → IsPGroup 2 N → N = ⊥ := by
  have := finite_adjointGroup_F4 (K := K)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimple : ∀ κ : TwoCentral, κ ≠ .tu → IsSimpleGroup (levi K κ) := by
    intro κ hκ
    have := isSimpleGroup_C3Levi (K := K)
    cases κ
    · exact ((leviModelT K).equiv.symm.trans (c3LeviEquiv K)).isSimpleGroup
    · exact ((leviModelU K).equiv.symm.trans (c3LeviEquiv K)).isSimpleGroup
    · exact absurd rfl hκ
  have key : ∀ κ : TwoCentral, κ ≠ .tu → ∃ Q : Subgroup (adjointGroup .F4 K), IsPGroup 2 Q ∧
      perfectCore (centralizer ({yRep K κ} : Set (adjointGroup .F4 K))) = Q ⊔ levi K κ ∧
      Disjoint Q (levi K κ) ∧ levi K κ ≤ normalizer (Q : Set (adjointGroup .F4 K)) ∧
      ∀ N : Subgroup (levi K κ), N.Normal → IsPGroup 2 N → N = ⊥ := by
    intro κ hκ
    obtain ⟨Q, hQp, hQM, hinf, hMQ⟩ := factF3 (K := K) κ
    have hperf := hF3p κ hκ
    refine ⟨Q, hQp, ?_, disjoint_iff.2 hinf, hMQ, ?_⟩
    · rw [perfectCore_eq_self_of_perfect hperf, hQM]
    · exact EPilot.forall_normal_isPGroup_eq_bot_of_isSimpleGroup_of_perfect hQp hMQ
        (hsimple κ hκ) (by rw [hQM]; exact hperf)
  cases κ
  · exact key .t (by decide)
  · exact key .u (by decide)
  · exact hF3tu

theorem le_leviQ2_of_le_rootSL2 [Finite K] {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ₀ : X₀ ≤ rootSL2 K rootR) (hX₀ : Odd (Nat.card X₀)) (κ : TwoCentral) :
    X₀ ≤ leviQ2 K κ := by
  have := finite_adjointGroup_F4 (K := K)
  cases κ
  · exact hXJ₀.trans (rootSL2_rootR_le_levi .t)
  · exact hXJ₀.trans (rootSL2_rootR_le_levi .u)
  · intro x hx
    refine subset_closure ⟨rootSL2_rootR_le_levi .tu (hXJ₀ hx), ?_⟩
    have h := orderOf_dvd_natCard (⟨x, hx⟩ : X₀)
    rw [Subgroup.orderOf_mk] at h
    exact Odd.of_dvd_nat hX₀ h

theorem natCard_leviQ2_tu_lt [Finite K] [CharP K 2] {κ : TwoCentral} (hκ : κ ≠ .tu) :
    Nat.card (leviQ2 K .tu) < Nat.card (levi K κ) := by
  have := finite_adjointGroup_F4 (K := K)
  have hle : leviQ2 K .tu ≤ levi K .tu := (Subgroup.closure_le _).2 fun c hc => hc.1
  calc Nat.card (leviQ2 K .tu) ≤ Nat.card (levi K .tu) := Subgroup.card_le_of_le hle
    _ < Nat.card (levi K κ) := by
      rw [natCard_levi_tu K, natCard_levi_of_ne_tu K hκ]
      exact natCard_statedSp_two_lt_three K

theorem nonempty_perfectCore_centralizer_leviQ2 [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (hZ3 : FactZ3RootTUTwo K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ₀ : X₀ ≤ rootSL2 K rootR) (hX₀ : Nat.card X₀ = 3) (hX₀M : ∀ κ, X₀ ≤ leviQ2 K κ)
    (κ κ' : TwoCentral) (ι : leviQ2 K κ ≃* leviQ2 K κ') :
    Nonempty (perfectCore (centralizer ((((X₀.subgroupOf (leviQ2 K κ)).map ι.toMonoidHom).map
      (leviQ2 K κ').subtype : Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K))) ≃*
        C3Levi K) := by
  have := finite_adjointGroup_F4 (K := K)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y := ((X₀.subgroupOf (leviQ2 K κ)).map ι.toMonoidHom).map (leviQ2 K κ').subtype with hYdef
  have hYcard : Nat.card Y = 3 := by
    rw [hYdef, card_map_of_injective (leviQ2 K κ').subtype_injective,
      card_map_of_injective ι.injective,
      Nat.card_congr (subgroupOfEquivOfLe (hX₀M κ)).toEquiv, hX₀]
  have hYcyc : IsCyclic Y := isCyclic_of_prime_card hYcard
  have hY3 : Nat.card Y = Nat.card K + 1 := by rw [hYcard, hK]
  suffices h : ∃ J ∈ leviRootSL2s K κ', Y ≤ J by
    obtain ⟨J, hJ, hYJ⟩ := h
    exact nonempty_perfectCore_centralizer_of_le_mem_leviRootSL2s hJ hYJ hYcyc hY3
  have hsub : ∀ {M : Subgroup (adjointGroup .F4 K)},
      X₀.subgroupOf M ≤ (rootSL2 K rootR).subgroupOf M := by
    intro M x hx
    rw [mem_subgroupOf] at hx ⊢
    exact hXJ₀ hx
  have hF5 : ∀ {κ₁ κ₂ : TwoCentral} (ι' : levi K κ₁ ≃* levi K κ₂),
      ∃ J ∈ leviRootSL2s K κ₂,
        ((X₀.subgroupOf (levi K κ₁)).map ι'.toMonoidHom).map (levi K κ₂).subtype ≤ J :=
    fun {κ₁ κ₂} ι' => ⟨_, factF5 K κ₁ κ₂ ι' (rootSL2 K rootR)
      (rootSL2_mem_leviRootSL2s (rootR_mem_phi0 κ₁)), map_mono (map_mono hsub)⟩
  have hmix : ∀ {κ₁ : TwoCentral}, κ₁ ≠ .tu → ¬ Nonempty (levi K κ₁ ≃* leviQ2 K .tu) := by
    rintro κ₁ hκ₁ ⟨ι'⟩
    have h := Nat.card_congr ι'.toEquiv
    exact absurd h (natCard_leviQ2_tu_lt hκ₁).ne'
  cases κ <;> cases κ'
  · exact hF5 ι
  · exact hF5 ι
  · exact absurd ⟨ι⟩ (hmix (by decide))
  · exact hF5 ι
  · exact hF5 ι
  · exact absurd ⟨ι⟩ (hmix (by decide))
  · exact absurd ⟨ι.symm⟩ (hmix (by decide))
  · exact absurd ⟨ι.symm⟩ (hmix (by decide))
  · exact hZ3 Y (map_subtype_le _) hYcard

end LeviTwo

section PerfectTwo

open RootOps

theorem centralizer_singleton_mulAut {G : Type*} [Group G] (α : MulAut G) (z : G) :
    centralizer ({α z} : Set G) = (centralizer ({z} : Set G)).map α.toMonoidHom := by
  ext x
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro hx
    have := congrArg α.symm hx
    simpa using this
  · intro hx
    have := congrArg α hx
    simpa using this

theorem commutator_centralizer_mulAut {G : Type*} [Group G] (α : MulAut G) {z : G}
    (h : ⁅centralizer ({z} : Set G), centralizer ({z} : Set G)⁆ = centralizer ({z} : Set G)) :
    ⁅centralizer ({α z} : Set G), centralizer ({α z} : Set G)⁆ = centralizer ({α z} : Set G) := by
  rw [centralizer_singleton_mulAut, ← Subgroup.map_commutator, h]

theorem C3Roots_mem_f4ParabolicOne :
    ∀ β ∈ C3Roots, ∃ p ∈ f4ParabolicOne, List.ofFn (orbitCertRoot .F4 p) = List.ofFn β := by
  decide +kernel


variable {K : Type} [Field K]

open CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCover (xr)

theorem commutator_centralizer_zT_two [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    ⁅centralizer ({zT K} : Set (adjointGroup .F4 K)),
        centralizer ({zT K} : Set (adjointGroup .F4 K))⁆ =
      centralizer ({zT K} : Set (adjointGroup .F4 K)) := by
  have : Finite (ModGL .F4 K) := finite_modGL
  obtain ⟨hder, hcov, hcomm⟩ := f4ParabolicOne_check
  set P : Subgroup (adjointGroup .F4 K) :=
    closure ((fun p => xr (K := K) (orbitCertRoot .F4 p)) '' {p | p ∈ f4ParabolicOne}) with hP
  have hgen : ∀ p ∈ f4ParabolicOne, xr (K := K) (orbitCertRoot .F4 p) ∈ P :=
    fun p hp => subset_closure ⟨p, hp, rfl⟩
  have hPt : P ≤ centralizer ({zT K} : Set (adjointGroup .F4 K)) := by
    rw [hP, Subgroup.closure_le]
    rintro _ ⟨p, hp, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    obtain ⟨hp48, h47 | hc⟩ := hcomm p hp
    · rw [h47]
      rfl
    · exact f4_commute_sound hK hp48 (by norm_num) hc
  have hperf : P ≤ ⁅P, P⁆ := by
    rw [hP, Subgroup.closure_le]
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (hcov p hp)
    exact f4_deriv_sound hK hgen hgen f4ParabolicOneDeriv [] (by simp) hder s hs
  obtain ⟨-, hQM, -, -⟩ := isTwoRadicalDecomp_zT (K := K)
  have hQ : radicalT K ≤ P := by
    intro u hu
    rw [radicalT, mem_subgroupOf] at hu
    exact mem_of_mem_posUnipotent_of_forall_xr hK
      (fun p hp hp' => hgen p (List.mem_range'_1.2 ⟨by omega, by omega⟩))
      (parabolicRadical_le_posUnipotent _ hu)
  have hD : C3Levi K ≤ P := by
    intro d hd
    rw [mem_C3Levi_iff_mem_rootSpan_C3Set] at hd
    have hle : rootSpan .F4 K C3Set ≤ P.map (adjointGroup .F4 K).subtype := by
      rw [rootSpan_eq_closure, Subgroup.closure_le]
      rintro _ ⟨β, hβ, c, rfl⟩
      obtain ⟨p, hp, hpβ⟩ := C3Roots_mem_f4ParabolicOne β hβ
      obtain rfl := List.ofFn_injective hpβ
      rcases eq_zero_or_eq_one_of_card_eq_two hK c with rfl | rfl
      · rw [pinnedX_zero]
        exact one_mem _
      · exact ⟨_, hgen p hp, rfl⟩
    obtain ⟨x, hx, hxd⟩ := hle hd
    rwa [show d = x from Subtype.ext hxd.symm]
  have heq : centralizer ({zT K} : Set (adjointGroup .F4 K)) = P :=
    le_antisymm (hQM ▸ sup_le hQ hD) hPt
  rw [heq]
  exact le_antisymm (CFSG.Quasithin.A3.commutator_self_le P) hperf

theorem factF3PerfectTwo [Finite K] [CharP K 2] (hK : Nat.card K = 2) : FactF3PerfectTwo K := by
  intro κ hκ
  obtain ⟨hT, hU, -⟩ := conj_nD_zT_zU (K := K)
  have h0 := commutator_centralizer_zT_two hK
  cases κ
  · rw [← hT]
    exact commutator_centralizer_mulAut _ h0
  · rw [← hU, ← graphAutF4_zT]
    exact commutator_centralizer_mulAut _ (commutator_centralizer_mulAut _ h0)
  · exact absurd rfl hκ

end PerfectTwo

section Skeleton

variable {G : Type} [Group G] {L : Subgroup G}

@[expose] def conjugateEquivSelf (L : Subgroup G) (x : G) : CFSG.conjugate L x ≃* L where
  toFun u := ⟨x * u * x⁻¹, SeitzQ2.mem_conjugate_iff_conj_mem.1 u.2⟩
  invFun l := ⟨x⁻¹ * l * x, SeitzQ2.mem_conjugate_iff_conj_mem.2 (by
    have e : x * (x⁻¹ * (l : G) * x) * x⁻¹ = l := by group
    rw [e]
    exact l.2)⟩
  left_inv u := Subtype.ext (by simp only; group)
  right_inv l := Subtype.ext (by simp only; group)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem exists_le_range_inf_centralizer_perfectCore_of_le_conj {C' : Type*} [Group C']
    {φ' : C' →* G} (hφ' : Function.Injective φ') {J' : Subgroup C'} {X : Subgroup G} {q₀ : G}
    (hq₀ : q₀ ∈ φ'.range) (hX : X ≤ (J'.map φ').map (MulAut.conj q₀).toMonoidHom) :
    ∃ P : Subgroup G, P ≤ φ'.range ⊓ centralizer (X : Set G) ∧
      Nonempty (P ≃* perfectCore (centralizer (J' : Set C'))) := by
  refine ⟨((perfectCore (centralizer (J' : Set C'))).map φ').map (MulAut.conj q₀).toMonoidHom,
    le_inf ?_ ?_, ?_⟩
  · rintro _ ⟨_, ⟨c, -, rfl⟩, rfl⟩
    obtain ⟨n', rfl⟩ := hq₀
    exact ⟨n' * c * n'⁻¹, by simp [MulAut.conj_apply]⟩
  · rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨_, ⟨j, hj, rfl⟩, hjx⟩ := hX hx
    have hcj := mem_centralizer_iff.1 (perfectCore_le _ hc) j hj
    have hφc : φ' j * φ' c = φ' c * φ' j := by rw [← map_mul, ← map_mul, hcj]
    rw [← hjx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc q₀ * φ' j * q₀⁻¹ * (q₀ * φ' c * q₀⁻¹) = q₀ * (φ' j * φ' c) * q₀⁻¹ := by group
      _ = q₀ * (φ' c * φ' j) * q₀⁻¹ := by rw [hφc]
      _ = q₀ * φ' c * q₀⁻¹ * (q₀ * φ' j * q₀⁻¹) := by group
  · exact ⟨(((perfectCore (centralizer (J' : Set C'))).map φ').equivMapOfInjective _
      (MulAut.conj q₀).injective).symm.trans
      ((perfectCore (centralizer (J' : Set C'))).equivMapOfInjective _ hφ').symm⟩

variable [Finite G]

theorem exists_le_centralizer_perfectCore_of_twoSided (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {C : Type*} [Group C] (e : L ≃* C) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {x z : G} (hzL : z ∈ L)
    (hzLx : z ∈ CFSG.conjugate L x) (hxt : x⁻¹ * t * x = t * z) (hz1 : z ≠ 1)
    (hzU : ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u)
    (hzU' : ∃ U' : Sylow 2 (CFSG.conjugate L x),
      ∀ u ∈ (U' : Subgroup (CFSG.conjugate L x)), (u : G) * z = z * u)
    (hact : ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹)
    {κ : Type*} (rep : κ → C)
    (hF2 : ∀ (U : Sylow 2 C) (w : C), (∀ u ∈ (U : Subgroup C), u * w = w * u) → w ≠ 1 →
      ∃ (k : κ) (c : C), c * w * c⁻¹ = rep k)
    (Q M : κ → Subgroup C)
    (hF3 : ∀ k, perfectCore (centralizer ({rep k} : Set C)) = Q k ⊔ M k)
    (hQ : ∀ k, IsPGroup 2 (Q k)) (hMN : ∀ k, M k ≤ normalizer (Q k : Set C))
    (hQM : ∀ k, Disjoint (Q k) (M k))
    (hM : ∀ k, ∀ N : Subgroup (M k), N.Normal → IsPGroup 2 N → N = ⊥)
    {J : Subgroup C} (hJ : ∀ k, J ≤ M k) {D : Type*} [Group D]
    (hF56 : ∀ (k k' : κ) (ι : M k ≃* M k'), Nonempty (perfectCore (centralizer
      ((((J.subgroupOf (M k)).map ι.toMonoidHom).map (M k').subtype : Subgroup C) : Set C)) ≃* D))
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ (J.map e.symm.toMonoidHom).map L.subtype) :
    ∃ (k : κ) (g : G), rep k ≠ 1 ∧ g⁻¹ * t * g = t * (e.symm (rep k) : G) ∧
      ∃ P : Subgroup G, P ≤ centralizer (X : Set G) ⊓ centralizer ({g⁻¹ * t * g} : Set G) ∧
        Nonempty (P ≃* D) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : C →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hφr : φ.range = L := by
    ext g
    constructor
    · rintro ⟨c, rfl⟩
      exact (e.symm c).2
    · intro hg
      exact ⟨e ⟨g, hg⟩, by simp [hφdef]⟩
  have hφL : ∀ c : C, φ c ∈ L := fun c => hφr ▸ ⟨c, rfl⟩
  obtain ⟨U, hU⟩ := hzU
  set zC : C := e ⟨z, hzL⟩ with hzC
  have hφz : φ zC = z := by simp [hφdef, hzC]
  have hzC1 : zC ≠ 1 := fun h => hz1 (by rw [← hφz, h, map_one])
  have hzCU : ∀ u ∈ ((U.mapSurjective (f := e.toMonoidHom) e.surjective : Sylow 2 C) :
      Subgroup C), u * zC = zC * u := by
    intro u hu
    change u ∈ (U : Subgroup L).map e.toMonoidHom at hu
    obtain ⟨v, hv, rfl⟩ := hu
    simp only [MulEquiv.coe_toMonoidHom]
    rw [hzC, ← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (hU v hv))
  obtain ⟨k, c, hc⟩ := hF2 _ zC hzCU hzC1
  have hrep1 : rep k ≠ 1 := by
    intro h1
    apply hzC1
    have : zC = c⁻¹ * (c * zC * c⁻¹) * c := by group
    rw [this, hc, h1]
    group
  set l : G := φ c with hldef
  set g₁ : G := x * l⁻¹ with hg₁def
  set y : G := φ (rep k) with hydef
  have hy : y = l * z * l⁻¹ := by rw [hydef, ← hc, map_mul, map_mul, map_inv, hφz]
  have htl : l * t = t * l := mem_centralizer_iff.1 htC l (hφL c)
  have htl' : l * t * l⁻¹ = t := by rw [htl, mul_inv_cancel_right]
  have hg₁ : g₁⁻¹ * t * g₁ = t * y := by
    calc g₁⁻¹ * t * g₁ = l * (x⁻¹ * t * x) * l⁻¹ := by rw [hg₁def]; group
      _ = l * t * z * l⁻¹ := by rw [hxt, mul_assoc l t z]
      _ = t * (l * z * l⁻¹) := by rw [htl]; group
      _ = t * y := by rw [hy]
  obtain ⟨U', hU'⟩ := hzU'
  set ψ : CFSG.conjugate L x ≃* C := (conjugateEquivSelf L x).trans e with hψ
  have hφψ : ∀ u : CFSG.conjugate L x, φ (ψ u) = x * u * x⁻¹ := by
    intro u
    simp [hφdef, hψ, conjugateEquivSelf]
  set w : C := ψ ⟨z, hzLx⟩ with hw
  have hwU : ∀ u ∈ ((U'.mapSurjective (f := ψ.toMonoidHom) ψ.surjective : Sylow 2 C) :
      Subgroup C), u * w = w * u := by
    intro u hu
    change u ∈ (U' : Subgroup (CFSG.conjugate L x)).map ψ.toMonoidHom at hu
    obtain ⟨v, hv, rfl⟩ := hu
    simp only [MulEquiv.coe_toMonoidHom]
    rw [hw, ← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext (hU' v hv))
  have hw1 : w ≠ 1 := by
    intro h
    apply hz1
    have h' : (⟨z, hzLx⟩ : CFSG.conjugate L x) = 1 := ψ.injective (h.trans (map_one ψ).symm)
    exact congrArg Subtype.val h'
  obtain ⟨k', c', hc'⟩ := hF2 _ w hwU hw1
  set φ'₀ : C →* G := (MulAut.conj g₁⁻¹).toMonoidHom.comp φ with hφ'₀def
  have hφ'₀ : Function.Injective φ'₀ := (MulAut.conj g₁⁻¹).injective.comp hφ
  have hφ'₀r : φ'₀.range = CFSG.conjugate L g₁ := by
    rw [hφ'₀def, MonoidHom.range_comp, hφr]
    rfl
  set φ' : C →* G := φ'₀.comp (MulAut.conj c'⁻¹).toMonoidHom with hφ'def
  have hφ' : Function.Injective φ' := hφ'₀.comp (MulAut.conj c'⁻¹).injective
  have hφ'r : φ'.range = CFSG.conjugate L g₁ := by
    rw [hφ'def, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulAut.conj c'⁻¹).surjective,
      ← MonoidHom.range_eq_map, hφ'₀r]
  have hφ'rep : φ' (rep k') = y := by
    have h1 : (MulAut.conj c'⁻¹).toMonoidHom (rep k') = w := by
      rw [← hc']
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [hφ'def, MonoidHom.comp_apply, h1, hφ'₀def, MonoidHom.comp_apply, hw, hφψ]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hy, hg₁def]
    group
  have hact' : ∀ m ∈ CFSG.conjugate L g₁, t * m * t⁻¹ = φ' (rep k') * m * (φ' (rep k'))⁻¹ := by
    intro m hm
    rw [hφ'rep, hy]
    have hm' : l⁻¹ * m * l ∈ CFSG.conjugate L x := by
      rw [SeitzQ2.mem_conjugate_iff_conj_mem] at hm ⊢
      have e' : x * (l⁻¹ * m * l) * x⁻¹ = g₁ * m * g₁⁻¹ := by rw [hg₁def]; group
      rw [e']
      exact hm
    have h := hact _ hm'
    calc t * m * t⁻¹ = (l * t * l⁻¹) * m * (l * t * l⁻¹)⁻¹ := by rw [htl']
      _ = l * (t * (l⁻¹ * m * l) * t⁻¹) * l⁻¹ := by group
      _ = l * (z * (l⁻¹ * m * l) * z⁻¹) * l⁻¹ := by rw [h]
      _ = l * z * l⁻¹ * m * (l * z * l⁻¹)⁻¹ := by group
  have hΛ := EPilot.map_perfectCore_centralizer_eq_of_inner hset hOut htC ht hφ hφr hφ' hφ'r
    (Or.inr hg₁) hact'
  rw [hF3 k, hF3 k'] at hΛ
  have hXJ' : X ≤ J.map φ := by
    rw [hφdef, ← Subgroup.map_map]
    exact hXJ
  obtain ⟨hQeq, ι, -, q₀, hq₀, hXq⟩ := EPilot.exists_conj_le_map_of_two_decompositions hφ hφ'
    (hQ k) (hQ k') (hM k) (hM k') (hMN k) (hMN k') (hQM k) (hQM k') hΛ (hJ k) hXJ'
    (fun h => (Nat.not_even_iff_odd.2 hXodd) (even_iff_two_dvd.2 h))
  have hq₀' : q₀ ∈ φ'.range := by
    rw [hQeq] at hq₀
    obtain ⟨n, -, rfl⟩ := hq₀
    exact ⟨n, rfl⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := exists_le_range_inf_centralizer_perfectCore_of_le_conj hφ' hq₀' hXq
  obtain ⟨eD⟩ := hF56 k k' ι
  refine ⟨k, g₁, hrep1, hg₁, P, le_inf (hP.trans inf_le_right) ?_, ⟨eP.trans eD⟩⟩
  exact (hP.trans inf_le_left).trans (hφ'r ▸ EPilot.conjugate_le_centralizer_conj htC g₁)

theorem not_normal_map_oddCore_of_twoSided (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {C : Type*} [Group C] (e : L ≃* C) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {x z : G} (hzL : z ∈ L)
    (hzLx : z ∈ CFSG.conjugate L x) (hxt : x⁻¹ * t * x = t * z) (hz1 : z ≠ 1)
    (hzU : ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u)
    (hzU' : ∃ U' : Sylow 2 (CFSG.conjugate L x),
      ∀ u ∈ (U' : Subgroup (CFSG.conjugate L x)), (u : G) * z = z * u)
    (hact : ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹)
    {κ : Type*} (rep : κ → C)
    (hF2 : ∀ (U : Sylow 2 C) (w : C), (∀ u ∈ (U : Subgroup C), u * w = w * u) → w ≠ 1 →
      ∃ (k : κ) (c : C), c * w * c⁻¹ = rep k)
    (Q M : κ → Subgroup C)
    (hF3 : ∀ k, perfectCore (centralizer ({rep k} : Set C)) = Q k ⊔ M k)
    (hQ : ∀ k, IsPGroup 2 (Q k)) (hMN : ∀ k, M k ≤ normalizer (Q k : Set C))
    (hQM : ∀ k, Disjoint (Q k) (M k))
    (hM : ∀ k, ∀ N : Subgroup (M k), N.Normal → IsPGroup 2 N → N = ⊥)
    {J : Subgroup C} (hJ : ∀ k, J ≤ M k) {DC : Subgroup C} (hrepD : ∀ k, rep k ∈ DC)
    (hF56 : ∀ (k k' : κ) (ι : M k ≃* M k'), Nonempty (perfectCore (centralizer
      ((((J.subgroupOf (M k)).map ι.toMonoidHom).map (M k').subtype : Subgroup C) : Set C)) ≃* DC))
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ (J.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    (hDX : (DC.map e.symm.toMonoidHom).map L.subtype ≤ centralizer (X : Set G))
    (hDq : CFSG.Open.IsQuasisimple ((DC.map e.symm.toMonoidHom).map L.subtype))
    (hZD : center ((DC.map e.symm.toMonoidHom).map L.subtype) = ⊥)
    (hOutD : Group.IsSolvable (Outer ((DC.map e.symm.toMonoidHom).map L.subtype)))
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((((DC.map e.symm.toMonoidHom).map L.subtype).subgroupOf
          (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2) :
    ¬ ((((DC.map e.symm.toMonoidHom).map L.subtype).subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  obtain ⟨k, g, hrep1, hg, P, hP, ⟨eP⟩⟩ := exists_le_centralizer_perfectCore_of_twoSided hset
    hOut e htC ht hzL hzLx hxt hz1 hzU hzU' hact rep hF2 Q M hF3 hQ hMN hQM hM hJ hF56 hXodd hXJ
  set DG := (DC.map e.symm.toMonoidHom).map L.subtype with hDG
  have hDGL : DG ≤ L := map_subtype_le _
  have hDt : DG ≤ centralizer ({t} : Set G) := hDGL.trans (le_centralizer_of_mem_centralizer htC)
  have hyD : (e.symm (rep k) : G) ∈ DG := ⟨e.symm (rep k), ⟨rep k, hrepD k, rfl⟩, rfl⟩
  have hy1 : (e.symm (rep k) : G) ≠ 1 := by
    intro h
    apply hrep1
    have h' : e.symm (rep k) = 1 := Subtype.ext h
    rw [← e.apply_symm_apply (rep k), h', map_one]
  have eDG : DC ≃* DG :=
    (DC.equivMapOfInjective _ e.symm.injective).trans
      ((DC.map e.symm.toMonoidHom).equivMapOfInjective _ L.subtype_injective)
  exact not_normal_map_oddCore_centralizer_of_mulEquiv htX ht hDX hDq hZD hOutD hDt hsyl hyD hy1
    (Or.inr hg) hP ⟨eP.trans eDG⟩

end Skeleton

section Main


theorem not_normal_map_oddCore_nonsplit_two {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) {K : Type} [Field K] (hK : Nat.card K = 2)
    (e : L ≃* adjointGroup .F4 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hF3tu : FactF3TUTwo K) (hZ3 : FactZ3RootTUTwo K)
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ₀ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hX₀ : Nat.card X₀ = 3)
    {X : Subgroup G} (hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP K 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  have := finite_adjointGroup_F4 (K := K)
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have htC : t ∈ centralizer (L : Set G) :=
    (show t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) from hKt ▸ mem_zpowers t).1
  have hOut : Group.IsSolvable (Outer L) := by
    have := (SeitzQ2.card_outer_le_two_of_mulEquiv_F4_two hK e).1
    have : Group.IsNilpotent (Outer L) :=
      (SeitzQ2.isPGroup_outer_of_mulEquiv_F4_two hK e).isNilpotent
    infer_instance
  obtain ⟨x, z, ⟨hzL, hzLx⟩, hxt, hz1, hzU, hzU', hact⟩ :=
    exists_conj_eq_mul_twoCentral_twoSided_F4_two hset hK e ht hKt
  choose Q hQ using exists_decomp_leviQ2 (factF3PerfectTwo hK) hF3tu
  have hXJ₀' : X₀ ≤ rootSL2 K rootR := by
    rw [rootSL2_rootR, ← highestRootRankOne_eq_rootSL2R]
    exact hXJ₀
  have hX₀odd : Odd (Nat.card X₀) := by rw [hX₀]; decide
  have hX₀M : ∀ κ, X₀ ≤ leviQ2 K κ := le_leviQ2_of_le_rootSL2 hXJ₀' hX₀odd
  have hcyc : IsCyclic X₀ := isCyclic_of_prime_card hX₀
  have hX₀' : Nat.card X₀ = Nat.card K + 1 := by rw [hX₀, hK]
  have hXL : X ≤ L := by rw [hX]; exact map_subtype_le _
  have htX : t ∈ centralizer (X : Set G) := centralizer_le hXL htC
  have hXodd : Odd (Nat.card X) := by
    rw [hX, card_map_of_injective L.subtype_injective, card_map_of_injective e.symm.injective]
    exact hX₀odd
  have hsyl := (neighbour_standard_nonsplit hset.standard htC ht hKt hK1 e hXJ₀ hcyc hX₀' hX htX
    hDe).2.1
  obtain ⟨-, -, hX₀D⟩ := centralizer_nonsplit hXJ₀ hcyc hX₀'
  subst hX hDe
  have hDX : ((C3Levi K).map e.symm.toMonoidHom).map L.subtype ≤
      centralizer (((X₀.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G) := by
    rw [Subgroup.map_map, Subgroup.map_map]
    exact map_le_centralizer_map _ (Subgroup.le_centralizer_iff.1 hX₀D)
  have eD : C3Levi K ≃* ((C3Levi K).map e.symm.toMonoidHom).map L.subtype :=
    ((C3Levi K).equivMapOfInjective _ e.symm.injective).trans
      (((C3Levi K).map e.symm.toMonoidHom).equivMapOfInjective _ L.subtype_injective)
  exact not_normal_map_oddCore_of_twoSided hset hOut e htC ht hzL hzLx hxt hz1 hzU hzU' hact
    (yRep K) (fun U w hw hw1 => factF2 U w (mem_centralizer_iff.2 hw) hw1) Q (leviQ2 K)
    (fun κ => (hQ κ).2.1) (fun κ => (hQ κ).1) (fun κ => (hQ κ).2.2.2.1) (fun κ => (hQ κ).2.2.1)
    (fun κ => (hQ κ).2.2.2.2) hX₀M yRep_mem_C3Levi
    (nonempty_perfectCore_centralizer_leviQ2 hK hZ3 hXJ₀' hX₀ hX₀M) hXodd le_rfl htX hDX
    (isQuasisimple_open_map_C3Levi e) (center_eq_bot_congr eD center_C3Levi_eq_bot)
    ((CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism eD).2.1
      (isSolvable_outer_C3Levi hK1)) hsyl

end Main

end CFSG.SeitzReduction.F4Pilot
