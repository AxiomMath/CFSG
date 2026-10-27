module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Rows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamField
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotUniqueBasic
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer solvable_of_equiv)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore OddSchurTrivial HasBLift statedSpMap
  statedSpMap_injective)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)

section Fix

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

omit [Finite G] in
theorem modelToG_complSp_le_centralizerPerfectCore_nsTorusSp {m : ℕ} (hK : Nat.card K = 2)
    (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) (k : Fin (m + 1)) :
    modelToG e (complSp K k) ≤ centralizerPerfectCore (modelToG e (nsTorusSp K k)) := by
  have hperf : ⁅complSp K k, complSp K k⁆ = complSp K k :=
    isPerfect_iff.mp (isQuasisimple_complSp_two hK hm k).1
  exact CFSG.Quasithin.le_perfectCore_of_perfect
    (UnitaryPilot.modelToG_le_centralizer e (complSp_le_centralizer_nsTorusSp k))
    (UnitaryPilot.modelToG_perfect e hperf)

theorem perfectCore_centralizerPerfectCore_nsTorusSp_inf_centralizer {m : ℕ}
    (hset : SeitzSetting G L) (hK : Nat.card K = 2) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (m + 1)) :
    perfectCore (centralizerPerfectCore (modelToG e (nsTorusSp K k)) ⊓
        centralizer ({t} : Set G)) = modelToG e (complSp K k) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow (f := 1) (by rw [hK, pow_one])
  have hcompl : ⁅complSp K k, complSp K k⁆ = complSp K k :=
    isPerfect_iff.mp (isQuasisimple_complSp_two hK hm k).1
  have hDperf := UnitaryPilot.modelToG_perfect e hcompl
  have hDE := modelToG_complSp_le_centralizerPerfectCore_nsTorusSp hK hm e k
  have hDt : modelToG e (complSp K k) ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (UnitaryPilot.modelToG_le e _ hd))
  refine le_antisymm ?_ (CFSG.Quasithin.le_perfectCore_of_perfect (le_inf hDE hDt) hDperf)
  have hP := CFSG.Quasithin.perfectCore_perfect
    (centralizerPerfectCore (modelToG e (nsTorusSp K k)) ⊓ centralizer ({t} : Set G))
  have hPt : perfectCore (centralizerPerfectCore (modelToG e (nsTorusSp K k)) ⊓
      centralizer ({t} : Set G)) ≤ centralizer ({t} : Set G) :=
    (CFSG.Quasithin.perfectCore_le _).trans inf_le_right
  have hOut : Group.IsSolvable (Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp (by omega : 3 ≤ m + 1) e)
  have hPL := std_perfect_le hset.standardSetting hOut htC ht hP hPt
  have hPX : perfectCore (centralizerPerfectCore (modelToG e (nsTorusSp K k)) ⊓
      centralizer ({t} : Set G)) ≤ centralizer (modelToG e (nsTorusSp K k) : Set G) :=
    (CFSG.Quasithin.perfectCore_le _).trans
      (inf_le_left.trans (F4Pilot.centralizerPerfectCore_le_centralizer _))
  have hPLX := le_inf hPL hPX
  rw [UnitaryPilot.inf_centralizer_modelToG, (centralizer_nsTorusSp hK k).1,
    UnitaryPilot.modelToG_sup] at hPLX
  have hXD : modelToG e (nsTorusSp K k) ≤ centralizer (modelToG e (complSp K k) : Set G) :=
    UnitaryPilot.modelToG_le_centralizer e
      (le_centralizer_iff.mp (complSp_le_centralizer_nsTorusSp k))
  have hXX : modelToG e (nsTorusSp K k) ≤ centralizer (modelToG e (nsTorusSp K k) : Set G) :=
    UnitaryPilot.modelToG_le_centralizer e (nsTorusSp_le_centralizer_self k)
  have hXsolv : Group.IsSolvable (modelToG e (nsTorusSp K k)) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (mem_centralizer_iff.1 (hXX b.2) a a.2)
  exact perfect_le_of_le_sup (hXD.trans (centralizer_le_normalizer _)) hXsolv hP
    (by rw [sup_comm]; exact hPLX)

end Fix

section Lift


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_centralizerPerfectCore_mulEquiv_of_field_nsTorusSp {m : ℕ}
    (hset : SeitzSetting G L) (hK : Nat.card K = 2) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (m + 1))
    {X : Subgroup G} (hX : X = modelToG e (nsTorusSp K k)) {D : Subgroup G}
    (hD : D = modelToG e (complSp K k)) (h : HR8KindAtSp t m 1 X D .field)
    (hN : t ∈ normalizer (centralizerPerfectCore X : Set G)) :
    ∃ (F' : Type) (_ : Field F') (_ : Finite F') (_ : CharP F' 2), Nat.card F' = 2 ^ (2 * 1) ∧
      Nonempty (StatedSp m F' ≃* centralizerPerfectCore X) ∧
      (centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ ∉
        (MulAut.conj : centralizerPerfectCore X →* MulAut (centralizerPerfectCore X)).range := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow (f := 1) (by rw [hK, pow_one])
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨htX, Kb, hKb, -, hcase⟩ := h
  obtain ⟨-, -, hlt, hsK, hsN, hov, hty⟩ := hcase.resolve_right fun h => by cases h.1
  have hty' : LieModel (Kb ⧸ center Kb) .PSp m 2 (2 * 1) := hty
  obtain ⟨F', _, _, _, hF', ⟨eF⟩⟩ := exists_mulEquiv_statedSp_of_lieModel hty'
  have hKbP : Group.IsPerfect Kb := hKb.1.1
  obtain ⟨eK⟩ := nonempty_mulEquiv_statedSp_of_centerQuotient_of_odd hKbP hov.2.1 eF
  have ht' : (⟨t, htX⟩ : centralizer (X : Set G)) * ⟨t, htX⟩ = 1 := Subtype.ext htt
  have hsC : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∉
      centralizer (Kb : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) := by
    intro hc
    refine hov.1 ⟨1, MulEquiv.ext fun k => Subtype.ext ?_⟩
    rw [map_one, MulAut.one_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
      ← mem_centralizer_iff.1 hc k k.2, mul_inv_cancel_right]
  have hs1 : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ≠ 1 :=
    fun h1 => hsK (h1 ▸ one_mem Kb)
  have hs2 : orderOf (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩) = 2 :=
    orderOf_eq_prime (by rw [sq, ← map_mul, ht', map_one]) hs1
  have hDt : D ≤ centralizer ({t} : Set G) := by
    rw [hD]
    exact fun d hd => mem_centralizer_singleton_iff.2
      (mem_centralizer_iff.1 htC d (UnitaryPilot.modelToG_le e _ hd))
  have hsD : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      centralizer (((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) : Subgroup _) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_nsTorusSp_of_seitzSetting hset hK hm e htC ht k
    hX htX hD
  have hOut : Group.IsSolvable (Outer Kb) := by
    have : Group.IsSolvable (Outer (StatedSp m F')) := isSolvable_outer_statedSp (by omega)
    exact solvable_of_equiv eK.symm
  have hcore := LinearPilot.perfectCore_top_eq_of_isComponent
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hKb hlt.le hs2 hsD hsN hsC hsyl hOut
  obtain ⟨-, -, hBall⟩ := bLift_neighbour_nsTorusSp_of_seitzSetting hset hK hm e htC ht k hX
    htX hD
  have hB : HasBLift Kb := hBall Kb (isPerfect_iff.mp hKbP) hsN
    (F4Pilot.le_commutator_zpowers_of_isQuasisimple hKb.1 hsN hsC)
  obtain ⟨qh, hqs, hqker, hqapp⟩ :=
    LinearPilot.exists_surjective_centralizerPerfectCore_of_perfectCore_eq hcore hB
  have hle : centralizerPerfectCore X ≤ centralizer (X : Set G) :=
    F4Pilot.centralizerPerfectCore_le_centralizer X
  have hmemO : ∀ y : qh.ker, (Subgroup.inclusion hle) (y : centralizerPerfectCore X) ∈
      oddCore (centralizer (X : Set G)) := by
    intro y
    have h1 := hqapp (y : centralizerPerfectCore X)
    rw [MonoidHom.mem_ker.1 y.2] at h1
    exact (QuotientGroup.eq_one_iff _).1 h1.symm
  let φ : qh.ker →* oddCore (centralizer (X : Set G)) :=
    ((Subgroup.inclusion hle).comp qh.ker.subtype).codRestrict _ hmemO
  have hφinj : Function.Injective φ := fun a b hab =>
    Subtype.ext (Subtype.ext (congrArg
      (fun z : oddCore (centralizer (X : Set G)) => ((z : centralizer (X : Set G)) : G)) hab))
  have hkodd : Odd (Nat.card qh.ker) :=
    Odd.of_dvd_nat CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
      (Subgroup.card_dvd_of_injective φ hφinj)
  let η : centralizerPerfectCore X →* StatedSp m F' := eK.toMonoidHom.comp qh
  have hηs : Function.Surjective η := eK.surjective.comp hqs
  have hker : η.ker = qh.ker := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hEperf : Group.IsPerfect (centralizerPerfectCore X) :=
    isPerfect_iff.mpr (F4Pilot.commutator_centralizerPerfectCore X)
  have hinj := F4Pilot.oddSchurTrivial_statedSp m F' (centralizerPerfectCore X) hEperf η hηs
    (hker ▸ hqker) (hker ▸ hkodd)
  refine ⟨F', inferInstance, inferInstance, inferInstance, hF',
    ⟨(MulEquiv.ofBijective η ⟨hinj, hηs⟩).symm⟩, ?_⟩
  have hθ : ∀ y : centralizerPerfectCore X,
      qh ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ y) =
        Kb.normalizerMonoidHom ⟨_, hsN⟩ (qh y) := by
    intro y
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hqapp, hqapp]
    have e1 : (⟨(((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ y :
        centralizerPerfectCore X) : G), hle ((centralizerPerfectCore X).normalizerMonoidHom
          ⟨t, hN⟩ y).2⟩ : centralizer (X : Set G)) =
        ⟨t, htX⟩ * ⟨(y : G), hle y.2⟩ * ⟨t, htX⟩⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      rfl
    rw [e1, map_mul, map_mul, map_inv]
  rintro ⟨z, hz⟩
  apply hov.1
  refine ⟨qh z, MulEquiv.ext fun w => ?_⟩
  obtain ⟨y, rfl⟩ := hqs w
  rw [MulAut.conj_apply, ← hθ y, ← hz, MulAut.conj_apply, map_mul, map_mul, map_inv]

end Lift

section Normalize

variable {r : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_mulEquiv_statedSpMap_eq_comm_two (hr : 3 ≤ r) {k : Type} [Field k] [Finite k]
    [CharP k 2] (ι : k →+* F) {σ : F ≃+* F} (hσ : orderOf σ = 2)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {M : Type*} [Group M] (ψ : StatedSp r F ≃* M)
    {θ : MulAut M} (hθ : θ * θ = 1) (hθi : θ ∉ (MulAut.conj : M →* MulAut M).range)
    (ε : StatedSp r k →* M) (hε : Function.Injective ε)
    (hεr : ε.range = perfectCore (MonoidHom.eqLocus θ.toMonoidHom (MonoidHom.id M))) :
    ∃ ψ' : StatedSp r F ≃* M, (∀ g, ψ' (statedSpMap ι r g) = ε g) ∧
      ∀ x, θ (ψ' x) = ψ' (fieldSp r F σ x) := by
  set β := MulAut.congr ψ.symm θ with hβdef
  have hβapp : ∀ y, β y = ψ.symm (θ (ψ y)) := fun _ => rfl
  have hβ : β * β = 1 := by rw [hβdef, ← map_mul, hθ, map_one]
  have hβi : β ∉ (MulAut.conj : StatedSp r F →* MulAut (StatedSp r F)).range := by
    rintro ⟨s, hs⟩
    apply hθi
    refine ⟨ψ s, MulEquiv.ext fun x => ?_⟩
    have h1 := hβapp (ψ.symm x)
    rw [← hs, MulAut.conj_apply, ψ.apply_symm_apply] at h1
    rw [MulAut.conj_apply, ← ψ.apply_symm_apply (θ x), ← h1, map_mul, map_mul, map_inv,
      ψ.apply_symm_apply]
  obtain ⟨h, hh⟩ := F4Pilot.exists_eq_conj_mul_fieldSp_mul_conj_inv hr hσ hβ hβi
  set ψ₁ : StatedSp r F ≃* M := (MulAut.conj h).trans ψ with hψ₁
  have hψ₁app : ∀ x, ψ₁ x = ψ (h * x * h⁻¹) := fun _ => rfl
  have hθψ₁ : ∀ x, θ (ψ₁ x) = ψ₁ (fieldSp r F σ x) := by
    intro x
    have h1 := hβapp (h * x * h⁻¹)
    rw [hh, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_inv_apply, MulAut.conj_apply,
      show h⁻¹ * (h * x * h⁻¹) * h = x by group] at h1
    rw [hψ₁app, hψ₁app, ← ψ.apply_symm_apply (θ (ψ (h * x * h⁻¹))), ← h1]
  have hfixθ : MonoidHom.eqLocus θ.toMonoidHom (MonoidHom.id M) =
      (statedSpMap ι r).range.map ψ₁.toMonoidHom := by
    ext y
    obtain ⟨x, rfl⟩ := ψ₁.surjective y
    rw [mem_map_equiv, ψ₁.symm_apply_apply, ← F4Pilot.eqLocus_fieldSp_eq_range ι hfix]
    change θ (ψ₁ x) = ψ₁ x ↔ fieldSp r F σ x = x
    rw [hθψ₁]
    exact ψ₁.injective.eq_iff
  have htop : ⁅(⊤ : Subgroup (StatedSp r k)), (⊤ : Subgroup (StatedSp r k))⁆ = ⊤ := by
    have := isPerfect_statedSp_of_charTwo (k := k) hr
    rw [← commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  have hperf : ⁅(statedSpMap ι r).range.map ψ₁.toMonoidHom,
      (statedSpMap ι r).range.map ψ₁.toMonoidHom⁆ =
        (statedSpMap ι r).range.map ψ₁.toMonoidHom := by
    rw [← map_commutator, MonoidHom.range_eq_map, ← map_commutator, htop]
  have hrange : ε.range = (ψ₁.toMonoidHom.comp (statedSpMap ι r)).range := by
    rw [hεr, hfixθ, CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf, MonoidHom.range_comp]
  have hinj₁ : Function.Injective (ψ₁.toMonoidHom.comp (statedSpMap ι r)) :=
    ψ₁.injective.comp (statedSpMap_injective ι r)
  set δ : MulAut (StatedSp r k) := ((MonoidHom.ofInjective hε).trans
    (MulEquiv.subgroupCongr hrange)).trans (MonoidHom.ofInjective hinj₁).symm with hδdef
  have hδ : ∀ g, ψ₁ (statedSpMap ι r (δ g)) = ε g := by
    intro g
    have h1 := (MonoidHom.ofInjective hinj₁).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hε g))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨δ', hδ', hδσ⟩ :=
    exists_mulAut_statedSpMap_comm_fieldSp ι hr (fun c => (hfix (ι c)).2 ⟨c, rfl⟩) δ
  refine ⟨δ'.trans ψ₁, fun g => ?_, fun x => ?_⟩
  · change ψ₁ (δ' (statedSpMap ι r g)) = ε g
    rw [hδ', hδ]
  · change θ (ψ₁ (δ' x)) = ψ₁ (δ' (fieldSp r F σ x))
    rw [hθψ₁, hδσ]

end Normalize

section Param

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {F : Type} [Field F]
  {n : ℕ}

structure NsFieldParam (e : L ≃* StatedSp n K) (t : G) (ι : K →+* F) (σ : F ≃+* F)
    (k : Fin n) where
  Φ : spBlock F ({k}ᶜ : Finset (Fin n)) →* G
  injective : Function.Injective Φ
  range_eq : Φ.range = centralizerPerfectCore (modelToG e (nsTorusSp K k))
  N1 : ∀ (x : StatedSp n K) (hx : x ∈ spBlock K ({k}ᶜ : Finset (Fin n))),
    Φ ⟨spFieldMap n ι x, spFieldMap_mem_spBlock ι hx⟩ = ((e.symm x : L) : G)
  N3 : ∀ x : spBlock F ({k}ᶜ : Finset (Fin n)),
    t * Φ x * t⁻¹ = Φ (fieldBlockSp σ ({k}ᶜ : Finset (Fin n)) x)

end Param

section Exists


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem nonempty_nsFieldParam {m : ℕ} (hset : SeitzSetting G L) (hK : Nat.card K = 2)
    (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (k : Fin (m + 1)) {F : Type} [Field F] [Finite F] (ι : K →+* F)
    {σ : F ≃+* F} (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (h : NsKindSp e t k .field) : Nonempty (NsFieldParam e t ι σ k) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hFc : Nat.card F = 2 ^ (2 * 1) := natCard_eq_two_pow_two_mul_of_fix ι hKc hσ hfix
  set X : Subgroup G := modelToG e (nsTorusSp K k) with hXdef
  have hN : t ∈ normalizer (centralizerPerfectCore X : Set G) :=
    F4Pilot.normalizer_le_normalizer_centralizerPerfectCore _
      (UnitaryPilot.mem_normalizer_modelToG_of_mem_centralizer e htC _)
  obtain ⟨F', _, _, _, hF', ⟨ψ₀⟩, hθout⟩ :=
    exists_centralizerPerfectCore_mulEquiv_of_field_nsTorusSp hset hK hm e htC ht k rfl rfl h hN
  have : Fintype F := Fintype.ofFinite F
  have : Fintype F' := Fintype.ofFinite F'
  have hcc : Fintype.card F = Fintype.card F' := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hFc, hF']
  let ψ : StatedSp m F ≃* centralizerPerfectCore X :=
    (F4Pilot.statedSpCongr (FiniteField.ringEquivOfCardEq hcc) m).trans ψ₀
  have hθθ : (centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ *
      (centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ = 1 := by
    rw [← map_mul, show (⟨t, hN⟩ : normalizer (centralizerPerfectCore X : Set G)) * ⟨t, hN⟩ = 1
      from Subtype.ext htt, map_one]
  have hD : modelToG e (complSp K k) ≤ centralizerPerfectCore X :=
    modelToG_complSp_le_centralizerPerfectCore_nsTorusSp hK hm e k
  let ε₀ : StatedSp m K →* G := L.subtype.comp (e.symm.toMonoidHom.comp
    ((complSp K k).subtype.comp (complSpEquiv k).toMonoidHom))
  have hε₀M : ∀ g, ε₀ g ∈ centralizerPerfectCore X := fun g =>
    hD (symm_mem_modelToG e (complSpEquiv k g).2)
  let ε : StatedSp m K →* centralizerPerfectCore X := ε₀.codRestrict _ hε₀M
  have hεapp : ∀ g, ((ε g : centralizerPerfectCore X) : G) =
      ((e.symm (complSpEquiv k g : StatedSp (m + 1) K) : L) : G) := fun g => rfl
  have hεinj : Function.Injective ε := by
    intro g₁ g₂ h12
    apply (complSpEquiv (K := K) k).injective
    apply Subtype.ext
    apply e.symm.injective
    apply Subtype.ext
    have := congrArg (fun z : centralizerPerfectCore X => (z : G)) h12
    simpa only [hεapp] using this
  have hεrange : ε.range.map (centralizerPerfectCore X).subtype = modelToG e (complSp K k) := by
    ext g
    constructor
    · rintro ⟨_, ⟨g', rfl⟩, rfl⟩
      exact symm_mem_modelToG e (complSpEquiv k g').2
    · intro hg
      obtain ⟨x, hx, rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hg
      obtain ⟨g', hg'⟩ := (complSpEquiv (K := K) k).surjective ⟨x, hx⟩
      refine ⟨ε g', ⟨g', rfl⟩, ?_⟩
      change ((ε g' : centralizerPerfectCore X) : G) = _
      rw [hεapp, hg']
  have hεr : ε.range = perfectCore (MonoidHom.eqLocus
      ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩).toMonoidHom (MonoidHom.id _)) := by
    apply map_injective (centralizerPerfectCore X).subtype_injective
    rw [CFSG.Quasithin.map_perfectCore, map_eqLocus_normalizerMonoidHom_eq hN,
      perfectCore_centralizerPerfectCore_nsTorusSp_inf_centralizer hset hK hm e htC ht k,
      hεrange]
  obtain ⟨ψ', hψ'ι, hψ'σ⟩ :=
    exists_mulEquiv_statedSpMap_eq_comm_two hm ι hσ hfix ψ hθθ hθout ε hεinj hεr
  let Φ : spBlock F ({k}ᶜ : Finset (Fin (m + 1))) →* G :=
    (centralizerPerfectCore X).subtype.comp
      (ψ'.toMonoidHom.comp (blockComplEquiv F k).toMonoidHom)
  have hΦapp : ∀ y, Φ y = ((ψ' (blockComplEquiv F k y) : centralizerPerfectCore X) : G) :=
    fun y => rfl
  have hΦinj : Function.Injective Φ :=
    Subtype.val_injective.comp (ψ'.injective.comp (blockComplEquiv F k).injective)
  refine ⟨⟨Φ, hΦinj, ?_, ?_, ?_⟩⟩
  ·
    have hs : Function.Surjective (ψ'.toMonoidHom.comp (blockComplEquiv F k).toMonoidHom) :=
      ψ'.surjective.comp (blockComplEquiv F k).surjective
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hs, ← MonoidHom.range_eq_map,
      range_subtype]
  ·
    intro x hx
    rw [hΦapp, blockComplEquiv_spFieldMap ι k hx, hψ'ι, hεapp,
      coe_complSpEquiv_blockComplEquiv]
  ·
    intro y
    rw [hΦapp, hΦapp, blockComplEquiv_fieldBlockSp, ← hψ'σ]
    rfl

end Exists

end CFSG.SeitzReduction.SymplecticPilot
