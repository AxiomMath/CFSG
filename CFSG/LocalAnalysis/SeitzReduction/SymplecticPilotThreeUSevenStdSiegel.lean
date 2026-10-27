module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUFourAlign
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeCoverOddSiegel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeUSevenEdge

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive unitaryInvolution_apply)
open CFSG.LieType.CurtisTits (rankOne)
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open CFSG.SeitzReduction.F4Pilot (statedSpMap centralizerPerfectCore ordSL
  centralizerPerfectCore_le_centralizer)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG OddCentralSplit)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

section Root

variable {F : Type} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)

theorem ctuaBarAut_rootHom {n : ℕ} {i j : Fin n} (hij : i ≠ j) (hi : i ≠ Fin.rev i)
    (hj : j ≠ Fin.rev j) (c : Multiplicative F) :
    ctuaBarAut σ hσ n (rootHom σ hσ hij hi hj c) =
      rootHom σ hσ hij hi hj (Multiplicative.ofAdd (σ (Multiplicative.toAdd c))) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_ctuaBarAut, coe_glAut, coe_rootHom, coe_rootHom, toAdd_ofAdd]
  ext a b
  simp only [rootMatrix, map_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.single_apply]
  split_ifs <;> simp

theorem uRootZero_hk : (⟨0, by norm_num⟩ : Fin ((2 * 2 + 1) / 2)).val + 1 < (2 * 2 + 1) / 2 := by
  norm_num

@[expose] noncomputable def uRootZero (c : F) : SU σ (2 * 2 + 1) :=
  rootHom σ hσ (lowIdx_ne_succ uRootZero_hk) (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _)
    (Multiplicative.ofAdd c)

theorem uRootZero_mem_rankOne (c : F) :
    uRootZero hσ c ∈
      rankOne (rootGroup σ hσ (2 * 2 + 1)) (⟨0, by norm_num⟩ : Fin ((2 * 2 + 1) / 2)) :=
  Subgroup.mem_sup_left (rootHom_mem hσ (lowIdx_ne_succ uRootZero_hk) (lowIdx_ne_rev _ _)
    (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) (toStd_short uRootZero_hk).symm
    (Multiplicative.ofAdd c))

theorem uRootZero_mul (c d : F) : uRootZero hσ c * uRootZero hσ d = uRootZero hσ (c + d) := by
  rw [uRootZero, uRootZero, uRootZero, ← map_mul]
  rfl

theorem uRootZero_inv (c : F) : (uRootZero hσ c)⁻¹ = uRootZero hσ (-c) := by
  rw [uRootZero, uRootZero, ← map_inv]
  rfl

theorem ctuaBarAut_uRootZero (c : F) :
    ctuaBarAut σ hσ (2 * 2 + 1) (uRootZero hσ c) = uRootZero hσ (σ c) := by
  rw [uRootZero, ctuaBarAut_rootHom, toAdd_ofAdd]
  rfl

theorem uRootZero_one_ne_one : uRootZero hσ (1 : F) ≠ 1 := by
  intro h
  have h1 := congrArg (fun x : SU σ (2 * 2 + 1) =>
    ((x : GL (Fin (2 * 2 + 1)) F) : Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) F) 0 1) h
  simp only [uRootZero, coe_rootHom, toAdd_ofAdd, rootMatrix] at h1
  simp [lowIdx, Fin.ext_iff] at h1

end Root

section Piece

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

omit [Finite G] [CharP K 2] in
theorem injective_comp_rankOne_zero {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {E : Type*} [Group E]
    {Φ : SU (unitaryInvolution F 2 f) (2 * 2 + 1) →* E}
    (hker : Φ.ker ≤ center (SU (unitaryInvolution F 2 f) (2 * 2 + 1))) :
    Function.Injective (Φ.comp (rankOne (rootGroup (unitaryInvolution F 2 f)
      (unitaryInvolution_involutive hF) (2 * 2 + 1))
        (⟨0, by norm_num⟩ : Fin ((2 * 2 + 1) / 2))).subtype) := by
  set eR := CFSG.LieType.Steinberg.rankOneShortEquiv (hσ := unitaryInvolution_involutive hF)
    (n := 2 * 2 + 1) (k := ⟨0, by norm_num⟩) (by norm_num) with heR
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxc : (x : SU (unitaryInvolution F 2 f) (2 * 2 + 1)) ∈
      center (SU (unitaryInvolution F 2 f) (2 * 2 + 1)) := hker hx
  have hex : eR x ∈ center (SpecialLinearGroup (Fin 2) F) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := eR.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_center_iff.1 hxc y)
  rw [center_SL_two_eq_bot_of_charTwo, mem_bot] at hex
  exact eR.injective (hex.trans (map_one eR).symm)

theorem map_rankOne_zero_le_pieceCore_zero_of_uodd_std {f : ℕ} (hf : 2 ≤ f)
    {e : L ≃* StatedSp 3 K} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ f) ^ 2) {ι : K →+* F}
    {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c}
    {Φ : SU (unitaryInvolution F 2 f) (2 * 2 + 1) →* G} (hrange : Φ.range = neighbourCore e 2)
    (hN1 : ∀ x : StatedSp 2 K, Φ (ctuEmbed 1 le_rfl (unitaryInvolution F 2 f) ι hι x) =
      ((e.symm ((complSpEquiv 2 x : complSp K 2) : StatedSp 3 K) : L) : G)) :
    (rankOne (rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF)
      (2 * 2 + 1)) (⟨0, by norm_num⟩ : Fin ((2 * 2 + 1) / 2))).map Φ ≤
        pieceCore e ({0} : Finset (Fin 3)) := by
  rw [pieceCore_eq e (k := 2) (by decide)]
  set R := rankOne (rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF)
    (2 * 2 + 1)) (⟨0, by norm_num⟩ : Fin ((2 * 2 + 1) / 2)) with hR
  have hRperf : ⁅R.map Φ, R.map Φ⁆ = R.map Φ := by
    rw [← Subgroup.map_commutator,
      Subgroup.isPerfect_iff.1 (isPerfect_rankOne hF hf (n := 2 * 2 + 1) (by norm_num) _)]
  refine le_perfectCore_of_perfect ?_ hRperf
  rw [inf_centralizer_eq_of_le_sup (H := neighbourCore e 2) (X := modelToG e (rootTorusSp K 2))
    (Y := modelToG e ((siegelTorus K 2).map (complSpHom (K := K) 2)))
    (centralizerPerfectCore_le_centralizer _)
    (UnitaryPilot.modelToG_mono e map_siegelTorus_two_le_leviTorusSp_zero)
    (by
      rw [← UnitaryPilot.modelToG_sup]
      exact UnitaryPilot.modelToG_mono e leviTorusSp_zero_le_sup)]
  rintro _ ⟨x, hx, rfl⟩
  refine Subgroup.mem_inf.2 ⟨hrange ▸ ⟨x, rfl⟩, ?_⟩
  rw [mem_centralizer_iff]
  intro g hg
  obtain ⟨_, ⟨y, ⟨s, rfl⟩, rfl⟩, hgy⟩ := (UnitaryPilot.mem_modelToG e).1 hg
  rw [← hgy]
  change ((e.symm (complSpHom 2 (diagSp K 2 (fun _ => s))) : L) : G) * Φ x =
    Φ x * ((e.symm (complSpHom 2 (diagSp K 2 (fun _ => s))) : L) : G)
  rw [complSpHom_apply, ← hN1, ← map_mul, ← map_mul]
  congr 1
  exact (commute_rankOne_short_ctuEmbed_diagSp (N := 2) (ε := 1) (hε := le_rfl)
    (j := ⟨0, by norm_num⟩) (by norm_num) (t := fun _ => s) rfl hx).symm

theorem ordSL_two_sq_dvd_natCard_pieceCore_zero_of_uodd_std {f : ℕ} (hf : 2 ≤ f)
    {e : L ≃* StatedSp 3 K} {t : G} (hn : SpThreeUOddNormalized e t f 2 false) :
    ordSL 2 ((2 ^ f) ^ 2) ∣ Nat.card (pieceCore e ({0} : Finset (Fin 3))) := by
  obtain ⟨F, _, _, _, hF, ι, hι, Φ, hrange, hker, hN1, -⟩ := hn
  have h1 := Subgroup.card_dvd_of_le
    (map_rankOne_zero_le_pieceCore_zero_of_uodd_std hf hF hrange (fun x => hN1 x))
  rw [natCard_map_rankOne_zero hF hker, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    hF] at h1
  rw [ordSL_two_eq]
  exact h1

end Piece

section Kinds

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

theorem false_of_siegelSwapParam_of_uodd_std {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    {e : L ≃* StatedSp 3 K} {t : G} (hn : SpThreeUOddNormalized e t f 2 false)
    (S : SiegelSwapParam e t) : False := by
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hKc
  have hq : 4 ≤ 2 ^ f := four_le_two_pow hf
  have hK4 : 4 ≤ Nat.card K := hKc ▸ hq
  have h1 := ordSL_two_sq_dvd_natCard_pieceCore_zero_of_uodd_std hf hn
  rw [S.natCard_pieceCore_singleton hK4 (by norm_num) (j := 0) (by decide), hKc] at h1
  have hq2 : 16 ≤ (2 ^ f) ^ 2 := by nlinarith
  have hpos : 0 < ordSL 2 (2 ^ f) ^ 2 := by
    apply pow_pos
    rw [ordSL_two_eq]
    exact Nat.mul_pos (by omega) (by omega)
  have h2 := Nat.le_of_dvd hpos h1
  have h3 := ctuf_ordSL_two_sq_lt (q := 2 ^ f) (by omega)
  omega

theorem false_of_siegel_normal_of_uodd_std (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp 3 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hn : SpThreeUOddNormalized e t f 2 false)
    (htX : t ∈ centralizer (modelToG e (siegelTorus K 3) : Set G))
    (hnorm : (((modelToG e (siegelLevi K 3)).subgroupOf
      (centralizer (modelToG e (siegelTorus K 3) : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer
          (modelToG e (siegelTorus K 3) : Set G))))).Normal) : False := by
  have hcen := mk_mem_center_of_siegel_normal hset hKc hf (by norm_num) e htC ht htX hnorm
  obtain ⟨F, _, _, _, hF, ι, hι, Φ, hrange, hker, hN1, hN3⟩ := hn
  set hσ := unitaryInvolution_involutive hF with hσdef
  have hσ1 : unitaryInvolution F 2 f ≠ 1 := by
    obtain ⟨a, ha⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_ne hF
    intro h1
    exact ha (by rw [h1]; rfl)
  have hσσ : unitaryInvolution F 2 f * unitaryInvolution F 2 f = 1 :=
    RingEquiv.ext fun c => hσ c
  obtain ⟨ω, hω⟩ := LinearPilot.exists_trace_one_of_involution hσ1 hσσ
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hw : t * Φ (uRootZero hσ ω) * t⁻¹ * (Φ (uRootZero hσ ω))⁻¹ = Φ (uRootZero hσ 1) := by
    rw [hN3, ctuaBarAut_uRootZero, ← map_inv, ← map_mul, uRootZero_inv, uRootZero_mul, hω]
    congr 2
    ring
  have hw1 : Φ (uRootZero hσ 1) ≠ 1 := by
    intro h
    apply uRootZero_one_ne_one hσ
    have h' := injective_comp_rankOne_zero hF hker
      (a₁ := ⟨_, uRootZero_mem_rankOne hσ 1⟩) (a₂ := 1) (by
        change Φ (uRootZero hσ 1) = Φ 1
        rw [h, map_one])
    exact congrArg Subtype.val h'
  have hsq : uRootZero hσ (1 : F) * uRootZero hσ 1 = 1 := by
    rw [uRootZero_mul, show (1 : F) + 1 = 0 by linear_combination h2, uRootZero]
    exact map_one _
  have hord : orderOf (Φ (uRootZero hσ 1)) = 2 :=
    orderOf_eq_prime (by rw [sq, ← map_mul, hsq, map_one]) hw1
  have hMu : Φ (uRootZero hσ ω) ∈ pieceCore e ({0} : Finset (Fin 3)) :=
    map_rankOne_zero_le_pieceCore_zero_of_uodd_std hf hF hrange (fun x => hN1 x)
      ⟨_, uRootZero_mem_rankOne hσ ω, rfl⟩
  refine false_of_mk_mem_center_of_orderOf_commutator htX
    (pieceCore_singleton_le_centralizer_siegelTorus e (j := 0) (by decide) hMu) ?_ hcen
  rw [hw]
  exact hord

theorem nonempty_siegelFieldParam_of_uodd_standard
    [Finite K]
    (hcat : LinearPilot.SLmCatalogueClausesAt 3) (hdet : LinearPilot.SLmEvenTypeDetAt 3)
    (hset : SeitzSetting G L) {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hk : RootKindSp e t f 2 .unitaryOdd) (hstd : SpThreeUOddStandard e) {F' : Type} [Field F']
    [Finite F'] (ι : K →+* F') {σ' : F' ≃+* F'} (hσ1 : σ' ≠ 1) (hσσ : σ' * σ' = 1)
    (hfix : ∀ x : F', σ' x = x ↔ x ∈ Set.range ι) :
    Nonempty (SiegelFieldParam e t ι σ') := by
  have hn := spThreeUOddNormalized_of_standard hset hKc hf e htC ht 2 hk hstd
  rcases siegel_normal_or_fieldParam_or_swapParam hcat hdet hset hKc hf le_rfl e htC ht
    (oddCentralSplit_siegelLevi (by norm_num)) ι hσ1 hσσ hfix with ⟨htX, hnorm⟩ | hS | hS'
  · exact (false_of_siegel_normal_of_uodd_std hset hKc hf e htC ht hn htX hnorm).elim
  · exact hS
  · obtain ⟨S⟩ := hS'
    exact (false_of_siegelSwapParam_of_uodd_std hKc hf hn S).elim

end Kinds

end CFSG.SeitzReduction.SymplecticPilot
