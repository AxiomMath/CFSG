module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeLSevenPieces
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeLSevenModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeLSevenNormal

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open LinearFlag
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.SeitzReduction.F4Pilot (statedSpMap centralizerPerfectCore ordSL
  centralizerPerfectCore_le_centralizer)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG OddCentralSplit)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open scoped MatrixGroups

section Cent

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem lift_mem_centralizer_siegelTorus (e : L ≃* StatedSp 3 K) {k : Fin 3} {F : Type}
    [Field F] [CharP F 2] (σ : K ≃+* F) (β : StatedSp 2 K →* StatedSp 2 K)
    (Φ : SpecialLinearGroup (Fin (2 * 2 + 1)) F →* G) (hrange : Φ.range = neighbourCore e k)
    (hN1 : ∀ x : StatedSp 2 K, Φ (ctEmbed 1 (statedSpMap (σ : K →+* F) 2 (β x))) =
      ((e.symm (complSpEquiv k x : complSp K k) : L) : G))
    (T₄ : Subgroup (StatedSp 2 K))
    (hT : siegelTorus K 3 ≤ rootTorusSp K k ⊔ T₄.map (complSpHom k))
    {x : SpecialLinearGroup (Fin (2 * 2 + 1)) F}
    (hx : ∀ d ∈ T₄, x * ctEmbed 1 (statedSpMap (σ : K →+* F) 2 (β d)) =
      ctEmbed 1 (statedSpMap (σ : K →+* F) 2 (β d)) * x) :
    Φ x ∈ centralizer (modelToG e (siegelTorus K 3) : Set G) := by
  have hxE : Φ x ∈ neighbourCore e k := hrange ▸ ⟨x, rfl⟩
  have hle : modelToG e (siegelTorus K 3) ≤ centralizer ({Φ x} : Set G) := by
    refine (UnitaryPilot.modelToG_mono e hT).trans ?_
    rw [UnitaryPilot.modelToG_sup]
    refine sup_le ?_ ?_
    · intro y hy
      rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.1 (centralizerPerfectCore_le_centralizer _ hxE) y hy
    · intro y hy
      obtain ⟨_, ⟨d, hd, rfl⟩, rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hy
      rw [mem_centralizer_singleton_iff]
      change ((e.symm (complSpEquiv k d : complSp K k) : L) : G) * Φ x =
        Φ x * ((e.symm (complSpEquiv k d : complSp K k) : L) : G)
      rw [← hN1 d, ← map_mul, ← map_mul, hx d hd]
  rw [mem_centralizer_iff]
  intro y hy
  have h := hle hy
  rw [mem_centralizer_singleton_iff] at h
  exact h

omit [Field K] in
theorem siegelTorus_three_le_sup [Field K] :
    siegelTorus K 3 ≤ rootTorusSp K 2 ⊔ (siegelTorus K 2).map (complSpHom (K := K) 2) := by
  refine le_trans ?_ leviTorusSp_zero_le_sup
  rw [siegelTorus_eq_leviTorusSp]
  exact leviTorusSp_anti (by decide)

end Cent

section Comm

variable {F : Type} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem oddRegUnip_mem : oddRegUnip F ∈ blockSpecialLinear (K := F) oddFixBlock := by
  rw [oddRegUnip]
  exact mul_mem (mul_mem (LinearPilot.transvection_mem_blockSpecialLinear
    (show (2 : Fin (2 * 2 + 1)) ≠ 4 by decide) (by decide) (by decide) 1)
    (LinearPilot.transvection_mem_blockSpecialLinear (show (4 : Fin (2 * 2 + 1)) ≠ 3 by decide)
      (by decide) (by decide) 1))
    (LinearPilot.transvection_mem_blockSpecialLinear (show (2 : Fin (2 * 2 + 1)) ≠ 3 by decide)
      (by decide) (by decide) 1)

theorem ctGraph_oddRegUnip_inv_mul :
    ctGraph 1 (oddRegUnip F)⁻¹ * ((oddRegUnip F)⁻¹)⁻¹ = oddZ F := by
  rw [map_inv, ctGraph_oddRegUnip, inv_inv, _root_.mul_inv_rev, inv_mul_cancel_right, oddZ,
    transvection_inv_charTwo]

theorem ctGraph_transvection_zero_two :
    ctGraph 1 (SpecialLinearGroup.transvection (show (0 : Fin (2 * 2 + 1)) ≠ 2 by decide) (1 : F)) =
      SpecialLinearGroup.transvection (show (3 : Fin (2 * 2 + 1)) ≠ 1 by decide) 1 :=
  ctGraph_transvection' _ (q2Par_five 2) (q2Par_five 0) _ 1

omit [CharP F 2] in
theorem transvection_three_one_commute :
    SpecialLinearGroup.transvection (show (3 : Fin (2 * 2 + 1)) ≠ 1 by decide) (1 : F) *
      SpecialLinearGroup.transvection (show (0 : Fin (2 * 2 + 1)) ≠ 2 by decide) 1 =
      SpecialLinearGroup.transvection (show (0 : Fin (2 * 2 + 1)) ≠ 2 by decide) 1 *
        SpecialLinearGroup.transvection (show (3 : Fin (2 * 2 + 1)) ≠ 1 by decide) 1 := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_five, Matrix.single_apply, Matrix.one_apply]

omit [CharP F 2] in
theorem transvection_three_one_mul_not_mem_center :
    SpecialLinearGroup.transvection (show (3 : Fin (2 * 2 + 1)) ≠ 1 by decide) (1 : F) *
      SpecialLinearGroup.transvection (show (0 : Fin (2 * 2 + 1)) ≠ 2 by decide) 1 ∉
        Subgroup.center (SpecialLinearGroup (Fin (2 * 2 + 1)) F) := by
  intro h
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 h
  have h1 := congrFun (congrFun hr 3) 1
  simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe] at h1
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.one_apply] at h1

omit [CharP F 2] in
theorem orderOf_map_eq_two_of_not_mem_center {G : Type} [Group G] {n : ℕ}
    (Φ : SpecialLinearGroup (Fin n) F →* G) (hker : Φ.ker ≤ center (SpecialLinearGroup (Fin n) F))
    {y : SpecialLinearGroup (Fin n) F} (hy : y * y = 1)
    (hyc : y ∉ center (SpecialLinearGroup (Fin n) F)) :
    orderOf (Φ y) = 2 := by
  refine orderOf_eq_prime (by rw [sq, ← map_mul, hy, map_one]) ?_
  intro h1
  exact hyc (hker h1)

end Comm

section Trivial

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite K] in
theorem false_of_siegel_normal_of_oddGraph (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp 3 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {b : Bool}
    (h : SpThreeOddGraphNormalized e t f 2 b)
    (htX : t ∈ centralizer (modelToG e (siegelTorus K 3) : Set G))
    (hnorm : (((modelToG e (siegelLevi K 3)).subgroupOf
      (centralizer (modelToG e (siegelTorus K 3) : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer
          (modelToG e (siegelTorus K 3) : Set G))))).Normal) : False := by
  have hcen := mk_mem_center_of_siegel_normal hset hKc hf (by norm_num) e htC ht htX hnorm
  obtain ⟨F, _, _, _, σ, Φ, -, hrange, hker, hN1, hN3⟩ := h
  have hcomm : ∀ x : SpecialLinearGroup (Fin (2 * 2 + 1)) F,
      t * Φ x * t⁻¹ * (Φ x)⁻¹ = Φ (ctGraph 1 x * x⁻¹) := by
    intro x
    rw [hN3, map_mul, map_inv]
  cases b with
  | false =>
    set x := SpecialLinearGroup.transvection (show (0 : Fin (2 * 2 + 1)) ≠ 2 by decide) (1 : F)
      with hxdef
    have hxH : Φ x ∈ centralizer (modelToG e (siegelTorus K 3) : Set G) := by
      refine lift_mem_centralizer_siegelTorus e σ (MonoidHom.id _) Φ hrange hN1
        (siegelTorus K 2) siegelTorus_three_le_sup ?_
      rintro _ ⟨s, rfl⟩
      change x * ctEmbed 1 (statedSpMap (σ : K →+* F) 2 (diagSp K 2 (fun _ => s))) =
        ctEmbed 1 (statedSpMap (σ : K →+* F) 2 (diagSp K 2 (fun _ => s))) * x
      rw [statedSpMap_diagSp]
      refine commute_of_mem_blockSpecialLinear_of_diagonal
        (I := oddTwA) (LinearPilot.transvection_mem_blockSpecialLinear _ (by decide) (by decide) _)
        (coe_ctEmbed_diagSp_two _) ?_
      intro i hi j hj
      simp only [oddTwA, Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rfl
    refine false_of_mk_mem_center_of_orderOf_commutator htX hxH ?_ hcen
    rw [hcomm, hxdef, ctGraph_transvection_zero_two, transvection_inv_charTwo]
    set a := SpecialLinearGroup.transvection (show (3 : Fin (2 * 2 + 1)) ≠ 1 by decide) (1 : F)
      with ha
    set b := SpecialLinearGroup.transvection (show (0 : Fin (2 * 2 + 1)) ≠ 2 by decide) (1 : F)
      with hb
    have hab : a * b = b * a := transvection_three_one_commute
    have hyy : a * b * (a * b) = 1 := by
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hab]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by
          rw [ha, hb, transvection_mul_self_charTwo, transvection_mul_self_charTwo, one_mul]
    exact orderOf_map_eq_two_of_not_mem_center Φ hker hyy transvection_three_one_mul_not_mem_center
  | true =>
    have hxH : Φ (oddRegUnip F)⁻¹ ∈ centralizer (modelToG e (siegelTorus K 3) : Set G) := by
      refine lift_mem_centralizer_siegelTorus e σ tauSp Φ hrange hN1
        (siegelTorus K 2) siegelTorus_three_le_sup ?_
      rintro _ ⟨s, rfl⟩
      change (oddRegUnip F)⁻¹ * ctEmbed 1 (statedSpMap (σ : K →+* F) 2
          (tauSp (diagSp K 2 (fun _ => s)))) =
        ctEmbed 1 (statedSpMap (σ : K →+* F) 2 (tauSp (diagSp K 2 (fun _ => s)))) *
          (oddRegUnip F)⁻¹
      rw [tauSp_diagSp_const, statedSpMap_rootTorusHom]
      refine commute_of_mem_blockSpecialLinear_of_diagonal (I := oddFixBlock)
        (inv_mem oddRegUnip_mem) (coe_ctEmbed_rootTorusHom_zero _) ?_
      intro i hi j hj
      simp only [oddFixBlock, Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> rfl
    refine false_of_mk_mem_center_of_orderOf_commutator htX hxH ?_ hcen
    rw [hcomm, ctGraph_oddRegUnip_inv_mul]
    exact orderOf_map_eq_two_of_not_mem_center Φ hker (transvection_mul_self_charTwo _ _)
      (transvection_not_mem_center_of_ne_zero (show (2 : Fin (2 * 2 + 1)) ≠ 3 by decide)
        one_ne_zero)

theorem spThreeLinearOddTrivialSiegelInput_holds :
    SpThreeLinearOddTrivialSiegelInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t hto hKt hroot htw htX hnorm
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  exact false_of_siegel_normal_of_oddGraph hset hKc hf e htC hto
    (spThreeOddGraphNormalized_of_twisted hset hKc hf e htC hto 2 (hroot 2) htw) htX hnorm

end Trivial

section Field

variable {F : Type} [Field F]

theorem natCard_map_sup_oddTw {E : Type*} [Group E]
    (Φ : SpecialLinearGroup (Fin (2 * 2 + 1)) F →* E)
    (hker : Φ.ker ≤ center (SpecialLinearGroup (Fin (2 * 2 + 1)) F)) :
    Nat.card ((blockSpecialLinear (K := F) oddTwA ⊔ blockSpecialLinear (K := F) oddTwB).map Φ) =
      Nat.card (SpecialLinearGroup (Fin 2) F) * Nat.card (SpecialLinearGroup (Fin 2) F) := by
  set H := blockSpecialLinear (K := F) oddTwA ⊔ blockSpecialLinear (K := F) oddTwB with hH
  have hH4 : H ≤ blockSpecialLinear (K := F) ({4} : Finset (Fin (2 * 2 + 1)))ᶜ :=
    sup_le (LinearPilot.blockSpecialLinear_mono (by decide))
      (LinearPilot.blockSpecialLinear_mono (by decide))
  have hinj : Function.Injective (Φ.comp H.subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, hx⟩ hx1
    have hxc : x ∈ center (SpecialLinearGroup (Fin (2 * 2 + 1)) F) := hker hx1
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hxc
    have h44 : (x : Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) F) 4 4 = 1 :=
      (mem_blockSpecialLinear.1 (hH4 hx) 4 4 (Or.inl (by decide))).trans (Matrix.one_apply_eq _)
    have hr1 : r = 1 := by
      rw [← hr] at h44
      simpa using h44
    apply Subtype.ext
    change x = 1
    apply Subtype.ext
    rw [← hr, hr1, map_one]
    rfl
  have hr : (Φ.comp H.subtype).range = H.map Φ := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [← hr, ← natCard_sup_oddTw]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

end Field

section Swap

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem nonempty_siegelSwapParam_of_oddStd
    (hcat : LinearPilot.SLmCatalogueClausesAt 3) (hdet : LinearPilot.SLmEvenTypeDetAt 3)
    (hsplit : OddCentralSplit (siegelLevi K 3)) (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp 3 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hk : RootKindSp e t f 2 .linearOdd) (hstd : SpThreeOddStandard e) :
    Nonempty (SiegelSwapParam e t) := by
  have hK : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hgn := spThreeOddGraphNormalized_of_standard hset hKc hf e htC ht 2 hk hstd
  obtain ⟨F', _, _, ι, σ', hσ, hfix⟩ := exists_quadraticExtension K
  obtain ⟨hσ1, hσσ⟩ := ne_one_and_mul_self_of_orderOf_eq_two hσ
  have hF' : Nat.card F' = Nat.card K ^ 2 := by
    rw [LinearPilot.natCard_eq_two_pow_of_fixedField hKc ι hσ1 hσσ hfix, hKc, ← pow_mul,
      mul_comm]
  rcases siegel_normal_or_fieldParam_or_swapParam hcat hdet hset hKc hf le_rfl e htC ht hsplit ι
    hσ1 hσσ hfix with ⟨htX, hnorm⟩ | hS' | hS
  · exact (false_of_siegel_normal_of_oddGraph hset hKc hf e htC ht hgn htX hnorm).elim
  · obtain ⟨S⟩ := hS'
    exfalso
    obtain ⟨F, _, _, _, σ, Φ, -, hrange, hker, hN1, -⟩ := hgn
    have hFK : Nat.card F = Nat.card K := (Nat.card_congr σ.toEquiv).symm
    have hSL : Nat.card SL(2, F) = ordSL 2 (Nat.card F) :=
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num)
    have h1 : Nat.card (pieceCore e ({0} : Finset (Fin 3))) = ordSL 2 (Nat.card K) ^ 2 := by
      rw [pieceCore_zero_eq_of_oddStd hK e σ Φ hrange hker (fun x => hN1 x),
        natCard_map_sup_oddTw Φ hker, hSL, hFK, sq]
    have h2 := S.natCard_pieceCore_singleton hK (by norm_num) (j := 0) (by decide)
    have hlt := ordSL_two_sq_lt_ordSL_two_sq (q := Nat.card K) (by omega)
    rw [h1, hF'] at h2
    omega
  · exact hS

end Swap

end CFSG.SeitzReduction.SymplecticPilot
