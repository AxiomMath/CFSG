module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeUSevenEdge
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeCoverOddSiegel

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive unitaryInvolution_apply)
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open CFSG.SeitzReduction.F4Pilot (statedSpMap centralizerPerfectCore ordSL
  centralizerPerfectCore_le_centralizer)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG OddCentralSplit)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

section Heis

variable {F : Type} [Field F] [CharP F 2] (σ : F ≃+* F)

omit [CharP F 2] in
theorem heisenbergMatrix_map {n : ℕ} (i k : Fin n) (a b : F) :
    (heisenbergMatrix σ i k a b).map σ = heisenbergMatrix σ i k (σ a) (σ b) := by
  ext r c
  simp only [heisenbergMatrix, map_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.single_apply]
  split_ifs <;> simp

theorem uOddHeis_hi : (1 : Fin (2 * 2 + 1)) ≠ Fin.rev 1 := by decide

theorem uOddHeis_hik : (1 : Fin (2 * 2 + 1)) ≠ 2 := by decide

theorem uOddHeis_hk : Fin.rev (2 : Fin (2 * 2 + 1)) = 2 := by decide

variable {σ} in
theorem uOddHeis_mul (ω : F) :
    heisenbergMatrix σ (1 : Fin (2 * 2 + 1)) 2 1 ω * heisenbergMatrix σ 1 2 1 (ω + 1) = 1 := by
  rw [heisenbergMatrix_mul σ uOddHeis_hi uOddHeis_hik uOddHeis_hk, map_one, mul_one]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [show (1 : F) + 1 = 0 by linear_combination h2,
    show ω + (ω + 1) - 1 = 0 by linear_combination ω * h2, heisenbergMatrix_zero]

variable {σ} in
theorem uOddHeis_mul' (ω : F) :
    heisenbergMatrix σ (1 : Fin (2 * 2 + 1)) 2 1 (ω + 1) * heisenbergMatrix σ 1 2 1 ω = 1 := by
  rw [heisenbergMatrix_mul σ uOddHeis_hi uOddHeis_hik uOddHeis_hk, map_one, mul_one]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [show (1 : F) + 1 = 0 by linear_combination h2,
    show ω + 1 + ω - 1 = 0 by linear_combination ω * h2, heisenbergMatrix_zero]

variable {σ} in
@[expose] noncomputable def uOddHeis (hσ : ∀ c, σ (σ c) = c) {ω : F} (hω : σ ω = ω + 1) :
    SU σ (2 * 2 + 1) :=
  ⟨⟨heisenbergMatrix σ (1 : Fin (2 * 2 + 1)) 2 1 ω, heisenbergMatrix σ 1 2 1 (ω + 1),
      uOddHeis_mul ω, uOddHeis_mul' ω⟩,
    det_heisenbergMatrix σ uOddHeis_hi uOddHeis_hik uOddHeis_hk 1 ω,
    heisenbergMatrix_isometry σ hσ uOddHeis_hi uOddHeis_hik uOddHeis_hk (by
      rw [hω, map_one, one_mul]
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      linear_combination (ω + 1) * h2)⟩

variable {σ} (hσ : ∀ c, σ (σ c) = c) {ω : F} (hω : σ ω = ω + 1)

theorem ctuaBarAut_uOddHeis :
    ctuaBarAut σ hσ (2 * 2 + 1) (uOddHeis hσ hω) = (uOddHeis hσ hω)⁻¹ := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_ctuaBarAut, coe_glAut]
  change (heisenbergMatrix σ (1 : Fin (2 * 2 + 1)) 2 1 ω).map σ =
    heisenbergMatrix σ (1 : Fin (2 * 2 + 1)) 2 1 (ω + 1)
  rw [heisenbergMatrix_map, map_one, hω]

theorem coe_uOddHeis_inv_sq :
    (((((uOddHeis hσ hω)⁻¹ * (uOddHeis hσ hω)⁻¹ : SU σ (2 * 2 + 1)) :
      GL (Fin (2 * 2 + 1)) F)) : Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) F) =
        heisenbergMatrix σ (1 : Fin (2 * 2 + 1)) 2 0 1 := by
  change heisenbergMatrix σ (1 : Fin (2 * 2 + 1)) 2 1 (ω + 1) *
    heisenbergMatrix σ (1 : Fin (2 * 2 + 1)) 2 1 (ω + 1) = _
  rw [heisenbergMatrix_mul σ uOddHeis_hi uOddHeis_hik uOddHeis_hk, map_one, mul_one]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [show (1 : F) + 1 = 0 by linear_combination h2,
    show ω + 1 + (ω + 1) - 1 = 1 by linear_combination ω * h2]

theorem uOddHeis_inv_sq_ne_one : (uOddHeis hσ hω)⁻¹ * (uOddHeis hσ hω)⁻¹ ≠ 1 := by
  intro h
  have h1 := congrArg (fun x : SU σ (2 * 2 + 1) =>
    ((x : GL (Fin (2 * 2 + 1)) F) : Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) F) 1 3) h
  rw [coe_uOddHeis_inv_sq] at h1
  simp [heisenbergMatrix, Fin.ext_iff] at h1

theorem uOddHeis_inv_sq_mul_self :
    ((uOddHeis hσ hω)⁻¹ * (uOddHeis hσ hω)⁻¹) * ((uOddHeis hσ hω)⁻¹ * (uOddHeis hσ hω)⁻¹) = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, coe_uOddHeis_inv_sq,
    heisenbergMatrix_mul σ uOddHeis_hi uOddHeis_hik uOddHeis_hk, map_zero, mul_zero, add_zero]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [show (1 : F) + 1 - 0 = 0 by linear_combination h2, heisenbergMatrix_zero]
  rfl

theorem uOddHeis_mem_ctuBlock : uOddHeis hσ hω ∈ ctuBlock σ 1 ({0} : Finset (Fin 2)) := by
  rw [mem_ctuBlock]
  intro a b hab
  have key : ∀ c : Fin (2 * 2 + 1), c ∈ ctuPlanes 1 ({0} : Finset (Fin 2)) → c = 0 ∨ c = 4 := by
    intro c hc
    rcases eq_or_eq_of_mem_ctuPlanes_singleton hc with rfl | rfl
    · exact Or.inl (Fin.ext (by rw [ctuCoord_inl_inl]; rfl))
    · exact Or.inr (Fin.ext (by rw [ctuCoord_inl_inr]; rfl))
  change heisenbergMatrix σ (1 : Fin (2 * 2 + 1)) 2 1 ω a b = (1 : Matrix _ _ F) a b
  rcases hab with ha | hb
  · rcases key a ha with rfl | rfl <;> fin_cases b <;>
      simp [heisenbergMatrix, Matrix.one_apply, Fin.ext_iff]
  · rcases key b hb with rfl | rfl <;> fin_cases a <;>
      simp [heisenbergMatrix, Matrix.one_apply, Fin.ext_iff]

end Heis

section Piece

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

theorem map_ctuBlock_zero_le_pieceCore_zero_of_uodd_twisted {f : ℕ} (hf : 2 ≤ f)
    {e : L ≃* StatedSp 3 K} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ f) ^ 2) {ι : K →+* F}
    {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c}
    {Φ : SU (unitaryInvolution F 2 f) (2 * 2 + 1) →* G} (hrange : Φ.range = neighbourCore e 2)
    (hN1 : ∀ x : StatedSp 2 K, Φ (ctuEmbed 1 le_rfl (unitaryInvolution F 2 f) ι hι (tauSp x)) =
      ((e.symm ((complSpEquiv 2 x : complSp K 2) : StatedSp 3 K) : L) : G)) :
    (ctuBlock (unitaryInvolution F 2 f) 1 ({0} : Finset (Fin 2))).map Φ ≤
      pieceCore e ({0} : Finset (Fin 3)) := by
  rw [pieceCore_eq e (k := 2) (by decide)]
  have hBperf : ⁅(ctuBlock (unitaryInvolution F 2 f) 1 ({0} : Finset (Fin 2))).map Φ,
      (ctuBlock (unitaryInvolution F 2 f) 1 ({0} : Finset (Fin 2))).map Φ⁆ =
        (ctuBlock (unitaryInvolution F 2 f) 1 ({0} : Finset (Fin 2))).map Φ := by
    rw [← Subgroup.map_commutator, commutator_ctuBlock_eq hF le_rfl (by decide) (fun h => by
      have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      omega)]
  refine le_perfectCore_of_perfect ?_ hBperf
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
  rw [complSpHom_apply, ← hN1, ← map_mul, ← map_mul, tauSp_diagSp_const]
  congr 1
  have hy : rootTorusHom K 2 0 (s * s) ∈ spBlock K ({0} : Finset (Fin 2)) := by
    rw [spBlock_singleton]
    exact rootTorusSp_le_longRootSp2 0 (rootTorusHom_mem_rootTorusSp 0 _)
  exact (commute_ctuBlock_ctuEmbed hx hy).symm

theorem cube_dvd_natCard_pieceCore_zero_of_uodd_twisted {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) {e : L ≃* StatedSp 3 K} {t : G} (hn : SpThreeUOddNormalized e t f 2 true) :
    (Nat.card K) ^ 3 ∣ Nat.card (pieceCore e ({0} : Finset (Fin 3))) := by
  obtain ⟨F, _, _, _, hF, ι, hι, Φ, hrange, hker, hN1, -⟩ := hn
  have h1 := Subgroup.card_dvd_of_le
    (map_ctuBlock_zero_le_pieceCore_zero_of_uodd_twisted hf hF hrange (fun x => hN1 x))
  rw [natCard_map_ctuBlock_zero_two hF hker, natCard_ctuBlock_zero_two hF, ← hKc] at h1
  exact (Dvd.intro (((Nat.card K) ^ 2 - 1) * ((Nat.card K) ^ 3 + 1)) (by ring)).trans h1

theorem false_of_siegel_normal_of_uodd_twisted (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp 3 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hn : SpThreeUOddNormalized e t f 2 true)
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
  have hu := uOddHeis_mem_ctuBlock hσ hω
  have hw : t * Φ (uOddHeis hσ hω) * t⁻¹ * (Φ (uOddHeis hσ hω))⁻¹ =
      Φ ((uOddHeis hσ hω)⁻¹ * (uOddHeis hσ hω)⁻¹) := by
    rw [hN3, ctuaBarAut_uOddHeis, ← map_inv, ← map_mul]
  have hwB : (uOddHeis hσ hω)⁻¹ * (uOddHeis hσ hω)⁻¹ ∈
      ctuBlock (unitaryInvolution F 2 f) 1 ({0} : Finset (Fin 2)) :=
    mul_mem (inv_mem hu) (inv_mem hu)
  have hw1 : Φ ((uOddHeis hσ hω)⁻¹ * (uOddHeis hσ hω)⁻¹) ≠ 1 := by
    intro h
    apply uOddHeis_inv_sq_ne_one hσ hω
    exact injOn_ctuBlock_of_ker_le_center (p := 2) hF (by norm_num)
      (fun h' => by have := (Prod.mk.inj h').1; omega) hker (Finset.mem_singleton_self 0) hwB
      (one_mem _) (by rw [h, map_one])
  have hord : orderOf (Φ ((uOddHeis hσ hω)⁻¹ * (uOddHeis hσ hω)⁻¹)) = 2 :=
    orderOf_eq_prime (by rw [sq, ← map_mul, uOddHeis_inv_sq_mul_self, map_one]) hw1
  have hMu : Φ (uOddHeis hσ hω) ∈ pieceCore e ({0} : Finset (Fin 3)) :=
    map_ctuBlock_zero_le_pieceCore_zero_of_uodd_twisted hf hF hrange (fun x => hN1 x)
      ⟨_, hu, rfl⟩
  refine false_of_mk_mem_center_of_orderOf_commutator htX
    (pieceCore_singleton_le_centralizer_siegelTorus e (j := 0) (by decide) hMu) ?_ hcen
  rw [hw]
  exact hord

end Piece

theorem spThreeUnitaryOddTwistedFalseInput_of_clauses
    (hcat : LinearPilot.SLmCatalogueClausesAt 3) (hdet : LinearPilot.SLmEvenTypeDetAt 3) :
    SpThreeUnitaryOddTwistedFalseInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t hto hKt hroot htw
  have htC : t ∈ centralizer (L : Set G) := by
    have h1 : t ∈ zpowers t := mem_zpowers t
    rw [← hKt] at h1
    exact h1.1
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hq2 : 2 ∣ Nat.card K := by
    rw [hKc]
    exact dvd_pow_self 2 (by omega)
  have hn := spThreeUOddNormalized_of_twisted hset hKc hf e htC hto 2 (hroot 2) htw
  have h3 := cube_dvd_natCard_pieceCore_zero_of_uodd_twisted hKc hf hn
  obtain ⟨F', _, _, ι, σ', hσ, hfix⟩ := exists_quadraticExtension K
  obtain ⟨hσ1, hσσ⟩ := ne_one_and_mul_self_of_orderOf_eq_two hσ
  have hF' : Nat.card F' = Nat.card K ^ 2 := by
    rw [LinearPilot.natCard_eq_two_pow_of_fixedField hKc ι hσ1 hσσ hfix, hKc, ← pow_mul,
      mul_comm]
  rcases siegel_normal_or_fieldParam_or_swapParam hcat hdet hset hKc hf le_rfl e htC hto
    (oddCentralSplit_siegelLevi (by norm_num)) ι hσ1 hσσ hfix with ⟨htX, hnorm⟩ | hS | hS
  · exact false_of_siegel_normal_of_uodd_twisted hset hKc hf e htC hto hn htX hnorm
  · obtain ⟨S⟩ := hS
    exact false_of_siegelFieldParam_of_cube_dvd hK4 hq2 hF' S h3
  · obtain ⟨S⟩ := hS
    exact false_of_siegelSwapParam_of_cube_dvd hK4 hq2 S h3

theorem spThreeKindCoverInput_unitaryOdd_of_clauses
    (hcat : LinearPilot.SLmCatalogueClausesAt 3) (hdet : LinearPilot.SLmEvenTypeDetAt 3)
    (hs : SpThreeUnitaryOddStandardInput) : SpThreeKindCoverInput .unitaryOdd :=
  spThreeKindCoverInput_unitaryOdd_of_oriented hs
    (spThreeUnitaryOddTwistedFalseInput_of_clauses hcat hdet)

end CFSG.SeitzReduction.SymplecticPilot
