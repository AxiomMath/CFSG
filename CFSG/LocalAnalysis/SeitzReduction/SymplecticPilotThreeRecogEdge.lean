module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeRecogModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCores
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelPiece
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR8RootTorus

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.SeitzReduction.F4Pilot (statedSpMap centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

section Generic

variable {E P : Type*} [Group E] [Group P] [Finite E] [Finite P]

omit [Finite P] in
theorem map_perfectCore_centralizer_le (ρ : E →* P) (Y : Subgroup E) :
    (perfectCore (centralizer (Y : Set E))).map ρ ≤
      perfectCore (centralizer ((Y.map ρ : Subgroup P) : Set P)) := by
  refine le_perfectCore_of_perfect ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 (perfectCore_le _ hx) y hy]
  · rw [← Subgroup.map_commutator, perfectCore_perfect]

theorem le_centralizer_of_commutator_le_center_of_perfect_three {H : Type*} [Group H]
    {C J : Subgroup H} (hC : ⁅C, C⁆ = C) (hCJ : ⁅C, J⁆ ≤ center H) :
    C ≤ centralizer (J : Set H) := by
  have hZC : ⁅center H, C⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    intro z hz
    rw [mem_centralizer_iff]
    intro c _
    exact mem_center_iff.1 hz c
  have h1 : ⁅⁅C, J⁆, C⁆ = ⊥ := eq_bot_iff.2 ((commutator_mono hCJ le_rfl).trans hZC.le)
  have h2 : ⁅⁅J, C⁆, C⁆ = ⊥ := by rw [commutator_comm J C]; exact h1
  have h3 := commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hC] at h3
  exact commutator_eq_bot_iff_le_centralizer.1 h3

omit [Finite P] in
theorem le_map_perfectCore_centralizer (ρ : E →* P) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ center E) (Y : Subgroup E) {Q : Subgroup P} (hQ : ⁅Q, Q⁆ = Q)
    (hQY : Q ≤ centralizer ((Y.map ρ : Subgroup P) : Set P)) :
    Q ≤ (perfectCore (centralizer (Y : Set E))).map ρ := by
  have : Finite P := Finite.of_surjective ρ hρ
  set Q₁ := perfectCore (Q.comap ρ) with hQ₁
  have hQ₁perf : ⁅Q₁, Q₁⁆ = Q₁ := perfectCore_perfect _
  have hQ₁map : Q₁.map ρ = Q := by
    rw [hQ₁, CFSG.Quasithin.map_perfectCore, Subgroup.map_comap_eq_self_of_surjective hρ,
      CFSG.Quasithin.perfectCore_eq_self_of_perfect hQ]
  have hcomm : ⁅Q₁, Y⁆ ≤ center E := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    apply hker
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    have hxQ : ρ x ∈ Q := hQ₁map ▸ Subgroup.mem_map_of_mem ρ hx
    exact (mem_centralizer_iff.1 (hQY hxQ) (ρ y) ⟨y, hy, rfl⟩).symm
  have hQ₁Y : Q₁ ≤ centralizer (Y : Set E) :=
    le_centralizer_of_commutator_le_center_of_perfect_three hQ₁perf hcomm
  rw [← hQ₁map]
  exact Subgroup.map_mono (le_perfectCore_of_perfect hQ₁Y hQ₁perf)

omit [Finite E] [Finite P] in
theorem exists_natCard_eq_natCard_map_mul [Finite E] (ρ : E →* P) (H : Subgroup E) :
    ∃ c, c ∣ Nat.card ρ.ker ∧ Nat.card H = Nat.card (H.map ρ) * c := by
  set ρH : H →* P := ρ.comp H.subtype with hρH
  have hrange : ρH.range = H.map ρ := by
    rw [hρH, MonoidHom.range_comp, range_subtype]
  refine ⟨Nat.card ρH.ker, ?_, ?_⟩
  · have hle : ρH.ker.map H.subtype ≤ ρ.ker := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    have h1 := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective H.subtype_injective] at h1
  · rw [← hrange, ← Subgroup.index_ker, mul_comm, Subgroup.card_mul_index]

end Generic


section EdgeCore

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def edgeCoreSp (e : L ≃* StatedSp n K) (k l : Fin n) : Subgroup G :=
  centralizerPerfectCore (modelToG e (rootTorusSp K k) ⊔ modelToG e (rootTorusSp K l))

omit [Finite G] in
theorem edgeCoreSp_comm (e : L ≃* StatedSp n K) (k l : Fin n) :
    edgeCoreSp e k l = edgeCoreSp e l k := by
  rw [edgeCoreSp, edgeCoreSp, sup_comm]

theorem edgeCoreSp_eq (e : L ≃* StatedSp n K) (k l : Fin n) :
    edgeCoreSp e k l =
      perfectCore (neighbourCore e k ⊓ centralizer (modelToG e (rootTorusSp K l) : Set G)) :=
  F4Pilot.centralizerPerfectCore_sup _ _

theorem natCard_edgeCoreSp_eq (e : L ≃* StatedSp n K) (k l : Fin n)
    (hle : modelToG e (rootTorusSp K l) ≤ neighbourCore e k) :
    Nat.card (edgeCoreSp e k l) = Nat.card (perfectCore (centralizer
      (((modelToG e (rootTorusSp K l)).subgroupOf
        (centralizerPerfectCore (modelToG e (rootTorusSp K k))) :
        Subgroup (centralizerPerfectCore (modelToG e (rootTorusSp K k)))) :
          Set (centralizerPerfectCore (modelToG e (rootTorusSp K k)))))) := by
  set E := centralizerPerfectCore (modelToG e (rootTorusSp K k)) with hE
  set X := modelToG e (rootTorusSp K l) with hX
  set Y := X.subgroupOf E with hY
  have hmap : (centralizer (Y : Set E)).map E.subtype = E ⊓ centralizer (X : Set G) := by
    ext g
    simp only [mem_map, mem_inf, mem_centralizer_iff, SetLike.mem_coe, coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, fun x hx => ?_⟩
      have h1 := hy ⟨x, hle hx⟩ (by rw [hY, mem_subgroupOf]; exact hx)
      exact congrArg Subtype.val h1
    · rintro ⟨hgE, hg⟩
      exact ⟨⟨g, hgE⟩, fun y hy => Subtype.ext (hg y (mem_subgroupOf.1 hy)), rfl⟩
  rw [edgeCoreSp_eq, neighbourCore_def, ← hE, ← hX, ← hmap, ← CFSG.Quasithin.map_perfectCore,
    Subgroup.card_map_of_injective E.subtype_injective]

end EdgeCore

section Orientation

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
theorem proj_two_mul_two_injective : Function.Injective (proj (2 * 2) F) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro A hA
  rw [MonoidHom.mem_ker, proj_eq_one_iff] at hA
  obtain ⟨c, hc, hA⟩ := hA
  have hc4 : (c : F) ^ 4 = 1 := by
    have h := congrArg (fun u : Fˣ => (u : F)) hc
    simpa using h
  have h0 : ((c : F) - 1) ^ 4 = 0 := by
    have h1 : ((c : F) - 1) ^ 4 = (c : F) ^ 4 - 1 +
        2 * (-2 * (c : F) ^ 3 + 3 * (c : F) ^ 2 - 2 * (c : F) + 1) := by ring
    rw [h1, hc4, CharTwo.two_eq_zero, zero_mul, add_zero, sub_self]
  have hc1 : (c : F) = 1 := sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h0)
  rw [mem_bot]
  apply Subtype.ext
  rw [hA, hc1, map_one]
  rfl

omit [Finite F] in
variable (F) in
@[expose] noncomputable def slFourEquivProj :
    SpecialLinearGroup (Fin (2 * 2)) F ≃* projectiveSL (2 * 2) F :=
  MulEquiv.ofBijective (proj (2 * 2) F) ⟨proj_two_mul_two_injective, proj_surjective _ _⟩

omit [Finite F] in
theorem slFourEquivProj_symm_proj (x : SpecialLinearGroup (Fin (2 * 2)) F) :
    (slFourEquivProj F).symm (proj (2 * 2) F x) = x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

end Orientation


section Image

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite G] [Finite K] [CharP K 2] [Finite F] [CharP F 2] in
theorem statedSpMap_rootTorusHom (ι : K →+* F) {n : ℕ} (a : Fin n) (κ : Kˣ) :
    statedSpMap ι n (rootTorusHom K n a κ) = rootTorusHom F n a (Units.map (ι : K →* F) κ) := by
  rw [rootTorusHom_apply, rootTorusHom_apply, statedSpMap_diagSp_mulSingle]

omit [Finite G] [Finite K] [Finite F] in
theorem statedSpMap_tauSp_rootTorusHom (ι : K →+* F) (a : Fin 2) (κ : Kˣ) :
    statedSpMap ι 2 (tauSp (rootTorusHom K 2 a κ)) =
      tauSp (rootTorusHom F 2 a (Units.map (ι : K →* F) κ)) := by
  fin_cases a
  · rw [show ((⟨0, by omega⟩ : Fin 2)) = 0 from rfl, tauSp_rootTorusHom_zero,
      tauSp_rootTorusHom_zero, statedSpMap_diagSp]
    congr 1
    funext i
    fin_cases i <;> rfl
  · rw [show ((⟨1, by omega⟩ : Fin 2)) = 1 from rfl, tauSp_rootTorusHom_one,
      tauSp_rootTorusHom_one, statedSpMap_diagSp]
    congr 1
    funext i
    fin_cases i
    · rfl
    · simp

omit [Finite G] [Finite K] [CharP K 2] in
theorem modelToG_rootTorusSp_le_neighbourCore_three (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K)
    {k l : Fin 3} {a : Fin 2} (ha : k.succAbove a = l) :
    modelToG e (rootTorusSp K l) ≤ neighbourCore e k := by
  refine le_trans ?_ (modelToG_complSp_le_neighbourCore e hK (by norm_num) k)
  intro g hg
  obtain ⟨x, hx, rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hg
  obtain ⟨κ, rfl⟩ := mem_rootTorusSp.1 hx
  rw [← ha, ← coe_complSpEquiv_rootTorusHom]
  exact symm_mem_modelToG e (complSpEquiv k (rootTorusHom K 2 a κ)).2

omit [Finite G] [Finite K] [CharP K 2] [Finite F] in
theorem map_rootTorusSp_eq_of_N1 (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K) {k l : Fin 3}
    {a : Fin 2} (ha : k.succAbove a = l) (σ : K ≃+* F) (βK : StatedSp 2 K →* StatedSp 2 K)
    (βF : StatedSp 2 F →* StatedSp 2 F)
    (hβ : ∀ κ : Kˣ, statedSpMap (σ : K →+* F) 2 (βK (rootTorusHom K 2 a κ)) =
      βF (rootTorusHom F 2 a (Units.map (σ : K →+* F) κ)))
    (ρ : centralizerPerfectCore (modelToG e (rootTorusSp K k)) →* projectiveSL (2 * 2) F)
    (hN1 : ∀ (x : StatedSp 2 K) (y : centralizerPerfectCore (modelToG e (rootTorusSp K k))),
      (y : G) = ((e.symm (complSpEquiv k x : complSp K k) : L) : G) →
        ρ y = spModelPSL 2 F (statedSpMap (σ : K →+* F) 2 (βK x))) :
    ((modelToG e (rootTorusSp K l)).subgroupOf
        (centralizerPerfectCore (modelToG e (rootTorusSp K k)))).map
        ((slFourEquivProj F).symm.toMonoidHom.comp ρ) =
      ((rootTorusSp F a).map βF).map (spModelSL 2 F) := by
  have hle := modelToG_rootTorusSp_le_neighbourCore_three hK e ha
  have hval : ∀ (κ : Kˣ) (y : centralizerPerfectCore (modelToG e (rootTorusSp K k))),
      (y : G) = ((e.symm (rootTorusHom K 3 l κ) : L) : G) →
        (slFourEquivProj F).symm (ρ y) =
          spModelSL 2 F (βF (rootTorusHom F 2 a (Units.map (σ : K →+* F) κ))) := by
    intro κ y hy
    have hy' : (y : G) = ((e.symm (complSpEquiv k (rootTorusHom K 2 a κ) : complSp K k) :
        L) : G) := by
      rw [hy, coe_complSpEquiv_rootTorusHom, ha]
    rw [hN1 _ y hy', hβ, spModelPSL_apply, slFourEquivProj_symm_proj]
  ext d
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf] at hy
    obtain ⟨x, hx, hxy⟩ := (UnitaryPilot.mem_modelToG e).1 hy
    obtain ⟨κ, rfl⟩ := mem_rootTorusSp.1 hx
    refine ⟨_, ⟨_, rootTorusHom_mem_rootTorusSp a (Units.map (σ : K →+* F) κ), rfl⟩, ?_⟩
    exact (hval κ y hxy.symm).symm
  · rintro ⟨_, ⟨_, hz, rfl⟩, rfl⟩
    obtain ⟨μ, rfl⟩ := mem_rootTorusSp.1 hz
    set κ : Kˣ := Units.map (σ.symm : F →+* K) μ with hκ
    have hμ : Units.map (σ : K →+* F) κ = μ := by
      ext
      simp [hκ]
    have hmem : ((e.symm (rootTorusHom K 3 l κ) : L) : G) ∈
        centralizerPerfectCore (modelToG e (rootTorusSp K k)) :=
      hle (symm_mem_modelToG e (rootTorusHom_mem_rootTorusSp l κ))
    refine ⟨⟨_, hmem⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_subgroupOf]
      exact symm_mem_modelToG e (rootTorusHom_mem_rootTorusSp l κ)
    · change (slFourEquivProj F).symm (ρ ⟨_, hmem⟩) = _
      rw [hval κ ⟨_, hmem⟩ rfl, hμ]

end Image


section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem not_sq_dvd_mul_sq_sub_one_mul {q c : ℕ} (hq2 : 2 ∣ q) (hq : 0 < q) (hc : Odd c) :
    ¬ q ^ 2 ∣ q * (q ^ 2 - 1) * c := by
  intro h
  have h1 : q * q ∣ q * ((q ^ 2 - 1) * c) := by
    rw [← pow_two, ← mul_assoc]
    exact h
  have h2 : q ∣ (q ^ 2 - 1) * c := Nat.dvd_of_mul_dvd_mul_left hq h1
  have hev : Even (q ^ 2) := Nat.even_pow.2 ⟨even_iff_two_dvd.2 hq2, two_ne_zero⟩
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have hodd : Odd ((q ^ 2 - 1) * c) := (Nat.Even.sub_odd hq1 hev odd_one).mul hc
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (hq2.trans h2))

omit [Finite K] [CharP K 2] in
theorem not_sq_dvd_natCard_edgeCoreSp_of_std {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {k l : Fin 3} (hlk : l ≠ k) (σ : K ≃+* F)
    (ρ : centralizerPerfectCore (modelToG e (rootTorusSp K k)) →* projectiveSL (2 * 2) F)
    (hodd : Odd (Nat.card ρ.ker))
    (hN1 : ∀ (x : StatedSp 2 K) (y : centralizerPerfectCore (modelToG e (rootTorusSp K k))),
      (y : G) = ((e.symm (complSpEquiv k x : complSp K k) : L) : G) →
        ρ y = spModelPSL 2 F (statedSpMap (σ : K →+* F) 2 x)) :
    ¬ (Nat.card K) ^ 2 ∣ Nat.card (edgeCoreSp e k l) := by
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hFK : Nat.card F = Nat.card K := (Nat.card_congr σ.toEquiv).symm
  have hF4 : 4 ≤ Nat.card F := hFK ▸ hK4
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hlk
  have hle := modelToG_rootTorusSp_le_neighbourCore_three hK4 e ha
  set ρ' := (slFourEquivProj F).symm.toMonoidHom.comp ρ with hρ'
  have hY := map_rootTorusSp_eq_of_N1 hK4 e ha σ (MonoidHom.id _) (MonoidHom.id _)
    (fun κ => statedSpMap_rootTorusHom (σ : K →+* F) a κ) ρ (fun x y hy => hN1 x y hy)
  rw [Subgroup.map_id] at hY
  rw [natCard_edgeCoreSp_eq e k l hle]
  set Y := (modelToG e (rootTorusSp K l)).subgroupOf
    (centralizerPerfectCore (modelToG e (rootTorusSp K k))) with hYdef
  set C := perfectCore (centralizer (Y : Set (centralizerPerfectCore
    (modelToG e (rootTorusSp K k))))) with hC
  have hCle : C.map ρ' ≤ blockSpecialLinear (offPlaneSL a) := by
    have h1 := map_perfectCore_centralizer_le ρ' Y
    rw [hY] at h1
    exact h1.trans (perfectCore_centralizer_stdTorusSL hF4 a).le
  obtain ⟨c, hc, hcard⟩ := exists_natCard_eq_natCard_map_mul ρ' C
  have hker : ρ'.ker = ρ.ker := by
    ext y
    simp [hρ']
  have hcodd : Odd c := Odd.of_dvd_nat hodd (hker ▸ hc)
  have hdvd : Nat.card (C.map ρ') ∣ Nat.card (SpecialLinearGroup (Fin 2) F) := by
    rw [← natCard_blockSpecialLinear_of_card_two (card_offPlaneSL a)]
    exact Subgroup.card_dvd_of_le hCle
  rw [hcard]
  intro h
  have h2 := h.trans (Nat.mul_dvd_mul_right hdvd c)
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hFK] at h2
  have hq2 : 2 ∣ Nat.card K := by
    rw [hKc]
    exact dvd_pow_self 2 (by omega)
  exact not_sq_dvd_mul_sq_sub_one_mul hq2 (by omega) hcodd h2

omit [Finite K] in
theorem sq_dvd_natCard_edgeCoreSp_of_twisted {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {k l : Fin 3} (hlk : l ≠ k) (σ : K ≃+* F)
    (ρ : centralizerPerfectCore (modelToG e (rootTorusSp K k)) →* projectiveSL (2 * 2) F)
    (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ center (centralizerPerfectCore (modelToG e (rootTorusSp K k))))
    (hN1 : ∀ (x : StatedSp 2 K) (y : centralizerPerfectCore (modelToG e (rootTorusSp K k))),
      (y : G) = ((e.symm (complSpEquiv k x : complSp K k) : L) : G) →
        ρ y = spModelPSL 2 F (statedSpMap (σ : K →+* F) 2 (tauSp x))) :
    (Nat.card K) ^ 2 ∣ Nat.card (edgeCoreSp e k l) := by
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hFK : Nat.card F = Nat.card K := (Nat.card_congr σ.toEquiv).symm
  have hF4 : 4 ≤ Nat.card F := hFK ▸ hK4
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hlk
  have hle := modelToG_rootTorusSp_le_neighbourCore_three hK4 e ha
  set ρ' := (slFourEquivProj F).symm.toMonoidHom.comp ρ with hρ'
  have hY : _ = twTorusSL F a := map_rootTorusSp_eq_of_N1 hK4 e ha σ tauSp tauSp
    (fun κ => statedSpMap_tauSp_rootTorusHom (σ : K →+* F) a κ) ρ hN1
  rw [natCard_edgeCoreSp_eq e k l hle]
  set Y := (modelToG e (rootTorusSp K l)).subgroupOf
    (centralizerPerfectCore (modelToG e (rootTorusSp K k))) with hYdef
  set Q := blockSpecialLinear (K := F) (twBlockSL a) ⊔
    blockSpecialLinear (K := F) (twBlockSL a)ᶜ with hQ
  have hQperf : ⁅Q, Q⁆ = Q := commutator_sup_eq_self_of_perfect
    (LinearPilot.commutator_blockSpecialLinear_eq_of_two_le (F := F) (card_twBlockSL a).ge hF4)
    (LinearPilot.commutator_blockSpecialLinear_eq_of_two_le (F := F) (card_compl_twBlockSL a).ge
      hF4)
  have hQY : Q ≤ centralizer ((Y.map ρ' : Subgroup _) : Set _) := by
    rw [hY]
    exact (sup_twBlock_le_perfectCore_centralizer_twTorusSL hF4 a).trans (perfectCore_le _)
  have hker' : ρ'.ker ≤ center (centralizerPerfectCore (modelToG e (rootTorusSp K k))) := by
    have : ρ'.ker = ρ.ker := by
      ext y
      simp [hρ']
    rw [this]
    exact hker
  have hQC := le_map_perfectCore_centralizer ρ' ((slFourEquivProj F).symm.surjective.comp hρ)
    hker' Y hQperf hQY
  have h1 : Nat.card Q ∣ Nat.card (perfectCore (centralizer (Y : Set (centralizerPerfectCore
      (modelToG e (rootTorusSp K k)))))) :=
    (Subgroup.card_dvd_of_le hQC).trans (Subgroup.card_map_dvd _ _)
  rw [hQ, natCard_sup_twBlock] at h1
  have h2 : Nat.card K ∣ Nat.card (SpecialLinearGroup (Fin 2) F) := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hFK]
    exact dvd_mul_right _ _
  exact (pow_two (Nat.card K) ▸ Nat.mul_dvd_mul h2 h2).trans h1

end Main

end CFSG.SeitzReduction.SymplecticPilot
