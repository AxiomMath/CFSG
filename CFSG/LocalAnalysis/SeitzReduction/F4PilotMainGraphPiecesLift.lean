module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphPiecesMain
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSL
public import CFSG.LieType.Steinberg.CentralExt.SLMilnor
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSetup
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointSchreier
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotSwapBLift
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormalCore
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParamLift

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
  CFSG.Assembly.LowTwoRank
open Matrix
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointSchreier
  (orthogonal_geometry_classical_model_Schreier)

local instance f4PilotMainGraphPiecesLiftNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section SLLift

variable {F : Type} [Field F] [Finite F] {m : ℕ}

theorem exists_sl_lift_of_central (hm : 4 ≤ m) {E : Type*} [Group E] [Group.IsPerfect E]
    (ρ : E →* Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ center E) :
    ∃ Φ : SpecialLinearGroup (Fin (m + 1)) F →* E, Function.Surjective Φ ∧
      ∀ g, ρ (Φ g) = QuotientGroup.mk' (center (SpecialLinearGroup (Fin (m + 1)) F)) g := by
  set π : SpecialLinearGroup (Fin (m + 1)) F →*
      Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F :=
    QuotientGroup.mk' (center (SpecialLinearGroup (Fin (m + 1)) F))
  set P : Subgroup (E × SpecialLinearGroup (Fin (m + 1)) F) :=
    MonoidHom.eqLocus (ρ.comp (MonoidHom.fst _ _)) (π.comp (MonoidHom.snd _ _)) with hPdef
  have hmemP : ∀ p : E × SpecialLinearGroup (Fin (m + 1)) F, p ∈ P ↔ ρ p.1 = π p.2 :=
    fun p => Iff.rfl
  set p₂ : P →* SpecialLinearGroup (Fin (m + 1)) F := (MonoidHom.snd _ _).comp P.subtype
  have hp₂ : Function.Surjective p₂ := by
    intro g
    obtain ⟨y, hy⟩ := hρ (π g)
    exact ⟨⟨(y, g), (hmemP _).2 hy⟩, rfl⟩
  have hp₂ker : p₂.ker ≤ center P := by
    intro x hx
    rw [mem_center_iff]
    intro z
    have hx2 : (x : E × SpecialLinearGroup (Fin (m + 1)) F).2 = 1 := hx
    have hx1 : (x : E × SpecialLinearGroup (Fin (m + 1)) F).1 ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, (hmemP _).1 x.2, hx2, map_one]
    have hc := mem_center_iff.1 (hker hx1) z.1.1
    apply Subtype.ext
    apply Prod.ext
    · exact hc
    · change z.1.2 * x.1.2 = x.1.2 * z.1.2
      rw [hx2, mul_one, one_mul]
  obtain ⟨σ, hσ⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_four_le hm hp₂
    hp₂ker
  set Φ : SpecialLinearGroup (Fin (m + 1)) F →* E :=
    (MonoidHom.fst _ _).comp (P.subtype.comp σ)
  have hΦ : ∀ g, ρ (Φ g) = π g := by
    intro g
    have h1 := (hmemP _).1 (σ g).2
    have h2 : (σ g).1.2 = g := hσ g
    calc ρ (Φ g) = ρ (σ g).1.1 := rfl
      _ = π (σ g).1.2 := h1
      _ = π g := by rw [h2]
  refine ⟨Φ, ?_, hΦ⟩
  have htop : (⊤ : Subgroup E) ≤ Φ.range := by
    refine perfect_le_of_forall_exists_commute (by
      rw [← _root_.commutator_def]
      exact Group.IsPerfect.commutator_eq_top) le_top fun a _ => ?_
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective
      (center (SpecialLinearGroup (Fin (m + 1)) F)) (ρ a)
    refine ⟨Φ g, ⟨g, rfl⟩, (Φ g)⁻¹ * a, by group, fun b _ => ?_⟩
    have hz : (Φ g)⁻¹ * a ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hΦ, hg, inv_mul_cancel]
    exact (mem_center_iff.1 (hker hz) b).symm
  intro a
  obtain ⟨g, hg⟩ := htop (mem_top a)
  exact ⟨g, hg⟩


theorem exists_lift_of_central {M Q : Type} [Group M] [Finite M] [Group Q] (π : M →* Q)
    (hπ : Function.Surjective π)
    (hsplit : ∀ (E' : Type) [Group E'] [Finite E'] (π' : E' →* M), Function.Surjective π' →
      π'.ker ≤ center E' → ∃ s : M →* E', ∀ g, π' (s g) = g)
    {E : Type} [Group E] [Finite E] [Group.IsPerfect E] (ρ : E →* Q) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ center E) :
    ∃ Φ : M →* E, Function.Surjective Φ ∧ ∀ g, ρ (Φ g) = π g := by
  set P : Subgroup (E × M) :=
    MonoidHom.eqLocus (ρ.comp (MonoidHom.fst _ _)) (π.comp (MonoidHom.snd _ _)) with hPdef
  have hmemP : ∀ p : E × M, p ∈ P ↔ ρ p.1 = π p.2 := fun p => Iff.rfl
  set p₂ : P →* M := (MonoidHom.snd _ _).comp P.subtype
  have hp₂ : Function.Surjective p₂ := by
    intro g
    obtain ⟨y, hy⟩ := hρ (π g)
    exact ⟨⟨(y, g), (hmemP _).2 hy⟩, rfl⟩
  have hp₂ker : p₂.ker ≤ center P := by
    intro x hx
    rw [mem_center_iff]
    intro z
    have hx2 : (x : E × M).2 = 1 := hx
    have hx1 : (x : E × M).1 ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, (hmemP _).1 x.2, hx2, map_one]
    have hc := mem_center_iff.1 (hker hx1) z.1.1
    apply Subtype.ext
    apply Prod.ext
    · exact hc
    · change z.1.2 * x.1.2 = x.1.2 * z.1.2
      rw [hx2, mul_one, one_mul]
  obtain ⟨σ, hσ⟩ := hsplit P p₂ hp₂ hp₂ker
  set Φ : M →* E := (MonoidHom.fst _ _).comp (P.subtype.comp σ)
  have hΦ : ∀ g, ρ (Φ g) = π g := by
    intro g
    have h1 := (hmemP _).1 (σ g).2
    have h2 : (σ g).1.2 = g := hσ g
    calc ρ (Φ g) = ρ (σ g).1.1 := rfl
      _ = π (σ g).1.2 := h1
      _ = π g := by rw [h2]
  refine ⟨Φ, ?_, hΦ⟩
  have htop : (⊤ : Subgroup E) ≤ Φ.range := by
    refine perfect_le_of_forall_exists_commute (by
      rw [← _root_.commutator_def]
      exact Group.IsPerfect.commutator_eq_top) le_top fun a _ => ?_
    obtain ⟨g, hg⟩ := hπ (ρ a)
    refine ⟨Φ g, ⟨g, rfl⟩, (Φ g)⁻¹ * a, by group, fun b _ => ?_⟩
    have hz : (Φ g)⁻¹ * a ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hΦ, hg, inv_mul_cancel]
    exact (mem_center_iff.1 (hker hz) b).symm
  intro a
  obtain ⟨g, hg⟩ := htop (mem_top a)
  exact ⟨g, hg⟩

end SLLift


section BLift


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_surjective_neighbourCore_X_of_hr8Kind {t : G} {f : ℕ} (hw : F4Work L K t f)
    (hf : 2 ≤ f) (e : L ≃* adjointGroup .F4 K) {κ : Sp6Kind} (hκ : κ ≠ .swap)
    (hX : HR8Kind e t f .X κ)
    (hOut : ∀ (Kb : Type) [Group Kb] [Finite Kb], Group.IsPerfect Kb →
      Sp6KindType (Kb ⧸ center Kb) f κ → Group.IsSolvable (Outer Kb)) :
    ∃ (S : Type) (_ : Group S), Sp6KindType S f κ ∧
      ∃ ρ : neighbourCore e .X →* S, Function.Surjective ρ ∧
        ρ.ker ≤ center (neighbourCore e .X) := by
  have := finite_of_natCard_eq_two_pow hw.card_eq
  have := charP_two_of_natCard_eq_two_pow hw.card_eq
  have hq : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have htC := hw.mem_centralizer
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  set X : Subgroup G := neighbourTorusG e .X with hXdef
  set H : Subgroup G := centralizer (X : Set G) with hHdef
  set D : Subgroup G := neighbourLeviG e .X with hDdef
  obtain ⟨htX, Kb, hKb, -, hcase⟩ := hX
  obtain ⟨-, -, hlt, hsK, hsN, hov, hty⟩ := hcase.resolve_right fun h => hκ h.1
  set π := QuotientGroup.mk' (oddCore H) with hπ
  set Db : Subgroup (H ⧸ oddCore H) := (D.subgroupOf H).map π with hDbdef
  set t' : H := ⟨t, htX⟩ with ht'def
  set s : H ⧸ oddCore H := π t' with hsdef
  have ht't' : t' * t' = 1 := Subtype.ext htt
  have hss : s * s = 1 := by rw [hsdef, ← map_mul, ht't', map_one]
  have hsC : s ∉ centralizer (Kb : Set (H ⧸ oddCore H)) := by
    intro hc
    refine hov.1 ⟨1, MulEquiv.ext fun k => Subtype.ext ?_⟩
    rw [map_one, MulAut.one_apply, coe_normalizerMonoidHom_mk_apply Kb hsN,
      ← mem_centralizer_iff.1 hc k k.2, mul_inv_cancel_right]
  have hs1 : s ≠ 1 := fun h => hsK (h ▸ one_mem Kb)
  have hs2 : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hss) hs1
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (map_subtype_le _ hd))
  have hsD : s ∈ centralizer (Db : Set (H ⧸ oddCore H)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [hsdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_torusLineR hw.standard.standard htC hw.orderOf_eq
    hw.inf_eq hf hw.card_eq e (X := X) rfl htX (D := D) rfl
  have hKbP : Group.IsPerfect Kb := hKb.1.1
  have hOutK : Group.IsSolvable (Outer Kb) := hOut Kb hKbP hty
  have hcore := LinearPilot.perfectCore_top_eq_of_isComponent
    (pPrimeCore_two_quotient_oddCore_eq_bot H) hKb hlt.le hs2 hsD hsN hsC hsyl hOutK
  have hTodd : Odd (Nat.card ((torusLineR K).subgroupOf (adjointGroup .F4 K))) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe torusLineR_le_adjointGroup).toEquiv]
    exact odd_card_torusLineR hw.one_le hw.card_eq
  have hC := mem_center_of_mem_oddCore_of_commute_sup hw.card_eq hw.standard.standard htC
    hw.orderOf_eq hw.inf_eq e (centralizer_torusLineR_eq hq) torusLineR_subgroupOf_le_centralizer
    torusLineR_subgroupOf_le_centralizer_self hTodd le_rfl (X := X) rfl htX (D := D) rfl
  have hB : HasBLift Kb := hasBLift_of_le_center ht't' (isPerfect_iff.mp hKbP) hsN
    (le_commutator_zpowers_of_isQuasisimple hKb.1 hsN hsC) hC
  obtain ⟨qh, hqs, hqker, -⟩ :=
    LinearPilot.exists_surjective_centralizerPerfectCore_of_perfectCore_eq hcore hB
  have hEperf : Group.IsPerfect (centralizerPerfectCore X) :=
    isPerfect_iff.mpr (commutator_centralizerPerfectCore X)
  refine ⟨Kb ⧸ center Kb, inferInstance, hty, (QuotientGroup.mk' (center Kb)).comp qh,
    (QuotientGroup.mk'_surjective _).comp hqs, fun y hy => ?_⟩
  have hy' : qh y ∈ center Kb := by
    have hy2 : QuotientGroup.mk' (center Kb) (qh y) = 1 := hy
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy2
  exact CFSG.ComponentClassification.OddSelector.mem_center_of_map_mem_center qh hqker hy'


theorem exists_surjective_neighbourCore_of_hr8Kind {t : G} {f : ℕ} (hw : F4Work L K t f)
    (hf : 2 ≤ f) (e : L ≃* adjointGroup .F4 K) {N : AmalgamNeighbour} (hN : N ≠ .X')
    {κ : Sp6Kind} (hκ : κ ≠ .swap) (h : HR8Kind e t f N κ)
    (hOut : ∀ (Kb : Type) [Group Kb] [Finite Kb], Group.IsPerfect Kb →
      Sp6KindType (Kb ⧸ center Kb) f κ → Group.IsSolvable (Outer Kb)) :
    ∃ (S : Type) (_ : Group S), Sp6KindType S f κ ∧
      ∃ ρ : neighbourCore e N →* S, Function.Surjective ρ ∧
        ρ.ker ≤ center (neighbourCore e N) := by
  cases N with
  | X => exact exists_surjective_neighbourCore_X_of_hr8Kind hw hf e hκ h hOut
  | Y =>
    have := finite_of_natCard_eq_two_pow hw.card_eq
    have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_two_of_natCard_eq_two_pow hw.card_eq
    rw [neighbourCore_Y_eq_X]
    exact exists_surjective_neighbourCore_X_of_hr8Kind hw hf _ hκ ((hr8Kind_Y_iff_X e).1 h) hOut
  | X' => exact absurd rfl hN

end BLift

section Linear

set_option linter.unusedVariables false in
theorem statedLieAdmissible_of_lieModel_PSL {S : Type} [Group S] {n p f : ℕ} (hn : n ≠ 0)
    (h : LieModel S .PSL n p f) : StatedLieAdmissible .PSL n p f :=
  CFSG.Blueprint.LieModel.admissible h

theorem isSolvable_outer_of_lieModel_PSL_quotient {Kb : Type} [Group Kb] (hKb : Group.IsPerfect Kb)
    {n f : ℕ} (hn : 3 ≤ n) (h : LieModel (Kb ⧸ center Kb) .PSL n 2 f) :
    Group.IsSolvable (Outer Kb) := by
  obtain ⟨F, _, _, -, ⟨ε⟩⟩ :=
    CFSG.ComponentClassification.CatLeafProof.nonempty_mulEquiv_psl_of_lieModel
    (statedLieAdmissible_of_lieModel_PSL (by omega) h) h
  have ε' : Kb ⧸ center Kb ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n F :=
    ε.trans (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center n F).symm)
  have := LinearPilot.isSolvable_outer_of_mulEquiv hn ε'
  exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient Kb

theorem exists_sl_cover_of_surjective {G : Type} [Group G] {E : Subgroup G}
    (hE : Group.IsPerfect E) {S : Type} [Group S] {m f : ℕ} (hm : 4 ≤ m)
    (hS : LieModel S .PSL (m + 1) 2 f) (ρ : E →* S) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ center E) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ f ∧
      ∃ Φ : SpecialLinearGroup (Fin (m + 1)) F →* G, Φ.range = E ∧
        Φ.ker ≤ center (SpecialLinearGroup (Fin (m + 1)) F) := by
  obtain ⟨F, _, _, hF, ⟨ε⟩⟩ :=
    CFSG.ComponentClassification.CatLeafProof.nonempty_mulEquiv_psl_of_lieModel
    (statedLieAdmissible_of_lieModel_PSL (by omega) hS) hS
  set ρ' : E →* Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F := ε.toMonoidHom.comp ρ
  have hρ' : Function.Surjective ρ' := ε.surjective.comp hρ
  have hker' : ρ'.ker ≤ center E := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact ε.map_eq_one_iff.mp hx
  obtain ⟨Φ₀, hΦ₀s, hΦ₀⟩ := exists_sl_lift_of_central hm ρ' hρ' hker'
  refine ⟨F, inferInstance, inferInstance, hF, E.subtype.comp Φ₀, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hΦ₀s, ← MonoidHom.range_eq_map,
      range_subtype]
  · intro g hg
    have hg₀ : Φ₀ g = 1 := E.subtype_injective (by rw [map_one]; exact hg)
    have h1 := hΦ₀ g
    rw [hg₀, map_one] at h1
    rw [eq_comm, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1

theorem isSolvable_outer_of_sp6KindType_graph {Kb : Type} [Group Kb] (hKb : Group.IsPerfect Kb)
    {f : ℕ} {κ : Sp6Kind} (hκF : κ ≠ .field) (hκS : κ ≠ .swap)
    (h : Sp6KindType (Kb ⧸ center Kb) f κ) : Group.IsSolvable (Outer Kb) := by
  have hom : ∀ {t : StatedLieTag}, (t = .POmegaPlus ∨ t = .POmegaMinus) →
      LieModel (Kb ⧸ center Kb) t 4 2 f → Group.IsSolvable (Outer Kb) := by
    intro t ht hm
    rcases hm with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · have := (orthogonal_geometry_classical_model_Schreier t (Or.inr ht) hc).2.2
      exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient Kb
    all_goals exact absurd h0 (by norm_num)
  cases κ with
  | field => exact absurd rfl hκF
  | swap => exact absurd rfl hκS
  | linear6 => exact isSolvable_outer_of_lieModel_PSL_quotient hKb (by norm_num) h
  | linear7 => exact isSolvable_outer_of_lieModel_PSL_quotient hKb (by norm_num) h
  | unitary6 =>
    have := CFSG.SeitzReduction.UnitaryPilot.isSolvable_outer_of_lieModel h
    exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient Kb
  | unitary7 =>
    have := CFSG.SeitzReduction.UnitaryPilot.isSolvable_outer_of_lieModel h
    exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient Kb
  | omegaPlus8 => exact hom (.inl rfl) h
  | omegaMinus8 => exact hom (.inr rfl) h

end Linear

section LinearNeighbour


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_sl6_cover_neighbourCore {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) {N : AmalgamNeighbour} (hN : N ≠ .X')
    (h : HR8Kind e t f N .linear6) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ f ∧
      ∃ Φ : SpecialLinearGroup (Fin 6) F →* G, Φ.range = neighbourCore e N ∧
        Φ.ker ≤ center (SpecialLinearGroup (Fin 6) F) := by
  obtain ⟨S, _, hS, ρ, hρ, hker⟩ := exists_surjective_neighbourCore_of_hr8Kind hw hf e hN
    (by decide) h fun Kb _ _ hKb hty =>
      isSolvable_outer_of_lieModel_PSL_quotient hKb (by norm_num) hty
  exact exists_sl_cover_of_surjective (m := 5)
    (isPerfect_iff.mpr (commutator_centralizerPerfectCore _)) (by norm_num) hS ρ hρ hker

theorem exists_sl7_cover_neighbourCore {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) {N : AmalgamNeighbour} (hN : N ≠ .X')
    (h : HR8Kind e t f N .linear7) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ f ∧
      ∃ Φ : SpecialLinearGroup (Fin 7) F →* G, Φ.range = neighbourCore e N ∧
        Φ.ker ≤ center (SpecialLinearGroup (Fin 7) F) := by
  obtain ⟨S, _, hS, ρ, hρ, hker⟩ := exists_surjective_neighbourCore_of_hr8Kind hw hf e hN
    (by decide) h fun Kb _ _ hKb hty =>
      isSolvable_outer_of_lieModel_PSL_quotient hKb (by norm_num) hty
  exact exists_sl_cover_of_surjective (m := 6)
    (isPerfect_iff.mpr (commutator_centralizerPerfectCore _)) (by norm_num) hS ρ hρ hker


theorem exists_surjective_neighbourCore_of_hr8Kind_graph {t : G} {f : ℕ} (hw : F4Work L K t f)
    (hf : 2 ≤ f) (e : L ≃* adjointGroup .F4 K) {N : AmalgamNeighbour} (hN : N ≠ .X')
    {κ : Sp6Kind} (hκF : κ ≠ .field) (hκS : κ ≠ .swap) (h : HR8Kind e t f N κ) :
    ∃ (S : Type) (_ : Group S), Sp6KindType S f κ ∧
      ∃ ρ : neighbourCore e N →* S, Function.Surjective ρ ∧
        ρ.ker ≤ center (neighbourCore e N) :=
  exists_surjective_neighbourCore_of_hr8Kind hw hf e hN hκS h fun _ _ _ hKb hty =>
    isSolvable_outer_of_sp6KindType_graph hKb hκF hκS hty

end LinearNeighbour


section TorusInput


@[expose] def LinearGraphTorusInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f →
    ∀ N : AmalgamNeighbour, N ≠ .X' →
      (HR8Kind e t f N .linear6 → ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ f →
        ∀ Φ : SpecialLinearGroup (Fin 6) F →* G, Φ.range = neighbourCore e N →
          Φ.ker ≤ center (SpecialLinearGroup (Fin 6) F) →
          SLModelOf F (lin6Torus F) (neighbourCore e N) (leviTorusG e {1, 2})
            (leviTorusG e (rankOneTori N).1) (leviTorusG e (rankOneTori N).2)) ∧
      (HR8Kind e t f N .linear7 → ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ f →
        ∀ Φ : SpecialLinearGroup (Fin 7) F →* G, Φ.range = neighbourCore e N →
          Φ.ker ≤ center (SpecialLinearGroup (Fin 7) F) →
          SLModelOf F (lin7Torus F) (neighbourCore e N) (leviTorusG e {1, 2})
            (leviTorusG e (rankOneTori N).1) (leviTorusG e (rankOneTori N).2))

end TorusInput

section Reduction


theorem linearGraphNeighbourInput_of_torusInput (hT : LinearGraphTorusInput) :
    LinearGraphNeighbourInput := by
  intro G _ _ L K _ _ _ e t f hw hf N hN
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨F, _, _, hF, Φ, hΦ, hker⟩ := exists_sl6_cover_neighbourCore hw hf e hN h
    exact ⟨F, inferInstance, inferInstance, hF,
      (hT G L K e t f hw hf N hN).1 h F hF Φ hΦ hker⟩
  · obtain ⟨F, _, _, hF, Φ, hΦ, hker⟩ := exists_sl7_cover_neighbourCore hw hf e hN h
    exact ⟨F, inferInstance, inferInstance, hF,
      (hT G L K e t f hw hf N hN).2 h F hF Φ hΦ hker⟩

theorem graphPieceTablesInput_of_torusInput (hT : LinearGraphTorusInput)
    (hUO : UnitaryOmegaPieceTablesInput) : GraphPieceTablesInput :=
  graphPieceTablesInput_of_inputs (linearGraphNeighbourInput_of_torusInput hT) hUO

end Reduction


theorem rankOneTori_subset_nodes {N : AmalgamNeighbour} (hN : N ≠ .X') :
    (rankOneTori N).1 ⊆ N.nodes ∧ (rankOneTori N).2 ⊆ N.nodes := by
  cases N
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact absurd rfl hN

section TorusSplit


variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem leviTorusG_sup_centralizer_eq [Finite K] [CharP K 2] (e : L ≃* adjointGroup .F4 K)
    {N : AmalgamNeighbour} {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes) :
    leviTorusG e J ⊔ centralizer (neighbourCore e N : Set G) =
      (leviTorusG e J ⊓ neighbourLeviG e N) ⊔ centralizer (neighbourCore e N : Set G) := by
  refine le_antisymm (sup_le ?_ le_sup_right) (sup_le (inf_le_left.trans le_sup_left) le_sup_right)
  intro g hg
  obtain ⟨x, hxT, rfl⟩ := (mem_modelToG e).1 hg
  obtain ⟨b, hb, hbx⟩ := mem_leviTorus.1 hxT
  obtain ⟨d₁, hd₁, d₂, ⟨y, hy, rfl⟩, hd⟩ := exists_eq_mul_of_rootDiagUnit (k := K) N b
  have hd₁C : d₁ ∈ adjointGroup .F4 K := by
    have : d₁ = (x : ModGL .F4 K) * ((y : ModGL .F4 K))⁻¹ := by
      rw [← hbx, hd]
      simp
    rw [this]
    exact mul_mem x.2 (inv_mem y.2)
  set x₁ : adjointGroup .F4 K := ⟨d₁, hd₁C⟩
  have hx : x = x₁ * y := Subtype.ext (by rw [← hbx, hd]; rfl)
  have h₁ : ((e.symm x₁ : L) : G) ∈ centralizer (neighbourCore e N : Set G) := by
    have hX : modelToG e (N.torus K) ≤ centralizer (neighbourCore e N : Set G) :=
      le_centralizer_iff.1 (centralizerPerfectCore_le_centralizer _)
    exact hX (symm_mem_modelToG e hd₁)
  have h₂ : ((e.symm y : L) : G) ∈ leviTorusG e J ⊓ neighbourLeviG e N := by
    refine mem_inf.2 ⟨symm_mem_modelToG e ?_, ⟨e.symm y, ⟨y, hy, rfl⟩, rfl⟩⟩
    have hy' : (y : ModGL .F4 K) = d₁⁻¹ * (x : ModGL .F4 K) := by
      rw [← hbx, hd]
      simp
    rw [hy']
    exact mul_mem (inv_mem (N.torus_le_leviTorus hJ hd₁)) hxT
  rw [hx, map_mul, L.coe_mul]
  exact mul_mem (mem_sup_right h₁) (mem_sup_left h₂)

end TorusSplit

section TorusExact


@[expose] def LinearGraphTorusExactInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f →
    ∀ N : AmalgamNeighbour, N ≠ .X' →
      (HR8Kind e t f N .linear6 → ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ f →
        ∀ Φ : SpecialLinearGroup (Fin 6) F →* G, Φ.range = neighbourCore e N →
          Φ.ker ≤ center (SpecialLinearGroup (Fin 6) F) →
          ∃ Φ' : SpecialLinearGroup (Fin 6) F →* G, Φ'.range = neighbourCore e N ∧
            Φ'.ker ≤ center (SpecialLinearGroup (Fin 6) F) ∧
            (linTorusA (lin6Torus F) ⊤).map Φ' = leviTorusG e {1, 2} ⊓ neighbourLeviG e N ∧
            (linTorusM2 (lin6Torus F) ⊤).map Φ' =
              leviTorusG e (rankOneTori N).1 ⊓ neighbourLeviG e N ∧
            (linTorusM3 (lin6Torus F) ⊤).map Φ' =
              leviTorusG e (rankOneTori N).2 ⊓ neighbourLeviG e N) ∧
      (HR8Kind e t f N .linear7 → ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ f →
        ∀ Φ : SpecialLinearGroup (Fin 7) F →* G, Φ.range = neighbourCore e N →
          Φ.ker ≤ center (SpecialLinearGroup (Fin 7) F) →
          ∃ Φ' : SpecialLinearGroup (Fin 7) F →* G, Φ'.range = neighbourCore e N ∧
            Φ'.ker ≤ center (SpecialLinearGroup (Fin 7) F) ∧
            (linTorusA (lin7Torus F) ⊤).map Φ' = leviTorusG e {1, 2} ⊓ neighbourLeviG e N ∧
            (linTorusM2 (lin7Torus F) ⊤).map Φ' =
              leviTorusG e (rankOneTori N).1 ⊓ neighbourLeviG e N ∧
            (linTorusM3 (lin7Torus F) ⊤).map Φ' =
              leviTorusG e (rankOneTori N).2 ⊓ neighbourLeviG e N)

theorem slModelOf_of_exact {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
    [CharP K 2] (e : L ≃* adjointGroup .F4 K) {N : AmalgamNeighbour} (hN : N ≠ .X') {n : ℕ}
    {F : Type} [Field F] {τ : (Fin 3 → Fˣ) →* SpecialLinearGroup (Fin n) F}
    {Φ : SpecialLinearGroup (Fin n) F →* G} (hE : Φ.range = neighbourCore e N)
    (hker : Φ.ker ≤ center (SpecialLinearGroup (Fin n) F))
    (hA : (linTorusA τ ⊤).map Φ = leviTorusG e {1, 2} ⊓ neighbourLeviG e N)
    (h₂ : (linTorusM2 τ ⊤).map Φ = leviTorusG e (rankOneTori N).1 ⊓ neighbourLeviG e N)
    (h₃ : (linTorusM3 τ ⊤).map Φ = leviTorusG e (rankOneTori N).2 ⊓ neighbourLeviG e N) :
    SLModelOf F τ (neighbourCore e N) (leviTorusG e {1, 2}) (leviTorusG e (rankOneTori N).1)
      (leviTorusG e (rankOneTori N).2) := by
  have h12 : ({1, 2} : Finset (Fin (Tag.rank .F4))) ⊆ N.nodes := by
    cases N
    · decide
    · decide
    · exact absurd rfl hN
  refine ⟨Φ, hE, hker, ?_, ?_, ?_⟩
  · rw [leviTorusG_sup_centralizer_eq e h12, hA]
  · rw [leviTorusG_sup_centralizer_eq e (rankOneTori_subset_nodes hN).1, h₂]
  · rw [leviTorusG_sup_centralizer_eq e (rankOneTori_subset_nodes hN).2, h₃]

theorem linearGraphTorusInput_of_exact (h : LinearGraphTorusExactInput) :
    LinearGraphTorusInput := by
  intro G _ _ L K _ _ _ e t f hw hf N hN
  refine ⟨fun hk F _ _ hF Φ hΦ hker => ?_, fun hk F _ _ hF Φ hΦ hker => ?_⟩
  · obtain ⟨Φ', hE, hker', hA, h₂, h₃⟩ := (h G L K e t f hw hf N hN).1 hk F hF Φ hΦ hker
    exact slModelOf_of_exact e hN hE hker' hA h₂ h₃
  · obtain ⟨Φ', hE, hker', hA, h₂, h₃⟩ := (h G L K e t f hw hf N hN).2 hk F hF Φ hΦ hker
    exact slModelOf_of_exact e hN hE hker' hA h₂ h₃

end TorusExact


section Final


theorem graphPieceTablesInput_of_exactInput (hT : LinearGraphTorusExactInput)
    (hUO : UnitaryOmegaPieceTablesInput) : GraphPieceTablesInput :=
  graphPieceTablesInput_of_torusInput (linearGraphTorusInput_of_exact hT) hUO

end Final

end CFSG.SeitzReduction.F4Pilot
