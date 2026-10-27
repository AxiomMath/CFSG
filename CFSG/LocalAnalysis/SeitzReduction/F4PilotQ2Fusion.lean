module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2FusionTwoCentral
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OuterTwoExceptional
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotClassRepsCenter

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.LieType.Ree (ReeTag)
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.EvenSmallLie
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

section Transport

theorem map_mem_closure_odd {H G : Type*} [Group H] [Group G] {f : H →* G}
    (hf : Function.Injective f) {w : H}
    (hw : w ∈ closure {c : H | c * w = w * c ∧ Odd (orderOf c)}) :
    f w ∈ closure {c : G | c ∈ f.range ∧ c * f w = f w * c ∧ Odd (orderOf c)} := by
  have h1 : f w ∈ (closure {c : H | c * w = w * c ∧ Odd (orderOf c)}).map f := ⟨w, hw, rfl⟩
  rw [MonoidHom.map_closure] at h1
  refine Subgroup.closure_mono ?_ h1
  rintro _ ⟨c, ⟨hcw, hco⟩, rfl⟩
  refine ⟨MonoidHom.mem_range.2 ⟨c, rfl⟩, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, hcw]
  · rw [orderOf_injective f hf c]
    exact hco

theorem mulAut_mem_closure_odd {H : Type*} [Group H] (α : MulAut H) {w : H}
    (hw : w ∈ closure {c : H | c * w = w * c ∧ Odd (orderOf c)}) :
    α w ∈ closure {c : H | c * α w = α w * c ∧ Odd (orderOf c)} := by
  have h := map_mem_closure_odd (f := α.toMonoidHom) α.injective hw
  refine Subgroup.closure_mono ?_ h
  rintro c ⟨-, hc1, hc2⟩
  exact ⟨hc1, hc2⟩

theorem conj_mem_closure_odd {H : Type*} [Group H] {w : H}
    (hw : w ∈ closure {c : H | c * w = w * c ∧ Odd (orderOf c)}) (g : H) :
    g * w * g⁻¹ ∈ closure {c : H | c * (g * w * g⁻¹) = (g * w * g⁻¹) * c ∧ Odd (orderOf c)} :=
  mulAut_mem_closure_odd (MulAut.conj g) hw

end Transport

section Classes


variable {K : Type} [Field K]

open ClassReps

theorem frameT_mem_closure_odd_two [Finite K] (hK : Nat.card K = 2) :
    frameT K ∈ closure {c : adjointGroup .F4 K | c * frameT K = frameT K * c ∧
      Odd (orderOf c)} :=
  posUnipotent_le_closure_odd_longRoot_two hK (u := frameT K)
    (f4x_mem_posUnipotent ⟨by norm_num, by norm_num⟩ 1)

theorem frameU_mem_closure_odd_two [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    frameU K ∈ closure {c : adjointGroup .F4 K | c * frameU K = frameU K * c ∧
      Odd (orderOf c)} := by
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  have h := mulAut_mem_closure_odd (f4Phi (K := K)) (frameT_mem_closure_odd_two hK)
  have e : (f4Phi (K := K)) (frameT K) = frameU K := (f4Phi_f4x_47_44 (K := K)).1
  rwa [e] at h

theorem frameTU_mem_closure_odd_two [Finite K] (hK : Nat.card K = 2) :
    frameTU K ∈ closure {c : adjointGroup .F4 K | c * frameTU K = frameTU K * c ∧
      Odd (orderOf c)} :=
  parabolicRadical_mid_le_closure_odd hK (u := frameTU K)
    (mul_mem (f4x_mem_parabolicRadical_mid (by decide) 1)
      (f4x_mem_parabolicRadical_mid (by decide) 1))

theorem frameV_mem_closure_odd_two (hK : Nat.card K = 2) :
    frameV K ∈ closure {c : adjointGroup .F4 K | c * frameV K = frameV K * c ∧
      Odd (orderOf c)} := by
  have h41 : f4x K 41 1 ∈ heightSeries .F4 K 3 :=
    pinnedX_mem_rootSpan (S := {α | IsRoot .F4 α ∧ 0 < height α ∧ (3 : ℤ) ≤ height α})
      ⟨(f4_isRoot_pos (i := 41) ⟨by norm_num, by norm_num⟩).1,
        (f4_isRoot_pos (i := 41) ⟨by norm_num, by norm_num⟩).2, by decide +kernel⟩ 1
  have h45 : f4x K 45 1 ∈ heightSeries .F4 K 3 :=
    pinnedX_mem_rootSpan (S := {α | IsRoot .F4 α ∧ 0 < height α ∧ (3 : ℤ) ≤ height α})
      ⟨(f4_isRoot_pos (i := 45) ⟨by norm_num, by norm_num⟩).1,
        (f4_isRoot_pos (i := 45) ⟨by norm_num, by norm_num⟩).2, by decide +kernel⟩ 1
  exact heightSeries_three_le_closure_odd_classV_two hK (u := frameV K) (mul_mem h41 h45)

theorem mem_closure_odd_of_orderOf_eq_two_F4_two [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {y : adjointGroup .F4 K} (hy : orderOf y = 2) :
    y ∈ closure {c : adjointGroup .F4 K | c * y = y * c ∧ Odd (orderOf c)} := by
  obtain ⟨g, hg⟩ := exists_conj_mem_frameReps hy
  have hw : g * y * g⁻¹ ∈ closure {c : adjointGroup .F4 K |
      c * (g * y * g⁻¹) = (g * y * g⁻¹) * c ∧ Odd (orderOf c)} := by
    simp only [frameReps, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with h | h | h | h <;> rw [h]
    · exact frameT_mem_closure_odd_two hK
    · exact frameU_mem_closure_odd_two hK
    · exact frameTU_mem_closure_odd_two hK
    · exact frameV_mem_closure_odd_two hK
  have h := conj_mem_closure_odd hw g⁻¹
  have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
  rwa [e] at h


theorem mem_closure_odd_of_mem_centralizer_sylow_F4_two [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {z : adjointGroup .F4 K} (hz : z ≠ 1) {S : Sylow 2 (adjointGroup .F4 K)}
    (hzS : ∀ u ∈ (S : Subgroup (adjointGroup .F4 K)), u * z = z * u) :
    z ∈ closure {c : adjointGroup .F4 K | c * z = z * c ∧ Odd (orderOf c)} := by
  have hzC : z ∈ centralizer ((S : Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K)) :=
    mem_centralizer_iff.2 hzS
  obtain ⟨κ, c, hc⟩ := factF2 S z hzC hz
  obtain ⟨hT, hU, hTU, -⟩ := weylEltC_conj_frame (K := K)
  set n := weylEltC K weylWordT
  have hy : yRep K κ ∈ closure {x : adjointGroup .F4 K | x * yRep K κ = yRep K κ * x ∧
      Odd (orderOf x)} := by
    cases κ
    · rw [← hT]; exact conj_mem_closure_odd (frameT_mem_closure_odd_two hK) n
    · rw [← hU]; exact conj_mem_closure_odd (frameU_mem_closure_odd_two hK) n
    · rw [← hTU]; exact conj_mem_closure_odd (frameTU_mem_closure_odd_two hK) n
  rw [← hc] at hy
  have h := conj_mem_closure_odd hy c⁻¹
  have e : c⁻¹ * (c * z * c⁻¹) * c⁻¹⁻¹ = z := by group
  rwa [e] at h

theorem mem_closure_odd_of_mulEquiv_F4_two {G : Type*} [Group G] {L : Subgroup G}
    (hK : Nat.card K = 2) (e : L ≃* adjointGroup .F4 K) {w : G} (hwL : w ∈ L)
    (hw : orderOf w = 2) :
    w ∈ closure {c : G | c ∈ L ∧ c * w = w * c ∧ Odd (orderOf c)} := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  set φ : adjointGroup .F4 K →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hwC : orderOf (e ⟨w, hwL⟩) = 2 := by rw [MulEquiv.orderOf_eq, orderOf_mk, hw]
  have h := map_mem_closure_odd hφ (mem_closure_odd_of_orderOf_eq_two_F4_two hK hwC)
  have hφw : φ (e ⟨w, hwL⟩) = w := by simp [hφdef]
  have hφr : φ.range = L := by
    ext g
    constructor
    · rintro ⟨c, rfl⟩
      exact (e.symm c).2
    · intro hg
      exact ⟨e ⟨g, hg⟩, by simp [hφdef]⟩
  rw [hφw, hφr] at h
  exact h

end Classes

section ConjNotMem


variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem not_mem_of_mem_centralizer_of_mulEquiv_F4 [Finite K] (e : L ≃* adjointGroup .F4 K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) : t ∉ L := by
  intro htL
  have htZ : e ⟨t, htL⟩ ∈ center (adjointGroup .F4 K) := by
    rw [mem_center_iff]
    intro c
    obtain ⟨a, rfl⟩ := e.surjective c
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (mem_centralizer_iff.1 htC a a.2))
  rw [center_adjointGroup_eq_bot, mem_bot] at htZ
  have ht1 : t = 1 := by
    have h := congrArg Subtype.val (e.injective (htZ.trans (map_one e).symm))
    exact h
  rw [ht1, orderOf_one] at ht
  exact absurd ht (by decide)

theorem conj_not_mem_of_mulEquiv_F4_two (hK : Nat.card K = 2) (e : L ≃* adjointGroup .F4 K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (g : G) :
    g⁻¹ * t * g ∉ L := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  exact SeitzQ2.conj_not_mem_of_forall_mem_closure_odd
    (SeitzQ2.isPGroup_outer_of_mulEquiv_F4_two hK e) htC ht
    (not_mem_of_mem_centralizer_of_mulEquiv_F4 e htC ht) hCN hKt
    (fun _ hw h2 => mem_closure_odd_of_mulEquiv_F4_two hK e hw h2) g

theorem conj_not_mem_F4_two [Finite G] (hset : StandardSetting G L) (hK : Nat.card K = 2)
    (e : L ≃* adjointGroup .F4 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (g : G) :
    g⁻¹ * t * g ∉ L := by
  have htC : t ∈ centralizer (L : Set G) :=
    (show t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) from hKt ▸ mem_zpowers t).1
  exact conj_not_mem_of_mulEquiv_F4_two hK e htC ht
    (centralizer_le_normalizer_of_standard hset.standard htC ht) hKt g

theorem not_forall_commute_sylow_F4_two (hK : Nat.card K = 2) (e : L ≃* adjointGroup .F4 K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u :=
  fun _ g hg => absurd hg (conj_not_mem_of_mulEquiv_F4_two hK e htC ht hCN hKt g)

end ConjNotMem

section AutU

theorem mem_range_conj_of_fix_sylow_of_fix {C : Type*} [Group C] [Finite C] {p : ℕ}
    [Fact p.Prime] (U₀ : Sylow p C)
    (h₀ : ∀ β : MulAut C, (∀ u ∈ (U₀ : Subgroup C), β u = u) →
      β ∈ (MulAut.conj : C →* MulAut C).range)
    (U : Sylow p C) (β : MulAut C) (hβ : ∀ u ∈ (U : Subgroup C), β u = u) :
    β ∈ (MulAut.conj : C →* MulAut C).range := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C U₀ U
  have hU : (U : Subgroup C) = (U₀ : Subgroup C).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  obtain ⟨x, hx⟩ := h₀ ((MulAut.conj g)⁻¹ * β * MulAut.conj g) fun u hu => by
    have hgu : g * u * g⁻¹ ∈ (U : Subgroup C) := by
      rw [hU]
      exact ⟨u, hu, rfl⟩
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, hβ _ hgu, MulAut.inv_apply,
      MulAut.conj_symm_apply]
    group
  refine ⟨g * x * g⁻¹, ?_⟩
  rw [map_mul, map_mul, hx, map_inv]
  group

theorem mem_range_conj_of_fix_sylow_of_mulEquiv_of_forall {X C : Type*} [Group X] [Group C]
    [Finite C] {p : ℕ} [Fact p.Prime]
    (hC : ∀ (U : Sylow p C) (β : MulAut C), (∀ u ∈ (U : Subgroup C), β u = u) →
      β ∈ (MulAut.conj : C →* MulAut C).range)
    (e : X ≃* C) (U : Sylow p X) (β : MulAut X) (hβ : ∀ u ∈ (U : Subgroup X), β u = u) :
    β ∈ (MulAut.conj : X →* MulAut X).range := by
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  set U' : Sylow p C := U.mapSurjective (f := e.toMonoidHom) e.surjective with hU'
  have hmem : ∀ x : X, x ∈ (U : Subgroup X) ↔ e x ∈ (U' : Subgroup C) := by
    intro x
    change x ∈ (U : Subgroup X) ↔ e x ∈ (U : Subgroup X).map e.toMonoidHom
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  obtain ⟨y, hy⟩ := hC U' (MulAut.congr e β) fun u hu => by
    obtain ⟨x, rfl⟩ := e.surjective u
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hβ x ((hmem x).2 hu)]
  refine ⟨e.symm y, ?_⟩
  apply (MulAut.congr e).injective
  rw [← hy]
  ext c
  simp [MulAut.congr_apply, MulAut.conj_apply]


variable {K : Type} [Field K]

theorem mem_range_conj_of_mem_diagonalFieldActors_two {τ : Tag} (hK : Nat.card K = 2)
    {β : MulAut (adjointGroup τ K)} (hβ : β ∈ diagonalFieldActors τ K) :
    β ∈ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range := by
  obtain ⟨g, hg, a, δ, hφ⟩ := ((Chevalley_diagonal_field_actor_data.1 τ K).1 β).1 hβ
  have ha : a = 1 := funext fun i => SeitzQ2.units_eq_one_of_natCard_eq_two hK (a i)
  have hδ : δ = 1 := SeitzQ2.ringEquiv_eq_refl_of_card_eq_two hK δ
  subst ha hδ
  refine ⟨⟨g, hg⟩, ?_⟩
  ext x
  rw [hφ x, rootDiagUnit_one, units_map_entrywiseHom_one_ringEquiv, MulAut.conj_apply]
  simp

theorem mem_range_conj_of_fix_posUnipotent_F4_two
    (hK : Nat.card K = 2) (β : MulAut (adjointGroup .F4 K))
    (hβ : ∀ u : adjointGroup .F4 K, (u : ModGL .F4 K) ∈ posUnipotent .F4 K → β u = u) :
    β ∈ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  exact mem_range_conj_of_mem_diagonalFieldActors_two hK
    (mem_diagonalFieldActors_of_forall_posUnipotent (f := 1) le_rfl (by rw [pow_one]; exact hK)
      β hβ)

theorem mem_range_conj_of_fix_sylow_F4_two (hK : Nat.card K = 2)
    (U : Sylow 2 (adjointGroup .F4 K)) (β : MulAut (adjointGroup .F4 K))
    (hβ : ∀ u ∈ (U : Subgroup (adjointGroup .F4 K)), β u = u) :
    β ∈ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  have : Finite (adjointGroup .F4 K) := by
    have : Finite (ModGL .F4 K) := finite_modGL
    infer_instance
  refine mem_range_conj_of_fix_sylow_of_fix (ClassReps.posUnipotentSylow (K := K))
    (fun β' hβ' => mem_range_conj_of_fix_posUnipotent_F4_two hK β' fun u hu =>
      hβ' u (ClassReps.mem_posUnipotentSylow.2 hu)) U β hβ

theorem mem_range_conj_of_fix_sylow_of_mulEquiv_F4_two
    {X : Type*} [Group X] (hK : Nat.card K = 2) (e : X ≃* adjointGroup .F4 K) (U : Sylow 2 X)
    (β : MulAut X) (hβ : ∀ u ∈ (U : Subgroup X), β u = u) :
    β ∈ (MulAut.conj : X →* MulAut X).range := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Finite (adjointGroup .F4 K) := by
    have : Finite (ModGL .F4 K) := finite_modGL
    infer_instance
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact mem_range_conj_of_fix_sylow_of_mulEquiv_of_forall (mem_range_conj_of_fix_sylow_F4_two hK) e
    U β hβ

theorem mem_range_conj_of_fix_posUnipotent_F4 {f : ℕ} (hf : 1 ≤ f)
    [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) (β : MulAut (adjointGroup .F4 K))
    (hβ : ∀ u : adjointGroup .F4 K, (u : ModGL .F4 K) ∈ posUnipotent .F4 K → β u = u) :
    β ∈ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range := by
  obtain ⟨g, hg, a, δ, hφ⟩ := ((Chevalley_diagonal_field_actor_data.1 .F4 K).1 β).1
    (mem_diagonalFieldActors_of_forall_posUnipotent hf hK β hβ)
  obtain ⟨⟨B, hB, -⟩, hrest⟩ := G2_F4_root_character_diagonals_inner .F4 (Or.inr rfl) K
  obtain ⟨haC, -⟩ := (hrest B hB a).2.2
  set h : adjointGroup .F4 K := ⟨g, hg⟩ * ⟨rootDiagUnit .F4 a, haC⟩ with hhdef
  have hβh : ∀ x : adjointGroup .F4 K, (β x : ModGL .F4 K) =
      (h : ModGL .F4 K) * Units.map (entrywiseHom δ.toRingHom) x * (h : ModGL .F4 K)⁻¹ := by
    intro x
    rw [hφ x, hhdef, Subgroup.coe_mul]
    group
  have hδU := ((chevalley_root_character_and_field_conjugation .F4 K).2.2.2.2.1 δ).2.1
  have hconj : ∀ v : adjointGroup .F4 K, (v : ModGL .F4 K) ∈ posUnipotent .F4 K →
      ((h⁻¹ * v * h : adjointGroup .F4 K) : ModGL .F4 K) ∈ posUnipotent .F4 K := by
    intro v hv
    have e1 := hβh v
    rw [hβ v hv] at e1
    have e2 : ((h⁻¹ * v * h : adjointGroup .F4 K) : ModGL .F4 K) =
        Units.map (entrywiseHom δ.toRingHom) (v : ModGL .F4 K) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (h : ModGL .F4 K)⁻¹ * v * h = (h : ModGL .F4 K)⁻¹ *
            ((h : ModGL .F4 K) * Units.map (entrywiseHom δ.toRingHom) (v : ModGL .F4 K) *
              (h : ModGL .F4 K)⁻¹) * h := by rw [← e1]
        _ = Units.map (entrywiseHom δ.toRingHom) (v : ModGL .F4 K) := by group
    rw [e2, ← hδU]
    exact ⟨_, hv, rfl⟩
  have hBn := borel_self_normalizers .F4 K
  have hBN : borelGroup .F4 K ≤ Subgroup.normalizer (posUnipotent .F4 K : Set (ModGL .F4 K)) :=
    fun b hb => (Subgroup.mem_inf.1 (hBn.1.symm ▸ hb : b ∈ _)).2
  have hUB : posUnipotent .F4 K ≤ borelGroup .F4 K := le_sup_right
  have hBC : borelGroup .F4 K ≤ adjointGroup .F4 K :=
    ((triangular_borel_structure.{0, 0} .F4 K).2.2.2.2.2.2.2.2.2.2.2 K).1
  have hhB : ((h⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) ∈ borelGroup .F4 K := by
    refine mem_borelGroup_of_conj_posUnipotent_le (h⁻¹).2 fun b hb b' hb' w hw u hu => ?_
    have hn : canonicalRep (coxeterSystem .F4) K w =
        b⁻¹ * ((h⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) * b'⁻¹ := by
      rw [← hw]; group
    have hv : b'⁻¹ * u * b' ∈ posUnipotent .F4 K := by
      have := (Subgroup.mem_normalizer_iff.1 (hBN (inv_mem hb')) u).1 hu
      simpa using this
    have hw' := hconj ⟨b'⁻¹ * u * b', hBC (hUB hv)⟩ hv
    have hx := (Subgroup.mem_normalizer_iff.1 (hBN (inv_mem hb)) _).1 hw'
    rw [hn]
    refine hUB ?_
    convert hx using 1
  have hhB' : (h : ModGL .F4 K) ∈ borelGroup .F4 K := by simpa using inv_mem hhB
  have hHU := (triangular_borel_structure.{0, 0} .F4 K).2.2.2.2.1
  have hhHU : (h : ModGL .F4 K) ∈ (borelGroup .F4 K : Set (ModGL .F4 K)) := hhB'
  rw [hHU] at hhHU
  obtain ⟨d, hd, u₀, hu₀, hdu⟩ := Set.mem_mul.1 hhHU
  have hr := (f4_isRoot_pos (i := 47) ⟨by norm_num, by norm_num⟩).1
  have hkey : ∀ c : K, torusRootChar d (orbitCertRoot .F4 47) * δ c = c := by
    intro c
    have e1 := hβh ⟨f4x K 47 c, pinnedX_mem_adjointGroup _ _⟩
    rw [hβ ⟨f4x K 47 c, pinnedX_mem_adjointGroup _ _⟩
      (f4x_mem_posUnipotent ⟨by norm_num, by norm_num⟩ c)] at e1
    have e3 : Units.map (entrywiseHom δ.toRingHom) (f4x K 47 c) = f4x K 47 (δ c) :=
      Units.ext (entrywise_pinnedX δ.toRingHom _ c)
    change f4x K 47 c = (h : ModGL .F4 K) * Units.map (entrywiseHom δ.toRingHom) (f4x K 47 c) *
      (h : ModGL .F4 K)⁻¹ at e1
    rw [e3, ← hdu] at e1
    have hcomm : u₀ * f4x K 47 (δ c) = f4x K 47 (δ c) * u₀ := f4x_central (Or.inr rfl) _ hu₀
    have e4 : d * u₀ * f4x K 47 (δ c) * (d * u₀)⁻¹ = d * f4x K 47 (δ c) * d⁻¹ := by
      rw [mul_assoc d, hcomm]; group
    rw [e4] at e1
    simp only [f4x] at e1
    rw [conj_pinnedX_of_mem_torusGroup hd hr] at e1
    exact pinnedX_injective _ _ _ e1.symm
  have hχ : torusRootChar d (orbitCertRoot .F4 47) = 1 := by
    have := hkey 1
    rwa [map_one, mul_one] at this
  have hδ : δ = 1 := RingEquiv.ext fun c => by
    have := hkey c
    rwa [hχ, one_mul] at this
  subst hδ
  refine ⟨h, ?_⟩
  ext x
  rw [hβh x, units_map_entrywiseHom_one_ringEquiv, MulAut.conj_apply]
  simp

theorem mem_range_conj_of_fix_sylow_F4 {f : ℕ} (hf : 1 ≤ f)
    [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) (U : Sylow 2 (adjointGroup .F4 K))
    (β : MulAut (adjointGroup .F4 K)) (hβ : ∀ u ∈ (U : Subgroup (adjointGroup .F4 K)), β u = u) :
    β ∈ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (adjointGroup .F4 K) := by
    have : Finite (ModGL .F4 K) := finite_modGL
    infer_instance
  exact mem_range_conj_of_fix_sylow_of_fix (ClassReps.posUnipotentSylow (K := K))
    (fun β' hβ' => mem_range_conj_of_fix_posUnipotent_F4 hf hK β' fun u hu =>
      hβ' u (ClassReps.mem_posUnipotentSylow.2 hu)) U β hβ

theorem mem_range_conj_of_fix_sylow_of_mulEquiv_F4 {X : Type*}
    [Group X] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (e : X ≃* adjointGroup .F4 K)
    (U : Sylow 2 X) (β : MulAut X) (hβ : ∀ u ∈ (U : Subgroup X), β u = u) :
    β ∈ (MulAut.conj : X →* MulAut X).range := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have : Finite (adjointGroup .F4 K) := by
    have : Finite (ModGL .F4 K) := finite_modGL
    infer_instance
  exact mem_range_conj_of_fix_sylow_of_mulEquiv_of_forall (mem_range_conj_of_fix_sylow_F4 hf hK) e
    U β hβ

end AutU

section Fusion


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_conj_eq_mul_twoCentral_twoSided_F4_two (hset : StandardSetting G L)
    (hK : Nat.card K = 2) (e : L ≃* adjointGroup .F4 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧ z ≠ 1 ∧
      (∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u) ∧
      (∃ U' : Sylow 2 (CFSG.conjugate L x),
        ∀ u ∈ (U' : Subgroup (CFSG.conjugate L x)), (u : G) * z = z * u) ∧
      ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹ := by
  have htC : t ∈ centralizer (L : Set G) :=
    (show t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) from hKt ▸ mem_zpowers t).1
  have hCN := centralizer_le_normalizer_of_standard hset.standard htC ht
  exact SeitzQ2.exists_conj_eq_mul_twoCentral_twoSided hset
    (SeitzQ2.card_outer_le_two_of_mulEquiv_F4_two hK e).2 ht hKt
    (not_forall_commute_sylow_F4_two hK e htC ht hCN hKt)
    (mem_range_conj_of_fix_sylow_of_mulEquiv_F4_two hK e)

theorem exists_conj_eq_mul_yRep_F4_two (hset : StandardSetting G L) (hK : Nat.card K = 2)
    (e : L ≃* adjointGroup .F4 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∃ (g : G) (κ : TwoCentral), g⁻¹ * t * g = t * (e.symm (yRep K κ) : G) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  have htC : t ∈ centralizer (L : Set G) :=
    (show t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) from hKt ▸ mem_zpowers t).1
  obtain ⟨x, z, ⟨hzL, -⟩, hxt, hz1, ⟨U, hU⟩, -, -⟩ :=
    exists_conj_eq_mul_twoCentral_twoSided_F4_two hset hK e ht hKt
  have hzCU : e ⟨z, hzL⟩ ∈ centralizer (((U.mapSurjective (f := e.toMonoidHom) e.surjective :
      Sylow 2 (adjointGroup .F4 K)) : Subgroup (adjointGroup .F4 K)) :
        Set (adjointGroup .F4 K)) := by
    rw [mem_centralizer_iff]
    intro u hu
    change u ∈ (U : Subgroup L).map e.toMonoidHom at hu
    obtain ⟨v, hv, rfl⟩ := hu
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (hU v hv))
  have hzC1 : e ⟨z, hzL⟩ ≠ 1 := by
    intro h
    apply hz1
    have h' : (⟨z, hzL⟩ : L) = 1 := e.injective (h.trans (map_one e).symm)
    exact congrArg Subtype.val h'
  obtain ⟨κ, c, hc⟩ := factF2 _ _ hzCU hzC1
  have htl : (e.symm c : G) * t = t * (e.symm c : G) :=
    mem_centralizer_iff.1 htC _ (e.symm c).2
  have hy : (e.symm (yRep K κ) : G) = (e.symm c : G) * z * (e.symm c : G)⁻¹ := by
    rw [← hc, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  refine ⟨x * (e.symm c : G)⁻¹, κ, ?_⟩
  calc (x * (e.symm c : G)⁻¹)⁻¹ * t * (x * (e.symm c : G)⁻¹) =
        (e.symm c : G) * (x⁻¹ * t * x) * (e.symm c : G)⁻¹ := by group
    _ = (e.symm c : G) * t * z * (e.symm c : G)⁻¹ := by rw [hxt, mul_assoc (e.symm c : G) t z]
    _ = t * ((e.symm c : G) * z * (e.symm c : G)⁻¹) := by rw [htl]; group
    _ = t * (e.symm (yRep K κ) : G) := by rw [hy]

end Fusion

end CFSG.SeitzReduction.F4Pilot
