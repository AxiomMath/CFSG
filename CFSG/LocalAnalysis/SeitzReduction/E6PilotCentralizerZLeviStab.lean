module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZLeviStabUnip
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZLeviStabSL3
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotNonsplit
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYStabBruhat
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZLeviStabBruhat
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZStab

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Chevalley
open CFSG.Quasithin (perfectCore perfectCore_eq_self_of_perfect perfectCore_mono)

local instance e6ZLeviStabNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section General

theorem center_eq_bot_of_isSimpleGroup_of_not_comm {H : Type*} [Group H] (hH : IsSimpleGroup H)
    (hc : ∃ a b : H, a * b ≠ b * a) : center H = ⊥ := by
  rcases hH.eq_bot_or_eq_top_of_normal (center H) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hc
    have ha : a ∈ center H := h ▸ mem_top a
    exact hab ((mem_center_iff.1 ha) b).symm

theorem not_isPGroup_of_isSimpleGroup_of_not_comm {H : Type*} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] (hH : IsSimpleGroup H) (hc : ∃ a b : H, a * b ≠ b * a) : ¬ IsPGroup p H := by
  intro hp
  have : Nontrivial H := hH.toNontrivial
  have hnt := hp.center_nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt (center_eq_bot_of_isSimpleGroup_of_not_comm hH hc)

variable {G : Type*} [Group G]

theorem eq_bot_of_normal_isPGroup_sup [Finite G] {p : ℕ} [Fact p.Prime] {A B : Subgroup G}
    (hAB : A ≤ centralizer (B : Set G)) (hA : IsSimpleGroup A) (hB : IsSimpleGroup B)
    (hAc : ∃ a b : A, a * b ≠ b * a) (hBc : ∃ a b : B, a * b ≠ b * a)
    (N : Subgroup ↥(A ⊔ B)) (hN : N.Normal) (hNp : IsPGroup p N) : N = ⊥ := by
  set N' := N.map (A ⊔ B).subtype with hN'
  have hBA : B ≤ centralizer (A : Set G) := le_centralizer_iff.1 hAB
  have hAM : A ≤ A ⊔ B := le_sup_left
  have hBM : B ≤ A ⊔ B := le_sup_right
  have hconj : ∀ m ∈ A ⊔ B, ∀ x ∈ N', m * x * m⁻¹ ∈ N' := by
    rintro m hm _ ⟨y, hy, rfl⟩
    exact ⟨⟨m, hm⟩ * y * ⟨m, hm⟩⁻¹, hN.conj_mem y hy ⟨m, hm⟩, rfl⟩
  have hN'p : IsPGroup p N' := hNp.map (A ⊔ B).subtype
  have hN'M : N' ≤ A ⊔ B := map_subtype_le N
  have hMA : A ⊔ B ≤ normalizer (A : Set G) :=
    sup_le le_normalizer (hBA.trans (centralizer_le_normalizer _))
  have hMB : A ⊔ B ≤ normalizer (B : Set G) :=
    sup_le (hAB.trans (centralizer_le_normalizer _)) le_normalizer
  have hinter : ∀ {X : Subgroup G}, X ≤ A ⊔ B → A ⊔ B ≤ normalizer (X : Set G) →
      IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) → ∀ x ∈ N', x ∈ X → x = 1 := by
    intro X hXM hMX hX hXc x hxN hxX
    have hnorm : ((N' ⊓ X).subgroupOf X).Normal := by
      refine ⟨fun y hy g => ?_⟩
      rw [mem_subgroupOf] at hy ⊢
      refine mem_inf.2 ⟨hconj g (hXM g.2) y hy.1, ?_⟩
      exact mul_mem (mul_mem g.2 hy.2) (inv_mem g.2)
    rcases hX.eq_bot_or_eq_top_of_normal ((N' ⊓ X).subgroupOf X) with h | h
    · have hm : (⟨x, hxX⟩ : X) ∈ (N' ⊓ X).subgroupOf X := mem_subgroupOf.2 (mem_inf.2 ⟨hxN, hxX⟩)
      rw [h, mem_bot] at hm
      exact congrArg Subtype.val hm
    · exfalso
      have hXN : X ≤ N' := fun y hy => by
        have hm : (⟨y, hy⟩ : X) ∈ (N' ⊓ X).subgroupOf X := h ▸ mem_top _
        exact (mem_inf.1 (mem_subgroupOf.1 hm)).1
      have : Finite X := Subtype.finite
      exact not_isPGroup_of_isSimpleGroup_of_not_comm hX hXc (hN'p.to_le hXN)
  have hNA := hinter hAM hMA hA hAc
  have hNB := hinter hBM hMB hB hBc
  have hcA : ∀ x ∈ N', ∀ a ∈ A, x * a = a * x := by
    intro x hx a ha
    have h1 : x * a * x⁻¹ * a⁻¹ ∈ N' := by
      have : a * x⁻¹ * a⁻¹ ∈ N' := hconj a (hAM ha) _ (inv_mem hx)
      have e : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
      rw [e]
      exact mul_mem hx this
    have h2 : x * a * x⁻¹ * a⁻¹ ∈ A :=
      mul_mem ((mem_normalizer_iff.1 (hMA (hN'M hx)) a).1 ha) (inv_mem ha)
    have h3 := hNA _ h1 h2
    calc x * a = x * a * x⁻¹ * a⁻¹ * (a * x) := by group
      _ = a * x := by rw [h3, one_mul]
  have hN'bot : N' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_bot]
    have hxM : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hN'M hx
    rw [coe_mul_of_right_le_normalizer_left A B (hBA.trans (centralizer_le_normalizer _))]
      at hxM
    obtain ⟨a₀, ha₀, b₀, hb₀, hab⟩ := Set.mem_mul.1 hxM
    have ha₀c : (⟨a₀, ha₀⟩ : A) ∈ center A := by
      rw [mem_center_iff]
      intro a
      apply Subtype.ext
      have h1 := hcA _ hx a a.2
      rw [← hab] at h1
      have h2 : b₀ * a = a * b₀ := (mem_centralizer_iff.1 (hBA hb₀) a a.2).symm
      show (a : G) * a₀ = a₀ * a
      have e : a₀ * b₀ * a = a₀ * a * b₀ := by rw [mul_assoc, h2, ← mul_assoc]
      rw [e] at h1
      have h1' : a₀ * a * b₀ = a * a₀ * b₀ := by rw [h1, mul_assoc]
      exact (mul_right_cancel h1').symm
    rw [center_eq_bot_of_isSimpleGroup_of_not_comm hA hAc, mem_bot] at ha₀c
    have ha₀1 : a₀ = 1 := congrArg Subtype.val ha₀c
    rw [ha₀1, one_mul] at hab
    rw [← hab] at hx ⊢
    exact hNB b₀ hx hb₀
  exact (map_eq_bot_iff_of_injective N (A ⊔ B).subtype_injective).1 hN'bot

theorem commutator_sup_eq_of_perfect {A B : Subgroup G} (hA : ⁅A, A⁆ = A) (hB : ⁅B, B⁆ = B) :
    ⁅A ⊔ B, A ⊔ B⁆ = A ⊔ B := by
  refine le_antisymm (commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_) (sup_le ?_ ?_)
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  · conv_lhs => rw [← hA]
    exact commutator_mono le_sup_left le_sup_left
  · conv_lhs => rw [← hB]
    exact commutator_mono le_sup_right le_sup_right

theorem eq_bot_of_normal_isPGroup_of_mulEquiv {X Y : Type*} [Group X] [Group Y] {p : ℕ}
    (e : X ≃* Y) (h : ∀ N : Subgroup Y, N.Normal → IsPGroup p N → N = ⊥) :
    ∀ N : Subgroup X, N.Normal → IsPGroup p N → N = ⊥ := by
  intro N hN hp
  have h1 := h (N.map e.toMonoidHom) (hN.map _ e.surjective) (hp.map _)
  exact (map_eq_bot_iff_of_injective N e.injective).1 h1

end General

variable {K : Type} [Field K]

theorem zLeviStabilizer [CharP K 2] : ZLeviStabilizer K := by
  intro m hmL hmz
  have hmC : m ∈ adjointGroup .E6 K := parabolicLevi_le_adjointGroup .E6 K zNodes hmL
  obtain ⟨w, hwJ, hwF, h, hh, u, hu, v, hv, hhz, huz, hvz, rfl⟩ :=
    exists_zBruhat_factors hmC (mem_centralizer_singleton_iff.1 hmz)
  set n := canonicalRep (coxeterSystem .E6) K w
  have hnL : n ∈ parabolicLevi .E6 K zNodes := canonicalRep_mem_parabolicLevi hwJ
  have hhL : h ∈ parabolicLevi .E6 K zNodes := torusGroup_le_parabolicLevi zNodes hh
  have hvV : v ∈ parabolicLeviUnipotent .E6 K zNodes :=
    rootSpan_mono (inversionSet_subset_parabolicPosRoots hwJ) hv
  have hvL : v ∈ parabolicLevi .E6 K zNodes :=
    parabolicLeviUnipotent_le_parabolicLevi (K := K) zNodes hvV
  have huL : u ∈ parabolicLevi .E6 K zNodes := by
    have e : u = h⁻¹ * (h * u * n * v) * v⁻¹ * n⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (mul_mem (inv_mem hhL) hmL) (inv_mem hvL)) (inv_mem hnL)
  have hu' := mem_zJ_sup_zS_of_mem_parabolicLeviUnipotent
    (mem_parabolicLeviUnipotent_of_mem_posUnipotent zNodes hu huL) huz
  have hv' := mem_zJ_sup_zS_of_mem_parabolicLeviUnipotent hvV hvz
  have hn' := canonicalRep_mem_zJ_sup_zS (K := K) hwJ hwF
  have hh' := mem_zJ_sup_zS_of_mem_torusGroup hh hhz
  exact mul_mem (mul_mem (mul_mem hh' hu') hn') hv'

theorem levi_inf_centralizer_zAS_eq [CharP K 2] :
    parabolicLevi .E6 K zNodes ⊓ centralizer ({zAS K} : Set (ModGL .E6 K)) = zJ K ⊔ zS K :=
  levi_inf_centralizer_eq_of_stabilizer zLeviStabilizer

theorem zLevi_eq_zJ_sup_zS [CharP K 2] :
    zLevi K = (zJ K ⊔ zS K).subgroupOf (adjointGroup .E6 K) :=
  zLevi_eq_of_stabilizer zLeviStabilizer

theorem zDLevi_eq_conj_zJ_sup_zS [CharP K 2] :
    zDLevi K = ((zJ K ⊔ zS K).subgroupOf (adjointGroup .E6 K)).map
      (MulAut.conj (e6RepConj K 2)).toMonoidHom :=
  zDLevi_eq_of_stabilizer zLeviStabilizer

theorem zJ_le_adjointGroup : zJ K ≤ adjointGroup .E6 K :=
  sup_le (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _)

theorem rootSL2_alpha2_injective [CharP K 2] :
    Function.Injective (rootSL2 .E6 K (Pi.single (1 : Fin Tag.E6.rank) 1)) :=
  (even_Chevalley_pinned_root_SL2_maps .E6 K (isRoot_single .E6 1)).1

theorem range_rootSL2_alpha2 [CharP K 2] :
    (rootSL2 .E6 K (Pi.single (1 : Fin Tag.E6.rank) 1)).range = zJ K :=
  (even_Chevalley_pinned_root_SL2_maps .E6 K (isRoot_single .E6 1)).2.1

variable (K) in
@[expose] noncomputable def zJEquiv [CharP K 2] : SL2 K ≃* ↥(zJ K) :=
  (MonoidHom.ofInjective rootSL2_alpha2_injective).trans
    (MulEquiv.subgroupCongr range_rootSL2_alpha2)

theorem center_zJ_eq_bot [CharP K 2] : center (zJ K) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨B, rfl⟩ := (zJEquiv K).surjective x
  have hB : B ∈ center (SL2 K) := by
    rw [mem_center_iff]
    intro A
    apply (zJEquiv K).injective
    rw [map_mul, map_mul]
    exact mem_center_iff.1 hx _
  rw [eq_one_of_mem_center_SL2 hB, map_one]
  exact one_mem _

theorem zJ_inf_zS_eq_bot [CharP K 2] : zJ K ⊓ zS K = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hgJ, hgS⟩ := mem_inf.1 hg
  have hc : (⟨g, hgJ⟩ : zJ K) ∈ center (zJ K) := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_iff.1 (zS_le_centralizer_zJ hgS) y y.2)
  rw [center_zJ_eq_bot, mem_bot] at hc
  exact congrArg Subtype.val hc

@[expose] noncomputable def zJEquivPSL [CharP K 2] :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* ↥(zJ K) :=
  ((QuotientGroup.quotientMulEquivOfEq (show center (SL2 K) = ⊥ from
      eq_bot_iff.2 fun _ hB => (mem_bot).2 (eq_one_of_mem_center_SL2 hB))).trans
    (QuotientGroup.quotientBot)).trans (zJEquiv K)

theorem lieModel_zJ {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    CFSG.Blueprint.LieModel (zJ K) .PSL 2 2 f := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL (1 + 1) 2 f :=
    ⟨Nat.prime_two, by omega, by norm_num, fun h => by simp at h; omega,
      fun h => by simp at h; omega⟩
  have hmodel :
      CFSG.Blueprint.LieModel (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) .PSL 2 2 f :=
    Or.inl ⟨by decide,
      CFSG.LieType.Universal.SpecialLinear.statedClassicalModel_center_quotient 1 K hadm hK⟩
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (zJEquivPSL (K := K)) hmodel

theorem zJ_le_centralizer_zS : zJ K ≤ centralizer (zS K : Set (ModGL .E6 K)) :=
  le_centralizer_iff.1 zS_le_centralizer_zJ

theorem zJ_simple_perfect [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    IsSimpleGroup (zJ K) ∧ Group.IsPerfect (zJ K) ∧ ∃ x y : zJ K, x * y ≠ y * x :=
  (even_Chevalley_pinned_root_SL2_maps .E6 K (isRoot_single .E6 1)).2.2.2.2.2.2.2.2.2.2.2 ‹_› hq

theorem commutator_zJ_eq [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) : ⁅zJ K, zJ K⁆ = zJ K := by
  rw [← Subgroup.map_subtype_commutator, (zJ_simple_perfect hq).2.1.commutator_eq_top,
    ← MonoidHom.range_eq_map, range_subtype]

theorem zS_not_comm [Finite K] [CharP K 2] : ∃ x y : zS K, x * y ≠ y * x := by
  obtain ⟨-, -, a, b, hab⟩ := isQuasisimple_zS (K := K)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨x, y, fun h => hab (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩

theorem eq_bot_of_normal_isPGroup_zJ_sup_zS [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    ∀ N : Subgroup ↥(zJ K ⊔ zS K), N.Normal → IsPGroup 2 N → N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite (adjointGroup .E6 K) := inferInstance
  set A := (zJ K).subgroupOf (adjointGroup .E6 K)
  set B := (zS K).subgroupOf (adjointGroup .E6 K)
  have hJC := zJ_le_adjointGroup (K := K)
  have hSC := zS_le_adjointGroup (K := K)
  have eA : A ≃* zJ K := subgroupOfEquivOfLe hJC
  have eB : B ≃* zS K := subgroupOfEquivOfLe hSC
  obtain ⟨hJs, -, hJc⟩ := zJ_simple_perfect hq
  have hAs : IsSimpleGroup A := eA.isSimpleGroup
  have hBs : IsSimpleGroup B := by
    have := isSimpleGroup_zS (K := K)
    exact eB.isSimpleGroup
  have hAc : ∃ a b : A, a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hJc
    exact ⟨eA.symm x, eA.symm y, fun h => hxy (by simpa using congrArg eA h)⟩
  have hBc : ∃ a b : B, a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := zS_not_comm (K := K)
    exact ⟨eB.symm x, eB.symm y, fun h => hxy (by simpa using congrArg eB h)⟩
  have hAB : A ≤ centralizer (B : Set (adjointGroup .E6 K)) := by
    intro a ha
    rw [mem_centralizer_iff]
    intro b hb
    exact Subtype.ext (mem_centralizer_iff.1 (zJ_le_centralizer_zS (mem_subgroupOf.1 ha)) b
      (mem_subgroupOf.1 hb))
  have hmain := eq_bot_of_normal_isPGroup_sup (p := 2) hAB hAs hBs hAc hBc
  have hsup : A ⊔ B = (zJ K ⊔ zS K).subgroupOf (adjointGroup .E6 K) :=
    (subgroupOf_sup hJC hSC).symm
  have e : ↥(A ⊔ B) ≃* ↥(zJ K ⊔ zS K) :=
    (MulEquiv.subgroupCongr hsup).trans (subgroupOfEquivOfLe (sup_le hJC hSC))
  exact eq_bot_of_normal_isPGroup_of_mulEquiv e.symm hmain

theorem commutator_zJ_sup_zS_eq [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    ⁅zJ K ⊔ zS K, zJ K ⊔ zS K⁆ = zJ K ⊔ zS K :=
  commutator_sup_eq_of_perfect (commutator_zJ_eq hq) commutator_zS_eq

variable (K) in
@[expose] noncomputable def zDLeviEquiv [CharP K 2] : ↥(zDLevi K) ≃* ↥(zJ K ⊔ zS K) :=
  (((zLevi K).equivMapOfInjective (MulAut.conj (e6RepConj K 2)).toMonoidHom
      (MulAut.conj (e6RepConj K 2)).injective).symm.trans
    (MulEquiv.subgroupCongr zLevi_eq_zJ_sup_zS)).trans
    (subgroupOfEquivOfLe (sup_le zJ_le_adjointGroup zS_le_adjointGroup))

theorem eq_bot_of_normal_isPGroup_zDLevi [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    ∀ N : Subgroup ↥(zDLevi K), N.Normal → IsPGroup 2 N → N = ⊥ :=
  eq_bot_of_normal_isPGroup_of_mulEquiv (zDLeviEquiv K) (eq_bot_of_normal_isPGroup_zJ_sup_zS hq)

theorem commutator_zDLevi_eq [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    ⁅zDLevi K, zDLevi K⁆ = zDLevi K := by
  have hle : zJ K ⊔ zS K ≤ adjointGroup .E6 K := sup_le zJ_le_adjointGroup zS_le_adjointGroup
  have hLevi : ⁅zLevi K, zLevi K⁆ = zLevi K := by
    apply map_injective (adjointGroup .E6 K).subtype_injective
    rw [Subgroup.map_commutator, zLevi_eq_zJ_sup_zS, subgroupOf_map_subtype, inf_of_le_left hle,
      commutator_zJ_sup_zS_eq hq]
  rw [zDLevi, ← Subgroup.map_commutator, hLevi]

theorem perfectCore_zDLevi_eq [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    perfectCore (zDLevi K) = zDLevi K :=
  perfectCore_eq_self_of_perfect (commutator_zDLevi_eq hq)

theorem eq_bot_of_normal_isPGroup_perfectCore_zDLevi [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) :
    ∀ N : Subgroup ↥(perfectCore (zDLevi K)), N.Normal → IsPGroup 2 N → N = ⊥ := by
  rw [perfectCore_zDLevi_eq hq]
  exact eq_bot_of_normal_isPGroup_zDLevi hq

end CFSG.SeitzReduction.E6Pilot
