module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCores
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalQuotient
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRootSL2Aut
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTBlocks

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.EvenSmallLie (StandardSetting)
open scoped commutatorElement

section Groups

variable {X : Type*} [Group X]

theorem eq_top_of_sup_center_eq_top_of_perfect [Group.IsPerfect X] {S : Subgroup X}
    (h : S ⊔ center X = ⊤) : S = ⊤ := by
  rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := X), commutator_def,
    Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (h ▸ Subgroup.mem_top x)
  obtain ⟨b, hb, d, hd, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (h ▸ Subgroup.mem_top y)
  have hc' := mem_center_iff.mp hc
  have hd' := mem_center_iff.mp hd
  have key : ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc a * c * (b * d) * (a * c)⁻¹ * (b * d)⁻¹
        = a * c * b * d * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by group
      _ = a * b * a⁻¹ * b⁻¹ := by
        have e1 : c * b = b * c := (hc' b).symm
        have e2 : d * c⁻¹ = c⁻¹ * d := by
          have := (mem_center_iff.mp (inv_mem hc)) d
          exact this
        have e3 : c * a⁻¹ = a⁻¹ * c := (hc' a⁻¹).symm
        have e4 : d * a⁻¹ = a⁻¹ * d := (hd' a⁻¹).symm
        have e5 : d * d⁻¹ = 1 := mul_inv_cancel d
        calc a * c * b * d * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹
            = a * b * (c * (d * c⁻¹)) * a⁻¹ * d⁻¹ * b⁻¹ := by rw [mul_assoc a c b, e1]; group
          _ = a * b * d * a⁻¹ * d⁻¹ * b⁻¹ := by rw [e2]; group
          _ = a * b * a⁻¹ * (d * d⁻¹) * b⁻¹ := by rw [mul_assoc (a * b) d a⁻¹, e4]; group
          _ = a * b * a⁻¹ * b⁻¹ := by rw [e5, mul_one]
  rw [key, commutatorElement_def]
  exact S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)

end Groups

section Ambient

variable {G : Type*} [Group G]

theorem le_centralizer_of_commutator_le_center {M C J : Subgroup G} (hCM : C ≤ M)
    (hC : ⁅C, C⁆ = C) (hCJ : ⁅C, J⁆ ≤ (center M).map M.subtype) :
    C ≤ centralizer (J : Set G) := by
  have hZC : ⁅(center M).map M.subtype, C⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_centralizer_iff]
    intro c hc
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨c, hCM hc⟩)
  have h1 : ⁅⁅C, J⁆, C⁆ = ⊥ := eq_bot_iff.2 ((commutator_mono hCJ le_rfl).trans hZC.le)
  have h2 : ⁅⁅J, C⁆, C⁆ = ⊥ := by rw [commutator_comm J C]; exact h1
  have h3 := commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hC] at h3
  exact commutator_eq_bot_iff_le_centralizer.1 h3

end Ambient

section Tori

variable {n : ℕ} {K F : Type*} [Field K] [Field F]

theorem map_torusDiagSL_mul_comm (ι : K →+* F) {I : Finset (Fin n)}
    {c : blockTorusParam (K := K) (∅ : Finset (Fin n))} (hc : c.1 ∈ blockTorusParam I)
    {A : Matrix.SpecialLinearGroup (Fin n) F} (hA : A ∈ blockSpecialLinear I) :
    Matrix.SpecialLinearGroup.map ι (torusDiagSL c) * A =
      A * Matrix.SpecialLinearGroup.map ι (torusDiagSL c) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, coe_torusDiagSL,
    Matrix.diagonal_map (map_zero ι)]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hij : i ∈ I ∧ j ∈ I
  · rw [hc.2 i hij.1 j hij.2, mul_comm]
  · rw [(mem_blockSpecialLinear.mp hA) i j (not_and_or.mp hij)]
    by_cases h : i = j
    · subst h
      rw [Matrix.one_apply_eq, mul_one, one_mul]
    · rw [Matrix.one_apply_ne h, mul_zero, zero_mul]

theorem projMap_blockTorus_le_centralizer (ι : K →+* F) (I : Finset (Fin n)) :
    (blockTorus (K := K) I).map (projMap n ι) ≤
      centralizer (blockSL (K := F) I : Set (LinearFlag.projectiveSL n F)) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨c, hc, rfl⟩ := mem_blockTorus.1 hx
  rw [mem_centralizer_iff]
  rintro _ ⟨A, hA, rfl⟩
  rw [projMap_proj, ← map_mul, ← map_mul, map_torusDiagSL_mul_comm ι hc hA]

end Tori

section Generation

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem le_iSup_pieceCore_of_le (hset : StandardSetting G L) (hOut : Group.IsSolvable (Outer L))
    {m : ℕ} (hm : 2 ≤ m) {K F : Type} [Field K] [Finite K] [Field F] [Finite F] [CharP F 2]
    (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) (e : L ≃* LinearFlag.projectiveSL (m + 1) K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {M : Subgroup G}
    [Group.IsPerfect M] (ψ₀ : M ⧸ center M ≃* LinearFlag.projectiveSL (m + 1) F) (hLM : L ≤ M)
    (htM : t ∈ normalizer (M : Set G)) :
    M ≤ ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) := by
  have hn : 3 ≤ m + 1 := by omega
  obtain ⟨ψ, hψL, -⟩ := exists_mulEquiv_globalNormal_center hn ι hσ1 hσσ hfix e ψ₀ hLM
    (by rw [← ht]; exact pow_orderOf_eq_one t) htM
    (perfectCore_inf_centralizer_eq_of_standardSetting hset hOut hn e hLM htC ht)
  set π : M →* LinearFlag.projectiveSL (m + 1) F :=
    ψ.toMonoidHom.comp (QuotientGroup.mk' (center M)) with hπ
  have hπs : Function.Surjective π := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπker : π.ker = center M := by
    ext x
    rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hπL : ∀ x : L, π (inclusion hLM x) = projMap (m + 1) ι (e x) := fun x => hψL x
  have hF4 : 4 ≤ Nat.card F := by
    have : CharP K 2 := ι.charP ι.injective 2
    obtain ⟨f, hf, hK⟩ := exists_natCard_eq_two_pow_of_charP K
    rw [natCard_eq_sq_of_fixedField ι hσ1 hσσ hfix, hK, ← pow_mul]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (f * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  set I : Fin m → Finset (Fin (m + 1)) := fun i => {i.castSucc, i.succ} with hI
  set B : Fin m → Subgroup M := fun i => (blockSL (K := F) (I i)).comap π with hB
  set C : Fin m → Subgroup M := fun i => perfectCore (B i) with hC
  have hCB : ∀ i, C i ≤ B i := fun i => CFSG.Quasithin.perfectCore_le _
  have hCpiece : ∀ i, (C i).map M.subtype ≤ pieceCore e (I i) := by
    intro i
    have hperf : ⁅(C i).map M.subtype, (C i).map M.subtype⁆ = (C i).map M.subtype := by
      rw [← map_commutator, CFSG.Quasithin.perfectCore_perfect]
    refine F4Pilot.le_centralizerPerfectCore hperf
      (le_centralizer_of_commutator_le_center (M := M) (map_subtype_le _) hperf ?_)
    rw [Subgroup.commutator_le]
    rintro _ ⟨c, hc, rfl⟩ y hy
    obtain ⟨x, hx, rfl⟩ := (mem_modelToG e).1 hy
    set j : M := inclusion hLM (e.symm x) with hj
    have hcB : π c ∈ blockSL (K := F) (I i) := hCB i hc
    have hjT : π j ∈ centralizer (blockSL (K := F) (I i) : Set (LinearFlag.projectiveSL (m + 1) F)) := by
      rw [hj, hπL, MulEquiv.apply_symm_apply]
      exact projMap_blockTorus_le_centralizer ι (I i) (mem_map_of_mem _ hx)
    have hcomm : π ⁅c, j⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (mem_centralizer_iff.1 hjT _ hcB)
    have hZ : ⁅c, j⁆ ∈ center M := by
      rw [← hπker]
      exact hcomm
    refine ⟨⁅c, j⁆, hZ, ?_⟩
    rfl
  have hgen : (⨆ i, C i) = ⊤ := by
    refine eq_top_of_sup_center_eq_top_of_perfect ?_
    rw [← hπker, ← Subgroup.comap_map_eq, Subgroup.map_iSup]
    have hi : ∀ i, (C i).map π = blockSL (K := F) (I i) := by
      intro i
      rw [hC, CFSG.Quasithin.map_perfectCore, hB, Subgroup.map_comap_eq_self_of_surjective hπs,
        CFSG.Quasithin.perfectCore_eq_self_of_perfect
          (commutator_blockSL_eq_of_card_two (card_nodePair i) hF4)]
    simp_rw [hi]
    rw [hI, iSup_blockSL_pair_eq_top F m, Subgroup.comap_top]
  intro g hg
  have hmem : (⟨g, hg⟩ : M) ∈ ⨆ i, C i := hgen ▸ mem_top _
  have h2 : g ∈ (⨆ i, C i).map M.subtype := ⟨⟨g, hg⟩, hmem, rfl⟩
  rw [Subgroup.map_iSup] at h2
  exact (iSup_mono hCpiece) h2

theorem eq_of_le_of_card_le (hset : StandardSetting G L) (hOut : Group.IsSolvable (Outer L))
    {m : ℕ} (hm : 2 ≤ m) {K F : Type} [Field K] [Finite K] [Field F] [Finite F] [CharP F 2]
    (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) (e : L ≃* LinearFlag.projectiveSL (m + 1) K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {M G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))))
    [Group.IsPerfect M] (ψ₀ : M ⧸ center M ≃* LinearFlag.projectiveSL (m + 1) F) (hLM : L ≤ M)
    (htM : t ∈ normalizer (M : Set G)) (hcard : Nat.card G₀ ≤ Nat.card M) : M = G₀ :=
  Subgroup.eq_of_le_of_card_ge
    (hG₀ ▸ le_iSup_pieceCore_of_le hset hOut hm ι hσ1 hσσ hfix e htC ht ψ₀ hLM htM) hcard

@[expose] noncomputable def conjugateEquiv (G₀ : Subgroup G) (g : G) :
    G₀ ≃* CFSG.conjugate G₀ g :=
  G₀.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective

@[expose] noncomputable def conjugateQuotientCenterEquiv (G₀ : Subgroup G) (g : G) :
    G₀ ⧸ center G₀ ≃* CFSG.conjugate G₀ g ⧸ center (CFSG.conjugate G₀ g) :=
  QuotientGroup.congr (center G₀) (center (CFSG.conjugate G₀ g)) (conjugateEquiv G₀ g)
    (Subgroup.map_center_eq (conjugateEquiv G₀ g))

theorem conjugate_eq_of_le (hset : StandardSetting G L) (hOut : Group.IsSolvable (Outer L))
    {m : ℕ} (hm : 2 ≤ m) {K F : Type} [Field K] [Finite K] [Field F] [Finite F] [CharP F 2]
    (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) (e : L ≃* LinearFlag.projectiveSL (m + 1) K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))))
    [Group.IsPerfect G₀] (ψ : G₀ ⧸ center G₀ ≃* LinearFlag.projectiveSL (m + 1) F) (g : G)
    (htg : t ∈ normalizer (CFSG.conjugate G₀ g : Set G)) (hLg : L ≤ CFSG.conjugate G₀ g) :
    CFSG.conjugate G₀ g = G₀ := by
  have : Group.IsPerfect (CFSG.conjugate G₀ g) :=
    Group.IsPerfect.ofSurjective (f := (conjugateEquiv G₀ g).toMonoidHom)
      (conjugateEquiv G₀ g).surjective
  exact eq_of_le_of_card_le hset hOut hm ι hσ1 hσσ hfix e htC ht hG₀
    ((conjugateQuotientCenterEquiv G₀ g).symm.trans ψ) hLg htg
    (Nat.card_congr (conjugateEquiv G₀ g).toEquiv).le

end Generation

end CFSG.SeitzReduction.LinearPilot
