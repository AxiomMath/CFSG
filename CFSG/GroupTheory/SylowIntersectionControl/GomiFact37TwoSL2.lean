module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2
public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact37Common
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOffender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSaturate
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorBinary
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorSection1
public import CFSG.Quasithin.Background.G64NatSec
public import CFSG.Quasithin.EmptyFaithful.S146zXGIdent
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpSL
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeGLTwoQs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesCentralQuotient

public section

namespace CFSG.GroupTheory

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Lift CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique
open scoped MatrixGroups LinearAlgebra.Projectivization
open Projectivization

section Linear

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

private theorem isIrreducible_of_forall_invariant {G k M : Type*} [Monoid G] [Field k]
    [AddCommGroup M] [Module k M] (ρ : Representation k G M) (hv : Nontrivial M)
    (h : ∀ U : Submodule k M, (∀ g, ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = ⊤) :
    ρ.IsIrreducible := by
  have hnt : Nontrivial (Subrepresentation ρ) := by
    refine ⟨⊥, ⊤, fun h' => ?_⟩
    obtain ⟨x, y, hxy⟩ := hv
    have h1 : (⊥ : Subrepresentation ρ).toSubmodule = (⊤ : Subrepresentation ρ).toSubmodule :=
      congrArg Subrepresentation.toSubmodule h'
    have h2 : (⊥ : Submodule k M) = ⊤ := h1
    have h3 : x - y ∈ (⊥ : Submodule k M) := h2 ▸ Submodule.mem_top
    exact hxy (sub_eq_zero.mp ((Submodule.mem_bot k).mp h3))
  refine ⟨fun Z => ?_⟩
  rcases h Z.toSubmodule (fun g u hu => Z.apply_mem_toSubmodule g hu) with h1 | h1
  · exact Or.inl (Subrepresentation.toSubmodule_injective h1)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h1)

private theorem forall_mem_toUnits_iff {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (A₀ : Subgroup (W ≃ₗ[ZMod 2] W)) (w : W) :
    (∀ a ∈ toUnits A₀, a.val w = w) ↔ ∀ b ∈ A₀, b w = w := by
  constructor
  · intro h b hb
    have hmem : (unitsEquiv (ZMod 2) W).symm b ∈ toUnits A₀ := by
      show unitsEquiv (ZMod 2) W ((unitsEquiv (ZMod 2) W).symm b) ∈ A₀
      rw [MulEquiv.apply_symm_apply]
      exact hb
    have := h _ hmem
    rwa [← unitsEquiv_apply, MulEquiv.apply_symm_apply] at this
  · intro h a ha
    exact h _ ha

private theorem isIrreducible_repOfSubgroup_toUnits {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] {B : Subgroup (W ≃ₗ[ZMod 2] W)} (hnt : Nontrivial W)
    (hinv : ∀ U : Submodule (ZMod 2) W, (∀ x ∈ B, ∀ u ∈ U, x u ∈ U) → U = ⊥ ∨ U = ⊤) :
    (repOfSubgroup (toUnits B)).IsIrreducible := by
  refine isIrreducible_of_forall_invariant _ hnt fun U hU => hinv U fun x hx u hu => ?_
  have hmem : (unitsEquiv (ZMod 2) W).symm x ∈ toUnits B := by
    show unitsEquiv (ZMod 2) W ((unitsEquiv (ZMod 2) W).symm x) ∈ B
    rw [MulEquiv.apply_symm_apply]
    exact hx
  have := hU ⟨_, hmem⟩ u hu
  rwa [repOfSubgroup_apply, ← unitsEquiv_apply, MulEquiv.apply_symm_apply] at this

private theorem toUnits_ne_bot {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {B : Subgroup (W ≃ₗ[ZMod 2] W)} (hB : B ≠ ⊥) : toUnits B ≠ ⊥ := by
  intro h
  apply hB
  rw [← Subgroup.card_eq_one, ← natCard_toUnits, h]
  exact Subgroup.card_bot

private theorem natCard_toUnits_mul_fix {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (B : Subgroup (W ≃ₗ[ZMod 2] W)) :
    Nat.card ↥(toUnits B) * Nat.card {w : W // ∀ a ∈ toUnits B, a.val w = w} =
      weight (MonoidHom.id (W ≃ₗ[ZMod 2] W)) B := by
  unfold CFSG.QuasithinUnique.Setup.Offender.weight
  rw [natCard_toUnits]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight fun w => forall_mem_toUnits_iff B w)

private theorem weight_le_of_le_minimal {A : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hoff : Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A)
    (hstrict : ∀ B : Subgroup (V ≃ₗ[ZMod 2] V), ⊥ < B → B < A →
      weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) B < weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A)
    (B : Subgroup (V ≃ₗ[ZMod 2] V)) (hB : B ≤ A) :
    weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) B ≤ weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A := by
  rcases hB.lt_or_eq with hlt | heq
  · by_cases hbot : B = ⊥
    · rw [hbot, weight_bot]
      exact hoff
    · exact (hstrict B (bot_lt_iff_ne_bot.2 hbot) hlt).le
  · rw [heq]

private theorem isSimpleGroup_of_mulEquiv_sl2 {H : Type*} [Group H] {n : ℕ} (hn : 2 ≤ n)
    {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ n) (e : H ≃* SL(2, F)) :
    IsSimpleGroup H := by
  have : CharP F 2 := charP_two_of_card_eq hF
  have h4 : 4 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have := CFSG.LocalAnalysis.RankThreeUC.S15.K421SpSLProof.isSimpleGroup_sl2_charTwo h4
  exact MulEquiv.isSimpleGroup e

section Coords

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {Z : Submodule (ZMod 2) M}
variable {Ω : Type*} [Fintype Ω] (ε : Ω ≃ Fin 5) (βd : (M ⧸ Z) ≃ₗ[ZMod 2] ↥(evenWeight Ω))

private def evenWeightCoords : M →+ (Fin 5 → ZMod 2) where
  toFun u i := (βd (Submodule.Quotient.mk u) : Ω → ZMod 2) (ε.symm i)
  map_zero' := by
    funext i
    simp
  map_add' u u' := by
    funext i
    simp

private theorem evenWeightCoords_apply (u : M) (i : Fin 5) :
    evenWeightCoords ε βd u i = (βd (Submodule.Quotient.mk u) : Ω → ZMod 2) (ε.symm i) := rfl

private theorem mem_range_evenWeightCoords (x : Fin 5 → ZMod 2) :
    x ∈ Set.range (evenWeightCoords ε βd) ↔ ∑ i, x i = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h : ∑ p, (βd (Submodule.Quotient.mk u) : Ω → ZMod 2) p = 0 :=
      (βd (Submodule.Quotient.mk u)).2
    rw [← Equiv.sum_comp ε.symm] at h
    simpa [evenWeightCoords_apply] using h
  · intro hx
    have hy : (fun p => x (ε p)) ∈ evenWeight Ω := by
      show ∑ p, x (ε p) = 0
      rw [Equiv.sum_comp ε]
      exact hx
    obtain ⟨u, hu⟩ := Submodule.mkQ_surjective Z (βd.symm ⟨_, hy⟩)
    refine ⟨u, funext fun i => ?_⟩
    have h1 : Submodule.Quotient.mk u = βd.symm ⟨_, hy⟩ := hu
    rw [evenWeightCoords_apply, h1, LinearEquiv.apply_symm_apply]
    simp

private theorem evenWeightCoords_eq_zero_iff (u : M) : evenWeightCoords ε βd u = 0 ↔ u ∈ Z := by
  constructor
  · intro hu
    have h1 : βd (Submodule.Quotient.mk u) = 0 := by
      apply Subtype.ext
      funext p
      have := congrFun hu (ε p)
      rw [evenWeightCoords_apply, Equiv.symm_apply_apply] at this
      simpa using this
    rwa [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero] at h1
  · intro hu
    have h1 : (Submodule.Quotient.mk u : M ⧸ Z) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hu
    funext i
    rw [evenWeightCoords_apply, h1, map_zero]
    rfl

private theorem evenWeightCoords_permAct (σ : Equiv.Perm Ω) (u u' : M)
    (h : (βd (Submodule.Quotient.mk u') : Ω → ZMod 2) =
      permAct σ (βd (Submodule.Quotient.mk u) : Ω → ZMod 2)) :
    evenWeightCoords ε βd u' = fun i => evenWeightCoords ε βd u ((ε.permCongr σ).symm i) := by
  funext i
  show (βd (Submodule.Quotient.mk u') : Ω → ZMod 2) (ε.symm i) =
    (βd (Submodule.Quotient.mk u) : Ω → ZMod 2) (ε.symm ((ε.permCongr σ).symm i))
  rw [h, Equiv.permCongr_def]
  simp [permAct]

end Coords

section ComponentSection

variable {L A : Subgroup (V ≃ₗ[ZMod 2] V)} {I : Submodule (ZMod 2) V}
variable (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V)))
variable (hI : CFSG.QuasithinUnique.Setup.Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V))
  (L ⊔ A) I)

private theorem actOn_L_injective [IsSimpleGroup ↥L]
    (hne : (actOn L A I hAn hI L le_sup_left).range ≠ ⊥) :
    Function.Injective (actOn L A I hAn hI L le_sup_left) := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (actOn L A I hAn hI L le_sup_left).ker
    with h | h
  · exact (MonoidHom.ker_eq_bot_iff _).mp h
  · exfalso
    apply hne
    rw [MonoidHom.range_eq_bot_iff]
    apply MonoidHom.ext
    intro l
    exact MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top l)

private noncomputable def lbarUnitsHom : ↥L →* ↥(toUnits (Lbar L A I hAn hI)) :=
  (toUnitsEquiv (Lbar L A I hAn hI)).symm.toMonoidHom.comp
    (actOn L A I hAn hI L le_sup_left).rangeRestrict

private theorem lbarUnitsHom_val_mk (l : ↥L) (u : ↥I) (h : (l : V ≃ₗ[ZMod 2] V) u ∈ I) :
    (lbarUnitsHom hAn hI l).1.val (Submodule.Quotient.mk u) =
      (Submodule.Quotient.mk ⟨_, h⟩ : ↥I ⧸ fixIn L I) := by
  show ((toUnitsEquiv (Lbar L A I hAn hI)).symm ⟨actOn L A I hAn hI L le_sup_left l, l, rfl⟩).1.val
    (Submodule.Quotient.mk u) = _
  rw [toUnitsEquiv_symm_val]
  show actOn L A I hAn hI L le_sup_left l (Submodule.Quotient.mk u) = _
  rw [actOn_L_mk]
  congr 1

private theorem lbarUnitsHom_surjective : Function.Surjective (lbarUnitsHom hAn hI) :=
  (toUnitsEquiv (Lbar L A I hAn hI)).symm.surjective.comp
    (actOn L A I hAn hI L le_sup_left).rangeRestrict_surjective

private theorem lbarUnitsHom_injective
    (hRinj : Function.Injective (actOn L A I hAn hI L le_sup_left)) :
    Function.Injective (lbarUnitsHom hAn hI) := by
  intro l l' h
  apply hRinj
  have h1 : (actOn L A I hAn hI L le_sup_left).rangeRestrict l =
      (actOn L A I hAn hI L le_sup_left).rangeRestrict l' :=
    (toUnitsEquiv (Lbar L A I hAn hI)).symm.injective h
  exact congrArg Subtype.val h1

private noncomputable def lbarUnitsEquiv {G' : Type*} [Group G']
    (hRinj : Function.Injective (actOn L A I hAn hI L le_sup_left)) (e : ↥L ≃* G') :
    ↥(toUnits (Lbar L A I hAn hI)) ≃* G' :=
  (MulEquiv.ofBijective (lbarUnitsHom hAn hI)
    ⟨lbarUnitsHom_injective hAn hI hRinj, lbarUnitsHom_surjective hAn hI⟩).symm.trans e

private theorem lbarUnitsEquiv_lbarUnitsHom {G' : Type*} [Group G']
    (hRinj : Function.Injective (actOn L A I hAn hI L le_sup_left)) (e : ↥L ≃* G') (l : ↥L) :
    lbarUnitsEquiv hAn hI hRinj e (lbarUnitsHom hAn hI l) = e l :=
  congrArg e ((MulEquiv.ofBijective (lbarUnitsHom hAn hI)
    ⟨lbarUnitsHom_injective hAn hI hRinj, lbarUnitsHom_surjective hAn hI⟩).symm_apply_apply l)

private theorem commGL_top_eq_of_section [Finite V] (hsec : ComponentSection L A I)
    (hoff : Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A)
    (hstrict : ∀ B : Subgroup (V ≃ₗ[ZMod 2] V), ⊥ < B → B < A →
      weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) B < weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A)
    (hw : weight (MonoidHom.id ((↥I ⧸ fixIn L I) ≃ₗ[ZMod 2] (↥I ⧸ fixIn L I)))
      (Abar L A I hAn hI) = Nat.card (↥I ⧸ fixIn L I)) :
    commGL L ⊤ = I := by
  have hinj : ∀ a : ↥A, actOn L A I hAn hI A le_sup_right a = 1 →
      resSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A I hsec.inv_A a = 1 := by
    intro a ha
    have h1 := hsec.inj ⟨a, Subgroup.mem_sup_right a.2⟩ ha
    rw [← resSub_sup_A hsec.inv_L hsec.inv_A a]
    exact h1
  exact (irreducible_section_weight_equality_saturates hsec.A_norm hsec.L_perf
    (weight_le_of_le_minimal hoff hstrict) hstrict hsec.inv_L hsec.inv_A hsec.comm hinj
    hsec.Abar_ne hw).2.2.2.1

private theorem exists_natural_of_quotient {F : Type} [Field F] (eL : ↥L ≃* SL(2, F))
    (β : (↥I ⧸ fixIn L I) ≃+ (Fin 2 → F))
    (hβ : ∀ (l : ↥L) (u : ↥I) (h : (l : V ≃ₗ[ZMod 2] V) u ∈ I),
      β (Submodule.Quotient.mk ⟨_, h⟩) =
        (eL l : Matrix (Fin 2) (Fin 2) F).mulVec (β (Submodule.Quotient.mk u))) :
    ∃ β : ↥I →+ (Fin 2 → F), Function.Surjective β ∧
      (∀ u, β u = 0 ↔ ∀ l ∈ L, l (u : V) = u) ∧
      ∀ (l : ↥L) (u : ↥I) (h : (l : V ≃ₗ[ZMod 2] V) u ∈ I),
        β ⟨_, h⟩ = (eL l : Matrix (Fin 2) (Fin 2) F).mulVec (β u) := by
  refine ⟨β.toAddMonoidHom.comp (fixIn L I).mkQ.toAddMonoidHom,
    β.surjective.comp (Submodule.mkQ_surjective _), fun u => ?_, hβ⟩
  show β (Submodule.Quotient.mk u) = 0 ↔ _
  rw [AddEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]
  exact mem_fixIn

private theorem exists_alt5_of_quotient {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (ε : Ω ≃ Fin 5)
    (f : ↥L →* Equiv.Perm Ω) (hfinj : Function.Injective f)
    (hfrange : f.range = alternatingGroup Ω) (βd : (↥I ⧸ fixIn L I) ≃ₗ[ZMod 2] ↥(evenWeight Ω))
    (hβd : ∀ (l : ↥L) (u : ↥I) (h : (l : V ≃ₗ[ZMod 2] V) u ∈ I),
      (βd (Submodule.Quotient.mk ⟨_, h⟩) : Ω → ZMod 2) =
        permAct (f l) (βd (Submodule.Quotient.mk u) : Ω → ZMod 2)) :
    ∃ (eA : ↥L ≃* ↥(alternatingGroup (Fin 5))) (β : ↥I →+ (Fin 5 → ZMod 2)),
      (∀ x, x ∈ Set.range β ↔ ∑ i, x i = 0) ∧
      (∀ u, β u = 0 ↔ ∀ l ∈ L, l (u : V) = u) ∧
      ∀ (l : ↥L) (u : ↥I) (h : (l : V ≃ₗ[ZMod 2] V) u ∈ I),
        β ⟨_, h⟩ = fun i => β u (((eA l : Equiv.Perm (Fin 5))).symm i) :=
  ⟨(MonoidHom.ofInjective hfinj).trans ((MulEquiv.subgroupCongr hfrange).trans ε.altCongrHom),
    evenWeightCoords ε βd, mem_range_evenWeightCoords ε βd,
    fun u => (evenWeightCoords_eq_zero_iff ε βd u).trans mem_fixIn,
    fun l u h => evenWeightCoords_permAct ε βd (f l) u ⟨_, h⟩ (hβd l u h)⟩

private noncomputable def permHomOfSupEquiv {Ω : Type*}
    (ψ : ↥(toUnits (Lbar L A I hAn hI) ⊔ toUnits (Abar L A I hAn hI)) ≃* Equiv.Perm Ω) :
    ↥L →* Equiv.Perm Ω :=
  ψ.toMonoidHom.comp ((Subgroup.inclusion le_sup_left).comp (lbarUnitsHom hAn hI))

private theorem permHomOfSupEquiv_injective
    (hRinj : Function.Injective (actOn L A I hAn hI L le_sup_left)) {Ω : Type*}
    (ψ : ↥(toUnits (Lbar L A I hAn hI) ⊔ toUnits (Abar L A I hAn hI)) ≃* Equiv.Perm Ω) :
    Function.Injective (permHomOfSupEquiv hAn hI ψ) := by
  intro l l' h
  apply lbarUnitsHom_injective hAn hI hRinj
  have h1 := congrArg Subtype.val (ψ.injective h)
  exact Subtype.ext h1

private theorem permHomOfSupEquiv_range {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (ψ : ↥(toUnits (Lbar L A I hAn hI) ⊔ toUnits (Abar L A I hAn hI)) ≃* Equiv.Perm Ω)
    (hψ : ((toUnits (Lbar L A I hAn hI)).subgroupOf
      (toUnits (Lbar L A I hAn hI) ⊔ toUnits (Abar L A I hAn hI))).map ψ.toMonoidHom =
        alternatingGroup Ω) :
    (permHomOfSupEquiv hAn hI ψ).range = alternatingGroup Ω := by
  rw [← hψ]
  ext σ
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨Subgroup.inclusion le_sup_left (lbarUnitsHom hAn hI l),
      Subgroup.mem_subgroupOf.mpr (lbarUnitsHom hAn hI l).2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨l, hl⟩ := lbarUnitsHom_surjective hAn hI ⟨_, Subgroup.mem_subgroupOf.mp hy⟩
    refine ⟨l, ?_⟩
    show ψ (Subgroup.inclusion le_sup_left (lbarUnitsHom hAn hI l)) = ψ y
    have h1 : ((lbarUnitsHom hAn hI l : ↥(toUnits (Lbar L A I hAn hI))) :
        (Module.End (ZMod 2) (↥I ⧸ fixIn L I))ˣ) = y := congrArg Subtype.val hl
    exact congrArg ψ (Subtype.ext h1)

private theorem permHomOfSupEquiv_compat {Ω : Type*} [Fintype Ω]
    (ψ : ↥(toUnits (Lbar L A I hAn hI) ⊔ toUnits (Abar L A I hAn hI)) ≃* Equiv.Perm Ω)
    (βd : (↥I ⧸ fixIn L I) ≃ₗ[ZMod 2] ↥(evenWeight Ω))
    (hψ : ∀ (y : ↥(toUnits (Lbar L A I hAn hI) ⊔ toUnits (Abar L A I hAn hI)))
      (w : ↥I ⧸ fixIn L I),
      ((βd ((y : (Module.End (ZMod 2) (↥I ⧸ fixIn L I))ˣ).val w) : ↥(evenWeight Ω)) :
        Ω → ZMod 2) = permAct (ψ y) (βd w : Ω → ZMod 2))
    (l : ↥L) (u : ↥I) (h : (l : V ≃ₗ[ZMod 2] V) u ∈ I) :
    (βd (Submodule.Quotient.mk ⟨_, h⟩) : Ω → ZMod 2) =
      permAct (permHomOfSupEquiv hAn hI ψ l) (βd (Submodule.Quotient.mk u) : Ω → ZMod 2) := by
  rw [← lbarUnitsHom_val_mk hAn hI l u h]
  exact hψ (Subgroup.inclusion le_sup_left (lbarUnitsHom hAn hI l)) (Submodule.Quotient.mk u)

end ComponentSection

private theorem gl_sl2_alternatives [Finite V] {G L A : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hL : IsComponentIn L G) {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2 ^ n) (eL : ↥L ≃* SL(2, F)) (hAG : A ≤ G)
    (hAel : CFSG.IsElementaryAbelian 2 A) (hAne : A ≠ ⊥)
    (hoff : Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A)
    (hstrict : ∀ B : Subgroup (V ≃ₗ[ZMod 2] V), ⊥ < B → B < A →
      weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) B < weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A)
    (hcomm : ⁅L, A⁆ ≠ ⊥) :
    ∃ I : Submodule (ZMod 2) V, commGL L ⊤ = I ∧ (∀ l ∈ L, ∀ u ∈ I, l u ∈ I) ∧
      ((∃ β : ↥I →+ (Fin 2 → F), Function.Surjective β ∧
          (∀ u, β u = 0 ↔ ∀ l ∈ L, l (u : V) = u) ∧
          ∀ (l : ↥L) (u : ↥I) (h : (l : V ≃ₗ[ZMod 2] V) u ∈ I),
            β ⟨_, h⟩ = (eL l : Matrix (Fin 2) (Fin 2) F).mulVec (β u)) ∨
        (n = 2 ∧ ∃ (eA : ↥L ≃* ↥(alternatingGroup (Fin 5))) (β : ↥I →+ (Fin 5 → ZMod 2)),
          (∀ x, x ∈ Set.range β ↔ ∑ i, x i = 0) ∧
          (∀ u, β u = 0 ↔ ∀ l ∈ L, l (u : V) = u) ∧
          ∀ (l : ↥L) (u : ↥I) (h : (l : V ≃ₗ[ZMod 2] V) u ∈ I),
            β ⟨_, h⟩ = fun i => β u (((eA l : Equiv.Perm (Fin 5))).symm i))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  obtain ⟨I, hsec⟩ := CFSG.QuasithinUnique.Setup.Layer.Final.component_section hL hAG hAel hAne
    hoff hstrict hcomm
  have hI := isInvariant_sup_subgroup hsec.inv_L hsec.inv_A
  have := isSimpleGroup_of_mulEquiv_sl2 hn hF eL
  have hRinj := actOn_L_injective hsec.A_norm hI hsec.Lbar_ne
  have : Fintype (ℙ F (Fin 2 → F)) := Fintype.ofFinite _
  have : CFSG.IsElementaryAbelian 2 ↥(toUnits (Abar L A I hsec.A_norm hI)) :=
    isElementaryAbelian_of_equiv (toUnitsEquiv _) hsec.Abar_elem
  have hirr := lbar_irreducible hsec.A_norm hI hsec.irr
  obtain ⟨halt, hwU⟩ := alternatives_of_iso hn hF _ (lbarUnitsEquiv hsec.A_norm hI hRinj eL)
    (isIrreducible_repOfSubgroup_toUnits hirr.1 hirr.2) (toUnits (Abar L A I hsec.A_norm hI))
    (toUnits_ne_bot hsec.Abar_ne) (toUnits_normalizer (abar_le_normalizer_lbar hsec.A_norm hI))
    (fun a ha b hb w => hsec.Abar_quad _ ha _ hb w)
    (hsec.Abar_off.trans_eq (natCard_toUnits_mul_fix (Abar L A I hsec.A_norm hI)).symm)
  refine ⟨I, commGL_top_eq_of_section hsec.A_norm hI hsec hoff hstrict
    ((natCard_toUnits_mul_fix _).symm.trans hwU), fun l hl u hu => hsec.inv_L l hl u hu, ?_⟩
  rcases halt with ⟨-, -, β, hβ, -⟩ | ⟨-, hn2, -, -, hΩ5, ψ, βd, -, hψ2, hψ3, -⟩
  · refine Or.inl (exists_natural_of_quotient eL β fun l u h => ?_)
    rw [← lbarUnitsHom_val_mk hsec.A_norm hI l u h, hβ, lbarUnitsEquiv_lbarUnitsHom]
  · exact Or.inr ⟨hn2, exists_alt5_of_quotient (Fintype.equivFinOfCardEq hΩ5) _
      (permHomOfSupEquiv_injective hsec.A_norm hI hRinj ψ)
      (permHomOfSupEquiv_range hsec.A_norm hI ψ hψ3) βd
      (permHomOfSupEquiv_compat hsec.A_norm hI ψ βd hψ2)⟩

end Linear

open CFSG.Quasithin (fixV commV IsFFStarOffender BinaryNaturalSL FFModel)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (PstarSet IsPStar)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt)
open CFSG.QuasithinUnique.Setup.Layer.Actor (binPsi_toAdd binPsi_sub mem_fixGL_map mapEquiv)
open CFSG.QuasithinUnique.Setup.Layer.Actor (isMinOffender_map_iff exists_binModel_of_binary)
open CFSG.QuasithinUnique.Setup.Layer.Actor (isComponentIn_map_iff map_commutator_mulEquiv)
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL specialLinearGroupEquivStatedSL_coe)

variable {W : Type} [CommGroup W]

private theorem mem_commGL_map_iff {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (θ : W ≃* Multiplicative V) (L : Subgroup (MulAut W)) (v : W) :
    Multiplicative.toAdd (θ v) ∈ commGL (L.map (binPsi θ).toMonoidHom) ⊤ ↔ v ∈ commV L := by
  constructor
  · intro hv
    suffices key : ∀ x ∈ commGL (L.map (binPsi θ).toMonoidHom) ⊤,
        θ.symm (Multiplicative.ofAdd x) ∈ commV L by
      have := key _ hv
      simpa using this
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, u, -, rfl⟩ := hx
      obtain ⟨l, hl, rfl⟩ := hb
      obtain ⟨w, rfl⟩ : ∃ w, Multiplicative.toAdd (θ w) = u :=
        ⟨θ.symm (Multiplicative.ofAdd u), by simp⟩
      show θ.symm (Multiplicative.ofAdd ((binPsi θ) l (Multiplicative.toAdd (θ w)) -
        Multiplicative.toAdd (θ w))) ∈ commV L
      rw [binPsi_sub θ l w]
      simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply]
      exact Subgroup.subset_closure ⟨l, hl, w, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      have := (commV L).mul_mem hx hy
      simpa [ofAdd_add, map_mul] using this
    | smul c x _ hx =>
      have hc : c = 0 ∨ c = 1 := by revert c; decide
      rcases hc with rfl | rfl
      · simp
      · simpa using hx
  · intro hv
    induction hv using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨l, hl, w, rfl⟩ := hx
      rw [← binPsi_sub θ l w]
      exact Submodule.subset_span ⟨binPsi θ l, ⟨l, hl, rfl⟩, Multiplicative.toAdd (θ w),
        Submodule.mem_top, rfl⟩
    | one => simp
    | mul x y _ _ hx hy =>
      have := Submodule.add_mem _ hx hy
      simpa [map_mul] using this
    | inv x _ hx =>
      have := Submodule.neg_mem _ hx
      simpa [map_inv] using this

private theorem altDn_five_ker_subgroupOf_eq_bot :
    ((FFModel.altDn 5).ker).subgroupOf (FFModel.altDn 5).sec = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨x, hxs⟩ hx
  rw [Subgroup.mem_subgroupOf] at hx
  obtain ⟨hxz, hxc⟩ := hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxz
  have hcoord : ∀ i : Fin 5,
      Multiplicative.toAdd ((CFSG.Quasithin.G6.allOnes 5) ^ k) i = ((k : ℤ) : ZMod 2) := by
    intro i
    rw [toAdd_zpow]
    show k • (1 : ZMod 2) = _
    rw [zsmul_one]
  have hsum : ∑ i : Fin 5, Multiplicative.toAdd ((CFSG.Quasithin.G6.allOnes 5) ^ k) i = 0 := hxc
  simp only [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have h5 : ((5 : ℕ) : ZMod 2) = 1 := by decide
  rw [h5, one_mul] at hsum
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext i
  show Multiplicative.toAdd ((CFSG.Quasithin.G6.allOnes 5) ^ k) i = 0
  rw [hcoord i, hsum]

private theorem altDn_five_eq_one_of_mem_ker {x : (FFModel.altDn 5).Amb}
    (hx : x ∈ (FFModel.altDn 5).ker) : x = 1 := by
  have hx' : x ∈ Subgroup.zpowers (CFSG.Quasithin.G6.allOnes 5) ⊓
      CFSG.Quasithin.G6.coreMod 5 := hx
  have hxs : x ∈ (FFModel.altDn 5).sec := (Subgroup.mem_inf.mp hx').2
  have hsub : (⟨x, hxs⟩ : ↥(FFModel.altDn 5).sec) ∈
      ((FFModel.altDn 5).ker).subgroupOf (FFModel.altDn 5).sec :=
    Subgroup.mem_subgroupOf.mpr hx
  rw [altDn_five_ker_subgroupOf_eq_bot, Subgroup.mem_bot] at hsub
  exact congrArg Subtype.val hsub

private theorem altDn_five_act_mem_ker (γ : (FFModel.altDn 5).Gam) (x : (FFModel.altDn 5).Amb)
    (hx : x ∈ (FFModel.altDn 5).ker) : (FFModel.altDn 5).act γ x ∈ (FFModel.altDn 5).ker := by
  rw [altDn_five_eq_one_of_mem_ker hx]
  have h1 : (FFModel.altDn 5).act γ 1 = 1 := (fun σ : ↥(alternatingGroup (Fin 5)) =>
    map_one (CFSG.Quasithin.G6.permAct 5 (σ : Equiv.Perm (Fin 5)))) γ
  rw [h1]
  exact Subgroup.one_mem _

private theorem altDn_five_quotient_mk_injective (x y : ↥(FFModel.altDn 5).sec)
    (hxy : (QuotientGroup.mk x : ↥(FFModel.altDn 5).sec ⧸
      ((FFModel.altDn 5).ker).subgroupOf (FFModel.altDn 5).sec) = QuotientGroup.mk y) :
    x = y := by
  have := QuotientGroup.eq.mp hxy
  rw [altDn_five_ker_subgroupOf_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at this
  exact this

private theorem isMinOffender_map_of_isPStar {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (θ : W ≃* Multiplicative V) {Y A : Subgroup (MulAut W)} (hAP : IsPStar Y A) :
    IsMinOffender (Y.map (binPsi θ).toMonoidHom) (A.map (binPsi θ).toMonoidHom) := by
  obtain ⟨hAoff, hAmin⟩ := hAP
  have hA : IsFFStarOffender Y A := hAoff
  refine (isMinOffender_map_iff θ Y A).mpr ⟨hA.1, hA.2.1, hA.2.2.1, ?_, fun B hBA hB hBA' => ?_⟩
  · have h1 := hA.2.2.2 ⊥ bot_le
    have h2 : fixV (⊥ : Subgroup (MulAut W)) = ⊤ := by
      ext v
      simp only [Subgroup.mem_top, iff_true]
      intro x hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      rfl
    rw [Subgroup.card_bot, one_mul, h2, Subgroup.card_top] at h1
    exact h1
  · refine lt_of_le_of_ne (hA.2.2.2 B hBA) fun heq => hBA' ?_
    refine hAmin B ⟨hBA.trans hA.1, hB, ⟨fun a ha b hb => hA.2.2.1.1 a (hBA ha) b (hBA hb),
      fun a ha => hA.2.2.1.2 a (hBA ha)⟩, fun B' hB' => ?_⟩ hBA heq.symm
    rw [heq]
    exact hA.2.2.2 B' (hB'.trans hBA)

private theorem isComponentIn_map_of_sl2 {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (θ : W ≃* Multiplicative V) {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hsn : (L.subgroupOf Y).IsSubnormal) {K : Type} [Field K] [Finite K] (h4 : 4 ≤ Nat.card K)
    (eL : ↥L ≃* SL(2, K)) :
    IsComponentIn (L.map (binPsi θ).toMonoidHom) (Y.map (binPsi θ).toMonoidHom) :=
  (isComponentIn_map_iff (binPsi θ)).mpr ⟨hLY,
    CFSG.IsQuasisimple.of_mulEquiv ((Subgroup.subgroupOfEquivOfLe hLY).trans eL)
      (CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree.isQuasisimple_specialLinear_two h4),
    hsn⟩

private theorem coe_sl2Equiv_mapEquiv {G' : Type*} [Group G'] (ψ : MulAut W ≃* G')
    {L : Subgroup (MulAut W)} {K : Type} [Field K] (e : ↥L ≃* ↥(CFSG.Open.StatedSL 2 K))
    (γ : ↥(CFSG.Open.StatedSL 2 K)) :
    ((((mapEquiv ψ L).symm.trans (e.trans (specialLinearGroupEquivStatedSL 2 K).symm))
      (mapEquiv ψ L (e.symm γ)) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply, ← specialLinearGroupEquivStatedSL_coe 2 K,
    MulEquiv.apply_symm_apply]

section Model

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {θ : W ≃* Multiplicative V}
variable {L : Subgroup (MulAut W)} {I : Submodule (ZMod 2) V}

private theorem apply_mem_commV_of_model
    (hmemI : ∀ v : W, Multiplicative.toAdd (θ v) ∈ I ↔ v ∈ commV L)
    (hIinv : ∀ l ∈ L.map (binPsi θ).toMonoidHom, ∀ u ∈ I, l u ∈ I) (l : ↥L) (u : W)
    (hu : u ∈ commV L) : (l : MulAut W) u ∈ commV L := by
  rw [← hmemI, ← binPsi_toAdd θ]
  exact hIinv _ ⟨l, l.2, rfl⟩ _ ((hmemI u).mpr hu)

private theorem apply_mem_gomiWXKer_of_model
    (hmemI : ∀ v : W, Multiplicative.toAdd (θ v) ∈ I ↔ v ∈ commV L)
    (hIinv : ∀ l ∈ L.map (binPsi θ).toMonoidHom, ∀ u ∈ I, l u ∈ I) (l : ↥L) (z : W)
    (hz : z ∈ gomiWXKer L) : (l : MulAut W) z ∈ gomiWXKer L := by
  refine ⟨apply_mem_commV_of_model hmemI hIinv l z hz.1, ?_⟩
  rw [hz.2 _ l.2]
  exact hz.2

private def commVHom (hmemI : ∀ v : W, Multiplicative.toAdd (θ v) ∈ I ↔ v ∈ commV L)
    {M : Type*} [AddCommGroup M] (β : ↥I →+ M) : ↥(commV L) →* Multiplicative M where
  toFun u := Multiplicative.ofAdd (β ⟨Multiplicative.toAdd (θ u), (hmemI u).mpr u.2⟩)
  map_one' := by
    have : (⟨Multiplicative.toAdd (θ ((1 : ↥(commV L)) : W)),
        (hmemI _).mpr (1 : ↥(commV L)).2⟩ : ↥I) = 0 := Subtype.ext (by simp)
    simp only [this, map_zero, ofAdd_zero]
  map_mul' u u' := by
    have : (⟨Multiplicative.toAdd (θ ((u * u' : ↥(commV L)) : W)),
        (hmemI _).mpr (u * u').2⟩ : ↥I) =
        ⟨Multiplicative.toAdd (θ u), (hmemI u).mpr u.2⟩ +
          ⟨Multiplicative.toAdd (θ u'), (hmemI u').mpr u'.2⟩ :=
      Subtype.ext (by simp)
    simp only [this, map_add, ofAdd_add]

private theorem commVHom_apply
    (hmemI : ∀ v : W, Multiplicative.toAdd (θ v) ∈ I ↔ v ∈ commV L) {M : Type*}
    [AddCommGroup M] (β : ↥I →+ M) (u : ↥(commV L)) :
    commVHom hmemI β u =
      Multiplicative.ofAdd (β ⟨Multiplicative.toAdd (θ u), (hmemI u).mpr u.2⟩) :=
  rfl

private theorem exists_commVHom_eq
    (hmemI : ∀ v : W, Multiplicative.toAdd (θ v) ∈ I ↔ v ∈ commV L) {M : Type*}
    [AddCommGroup M] (β : ↥I →+ M) (x : ↥I) :
    ∃ u, commVHom hmemI β u = Multiplicative.ofAdd (β x) := by
  have hv : θ.symm (Multiplicative.ofAdd (x : V)) ∈ commV L := by
    rw [← hmemI]
    simp
  refine ⟨⟨_, hv⟩, ?_⟩
  rw [commVHom_apply]
  have : (⟨Multiplicative.toAdd (θ (θ.symm (Multiplicative.ofAdd (x : V)))),
      (hmemI _).mpr hv⟩ : ↥I) = x := Subtype.ext (by simp)
  rw [this]

private theorem commVHom_eq_one_iff
    (hmemI : ∀ v : W, Multiplicative.toAdd (θ v) ∈ I ↔ v ∈ commV L) {M : Type*}
    [AddCommGroup M] (β : ↥I →+ M)
    (hβk : ∀ u, β u = 0 ↔ ∀ l ∈ L.map (binPsi θ).toMonoidHom, l (u : V) = u)
    (u : ↥(commV L)) : commVHom hmemI β u = 1 ↔ (u : W) ∈ gomiWXKer L := by
  have hfixL : ∀ v : W, (∀ l ∈ L.map (binPsi θ).toMonoidHom,
      l (Multiplicative.toAdd (θ v)) = Multiplicative.toAdd (θ v)) ↔ v ∈ fixV L :=
    fun v => mem_fixGL_map θ L v
  rw [commVHom_apply, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, hβk]
  show _ ↔ (u : W) ∈ commV L ∧ (u : W) ∈ fixV L
  rw [hfixL]
  exact ⟨fun h => ⟨u.2, h⟩, fun h => h.2⟩

private theorem map_commV_of_equivariant
    (hmemI : ∀ v : W, Multiplicative.toAdd (θ v) ∈ I ↔ v ∈ commV L)
    (hIinv : ∀ l ∈ L.map (binPsi θ).toMonoidHom, ∀ u ∈ I, l u ∈ I) {M : Type*} (β : ↥I → M)
    (act : ↥(L.map (binPsi θ).toMonoidHom) → M → M)
    (hβe : ∀ (l : ↥(L.map (binPsi θ).toMonoidHom)) (u : ↥I) (h : (l : V ≃ₗ[ZMod 2] V) u ∈ I),
      β ⟨_, h⟩ = act l (β u))
    (l : ↥L) (u : W) (hu : u ∈ commV L) (hlu : (l : MulAut W) u ∈ commV L) :
    β ⟨Multiplicative.toAdd (θ ((l : MulAut W) u)), (hmemI _).mpr hlu⟩ =
      act (mapEquiv (binPsi θ) L l) (β ⟨Multiplicative.toAdd (θ u), (hmemI u).mpr hu⟩) := by
  have hmem : binPsi θ (l : MulAut W) ∈ L.map (binPsi θ).toMonoidHom := ⟨l, l.2, rfl⟩
  have h1 : (⟨Multiplicative.toAdd (θ ((l : MulAut W) u)), (hmemI _).mpr hlu⟩ : ↥I) =
      ⟨binPsi θ (l : MulAut W) (Multiplicative.toAdd (θ u)),
        hIinv _ hmem _ ((hmemI u).mpr hu)⟩ := Subtype.ext (binPsi_toAdd θ l u).symm
  rw [h1]
  exact hβe ⟨binPsi θ (l : MulAut W), hmem⟩ ⟨Multiplicative.toAdd (θ u), (hmemI u).mpr hu⟩ _

private theorem realizesVia_nat_of_model
    (hmemI : ∀ v : W, Multiplicative.toAdd (θ v) ∈ I ↔ v ∈ commV L)
    (hIinv : ∀ l ∈ L.map (binPsi θ).toMonoidHom, ∀ u ∈ I, l u ∈ I) {K : Type} [Field K]
    (e : ↥L ≃* ↥(CFSG.Open.StatedSL 2 K)) (eL' : ↥(L.map (binPsi θ).toMonoidHom) ≃* SL(2, K))
    (β : ↥I →+ (Fin 2 → K)) (hβs : Function.Surjective β)
    (hβk : ∀ u, β u = 0 ↔ ∀ l ∈ L.map (binPsi θ).toMonoidHom, l (u : V) = u)
    (hβe : ∀ (l : ↥(L.map (binPsi θ).toMonoidHom)) (u : ↥I) (h : (l : V ≃ₗ[ZMod 2] V) u ∈ I),
      β ⟨_, h⟩ = (eL' l : Matrix (Fin 2) (Fin 2) K).mulVec (β u))
    (heL' : ∀ γ, ((eL' (mapEquiv (binPsi θ) L (e.symm γ)) : SL(2, K)) :
      Matrix (Fin 2) (Fin 2) K) = ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) :
    (FFModel.nat (CFSG.Open.StatedSL 2 K)).RealizesVia L (commV L) (gomiWXKer L)
      e.symm.toMonoidHom := by
  refine CFSG.Quasithin.G64.realizesVia_nat_of e.symm.surjective inf_le_left
    (apply_mem_commV_of_model hmemI hIinv) (apply_mem_gomiWXKer_of_model hmemI hIinv)
    (commVHom hmemI β) (fun x => ?_) (commVHom_eq_one_iff hmemI β hβk) fun γ u hu => ?_
  · obtain ⟨u', hu'⟩ := hβs (Multiplicative.toAdd x)
    obtain ⟨u, hu⟩ := exists_commVHom_eq hmemI β u'
    exact ⟨u, hu.trans (congrArg Multiplicative.ofAdd hu')⟩
  · have key := map_commV_of_equivariant hmemI hIinv β
      (fun l x => (eL' l : Matrix (Fin 2) (Fin 2) K).mulVec x) hβe (e.symm γ) u u.2 hu
    rw [commVHom_apply, commVHom_apply]
    exact congrArg Multiplicative.ofAdd (key.trans (congrArg (Matrix.mulVec · _) (heL' γ)))

private def commVCore (hmemI : ∀ v : W, Multiplicative.toAdd (θ v) ∈ I ↔ v ∈ commV L)
    (βd : ↥I →+ (Fin 5 → ZMod 2)) (hβr : ∀ x, x ∈ Set.range βd ↔ ∑ i, x i = 0) :
    ↥(commV L) →* ↥(FFModel.altDn 5).sec :=
  (commVHom hmemI βd : ↥(commV L) →* CFSG.Quasithin.G6.PermMod 5).codRestrict
    (FFModel.altDn 5).sec fun _ => (hβr _).mp ⟨_, rfl⟩

private theorem commVCore_surjective
    (hmemI : ∀ v : W, Multiplicative.toAdd (θ v) ∈ I ↔ v ∈ commV L)
    (βd : ↥I →+ (Fin 5 → ZMod 2)) (hβr : ∀ x, x ∈ Set.range βd ↔ ∑ i, x i = 0) :
    Function.Surjective (commVCore hmemI βd hβr) := by
  intro x
  obtain ⟨y, hy⟩ := (hβr (Multiplicative.toAdd (x.1 : CFSG.Quasithin.G6.PermMod 5))).mpr x.2
  obtain ⟨u, hu⟩ := exists_commVHom_eq hmemI βd y
  refine ⟨u, Subtype.ext ?_⟩
  show commVHom hmemI βd u = _
  exact hu.trans (congrArg Multiplicative.ofAdd hy)

private theorem commVCore_act
    (hmemI : ∀ v : W, Multiplicative.toAdd (θ v) ∈ I ↔ v ∈ commV L)
    (βd : ↥I →+ (Fin 5 → ZMod 2)) (hβr : ∀ x, x ∈ Set.range βd ↔ ∑ i, x i = 0)
    (eA : ↥L ≃* ↥(alternatingGroup (Fin 5)))
    (hβe : ∀ (l : ↥L) (u : W) (hu : u ∈ commV L) (hlu : (l : MulAut W) u ∈ commV L),
      βd ⟨Multiplicative.toAdd (θ ((l : MulAut W) u)), (hmemI _).mpr hlu⟩ = fun i =>
        βd ⟨Multiplicative.toAdd (θ u), (hmemI u).mpr hu⟩ ((eA l : Equiv.Perm (Fin 5)).symm i))
    (γ : ↥(alternatingGroup (Fin 5))) (u : ↥(commV L))
    (hu : ((eA.symm γ : ↥L) : MulAut W) u ∈ commV L) :
    (commVCore hmemI βd hβr ⟨_, hu⟩ : (FFModel.altDn 5).Amb) =
      (FFModel.altDn 5).act γ (commVCore hmemI βd hβr u) := by
  have key := hβe (eA.symm γ) u u.2 hu
  rw [MulEquiv.apply_symm_apply] at key
  exact congrArg Multiplicative.ofAdd key

private theorem realizesVia_altDn_five_of_model
    (hmemI : ∀ v : W, Multiplicative.toAdd (θ v) ∈ I ↔ v ∈ commV L)
    (hIinv : ∀ l ∈ L.map (binPsi θ).toMonoidHom, ∀ u ∈ I, l u ∈ I)
    (eA : ↥(L.map (binPsi θ).toMonoidHom) ≃* ↥(alternatingGroup (Fin 5)))
    (βd : ↥I →+ (Fin 5 → ZMod 2)) (hβr : ∀ x, x ∈ Set.range βd ↔ ∑ i, x i = 0)
    (hβk : ∀ u, βd u = 0 ↔ ∀ l ∈ L.map (binPsi θ).toMonoidHom, l (u : V) = u)
    (hβe : ∀ (l : ↥(L.map (binPsi θ).toMonoidHom)) (u : ↥I) (h : (l : V ≃ₗ[ZMod 2] V) u ∈ I),
      βd ⟨_, h⟩ = fun i => βd u (((eA l : Equiv.Perm (Fin 5))).symm i)) :
    (FFModel.altDn 5).RealizesVia L (commV L) (gomiWXKer L)
      ((mapEquiv (binPsi θ) L).trans eA).symm.toMonoidHom := by
  refine ⟨((mapEquiv (binPsi θ) L).trans eA).symm.surjective, inf_le_left, inf_le_right,
    apply_mem_commV_of_model hmemI hIinv, apply_mem_gomiWXKer_of_model hmemI hIinv,
    fun γ x hx => CFSG.Quasithin.G6.permAct_mem_coreMod (n := 5) _ hx, altDn_five_act_mem_ker,
    (QuotientGroup.mk' _).comp (commVCore hmemI βd hβr),
    (QuotientGroup.mk'_surjective _).comp (commVCore_surjective hmemI βd hβr),
    fun u => ?_, fun γ u x hu hx hux => ?_⟩
  · show QuotientGroup.mk (commVCore hmemI βd hβr u) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, altDn_five_ker_subgroupOf_eq_bot, Subgroup.mem_bot,
      ← OneMemClass.coe_eq_one]
    exact commVHom_eq_one_iff hmemI βd hβk u
  · obtain rfl := altDn_five_quotient_mk_injective _ _ hux
    show QuotientGroup.mk (commVCore hmemI βd hβr ⟨_, hu⟩) = QuotientGroup.mk ⟨_, hx⟩
    congr 1
    exact Subtype.ext (commVCore_act hmemI βd hβr ((mapEquiv (binPsi θ) L).trans eA)
      (map_commV_of_equivariant hmemI hIinv βd
        (fun l x i => x ((eA l : Equiv.Perm (Fin 5)).symm i)) hβe) γ u hu)

end Model

variable [Finite W]

theorem gomiFact37Two_of_isSLn (hW : ∀ w : W, w ^ 2 = 1) {Y S L : Subgroup (MulAut W)}
    (hyp : GomiFact37Hyp Y S L) {m : ℕ} (hm : 2 ≤ m) (hL : IsSLn ↥L 2 m)
    (hP : ⁅L, sSup (PstarSet Y)⁆ ≠ ⊥) :
    BinaryNaturalSL L (commV L) (gomiWXKer L) 2 m ∨
      (m = 2 ∧ (FFModel.altDn 5).Realizes L (commV L) (gomiWXKer L)) := by
  classical
  obtain ⟨-, -, hLY, hsn, -, -⟩ := hyp
  obtain ⟨A, hAP, hLA⟩ := exists_mem_commutator_ne_bot_of_sSup hP
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hL
  have : Fintype K := Fintype.ofFinite K
  have hKc : Fintype.card K = 2 ^ m := by rw [Fintype.card_eq_nat_card, hK]
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  obtain ⟨V, _, _, _, ⟨θ⟩⟩ :=
    exists_binModel_of_binary (fun v : W => by rw [← pow_two]; exact hW v)
  obtain ⟨hAG, hAne, hAel, hoff, hstrict⟩ := isMinOffender_map_of_isPStar θ hAP
  obtain ⟨I, hIL, hIinv, halt⟩ := gl_sl2_alternatives
    (isComponentIn_map_of_sl2 θ hLY hsn h4 (e.trans (specialLinearGroupEquivStatedSL 2 K).symm))
    hm hKc
    ((mapEquiv (binPsi θ) L).symm.trans (e.trans (specialLinearGroupEquivStatedSL 2 K).symm))
    hAG hAel hAne hoff hstrict (by
      rw [← map_commutator_mulEquiv]
      intro h
      exact hLA ((Subgroup.map_eq_bot_iff_of_injective _ (binPsi θ).injective).mp h))
  have hmemI : ∀ v : W, Multiplicative.toAdd (θ v) ∈ I ↔ v ∈ commV L := fun v => by
    rw [← hIL]
    exact mem_commGL_map_iff θ L v
  rcases halt with ⟨β, hβs, hβk, hβe⟩ | ⟨hm2, eA, βd, hβr, hβk, hβe⟩
  · exact Or.inl ⟨K, inferInstance, inferInstance, hK, e.symm.toMonoidHom,
      realizesVia_nat_of_model hmemI hIinv e _ β hβs hβk hβe
        (coe_sl2Equiv_mapEquiv (binPsi θ) e)⟩
  · exact Or.inr ⟨hm2, _, realizesVia_altDn_five_of_model hmemI hIinv eA βd hβr hβk hβe⟩

theorem gomiFact37Two_of_isAlt_five (hW : ∀ w : W, w ^ 2 = 1) {Y S L : Subgroup (MulAut W)}
    (hyp : GomiFact37Hyp Y S L) (hL : IsAlt ↥L 5) (hP : ⁅L, sSup (PstarSet Y)⁆ ≠ ⊥) :
    (∃ m : ℕ, 2 ≤ m ∧ IsSLn ↥L 2 m ∧ BinaryNaturalSL L (commV L) (gomiWXKer L) 2 m) ∨
      (∃ m : ℕ, 2 ≤ m ∧ IsAlt ↥L (2 * m - 1) ∧
        (FFModel.altDn (2 * m - 1)).Realizes L (commV L) (gomiWXKer L)) := by
  obtain ⟨eA⟩ := hL
  obtain ⟨e4⟩ := CFSG.Quasithin.S146zX.nonempty_mulEquiv_sl_two_four_of_alt_five
  have hSL : IsSLn ↥L 2 2 :=
    ⟨GaloisField 2 2, inferInstance, inferInstance, GaloisField.card 2 2 (by norm_num),
      ⟨(eA.trans e4.symm).trans (specialLinearGroupEquivStatedSL 2 (GaloisField 2 2))⟩⟩
  rcases gomiFact37Two_of_isSLn hW hyp le_rfl hSL hP with h | ⟨-, h⟩
  · exact Or.inl ⟨2, le_rfl, hSL, h⟩
  · exact Or.inr ⟨3, by norm_num, ⟨eA⟩, h⟩

end CFSG.GroupTheory

end
