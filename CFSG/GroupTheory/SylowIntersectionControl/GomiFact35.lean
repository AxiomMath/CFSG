module

public import CFSG.Quasithin.MS93.S46SL2
public import CFSG.Quasithin.Background.G64NatSec
public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpSL
import CFSG.Open.MatrixFixedVectors
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.SubrepresentationLattice

public section

namespace CFSG.GroupTheory

open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.Quasithin.MS93.S46
open CFSG.Quasithin (fixV IsElemAbelian2 BinaryNaturalSL FFModel natAct)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL specialLinearGroupEquivStatedSL_coe)
open scoped MatrixGroups

section Additive

variable {F : Type} [Field F] [Fintype F] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [Finite V]

private theorem finrank_le_add_finrank_of_card_le {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Module.Finite (ZMod 2) V] {A : Type*} [Fintype A] {a : ℕ}
    (ha : Nat.card A = 2 ^ a) {C : Submodule (ZMod 2) V}
    (h : Nat.card V ≤ Nat.card A * Nat.card C) :
    Module.finrank (ZMod 2) V ≤ a + Module.finrank (ZMod 2) C := by
  have hV : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hC : Nat.card C = 2 ^ Module.finrank (ZMod 2) C := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hV, hC, ha, ← pow_add] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

private theorem sl2OddFix_quotient_fixed_eq_bot {F V : Type*} [Field F] [Fintype F]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, F) V) (q : V ⧸ sl2OddFix ρ)
    (hq : ∀ g : SL(2, F), Odd (orderOf g) →
      (ρ.quotient (sl2OddFix ρ) (fun g _ hv => apply_mem_sl2OddFix ρ g hv)) g q = q) :
    q = 0 := by
  obtain ⟨v, rfl⟩ := (sl2OddFix ρ).mkQ_surjective q
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine (mem_sl2OddFix ρ).mpr fun g hg => ?_
  have h1 : (sl2OddFix ρ).mkQ (ρ g v) = (sl2OddFix ρ).mkQ v := hq g hg
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h1
  exact eq_of_odd_of_fix_sub ρ hg ((mem_sl2OddFix ρ).mp h1 g hg)

private theorem exists_irreducible_subrepresentation {k G M : Type*} [Field k] [Group G]
    [AddCommGroup M] [Module k M] [Module.Finite k M] (σ : Representation k G M)
    (hnt : Nontrivial M) :
    ∃ S : Subrepresentation σ, S ≠ ⊥ ∧ S.toRepresentation.IsIrreducible := by
  classical
  have hbt : (⊥ : Subrepresentation σ) ≠ ⊤ := by
    intro h
    have h' : (⊥ : Submodule k M) = ⊤ := congrArg Subrepresentation.toSubmodule h
    obtain ⟨x, y, hxy⟩ := hnt
    have hx : x - y ∈ (⊥ : Submodule k M) := h' ▸ Submodule.mem_top
    exact hxy (sub_eq_zero.mp ((Submodule.mem_bot k).mp hx))
  have hex : ∃ d, ∃ S : Subrepresentation σ, S ≠ ⊥ ∧
      Module.finrank k S.toSubmodule = d := ⟨_, ⊤, hbt.symm, rfl⟩
  obtain ⟨S, hSne, hSd⟩ := Nat.find_spec hex
  have hSmin : ∀ T : Subrepresentation σ, T ≠ ⊥ →
      Nat.find hex ≤ Module.finrank k T.toSubmodule :=
    fun T hT => Nat.find_min' hex ⟨T, hT, rfl⟩
  have hSbot : S.toSubmodule ≠ ⊥ := fun h => hSne (Subrepresentation.toSubmodule_injective h)
  refine ⟨S, hSne, ?_⟩
  have : Nontrivial (Subrepresentation S.toRepresentation) := by
    refine ⟨⊥, ⊤, fun h => ?_⟩
    have h' : (⊥ : Submodule k S.toSubmodule) = ⊤ :=
      congrArg Subrepresentation.toSubmodule h
    obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSbot
    have hmem : (⟨s, hs⟩ : S.toSubmodule) ∈ (⊥ : Submodule k S.toSubmodule) :=
      h' ▸ Submodule.mem_top
    exact hs0 (by simpa using hmem)
  refine { eq_bot_or_eq_top := fun T => ?_ }
  by_cases hT : T = ⊥
  · exact Or.inl hT
  right
  have hTbot : T.toSubmodule ≠ ⊥ := fun h => hT (Subrepresentation.toSubmodule_injective h)
  let T' : Subrepresentation σ :=
    { toSubmodule := T.toSubmodule.map S.toSubmodule.subtype
      apply_mem_toSubmodule := by
        rintro g _ ⟨t, ht, rfl⟩
        exact ⟨S.toRepresentation g t, T.apply_mem_toSubmodule g ht, rfl⟩ }
  have hT' : T' ≠ ⊥ := by
    intro h
    obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hTbot
    have hmem : (t : M) ∈ T'.toSubmodule := ⟨t, ht, rfl⟩
    rw [h] at hmem
    exact ht0 (Subtype.ext ((Submodule.mem_bot _).mp hmem))
  have h1 := hSmin T' hT'
  have h2 : Module.finrank k T'.toSubmodule = Module.finrank k T.toSubmodule :=
    Submodule.finrank_map_subtype_eq _ _
  apply Subrepresentation.toSubmodule_injective
  exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (by omega))

private theorem exists_action_ne_one_of_fixed_eq_bot {k G M : Type*} [Field k] [Group G]
    [AddCommGroup M] [Module k M] (σ : Representation k G M) (S : Subrepresentation σ)
    (hS : S.toSubmodule ≠ ⊥)
    (hfixed : ∀ q : M, (∀ g : G, Odd (orderOf g) → σ g q = q) → q = 0) :
    ∃ g : G, S.toRepresentation g ≠ 1 := by
  by_contra h
  push Not at h
  apply hS
  rw [eq_bot_iff]
  intro s hs
  rw [Submodule.mem_bot]
  refine hfixed s fun g hg => ?_
  exact congrArg Subtype.val (LinearMap.congr_fun (h g) ⟨s, hs⟩)

private theorem finrank_quotient_le_add_finrank_fix {F V : Type*} [Field F] [Fintype F]
    [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    {A : Subgroup SL(2, F)} [CFSG.IsElementaryAbelian 2 A]
    (ρ : Representation (ZMod 2) SL(2, F) V) {a : ℕ}
    (hdimC : Module.finrank (ZMod 2) V ≤ a +
      Module.finrank (ZMod 2) (CFSG.Quasithin.MS93.S46.sl2Fix ρ (A : Set SL(2, F)))) :
    Module.finrank (ZMod 2) (V ⧸ sl2OddFix ρ) ≤ a +
      Module.finrank (ZMod 2) (CFSG.Quasithin.MS93.S46.sl2Fix
        (ρ.quotient (sl2OddFix ρ) (fun g _ hv => apply_mem_sl2OddFix ρ g hv))
        (A : Set SL(2, F))) := by
  classical
  set W := sl2OddFix ρ with hWdef
  set C := CFSG.Quasithin.MS93.S46.sl2Fix ρ (A : Set SL(2, F)) with hCdef
  have hdimC' : Module.finrank (ZMod 2) V ≤ a + Module.finrank (ZMod 2) C := hdimC
  set σ : Representation (ZMod 2) SL(2, F) (V ⧸ W) :=
    ρ.quotient W (fun g _ hv => apply_mem_sl2OddFix ρ g hv) with hσdef
  have hσ : ∀ g v, σ g (W.mkQ v) = W.mkQ (ρ g v) := fun g v => rfl
  set CQ := CFSG.Quasithin.MS93.S46.sl2Fix σ (A : Set SL(2, F)) with hCQdef
  have hquot := Submodule.finrank_quotient_add_finrank W
  let f : C →ₗ[ZMod 2] V ⧸ W := W.mkQ.comp C.subtype
  have hrange : LinearMap.range f ≤ CQ := by
    rintro _ ⟨c, rfl⟩ g hg
    show σ g (W.mkQ c) = W.mkQ c
    rw [hσ, c.2 g hg]
  have hker : (LinearMap.ker f).map C.subtype ≤ W := by
    rintro _ ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hc
    simpa [f] using hc
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 := Submodule.finrank_mono hrange
  have h3 := Submodule.finrank_mono hker
  rw [Submodule.finrank_map_subtype_eq] at h3
  change Module.finrank (ZMod 2) (V ⧸ W) ≤ a + Module.finrank (ZMod 2) CQ
  omega

private theorem card_le_offender_subrepresentation {F V : Type*} [Field F] [Fintype F]
    [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    {A : Subgroup SL(2, F)} [CFSG.IsElementaryAbelian 2 A]
    (ρ : Representation (ZMod 2) SL(2, F) V) {a : ℕ} (ha : Nat.card A = 2 ^ a)
    (hdimCQ : Module.finrank (ZMod 2) (V ⧸ sl2OddFix ρ) ≤ a +
      Module.finrank (ZMod 2) (CFSG.Quasithin.MS93.S46.sl2Fix
        (ρ.quotient (sl2OddFix ρ) (fun g _ hv => apply_mem_sl2OddFix ρ g hv))
        (A : Set SL(2, F)))) :
    ∀ S : Subrepresentation (ρ.quotient (sl2OddFix ρ)
      (fun g _ hv => apply_mem_sl2OddFix ρ g hv)),
      Nat.card S.toSubmodule ≤ Nat.card A *
        Nat.card {s : S.toSubmodule // ∀ g ∈ A, S.toRepresentation g s = s} := by
  classical
  set W := sl2OddFix ρ with hWdef
  set σ : Representation (ZMod 2) SL(2, F) (V ⧸ W) :=
    ρ.quotient W (fun g _ hv => apply_mem_sl2OddFix ρ g hv) with hσdef
  set CQ := CFSG.Quasithin.MS93.S46.sl2Fix σ (A : Set SL(2, F)) with hCQdef
  have hdimCQ' : Module.finrank (ZMod 2) (V ⧸ W) ≤ a + Module.finrank (ZMod 2) CQ := hdimCQ
  intro S
  set CS := CFSG.Quasithin.MS93.S46.sl2Fix S.toRepresentation (A : Set SL(2, F)) with hCSdef
  have hCSmap : CS.map S.toSubmodule.subtype = S.toSubmodule ⊓ CQ := by
    ext q
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s.2, fun g hg => congrArg Subtype.val (hs g hg)⟩
    · rintro ⟨hqS, hqC⟩
      exact ⟨⟨q, hqS⟩, fun g hg => Subtype.ext (hqC g hg), rfl⟩
  have hdimCS : Module.finrank (ZMod 2) CS =
      Module.finrank (ZMod 2) ↥(S.toSubmodule ⊓ CQ) := by
    rw [← hCSmap, Submodule.finrank_map_subtype_eq]
  have hsi : Module.finrank (ZMod 2) ↥(S.toSubmodule ⊔ CQ) +
      Module.finrank (ZMod 2) CS =
      Module.finrank (ZMod 2) ↥S.toSubmodule + Module.finrank (ZMod 2) CQ := by
    rw [hdimCS]
    exact Submodule.finrank_sup_add_finrank_inf_eq S.toSubmodule CQ
  have hsle : Module.finrank (ZMod 2) ↥(S.toSubmodule ⊔ CQ) ≤
      Module.finrank (ZMod 2) (V ⧸ W) := Submodule.finrank_le _
  have hmain : Module.finrank (ZMod 2) ↥S.toSubmodule ≤
      a + Module.finrank (ZMod 2) CS := by omega
  have hcard1 : Nat.card {s : S.toSubmodule // ∀ g ∈ A, S.toRepresentation g s = s} =
      Nat.card CS := Nat.card_congr (Equiv.subtypeEquivRight fun s => Iff.rfl)
  have hS : Nat.card ↥S.toSubmodule = 2 ^ Module.finrank (ZMod 2) ↥S.toSubmodule := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hCS : Nat.card ↥CS = 2 ^ Module.finrank (ZMod 2) ↥CS := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hcard1, ha, hS, hCS, ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) hmain

theorem card_eq_of_offender_sl2 {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    (ρ : Representation (ZMod 2) SL(2, F) V)
    (hO : CFSG.Quasithin.MS93.S46.sl2OddFix ρ ≠ ⊤) (A : Subgroup SL(2, F))
    [CFSG.IsElementaryAbelian 2 A] (hA1 : A ≠ ⊥)
    (hoff : Nat.card V ≤ Nat.card A *
      Nat.card (CFSG.Quasithin.MS93.S46.sl2Fix ρ (A : Set SL(2, F)))) :
    Nat.card A = Nat.card F := by
  classical
  have : CharP F 2 := charP_two_of_card_eq hF
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hcardF : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · have := Fintype.one_lt_card (α := F)
      rw [hF] at this
      simp at this
    · exact h
  obtain ⟨a, ha⟩ : ∃ a : ℕ, Nat.card A = 2 ^ a := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine IsPGroup.iff_card.mp fun g => ⟨1, Subtype.ext ?_⟩
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (g : SL(2, F)) g.2
    simpa using this
  have hdimC : Module.finrank (ZMod 2) V ≤ a +
      Module.finrank (ZMod 2) (CFSG.Quasithin.MS93.S46.sl2Fix ρ (A : Set SL(2, F))) :=
    finrank_le_add_finrank_of_card_le ha hoff
  have hWinv : ∀ g, sl2OddFix ρ ≤ (sl2OddFix ρ).comap (ρ g) :=
    fun g _ hv => apply_mem_sl2OddFix ρ g hv
  set σ := ρ.quotient (sl2OddFix ρ) hWinv with hσdef
  have hA := sl2OddFix_quotient_fixed_eq_bot ρ
  have hQnt : Nontrivial (V ⧸ sl2OddFix ρ) := by
    obtain ⟨v, hv⟩ : ∃ v, v ∉ sl2OddFix ρ := by
      by_contra h
      push Not at h
      exact hO (eq_top_iff.mpr fun v _ => h v)
    exact ⟨⟨(sl2OddFix ρ).mkQ v, 0,
      by rw [Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero]; exact hv⟩⟩
  have : Finite (V ⧸ sl2OddFix ρ) :=
    Finite.of_surjective (sl2OddFix ρ).mkQ (sl2OddFix ρ).mkQ_surjective
  have : Module.Finite (ZMod 2) (V ⧸ sl2OddFix ρ) := Module.Finite.of_finite
  obtain ⟨S, hSne, hirr⟩ := exists_irreducible_subrepresentation σ hQnt
  have hSbot : S.toSubmodule ≠ ⊥ := fun h => hSne (Subrepresentation.toSubmodule_injective h)
  have hnt : ∃ g, S.toRepresentation g ≠ 1 :=
    exists_action_ne_one_of_fixed_eq_bot σ S hSbot hA
  have hdimCQ := finrank_quotient_le_add_finrank_fix (A := A) ρ hdimC
  have hoffS := card_le_offender_subrepresentation (A := A) ρ ha hdimCQ S
  obtain ⟨-, -, -, -, -, -, -, -, -, hAc, -⟩ :=
    binary_SL2_internal_offender_natural_module hn hF S.toRepresentation hirr hnt A hA1 hoffS
  rw [hAc, hcardF]

end Additive

theorem finrank_ker_mulVecLin_sub_id_le_one {K : Type} [Field K] {a : Matrix (Fin 2) (Fin 2) K}
    (ha : a ≠ 1) : Module.finrank K (LinearMap.ker (Matrix.mulVecLin a - LinearMap.id)) ≤ 1 := by
  set T : (Fin 2 → K) →ₗ[K] (Fin 2 → K) := Matrix.mulVecLin a - LinearMap.id with hTdef
  have hT : T ≠ 0 := by
    intro h
    apply ha
    have h1 : Matrix.mulVecLin a = Matrix.mulVecLin (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [Matrix.mulVecLin_one]
      exact sub_eq_zero.mp h
    exact Matrix.toLin'.injective h1
  have h1 := LinearMap.finrank_range_add_finrank_ker T
  have h2 : Module.finrank K (Fin 2 → K) = 2 := by simp
  have h3 : 1 ≤ Module.finrank K (LinearMap.range T) := by
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact fun h => hT (LinearMap.range_eq_bot.mp h)
  omega

private theorem card_le_of_forall_mulVec_eq {K : Type} [Field K] [Finite K]
    {a : Matrix (Fin 2) (Fin 2) K} (ha : a ≠ 1) (S : AddSubgroup (Fin 2 → K))
    (hS : ∀ x ∈ S, a.mulVec x = x) : Nat.card S ≤ Nat.card K := by
  have hinj : Function.Injective (fun x : S =>
      (⟨(x : Fin 2 → K), hS x x.2⟩ : {v : Fin 2 → K // a.mulVec v = v})) := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : {v : Fin 2 → K // a.mulVec v = v} => (z : Fin 2 → K)) h)
  exact (Nat.card_le_card_of_injective _ hinj).trans
    (CFSG.Open.StatedAPI.card_mulVec_fixed_le ha)

variable {W : Type} [CommGroup W] [Finite W]

private noncomputable def gomiRep [Module (ZMod 2) (Additive W)] {Γ : Type} [Group Γ]
    (θ : Γ →* MulAut W) : Representation (ZMod 2) Γ (Additive W) where
  toFun γ := AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive (θ γ).toMonoidHom)
  map_one' := by
    ext m
    simp
  map_mul' γ δ := by
    ext m
    simp

private theorem map_props_of_isElemAbelian2 {W : Type*} [CommGroup W] {K : Type*} [Field K]
    {Y : Subgroup (MulAut W)} {A : Subgroup (MulAut W)} (θL : ↥Y ≃* SL(2, K))
    (hAY : A ≤ Y) (hA1 : A ≠ ⊥) (hAel : IsElemAbelian2 A) :
    (∀ g, g ∈ (A.subgroupOf Y).map θL.toMonoidHom ↔
        ((θL.symm g : ↥Y) : MulAut W) ∈ A) ∧
      CFSG.IsElementaryAbelian 2 ((A.subgroupOf Y).map θL.toMonoidHom) ∧
      (A.subgroupOf Y).map θL.toMonoidHom ≠ ⊥ ∧
      Nat.card ((A.subgroupOf Y).map θL.toMonoidHom) = Nat.card A := by
  classical
  set A' : Subgroup SL(2, K) := (A.subgroupOf Y).map θL.toMonoidHom with hA'def
  have hmemA' : ∀ g, g ∈ A' ↔ ((θL.symm g : ↥Y) : MulAut W) ∈ A := by
    intro g
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      exact Subgroup.mem_subgroupOf.mp hy
    · intro hg
      exact ⟨θL.symm g, Subgroup.mem_subgroupOf.mpr hg, by simp⟩
  have hA'comm : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := by
    intro a ha b hb
    apply θL.symm.injective
    apply Subtype.ext
    simpa using hAel.1 _ ((hmemA' a).mp ha) _ ((hmemA' b).mp hb)
  have hA'sq : ∀ a ∈ A', a * a = 1 := by
    intro a ha
    apply θL.symm.injective
    apply Subtype.ext
    simpa [pow_two] using hAel.2 _ ((hmemA' a).mp ha)
  have hA'el : CFSG.IsElementaryAbelian 2 A' :=
    { is_comm := ⟨fun a b => Subtype.ext (hA'comm _ a.2 _ b.2)⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (by simpa [pow_two] using hA'sq _ a.2) }
  obtain ⟨a₀, ha₀A, ha₀1⟩ : ∃ a ∈ A', a ≠ 1 := by
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
    refine ⟨θL ⟨a, hAY a.2⟩, (hmemA' _).mpr (by simp), fun h => ?_⟩
    apply ha1
    have h1 : (⟨a, hAY a.2⟩ : ↥Y) = 1 := by
      rw [← θL.symm_apply_apply ⟨a, hAY a.2⟩, h, map_one]
    have h2 : ((⟨a, hAY a.2⟩ : ↥Y) : MulAut W) = ((1 : ↥Y) : MulAut W) := congrArg Subtype.val h1
    exact Subtype.ext h2
  have hA'1 : A' ≠ ⊥ := fun h => ha₀1 (by rw [h] at ha₀A; exact ha₀A)
  have hA'card : Nat.card A' = Nat.card A := by
    rw [hA'def, Subgroup.card_map_of_injective θL.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY).toEquiv
  exact ⟨hmemA', hA'el, hA'1, hA'card⟩

private theorem sl2Fix_map_eq_fixV {W : Type*} [CommGroup W] {K : Type*} [Field K]
    {Y : Subgroup (MulAut W)} {A : Subgroup (MulAut W)} (θL : ↥Y ≃* SL(2, K))
    (hAY : A ≤ Y) [Module (ZMod 2) (Additive W)] {ρ : Representation (ZMod 2) SL(2, K) (Additive W)}
    (hρ : ∀ g w, ρ g w = Additive.ofMul (((θL.symm g : ↥Y) : MulAut W) (Additive.toMul w)))
    (A' : Subgroup SL(2, K)) (hA'def : A' = (A.subgroupOf Y).map θL.toMonoidHom)
    (hAoff : Nat.card W ≤ Nat.card A * Nat.card (fixV A)) :
    (∀ v : Additive W, v ∈ sl2Fix ρ (A' : Set SL(2, K)) ↔ Additive.toMul v ∈ fixV A) ∧
      Nat.card (sl2Fix ρ (A' : Set SL(2, K))) = Nat.card (fixV A) ∧
      Nat.card (Additive W) ≤
        Nat.card A' * Nat.card (sl2Fix ρ (A' : Set SL(2, K))) := by
  classical
  have hmemA' : ∀ g, g ∈ A' ↔ ((θL.symm g : ↥Y) : MulAut W) ∈ A := by
    rw [hA'def]
    intro g
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      exact Subgroup.mem_subgroupOf.mp hy
    · intro hg
      exact ⟨θL.symm g, Subgroup.mem_subgroupOf.mpr hg, by simp⟩
  have hfix : ∀ v : Additive W,
      v ∈ sl2Fix ρ (A' : Set SL(2, K)) ↔ Additive.toMul v ∈ fixV A := by
    intro v
    constructor
    · intro hv a ha
      have h1 := hv (θL ⟨a, hAY ha⟩) ((hmemA' _).mpr (by simpa using ha))
      rw [hρ] at h1
      have h2 := congrArg Additive.toMul h1
      simpa using h2
    · intro hv g hg
      rw [hρ]
      have h1 := hv _ ((hmemA' g).mp hg)
      rw [h1]
      rfl
  have hfixcard : Nat.card (sl2Fix ρ (A' : Set SL(2, K))) = Nat.card (fixV A) :=
    Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun v => hfix v)
  have hVW : Nat.card (Additive W) = Nat.card W := Nat.card_congr Additive.toMul
  refine ⟨hfix, hfixcard, ?_⟩
  have hA'card : Nat.card A' = Nat.card A := by
    rw [hA'def, Subgroup.card_map_of_injective θL.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY).toEquiv
  rw [hVW, hA'card, hfixcard]
  exact hAoff

private theorem core_exists_order_three {K : Type*} [Field K] [Fintype K] [CharP K 2]
    {m : ℕ} (hK : Nat.card K = 2 ^ m) :
    ∃ M : SL(2, K), orderOf M = 3 ∧ M ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨M, hM⟩ : ∃ M : SL(2, K), orderOf M = 3 := by
    refine exists_prime_orderOf_dvd_card' 3 ?_
    rw [CFSG.GorensteinWalter.sl2_card_formula K, hK]
    apply Dvd.dvd.mul_left
    have h4 : (2 ^ m) ^ 2 = 4 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h4]
    have hmod : 4 ^ m ≡ 1 [MOD 3] := by simpa using (show 4 ≡ 1 [MOD 3] by decide).pow m
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp hmod.symm
  exact ⟨M, hM, fun h => by rw [h, orderOf_one] at hM; norm_num at hM⟩

private theorem core_sl2OddFix_ne_top {W : Type*} [CommGroup W] {K : Type*} [Field K]
    {Y : Subgroup (MulAut W)} [Module (ZMod 2) (Additive W)]
    (θL : ↥Y ≃* SL(2, K))
    {ρ : Representation (ZMod 2) SL(2, K) (Additive W)}
    (hρ : ∀ g w, ρ g w = Additive.ofMul (((θL.symm g : ↥Y) : MulAut W) (Additive.toMul w)))
    {M : SL(2, K)} (hM : orderOf M = 3) (hM1 : M ≠ 1) :
    sl2OddFix ρ ≠ ⊤ := by
  intro htop
  apply hM1
  have hModd : Odd (orderOf M) := by rw [hM]; decide
  have h1 : ((θL.symm M : ↥Y) : MulAut W) = 1 := by
    ext w
    have hw : Additive.ofMul w ∈ sl2OddFix ρ := by
      rw [htop]
      exact Submodule.mem_top
    have h2 := (mem_sl2OddFix ρ).mp hw M hModd
    rw [hρ] at h2
    simpa using congrArg Additive.toMul h2
  have h3 : θL.symm M = 1 := Subtype.ext h1
  rw [← θL.apply_symm_apply M, h3, map_one]

private theorem core_natural_exists {W : Type*} [CommGroup W] [Finite W] {K : Type*}
    [Field K] [Fintype K] [Module (ZMod 2) (Additive W)] {m : ℕ}
    (hK : Nat.card K = 2 ^ m)
    {ρ : Representation (ZMod 2) SL(2, K) (Additive W)} (hO : sl2OddFix ρ ≠ ⊤)
    (A' : Subgroup SL(2, K)) (hA'p : IsPGroup 2 A')
    (hA'K : Nat.card A' = Nat.card K)
    (hoff : Nat.card (Additive W) ≤ Nat.card A' *
      Nat.card (sl2Fix ρ (A' : Set SL(2, K)))) :
    ∃ φ : Additive W →+ (Fin 2 → K), Function.Surjective φ ∧
      (∀ g v, φ (ρ g v) = (g : Matrix (Fin 2) (Fin 2) K).mulVec (φ v)) ∧
      ∀ v, φ v = 0 ↔ v ∈ sl2OddFix ρ := by
  let _ : Finite (Additive W) := inferInstance
  have hKc : Fintype.card K = 2 ^ m := by rw [Fintype.card_eq_nat_card, hK]
  rcases natural_of_sl2Fix ρ hKc A' hA'p hA'K (by rw [← hA'K]; exact hoff) with
      htop | ⟨φ, hφs, hφe, hφk⟩
  · exact absurd htop hO
  · exact ⟨φ, hφs, hφe, hφk⟩

private theorem core_quotient_card {W : Type*} [CommGroup W] [Finite W] {K : Type*}
    [Field K] [Fintype K] [Module (ZMod 2) (Additive W)]
    (ρ : Representation (ZMod 2) SL(2, K) (Additive W)) {m : ℕ}
    (hK : Nat.card K = 2 ^ m) (φ : Additive W →+ (Fin 2 → K))
    (hφs : Function.Surjective φ) (hφk : ∀ v, φ v = 0 ↔ v ∈ sl2OddFix ρ) :
    Nat.card (Additive W ⧸ sl2OddFix ρ) = Nat.card K ^ 2 ∧
      Module.finrank (ZMod 2) (Additive W ⧸ sl2OddFix ρ) = 2 * m := by
  classical
  set U := sl2OddFix ρ with hUdef
  set χ : Additive W ⧸ U → (Fin 2 → K) := fun q => φ (Quotient.out q) with hχdef
  have hχmk : ∀ v, χ (U.mkQ v) = φ v := by
    intro v
    have h1 : U.mkQ (Quotient.out (U.mkQ v)) = U.mkQ v := Quotient.out_eq _
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h1
    have h2 : φ (Quotient.out (U.mkQ v) - v) = 0 := (hφk _).mpr h1
    rw [map_sub, sub_eq_zero] at h2
    exact h2
  have hχinj : Function.Injective χ := by
    intro q q' h
    obtain ⟨v, rfl⟩ := U.mkQ_surjective q
    obtain ⟨v', rfl⟩ := U.mkQ_surjective q'
    rw [hχmk, hχmk] at h
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact (hφk _).mp (by rw [map_sub, h, sub_self])
  have hχsurj : Function.Surjective χ := by
    intro x
    obtain ⟨v, rfl⟩ := hφs x
    exact ⟨U.mkQ v, hχmk v⟩
  have hcardQ : Nat.card (Additive W ⧸ U) = Nat.card K ^ 2 := by
    rw [Nat.card_eq_of_bijective χ ⟨hχinj, hχsurj⟩, Nat.card_fun, Nat.card_fin]
  refine ⟨hcardQ, ?_⟩
  let _ : Finite (Additive W ⧸ U) := Finite.of_surjective U.mkQ U.mkQ_surjective
  let _ : Module.Finite (ZMod 2) (Additive W ⧸ U) := Module.Finite.of_finite
  have h1 : Nat.card (Additive W ⧸ U) =
      2 ^ Module.finrank (ZMod 2) (Additive W ⧸ U) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hcardQ, hK, ← pow_mul, mul_comm] at h1
  exact (Nat.pow_right_injective (le_refl 2) h1).symm

private theorem finrank_le_add_finrank_fix_of_card_le {W : Type*} [CommGroup W] [Finite W]
    {K : Type*} [Field K] [Fintype K] [Module (ZMod 2) (Additive W)] {m : ℕ}
    (hK : Nat.card K = 2 ^ m)
    {ρ : Representation (ZMod 2) SL(2, K) (Additive W)} {A' : Subgroup SL(2, K)}
    (hA'K : Nat.card A' = Nat.card K)
    (hoff : Nat.card (Additive W) ≤ Nat.card A' *
      Nat.card (sl2Fix ρ (A' : Set SL(2, K)))) :
    Module.finrank (ZMod 2) (Additive W) ≤ m +
      Module.finrank (ZMod 2) (sl2Fix ρ (A' : Set SL(2, K))) := by
  let _ : Module.Finite (ZMod 2) (Additive W) := Module.Finite.of_finite
  let _ : Module.Finite (ZMod 2) ↥(sl2Fix ρ (A' : Set SL(2, K))) := Module.Finite.of_finite
  have hC : Nat.card (sl2Fix ρ (A' : Set SL(2, K))) =
      2 ^ Module.finrank (ZMod 2) (sl2Fix ρ (A' : Set SL(2, K))) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hV : Nat.card (Additive W) = 2 ^ Module.finrank (ZMod 2) (Additive W) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h1 : Nat.card (Additive W) ≤
      2 ^ (m + Module.finrank (ZMod 2) (sl2Fix ρ (A' : Set SL(2, K)))) := by
    rw [pow_add, ← hK, ← hC, ← hA'K]
    exact hoff
  rw [hV] at h1
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1

private theorem core_chi_injective {W : Type*} [CommGroup W] {K : Type*} [Field K] [Fintype K]
    [Module (ZMod 2) (Additive W)]
    {ρ : Representation (ZMod 2) SL(2, K) (Additive W)}
    (φ : Additive W →+ (Fin 2 → K))
    (hφk : ∀ v, φ v = 0 ↔ v ∈ sl2OddFix ρ) :
    (∀ v, (fun q : Additive W ⧸ sl2OddFix ρ => φ (Quotient.out q))
        ((sl2OddFix ρ).mkQ v) = φ v) ∧
      Function.Injective (fun q : Additive W ⧸ sl2OddFix ρ => φ (Quotient.out q)) := by
  classical
  set U := sl2OddFix ρ with hUdef
  have hχmk : ∀ v, (fun q : Additive W ⧸ U => φ (Quotient.out q)) (U.mkQ v) = φ v := by
    intro v
    have h1 : U.mkQ (Quotient.out (U.mkQ v)) = U.mkQ v := Quotient.out_eq _
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h1
    have h2 : φ (Quotient.out (U.mkQ v) - v) = 0 := (hφk _).mpr h1
    rw [map_sub, sub_eq_zero] at h2
    exact h2
  refine ⟨hχmk, ?_⟩
  intro q q' h
  obtain ⟨v, rfl⟩ := U.mkQ_surjective q
  obtain ⟨v', rfl⟩ := U.mkQ_surjective q'
  rw [hχmk, hχmk] at h
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  exact (hφk _).mp (by rw [map_sub, h, sub_self])

private theorem core_card_fixCQ_le {W : Type*} [CommGroup W] [Finite W] {K : Type}
    [Field K] [Fintype K] [Module (ZMod 2) (Additive W)]
    {ρ : Representation (ZMod 2) SL(2, K) (Additive W)}
    {A' : Subgroup SL(2, K)} (a₀ : SL(2, K)) (ha₀ : a₀ ∈ A')
    (φ : Additive W →+ (Fin 2 → K))
    (hφk : ∀ v, φ v = 0 ↔ v ∈ sl2OddFix ρ)
    (A₀ : Matrix (Fin 2) (Fin 2) K) (hA₀1 : A₀ ≠ 1)
    (hA₀ : ∀ v, A₀.mulVec (φ v) = φ (ρ a₀ v)) :
    Nat.card (sl2Fix (ρ.quotient (sl2OddFix ρ)
      (fun g _ hv => apply_mem_sl2OddFix ρ g hv)) (A' : Set SL(2, K))) ≤ Nat.card K := by
  classical
  set U := sl2OddFix ρ with hUdef
  set σ := ρ.quotient U (fun g _ hv => apply_mem_sl2OddFix ρ g hv) with hσdef
  have hσ : ∀ g v, σ g (U.mkQ v) = U.mkQ (ρ g v) := fun g v => rfl
  set CQ := sl2Fix σ (A' : Set SL(2, K)) with hCQdef
  have h1 : Nat.card CQ ≤ Nat.card K := by
    let χ : Additive W ⧸ U → (Fin 2 → K) := fun q => φ (Quotient.out q)
    obtain ⟨hχmk', hχinj⟩ := core_chi_injective φ hφk
    have hχmk'' : ∀ v, χ (U.mkQ v) = φ v := hχmk'
    let S : AddSubgroup (Fin 2 → K) :=
      { carrier := {x | A₀.mulVec x = x}
        add_mem' := fun {x y} hx hy => by
          simp only [Set.mem_setOf_eq, Matrix.mulVec_add] at hx hy ⊢
          rw [hx, hy]
        zero_mem' := by simp
        neg_mem' := fun {x} hx => by
          simp only [Set.mem_setOf_eq, Matrix.mulVec_neg] at hx ⊢
          rw [hx] }
    have hinj : Function.Injective (fun c : CQ => (⟨χ c, by
        obtain ⟨v, hv⟩ := U.mkQ_surjective (c : Additive W ⧸ U)
        show A₀.mulVec (χ c) = χ c
        have h2 := c.2 a₀ ha₀
        rw [← hv, hσ, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h2
        rw [← hv, hχmk'', hA₀]
        have h3 : φ (ρ a₀ v - v) = 0 := (hφk _).mpr h2
        rw [map_sub, sub_eq_zero] at h3
        exact h3⟩ : S)) := by
      intro c c' h
      exact Subtype.ext (hχinj (congrArg Subtype.val h))
    exact (Nat.card_le_card_of_injective _ hinj).trans
      (card_le_of_forall_mulVec_eq hA₀1 S fun x hx => hx)
  exact h1

private theorem core_finrank_fixCQ {W : Type*} [CommGroup W] [Finite W] {K : Type}
    [Field K] [Fintype K] [Module (ZMod 2) (Additive W)] {m : ℕ}
    (hK : Nat.card K = 2 ^ m) {ρ : Representation (ZMod 2) SL(2, K) (Additive W)}
    {A' : Subgroup SL(2, K)} (a₀ : SL(2, K)) (ha₀ : a₀ ∈ A')
    (φ : Additive W →+ (Fin 2 → K))
    (hφk : ∀ v, φ v = 0 ↔ v ∈ sl2OddFix ρ)
    (A₀ : Matrix (Fin 2) (Fin 2) K) (hA₀1 : A₀ ≠ 1)
    (hA₀ : ∀ v, A₀.mulVec (φ v) = φ (ρ a₀ v)) :
    Module.finrank (ZMod 2) (sl2Fix (ρ.quotient (sl2OddFix ρ)
      (fun g _ hv => apply_mem_sl2OddFix ρ g hv)) (A' : Set SL(2, K))) ≤ m := by
  have hcard := core_card_fixCQ_le (A' := A') a₀ ha₀ φ hφk A₀ hA₀1 hA₀
  have hCQ : Nat.card (sl2Fix (ρ.quotient (sl2OddFix ρ)
      (fun g _ hv => apply_mem_sl2OddFix ρ g hv)) (A' : Set SL(2, K))) =
      2 ^ Module.finrank (ZMod 2) (sl2Fix (ρ.quotient (sl2OddFix ρ)
        (fun g _ hv => apply_mem_sl2OddFix ρ g hv)) (A' : Set SL(2, K))) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hCQ, hK] at hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcard

private theorem core_sl2OddFix_le_fix {W : Type*} [CommGroup W] [Finite W] {K : Type}
    [Field K] [Fintype K] [Module (ZMod 2) (Additive W)] {m : ℕ}
    (hK : Nat.card K = 2 ^ m) {ρ : Representation (ZMod 2) SL(2, K) (Additive W)}
    {A' : Subgroup SL(2, K)} (a₀ : SL(2, K)) (ha₀ : a₀ ∈ A')
    (φ : Additive W →+ (Fin 2 → K))
    (hφk : ∀ v, φ v = 0 ↔ v ∈ sl2OddFix ρ)
    (A₀ : Matrix (Fin 2) (Fin 2) K) (hA₀1 : A₀ ≠ 1)
    (hA₀ : ∀ v, A₀.mulVec (φ v) = φ (ρ a₀ v))
    (hdimC : Module.finrank (ZMod 2) (Additive W) ≤ m +
      Module.finrank (ZMod 2) (sl2Fix ρ (A' : Set SL(2, K))))
    (hdimQ : Module.finrank (ZMod 2) (Additive W ⧸ sl2OddFix ρ) = 2 * m) :
    sl2OddFix ρ ≤ sl2Fix ρ (A' : Set SL(2, K)) ∧
      Module.finrank (ZMod 2) (sl2Fix ρ (A' : Set SL(2, K))) ≤
        m + Module.finrank (ZMod 2) (sl2OddFix ρ) := by
  classical
  set U := sl2OddFix ρ with hUdef
  set C := sl2Fix ρ (A' : Set SL(2, K)) with hCdef
  set σ := ρ.quotient U (fun g _ hv => apply_mem_sl2OddFix ρ g hv) with hσdef
  have hσ : ∀ g v, σ g (U.mkQ v) = U.mkQ (ρ g v) := fun g v => rfl
  set CQ := sl2Fix σ (A' : Set SL(2, K)) with hCQdef
  have hdimCQ : Module.finrank (ZMod 2) ↥CQ ≤ m := by
    rw [hCQdef]
    exact core_finrank_fixCQ (A' := A') hK a₀ ha₀ φ hφk A₀ hA₀1 hA₀
  have hquot := Submodule.finrank_quotient_add_finrank U
  have hdimQ' : Module.finrank (ZMod 2) (Additive W ⧸ U) = 2 * m := by
    rw [hUdef]
    exact hdimQ
  have hdimC' : Module.finrank (ZMod 2) (Additive W) ≤ m + Module.finrank (ZMod 2) ↥C := hdimC
  let f : C →ₗ[ZMod 2] Additive W ⧸ U := U.mkQ.comp C.subtype
  have hrange : LinearMap.range f ≤ CQ := by
    rintro _ ⟨c, rfl⟩ g hg
    show σ g (U.mkQ c) = U.mkQ c
    rw [hσ, c.2 g hg]
  have hker : (LinearMap.ker f).map C.subtype ≤ C ⊓ U := by
    rintro _ ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hc
    refine ⟨c.2, ?_⟩
    simpa [f] using hc
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  have hr1 := Submodule.finrank_mono hrange
  have hk1 := Submodule.finrank_mono hker
  rw [Submodule.finrank_map_subtype_eq] at hk1
  have h1 : C ⊓ U = U :=
    Submodule.eq_of_le_of_finrank_le inf_le_right (by omega)
  have hCdim : Module.finrank (ZMod 2) ↥C ≤ m + Module.finrank (ZMod 2) ↥U := by
    rw [h1] at hk1
    omega
  refine ⟨?_, hCdim⟩
  rw [← h1]; exact inf_le_left

private theorem eq_top_of_order_three_of_eq_one {K : Type} [Field K] [Fintype K]
    {m : ℕ} (hK : Nat.card K = 2 ^ m) (hm1 : m = 1)
    {N : Subgroup SL(2, K)} {M : SL(2, K)} (hM : orderOf M = 3) (hMN : M ∈ N)
    {A' : Subgroup SL(2, K)} (hA'N : A' ≤ N) (hA'K : Nat.card A' = Nat.card K) :
    N = ⊤ := by
  subst hm1
  have h6 : Nat.card SL(2, K) = 6 := by
    rw [CFSG.GorensteinWalter.sl2_card_formula K, hK]
    norm_num
  apply Subgroup.eq_top_of_card_eq
  have h3 : 3 ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨M, hMN⟩ : ↥N)
    rwa [Subgroup.orderOf_mk, hM] at this
  have h2 : 2 ∣ Nat.card N := by
    have := Subgroup.card_dvd_of_le hA'N
    rwa [hA'K, hK, pow_one] at this
  have h6' : 6 ∣ Nat.card N := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
  have hle : Nat.card N ≤ 6 := h6 ▸ Subgroup.card_le_card_group N
  have hpos : 0 < Nat.card N := Nat.card_pos
  rw [h6]
  obtain ⟨k, hk⟩ := h6'
  rcases k with _ | _ | k
  · omega
  · omega
  · omega

private theorem eq_top_of_order_three_of_two_le {K : Type} [Field K] [Fintype K] [CharP K 2]
    {N : Subgroup SL(2, K)} (hNn : N.Normal) {M : SL(2, K)}
    (hM1 : M ≠ 1) (hMN : M ∈ N) {m : ℕ} (hK : Nat.card K = 2 ^ m) (hm2 : 2 ≤ m) :
    N = ⊤ := by
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  have := CFSG.LocalAnalysis.RankThreeUC.S15.K421SpSLProof.isSimpleGroup_sl2_charTwo h4
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact absurd (h ▸ hMN : M ∈ (⊥ : Subgroup SL(2, K))) (by simpa using hM1)
  · exact h

private theorem core_sl2_stabilizes {W : Type*} [CommGroup W] [Finite W] {K : Type}
    [Field K] [Fintype K] [CharP K 2] [Module (ZMod 2) (Additive W)] {m : ℕ}
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m)
    {ρ : Representation (ZMod 2) SL(2, K) (Additive W)} {A' : Subgroup SL(2, K)}
    (hUC : sl2OddFix ρ ≤ sl2Fix ρ (A' : Set SL(2, K)))
    {M : SL(2, K)} (hM : orderOf M = 3) (hM1 : M ≠ 1)
    (hA'K : Nat.card A' = Nat.card K) :
    ∀ g : SL(2, K), ∀ u ∈ sl2OddFix ρ, ρ g u = u := by
  classical
  have hModd : Odd (orderOf M) := by rw [hM]; decide
  let N : Subgroup SL(2, K) :=
    { carrier := {g | ∀ u ∈ sl2OddFix ρ, ρ g u = u}
      one_mem' := fun u _ => by simp
      mul_mem' := fun {g h} hg hh u hu => by
        rw [map_mul, Module.End.mul_apply, hh u hu, hg u hu]
      inv_mem' := fun {g} hg u hu => by
        have h1 : ρ g (ρ g⁻¹ u) = ρ g⁻¹ u := hg _ (apply_mem_sl2OddFix ρ g⁻¹ hu)
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_apply] at h1
        exact h1.symm }
  have hNn : N.Normal := by
    refine ⟨fun n hn h u hu => ?_⟩
    have h1 := hn (ρ h⁻¹ u) (apply_mem_sl2OddFix ρ h⁻¹ hu)
    show ρ (h * n * h⁻¹) u = u
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h1,
      ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hMN : M ∈ N := fun u hu => (mem_sl2OddFix ρ).mp hu M hModd
  have hA'N : A' ≤ N := fun g hg u hu => hUC hu g hg
  have hNtop : N = ⊤ := by
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · have hm1 : m = 1 := by omega
      exact eq_top_of_order_three_of_eq_one hK hm1 hM hMN hA'N hA'K
    · exact eq_top_of_order_three_of_two_le hNn hM1 hMN hK hm2
  intro g u hu
  have : g ∈ N := hNtop ▸ Subgroup.mem_top g
  exact this u hu

private theorem mem_sl2OddFix_iff_mem_fixV {W : Type*} [CommGroup W] {K : Type} [Field K]
    [Fintype K] [Module (ZMod 2) (Additive W)] {Y : Subgroup (MulAut W)}
    (θL : ↥Y ≃* SL(2, K)) {ρ : Representation (ZMod 2) SL(2, K) (Additive W)}
    (hρ : ∀ g w, ρ g w = Additive.ofMul (((θL.symm g : ↥Y) : MulAut W) (Additive.toMul w)))
    (hstab : ∀ g : SL(2, K), ∀ u ∈ sl2OddFix ρ, ρ g u = u) :
    ∀ v : Additive W, v ∈ sl2OddFix ρ ↔ Additive.toMul v ∈ fixV Y := by
  intro v
  constructor
  · intro hv y hy
    have h1 := hstab (θL ⟨y, hy⟩) v hv
    rw [hρ, θL.symm_apply_apply] at h1
    simpa using congrArg Additive.toMul h1
  · intro hv
    refine (mem_sl2OddFix ρ).mpr fun g _ => ?_
    rw [hρ, hv _ (θL.symm g).2]
    rfl

private theorem core_natural_module {W : Type*} [CommGroup W] [Finite W] {K : Type}
    [Field K] [Fintype K] [Module (ZMod 2) (Additive W)] {Y : Subgroup (MulAut W)}
    {m : ℕ} (hK : Nat.card K = 2 ^ m)
    (e : ↥Y ≃* ↥(CFSG.Open.StatedSL 2 K)) (θL : ↥Y ≃* SL(2, K))
    (hθL : θL = e.trans (specialLinearGroupEquivStatedSL 2 K).symm)
    {ρ : Representation (ZMod 2) SL(2, K) (Additive W)}
    (hρ : ∀ g w, ρ g w = Additive.ofMul (((θL.symm g : ↥Y) : MulAut W) (Additive.toMul w)))
    (φ : Additive W →+ (Fin 2 → K)) (hφs : Function.Surjective φ)
    (hφe : ∀ g v, φ (ρ g v) = (g : Matrix (Fin 2) (Fin 2) K).mulVec (φ v))
    (hφk : ∀ v, φ v = 0 ↔ v ∈ sl2OddFix ρ)
    (hUfix : ∀ v, v ∈ sl2OddFix ρ ↔ Additive.toMul v ∈ fixV Y) :
    BinaryNaturalSL Y ⊤ (fixV Y) 2 m := by
  classical
  let π : ↥(CFSG.Open.StatedSL 2 K) →* ↥Y := e.symm.toMonoidHom
  have hπ : Function.Surjective π := e.symm.surjective
  have hπθ : ∀ γ : ↥(CFSG.Open.StatedSL 2 K), (π γ : ↥Y) =
      θL.symm ((specialLinearGroupEquivStatedSL 2 K).symm γ) := by
    intro γ
    rw [hθL, MulEquiv.symm_trans_apply, MulEquiv.symm_symm, MulEquiv.apply_symm_apply]
    rfl
  let fW : ↥(⊤ : Subgroup W) →* Multiplicative (Fin 2 → K) :=
    { toFun := fun u => Multiplicative.ofAdd (φ (Additive.ofMul (u : W)))
      map_one' := by simp
      map_mul' := fun u v => by simp [← ofAdd_add] }
  refine ⟨K, inferInstance, inferInstance, hK, π,
    CFSG.Quasithin.G64.realizesVia_nat_of hπ le_top (fun _ _ _ => trivial)
      (fun h z hz y hy => by rw [hz _ h.2]; exact hz y hy) fW ?_ ?_ ?_⟩
  · intro x
    obtain ⟨v, hv⟩ := hφs (Multiplicative.toAdd x)
    exact ⟨⟨Additive.toMul v, trivial⟩, by simp [fW, hv]⟩
  · intro u
    show Multiplicative.ofAdd (φ (Additive.ofMul (u : W))) = 1 ↔ (u : W) ∈ fixV Y
    rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, hφk, hUfix]
    rfl
  · intro γ u hu
    show Multiplicative.ofAdd (φ (Additive.ofMul (((π γ : ↥Y) : MulAut W) (u : W)))) =
      natAct (CFSG.Open.StatedSL 2 K) γ (Multiplicative.ofAdd (φ (Additive.ofMul (u : W))))
    have h1 : Additive.ofMul (((π γ : ↥Y) : MulAut W) (u : W)) =
        ρ ((specialLinearGroupEquivStatedSL 2 K).symm γ) (Additive.ofMul (u : W)) := by
      rw [hρ, ← hπθ]
      rfl
    rw [h1, hφe]
    simp only [natAct, toAdd_ofAdd]
    congr 2
    rw [← specialLinearGroupEquivStatedSL_coe 2 K, MulEquiv.apply_symm_apply]

private theorem core_card_W {W : Type*} [CommGroup W] [Finite W] {K : Type} [Field K]
    [Fintype K]
    [Module (ZMod 2) (Additive W)] {m : ℕ} {A : Subgroup (MulAut W)}
    {ρ : Representation (ZMod 2) SL(2, K) (Additive W)} {A' : Subgroup SL(2, K)}
    (hfixcard : Nat.card (sl2Fix ρ (A' : Set SL(2, K))) = Nat.card (fixV A))
    (hdimC : Module.finrank (ZMod 2) (Additive W) ≤ m +
      Module.finrank (ZMod 2) (sl2Fix ρ (A' : Set SL(2, K))))
    (hdimQ : Module.finrank (ZMod 2) (Additive W ⧸ sl2OddFix ρ) = 2 * m)
    (hCdim : Module.finrank (ZMod 2) (sl2Fix ρ (A' : Set SL(2, K))) ≤
      m + Module.finrank (ZMod 2) (sl2OddFix ρ)) :
    Nat.card W = 2 ^ m * Nat.card (fixV A) := by
  let _ : Module.Finite (ZMod 2) (Additive W) := Module.Finite.of_finite
  let _ : Module.Finite (ZMod 2) ↥(sl2Fix ρ (A' : Set SL(2, K))) := Module.Finite.of_finite
  have hquot := Submodule.finrank_quotient_add_finrank (sl2OddFix ρ)
  have h1 : Module.finrank (ZMod 2) (Additive W) =
      m + Module.finrank (ZMod 2) (sl2Fix ρ (A' : Set SL(2, K))) := by omega
  have hV : Nat.card (Additive W) = 2 ^ Module.finrank (ZMod 2) (Additive W) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hC : Nat.card (sl2Fix ρ (A' : Set SL(2, K))) =
      2 ^ Module.finrank (ZMod 2) (sl2Fix ρ (A' : Set SL(2, K))) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hVW : Nat.card (Additive W) = Nat.card W := Nat.card_congr Additive.toMul
  rw [h1, pow_add, ← hC, hVW, hfixcard] at hV
  exact hV

private theorem gomiFact35_core (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} {m : ℕ}
    (hm : 1 ≤ m) (hY : IsSLn ↥Y 2 m) {A : Subgroup (MulAut W)} (hA : A ∈ gomiOset Y) :
    BinaryNaturalSL Y ⊤ (fixV Y) 2 m ∧ Nat.card A = 2 ^ m ∧
      Nat.card W = 2 ^ m * Nat.card (fixV A) := by
  classical
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hY
  have : Fintype K := Fintype.ofFinite K
  have hKc : Fintype.card K = 2 ^ m := by rw [Fintype.card_eq_nat_card, hK]
  have : CharP K 2 := charP_two_of_card_eq hKc
  let _ : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule (n := 2) fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, hW]
    rfl
  have : Module.Finite (ZMod 2) (Additive W) := Module.Finite.of_finite
  set θL : ↥Y ≃* SL(2, K) := e.trans (specialLinearGroupEquivStatedSL 2 K).symm with hθL
  set act : SL(2, K) →* MulAut W := Y.subtype.comp θL.symm.toMonoidHom with hact
  set ρ : Representation (ZMod 2) SL(2, K) (Additive W) := gomiRep act with hρdef
  have hρ : ∀ g w, ρ g w = Additive.ofMul (((θL.symm g : ↥Y) : MulAut W) (Additive.toMul w)) :=
    fun _ _ => rfl
  obtain ⟨hAY, hA1, hAel, hAoff⟩ := hA
  set A' : Subgroup SL(2, K) := (A.subgroupOf Y).map θL.toMonoidHom with hA'def
  obtain ⟨hmemA', hA'el, hA'1, hA'card⟩ := by
    have h := map_props_of_isElemAbelian2 θL hAY hA1 hAel
    rwa [← hA'def] at h
  obtain ⟨hfix, hfixcard, hoff⟩ := sl2Fix_map_eq_fixV θL hAY hρ A' hA'def hAoff
  obtain ⟨M, hM, hM1⟩ := core_exists_order_three hK
  have hO := core_sl2OddFix_ne_top θL hρ hM hM1
  have hA'K : Nat.card A' = Nat.card K := card_eq_of_offender_sl2 hKc ρ hO A' hA'1 hoff
  have hA'p : IsPGroup 2 A' := IsPGroup.iff_card.mpr ⟨m, by rw [hA'K, hK]⟩
  obtain ⟨φ, hφs, hφe, hφk⟩ := core_natural_exists hK hO A' hA'p hA'K hoff
  have hdimC := finrank_le_add_finrank_fix_of_card_le hK hA'K hoff
  obtain ⟨hcardQ, hdimQ⟩ := core_quotient_card ρ hK φ hφs hφk
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA'1
  let a₀ : SL(2, K) := a
  have ha₀ : a₀ ∈ A' := a.2
  have ha₀1 : a₀ ≠ 1 := fun h => ha (Subtype.ext h)
  let A₀ : Matrix (Fin 2) (Fin 2) K := (a₀ : Matrix (Fin 2) (Fin 2) K)
  have hA₀1 : A₀ ≠ 1 := fun h => ha₀1 (Subtype.ext h)
  have hA₀ : ∀ v, A₀.mulVec (φ v) = φ (ρ a₀ v) := fun v => (hφe a₀ v).symm
  obtain ⟨hUC, hCdim⟩ :=
    core_sl2OddFix_le_fix hK a₀ ha₀ φ hφk A₀ hA₀1 hA₀ hdimC hdimQ
  have hstab := core_sl2_stabilizes hm hK hUC hM hM1 hA'K
  have hUfix := mem_sl2OddFix_iff_mem_fixV θL hρ hstab
  refine ⟨?_, by rw [← hA'card, hA'K, hK], ?_⟩
  · exact core_natural_module hK e θL hθL hρ φ hφs hφe hφk hUfix
  · exact core_card_W hfixcard hdimC hdimQ hCdim

theorem gomiFact35_of_two_le (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} {m : ℕ}
    (hm : 2 ≤ m) (hY : IsSLn ↥Y 2 m) {A : Subgroup (MulAut W)} (hA : A ∈ gomiOset Y) :
    BinaryNaturalSL Y ⊤ (fixV Y) 2 m ∧ Nat.card A = 2 ^ m ∧
      Nat.card W = 2 ^ m * Nat.card (fixV A) :=
  gomiFact35_core hW (by omega) hY hA

theorem gomiFact35_one (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} (hY : IsSLn ↥Y 2 1)
    {A : Subgroup (MulAut W)} (hA : A ∈ gomiOset Y) :
    BinaryNaturalSL Y ⊤ (fixV Y) 2 1 ∧ Nat.card A = 2 ^ 1 ∧
      Nat.card W = 2 ^ 1 * Nat.card (fixV A) :=
  gomiFact35_core hW le_rfl hY hA

theorem gomiFact35_holds : GomiFact35 := by
  intro W _ _ hW Y m hm hY A hA
  rcases Nat.lt_or_ge m 2 with h | h
  · obtain rfl : m = 1 := by omega
    exact gomiFact35_one hW hY hA
  · exact gomiFact35_of_two_le hW h hY hA

end CFSG.GroupTheory

end
