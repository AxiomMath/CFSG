module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannUnit
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftMaxSL2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOffenderNatClass

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.SL2Modules CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section Counting

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

theorem card_range_fixed_quot [Finite V] (I P : Submodule k V) (Z : Submodule k ↥I)
    (hZP : ∀ w ∈ Z, (w : V) ∈ P) (hsup : I ⊔ P = ⊤) (a : ℕ) (hapos : 0 < a)
    (hw : a * Nat.card ↥P = Nat.card V) (hW : Nat.card (↥I ⧸ Z) = a * a) :
    Nat.card ↥(LinearMap.range (Z.mkQ ∘ₗ Submodule.inclusion (inf_le_left : I ⊓ P ≤ I))) = a := by
  set f : ↥(I ⊓ P) →ₗ[k] (↥I ⧸ Z) := Z.mkQ ∘ₗ Submodule.inclusion (inf_le_left : I ⊓ P ≤ I)
    with hf
  have hfcard := natCard_eq_ker_mul_range f
  have hkerZ : Nat.card ↥(LinearMap.ker f) = Nat.card ↥Z := by
    refine Nat.card_congr
      { toFun := fun x => ⟨Submodule.inclusion (inf_le_left : I ⊓ P ≤ I) x.1, by
          have h0 : Z.mkQ (Submodule.inclusion (inf_le_left : I ⊓ P ≤ I) x.1) = 0 :=
            LinearMap.mem_ker.1 x.2
          exact (Submodule.Quotient.mk_eq_zero Z).1 h0⟩
        invFun := fun z => ⟨⟨(z.1 : V), ⟨z.1.2, hZP z.1 z.2⟩⟩, by
          rw [LinearMap.mem_ker]
          exact (Submodule.Quotient.mk_eq_zero Z).2 z.2⟩
        left_inv := fun x => by
          apply Subtype.ext
          apply Subtype.ext
          rfl
        right_inv := fun z => by
          apply Subtype.ext
          apply Subtype.ext
          rfl }
  have hII : Nat.card ↥I = Nat.card ↥Z * (a * a) := by
    have := Submodule.card_eq_card_quotient_mul_card Z
    rw [← hW]
    exact this
  have hsupcard := natCard_sup_mul_natCard_inf I P
  rw [hsup, Nat.card_congr (Submodule.topEquiv (R := k) (M := V)).toEquiv] at hsupcard
  have hPpos : 0 < Nat.card ↥P := Nat.card_pos
  have hm : a * Nat.card ↥(I ⊓ P) = Nat.card ↥I := by
    have h1 : a * Nat.card ↥P * Nat.card ↥(I ⊓ P) = Nat.card ↥I * Nat.card ↥P := by
      rw [hw]
      exact hsupcard
    have h2 : (a * Nat.card ↥(I ⊓ P)) * Nat.card ↥P = Nat.card ↥I * Nat.card ↥P := by
      rw [← h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hPpos h2
  have hZpos : 0 < Nat.card ↥Z := Nat.card_pos
  have hm' : Nat.card ↥(I ⊓ P) = a * Nat.card ↥Z := by
    have h3 : a * Nat.card ↥(I ⊓ P) = a * (a * Nat.card ↥Z) := by
      rw [hm, hII]; ring
    exact Nat.eq_of_mul_eq_mul_left hapos h3
  rw [hkerZ, hm'] at hfcard
  have : Nat.card ↥Z * Nat.card ↥(LinearMap.range f) = Nat.card ↥Z * a := by
    rw [← hfcard]; ring
  exact Nat.eq_of_mul_eq_mul_left hZpos this

end Counting

section Natural

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}

omit [Finite V] [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))] in
theorem natural_coords (hnat : NaturalFamily H F r Lc) {i : Fin r}
    {U : Subgroup (V ≃ₗ[ZMod 2] V)} (hU : IsSylowTwoOf U (Lc i)) :
    ∃ (θ : ↥(Lc i) ≃* SL(2, F))
      (β : (↥(commGL (Lc i) ⊤) ⧸ fixIn (Lc i) (commGL (Lc i) ⊤)) ≃+ (Fin 2 → F))
      (x : SL(2, F)),
      (∀ (l : ↥(Lc i)) (u u' : ↥(commGL (Lc i) ⊤)), (u' : V) = (l : V ≃ₗ[ZMod 2] V) (u : V) →
        β (Submodule.Quotient.mk u') =
          (θ l : Matrix (Fin 2) (Fin 2) F).mulVec (β (Submodule.Quotient.mk u))) ∧
      ∀ g : SL(2, F), g ∈ (U.subgroupOf (Lc i)).map θ.toMonoidHom ↔
        ((∀ v ∈ rootLine x, (g : Matrix (Fin 2) (Fin 2) F).mulVec v = v) ∧
          ∀ v, (g : Matrix (Fin 2) (Fin 2) F).mulVec v - v ∈ rootLine x) := by
  obtain ⟨θ, β, hc, hA⟩ := hnat.model i
  obtain ⟨ℓ, hℓ1, hℓ⟩ := hA U hU
  obtain ⟨x, rfl⟩ := exists_rootLine_eq ℓ hℓ1
  exact ⟨θ, β, x, hc, hℓ⟩

omit [Finite V] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))] in
theorem natCard_of_natural_coords {i : Fin r} {U : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hUL : U ≤ Lc i) (θ : ↥(Lc i) ≃* SL(2, F)) (x : SL(2, F))
    (hline : ∀ g : SL(2, F), g ∈ (U.subgroupOf (Lc i)).map θ.toMonoidHom ↔
        ((∀ v ∈ rootLine x, (g : Matrix (Fin 2) (Fin 2) F).mulVec v = v) ∧
          ∀ v, (g : Matrix (Fin 2) (Fin 2) F).mulVec v - v ∈ rootLine x)) :
    Nat.card ↥U = Fintype.card F := by
  have hU' := natCard_rootSet (rootLine x) (finrank_rootLine x)
    ((U.subgroupOf (Lc i)).map θ.toMonoidHom) hline
  have hinj : Function.Injective θ.toMonoidHom := θ.injective
  have h1 : Nat.card ↥U = Nat.card ↥((U.subgroupOf (Lc i)).map θ.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective hinj]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUL).toEquiv).symm
  rw [h1]
  exact hU'

theorem natural_lines_lift (ctx : FamilyCtx H T n F r Lc) (hnat : NaturalFamily H F r Lc)
    {i : Fin r} {U : Subgroup (V ≃ₗ[ZMod 2] V)} (hU : IsSylowTwoOf U (Lc i))
    (θ : ↥(Lc i) ≃* SL(2, F))
    (β : (↥(commGL (Lc i) ⊤) ⧸ fixIn (Lc i) (commGL (Lc i) ⊤)) ≃+ (Fin 2 → F))
    (x : SL(2, F))
    (hcompat : ∀ (l : ↥(Lc i)) (u u' : ↥(commGL (Lc i) ⊤)),
      (u' : V) = (l : V ≃ₗ[ZMod 2] V) (u : V) →
        β (Submodule.Quotient.mk u') =
          (θ l : Matrix (Fin 2) (Fin 2) F).mulVec (β (Submodule.Quotient.mk u)))
    (hline : ∀ g : SL(2, F), g ∈ (U.subgroupOf (Lc i)).map θ.toMonoidHom ↔
        ((∀ v ∈ rootLine x, (g : Matrix (Fin 2) (Fin 2) F).mulVec v = v) ∧
          ∀ v, (g : Matrix (Fin 2) (Fin 2) F).mulVec v - v ∈ rootLine x)) :
    ∀ w ∈ rootLine x, ∃ v : ↥(commGL (Lc i) ⊤), (v : V) ∈ fixGL U ∧
      β (Submodule.Quotient.mk v) = w := by
  classical
  have hUmin : IsMinOffender H U := (hnat.P_eq U).2 ⟨i, hU⟩
  have hmove : ⁅Lc i, U⁆ ≠ ⊥ := moves_of_le_of_ne_bot ctx hU.1 hUmin.2.1
  obtain ⟨hd, -⟩ := ctx.offd U hUmin i hmove
  have hsup : commGL (Lc i) ⊤ ⊔ fixGL U = ⊤ := hd.V_split
  have hwt : Nat.card ↥U * Nat.card ↥(fixGL U) = Nat.card V := weight_eq_of_mem ctx hUmin
  have hUcard : Nat.card ↥U = Fintype.card F := natCard_of_natural_coords hU.1 θ x hline
  have hapos : 0 < Fintype.card F := Fintype.card_pos
  have hW : Nat.card ((↥(commGL (Lc i) ⊤)) ⧸ fixIn (Lc i) (commGL (Lc i) ⊤)) =
      Fintype.card F * Fintype.card F := by
    rw [Nat.card_congr β.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := F)]
    simp [sq]
  have hcount := card_range_fixed_quot (commGL (Lc i) ⊤) (fixGL U)
    (fixIn (Lc i) (commGL (Lc i) ⊤))
    (fun w hw l hl => hw l (hU.1 hl)) hsup (Fintype.card F) hapos (by rw [← hUcard]; exact hwt) hW
  let R : Submodule (ZMod 2) (↥(commGL (Lc i) ⊤) ⧸ fixIn (Lc i) (commGL (Lc i) ⊤)) :=
    LinearMap.range ((fixIn (Lc i) (commGL (Lc i) ⊤)).mkQ ∘ₗ
      Submodule.inclusion (inf_le_left : commGL (Lc i) ⊤ ⊓ fixGL U ≤ commGL (Lc i) ⊤))
  let S : Set (↥(commGL (Lc i) ⊤) ⧸ fixIn (Lc i) (commGL (Lc i) ⊤)) := {q | β q ∈ rootLine x}
  have hRS : ∀ q ∈ R, q ∈ S := by
    rintro q ⟨y, rfl⟩
    show β (Submodule.Quotient.mk ⟨(y : V), y.2.1⟩) ∈ rootLine x
    refine mem_rootLine_of_fixed x _ (fun g hg => ?_)
    have hg' := (conj_mem_range_iff_fixes_line x g).1 hg
    have hgU : g ∈ (U.subgroupOf (Lc i)).map θ.toMonoidHom :=
      (hline g).2 ⟨fun v hv => by rw [← smul_eq_mulVec']; exact hg'.1 v hv,
        fun v => by rw [← smul_eq_mulVec']; exact hg'.2 v⟩
    obtain ⟨u, hu, rfl⟩ := hgU
    have hu' : (u : V ≃ₗ[ZMod 2] V) ∈ U := hu
    have := hcompat u ⟨(y : V), y.2.1⟩ ⟨(y : V), y.2.1⟩ (by
      show (y : V) = (u : V ≃ₗ[ZMod 2] V) (y : V)
      exact (y.2.2 u (hu')).symm)
    rw [smul_eq_mulVec']
    exact this.symm
  have hScard : Nat.card S = Fintype.card F := by
    have e : S ≃ ↥(rootLine x) := β.toEquiv.subtypeEquiv (fun q => Iff.rfl)
    rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := F), finrank_rootLine,
      Nat.card_eq_fintype_card (α := F), pow_one]
  have hinj : Function.Injective (fun q : ↥R => (⟨q.1, hRS q.1 q.2⟩ : S)) := fun a b h =>
    Subtype.ext (Subtype.mk.inj h)
  have hRcard : Nat.card ↥R = Fintype.card F := hcount
  have hbij : Function.Bijective (fun q : ↥R => (⟨q.1, hRS q.1 q.2⟩ : S)) :=
    hinj.bijective_of_nat_card_le (by rw [hScard, hRcard])
  intro w hw
  obtain ⟨⟨q, hq⟩, hqw⟩ := hbij.2 ⟨β.symm w, by
    show β (β.symm w) ∈ rootLine x
    rw [AddEquiv.apply_symm_apply]
    exact hw⟩
  obtain ⟨y, hy⟩ := hq
  refine ⟨⟨(y : V), y.2.1⟩, y.2.2, ?_⟩
  have hqeq : q = β.symm w := congrArg Subtype.val hqw
  have hq2 : β q = w := by rw [hqeq]; exact AddEquiv.apply_symm_apply β w
  rw [← hq2, ← hy]
  rfl

omit [Finite V] [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))] in
theorem conjEnd_actW_of_mem {L A : Subgroup (V ≃ₗ[ZMod 2] V)} {I : Submodule (ZMod 2) V}
    (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V)))
    (hI : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (L ⊔ A) I)
    (θ : ↥L ≃* SL(2, F)) (β : (↥I ⧸ fixIn L I) ≃+ (Fin 2 → F))
    (hcompat : ∀ (l : ↥L) (u u' : ↥I), (u' : V) = (l : V ≃ₗ[ZMod 2] V) (u : V) →
        β (Submodule.Quotient.mk u') =
          (θ l : Matrix (Fin 2) (Fin 2) F).mulVec (β (Submodule.Quotient.mk u)))
    (l : ↥L) :
    conjEnd β (actW L A I hAn hI ⟨l, Subgroup.mem_sup_left l.2⟩) = natEndHom F (θ l) := by
  refine AddMonoidHom.ext fun v => ?_
  have hL : conjEnd β (actW L A I hAn hI ⟨l, Subgroup.mem_sup_left l.2⟩) v =
      β ((actW L A I hAn hI ⟨l, Subgroup.mem_sup_left l.2⟩) (β.symm v)) := conjEnd_apply β _ v
  have hR : natEndHom F (θ l) v = (θ l : Matrix (Fin 2) (Fin 2) F).mulVec v :=
    natEndHom_apply (θ l) v
  show conjEnd β (actW L A I hAn hI ⟨l, Subgroup.mem_sup_left l.2⟩) v = natEndHom F (θ l) v
  rw [hL, hR]
  obtain ⟨u0, hu0⟩ := Submodule.Quotient.mk_surjective _ (β.symm v)
  rw [← hu0, actW_mk hAn hI]
  have h := hcompat l u0
    (resSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (L ⊔ A) I hI ⟨l, Subgroup.mem_sup_left l.2⟩ u0)
    (resSub_apply _ _ _ _ _ _)
  rw [h, hu0, AddEquiv.apply_symm_apply]

theorem natural_baumann (ctx : FamilyCtx H T n F r Lc) (hnat : NaturalFamily H F r Lc)
    (hT : IsPGroup 2 ↥T) (hU : ∀ i, IsSylowTwoOf (T ⊓ Lc i) (Lc i)) {t : V ≃ₗ[ZMod 2] V}
    (ht : t ∈ T) (hfix : ∀ v ∈ fixGL (⨆ i, T ⊓ Lc i), t v = v) : t ∈ ⨆ i, T ⊓ Lc i := by
  classical
  have : CharP F 2 := charP_two_of_card_pow ctx.hF
  refine eq_iSup_of_actions ctx (T_le_H ctx ht) (fun i => T ⊓ Lc i)
    (fun i => inf_le_right.trans (Lc_le_blockB ctx i)) fun i => ?_
  obtain ⟨θ, β, x, hcompat, hline⟩ := natural_coords hnat (hU i)
  have hlift := natural_lines_lift ctx hnat (hU i) θ β x hcompat hline
  have hfixD : ∀ u : ↥(commGL (Lc i) ⊤), (u : V) ∈ fixGL (T ⊓ Lc i) →
      (u : V) ∈ fixGL (⨆ j, T ⊓ Lc j) := by
    intro u hu
    have hle : (⨆ j, T ⊓ Lc j) ≤ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) (u : V) := by
      refine iSup_le fun j => ?_
      by_cases hji : j = i
      · subst hji
        exact fun z hz => hu z hz
      · intro z hz
        exact ctx.layer.others_fix i j hji z hz.2 u u.2
    intro g hg
    exact hle hg
  obtain ⟨v0, hv0P, hv0β⟩ := hlift _ (smul_single_mem_rootLine x)
  have htv0 : t v0 = v0 := hfix _ (hfixD v0 hv0P)
  have hv0nz : (v0 : V) ∉ fixGL (Lc i) := by
    intro hmem
    have h0 : (Submodule.Quotient.mk v0 :
        ↥(commGL (Lc i) ⊤) ⧸ fixIn (Lc i) (commGL (Lc i) ⊤)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 hmem
    rw [h0, map_zero] at hv0β
    exact smul_single_ne_zero x hv0β.symm
  have hnorm := normalizes_of_fixed ctx ht v0.2 hv0nz htv0
  have hAn : Subgroup.zpowers t ≤ Subgroup.normalizer (Lc i : Set (V ≃ₗ[ZMod 2] V)) :=
    Subgroup.zpowers_le.2 hnorm
  have hI : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (Lc i ⊔ Subgroup.zpowers t)
      (commGL (Lc i) ⊤) :=
    isInvariant_sup_subgroup (isInvariant_commGL_self (Lc i))
      (isInvariant_commGL_of_le_normalizer hAn)
  have key : ∀ l : ↥(Lc i), conjEnd β (actW (Lc i) (Subgroup.zpowers t) (commGL (Lc i) ⊤) hAn hI
      ⟨l, Subgroup.mem_sup_left l.2⟩) = natEndHom F (θ l) :=
    conjEnd_actW_of_mem hAn hI θ β hcompat
  set X : Subgroup (V ≃ₗ[ZMod 2] V) := Lc i ⊔ Subgroup.zpowers t with hX
  set φ := actW (Lc i) (Subgroup.zpowers t) (commGL (Lc i) ⊤) hAn hI with hφdef
  have hLs : ∀ g : SL(2, F), ∃ l ∈ (Lc i).subgroupOf X, conjEnd β (φ l) = natEndHom F g := by
    intro g
    refine ⟨⟨(θ.symm g : ↥(Lc i)), Subgroup.mem_sup_left (θ.symm g).2⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.2 (θ.symm g).2
    · rw [key, θ.apply_symm_apply]
  have hLs' : ∀ l ∈ (Lc i).subgroupOf X, ∃ g : SL(2, F), conjEnd β (φ l) = natEndHom F g := by
    intro l hl
    have hl' : (l : V ≃ₗ[ZMod 2] V) ∈ Lc i := Subgroup.mem_subgroupOf.1 hl
    have hll : l = ⟨(⟨l, hl'⟩ : ↥(Lc i)), Subgroup.mem_sup_left hl'⟩ := Subtype.ext rfl
    rw [hll]
    exact ⟨θ ⟨l, hl'⟩, key ⟨l, hl'⟩⟩
  have hAs : ∀ g : SL(2, F), (∃ a ∈ (T ⊓ Lc i).subgroupOf X, conjEnd β (φ a) = natEndHom F g) ↔
      x⁻¹ * g * x ∈ (upperUnipotent (F := F)).range := by
    intro g
    rw [conj_mem_range_iff_fixes_line]
    constructor
    · rintro ⟨a, ha, hag⟩
      have ha' : (a : V ≃ₗ[ZMod 2] V) ∈ T ⊓ Lc i := Subgroup.mem_subgroupOf.1 ha
      have haa : a = ⟨(⟨a, ha'.2⟩ : ↥(Lc i)), Subgroup.mem_sup_left ha'.2⟩ := Subtype.ext rfl
      rw [haa, key] at hag
      have hgθ : θ ⟨a, ha'.2⟩ = g := natEndHom_injective hag
      have hmem : g ∈ ((T ⊓ Lc i).subgroupOf (Lc i)).map θ.toMonoidHom :=
        ⟨⟨a, ha'.2⟩, ha', hgθ⟩
      obtain ⟨h1, h2⟩ := (hline g).1 hmem
      exact ⟨fun v hv => by rw [smul_eq_mulVec']; exact h1 v hv,
        fun v => by rw [smul_eq_mulVec']; exact h2 v⟩
    · rintro ⟨h1, h2⟩
      have hmem : g ∈ ((T ⊓ Lc i).subgroupOf (Lc i)).map θ.toMonoidHom :=
        (hline g).2 ⟨fun v hv => by rw [← smul_eq_mulVec']; exact h1 v hv,
          fun v => by rw [← smul_eq_mulVec']; exact h2 v⟩
      obtain ⟨l0, hl0, hl0g⟩ := hmem
      refine ⟨⟨l0, Subgroup.mem_sup_left l0.2⟩, Subgroup.mem_subgroupOf.2 hl0, ?_⟩
      rw [key, ← hl0g]
      rfl
  have hEn : ∀ e ∈ (Subgroup.zpowers t).subgroupOf X, ∀ l ∈ (Lc i).subgroupOf X,
      e * l * e⁻¹ ∈ (Lc i).subgroupOf X := by
    intro e he l hl
    have he' : (e : V ≃ₗ[ZMod 2] V) ∈ Subgroup.zpowers t := Subgroup.mem_subgroupOf.1 he
    have hl' : (l : V ≃ₗ[ZMod 2] V) ∈ Lc i := Subgroup.mem_subgroupOf.1 hl
    exact Subgroup.mem_subgroupOf.2 ((Subgroup.mem_normalizer_iff.1 (hAn he') _).1 hl')
  have htX : t ∈ X := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have hek : (⟨t, htX⟩ : ↥X) ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  have hfix' : ∀ v ∈ rootLine x, conjEnd β (φ ⟨t, htX⟩) v = v := by
    intro v hv
    obtain ⟨u, hu, hβu⟩ := hlift v hv
    have htu : t (u : V) = (u : V) := hfix _ (hfixD u hu)
    have hbu : β.symm v = Submodule.Quotient.mk u := (AddEquiv.symm_apply_eq β).2 hβu.symm
    rw [conjEnd_apply, hbu, hφdef, actW_mk hAn hI]
    have hres : resSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (Lc i ⊔ Subgroup.zpowers t) (commGL (Lc i) ⊤) hI
        ⟨t, htX⟩ u = u := Subtype.ext (by rw [resSub_apply]; exact htu)
    rw [hres]
    exact hβu
  obtain ⟨a, haAs, hφ⟩ := exists_element_of_fix_line φ β ((Lc i).subgroupOf X)
    ((T ⊓ Lc i).subgroupOf X) ((Subgroup.zpowers t).subgroupOf X) x hLs hLs' hAs hEn
    (Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers t) : (⟨t, htX⟩ : ↥X) ∈
      (Subgroup.zpowers t).subgroupOf X) hek hfix'
  have ha' : (a : V ≃ₗ[ZMod 2] V) ∈ T ⊓ Lc i := Subgroup.mem_subgroupOf.1 haAs
  refine ⟨(a : V ≃ₗ[ZMod 2] V), ha', fun y hy => ?_⟩
  have h1 : φ ⟨t, htX⟩ (Submodule.Quotient.mk ⟨y, hy⟩) = φ a (Submodule.Quotient.mk ⟨y, hy⟩) := by
    rw [hφ]
  rw [hφdef, actW_mk hAn hI, actW_mk hAn hI, Submodule.Quotient.eq] at h1
  have hty : t y ∈ commGL (Lc i) ⊤ := isInvariant_commGL_of_le_normalizer hAn t
    (Subgroup.mem_zpowers t) y hy
  have hay : (a : V ≃ₗ[ZMod 2] V) y ∈ commGL (Lc i) ⊤ :=
    isInvariant_commGL_self (Lc i) a ha'.2 y hy
  have h2 : t y - (a : V ≃ₗ[ZMod 2] V) y ∈ fixGL (Lc i) := by
    have e1 : ((resSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (Lc i ⊔ Subgroup.zpowers t) (commGL (Lc i) ⊤)
        hI ⟨t, htX⟩ ⟨y, hy⟩ - resSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (Lc i ⊔ Subgroup.zpowers t)
        (commGL (Lc i) ⊤) hI a ⟨y, hy⟩ : ↥(commGL (Lc i) ⊤)) : V) =
        t y - (a : V ≃ₗ[ZMod 2] V) y := by
      rw [Submodule.coe_sub, resSub_apply, resSub_apply]
      rfl
    rw [← e1]
    exact h1
  have h4 : t y - (a : V ≃ₗ[ZMod 2] V) y ∈ commGL (Lc i) ⊤ ⊓ fixGL (Lc i) :=
    ⟨(commGL (Lc i) ⊤).sub_mem hty hay, h2⟩
  rw [← I_inf_C ctx i] at h4
  exact h4.2

end Natural

end CFSG.QuasithinUnique.Setup.Lift
