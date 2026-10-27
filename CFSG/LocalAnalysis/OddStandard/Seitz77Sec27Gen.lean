module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup

theorem nonempty_mulEquiv_fin_zmod_two {W : Type*} [Group W] [Finite W]
    (hc : ∀ a b : W, a * b = b * a) (hsq : ∀ a : W, a * a = 1) (hcard : Nat.card W = 2 ^ 8) :
    Nonempty (W ≃* Multiplicative (Fin 8 → ZMod 2)) := by
  let _ : CommGroup W := { ‹Group W› with mul_comm := hc }
  have h2 : ∀ x : Additive W, (2 : ℕ) • x = 0 := fun x => by
    rw [two_nsmul]
    exact hsq x.toMul
  let _ : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule h2
  have hfin : Module.finrank (ZMod 2) (Additive W) = 8 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    rw [Nat.card_zmod] at h
    have h' : Nat.card (Additive W) = 2 ^ 8 := by
      rw [← hcard]
      exact Nat.card_congr Additive.toMul
    rw [h'] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive W) hfin
  exact ⟨AddEquiv.toMultiplicativeRight b.equivFun.toAddEquiv⟩

def zmodTwoLinearOfAddHom (f : (Fin 8 → ZMod 2) →+ (Fin 8 → ZMod 2)) :
    (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2) :=
  { toFun := f
    map_add' := map_add f
    map_smul' := fun c x => by
      rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul, RingHom.id_apply,
        Nat.cast_smul_eq_nsmul]
      exact map_nsmul f _ x }

theorem exists_gl_rep {W : Type*} [Group W] [Finite W] (hc : ∀ a b : W, a * b = b * a)
    (hsq : ∀ a : W, a * a = 1) (hcard : Nat.card W = 2 ^ 8) {H : Type*} [Group H]
    (α : H →* MulAut W) (hα : Function.Injective α) :
    ∃ (κ : W ≃* Multiplicative (Fin 8 → ZMod 2)) (ρ : H →* GL (Fin 8) (ZMod 2)),
      Function.Injective ρ ∧ ∀ (h : H) (w : W), κ (α h w) =
        Multiplicative.ofAdd ((ρ h : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec
          (Multiplicative.toAdd (κ w))) := by
  obtain ⟨κ⟩ := nonempty_mulEquiv_fin_zmod_two hc hsq hcard
  let φ : H → ((Fin 8 → ZMod 2) →+ (Fin 8 → ZMod 2)) := fun h =>
    { toFun := fun x => Multiplicative.toAdd (κ (α h (κ.symm (Multiplicative.ofAdd x))))
      map_zero' := by simp
      map_add' := fun x y => by simp }
  let L : H → ((Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) := fun h =>
    zmodTwoLinearOfAddHom (φ h)
  have hL : ∀ h x, L h x = Multiplicative.toAdd (κ (α h (κ.symm (Multiplicative.ofAdd x)))) :=
    fun _ _ => rfl
  have hL1 : L 1 = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    simp [hL]
  have hLmul : ∀ h k, L (h * k) = (L h).comp (L k) := by
    intro h k
    refine LinearMap.ext fun x => ?_
    simp [hL]
  let Mhom : H →* Matrix (Fin 8) (Fin 8) (ZMod 2) :=
    { toFun := fun h => LinearMap.toMatrix' (L h)
      map_one' := by rw [hL1, LinearMap.toMatrix'_id]
      map_mul' := fun h k => by rw [hLmul, LinearMap.toMatrix'_comp] }
  have key : ∀ h w, κ (α h w) =
      Multiplicative.ofAdd ((Mhom h).mulVec (Multiplicative.toAdd (κ w))) := by
    intro h w
    show _ = Multiplicative.ofAdd (Matrix.mulVec (LinearMap.toMatrix' (L h)) _)
    rw [LinearMap.toMatrix'_mulVec, hL]
    simp
  refine ⟨κ, Mhom.toHomUnits, ?_, ?_⟩
  · intro h k hhk
    apply hα
    refine MulEquiv.ext fun w => κ.injective ?_
    rw [key h w, key k w]
    have := congrArg (fun u : GL (Fin 8) (ZMod 2) => (u : Matrix (Fin 8) (Fin 8) (ZMod 2))) hhk
    simp at this
    rw [this]
  · intro h w
    exact key h w

theorem card_eq_two_pow_finrank_aux {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] :
    Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V), Nat.card_zmod]

theorem card_submodule_eq_two_pow (U : Submodule (ZMod 2) (Fin 8 → ZMod 2)) :
    Nat.card U = 2 ^ Module.finrank (ZMod 2) U :=
  @card_eq_two_pow_finrank_aux U (Submodule.addCommGroup U) (Submodule.module U) inferInstance


theorem stab_of_trans_sixty {R : Type*} [Group R] [Finite R] (hR : Nat.card R = 16)
    (S : Subgroup (MulAut R)) (hS : Nat.card S = 60)
    (htrans : ∀ r s : R, r ≠ 1 → s ≠ 1 → ∃ g ∈ S, g r = s) :
    ∀ g ∈ S, g ^ 3 = 1 → ∀ r : R, r ≠ 1 → g r = r → g = 1 := by
  intro g hg hg3 r hr hgr
  have horb : MulAction.orbit S r = {s : R | s ≠ 1} := by
    ext s
    constructor
    · rintro ⟨⟨h, hh⟩, rfl⟩ h1
      apply hr
      have h1' : h r = 1 := h1
      simpa using h1'
    · intro hs
      obtain ⟨g, hg, hgs⟩ := htrans r s hr hs
      exact ⟨⟨g, hg⟩, hgs⟩
  have hcard : Nat.card (MulAction.orbit S r) = 15 := by
    rw [horb, Nat.card_coe_set_eq]
    have : {s : R | s ≠ 1} = Set.univ \ {1} := by
      ext s; simp
    rw [this, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, hR]
  have hprod := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup S r)
  rw [Nat.card_prod, hcard, hS] at hprod
  have hstab : Nat.card (MulAction.stabilizer S r) = 4 := by omega
  have hmem : (⟨g, hg⟩ : S) ∈ MulAction.stabilizer S r := by
    rw [MulAction.mem_stabilizer_iff]
    exact hgr
  obtain ⟨h, hh⟩ : ∃ h : MulAction.stabilizer S r, ((h : S) : MulAut R) = g :=
    ⟨⟨⟨g, hg⟩, hmem⟩, rfl⟩
  have h4 : h ^ 4 = 1 := by
    have := pow_card_eq_one' (G := MulAction.stabilizer S r) (x := h)
    rwa [hstab] at this
  have h3 : h ^ 3 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simpa [hh] using hg3
  have h1 : h = 1 := by
    calc h = h ^ 4 * (h ^ 3)⁻¹ := by group
      _ = 1 := by rw [h4, h3]; simp
  rw [← hh, h1]
  simp

theorem card_invariant_aux {G : Type*} [Group G] {R P V : Subgroup G}
    (hRc : Nat.card R = 16)
    (htrans : ∀ r ∈ R, ∀ s ∈ R, r ≠ 1 → s ≠ 1 → ∃ p ∈ P, p * r * p⁻¹ = s)
    (hVR : V ≤ R) (hVinv : ∀ p ∈ P, ∀ v ∈ V, p * v * p⁻¹ ∈ V) :
    Nat.card V = 1 ∨ Nat.card V = 16 := by
  by_cases hV : V = ⊥
  · left
    rw [hV]
    exact Subgroup.card_bot
  · right
    obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV
    have hRV : R ≤ V := by
      intro s hs
      by_cases hs1 : s = 1
      · rw [hs1]
        exact V.one_mem
      · obtain ⟨p, hp, hps⟩ :=
          htrans (v : G) (hVR v.2) s hs (fun h => hv1 (Subtype.ext h)) hs1
        rw [← hps]
        exact hVinv p hp v v.2
    rw [le_antisymm hVR hRV]
    exact hRc

theorem exists_commutator_hom_aux {G : Type*} [Group G] {W : Subgroup G} {t : G}
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (htn : ∀ w ∈ W, t * w * t⁻¹ ∈ W) :
    ∃ δ : W →* G, ∀ w : W, δ w = t * (w : G) * t⁻¹ * (w : G)⁻¹ := by
  refine ⟨MonoidHom.mk' (fun w : W => t * (w : G) * t⁻¹ * (w : G)⁻¹) ?_, fun w => rfl⟩
  intro a b
  have hz : (t * (b : G) * t⁻¹ * (b : G)⁻¹) * (a : G)⁻¹
      = (a : G)⁻¹ * (t * (b : G) * t⁻¹ * (b : G)⁻¹) :=
    hWab _ (W.mul_mem (htn b b.2) (W.inv_mem b.2)) _ (W.inv_mem a.2)
  show t * ((a : G) * (b : G)) * t⁻¹ * ((a : G) * (b : G))⁻¹ =
    (t * (a : G) * t⁻¹ * (a : G)⁻¹) * (t * (b : G) * t⁻¹ * (b : G)⁻¹)
  calc t * ((a : G) * (b : G)) * t⁻¹ * ((a : G) * (b : G))⁻¹
      = t * (a : G) * t⁻¹ * ((t * (b : G) * t⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
    _ = t * (a : G) * t⁻¹ * ((a : G)⁻¹ * (t * (b : G) * t⁻¹ * (b : G)⁻¹)) := by rw [hz]
    _ = (t * (a : G) * t⁻¹ * (a : G)⁻¹) * (t * (b : G) * t⁻¹ * (b : G)⁻¹) := by group

theorem invariant_card_of_trans {G : Type*} [Group G] [Finite G] {W R P U : Subgroup G} {t : G}
    (hRW : R ≤ W) (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hWc : Nat.card W = 2 ^ 8) (hRc : Nat.card R = 16) (htn : ∀ w ∈ W, t * w * t⁻¹ ∈ W)
    (hCt : ∀ w ∈ W, w * t = t * w → w ∈ R) (hCt' : ∀ r ∈ R, r * t = t * r)
    (hcomm : ∀ v ∈ R, ∃ w ∈ W, t * w * t⁻¹ * w⁻¹ = v)
    (hPc : ∀ p ∈ P, p * t = t * p) (hPR : ∀ p ∈ P, ∀ r ∈ R, p * r * p⁻¹ ∈ R)
    (htrans : ∀ r ∈ R, ∀ s ∈ R, r ≠ 1 → s ≠ 1 → ∃ p ∈ P, p * r * p⁻¹ = s)
    (hU : U ≤ W) (hUinv : ∀ p ∈ P, ∀ u ∈ U, p * u * p⁻¹ ∈ U) :
    Nat.card U = 1 ∨ Nat.card U = 16 ∨ Nat.card U = 2 ^ 8 := by
  obtain ⟨δ, hδ⟩ := exists_commutator_hom_aux hWab htn
  have hδker : ∀ w : W, δ w = 1 ↔ (w : G) ∈ R := by
    intro w
    rw [hδ]
    constructor
    · intro h
      apply hCt _ w.2
      have h' : t * (w : G) * t⁻¹ = (w : G) := mul_inv_eq_one.mp h
      calc (w : G) * t = t * (w : G) * t⁻¹ * t := by rw [h']
        _ = t * (w : G) := by group
    · intro h
      have h1 := hCt' _ h
      rw [← h1]
      group
  have hkerR : δ.ker = R.subgroupOf W := by
    ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hδker w
  have hkerc : Nat.card δ.ker = 16 := by
    rw [hkerR, ← hRc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRW).toEquiv
  have hrangec : Nat.card δ.range = 16 := by
    have := Subgroup.card_ker_mul_card_range δ
    rw [hkerc, hWc] at this
    omega
  have hRrange : R ≤ δ.range := by
    intro v hv
    obtain ⟨w, hw, hwv⟩ := hcomm v hv
    exact ⟨⟨w, hw⟩, by rw [hδ]; exact hwv⟩
  have hrange : R = δ.range :=
    Subgroup.eq_of_le_of_card_ge hRrange (by rw [hrangec, hRc])
  obtain ⟨δU, hδU⟩ : ∃ δU : U →* G, ∀ u : U, δU u = t * (u : G) * t⁻¹ * (u : G)⁻¹ :=
    ⟨δ.comp (Subgroup.inclusion hU), fun u => hδ _⟩
  have hδUR : ∀ u : U, δU u ∈ R := by
    intro u
    have : δU u ∈ δ.range := ⟨⟨u, hU u.2⟩, by rw [hδ, hδU]⟩
    rwa [← hrange] at this
  have hkerU : δU.ker = (U ⊓ R).subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : δ ⟨u, hU u.2⟩ = 1 := by
        rw [hδ]
        rw [hδU] at h
        exact h
      exact ⟨u.2, (hδker _).mp h1⟩
    · intro h
      have h1 := (hδker ⟨u, hU u.2⟩).mpr h.2
      rw [hδ] at h1
      rw [hδU]
      exact h1
  have hkerUc : Nat.card δU.ker = Nat.card (U ⊓ R : Subgroup G) := by
    rw [hkerU]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcardU : Nat.card δU.ker * Nat.card δU.range = Nat.card U :=
    Subgroup.card_ker_mul_card_range δU
  have hK : Nat.card (U ⊓ R : Subgroup G) = 1 ∨ Nat.card (U ⊓ R : Subgroup G) = 16 :=
    card_invariant_aux hRc htrans inf_le_right
      (fun p hp v hv => ⟨hUinv p hp v hv.1, hPR p hp v hv.2⟩)
  have hD : Nat.card δU.range = 1 ∨ Nat.card δU.range = 16 := by
    refine card_invariant_aux hRc htrans ?_ ?_
    · rintro _ ⟨u, rfl⟩
      exact hδUR u
    · rintro p hp _ ⟨u, rfl⟩
      refine ⟨⟨p * u * p⁻¹, hUinv p hp u u.2⟩, ?_⟩
      have hpt : p * t * p⁻¹ = t := by rw [hPc p hp]; group
      rw [hδU, hδU]
      calc t * (p * (u : G) * p⁻¹) * t⁻¹ * (p * (u : G) * p⁻¹)⁻¹
          = (p * t * p⁻¹) * (p * (u : G) * p⁻¹) * (p * t * p⁻¹)⁻¹ * (p * (u : G) * p⁻¹)⁻¹ := by
            rw [hpt]
        _ = p * (t * (u : G) * t⁻¹ * (u : G)⁻¹) * p⁻¹ := by group
  rw [← hcardU, hkerUc]
  rcases hK with h1 | h1 <;> rcases hD with h2 | h2 <;> rw [h1, h2] <;> norm_num


theorem derivedSeries_eq_top_of_commutator_eq_top {S : Type*} [Group S]
    (hS : commutator S = ⊤) (n : ℕ) : derivedSeries S n = ⊤ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [derivedSeries_succ, ih]; exact hS

theorem exists_perfect_residual {B S : Type*} [Group B] [Finite B] [Group S] (ρ : B →* S)
    (hρ : Function.Surjective ρ) (hS : commutator S = ⊤) :
    ∃ P : Subgroup B, ⁅P, P⁆ = P ∧ P.map ρ = ⊤ ∧ ∀ f : B ≃* B, P.map f.toMonoidHom = P := by
  obtain ⟨n, hn⟩ := WellFoundedLT.antitone_chain_condition (derivedSeries_antitone B)
  refine ⟨derivedSeries B n, ?_, ?_, ?_⟩
  · rw [← derivedSeries_succ]
    exact (hn (n + 1) (Nat.le_succ n)).symm
  · rw [map_derivedSeries_eq hρ n]
    exact derivedSeries_eq_top_of_commutator_eq_top hS n
  · exact characteristic_iff_map_eq.mp (derivedSeries_characteristic B n)

end CFSG.OddStandard.Seitz77
