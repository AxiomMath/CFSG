module

public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.OddOrder.PrimeDimAbelianImageTwoModels
public import CFSG.FeitThompson.OddOrder.QuotientFrobeniusAction
public import CFSG.FeitThompson.Local.ElementaryAbelianCubeInvariantPlane
public import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
open CFSG.FeitThompson.Prep05

universe u v

namespace natCardBound

theorem sub_one_pow_le_div {p q : ℕ} (hp : 1 < p) (hq : 1 ≤ q) :
    (p - 1) ^ (q - 1) ≤ (p ^ q - 1) / (p - 1) := by
  have hp1 : 0 < p - 1 := by omega
  rw [Nat.le_div_iff_mul_le hp1]
  have h1 : (p - 1) ^ (q - 1) * (p - 1) = (p - 1) ^ q := by
    rw [← pow_succ]; congr 1; omega
  have h2 : (p - 1) ^ q < p ^ q := Nat.pow_lt_pow_left (by omega) (by omega)
  omega

theorem one_le_div {p q : ℕ} (hp : 1 < p) (hq : 1 ≤ q) : 1 ≤ (p ^ q - 1) / (p - 1) := by
  have h1 := sub_one_pow_le_div hp hq
  have h2 : 1 ≤ (p - 1) ^ (q - 1) := Nat.one_le_pow _ _ (by omega)
  omega

end natCardBound

section Stabilizer

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

private theorem map_mul_coe (W : Submodule k V) (x y : V ≃ₗ[k] V) :
    W.map ((x * y : V ≃ₗ[k] V) : V →ₗ[k] V) = (W.map (y : V →ₗ[k] V)).map (x : V →ₗ[k] V) := by
  rw [← Submodule.map_comp]; rfl

def submoduleStabilizer (W : Submodule k V) : Subgroup (V ≃ₗ[k] V) where
  carrier := {g | W.map (g : V →ₗ[k] V) = W}
  one_mem' := by simp
  mul_mem' {x y} hx hy := by
    change W.map ((x * y : V ≃ₗ[k] V) : V →ₗ[k] V) = W
    rw [map_mul_coe, show W.map (y : V →ₗ[k] V) = W from hy,
      show W.map (x : V →ₗ[k] V) = W from hx]
  inv_mem' {x} hx := by
    change W.map ((x⁻¹ : V ≃ₗ[k] V) : V →ₗ[k] V) = W
    have h : W.map ((x⁻¹ * x : V ≃ₗ[k] V) : V →ₗ[k] V) = W := by rw [inv_mul_cancel]; simp
    rw [map_mul_coe, show W.map (x : V →ₗ[k] V) = W from hx] at h
    exact h

theorem mem_submoduleStabilizer {W : Submodule k V} {g : V ≃ₗ[k] V} :
    g ∈ submoduleStabilizer W ↔ W.map (g : V →ₗ[k] V) = W := Iff.rfl

theorem le_submoduleStabilizer_iff {D : Subgroup (V ≃ₗ[k] V)} {W : Submodule k V} :
    D ≤ submoduleStabilizer W ↔ IsInvariantSubmodule D W := by
  constructor
  · intro h g hg v hv
    rw [← mem_submoduleStabilizer.1 (h hg)]
    exact Submodule.mem_map_of_mem hv
  · intro h g hg
    rw [mem_submoduleStabilizer]
    refine le_antisymm ?_ fun v hv =>
      ⟨(g⁻¹ : V ≃ₗ[k] V) v, h _ (inv_mem hg) v hv, by simp⟩
    rintro _ ⟨v, hv, rfl⟩
    exact h g hg v hv

theorem isInvariantSubmodule_sup {D B : Subgroup (V ≃ₗ[k] V)} {W : Submodule k V}
    (hD : IsInvariantSubmodule D W) (hB : IsInvariantSubmodule B W) :
    IsInvariantSubmodule (D ⊔ B) W :=
  le_submoduleStabilizer_iff.1 (sup_le (le_submoduleStabilizer_iff.2 hD)
    (le_submoduleStabilizer_iff.2 hB))

end Stabilizer

section Translate

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {D : Subgroup (V ≃ₗ[k] V)}

theorem fixedSubmodule_eq_invariants (D : Subgroup (V ≃ₗ[k] V)) :
    fixedSubmodule D = Representation.invariants (linearGroupRep D) := by
  ext v
  rw [mem_fixedSubmodule, Representation.mem_invariants]
  simp only [linearGroupRep_apply]
  exact ⟨fun h g => h g g.2, fun h g hg => h ⟨g, hg⟩⟩

theorem isIrreducibleLinear_iff [Nontrivial V] :
    IsIrreducibleLinear D ↔ (linearGroupRep D).IsIrreducible := by
  rw [isIrreducible_linearGroupRep_iff]
  exact ⟨fun h => ⟨‹_›, fun W hW => h W hW⟩, fun h W hW => h.2 W hW⟩

theorem actsReducibly_iff_not_isIrreducibleLinear [Nontrivial V] :
    ActsReducibly D ↔ ¬ IsIrreducibleLinear D := by
  rw [isIrreducibleLinear_iff, ← not_actsReducibly_iff, not_not]

end Translate

section Realized

variable {G : Type*} [Group G] {M H U W₁ : Subgroup G} {p : ℕ} {V : Type*} [AddCommGroup V]
  [Module (ZMod p) V] {e : ↥H ≃* Multiplicative V} {ρ : ↥M →* (V ≃ₗ[ZMod p] V)}

def subgroupOfSubmodule (e : ↥H ≃* Multiplicative V) (W : Submodule (ZMod p) V) : Subgroup G :=
  ((AddSubgroup.toSubgroup W.toAddSubgroup).comap e.toMonoidHom).map H.subtype

theorem subgroupOfSubmodule_le (e : ↥H ≃* Multiplicative V) (W : Submodule (ZMod p) V) :
    subgroupOfSubmodule e W ≤ H := Subgroup.map_subtype_le _

theorem mem_subgroupOfSubmodule {W : Submodule (ZMod p) V} {g : G} :
    g ∈ subgroupOfSubmodule e W ↔ ∃ hg : g ∈ H, Multiplicative.toAdd (e ⟨g, hg⟩) ∈ W := by
  simp only [subgroupOfSubmodule, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
  exact ⟨fun ⟨x, hx, hxg⟩ => ⟨hxg ▸ x.2, by subst hxg; exact hx⟩, fun ⟨hg, h⟩ => ⟨⟨g, hg⟩, h, rfl⟩⟩

theorem subgroupOfSubmodule_eq_bot_iff {W : Submodule (ZMod p) V} :
    subgroupOfSubmodule e W = ⊥ ↔ W = ⊥ := by
  constructor
  · intro h
    refine le_antisymm (fun w hw => ?_) bot_le
    have hmem : ((e.symm (Multiplicative.ofAdd w) : ↥H) : G) ∈ subgroupOfSubmodule e W :=
      mem_subgroupOfSubmodule.2 ⟨(e.symm (Multiplicative.ofAdd w) : ↥H).2, by simpa using hw⟩
    rw [h, Subgroup.mem_bot] at hmem
    have h2 := congrArg e (Subtype.ext hmem : e.symm (Multiplicative.ofAdd w) = 1)
    rw [MulEquiv.apply_symm_apply, map_one] at h2
    simpa [ofAdd_eq_one] using h2
  · rintro rfl
    refine le_antisymm (fun g hg => ?_) bot_le
    obtain ⟨hgH, hg⟩ := mem_subgroupOfSubmodule.1 hg
    rw [Submodule.mem_bot] at hg
    have hone : (⟨g, hgH⟩ : ↥H) = 1 := by
      refine e.injective ?_
      rw [map_one]
      exact Multiplicative.toAdd.injective (by simpa using hg)
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hone)

theorem subgroupOfSubmodule_eq_top_iff {W : Submodule (ZMod p) V} :
    subgroupOfSubmodule e W = H ↔ W = ⊤ := by
  refine ⟨fun h => le_antisymm le_top fun w _ => ?_, ?_⟩
  · have hmem : ((e.symm (Multiplicative.ofAdd w) : ↥H) : G) ∈ subgroupOfSubmodule e W := by
      rw [h]; exact (e.symm (Multiplicative.ofAdd w) : ↥H).2
    obtain ⟨hwH, h2⟩ := mem_subgroupOfSubmodule.1 hmem
    simpa using h2
  · rintro rfl
    exact le_antisymm (subgroupOfSubmodule_le e ⊤)
      fun g hg => mem_subgroupOfSubmodule.2 ⟨hg, Submodule.mem_top⟩

theorem conj_mem_of_le_normalizer (hHM : M ≤ normalizer (H : Set G)) {x : G} (hx : x ∈ M)
    {h : G} (hh : h ∈ H) : x * h * x⁻¹ ∈ H :=
  (Subgroup.mem_set_normalizer_iff.1 (hHM hx) h).1 hh

theorem toAdd_e_conj (hρ : IsConjModule p H M V e ρ) (hHM : M ≤ normalizer (H : Set G))
    (x : ↥M) (h : ↥H) :
    ρ x (Multiplicative.toAdd (e h)) =
      Multiplicative.toAdd
        (e ⟨(x : G) * (h : G) * (x : G)⁻¹, conj_mem_of_le_normalizer hHM x.2 h.2⟩) := by
  rw [hρ.conj_eq x h (conj_mem_of_le_normalizer hHM x.2 h.2)]
  rfl

theorem rho_apply_eq_self_iff (hρ : IsConjModule p H M V e ρ)
    (hHM : M ≤ normalizer (H : Set G)) (x : ↥M) (h : ↥H) :
    ρ x (Multiplicative.toAdd (e h)) = Multiplicative.toAdd (e h) ↔
      (x : G) * (h : G) = (h : G) * (x : G) := by
  rw [toAdd_e_conj hρ hHM x h]
  refine ⟨fun hh => mul_inv_eq_iff_eq_mul.1
    (congrArg Subtype.val (e.injective (Multiplicative.toAdd.injective hh))), fun hh => ?_⟩
  congr 2
  exact Subtype.ext (by rw [mul_inv_eq_iff_eq_mul, hh])

theorem rho_eq_one_iff (hρ : IsConjModule p H M V e ρ) (hHM : M ≤ normalizer (H : Set G))
    (x : ↥M) : ρ x = 1 ↔ (x : G) ∈ centralizer (H : Set G) := by
  refine ⟨fun hx => Subgroup.mem_centralizer_iff.2 fun h hh =>
    ((rho_apply_eq_self_iff hρ hHM x ⟨h, hh⟩).1 (by rw [hx]; rfl)).symm, fun hx => ?_⟩
  refine LinearEquiv.ext fun w => ?_
  obtain ⟨h, rfl⟩ : ∃ h : ↥H, Multiplicative.toAdd (e h) = w :=
    ⟨e.symm (Multiplicative.ofAdd w), by simp⟩
  rw [(rho_apply_eq_self_iff hρ hHM x h).2 (Subgroup.mem_centralizer_iff.1 hx (h : G) h.2).symm]
  rfl

theorem ker_rho (hρ : IsConjModule p H M V e ρ) (hHM : M ≤ normalizer (H : Set G)) :
    ρ.ker = (centralizer (H : Set G)).subgroupOf M := by
  ext x
  rw [MonoidHom.mem_ker, rho_eq_one_iff hρ hHM, Subgroup.mem_subgroupOf]

theorem natCard_map_rho [Finite G] (hρ : IsConjModule p H M V e ρ)
    (hHM : M ≤ normalizer (H : Set G)) {K : Subgroup G} (hK : K ≤ M) :
    Nat.card ↥((K.subgroupOf M).map ρ) = (centralizerIn K H).relIndex K := by
  rw [← Subgroup.relIndex_ker, ker_rho hρ hHM, Subgroup.relIndex_subgroupOf hK, centralizerIn_eq,
    Subgroup.relIndex, Subgroup.relIndex, inf_comm, Subgroup.inf_subgroupOf_right]

theorem mem_fixedSubmodule_map_rho_iff (hρ : IsConjModule p H M V e ρ)
    (hHM : M ≤ normalizer (H : Set G)) {K : Subgroup G} (hK : K ≤ M) (h : ↥H) :
    Multiplicative.toAdd (e h) ∈ fixedSubmodule ((K.subgroupOf M).map ρ) ↔
      (h : G) ∈ centralizerIn H K := by
  rw [mem_fixedSubmodule, centralizerIn_eq, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  refine ⟨fun hh => ⟨h.2, fun y hy => ?_⟩, ?_⟩
  · have hy' : (⟨y, hK hy⟩ : ↥M) ∈ K.subgroupOf M := Subgroup.mem_subgroupOf.2 hy
    exact (rho_apply_eq_self_iff hρ hHM ⟨y, hK hy⟩ h).1 (hh (ρ ⟨y, hK hy⟩) ⟨_, hy', rfl⟩)
  · rintro ⟨-, hc⟩ g ⟨y, hy, rfl⟩
    exact (rho_apply_eq_self_iff hρ hHM y h).2 (hc (y : G) (Subgroup.mem_subgroupOf.1 hy))

theorem le_normalizer_subgroupOfSubmodule (hρ : IsConjModule p H M V e ρ)
    (hHM : M ≤ normalizer (H : Set G)) {W : Submodule (ZMod p) V}
    (hW : IsInvariantSubmodule ρ.range W) :
    M ≤ normalizer ((subgroupOfSubmodule e W : Subgroup G) : Set G) := by
  have key : ∀ y : G, ∀ hy : y ∈ M, ∀ z : G, z ∈ subgroupOfSubmodule e W →
      y * z * y⁻¹ ∈ subgroupOfSubmodule e W := by
    intro y hy z hz
    obtain ⟨hzH, hz⟩ := mem_subgroupOfSubmodule.1 hz
    refine mem_subgroupOfSubmodule.2 ⟨conj_mem_of_le_normalizer hHM hy hzH, ?_⟩
    rw [← toAdd_e_conj hρ hHM ⟨y, hy⟩ ⟨z, hzH⟩]
    exact hW (ρ ⟨y, hy⟩) ⟨⟨y, hy⟩, rfl⟩ _ hz
  intro x hx
  refine Subgroup.mem_set_normalizer_iff.2 fun g => ⟨fun hg => key x hx g hg, fun hg => ?_⟩
  have h := key x⁻¹ (M.inv_mem hx) _ hg
  rwa [show x⁻¹ * (x * g * x⁻¹) * (x⁻¹)⁻¹ = g by group] at h

theorem isIrreducibleLinear_range (hρ : IsConjModule p H M V e ρ)
    (hHM : M ≤ normalizer (H : Set G))
    (hmin : ∀ N : Subgroup G, N ≤ H → M ≤ normalizer (N : Set G) → N = ⊥ ∨ N = H) :
    IsIrreducibleLinear ρ.range := fun W hW => by
  rcases hmin (subgroupOfSubmodule e W) (subgroupOfSubmodule_le e W)
    (le_normalizer_subgroupOfSubmodule hρ hHM hW) with h | h
  · exact Or.inl (subgroupOfSubmodule_eq_bot_iff.1 h)
  · exact Or.inr (subgroupOfSubmodule_eq_top_iff.1 h)

theorem range_rho_eq_sup (hHle : H ≤ M) (hHab : IsMulCommutative ↥H)
    (hρ : IsConjModule p H M V e ρ) (hHM : M ≤ normalizer (H : Set G))
    (hUM : U ≤ M) (hWM : W₁ ≤ M) (hsup : H ⊔ (U ⊔ W₁) = M) :
    ρ.range = (U.subgroupOf M).map ρ ⊔ (W₁.subgroupOf M).map ρ := by
  have hHker : H.subgroupOf M ≤ ρ.ker := by
    rw [ker_rho hρ hHM]
    refine Subgroup.subgroupOf_mono M fun x hx => ?_
    exact Subgroup.mem_centralizer_iff.2 fun y hy =>
      congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : ↥H) ⟨x, hx⟩)
  have h1 : (H.subgroupOf M).map ρ = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_bot.2 (MonoidHom.mem_ker.1 (hHker hx))
  have h3 : (⊤ : Subgroup ↥M) = H.subgroupOf M ⊔ (U.subgroupOf M ⊔ W₁.subgroupOf M) := by
    rw [← Subgroup.subgroupOf_sup hUM hWM, ← Subgroup.subgroupOf_sup hHle (sup_le hUM hWM),
      hsup, Subgroup.subgroupOf_self]
  rw [MonoidHom.range_eq_map ρ, h3, Subgroup.map_sup, h1, bot_sup_eq, Subgroup.map_sup]

theorem mem_subgroupOf_centralizerIn_iff (hρ : IsConjModule p H M V e ρ)
    (hHM : M ≤ normalizer (H : Set G)) (hUM : U ≤ M) (x : ↥U) :
    x ∈ (centralizerIn U H).subgroupOf U ↔ ρ ⟨(x : G), hUM x.2⟩ = 1 := by
  rw [Subgroup.mem_subgroupOf, centralizerIn_eq, Subgroup.mem_inf, rho_eq_one_iff hρ hHM]
  exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩

theorem map_rho_ne_bot (hρ : IsConjModule p H M V e ρ) (hHM : M ≤ normalizer (H : Set G))
    (hUM : U ≤ M) (hCltU : centralizerIn U H < U) : (U.subgroupOf M).map ρ ≠ ⊥ := by
  intro hcon
  refine absurd (le_antisymm hCltU.le fun x hx => Subgroup.mem_inf.2 ⟨hx, ?_⟩) hCltU.ne
  have h1 : ρ ⟨x, hUM hx⟩ ∈ (U.subgroupOf M).map ρ :=
    Subgroup.mem_map.2 ⟨⟨x, hUM hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  rw [hcon, Subgroup.mem_bot] at h1
  exact (rho_eq_one_iff hρ hHM ⟨x, hUM hx⟩).1 h1

theorem natCard_fixedSubmodule_map (hρ : IsConjModule p H M V e ρ)
    (hHM : M ≤ normalizer (H : Set G)) {K : Subgroup G} (hK : K ≤ M) :
    Nat.card ↥(fixedSubmodule ((K.subgroupOf M).map ρ)) = Nat.card ↥(centralizerIn H K) := by
  have h1 : Nat.card ↥((centralizerIn H K).subgroupOf H) = Nat.card ↥(centralizerIn H K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (centralizerIn_le H K)).toEquiv
  rw [← h1]
  refine Nat.card_congr (Equiv.symm (Equiv.subtypeEquiv
    (e.toEquiv.trans (Multiplicative.toAdd (α := V))) fun x => ?_))
  rw [Subgroup.mem_subgroupOf, ← mem_fixedSubmodule_map_rho_iff hρ hHM hK x]
  rfl

theorem mem_normalizer_map_rho {w : G} (hwM : w ∈ M) (hw : w ∈ normalizer (U : Set G)) :
    ρ ⟨w, hwM⟩ ∈ normalizer (((U.subgroupOf M).map ρ : Subgroup (V ≃ₗ[ZMod p] V)) :
      Set (V ≃ₗ[ZMod p] V)) := by
  have key : ∀ x : G, ∀ hxM : x ∈ M, x ∈ normalizer (U : Set G) → ∀ g : V ≃ₗ[ZMod p] V,
      g ∈ (U.subgroupOf M).map ρ → ρ ⟨x, hxM⟩ * g * (ρ ⟨x, hxM⟩)⁻¹ ∈ (U.subgroupOf M).map ρ := by
    intro x hxM hx g hg
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hg
    have hconj : x * (a : G) * x⁻¹ ∈ U :=
      (Subgroup.mem_set_normalizer_iff.1 hx (a : G)).1 (Subgroup.mem_subgroupOf.1 ha)
    refine Subgroup.mem_map.2 ⟨⟨x, hxM⟩ * a * (⟨x, hxM⟩)⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    rw [Subgroup.mem_subgroupOf]
    simpa using hconj
  refine Subgroup.mem_normalizer_iff.2 fun g => ⟨fun hg => key w hwM hw g hg, fun hg => ?_⟩
  have h := key w⁻¹ (M.inv_mem hwM) ((normalizer (U : Set G)).inv_mem hw) _ hg
  rw [show (⟨w⁻¹, M.inv_mem hwM⟩ : ↥M) = (⟨w, hwM⟩ : ↥M)⁻¹ from rfl, map_inv] at h
  rwa [show (ρ ⟨w, hwM⟩)⁻¹ * (ρ ⟨w, hwM⟩ * g * (ρ ⟨w, hwM⟩)⁻¹) * ((ρ ⟨w, hwM⟩)⁻¹)⁻¹ = g by group]
    at h

theorem orderOf_rho_w (hρ : IsConjModule p H M V e ρ) (hHM : M ≤ normalizer (H : Set G))
    (hW₁M : W₁ ≤ M) (hCW : centralizerIn W₁ H = ⊥) {q : ℕ} (hqp : q.Prime)
    (hcardW : Nat.card ↥W₁ = q) {w : G} (hw : w ∈ W₁) (hw1 : w ≠ 1) :
    orderOf (ρ ⟨w, hW₁M hw⟩) = q := by
  have hne : ρ ⟨w, hW₁M hw⟩ ≠ 1 := fun hcon => by
    rw [rho_eq_one_iff hρ hHM] at hcon
    have hmem : w ∈ centralizerIn W₁ H := Subgroup.mem_inf.2 ⟨hw, hcon⟩
    rw [hCW, Subgroup.mem_bot] at hmem
    exact hw1 hmem
  have hpow : (⟨w, hW₁M hw⟩ : ↥M) ^ q = 1 := by
    have hmem : (⟨w, hW₁M hw⟩ : ↥M) ∈ W₁.subgroupOf M := Subgroup.mem_subgroupOf.2 hw
    have hcard : Nat.card ↥(W₁.subgroupOf M) = q := by
      rw [← hcardW]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW₁M).toEquiv
    have h1 : (⟨(⟨w, hW₁M hw⟩ : ↥M), hmem⟩ : ↥(W₁.subgroupOf M)) ^ q = 1 := by
      rw [← hcard]; exact pow_card_eq_one'
    exact congrArg (Subtype.val (p := fun y : ↥M => y ∈ W₁.subgroupOf M)) h1
  rcases hqp.eq_one_or_self_of_dvd _
      (orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hpow, map_one]) :
        orderOf (ρ ⟨w, hW₁M hw⟩) ∣ q) with h | h
  · exact absurd (orderOf_eq_one_iff.1 h) hne
  · exact h

end Realized

section Images

variable {G : Type*} [Group G] {M K : Subgroup G} {p : ℕ}
  {V : Type*} [AddCommGroup V] [Module (ZMod p) V] {ρ : ↥M →* (V ≃ₗ[ZMod p] V)}

theorem isMulCommutative_subgroupOf (hK : IsMulCommutative ↥K) :
    IsMulCommutative ↥(K.subgroupOf M) :=
  ⟨⟨fun x y => Subtype.ext (Subtype.ext (congrArg (Subtype.val (p := fun z : G => z ∈ K))
    (hK.is_comm.comm (⟨(x : ↥M), Subgroup.mem_subgroupOf.1 x.2⟩ : ↥K)
      ⟨(y : ↥M), Subgroup.mem_subgroupOf.1 y.2⟩)))⟩⟩

theorem isMulCommutative_map (hK : IsMulCommutative ↥K) :
    IsMulCommutative ↥((K.subgroupOf M).map ρ) := by
  have hKM := isMulCommutative_subgroupOf (M := M) hK
  refine ⟨⟨fun x y => ?_⟩⟩
  obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 x.2
  obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.1 y.2
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul, ← hax, ← hby, ← map_mul]
  have hab : a * b = b * a :=
    congrArg Subtype.val (hKM.is_comm.comm (⟨a, ha⟩ : ↥(K.subgroupOf M)) ⟨b, hb⟩)
  rw [hab]

theorem subgroupOf_eq_zpowers (hKM : K ≤ M) {w : G} (hw : w ∈ K) (hgen : zpowers w = K) :
    K.subgroupOf M = zpowers (⟨w, hKM hw⟩ : ↥M) := by
  refine le_antisymm (fun x hx => ?_)
    (by rw [Subgroup.zpowers_le, Subgroup.mem_subgroupOf]; exact hw)
  have h := Subgroup.mem_subgroupOf.1 hx
  rw [← hgen] at h
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h
  exact Subgroup.mem_zpowers_iff.2 ⟨n, Subtype.ext (by simpa using hn)⟩

theorem map_rho_eq_zpowers (hKM : K ≤ M) {w : G} (hw : w ∈ K) (hgen : zpowers w = K) :
    (K.subgroupOf M).map ρ = zpowers (ρ ⟨w, hKM hw⟩) := by
  rw [subgroupOf_eq_zpowers hKM hw hgen, MonoidHom.map_zpowers]

end Images

section ConfigFacts

variable {G : Type*} [Group G] [Finite G] {M U W₁ W₂ : Subgroup G}

theorem centralizerIn_W₁_hallCore_eq_bot (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    centralizerIn W₁ (hallCoreOf M) = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  obtain ⟨hxW, hxc⟩ := Subgroup.mem_inf.1 hx
  by_contra hx1
  rw [Subgroup.mem_bot] at hx1
  have h1 : (hallCoreOf M : Subgroup G) ≤ (⁅M, M⁆ : Subgroup G) ⊓ centralizer {x} :=
    le_inf hc.hallCore_le_commutator fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hxc y hy)
  rw [hc.inf_centralizer_eq_W₂ x hxW hx1] at h1
  exact hc.not_isCyclic_hallCore
    ((le_antisymm h1 hc.le_hallCore_W₂ : (hallCore ↥M).map M.subtype = W₂) ▸ hc.isCyclic_W₂)

omit [Finite G] in
private theorem sup_sup_eq_of {H : Subgroup G} (h1 : H ⊔ U = ⁅M, M⁆)
    (h2 : (⁅M, M⁆ : Subgroup G) ⊔ W₁ = M) : H ⊔ (U ⊔ W₁) = M := by
  rw [← h2, ← h1, sup_assoc]

theorem sup_hallCore_sup_eq (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    hallCoreOf M ⊔ (U ⊔ W₁) = M :=
  sup_sup_eq_of hc.sup_hallCore_E hc.sup_commutator_W₁

theorem card_W₂_ne_card_W₁ (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hqp : (Nat.card ↥W₁).Prime) : Nat.card ↥W₂ ≠ Nat.card ↥W₁ := fun h => by
  have hdvd : Nat.card ↥W₂ ∣ Nat.card ↥(⁅M, M⁆ : Subgroup G) :=
    Subgroup.card_dvd_of_le
      (hc.le_commutator_commutator_W₂.trans (Subgroup.commutator_le_self _))
  have hcop := hc.coprime_natCard_W₁_natCard_commutator
  rw [← h] at hcop
  exact hqp.one_lt.ne' (h ▸ hcop.eq_one_of_dvd hdvd)

end ConfigFacts

section FixedFree

variable {G : Type*} [Group G] {U W₁ : Subgroup G}

theorem centralizer_zpowers_eq {w : G} :
    centralizer ((zpowers w : Subgroup G) : Set G) = centralizer {w} := by
  refine le_antisymm (Subgroup.centralizer_le (by simp)) fun x hx => ?_
  refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  exact Commute.zpow_left (Commute.symm (Subgroup.mem_centralizer_singleton_iff.1 hx)) n

theorem fixedPointFree_conjOnNormalized (hW₁U : W₁ ≤ normalizer (U : Set G))
    (hfree : IsFixedPointFreeOn U W₁) {w : G} (hw : w ∈ W₁) (hw1 : w ≠ 1) :
    MonoidHom.FixedPointFree ((conjOnNormalized U hW₁U ⟨w, hw⟩ : MulAut ↥U) : ↥U → ↥U) := by
  intro x hx
  have hcoe : w * (x : G) * w⁻¹ = (x : G) := by
    have h := congrArg (Subtype.val (p := fun y : G => y ∈ U)) hx
    rwa [conjOnNormalized_apply_coe] at h
  have hcomm : (x : G) * w = w * (x : G) := by
    calc (x : G) * w = (w * (x : G) * w⁻¹) * w := by rw [hcoe]
      _ = w * (x : G) := by group
  have hmem : (x : G) ∈ centralizerIn U (zpowers w) :=
    Subgroup.mem_inf.2 ⟨x.2, by
      rw [centralizer_zpowers_eq]; exact Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩
  rw [hfree w hw hw1, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

theorem isInvariantSubgroup_subgroupOf {C : Subgroup G} (hW₁U : W₁ ≤ normalizer (U : Set G))
    (hnorm : W₁ ≤ normalizer (C : Set G)) :
    IsInvariantSubgroup (conjOnNormalized U hW₁U) (C.subgroupOf U) := by
  have key : ∀ b : ↥W₁, ∀ v : ↥U, (v : G) ∈ C →
      ((conjOnNormalized U hW₁U b v : ↥U) : G) ∈ C := by
    intro b v hv
    rw [conjOnNormalized_apply_coe]
    exact (Subgroup.mem_set_normalizer_iff.1 (hnorm b.2) (v : G)).1 hv
  rw [isInvariantSubgroup_iff_forall_map_eq]
  intro b
  refine le_antisymm ?_ ?_
  · rintro x ⟨v, hv, rfl⟩
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hv
    rw [Subgroup.mem_subgroupOf]
    exact key b v hv
  · intro v hv
    rw [Subgroup.mem_subgroupOf] at hv
    refine ⟨(conjOnNormalized U hW₁U b)⁻¹ v, ?_, ?_⟩
    · simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      have h1 : (((conjOnNormalized U hW₁U b)⁻¹ v : ↥U) : G)
          = ((conjOnNormalized U hW₁U b⁻¹ v : ↥U) : G) := by rw [map_inv]
      rw [h1]
      exact key b⁻¹ v hv
    · change conjOnNormalized U hW₁U b ((conjOnNormalized U hW₁U b)⁻¹ v) = v
      rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]

end FixedFree

section Centralizer

variable {G : Type*} [Group G] [Finite G] {M H U W₁ : Subgroup G} {p q : ℕ}
  {V : Type*} [AddCommGroup V] [Module (ZMod p) V] {e : ↥H ≃* Multiplicative V}
  {ρ : ↥M →* (V ≃ₗ[ZMod p] V)}

theorem inf_centralizer_map_rho_eq_bot [Group.IsSolvable ↥U]
    (hρ : IsConjModule p H M V e ρ) (hHM : M ≤ normalizer (H : Set G))
    (hUM : U ≤ M) (hW₁M : W₁ ≤ M) (hqp : q.Prime) (hcardW : Nat.card ↥W₁ = q)
    (hW₁U : W₁ ≤ normalizer (U : Set G)) (hfree : IsFixedPointFreeOn U W₁)
    (hnormC : U ≤ normalizer ((centralizerIn U H : Subgroup G) : Set G))
    {w : G} (hw : w ∈ W₁) (hw1 : w ≠ 1) (hgen : zpowers (⟨w, hw⟩ : ↥W₁) = ⊤)
    (hinv : IsInvariantSubgroup (conjOnNormalized U hW₁U) ((centralizerIn U H).subgroupOf U)) :
    (U.subgroupOf M).map ρ ⊓ centralizer {ρ ⟨w, hW₁M hw⟩} = ⊥ := by
  have hCnormal : ((centralizerIn U H).subgroupOf U).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hnormC
  refine le_antisymm (fun g hg => ?_) bot_le
  obtain ⟨hgD, hgc⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨y, hyU, rfl⟩ := Subgroup.mem_map.1 hgD
  set uu : ↥U := ⟨(y : G), Subgroup.mem_subgroupOf.1 hyU⟩ with huu
  have hcomm : ρ y * ρ ⟨w, hW₁M hw⟩ = ρ ⟨w, hW₁M hw⟩ * ρ y :=
    Subgroup.mem_centralizer_singleton_iff.1 hgc
  have hker : uu⁻¹ * conjOnNormalized U hW₁U ⟨w, hw⟩ uu ∈ (centralizerIn U H).subgroupOf U := by
    rw [mem_subgroupOf_centralizerIn_iff hρ hHM hUM]
    have key : (⟨((uu⁻¹ * conjOnNormalized U hW₁U ⟨w, hw⟩ uu : ↥U) : G),
        hUM (uu⁻¹ * conjOnNormalized U hW₁U ⟨w, hw⟩ uu).2⟩ : ↥M)
        = y⁻¹ * (⟨w, hW₁M hw⟩ * y * (⟨w, hW₁M hw⟩)⁻¹) := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_mul, Subgroup.coe_inv, conjOnNormalized_apply_coe]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rfl
    rw [key, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
    group
  have hfinal := mem_of_inv_mul_apply_mem hqp hcardW hgen
    (fixedPointFree_conjOnNormalized hW₁U hfree hw hw1) hinv hker
  rw [mem_subgroupOf_centralizerIn_iff hρ hHM hUM] at hfinal
  exact Subgroup.mem_bot.2 (by rw [← hfinal])

end Centralizer

section Model

theorem isSolvable_of_le {G : Type*} [Group G] {M U : Subgroup G} (hUM : U ≤ M)
    (h : Group.IsSolvable ↥M) : Group.IsSolvable ↥U :=
  Group.isSolvable_of_isSolvable_injective (G' := ↥M)
    (f := Subgroup.inclusion hUM) (Subgroup.inclusion_injective hUM)

variable {G : Type*} [Group G] [Finite G] {M U W₁ W₂ : Subgroup G} {p q : ℕ}
  [Fact p.Prime] [Fact q.Prime]
  {V : Type*} [AddCommGroup V] [Module (ZMod p) V] {e : ↥(hallCoreOf M) ≃* Multiplicative V}
  {ρ : ↥M →* (V ≃ₗ[ZMod p] V)}

theorem exists_linearSetup [Nontrivial V] (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hsolvM : Group.IsSolvable ↥M)
    (hρ : IsConjModule p (hallCoreOf M) M V e ρ) (hpq : p ≠ q)
    (hdimV : finrank (ZMod p) V = q) (hUab : IsMulCommutative ↥U)
    (hCltU : centralizerIn U (hallCoreOf M) < U)
    (hsup : hallCoreOf M ⊔ (U ⊔ W₁) = M)
    (hfree : IsFixedPointFreeOn U W₁)
    (hnormC : M ≤ normalizer ((centralizerIn U (hallCoreOf M) : Subgroup G) : Set G))
    (hmin : ∀ N : Subgroup G, N ≤ hallCoreOf M → M ≤ normalizer (N : Set G) →
      N = ⊥ ∨ N = hallCoreOf M)
    (hcardW : Nat.card ↥W₁ = q)
    (hfixdim : finrank (ZMod p) ↥(fixedSubmodule ((W₁.subgroupOf M).map ρ)) = 1)
    {w : G} (hw : w ∈ W₁) (hw1 : w ≠ 1) (hgen : zpowers w = W₁) (hwM : w ∈ M) :
    ∃ Dm : PrimeDimLinearSetup p q V,
      Dm.A = (U.subgroupOf M).map ρ ∧ Dm.b = ρ ⟨w, hwM⟩ := by
  have hHM : M ≤ normalizer ((hallCoreOf M : Subgroup G) : Set G) :=
    le_normalizer_map_subtype_hallCore M
  have hHle : (hallCoreOf M : Subgroup G) ≤ M := hallCoreOf_le M
  have hUM : U ≤ M := hc.le_M_E
  have hW₁M : W₁ ≤ M := hc.le_M_W₁
  have hHab : IsMulCommutative ↥(hallCoreOf M) :=
    ⟨⟨fun x y => e.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
  have hsolvU : Group.IsSolvable ↥U := isSolvable_of_le hUM hsolvM
  have hwMeq : ρ (⟨w, hW₁M hw⟩ : ↥M) = ρ ⟨w, hwM⟩ := rfl
  exact ⟨{ ne_char := hpq.symm
           finrank_eq := hdimV
           A := (U.subgroupOf M).map ρ
           b := ρ ⟨w, hW₁M hw⟩
           A_ne_bot := map_rho_ne_bot hρ hHM hUM hCltU
           isMulCommutative_A := isMulCommutative_map hUab
           orderOf_b := orderOf_rho_w hρ hHM hW₁M (centralizerIn_W₁_hallCore_eq_bot hc)
             Fact.out hcardW hw hw1
           b_mem_normalizer := mem_normalizer_map_rho (hW₁M hw) (hc.le_normalizer_E hw)
           isIrreducible_sup := by
             rw [← isIrreducibleLinear_iff, ← map_rho_eq_zpowers hW₁M hw hgen,
               ← range_rho_eq_sup hHle hHab hρ hHM hUM hW₁M hsup]
             exact isIrreducibleLinear_range hρ hHM hmin
           inf_centralizer_b := inf_centralizer_map_rho_eq_bot hρ hHM hUM hW₁M Fact.out hcardW
             hc.le_normalizer_E hfree (hUM.trans hnormC) hw hw1
             (by
               have h := subgroupOf_eq_zpowers (M := W₁) (K := W₁) le_rfl hw hgen
               rw [Subgroup.subgroupOf_self] at h
               exact h.symm)
             (isInvariantSubgroup_subgroupOf hc.le_normalizer_E (hW₁M.trans hnormC))
           finrank_invariants := by
             rw [← fixedSubmodule_eq_invariants, ← map_rho_eq_zpowers hW₁M hw hgen]
             exact hfixdim }, rfl, hwMeq⟩

end Model

section Alternatives

theorem zmodEquivFin_symm_finRotate (q : ℕ) [NeZero q] (i : Fin q) :
    (zmodEquivFin q).symm (finRotate q i) = (zmodEquivFin q).symm i + 1 := by
  rw [zmodEquivFin_symm_apply, zmodEquivFin_symm_apply, finRotate_apply, Fin.val_add,
    ZMod.natCast_mod]
  push_cast
  simp

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {V : Type v} [AddCommGroup V]
  [Module (ZMod p) V]

theorem reducible_alternative (Dm : PrimeDimLinearSetup p q V) {B : Subgroup (V ≃ₗ[ZMod p] V)}
    (hB : B = zpowers Dm.b) (hred : ActsReducibly Dm.A) :
    ∃ L : Fin q → Submodule (ZMod p) V,
      (∀ i, IsInvariantSubmodule Dm.A (L i)) ∧
      (∀ i, finrank (ZMod p) ↥(L i) = 1) ∧
      iSupIndep L ∧ (⨆ i, L i) = ⊤ ∧
      (∃ b ∈ B, ∀ i : Fin q, (L i).map (b : V ≃ₗ[ZMod p] V).toLinearMap = L (finRotate q i)) ∧
      (∃ a : ℕ, 1 < a ∧ a ∣ p - 1 ∧
        ∃ φ : ↥Dm.A →* (Fin (q - 1) → Multiplicative (ZMod a)), Function.Injective φ) ∧
      ∀ g ∈ Dm.A, ∃ c : Fin q → ZMod p,
        (∀ i, ∀ v ∈ L i, (g : V ≃ₗ[ZMod p] V) v = c i • v) ∧ ∏ i, c i = 1 := by
  classical
  have hq : q.Prime := Fact.out
  have hnz : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨L, m, hL1, hLinv, hLb, hLint, hm1, hmdvd, ⟨ψ, hψ⟩, hprod⟩ := Dm.reducible_model hred
  refine ⟨fun i => L ((zmodEquivFin q).symm i), fun i g hg v hv => ?_, fun i => hL1 _, ?_, ?_,
    ⟨Dm.b, hB ▸ Subgroup.mem_zpowers Dm.b, fun i => ?_⟩, ⟨m, hm1, hmdvd, ψ, hψ⟩, fun g hg => ?_⟩
  · have h1 : (g : V ≃ₗ[ZMod p] V) v ∈ L ((zmodEquivFin q).symm i) := by
      rw [← hLinv g hg ((zmodEquivFin q).symm i)]; exact Submodule.mem_map_of_mem hv
    exact h1
  · exact hLint.submodule_iSupIndep.comp (zmodEquivFin q).symm.injective
  · exact (Equiv.iSup_comp (g := L) (zmodEquivFin q).symm).trans hLint.submodule_iSup_eq_top
  · change (L ((zmodEquivFin q).symm i)).map _ = L ((zmodEquivFin q).symm (finRotate q i))
    rw [hLb, zmodEquivFin_symm_finRotate]
  · choose c hc using fun i => existsUnique_units_forall_apply_eq_smul (hL1 i) g (fun v hv => by
      rw [← hLinv g hg i]; exact Submodule.mem_map_of_mem hv)
    refine ⟨fun i => ((c ((zmodEquivFin q).symm i) : (ZMod p)ˣ) : ZMod p),
      fun i v hv => (hc _).1 v hv, ?_⟩
    have h1 := hprod g hg (fun i => ((c i : (ZMod p)ˣ) : ZMod p)) fun i v hv => (hc i).1 v hv
    rw [← h1]
    exact (Fintype.prod_equiv (zmodEquivFin q) (fun i => ((c i : (ZMod p)ˣ) : ZMod p))
      (fun i => ((c ((zmodEquivFin q).symm i) : (ZMod p)ˣ) : ZMod p)) (fun i => by simp)).symm

theorem apply_eq_self_of_mem_zpowers_linear {b : V ≃ₗ[ZMod p] V} {s : V} (hbs : b s = s)
    {g : V ≃ₗ[ZMod p] V} (hg : g ∈ zpowers b) : g s = s := by
  rw [← mem_invariants_zpowers_iff (b := b)] at hbs
  exact mem_invariants_linearGroupRep_iff.1 hbs g hg

theorem field_alternative (Dm : PrimeDimLinearSetup p q V) {B : Subgroup (V ≃ₗ[ZMod p] V)}
    (hB : B = zpowers Dm.b) [(linearGroupRep Dm.A).IsIrreducible]
    {u N : ℕ} (hu : u = Nat.card ↥Dm.A) (hN : N = (p ^ q - 1) / (p - 1)) :
    ∃ (E : Type v) (_ : Field E) (_ : Algebra (ZMod p) E), Nat.card E = p ^ q ∧
      ∃ φ : V ≃ₗ[ZMod p] E,
        (∃ v ∈ fixedSubmodule B, v ≠ 0 ∧ φ v = 1) ∧
        (∃ S : Subgroup Eˣ, IsCyclic ↥S ∧
          ∀ g : V ≃ₗ[ZMod p] V, g ∈ Dm.A ↔ ∃ s ∈ S, ∀ v : V, φ (g v) = (s : E) * φ v) ∧
        (∀ b : V ≃ₗ[ZMod p] V, b ∈ B ↔
          ∃ σ : E ≃ₐ[ZMod p] E, ∀ v : V, φ (b v) = σ (φ v)) ∧
        (fun v => φ v) '' (fixedSubmodule B : Set V) = Set.range (algebraMap (ZMod p) E) ∧
        Nat.Coprime u (p - 1) ∧ u ∣ N := by
  obtain ⟨s, hs0, hbs⟩ := Dm.exists_ne_zero_fixed
  have hfd := Dm.finiteDimensional
  obtain ⟨-, hcard, hs1, -, hact, hrange, himage, hcyc, hcop, hdvd⟩ :=
    Dm.irreducible_model hs0 hbs
  have hfixB : fixedSubmodule B = Representation.invariants (linearGroupRep (zpowers Dm.b)) := by
    rw [hB, fixedSubmodule_eq_invariants]
  set hBA := zpowers_le_normalizer (A := Dm.A) Dm.b_mem_normalizer with hBAdef
  refine ⟨↥(envelopingSubalgebra Dm.A), inferInstance, inferInstance, hcard,
    (evalEnvelopingSubalgebraEquiv (A := Dm.A) hs0).symm, ?_, ?_, ?_, ?_,
    hu ▸ hcop, hN ▸ hu ▸ hdvd⟩
  · exact ⟨s, by rw [hfixB]; exact mem_invariants_zpowers_iff.2 hbs, hs0, hs1⟩
  · refine ⟨(unitsHom Dm.A).range, isCyclic_of_surjective _
      (MonoidHom.rangeRestrict_surjective _), fun g => ⟨fun hg =>
        ⟨unitsHom Dm.A ⟨g, hg⟩, ⟨⟨g, hg⟩, rfl⟩, fun v => hact ⟨g, hg⟩ v⟩, ?_⟩⟩
    rintro ⟨t, ⟨a, rfl⟩, ht⟩
    have heq : g = (a : V ≃ₗ[ZMod p] V) :=
      LinearEquiv.ext fun v =>
        (evalEnvelopingSubalgebraEquiv (A := Dm.A) hs0).symm.injective (by
          rw [ht v, ← hact a v])
    rw [heq]
    exact a.2
  · intro b
    rw [hB]
    refine ⟨fun hb => ⟨conjEnveloping Dm.A (hBA hb), fun v =>
      symm_evalEnvelopingSubalgebraEquiv_apply hs0 (hBA hb)
        (apply_eq_self_of_mem_zpowers_linear hbs hb) v⟩, ?_⟩
    rintro ⟨σ, hσ⟩
    obtain ⟨b', hb'⟩ := (MonoidHom.mem_range (f := conjEnvelopingHomOfLE hBA)).1
      (hrange ▸ Subgroup.mem_top σ)
    have heq : b = (b' : V ≃ₗ[ZMod p] V) :=
      LinearEquiv.ext fun v =>
        (evalEnvelopingSubalgebraEquiv (A := Dm.A) hs0).symm.injective (by
          rw [hσ v, ← hb', conjEnvelopingHomOfLE_apply,
            ← symm_evalEnvelopingSubalgebraEquiv_apply hs0 (hBA b'.2)
              (apply_eq_self_of_mem_zpowers_linear hbs b'.2) v])
    rw [heq]
    exact b'.2
  · rw [hfixB]; exact himage

end Alternatives

theorem FNI_type_p_core_linear_alternative
    (h₁ : Statements.FNI_type_p_elementary_core_structure.{u}) :
    Statements.FNI_type_p_core_linear_alternative.{u, v} := by
  intro G _ _ hG M U W₁ W₂ hM hc p q uu N hp hq hu hN V _ _ e ρ hρ D B hD hB
  obtain ⟨-, hpp, hqp, -, -, hpq, -, hUab, -, -, -, hfreeUW,
    -, hcardH, -, hCHW, -, hmin, hCltU, hnormC, -, -, -, -⟩ :=
    h₁ G hG M U W₁ W₂ hM hc p q hp hq
  subst hD hB hu hN
  have hHM : M ≤ normalizer ((hallCoreOf M : Subgroup G) : Set G) :=
    le_normalizer_map_subtype_hallCore M
  have hHle : (hallCoreOf M : Subgroup G) ≤ M := hallCoreOf_le M
  have hUM : U ≤ M := hc.le_M_E
  have hW₁M : W₁ ≤ M := hc.le_M_W₁
  have hsolvM : Group.IsSolvable ↥M := hG.isSolvable_of_ne_top M hM.1
  have hfp : Fact p.Prime := ⟨hpp⟩
  have hfq : Fact q.Prime := ⟨hqp⟩
  have hHab : IsMulCommutative ↥(hallCoreOf M) :=
    ⟨⟨fun x y => e.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
  have hfinV : Finite V :=
    Finite.of_equiv ↥(hallCoreOf M) (e.toEquiv.trans (Multiplicative.toAdd (α := V)))
  have hdimV : finrank (ZMod p) V = q := by
    have hcV : Nat.card V = p ^ q := by
      rw [← hcardH]
      exact (Nat.card_congr (e.toEquiv.trans (Multiplicative.toAdd (α := V)))).symm
    have h := FiniteField.pow_finrank_eq_natCard p V
    rw [hcV] at h
    exact Nat.pow_right_injective hpp.two_le h
  have hfd : FiniteDimensional (ZMod p) V :=
    FiniteDimensional.of_finrank_pos (by rw [hdimV]; exact hqp.pos)
  have hntV : Nontrivial V :=
    Module.nontrivial_of_finrank_pos (R := ZMod p) (by rw [hdimV]; exact hqp.pos)
  obtain ⟨w, hw, hw1, hgen⟩ := exists_zpowers_eq_of_prime_natCard (hq ▸ hqp : (Nat.card ↥W₁).Prime)
  have hBeq : (W₁.subgroupOf M).map ρ = zpowers (ρ ⟨w, hW₁M hw⟩) :=
    map_rho_eq_zpowers hW₁M hw hgen
  have hfixdim : finrank (ZMod p) ↥(fixedSubmodule ((W₁.subgroupOf M).map ρ)) = 1 := by
    have hc2 : Nat.card ↥(fixedSubmodule ((W₁.subgroupOf M).map ρ)) = p := by
      rw [natCard_fixedSubmodule_map hρ hHM hW₁M, hCHW, hp]
    have hfin : Finite ↥(fixedSubmodule ((W₁.subgroupOf M).map ρ)) := Subtype.finite
    have hcc := FiniteField.pow_finrank_eq_natCard p
      ↥(fixedSubmodule ((W₁.subgroupOf M).map ρ))
    rw [hc2] at hcc
    refine Nat.pow_right_injective hpp.two_le
      (a₁ := finrank (ZMod p) ↥(fixedSubmodule ((W₁.subgroupOf M).map ρ))) (a₂ := 1) ?_
    simpa using hcc
  have hsup : hallCoreOf M ⊔ (U ⊔ W₁) = M := sup_hallCore_sup_eq hc
  obtain ⟨Dm, hDmA, hDmb⟩ := exists_linearSetup hc hsolvM hρ hpq hdimV hUab hCltU hsup hfreeUW
    hnormC hmin hq.symm hfixdim hw hw1 hgen (hW₁M hw)
  have hBDm : (W₁.subgroupOf M).map ρ = zpowers Dm.b := by rw [hDmb, hBeq]
  have hcardD : Nat.card ↥((U.subgroupOf M).map ρ)
      = (centralizerIn U (hallCoreOf M)).relIndex U := natCard_map_rho hρ hHM hUM
  have hcardDm : Nat.card ↥Dm.A = (centralizerIn U (hallCoreOf M)).relIndex U := by
    rw [hDmA]; exact hcardD
  have hudvd : (centralizerIn U (hallCoreOf M)).relIndex U ∣ Nat.card ↥U :=
    Subgroup.relIndex_dvd_card _ _
  have huodd : Odd ((centralizerIn U (hallCoreOf M)).relIndex U) :=
    Odd.of_dvd_nat hG.odd_natCard (hudvd.trans (Subgroup.card_subgroup_dvd_card U))
  have hucop : ((centralizerIn U (hallCoreOf M)).relIndex U).Coprime q := by
    refine Nat.Coprime.coprime_dvd_left hudvd ?_
    have h1 : (Nat.card ↥W₁).Coprime (Nat.card ↥U) :=
      (hc.coprime_natCard_W₁_natCard_commutator).coprime_dvd_right
        (Subgroup.card_dvd_of_le hc.le_commutator_E)
    exact (hq ▸ h1).symm
  have hxor := Dm.xor_actsReducibly_isIrreducible
  have hinfcent : (U.subgroupOf M).map ρ ⊓
      centralizer (((W₁.subgroupOf M).map ρ : Subgroup (V ≃ₗ[ZMod p] V)) :
        Set (V ≃ₗ[ZMod p] V)) = ⊥ := by
    rw [← hDmA, hBDm, centralizer_zpowers_eq]
    exact Dm.inf_centralizer_b
  have hirrsup : IsIrreducibleLinear ((U.subgroupOf M).map ρ ⊔ (W₁.subgroupOf M).map ρ) := by
    rw [← range_rho_eq_sup hHle hHab hρ hHM hUM hW₁M hsup]
    exact isIrreducibleLinear_range hρ hHM hmin
  refine ⟨map_rho_ne_bot hρ hHM hUM hCltU, isMulCommutative_map hUab, hcardD, huodd, hucop,
    by rw [hBeq, Nat.card_zpowers, orderOf_rho_w hρ hHM hW₁M
      (centralizerIn_W₁_hallCore_eq_bot hc) hqp hq.symm hw hw1],
    hinfcent, hfixdim, hirrsup, ?_, ?_⟩
  ·
    rcases hxor with ⟨hred, hirr⟩ | ⟨hirr, hred⟩
    · refine Or.inl ⟨⟨?_, ?_⟩, fun hcon => hirr (isIrreducibleLinear_iff.1 (hDmA ▸ hcon.1))⟩
      · rw [← hDmA]; exact actsReducibly_iff_not_isIrreducibleLinear.1 hred
      · rw [← hDmA, hBDm]; exact reducible_alternative Dm rfl hred
    · refine Or.inr ⟨⟨hDmA ▸ isIrreducibleLinear_iff.2 hirr, ?_⟩,
        fun hcon => hred (actsReducibly_iff_not_isIrreducibleLinear.2 (hDmA ▸ hcon.1))⟩
      rw [← hDmA, hBDm]
      exact field_alternative Dm rfl hcardDm.symm rfl
  ·
    rcases hxor with ⟨hred, -⟩ | ⟨hirr, -⟩
    ·
      obtain ⟨-, -, -, -, -, -, ⟨a, ha1, hadvd, φ, hφ⟩, -⟩ := reducible_alternative Dm
        (B := zpowers Dm.b) rfl hred
      have hane : NeZero a := ⟨by omega⟩
      have hcardle : Nat.card ↥Dm.A ≤ Nat.card (Fin (q - 1) → Multiplicative (ZMod a)) :=
        Nat.card_le_card_of_injective _ hφ
      have hcardfun : Nat.card (Fin (q - 1) → Multiplicative (ZMod a)) = a ^ (q - 1) := by
        simp [Nat.card_eq_fintype_card]
      calc (centralizerIn U (hallCoreOf M)).relIndex U = Nat.card ↥Dm.A := hcardDm.symm
        _ ≤ a ^ (q - 1) := hcardfun ▸ hcardle
        _ ≤ (p - 1) ^ (q - 1) :=
          Nat.pow_le_pow_left (Nat.le_of_dvd (by have := hpp.two_le; omega) hadvd) _
        _ ≤ (p ^ q - 1) / (p - 1) := natCardBound.sub_one_pow_le_div hpp.one_lt hqp.pos
    ·
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hdvd⟩ :=
        field_alternative (u := (centralizerIn U (hallCoreOf M)).relIndex U) Dm
          (B := zpowers Dm.b) rfl hcardDm.symm rfl
      exact Nat.le_of_dvd (natCardBound.one_le_div hpp.one_lt hqp.pos) hdvd

end

end CFSG.FeitThompson.Proofs
