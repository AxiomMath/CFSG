module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

def expProd {R : Type*} [CommGroup R] {k : ℕ} (x : Fin k → R) :
    Multiplicative (Fin k → ℤ) →* R where
  toFun e := ∏ i, x i ^ Multiplicative.toAdd e i
  map_one' := by simp
  map_mul' a b := by simp [zpow_add, Finset.prod_mul_distrib]

def redMod3 (k : ℕ) : Multiplicative (Fin k → ℤ) →* Multiplicative (Fin k → ZMod 3) where
  toFun e := Multiplicative.ofAdd fun i => ((Multiplicative.toAdd e i : ℤ) : ZMod 3)
  map_one' := by
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
    congr 1
  map_mul' a b := by
    rw [← ofAdd_add]
    congr 1
    funext i
    simp

theorem pow_three_eq_one (k : ℕ) (v : Multiplicative (Fin k → ZMod 3)) : v ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  have h3 : ∀ a : ZMod 3, (3 : ℕ) • a = 0 := by decide
  rw [toAdd_pow, toAdd_one]
  funext i
  exact h3 _

theorem redMod3_surjective (k : ℕ) : Function.Surjective (redMod3 k) := by
  intro v
  refine ⟨Multiplicative.ofAdd fun i => ((Multiplicative.toAdd v i).val : ℤ), ?_⟩
  simp [redMod3, ZMod.natCast_zmod_val]

theorem card_zmod_three_pow (k : ℕ) :
    Nat.card (Multiplicative (Fin k → ZMod 3)) = 3 ^ k := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_le_card_ker_pow_three {H V : Type*} [CommGroup H] [Finite H] [Group V]
    (f : H →* V) (hf : Function.Surjective f) (hV : ∀ v : V, v ^ 3 = 1) :
    Nat.card V ≤ Nat.card (powMonoidHom 3 : H →* H).ker := by
  have h1 := Subgroup.card_ker_mul_card_range (powMonoidHom 3 : H →* H)
  have h2 := Subgroup.card_ker_mul_card_range f
  have h3 : Nat.card f.range = Nat.card V := by
    rw [MonoidHom.range_eq_top.mpr hf, Subgroup.card_top]
  have hle : (powMonoidHom 3 : H →* H).range ≤ f.ker := by
    intro y hy
    obtain ⟨h, rfl⟩ := MonoidHom.mem_range.mp hy
    rw [MonoidHom.mem_ker, powMonoidHom_apply, map_pow]
    exact hV _
  have h4 : Nat.card (powMonoidHom 3 : H →* H).range ≤ Nat.card f.ker :=
    Subgroup.card_le_of_le hle
  have hpos : 0 < Nat.card (powMonoidHom 3 : H →* H).range := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card V * Nat.card (powMonoidHom 3 : H →* H).range
      ≤ Nat.card V * Nat.card f.ker := Nat.mul_le_mul_left _ h4
    _ = Nat.card f.ker * Nat.card f.range := by rw [h3, mul_comm]
    _ = Nat.card H := h2
    _ = Nat.card (powMonoidHom 3 : H →* H).ker * Nat.card (powMonoidHom 3 : H →* H).range :=
      h1.symm

theorem exists_elemAbelian_card_ge_pow {R : Type*} [CommGroup R] [Finite R] {k : ℕ}
    (x : Fin k → R) (hrel : ∀ e : Fin k → ℤ, ∏ i, x i ^ e i = 1 → ∀ i, (3 : ℤ) ∣ e i) :
    ∃ E : Subgroup R, (∀ r ∈ E, r ^ 3 = 1) ∧ E ≤ Subgroup.closure (Set.range x) ∧
      3 ^ k ≤ Nat.card E := by
  have hmem : ∀ e : Multiplicative (Fin k → ℤ), expProd x e ∈ Subgroup.closure (Set.range x) := by
    intro e
    show (∏ i, x i ^ Multiplicative.toAdd e i) ∈ Subgroup.closure (Set.range x)
    exact Subgroup.prod_mem _ fun i _ =>
      Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_range_self i)) _
  have hinj : Function.Injective (QuotientGroup.kerLift (expProd x)) :=
    QuotientGroup.kerLift_injective _
  haveI : Finite (Multiplicative (Fin k → ℤ) ⧸ (expProd x).ker) := Finite.of_injective _ hinj
  have hle : (expProd x).ker ≤ (redMod3 k).ker := by
    intro e he
    rw [MonoidHom.mem_ker] at he ⊢
    have hd := hrel (Multiplicative.toAdd e) he
    show Multiplicative.ofAdd (fun i => ((Multiplicative.toAdd e i : ℤ) : ZMod 3)) =
      Multiplicative.ofAdd 0
    congr 1
    funext i
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (by exact_mod_cast hd i)
  let f : Multiplicative (Fin k → ℤ) ⧸ (expProd x).ker →* Multiplicative (Fin k → ZMod 3) :=
    QuotientGroup.lift (expProd x).ker (redMod3 k) hle
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨e, he⟩ := redMod3_surjective k v
    exact ⟨(e : Multiplicative (Fin k → ℤ) ⧸ (expProd x).ker), he⟩
  have hcard := card_le_card_ker_pow_three f hf (pow_three_eq_one k)
  rw [card_zmod_three_pow] at hcard
  refine ⟨((powMonoidHom 3 : Multiplicative (Fin k → ℤ) ⧸ (expProd x).ker →* _).ker).map
    (QuotientGroup.kerLift (expProd x)), ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hr
    rw [MonoidHom.mem_ker, powMonoidHom_apply] at hh
    rw [← map_pow, hh, map_one]
  · intro r hr
    obtain ⟨h, _, rfl⟩ := Subgroup.mem_map.mp hr
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective h
    rw [QuotientGroup.kerLift_mk]
    exact hmem e
  · rw [Subgroup.card_map_of_injective hinj]
    exact hcard

open scoped IsMulCommutative in
theorem exists_elemAbelian_of_commute {G : Type*} [Group G] [Finite G] {k : ℕ} (x : Fin k → G)
    (hc : ∀ i j, x i * x j = x j * x i)
    (hrel : ∀ e : Fin k → ℤ, (List.ofFn fun i => x i ^ e i).prod = 1 → ∀ i, (3 : ℤ) ∣ e i) :
    ∃ E : Subgroup G, (∀ g ∈ E, g ^ 3 = 1) ∧ E ≤ Subgroup.closure (Set.range x) ∧
      3 ^ k ≤ Nat.card E := by
  have hcomm : IsMulCommutative (Subgroup.closure (Set.range x)) := by
    apply Subgroup.isMulCommutative_closure
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hc i j
  let y : Fin k → Subgroup.closure (Set.range x) :=
    fun i => ⟨x i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hprod : ∀ e : Fin k → ℤ,
      ((∏ i, y i ^ e i : Subgroup.closure (Set.range x)) : G) =
        (List.ofFn fun i => x i ^ e i).prod := by
    intro e
    rw [← List.prod_ofFn]
    have h := map_list_prod (Subgroup.closure (Set.range x)).subtype
      (List.ofFn fun i => y i ^ e i)
    rw [List.map_ofFn] at h
    exact h
  have hrelK : ∀ e : Fin k → ℤ, ∏ i, y i ^ e i = 1 → ∀ i, (3 : ℤ) ∣ e i := by
    intro e he
    apply hrel e
    rw [← hprod e, he]
    rfl
  obtain ⟨E, hE3, -, hcard⟩ := exists_elemAbelian_card_ge_pow y hrelK
  refine ⟨E.map (Subgroup.closure (Set.range x)).subtype, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hg
    rw [← map_pow, hE3 s hs, map_one]
  · intro g hg
    obtain ⟨s, _, rfl⟩ := Subgroup.mem_map.mp hg
    exact s.2
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact hcard

theorem comm_pair_identity {X : Type*} [Group X] (a b A B : X) (hab : a * b = b * a)
    (hAb : A * b = b * A) : (b⁻¹ * a⁻¹) * (A * B) = (a⁻¹ * A) * (b⁻¹ * B) := by
  have h1 : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ := (Commute.inv_inv (show Commute a b from hab)).symm
  have h2 : A * b⁻¹ = b⁻¹ * A := Commute.inv_right (show Commute A b from hAb)
  calc (b⁻¹ * a⁻¹) * (A * B) = a⁻¹ * (b⁻¹ * (A * B)) := by rw [h1, mul_assoc]
    _ = a⁻¹ * (A * (b⁻¹ * B)) := by rw [← mul_assoc b⁻¹ A B, ← h2, mul_assoc A b⁻¹ B]
    _ = (a⁻¹ * A) * (b⁻¹ * B) := by rw [mul_assoc]

theorem card_inf_centralizer_le {X : Type*} [Group X] [Finite X] (x : X) (Z Z₀ : Subgroup X)
    (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hinv : ∀ a ∈ Z, x⁻¹ * a * x ∈ Z)
    (hgen : ∀ a ∈ Z, ∃ z ∈ Z₀, ∃ d ∈ Z, a = z * (d⁻¹ * (x⁻¹ * d * x))) :
    Nat.card ↥(Z ⊓ Subgroup.centralizer ({x} : Set X)) ≤ Nat.card Z₀ := by
  have hε : ∀ d ∈ Z, d⁻¹ * (x⁻¹ * d * x) ∈ Z := fun d hd =>
    Z.mul_mem (Z.inv_mem hd) (hinv d hd)
  let ε : Z →* Z := MonoidHom.mk'
    (fun d => ⟨(d : X)⁻¹ * (x⁻¹ * (d : X) * x), hε d d.2⟩) (by
      intro a b
      apply Subtype.ext
      have e1 : ((a * b : Z) : X)⁻¹ * (x⁻¹ * ((a * b : Z) : X) * x) =
          ((b : X)⁻¹ * (a : X)⁻¹) * ((x⁻¹ * (a : X) * x) * (x⁻¹ * (b : X) * x)) := by
        rw [Subgroup.coe_mul]
        group
      show ((a * b : Z) : X)⁻¹ * (x⁻¹ * ((a * b : Z) : X) * x) = _
      rw [e1, comm_pair_identity (a : X) (b : X) _ _ (hZ _ a.2 _ b.2)
        (hZ _ (hinv _ a.2) _ b.2)]
      rfl)
  have hε1 : ∀ d : Z, ((ε d : Z) : X) = (d : X)⁻¹ * (x⁻¹ * (d : X) * x) := fun _ => rfl
  have hsurj : Function.Surjective
      (fun p : (Z₀ ⊓ Z : Subgroup X) × ε.range =>
        (⟨(p.1 : X) * ((p.2 : Z) : X),
          Z.mul_mem (Subgroup.mem_inf.mp p.1.2).2 (p.2 : Z).2⟩ : Z)) := by
    intro a
    obtain ⟨z, hz₀, d, hd, hza⟩ := hgen (a : X) a.2
    have hzZ : z ∈ Z := by
      have hz : z = (a : X) * ((ε ⟨d, hd⟩ : Z) : X)⁻¹ := by
        rw [hε1, hza]
        group
      rw [hz]
      exact Z.mul_mem a.2 (Z.inv_mem (ε ⟨d, hd⟩).2)
    refine ⟨(⟨⟨z, Subgroup.mem_inf.mpr ⟨hz₀, hzZ⟩⟩,
      ⟨ε ⟨d, hd⟩, MonoidHom.mem_range.mpr ⟨⟨d, hd⟩, rfl⟩⟩⟩), ?_⟩
    apply Subtype.ext
    show z * ((ε ⟨d, hd⟩ : Z) : X) = (a : X)
    rw [hε1, hza]
  have hpos : 0 < Nat.card ε.range := Nat.card_pos
  have hZle : Nat.card Z ≤ Nat.card (Z₀ ⊓ Z : Subgroup X) * Nat.card ε.range := by
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_surjective _ hsurj
  have hker := Subgroup.card_ker_mul_card_range ε
  have hkerle : Nat.card ε.ker ≤ Nat.card (Z₀ ⊓ Z : Subgroup X) := by
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    rw [hker]
    exact hZle
  have hmap : ε.ker.map Z.subtype = Z ⊓ Subgroup.centralizer ({x} : Set X) := by
    ext y
    rw [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨d, hd, rfl⟩
      rw [MonoidHom.mem_ker] at hd
      have h' : (d : X)⁻¹ * (x⁻¹ * (d : X) * x) = 1 := congrArg Subtype.val hd
      have h2 : (d : X) = x⁻¹ * (d : X) * x := inv_mul_eq_one.mp h'
      refine ⟨d.2, ?_⟩
      calc (d : X) * x = x * (x⁻¹ * (d : X) * x) := by group
        _ = x * (d : X) := by rw [← h2]
    · rintro ⟨hy, hyx⟩
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      have h2 : x⁻¹ * y * x = y := by
        calc x⁻¹ * y * x = x⁻¹ * (y * x) := mul_assoc _ _ _
          _ = x⁻¹ * (x * y) := by rw [hyx]
          _ = y := inv_mul_cancel_left x y
      show (y : X)⁻¹ * (x⁻¹ * y * x) = 1
      rw [h2, inv_mul_cancel]
  have hcardeq : Nat.card ↥(Z ⊓ Subgroup.centralizer ({x} : Set X)) = Nat.card ε.ker := by
    rw [← hmap, Subgroup.card_map_of_injective (Subgroup.subtype_injective Z)]
  calc Nat.card ↥(Z ⊓ Subgroup.centralizer ({x} : Set X)) = Nat.card ε.ker := hcardeq
    _ ≤ Nat.card (Z₀ ⊓ Z : Subgroup X) := hkerle
    _ ≤ Nat.card Z₀ := Subgroup.card_le_of_le inf_le_left

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
