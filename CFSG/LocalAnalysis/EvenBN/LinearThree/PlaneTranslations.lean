module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.PlaneDesign
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Equiv Matrix
open scoped MatrixGroups

namespace Plane

section Algebra

variable {k : Type*} [Field k]

abbrev slPerm : SL(2, k) →* Perm (Fin 2 → k) := MulAction.toPermHom SL(2, k) (Fin 2 → k)

theorem slPerm_apply (M : SL(2, k)) (v : Fin 2 → k) :
    slPerm M v = (M : Matrix (Fin 2) (Fin 2) k) *ᵥ v :=
  rfl

theorem vec_ext {α : Type*} {x y : Fin 2 → α} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  funext i
  fin_cases i
  · exact h0
  · exact h1

theorem sl_smul_smul (M : SL(2, k)) (a : k) (v : Fin 2 → k) : M • (a • v) = a • (M • v) :=
  Matrix.mulVec_smul _ _ _

@[expose] def axisLine (k : Type*) [Field k] : Set (Fin 2 → k) := {v | v 1 = 0}

@[expose] def kLine (v : Fin 2 → k) : Set (Fin 2 → k) := {w | ∃ a : k, w = a • v}

theorem eq_smul_e₁ {v : Fin 2 → k} (hv : v ∈ axisLine k) : v = v 0 • ![1, 0] :=
  vec_ext (by simp) (by simpa [axisLine] using hv)

theorem smul_e₁_mem (a : k) : a • ![(1 : k), 0] ∈ axisLine k := by
  simp [axisLine]

@[expose] def rootSL (a : k) : SL(2, k) :=
  ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem rootSL_smul (a : k) (v : Fin 2 → k) : rootSL a • v = ![v 0 + a * v 1, v 1] := by
  refine vec_ext ?_ ?_ <;>
    simp [rootSL, Matrix.SpecialLinearGroup.coe_mk, HSMul.hSMul, SMul.smul, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]

theorem rootSL_add (a b : k) : rootSL (a + b) = rootSL a * rootSL b := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [rootSL, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem rootSL_zero : rootSL (0 : k) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootSL]

@[expose] def rootHom : Multiplicative k →* SL(2, k) where
  toFun a := rootSL (Multiplicative.toAdd a)
  map_one' := rootSL_zero
  map_mul' _ _ := rootSL_add _ _

theorem rootSL_smul_of_mem {a : k} {v : Fin 2 → k} (hv : v ∈ axisLine k) : rootSL a • v = v := by
  rw [rootSL_smul]
  exact vec_ext (by simp [show v 1 = 0 from hv]) (by simp)

theorem mem_axisLine_of_rootSL_one {v : Fin 2 → k} (hv : rootSL (1 : k) • v = v) :
    v ∈ axisLine k := by
  have h0 := congrFun hv 0
  rw [rootSL_smul] at h0
  show v 1 = 0
  simpa using h0

theorem exists_sl_smul_e₁ {v : Fin 2 → k} (hv : v ≠ 0) : ∃ M : SL(2, k), M • ![1, 0] = v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := fun h1 => hv (vec_ext (by simp [h0]) (by simp [h1]))
    refine ⟨⟨!![0, -(v 1)⁻¹; v 1, 0], by simp [Matrix.det_fin_two, h1]⟩, ?_⟩
    refine vec_ext ?_ ?_ <;>
      simp [HSMul.hSMul, SMul.smul, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0]
  · refine ⟨⟨!![v 0, 0; v 1, (v 0)⁻¹], by simp [Matrix.det_fin_two, h0]⟩, ?_⟩
    refine vec_ext ?_ ?_ <;>
      simp [HSMul.hSMul, SMul.smul, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_sl_smul {v w : Fin 2 → k} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ M : SL(2, k), M • v = w := by
  obtain ⟨A, hA⟩ := exists_sl_smul_e₁ hv
  obtain ⟨B, hB⟩ := exists_sl_smul_e₁ hw
  refine ⟨B * A⁻¹, ?_⟩
  rw [mul_smul, ← hA, inv_smul_smul, hB]

theorem sl_smul_of_fix {M : SL(2, k)} {b : Fin 2 → k} (hb : b ∈ axisLine k) (hb0 : b ≠ 0)
    (hM : M • b = b) {v : Fin 2 → k} (hv : v ∈ axisLine k) : M • v = v := by
  have hb00 : b 0 ≠ 0 := fun h => hb0 (vec_ext (by simp [h]) (by simpa [axisLine] using hb))
  have he : M • ![(1 : k), 0] = ![1, 0] := by
    rw [eq_smul_e₁ hb, sl_smul_smul] at hM
    exact smul_right_injective _ hb00 hM
  rw [eq_smul_e₁ hv, sl_smul_smul, he]

theorem image_axisLine (M : SL(2, k)) :
    (slPerm M : (Fin 2 → k) → (Fin 2 → k)) '' axisLine k = kLine (M • ![1, 0]) := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v 0, by rw [slPerm_apply, ← sl_smul_smul]; exact congrArg _ (eq_smul_e₁ hv)⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a • ![1, 0], smul_e₁_mem a, sl_smul_smul M a _⟩

theorem mem_kLine_self (v : Fin 2 → k) : v ∈ kLine v := ⟨1, (one_smul k v).symm⟩

theorem zero_mem_kLine (v : Fin 2 → k) : (0 : Fin 2 → k) ∈ kLine v := ⟨0, (zero_smul k v).symm⟩

theorem sub_mem_kLine {v x y : Fin 2 → k} (hx : x ∈ kLine v) (hy : y ∈ kLine v) :
    x - y ∈ kLine v := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a - b, (sub_smul a b v).symm⟩

theorem add_mem_kLine {v x y : Fin 2 → k} (hx : x ∈ kLine v) (hy : y ∈ kLine v) :
    x + y ∈ kLine v := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, (add_smul a b v).symm⟩

theorem kLine_eq_of_mem {v x : Fin 2 → k} (hx : x ∈ kLine v) (hx0 : x ≠ 0) :
    kLine x = kLine v := by
  obtain ⟨a, rfl⟩ := hx
  have ha : a ≠ 0 := fun h => hx0 (by rw [h, zero_smul])
  ext w
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b * a, by rw [smul_smul]⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b * a⁻¹, by rw [smul_smul, mul_assoc, inv_mul_cancel₀ ha, mul_one]⟩

end Algebra

theorem exists_mem_sylow_smul_eq {H X : Type*} [Group H] [Finite H] [MulAction H X] [Finite X]
    {p n : ℕ} [hp : Fact p.Prime] (P : Sylow p H) (hX : Nat.card X = p ^ n) {x : X}
    (htr : ∀ y : X, ∃ h : H, h • x = y) (y : X) : ∃ g ∈ (P : Subgroup H), g • x = y := by
  have horb : MulAction.orbit H x = Set.univ := Set.eq_univ_of_forall fun y => htr y
  have hS : (MulAction.stabilizer H x).index = p ^ n := by
    rw [MulAction.index_stabilizer, horb, Set.ncard_univ, hX]
  set P₀ := (P : Subgroup H) ⊓ MulAction.stabilizer H x with hP₀
  have h1 : p ^ n ∣ P₀.index := hS ▸ Subgroup.index_dvd_of_le inf_le_right
  have h2 : P₀.relIndex P * (P : Subgroup H).index = P₀.index :=
    Subgroup.relIndex_mul_index inf_le_left
  have hcop : Nat.Coprime (p ^ n) (P : Subgroup H).index :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr P.not_dvd_index)
  have h3 : p ^ n ∣ P₀.relIndex P := hcop.dvd_of_dvd_mul_right (h2 ▸ h1)
  have h4 : P₀.relIndex P = (MulAction.orbit (P : Subgroup H) x).ncard := by
    rw [← MulAction.index_stabilizer, Subgroup.relIndex]
    congr 1
    ext g
    simp [hP₀, MulAction.mem_stabilizer_iff]
  have h5 : (MulAction.orbit (P : Subgroup H) x).ncard ≤ p ^ n := by
    rw [← hX, ← Set.ncard_univ]
    exact Set.ncard_le_ncard (Set.subset_univ _)
  have h6 : 0 < (MulAction.orbit (P : Subgroup H) x).ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨x, MulAction.mem_orbit_self x⟩
  have h7 : (MulAction.orbit (P : Subgroup H) x).ncard = p ^ n :=
    le_antisymm h5 (Nat.le_of_dvd h6 (h4 ▸ h3))
  have horbP : MulAction.orbit (P : Subgroup H) x = Set.univ :=
    Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by rw [Set.ncard_univ, hX, h7])
      (Set.toFinite _)
  have hy : y ∈ MulAction.orbit (P : Subgroup H) x := horbP ▸ Set.mem_univ y
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hy
  exact ⟨g, g.2, hg⟩

section Natural

variable {k : Type*} [Field k] [Fintype k]

structure NaturalAffine (Γ : Subgroup (Perm (Fin 2 → k))) : Prop where
  affine : ∀ γ ∈ Γ, ∀ v w, γ (v + w) + γ 0 = γ v + γ w
  sl_mem : ∀ M : SL(2, k), slPerm M ∈ Γ
  sl_normal : ∀ δ ∈ Γ, δ 0 = 0 → ∀ M : SL(2, k), ∃ M' : SL(2, k),
    δ⁻¹ * slPerm M * δ = slPerm M'
  line : ∀ c : k, ∃ σ ∈ Γ, (∀ v ∈ axisLine k, σ v ∈ axisLine k) ∧ σ 0 = ![c, 0]

omit [Fintype k] in
theorem ncard_axisLine [Finite k] : (axisLine k).ncard = Nat.card k := by
  have : axisLine k = Set.range (fun a : k => a • ![(1 : k), 0]) := by
    ext v
    constructor
    · intro hv
      exact ⟨v 0, (eq_smul_e₁ hv).symm⟩
    · rintro ⟨a, rfl⟩
      exact smul_e₁_mem a
  rw [this, Set.ncard_range_of_injective]
  intro a b hab
  simpa using congrFun hab 0

theorem image_axisLine_eq {σ : Perm (Fin 2 → k)} (h : ∀ v ∈ axisLine k, σ v ∈ axisLine k) :
    (σ : (Fin 2 → k) → (Fin 2 → k)) '' axisLine k = axisLine k :=
  Set.eq_of_subset_of_ncard_le (by rintro _ ⟨v, hv, rfl⟩; exact h v hv)
    (by rw [Set.ncard_image_of_injective _ σ.injective]) (Set.toFinite _)

namespace NaturalAffine

variable {Γ : Subgroup (Perm (Fin 2 → k))}

theorem spread (h : NaturalAffine Γ) {δ : Perm (Fin 2 → k)} (hδ : δ ∈ Γ) (hδ0 : δ 0 = 0)
    {b : Fin 2 → k} (hb : b ∈ axisLine k) (hb0 : b ≠ 0) (hδb : δ b ∈ axisLine k) :
    (δ : (Fin 2 → k) → (Fin 2 → k)) '' axisLine k = axisLine k := by
  obtain ⟨M', hM'⟩ := h.sl_normal δ hδ hδ0 (rootSL 1)
  have key : ∀ v, δ⁻¹ (rootSL (1 : k) • δ v) = M' • v := fun v =>
    congrArg (fun f : Perm (Fin 2 → k) => f v) hM'
  have hM'b : M' • b = b := by
    rw [← key, rootSL_smul_of_mem hδb]
    simp
  refine image_axisLine_eq fun v hv => mem_axisLine_of_rootSL_one ?_
  have := key v
  rw [sl_smul_of_fix hb hb0 hM'b hv, Perm.inv_eq_iff_eq] at this
  exact this

omit [Fintype k] in
theorem trans (h : NaturalAffine Γ) (v : Fin 2 → k) : ∃ γ ∈ Γ, γ 0 = v := by
  by_cases hv : v = 0
  · exact ⟨1, one_mem Γ, by rw [hv, Perm.one_apply]⟩
  obtain ⟨σ, hσ, -, hσ0⟩ := h.line 1
  obtain ⟨M, hM⟩ := exists_sl_smul_e₁ hv
  exact ⟨slPerm M * σ, mul_mem (h.sl_mem M) hσ, by rw [Perm.mul_apply, hσ0]; exact hM⟩

theorem stab (h : NaturalAffine Γ) {a : Fin 2 → k} (ha : a ∈ axisLine k) :
    ∃ σ ∈ Γ, (σ : (Fin 2 → k) → (Fin 2 → k)) '' axisLine k = axisLine k ∧ σ 0 = a := by
  obtain ⟨σ, hσ, hmaps, hσ0⟩ := h.line (a 0)
  refine ⟨σ, hσ, image_axisLine_eq hmaps, ?_⟩
  rw [hσ0]
  exact vec_ext (by simp) (by simpa [axisLine] using ha.symm)

theorem goodLineQ (h : NaturalAffine Γ) :
    GoodLineQ Γ (axisLine k) 0 (Fintype.card k) where
  one_lt := Fintype.one_lt_card
  card := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := k), Nat.card_eq_fintype_card (α := Fin 2),
      Fintype.card_fin]
  mem := by simp [axisLine]
  ncard := by rw [ncard_axisLine, Nat.card_eq_fintype_card]
  trans₂ := fun _ _ _ _ hx hy => exists_two_trans h.trans (fun x y hx hy => by
    obtain ⟨M, hM⟩ := exists_sl_smul hx hy
    exact ⟨slPerm M, h.sl_mem M, by simp, hM⟩) hx hy
  stab := fun _ ha => h.stab ha
  spread := fun _ hδ hδ0 _ hb hb0 hδb => h.spread hδ hδ0 hb hb0 hδb

omit [Fintype k] in
theorem kLine_mem (h : NaturalAffine Γ) {v : Fin 2 → k} (hv : v ≠ 0) :
    kLine v ∈ orbitLines Γ (axisLine k) := by
  obtain ⟨M, hM⟩ := exists_sl_smul_e₁ hv
  exact ⟨slPerm M, h.sl_mem M, by rw [image_axisLine, hM]⟩

theorem zero_mem_of_kLine (h : NaturalAffine Γ) {L : Set (Fin 2 → k)}
    (hL : L ∈ orbitLines Γ (axisLine k)) {v : Fin 2 → k} (hv : v ≠ 0) {x y : Fin 2 → k}
    (hxy : x ≠ y) (hx : x ∈ kLine v) (hy : y ∈ kLine v) (hxL : x ∈ L) (hyL : y ∈ L) :
    (0 : Fin 2 → k) ∈ L := by
  rw [← h.goodLineQ.eq_of_mem (h.kLine_mem hv) hL hxy hx hy hxL hyL]
  exact zero_mem_kLine v

theorem eq_kLine_of_zero_mem (h : NaturalAffine Γ) {L : Set (Fin 2 → k)}
    (hL : L ∈ orbitLines Γ (axisLine k)) (h0 : (0 : Fin 2 → k) ∈ L) {x : Fin 2 → k} (hx : x ∈ L)
    (hx0 : x ≠ 0) : L = kLine x :=
  h.goodLineQ.eq_of_mem hL (h.kLine_mem hx0) (Ne.symm hx0) h0 hx (zero_mem_kLine x)
    (mem_kLine_self x)

theorem linear_part_mem_kLine (h : NaturalAffine Γ) {γ : Perm (Fin 2 → k)} (hγ : γ ∈ Γ)
    {v : Fin 2 → k} (hv : v ∈ axisLine k) : γ v - γ 0 ∈ kLine (γ ![1, 0] - γ 0) := by
  have hG := h.goodLineQ
  have he₁ : ![(1 : k), 0] ∈ axisLine k := by simp [axisLine]
  have h0 : (0 : Fin 2 → k) ∈ axisLine k := by simp [axisLine]
  have hd₁ : γ ![1, 0] - γ 0 ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h' => by simpa using congrFun (γ.injective h') 0
  set M := (γ : (Fin 2 → k) → (Fin 2 → k)) '' axisLine k with hM
  have hML : M ∈ orbitLines Γ (axisLine k) := image_mem_orbitLines hγ
  have hγ0 : γ 0 ∈ M := ⟨0, h0, rfl⟩
  have hγe : γ ![1, 0] ∈ M := ⟨_, he₁, rfl⟩
  have hγv : γ v ∈ M := ⟨v, hv, rfl⟩
  by_cases hM0 : (0 : Fin 2 → k) ∈ M
  ·
    obtain ⟨x, hxM, hx0⟩ : ∃ x ∈ M, x ≠ 0 := by
      by_cases h' : γ 0 = 0
      · refine ⟨γ ![1, 0], hγe, fun h'' => ?_⟩
        have := congrFun (γ.injective (h''.trans h'.symm)) 0
        simp at this
      · exact ⟨γ 0, hγ0, h'⟩
    have hMx := h.eq_kLine_of_zero_mem hML hM0 hxM hx0
    rw [hMx] at hγ0 hγe hγv
    rw [kLine_eq_of_mem (sub_mem_kLine hγe hγ0) hd₁]
    exact sub_mem_kLine hγv hγ0
  ·
    obtain ⟨Λ, ⟨hΛ, hΛ0, hΛM⟩, hΛu⟩ := hG.existsUnique_parallel hML hM0
    have htr : ∀ w ∈ axisLine k, ∀ x ∈ M, x + (γ w - γ 0) ∈ M := by
      rintro w hw _ ⟨y, hy, rfl⟩
      refine ⟨y + w, ?_, ?_⟩
      · show (y + w) 1 = 0
        simp [show y 1 = 0 from hy, show w 1 = 0 from hw]
      · have := h.affine γ hγ y w
        rw [← sub_eq_iff_eq_add.mpr this.symm]
        abel
    have hpar : ∀ w ∈ axisLine k, γ w - γ 0 ≠ 0 → kLine (γ w - γ 0) = Λ := by
      intro w hw hd
      refine hΛu _ ⟨h.kLine_mem hd, zero_mem_kLine _, ?_⟩
      rw [Set.disjoint_left]
      intro x hxM hxd
      have hx2 : x + (γ w - γ 0) ∈ kLine (γ w - γ 0) := add_mem_kLine hxd (mem_kLine_self _)
      have hne : x ≠ x + (γ w - γ 0) := fun h' => hd (by
        have := congrArg (fun z => z - x) h'
        simpa using this.symm)
      exact hM0 (h.zero_mem_of_kLine hML hd hne hxd hx2 hxM (htr w hw x hxM))
    by_cases hdv : γ v - γ 0 = 0
    · rw [hdv]
      exact zero_mem_kLine _
    · rw [hpar _ he₁ hd₁, ← hpar v hv hdv]
      exact mem_kLine_self _

variable [CharP k 2]

theorem exists_involution (h : NaturalAffine Γ) :
    ∃ z ∈ Γ, z * z = 1 ∧ z 0 ≠ 0 ∧ ∀ a : k, z * slPerm (rootSL a) = slPerm (rootSL a) * z := by
  classical
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, -, hq⟩ := FiniteField.card k 2
  set U' : Subgroup (Perm (Fin 2 → k)) := (slPerm.comp rootHom).range with hU'
  set U : Subgroup Γ := U'.subgroupOf Γ with hU
  have hU2 : IsPGroup 2 U := by
    intro g
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    obtain ⟨a, ha⟩ := (Subgroup.mem_subgroupOf.mp g.2 : ((g : Γ) : Perm (Fin 2 → k)) ∈ U')
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_pow, ← ha, ← map_pow, pow_two]
    show slPerm (rootSL (Multiplicative.toAdd a + Multiplicative.toAdd a)) = 1
    rw [CharTwo.add_self_eq_zero, rootSL_zero, map_one]
  have hu₁ : slPerm (rootSL (1 : k)) ∈ U' := ⟨Multiplicative.ofAdd 1, rfl⟩
  set u₁ : U := ⟨⟨slPerm (rootSL 1), h.sl_mem _⟩, Subgroup.mem_subgroupOf.mpr hu₁⟩ with hu₁def
  have hu₁1 : u₁ ≠ 1 := by
    intro h'
    have := congrArg (fun g : U => ((g : Γ) : Perm (Fin 2 → k)) ![0, 1]) h'
    simp only [hu₁def, slPerm_apply] at this
    have h0 := congrFun this 0
    simp [rootSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
  obtain ⟨P, hUP⟩ := hU2.exists_le_sylow
  have hPtr : ∀ v : Fin 2 → k, ∃ g ∈ (P : Subgroup Γ), ((g : Γ) : Perm (Fin 2 → k)) 0 = v := by
    intro v
    refine exists_mem_sylow_smul_eq (p := 2) (n := 2 * n) P ?_ (fun y => ?_) v
    · rw [Nat.card_fun, Nat.card_eq_fintype_card (α := k), hq,
        Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin, ← pow_mul, mul_comm]
    · obtain ⟨γ, hγ, hγ0⟩ := h.trans y
      exact ⟨⟨γ, hγ⟩, hγ0⟩
  have : Nontrivial (P : Subgroup Γ) := by
    refine ⟨⟨⟨u₁, hUP u₁.2⟩, 1, fun h' => hu₁1 ?_⟩⟩
    have h'' : (u₁ : Γ) = 1 := congrArg Subtype.val h'
    exact Subtype.ext h''
  have hZ : Nontrivial (Subgroup.center (P : Subgroup Γ)) := P.isPGroup'.center_nontrivial
  have h2Z : 2 ∣ Nat.card (Subgroup.center (P : Subgroup Γ)) := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (P.isPGroup'.to_subgroup (Subgroup.center _))
    have h1 : 1 < Nat.card (Subgroup.center (P : Subgroup Γ)) :=
      Finite.one_lt_card_iff_nontrivial.mpr hZ
    rw [hm] at h1 ⊢
    exact dvd_pow_self 2 (by rintro rfl; simp at h1)
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' 2 h2Z
  set z : Perm (Fin 2 → k) :=
    ((((z₀ : Subgroup.center (P : Subgroup Γ)) : (P : Subgroup Γ)) : Γ) : Perm (Fin 2 → k))
    with hzdef
  have hzc : ∀ g ∈ (P : Subgroup Γ), z * ((g : Γ) : Perm (Fin 2 → k)) =
      ((g : Γ) : Perm (Fin 2 → k)) * z := by
    intro g hg
    have := Subgroup.mem_center_iff.mp z₀.2 ⟨g, hg⟩
    exact (congrArg (fun g : (P : Subgroup Γ) => ((g : Γ) : Perm (Fin 2 → k))) this).symm
  refine ⟨z, (((z₀ : Subgroup.center (P : Subgroup Γ)) : (P : Subgroup Γ)) : Γ).2, ?_, ?_,
    fun a => hzc ⟨slPerm (rootSL a), h.sl_mem _⟩
      (hUP (Subgroup.mem_subgroupOf.mpr ⟨Multiplicative.ofAdd a, rfl⟩))⟩
  · have h1 : z₀ ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hz₀)
    have h2 := congrArg (fun g : Subgroup.center (P : Subgroup Γ) =>
      (((g : (P : Subgroup Γ)) : Γ) : Perm (Fin 2 → k))) h1
    simpa [pow_two] using h2
  ·
    intro hc
    have h1 : z = 1 := by
      ext v
      obtain ⟨g, hg, rfl⟩ := hPtr v
      have := congrArg (fun f : Perm (Fin 2 → k) => f 0) (hzc g hg)
      simp only [Perm.mul_apply] at this
      rw [this, hc]
      rfl
    have h2 : z₀ = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact h1
    rw [h2, orderOf_one] at hz₀
    exact absurd hz₀ (by norm_num)

theorem addRight_mem_of_involution (h : NaturalAffine Γ) {z : Perm (Fin 2 → k)} (hzΓ : z ∈ Γ)
    (hzz : z * z = 1) (hc0 : z 0 ≠ 0)
    (hzu : ∀ a : k, z * slPerm (rootSL a) = slPerm (rootSL a) * z) :
    Equiv.addRight (z 0) ∈ Γ := by
  have hneg : ∀ v : Fin 2 → k, -v = v := fun v => funext fun i => CharTwo.neg_eq (v i)
  set c := z 0 with hcdef
  have hA : ∀ v w, z (v + w) - c = (z v - c) + (z w - c) := by
    intro v w
    have := h.affine z hzΓ v w
    rw [← hcdef] at this
    rw [eq_sub_of_add_eq this]
    abel
  have hzr : ∀ a : k, ∀ v, z (rootSL a • v) = rootSL a • z v := fun a v =>
    congrArg (fun f : Perm (Fin 2 → k) => f v) (hzu a)
  have hcℓ : c ∈ axisLine k := by
    apply mem_axisLine_of_rootSL_one
    have := hzr 1 0
    rw [smul_zero] at this
    exact this.symm
  have hAr : ∀ a : k, ∀ v, z (rootSL a • v) - c = rootSL a • (z v - c) := by
    intro a v
    rw [hzr, smul_sub, rootSL_smul_of_mem hcℓ]
  have hstar : ∀ a y : k,
      z ((a * y) • ![1, 0]) - c = (a * (z (y • ![0, 1]) - c) 1) • ![1, 0] := by
    intro a y
    have e1 : rootSL a • (y • ![(0 : k), 1]) = (a * y) • ![1, 0] + y • ![0, 1] := by
      rw [rootSL_smul]
      refine vec_ext ?_ ?_ <;> simp
    have e2 : ∀ w : Fin 2 → k, rootSL a • w = w + (a * w 1) • ![1, 0] := by
      intro w
      rw [rootSL_smul]
      refine vec_ext ?_ ?_ <;> simp
    have := hAr a (y • ![0, 1])
    rw [e1, hA, e2] at this
    exact add_right_cancel (this.trans (add_comm _ _))
  set μ := (z ![0, 1] - c) 1 with hμ
  have hstar1 : ∀ a : k, z (a • ![1, 0]) - c = (a * μ) • ![1, 0] := by
    intro a
    have := hstar a 1
    rwa [mul_one, one_smul] at this
  have hμ1 : μ = 1 := by
    have hc : c = c 0 • ![1, 0] := eq_smul_e₁ hcℓ
    have hc00 : c 0 ≠ 0 := fun h' => hc0 (by rw [hc, h', zero_smul])
    have hzc' : z c = 0 := by
      have := congrArg (fun f : Perm (Fin 2 → k) => f 0) hzz
      simpa [Perm.mul_apply] using this
    have := hstar1 (c 0)
    rw [← hc, hzc', zero_sub, hneg] at this
    have h0 := congrFun this 0
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, mul_one] at h0
    exact mul_left_cancel₀ hc00 (by rw [mul_one]; exact h0.symm)
  have hAe₁ : ∀ a : k, z (a • ![1, 0]) - c = a • ![1, 0] := by
    intro a
    rw [hstar1, hμ1, mul_one]
  have hAe₂ : ∀ y : k, (z (y • ![0, 1]) - c) 1 = y := by
    intro y
    have h1 := hstar 1 y
    rw [one_mul, one_mul, hAe₁] at h1
    simpa using (congrFun h1 0).symm
  obtain ⟨M₂, hM₂⟩ := exists_sl_smul_e₁
    (show ![(0 : k), 1] ≠ 0 from fun h' => by simpa using congrFun h' 1)
  set γ := z * slPerm M₂ with hγ
  have hγΓ : γ ∈ Γ := mul_mem hzΓ (h.sl_mem M₂)
  have hγa : ∀ a : k, γ (a • ![1, 0]) = z (a • ![0, 1]) := by
    intro a
    rw [hγ, Perm.mul_apply, ← hM₂]
    exact congrArg z (sl_smul_smul M₂ a _)
  have hγe : γ ![1, 0] = z ![0, 1] := by simpa using hγa 1
  have hγ0 : γ 0 = c := by
    rw [hγ, Perm.mul_apply]
    exact congrArg z (smul_zero M₂)
  have hlin : ∀ y : k, z (y • ![0, 1]) - c = y • (z ![0, 1] - c) := by
    intro y
    have := h.linear_part_mem_kLine hγΓ (smul_e₁_mem y)
    rw [hγa, hγ0, hγe] at this
    obtain ⟨a, ha⟩ := this
    have h1 := congrFun ha 1
    rw [hAe₂, Pi.smul_apply, smul_eq_mul, ← hμ, hμ1, mul_one] at h1
    rw [ha, h1]
  set b := (z ![0, 1] - c) 0 with hb
  have he₂ : z ![0, 1] - c = ![b, 1] := vec_ext (by simp [hb]) (by simp [← hμ, hμ1])
  have hform : ∀ v, z v = rootSL b • v + c := by
    intro v
    have hv : v = v 0 • ![1, 0] + v 1 • ![0, 1] := vec_ext (by simp) (by simp)
    have := hA (v 0 • ![1, 0]) (v 1 • ![0, 1])
    rw [← hv, hAe₁, hlin, he₂] at this
    rw [eq_add_of_sub_eq this, rootSL_smul]
    congr 1
    refine vec_ext ?_ ?_ <;> simp [mul_comm]
  have hτ : Equiv.addRight c = z * (slPerm (rootSL b))⁻¹ := by
    refine Equiv.ext fun v => ?_
    rw [Perm.mul_apply, ← map_inv, hform, Equiv.coe_addRight]
    show v + c = rootSL b • ((rootSL b)⁻¹ • v) + c
    rw [smul_inv_smul]
  rw [hτ]
  exact mul_mem hzΓ (inv_mem (h.sl_mem _))

theorem exists_translation (h : NaturalAffine Γ) :
    ∃ c : Fin 2 → k, c ≠ 0 ∧ Equiv.addRight c ∈ Γ := by
  obtain ⟨z, hzΓ, hzz, hz0, hzu⟩ := h.exists_involution
  exact ⟨z 0, hz0, h.addRight_mem_of_involution hzΓ hzz hz0 hzu⟩

theorem translations_le (h : NaturalAffine Γ) (b : Fin 2 → k) : Equiv.addRight b ∈ Γ := by
  obtain ⟨c, hc0, hc⟩ := h.exists_translation
  by_cases hb : b = 0
  · have : Equiv.addRight b = 1 := Equiv.ext fun v => by simp [hb]
    rw [this]
    exact one_mem Γ
  · obtain ⟨M, hM⟩ := exists_sl_smul hc0 hb
    have : Equiv.addRight b = slPerm M * Equiv.addRight c * (slPerm M)⁻¹ := by
      refine Equiv.ext fun v => ?_
      rw [Perm.mul_apply, Perm.mul_apply, ← map_inv, Equiv.coe_addRight, Equiv.coe_addRight]
      show v + b = M • (M⁻¹ • v + c)
      rw [smul_add, smul_inv_smul, hM]
    rw [this]
    exact mul_mem (mul_mem (h.sl_mem M) hc) (inv_mem (h.sl_mem M))

end NaturalAffine

end Natural

section Coset

open Subgroup

variable {G : Type*} [Group G] {W : Subgroup G} {k : Type*} [Field k]
  (ι : Multiplicative (Fin 2 → k) ≃* W) (t : G)

@[expose] noncomputable def wCoord (g : G) : Fin 2 → k := by
  classical
  exact if h : g ∈ W then Multiplicative.toAdd (ι.symm ⟨g, h⟩) else 0

@[expose] def cosetPt (v : Fin 2 → k) : G := t * (ι (Multiplicative.ofAdd v) : G)

variable {ι t}

theorem wCoord_mem {g : G} (hg : g ∈ W) : (ι (Multiplicative.ofAdd (wCoord ι g)) : G) = g := by
  rw [wCoord, dite_eq_left hg, ofAdd_toAdd, MulEquiv.apply_symm_apply]

theorem wCoord_apply (v : Fin 2 → k) : wCoord ι (ι (Multiplicative.ofAdd v) : G) = v := by
  rw [wCoord, dite_eq_left (ι _).2, Subtype.coe_eta, MulEquiv.symm_apply_apply, toAdd_ofAdd]

theorem wCoord_mul {g h : G} (hg : g ∈ W) (hh : h ∈ W) :
    wCoord ι (g * h) = wCoord ι g + wCoord ι h := by
  conv_lhs => rw [← wCoord_mem (ι := ι) hg, ← wCoord_mem (ι := ι) hh]
  rw [← Subgroup.coe_mul, ← map_mul, ← ofAdd_add, wCoord_apply]

theorem mul_comm_of_mem (e : Multiplicative (Fin 2 → k) ≃* W) {g h : G} (hg : g ∈ W)
    (hh : h ∈ W) : g * h = h * g := by
  have : (⟨g, hg⟩ * ⟨h, hh⟩ : W) = ⟨h, hh⟩ * ⟨g, hg⟩ :=
    e.symm.injective (by rw [map_mul, map_mul, mul_comm])
  exact congrArg Subtype.val this

theorem wCoord_one : wCoord ι (1 : G) = 0 := by
  simpa using wCoord_apply (ι := ι) 0

theorem cosetPt_injective : Function.Injective (cosetPt ι t) := by
  intro v w h
  have h' := mul_left_cancel h
  rw [← wCoord_apply (ι := ι) v, h', wCoord_apply]

theorem cosetPt_zero : cosetPt ι t 0 = t := by
  simp [cosetPt]

theorem wCoord_cosetPt (v : Fin 2 → k) : wCoord ι (t⁻¹ * cosetPt ι t v) = v := by
  rw [cosetPt, inv_mul_cancel_left, wCoord_apply]

theorem cosetPt_wCoord {g : G} (hg : t⁻¹ * g ∈ W) : cosetPt ι t (wCoord ι (t⁻¹ * g)) = g := by
  rw [cosetPt, wCoord_mem hg, mul_inv_cancel_left]

variable {X : Subgroup G}

theorem conj_cosetPt_mem (hXW : X ≤ normalizer (W : Set G))
    (hXt : ∀ x ∈ X, t⁻¹ * (x * t * x⁻¹) ∈ W) {x : G} (hx : x ∈ X) (v : Fin 2 → k) :
    t⁻¹ * (x * cosetPt ι t v * x⁻¹) ∈ W := by
  have h1 : x * (ι (Multiplicative.ofAdd v) : G) * x⁻¹ ∈ W :=
    (mem_normalizer_iff.mp (hXW hx) _).mp (ι _).2
  have e : t⁻¹ * (x * cosetPt ι t v * x⁻¹) =
      (t⁻¹ * (x * t * x⁻¹)) * (x * (ι (Multiplicative.ofAdd v) : G) * x⁻¹) := by
    simp only [cosetPt]
    group
  rw [e]
  exact mul_mem (hXt x hx) h1

variable (ι t) in
@[expose] noncomputable def cosetAction (hXW : X ≤ normalizer (W : Set G))
    (hXt : ∀ x ∈ X, t⁻¹ * (x * t * x⁻¹) ∈ W) : X →* Perm (Fin 2 → k) where
  toFun x :=
    { toFun := fun v => wCoord ι (t⁻¹ * ((x : G) * cosetPt ι t v * (x : G)⁻¹))
      invFun := fun v => wCoord ι (t⁻¹ * ((x : G)⁻¹ * cosetPt ι t v * (x : G)))
      left_inv := fun v => by
        dsimp only
        rw [cosetPt_wCoord (conj_cosetPt_mem hXW hXt x.2 v)]
        rw [show (x : G)⁻¹ * ((x : G) * cosetPt ι t v * (x : G)⁻¹) * (x : G) = cosetPt ι t v by
          group]
        exact wCoord_cosetPt v
      right_inv := fun v => by
        dsimp only
        have h := conj_cosetPt_mem (ι := ι) hXW hXt (X.inv_mem x.2) v
        rw [inv_inv] at h
        rw [cosetPt_wCoord h]
        rw [show (x : G) * ((x : G)⁻¹ * cosetPt ι t v * (x : G)) * (x : G)⁻¹ = cosetPt ι t v by
          group]
        exact wCoord_cosetPt v }
  map_one' := Equiv.ext fun v => by
    simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one, Equiv.coe_fn_mk,
      Perm.coe_one, id_eq]
    exact wCoord_cosetPt v
  map_mul' x y := Equiv.ext fun v => by
    simp only [Subgroup.coe_mul, Equiv.coe_fn_mk, Perm.coe_mul, Function.comp_apply]
    rw [cosetPt_wCoord (conj_cosetPt_mem hXW hXt y.2 v)]
    congr 2
    group

variable {hXW : X ≤ normalizer (W : Set G)} {hXt : ∀ x ∈ X, t⁻¹ * (x * t * x⁻¹) ∈ W}

theorem cosetAction_apply (x : X) (v : Fin 2 → k) :
    cosetAction ι t hXW hXt x v = wCoord ι (t⁻¹ * ((x : G) * cosetPt ι t v * (x : G)⁻¹)) :=
  rfl

theorem cosetPt_cosetAction (x : X) (v : Fin 2 → k) :
    cosetPt ι t (cosetAction ι t hXW hXt x v) = (x : G) * cosetPt ι t v * (x : G)⁻¹ :=
  cosetPt_wCoord (conj_cosetPt_mem hXW hXt x.2 v)

theorem cosetAction_affine (x : X) (v w : Fin 2 → k) :
    cosetAction ι t hXW hXt x (v + w) + cosetAction ι t hXW hXt x 0 =
      cosetAction ι t hXW hXt x v + cosetAction ι t hXW hXt x w := by
  have hc : t⁻¹ * ((x : G) * t * (x : G)⁻¹) ∈ W := hXt x x.2
  have hm : ∀ u : Fin 2 → k, (x : G) * (ι (Multiplicative.ofAdd u) : G) * (x : G)⁻¹ ∈ W :=
    fun u => (mem_normalizer_iff.mp (hXW x.2) _).mp (ι _).2
  have key : ∀ u, cosetAction ι t hXW hXt x u = wCoord ι (t⁻¹ * ((x : G) * t * (x : G)⁻¹)) +
      wCoord ι ((x : G) * (ι (Multiplicative.ofAdd u) : G) * (x : G)⁻¹) := by
    intro u
    rw [cosetAction_apply, ← wCoord_mul hc (hm u)]
    congr 1
    simp only [cosetPt]
    group
  have hadd : ∀ u u' : Fin 2 → k,
      wCoord ι ((x : G) * (ι (Multiplicative.ofAdd (u + u')) : G) * (x : G)⁻¹) =
        wCoord ι ((x : G) * (ι (Multiplicative.ofAdd u) : G) * (x : G)⁻¹) +
        wCoord ι ((x : G) * (ι (Multiplicative.ofAdd u') : G) * (x : G)⁻¹) := by
    intro u u'
    rw [← wCoord_mul (hm u) (hm u'), ofAdd_add, map_mul, Subgroup.coe_mul]
    congr 1
    group
  have h0 : wCoord ι ((x : G) * (ι (Multiplicative.ofAdd (0 : Fin 2 → k)) : G) * (x : G)⁻¹) =
      0 := by
    simpa using wCoord_one (ι := ι)
  rw [key, key, key, key, hadd, h0]
  abel

end Coset

section Points

open Subgroup

variable {G : Type*} [Group G] {W X : Subgroup G} {t : G} {k : Type*} [Field k]

theorem conj_mem_coset (ht : t * t = 1) (hWt : W ≤ centralizer ({t} : Set G))
    {x : G} (hxW : x ∈ normalizer (W : Set G))
    (hxE : x ∈ normalizer ((W ⊔ zpowers t : Subgroup G) : Set G)) :
    t⁻¹ * (x * t * x⁻¹) ∈ W := by
  have hc : ∀ w ∈ W, t * w = w * t := fun w hw =>
    mem_centralizer_iff.mp (hWt hw) t (Set.mem_singleton t)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  let S : Subgroup G :=
    { carrier := {y | y ∈ W ∨ t⁻¹ * y ∈ W}
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (mul_mem ha hb)
        · refine Or.inr ?_
          have e : t⁻¹ * (a * b) = a * (t⁻¹ * b) := by
            rw [htinv, ← mul_assoc, hc a ha, mul_assoc]
          rw [e]
          exact mul_mem ha hb
        · refine Or.inr ?_
          rw [← mul_assoc]
          exact mul_mem ha hb
        · refine Or.inl ?_
          have e : a * b = (t⁻¹ * a) * (t⁻¹ * b) := by
            calc a * b = (t * (t⁻¹ * a)) * b := by group
              _ = ((t⁻¹ * a) * t) * b := by rw [hc _ ha]
              _ = (t⁻¹ * a) * (t⁻¹ * b) := by rw [htinv]; group
          rw [e]
          exact mul_mem ha hb
      one_mem' := Or.inl W.one_mem
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (inv_mem ha)
        · refine Or.inr ?_
          have e : t⁻¹ * a⁻¹ = (t⁻¹ * a)⁻¹ := by
            calc t⁻¹ * a⁻¹ = t * (t⁻¹ * a)⁻¹ * t := by rw [htinv]; group
              _ = (t⁻¹ * a)⁻¹ * t * t := by rw [hc _ (inv_mem ha)]
              _ = (t⁻¹ * a)⁻¹ := by rw [mul_assoc, ht, mul_one]
          rw [e]
          exact inv_mem ha }
  have hES : W ⊔ zpowers t ≤ S :=
    sup_le (fun w hw => Or.inl hw) (zpowers_le.mpr (Or.inr (by rw [inv_mul_cancel]; exact
      W.one_mem)))
  have hy : x * t * x⁻¹ ∈ W ⊔ zpowers t :=
    (mem_normalizer_iff.mp hxE t).mp (mem_sup_right (mem_zpowers t))
  rcases hES hy with hy | hy
  ·
    have htW : t ∈ W := by
      have := (mem_normalizer_iff.mp hxW t).mpr hy
      exact this
    exact mul_mem (inv_mem htW) hy
  · exact hy

theorem cosetAction_eq_slPerm (ι : Multiplicative (Fin 2 → k) ≃* W)
    (hXW : X ≤ normalizer (W : Set G)) (hXt : ∀ x ∈ X, t⁻¹ * (x * t * x⁻¹) ∈ W) {g : G}
    (hgX : g ∈ X) (hgt : g ∈ centralizer ({t} : Set G)) {M : SL(2, k)}
    (hM : ∀ v : Fin 2 → k, g * (ι (Multiplicative.ofAdd v) : G) * g⁻¹ =
      ι (Multiplicative.ofAdd ((M : Matrix (Fin 2) (Fin 2) k) *ᵥ v))) :
    cosetAction ι t hXW hXt ⟨g, hgX⟩ = slPerm M := by
  refine Equiv.ext fun v => ?_
  rw [cosetAction_apply, slPerm_apply]
  have hgt' : g * t = t * g := (mem_centralizer_iff.mp hgt t (Set.mem_singleton t)).symm
  have e : g * cosetPt ι t v * g⁻¹ = cosetPt ι t ((M : Matrix (Fin 2) (Fin 2) k) *ᵥ v) := by
    rw [cosetPt, cosetPt, ← hM v]
    calc g * (t * ↑(ι (Multiplicative.ofAdd v))) * g⁻¹
        = g * t * ↑(ι (Multiplicative.ofAdd v)) * g⁻¹ := by group
      _ = t * (g * ↑(ι (Multiplicative.ofAdd v)) * g⁻¹) := by rw [hgt']; group
  exact (congrArg (fun y => wCoord ι (t⁻¹ * y)) e).trans (wCoord_cosetPt _)

end Points

end Plane

section Main

open Subgroup Plane

variable {G : Type*} [Group G] {W X K : Subgroup G} {t : G} {k : Type*} [Field k]
  [Fintype k] [CharP k 2]

theorem exists_conj_eq_mul_of_natural (ι : Multiplicative (Fin 2 → k) ≃* W)
    (hXW : X ≤ normalizer (W : Set G)) (hXt : ∀ x ∈ X, t⁻¹ * (x * t * x⁻¹) ∈ W)
    (hK : K ≤ X ⊓ centralizer ({t} : Set G))
    (hKn : ∀ x ∈ X ⊓ centralizer ({t} : Set G), ∀ g ∈ K, x * g * x⁻¹ ∈ K)
    (hnat : ∀ g ∈ K, ∃ M : SL(2, k), ∀ v : Fin 2 → k, g * (ι (Multiplicative.ofAdd v) : G) * g⁻¹ =
      ι (Multiplicative.ofAdd ((M : Matrix (Fin 2) (Fin 2) k) *ᵥ v)))
    (hsurj : ∀ M : SL(2, k), ∃ g ∈ K, ∀ v : Fin 2 → k,
      g * (ι (Multiplicative.ofAdd v) : G) * g⁻¹ =
        ι (Multiplicative.ofAdd ((M : Matrix (Fin 2) (Fin 2) k) *ᵥ v)))
    (hline : ∀ c : k, ∃ x ∈ X, (∀ a : k, ∃ b : k,
        x * (t * ι (Multiplicative.ofAdd ![a, 0])) * x⁻¹ = t * ι (Multiplicative.ofAdd ![b, 0])) ∧
      x * t * x⁻¹ = t * ι (Multiplicative.ofAdd ![c, 0])) :
    ∀ w ∈ W, ∃ x ∈ X, x ∈ centralizer (W : Set G) ∧ x * t * x⁻¹ = t * w := by
  set ρ := cosetAction ι t hXW hXt with hρ
  have hNA : NaturalAffine ρ.range := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro _ ⟨x, rfl⟩ v w
      exact cosetAction_affine x v w
    · intro M
      obtain ⟨g, hg, hgM⟩ := hsurj M
      exact ⟨⟨g, (hK hg).1⟩, cosetAction_eq_slPerm ι hXW hXt (hK hg).1 (hK hg).2 hgM⟩
    · rintro _ ⟨x, rfl⟩ hx0 M
      have hxt : (x : G) * t * (x : G)⁻¹ = t := by
        have := cosetPt_cosetAction (ι := ι) (t := t) (hXW := hXW) (hXt := hXt) x 0
        rw [hx0, cosetPt_zero] at this
        exact this.symm
      have hxc : (x : G)⁻¹ ∈ X ⊓ centralizer ({t} : Set G) := by
        refine ⟨X.inv_mem x.2, mem_centralizer_iff.mpr ?_⟩
        intro y hy
        rw [Set.mem_singleton_iff.mp hy]
        calc t * (x : G)⁻¹ = (x : G)⁻¹ * ((x : G) * t * (x : G)⁻¹) := by group
          _ = (x : G)⁻¹ * t := by rw [hxt]
      obtain ⟨g, hg, hgM⟩ := hsurj M
      have hg' : (x : G)⁻¹ * g * (x : G)⁻¹⁻¹ ∈ K := hKn _ hxc g hg
      obtain ⟨M', hM'⟩ := hnat _ hg'
      refine ⟨M', ?_⟩
      rw [← cosetAction_eq_slPerm ι hXW hXt (hK hg).1 (hK hg).2 hgM,
        ← cosetAction_eq_slPerm ι hXW hXt (hK hg').1 (hK hg').2 hM', ← map_inv, ← map_mul,
        ← map_mul]
      congr 1
      ext
      simp
    · intro c
      obtain ⟨x, hx, hmaps, hxt⟩ := hline c
      refine ⟨ρ ⟨x, hx⟩, ⟨_, rfl⟩, fun v hv => ?_, cosetPt_injective (ι := ι) (t := t) ?_⟩
      · obtain ⟨b, hb⟩ := hmaps (v 0)
        have hv' : v = ![v 0, 0] := vec_ext (by simp) (by simpa [axisLine] using hv)
        have : ρ ⟨x, hx⟩ v = ![b, 0] := by
          apply cosetPt_injective (ι := ι) (t := t)
          rw [hρ, cosetPt_cosetAction]
          rw [hv'] at *
          exact hb
        rw [this]
        simp [axisLine]
      · rw [hρ, cosetPt_cosetAction, cosetPt_zero]
        exact hxt
  intro w hw
  obtain ⟨⟨x, hx⟩, hρx⟩ := hNA.translations_le (wCoord ι w)
  have hpt : ∀ u, x * cosetPt ι t u * x⁻¹ = cosetPt ι t (u + wCoord ι w) := by
    intro u
    have := cosetPt_cosetAction (ι := ι) (t := t) (hXW := hXW) (hXt := hXt) ⟨x, hx⟩ u
    rw [← hρ, hρx, Equiv.coe_addRight] at this
    exact this.symm
  have hxt : x * t * x⁻¹ = t * w := by
    have := hpt 0
    rw [cosetPt_zero, zero_add, cosetPt, wCoord_mem hw] at this
    exact this
  refine ⟨x, hx, mem_centralizer_iff.mpr fun w' hw' => ?_, hxt⟩
  have h1 := hpt (wCoord ι w')
  rw [cosetPt, cosetPt, ofAdd_add, map_mul, Subgroup.coe_mul, wCoord_mem hw,
    wCoord_mem hw'] at h1
  have h2 : x * (t * w') * x⁻¹ = (x * t * x⁻¹) * (x * w' * x⁻¹) := by group
  rw [h2, hxt, mul_assoc, mul_right_inj, mul_comm_of_mem ι hw' hw] at h1
  have h3 : x * w' * x⁻¹ = w' := mul_left_cancel h1
  calc w' * x = (x * w' * x⁻¹) * x := by rw [h3]
    _ = x * w' := by group

theorem exists_regularNormal_of_natural (ι : Multiplicative (Fin 2 → k) ≃* W) (ht : t * t = 1)
    (hWt : W ≤ centralizer ({t} : Set G)) (hXW : X ≤ normalizer (W : Set G))
    (hXE : X ≤ normalizer ((W ⊔ zpowers t : Subgroup G) : Set G))
    (hK : K ≤ X ⊓ centralizer ({t} : Set G))
    (hKn : ∀ x ∈ X ⊓ centralizer ({t} : Set G), ∀ g ∈ K, x * g * x⁻¹ ∈ K)
    (hnat : ∀ g ∈ K, ∃ M : SL(2, k), ∀ v : Fin 2 → k, g * (ι (Multiplicative.ofAdd v) : G) * g⁻¹ =
      ι (Multiplicative.ofAdd ((M : Matrix (Fin 2) (Fin 2) k) *ᵥ v)))
    (hsurj : ∀ M : SL(2, k), ∃ g ∈ K, ∀ v : Fin 2 → k,
      g * (ι (Multiplicative.ofAdd v) : G) * g⁻¹ =
        ι (Multiplicative.ofAdd ((M : Matrix (Fin 2) (Fin 2) k) *ᵥ v)))
    (hline : ∀ c : k, ∃ x ∈ X, (∀ a : k, ∃ b : k,
        x * (t * ι (Multiplicative.ofAdd ![a, 0])) * x⁻¹ = t * ι (Multiplicative.ofAdd ![b, 0])) ∧
      x * t * x⁻¹ = t * ι (Multiplicative.ofAdd ![c, 0])) :
    ∃ T : Subgroup G, T ≤ X ∧ (T.subgroupOf X).Normal ∧ T ≤ centralizer (W : Set G) ∧
      X ⊓ centralizer ((W ⊔ zpowers t : Subgroup G) : Set G) ≤ T ∧
      ∀ w ∈ W, ∃ x ∈ T, x * t * x⁻¹ = t * w := by
  have hXt : ∀ x ∈ X, t⁻¹ * (x * t * x⁻¹) ∈ W := fun x hx =>
    conj_mem_coset ht hWt (hXW hx) (hXE hx)
  refine ⟨X ⊓ centralizer (W : Set G), inf_le_left, ⟨fun n hn g => ?_⟩, inf_le_right, ?_, ?_⟩
  · rw [mem_subgroupOf] at hn ⊢
    refine Subgroup.mem_inf.mpr ⟨(g * n * g⁻¹).2, mem_centralizer_iff.mpr fun w hw => ?_⟩
    have hw' : (g : G)⁻¹ * w * (g : G)⁻¹⁻¹ ∈ W :=
      (mem_normalizer_iff.mp (hXW (X.inv_mem g.2)) w).mp hw
    rw [inv_inv] at hw'
    have hc := mem_centralizer_iff.mp hn.2 _ hw'
    simp only [coe_mul, coe_inv]
    calc w * ((g : G) * n * (g : G)⁻¹) = g * (((g : G)⁻¹ * w * g) * n) * (g : G)⁻¹ := by group
      _ = g * (n * ((g : G)⁻¹ * w * g)) * (g : G)⁻¹ := by rw [hc]
      _ = ((g : G) * n * (g : G)⁻¹) * w := by group
  · exact inf_le_inf_left _ (centralizer_le (le_sup_left : W ≤ W ⊔ zpowers t))
  · intro w hw
    obtain ⟨x, hx, hxc, hxt⟩ :=
      exists_conj_eq_mul_of_natural ι hXW hXt hK hKn hnat hsurj hline w hw
    exact ⟨x, ⟨hx, hxc⟩, hxt⟩

end Main

end CFSG.LocalAnalysis.EvenBN.LinearThree
