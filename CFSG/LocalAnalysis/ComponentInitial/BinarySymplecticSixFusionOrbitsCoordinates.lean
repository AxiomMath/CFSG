module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixFirstFusion
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCentralizerObstruction

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits

open Subgroup Module Matrix SymplecticFlag SymplecticTorusWeyl CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)
open scoped Pointwise

variable {G : Type*} [Group G] {L : Subgroup G}
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}

@[expose] def tauSet (φ : L ≃* bilinIsometryGroup b) (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V)
    (P : Matrix (Fin 3) (Fin 3) (ZMod 2) → Prop) : Set G :=
  {a | ∃ ha : a ∈ L, ∃ B : Matrix (Fin 3) (Fin 3) (ZMod 2), Bᵀ = B ∧ P B ∧
    LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) = fromBlocks 1 B 0 1}

variable (φ : L ≃* bilinIsometryGroup b) {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V}
  (he : IsSymplecticBasis b e)

@[expose] def spHom : StatedSp 3 (ZMod 2) →* G :=
  L.subtype.comp (φ.symm.toMonoidHom.comp (spCoord he).symm.toMonoidHom)

@[expose] def tauHom : Multiplicative (binarySymMatrices 3) →* G :=
  (spHom φ he).comp (tauSym 3)

@[expose] def leviHom : GL (Fin 3) (ZMod 2) →* G :=
  (spHom φ he).comp leviSp

theorem spHom_mem (g : StatedSp 3 (ZMod 2)) : spHom φ he g ∈ L :=
  (φ.symm ((spCoord he).symm g)).2

theorem apply_spHom (g : StatedSp 3 (ZMod 2)) :
    φ ⟨spHom φ he g, spHom_mem φ he g⟩ = (spCoord he).symm g := by
  have : (⟨spHom φ he g, spHom_mem φ he g⟩ : L) = φ.symm ((spCoord he).symm g) := rfl
  rw [this, MulEquiv.apply_symm_apply]

theorem spHom_injective : Function.Injective (spHom φ he) := fun g g' h => by
  have h' : (⟨spHom φ he g, spHom_mem φ he g⟩ : L) = ⟨spHom φ he g', spHom_mem φ he g'⟩ :=
    Subtype.ext h
  have := congrArg φ h'
  rw [apply_spHom, apply_spHom] at this
  exact (spCoord he).symm.injective this

theorem toMatrix_spHom (g : StatedSp 3 (ZMod 2)) :
    LinearMap.toMatrix e e (linOf (φ ⟨spHom φ he g, spHom_mem φ he g⟩)) = spMatrixOf g := by
  rw [apply_spHom, ← spMatrixOf_spCoord he, MulEquiv.apply_symm_apply]

theorem tauHom_injective : Function.Injective (tauHom φ he) :=
  (spHom_injective φ he).comp (tauSym_injective (n := 3))

theorem tauHom_mem (B : Multiplicative (binarySymMatrices 3)) : tauHom φ he B ∈ L :=
  spHom_mem φ he _

theorem toMatrix_tauHom (B : Multiplicative (binarySymMatrices 3)) :
    LinearMap.toMatrix e e (linOf (φ ⟨tauHom φ he B, tauHom_mem φ he B⟩)) =
      fromBlocks 1 (B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 1 := by
  rw [← spMatrixOf_tauSym]
  exact toMatrix_spHom φ he _

theorem leviHom_mem (D : GL (Fin 3) (ZMod 2)) : leviHom φ he D ∈ L :=
  spHom_mem φ he _

theorem leviHom_conj_tauHom (D : GL (Fin 3) (ZMod 2)) (B : Multiplicative (binarySymMatrices 3)) :
    leviHom φ he D * tauHom φ he B * (leviHom φ he D)⁻¹ =
      tauHom φ he (Multiplicative.ofAdd ⟨D * (B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        (D : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ, congr_mem_binarySymMatrices _ _⟩) := by
  simp only [leviHom, tauHom, MonoidHom.comp_apply]
  rw [← map_inv, ← map_mul, ← map_mul, leviSp_mul_tauSym_mul_inv]

theorem mem_tauSet_iff {P : Matrix (Fin 3) (Fin 3) (ZMod 2) → Prop} {a : G} :
    a ∈ tauSet φ e P ↔ ∃ B : Multiplicative (binarySymMatrices 3),
      P (B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∧ tauHom φ he B = a := by
  constructor
  · rintro ⟨ha, B, hBt, hP, hB⟩
    refine ⟨Multiplicative.ofAdd ⟨B, mem_binarySymMatrices.2 hBt⟩, hP, ?_⟩
    have h1 : spCoord he (φ ⟨a, ha⟩) =
        tauSym 3 (Multiplicative.ofAdd ⟨B, mem_binarySymMatrices.2 hBt⟩) :=
      statedSp_ext (by
        change spMatrixOf (spCoord he (φ ⟨a, ha⟩)) = spMatrixOf (tauSym 3 _)
        rw [spMatrixOf_spCoord, hB, spMatrixOf_tauSym]
        rfl)
    have h2 : φ.symm ((spCoord he).symm (tauSym 3 (Multiplicative.ofAdd
        ⟨B, mem_binarySymMatrices.2 hBt⟩))) = ⟨a, ha⟩ := by
      rw [← h1, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    exact congrArg Subtype.val h2
  · rintro ⟨B, hP, rfl⟩
    exact ⟨tauHom_mem φ he B, B.toAdd, binarySym_transpose _, hP, toMatrix_tauHom φ he B⟩

theorem mem_pullSub_iff {a : G} :
    a ∈ pullSub φ (pointwiseStabilizer b (lagrangianOf e)) ↔
      ∃ B : Multiplicative (binarySymMatrices 3), tauHom φ he B = a := by
  rw [mem_pullSub]
  constructor
  · rintro ⟨ha, hmem⟩
    rw [mem_pointwiseStabilizer_iff_spCoord he] at hmem
    obtain ⟨B, hB⟩ := hmem
    refine ⟨B, ?_⟩
    have : φ.symm ((spCoord he).symm (tauSym 3 B)) = ⟨a, ha⟩ := by
      rw [hB, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    exact congrArg Subtype.val this
  · rintro ⟨B, rfl⟩
    refine ⟨tauHom_mem φ he B, ?_⟩
    change φ ⟨spHom φ he (tauSym 3 B), spHom_mem φ he _⟩ ∈ _
    rw [apply_spHom, mem_pointwiseStabilizer_iff_spCoord he, MulEquiv.apply_symm_apply]
    exact ⟨B, rfl⟩

include he in
theorem tauSet_top :
    tauSet φ e (fun _ => True) = (pullSub φ (pointwiseStabilizer b (lagrangianOf e)) : Set G) := by
  ext a
  rw [mem_tauSet_iff φ he, SetLike.mem_coe, mem_pullSub_iff φ he]
  simp

include he in
theorem tauSet_subset (P : Matrix (Fin 3) (Fin 3) (ZMod 2) → Prop) :
    tauSet φ e P ⊆ (pullSub φ (pointwiseStabilizer b (lagrangianOf e)) : Set G) := by
  rw [← tauSet_top φ he]
  rintro a ⟨ha, B, hBt, -, hB⟩
  exact ⟨ha, B, hBt, trivial, hB⟩

theorem tauSet_eq_image (P : Matrix (Fin 3) (Fin 3) (ZMod 2) → Prop) :
    tauSet φ e P = (fun B : binarySymMatrices 3 => tauHom φ he (Multiplicative.ofAdd B)) ''
      {B | P (B : Matrix (Fin 3) (Fin 3) (ZMod 2))} := by
  ext a
  rw [mem_tauSet_iff φ he]
  constructor
  · rintro ⟨B, hP, rfl⟩
    exact ⟨B.toAdd, hP, rfl⟩
  · rintro ⟨B, hP, rfl⟩
    exact ⟨Multiplicative.ofAdd B, hP, rfl⟩

include he in
theorem card_tauSet (P : Matrix (Fin 3) (Fin 3) (ZMod 2) → Prop) :
    Nat.card (tauSet φ e P) =
      Nat.card {B : binarySymMatrices 3 // P (B : Matrix (Fin 3) (Fin 3) (ZMod 2))} := by
  rw [tauSet_eq_image φ he, Nat.card_image_of_injective (fun B B' h =>
    Multiplicative.ofAdd.injective (tauHom_injective φ he h))]
  rfl

include he in
theorem disjoint_tauSet {P Q : Matrix (Fin 3) (Fin 3) (ZMod 2) → Prop}
    (h : ∀ B, P B → Q B → False) : Disjoint (tauSet φ e P) (tauSet φ e Q) := by
  rw [Set.disjoint_left]
  intro a ha ha'
  obtain ⟨B, hB, rfl⟩ := (mem_tauSet_iff φ he).1 ha
  obtain ⟨B', hB', hBB'⟩ := (mem_tauSet_iff φ he).1 ha'
  rw [tauHom_injective φ he hBB'] at hB'
  exact h _ hB hB'

include he in
theorem one_notMem_tauSet {P : Matrix (Fin 3) (Fin 3) (ZMod 2) → Prop} (h : ¬ P 0) :
    (1 : G) ∉ tauSet φ e P := by
  intro h1
  obtain ⟨B, hB, hB1⟩ := (mem_tauSet_iff φ he).1 h1
  rw [← map_one (tauHom φ he)] at hB1
  rw [tauHom_injective φ he hB1] at hB
  exact h hB

section Radical

variable [FiniteDimensional (ZMod 2) V] (hb : b.IsAlt) (hnd : b.Nondegenerate)
  (hV : finrank (ZMod 2) V = 6)

include hb hnd hV in
theorem leviHom_mem_normalizer (D : GL (Fin 3) (ZMod 2)) :
    leviHom φ he D ∈
      normalizer (pullSub φ (pointwiseStabilizer b (lagrangianOf e)) : Set G) ⊓ L := by
  obtain ⟨-, -, -, hNL⟩ := pullSub_radical hb hnd hV φ (isTotallyIsotropic_lagrangianOf he)
    finrank_lagrangianOf
  rw [hNL, mem_pullSub]
  refine ⟨leviHom_mem φ he D, ?_⟩
  change φ ⟨spHom φ he (leviSp D), spHom_mem φ he _⟩ ∈ _
  rw [apply_spHom, mem_subspaceStabilizer_iff_spCoord he, MulEquiv.apply_symm_apply]
  exact leviSp_mem_stabilizer D

end Radical

theorem exists_conj_of_mem_tauSet {P : Matrix (Fin 3) (Fin 3) (ZMod 2) → Prop}
    (hP : ∀ B B' : binarySymMatrices 3, P B → P B' →
      (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = (B' : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank ∧
        ((B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 2 →
          ((∀ i, (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0) ↔
            ∀ i, (B' : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0)))
    {x y : G} (hx : x ∈ tauSet φ e P) (hy : y ∈ tauSet φ e P) :
    ∃ D : GL (Fin 3) (ZMod 2), leviHom φ he D * x * (leviHom φ he D)⁻¹ = y := by
  obtain ⟨B, hB, rfl⟩ := (mem_tauSet_iff φ he).1 hx
  obtain ⟨B', hB', rfl⟩ := (mem_tauSet_iff φ he).1 hy
  obtain ⟨D, hD⟩ := (sym_congruent_iff B.toAdd B'.toAdd).2 (hP _ _ hB hB')
  refine ⟨D, ?_⟩
  rw [leviHom_conj_tauHom]
  congr 1
  exact Multiplicative.toAdd.injective (Subtype.ext hD)

theorem congr_classes :
    (∀ B B' : binarySymMatrices 3, (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 1 →
      (B' : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 1 →
      (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = (B' : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank ∧
        ((B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 2 →
          ((∀ i, (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0) ↔
            ∀ i, (B' : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0))) ∧
    (∀ B B' : binarySymMatrices 3,
      ((B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 2 ∧
        ∀ i, (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0) →
      ((B' : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 2 ∧
        ∀ i, (B' : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0) →
      (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = (B' : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank ∧
        ((B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 2 →
          ((∀ i, (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0) ↔
            ∀ i, (B' : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0))) ∧
    (∀ B B' : binarySymMatrices 3,
      ((B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 2 ∧
        ¬ ∀ i, (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0) →
      ((B' : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 2 ∧
        ¬ ∀ i, (B' : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0) →
      (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = (B' : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank ∧
        ((B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 2 →
          ((∀ i, (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0) ↔
            ∀ i, (B' : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0))) ∧
    (∀ B B' : binarySymMatrices 3, (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 3 →
      (B' : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 3 →
      (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = (B' : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank ∧
        ((B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 2 →
          ((∀ i, (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0) ↔
            ∀ i, (B' : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0))) := by
  refine ⟨fun B B' h h' => ⟨h.trans h'.symm, fun h2 => by omega⟩,
    fun B B' h h' => ⟨h.1.trans h'.1.symm, fun _ => ⟨fun _ => h'.2, fun _ => h.2⟩⟩,
    fun B B' h h' => ⟨h.1.trans h'.1.symm, fun _ => ⟨fun h'' => absurd h'' h.2,
      fun h'' => absurd h'' h'.2⟩⟩,
    fun B B' h h' => ⟨h.trans h'.symm, fun h2 => by omega⟩⟩

section Fusion

variable {z : G} (hzC : z ∈ centralizer (L : Set G))
  (hsup : L ⊔ zpowers z = centralizer ({z} : Set G)) (hinf : L ⊓ zpowers z = ⊥)
  (hz : orderOf z = 2)

include hinf hz in
theorem notMem_of_inf_eq_bot : z ∉ L := by
  intro hzL
  have : z ∈ L ⊓ zpowers z := Subgroup.mem_inf.2 ⟨hzL, mem_zpowers z⟩
  rw [hinf, mem_bot] at this
  rw [this, orderOf_one] at hz
  exact absurd hz (by norm_num)

variable [Finite G] [FiniteDimensional (ZMod 2) V]

include hzC hsup hinf hz in
theorem not_conj_of_rank_le_two (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) {y : G} (hy : y ∈ L)
    (hrk : finrank (ZMod 2) (LinearMap.range (linOf (φ ⟨y, hy⟩) - 1)) ≤ 2) :
    ¬ ∃ g : G, g * z * g⁻¹ = y := by
  rintro ⟨g, rfl⟩
  have hLH : L ≤ centralizer ({z} : Set G) := hsup ▸ le_sup_left
  have hzz : zpowers z ≤ centralizer (L : Set G) := zpowers_le.2 hzC
  have hHc : Nat.card (centralizer ({z} : Set G)) = Nat.card L * 2 := by
    rw [← hsup, card_sup_eq_mul hzz hinf, Nat.card_zpowers, hz]
  set H := centralizer ({z} : Set G) with hH
  have hidx : (L.subgroupOf H).index = 2 := by
    have h1 := (L.subgroupOf H).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hLH).toEquiv, hHc, mul_comm (Nat.card L)] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have : (L.subgroupOf H).Normal := Subgroup.normal_of_index_eq_two hidx
  set x := φ ⟨g * z * g⁻¹, hy⟩ with hx
  have hxo : orderOf x = 2 := by
    rw [hx, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, ← hz]
    exact MulEquiv.orderOf_eq (MulAut.conj g) z
  have hcomm : ∀ u ∈ centralizer ({x} : Set (bilinIsometryGroup b)),
      g⁻¹ * (φ.symm u : G) * g ∈ H := by
    intro u hu
    have h1 : φ.symm u * φ.symm x = φ.symm x * φ.symm u := by
      rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hu]
    rw [hx, MulEquiv.symm_apply_apply] at h1
    have h2 : (φ.symm u : G) * (g * z * g⁻¹) = (g * z * g⁻¹) * (φ.symm u : G) :=
      congrArg Subtype.val h1
    rw [hH, mem_centralizer_singleton_iff]
    calc g⁻¹ * (φ.symm u : G) * g * z = g⁻¹ * ((φ.symm u : G) * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * (φ.symm u : G)) * g := by rw [h2]
      _ = z * (g⁻¹ * (φ.symm u : G) * g) := by group
  let f : centralizer ({x} : Set (bilinIsometryGroup b)) →* H :=
    { toFun := fun u => ⟨g⁻¹ * (φ.symm u : G) * g, hcomm u u.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun u v => Subtype.ext (by simp only [Subgroup.coe_mul, map_mul]; group) }
  have hQ : Nat.card (H ⧸ L.subgroupOf H) = 2 := hidx
  have h1 := (involution_centralizer_obstruction hb hnd hV hxo).2.2.2 hrk
    (H ⧸ L.subgroupOf H) hQ ((QuotientGroup.mk' (L.subgroupOf H)).comp f)
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    mem_subgroupOf] at h1
  have h2 : ((f ⟨x, mem_centralizer_singleton_iff.2 rfl⟩ : H) : G) = z := by
    change g⁻¹ * (φ.symm x : G) * g = z
    rw [hx, MulEquiv.symm_apply_apply]
    group
  rw [h2] at h1
  exact notMem_of_inf_eq_bot hinf hz h1

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
include hzC in
theorem zpowers_le_centralizer_pullSub (P : Subgroup (bilinIsometryGroup b)) :
    zpowers z ≤ centralizer (pullSub φ P : Set G) := fun _ ht =>
  mem_centralizer_iff.2 fun a ha =>
    mem_centralizer_iff.1 (zpowers_le.2 hzC ht) a (pullSub_le φ P ha)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
include hz in
theorem eq_one_or_eq_of_mem_zpowers {s : G} (hs : s ∈ zpowers z) : s = 1 ∨ s = z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hs
  rw [← zpow_mod_orderOf, hz]
  have h : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases h with h | h <;> rw [h]
  · exact Or.inl (zpow_zero z)
  · exact Or.inr (zpow_one z)

include hzC hsup hinf hz he in
theorem conj_mem_pieces (hb : b.IsAlt) (hnd : b.Nondegenerate) (hV : finrank (ZMod 2) V = 6)
    {x : G} (hxR : x ∈ pullSub φ (pointwiseStabilizer b (lagrangianOf e)) ⊔ zpowers z)
    (hxz : ∃ g : G, g * z * g⁻¹ = x) :
    x ∈ {z} ∪ z • tauSet φ e (fun B => B.rank = 1) ∪
      z • tauSet φ e (fun B => B.rank = 2 ∧ ∀ i, B i i = 0) ∪
      z • tauSet φ e (fun B => B.rank = 2 ∧ ¬ ∀ i, B i i = 0) ∪
      z • tauSet φ e (fun B => B.rank = 3) ∪ tauSet φ e (fun B => B.rank = 3) := by
  obtain ⟨a, ha, s, hs, rfl⟩ := (mem_sup_of_le_centralizer
    (zpowers_le_centralizer_pullSub φ hzC _)).1 hxR
  obtain ⟨B, rfl⟩ := (mem_pullSub_iff φ he).1 ha
  have hrk3 := rank_le_card_width (B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2))
  rw [Fintype.card_fin] at hrk3
  rcases eq_one_or_eq_of_mem_zpowers hz hs with h | h <;> rw [h] at hxz ⊢
  ·
    rw [mul_one] at hxz ⊢
    refine Or.inr ((mem_tauSet_iff φ he).2 ⟨B, ?_, rfl⟩)
    by_contra hne
    have hle : finrank (ZMod 2) (LinearMap.range
        (linOf (φ ⟨tauHom φ he B, tauHom_mem φ he B⟩) - 1)) ≤ 2 := by
      rw [finrank_range_sub_one_eq_rank _ (toMatrix_tauHom φ he B)]
      omega
    exact not_conj_of_rank_le_two φ hzC hsup hinf hz hb hnd hV (tauHom_mem φ he B) hle hxz
  ·
    have hcomm : tauHom φ he B * z = z * tauHom φ he B :=
      mem_centralizer_iff.1 hzC _ (tauHom_mem φ he B)
    rw [hcomm]
    have hzmem : ∀ {P : Matrix (Fin 3) (Fin 3) (ZMod 2) → Prop},
        P (B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) → z * tauHom φ he B ∈ z • tauSet φ e P :=
      fun hP => Set.smul_mem_smul_set ((mem_tauSet_iff φ he).2 ⟨B, hP, rfl⟩)
    rcases sym_orbit_cases B.toAdd with h0 | h1 | h2 | h2 | h3
    · have hB : B = 1 := Multiplicative.toAdd.injective (Subtype.ext h0)
      rw [hB, map_one, mul_one]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl rfl))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (hzmem h1)))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr (hzmem h2))))
    · exact Or.inl (Or.inl (Or.inr (hzmem h2)))
    · exact Or.inl (Or.inr (hzmem h3))

end Fusion

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits
