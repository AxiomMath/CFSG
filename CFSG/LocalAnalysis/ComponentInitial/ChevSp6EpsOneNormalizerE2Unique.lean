module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerLagBasic

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

theorem utMat_mul_utMat_add : ∀ a b c : ZMod 2, utMat a b c * utMat a b (c + a * b) = 1 := by
  decide

theorem utMat_add_mul_utMat : ∀ a b c : ZMod 2, utMat a b (c + a * b) * utMat a b c = 1 := by
  decide

def utUnit (a b c : ZMod 2) : GL (Fin 3) (ZMod 2) :=
  ⟨utMat a b c, utMat a b (c + a * b), utMat_mul_utMat_add a b c, utMat_add_mul_utMat a b c⟩

theorem card_unitriangularGL : Nat.card (unitriangularGL 3 (ZMod 2)) = 8 := by
  refine le_antisymm card_unitriangularGL_le ?_
  have hinj : Function.Injective fun p : ZMod 2 × ZMod 2 × ZMod 2 =>
      (⟨utUnit p.1 p.2.1 p.2.2, mem_unitriangularGL.2 (isUnitriangular_utMat _ _ _)⟩ :
        unitriangularGL 3 (ZMod 2)) := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ hp
    have h' : utMat a b c = utMat a' b' c' :=
      congrArg (fun u : unitriangularGL 3 (ZMod 2) => ((u : GL (Fin 3) (ZMod 2)) : M₃)) hp
    have h1 := congrFun (congrFun h' 0) 1
    have h2 := congrFun (congrFun h' 1) 2
    have h3 := congrFun (congrFun h' 0) 2
    simp only [utMat, of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two,
      empty_val', cons_val_fin_one, head_cons, tail_cons] at h1 h2 h3
    rw [h1, h2, h3]
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_fintype_card (α := ZMod 2 × ZMod 2 × ZMod 2), Fintype.card_prod,
    Fintype.card_prod, ZMod.card] at this

theorem exists_conj_mem_unitriangularGL {W : Subgroup (GL (Fin 3) (ZMod 2))}
    (hW : IsPGroup 2 W) :
    ∃ k : GL (Fin 3) (ZMod 2), ∀ w ∈ W, k * w * k⁻¹ ∈ unitriangularGL 3 (ZMod 2) := by
  have hU : IsPGroup 2 (unitriangularGL 3 (ZMod 2)) :=
    IsPGroup.of_card (n := 3) (by rw [card_unitriangularGL]; norm_num)
  have hidx : (unitriangularGL 3 (ZMod 2)).index = 21 := by
    have := (unitriangularGL 3 (ZMod 2)).card_mul_index
    rw [card_unitriangularGL, card_glThree] at this
    omega
  let S : Sylow 2 (GL (Fin 3) (ZMod 2)) := hU.toSylow (by rw [hidx]; norm_num)
  obtain ⟨P, hWP⟩ := hW.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (GL (Fin 3) (ZMod 2)) P S
  refine ⟨k, fun w hw => ?_⟩
  have h1 : MulAut.conj k • w ∈ MulAut.conj k • (P : Subgroup (GL (Fin 3) (ZMod 2))) :=
    Subgroup.smul_mem_pointwise_smul w _ _ (hWP hw)
  rw [← Sylow.coe_subgroup_smul, hk] at h1
  exact h1

theorem card_fixed_alt_utMat_le : ∀ a b c : ZMod 2, utMat a b c ≠ 1 →
    (Finset.univ.filter fun x : SixBits => x.1 = 0 ∧ x.2.1 = 0 ∧ x.2.2.1 = 0 ∧
      utMat a b c * symMat x * (utMat a b c)ᵀ = symMat x).card ≤ 4 := by
  decide

theorem card_fixed_alt_le_four {M : M₃} (hM : IsUnitriangular M) (hM1 : M ≠ 1) :
    (Finset.univ.filter fun x : SixBits => x.1 = 0 ∧ x.2.1 = 0 ∧ x.2.2.1 = 0 ∧
      M * symMat x * Mᵀ = symMat x).card ≤ 4 := by
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, M = utMat a b c := ⟨_, _, _, utMat_of_isUnitriangular hM⟩
  exact card_fixed_alt_utMat_le a b c hM1

theorem symCoord_injective {B B' : M₃} (hB : Bᵀ = B) (hB' : B'ᵀ = B')
    (h : symCoord B = symCoord B') : B = B' := by
  rw [← symMat_symCoord hB, ← symMat_symCoord hB', h]

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} {he : IsSymplecticBasis b e}

variable {G : Type} [Group G] {L : Subgroup G} {φ : L ≃* bilinIsometryGroup b} {z : G}
  {hzC : z ∈ centralizer (L : Set G)} {hz : orderOf z = 2}

local notation "𝒜₂" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℛ" => radSub φ z e
local notation "𝒩₂" => normalizer ((radSub φ z e : Subgroup G) : Set G)

variable {D₂ C₂ E₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)}
variable {σ : ↥(normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G)) →*
  GL (Fin 3) (ZMod 2)}

theorem LagBase.eq_one_of_leviHom_mem (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ)
    (hinf : L ⊓ zpowers z = ⊥) {g : GL (Fin 3) (ZMod 2)} (hg : leviHom φ he g ∈ D₂) : g = 1 := by
  have hgi : (leviHom φ he g)⁻¹ ∈ D₂ := inv_mem hg
  have hfix : ∀ w : Fin 3 → ZMod 2, (g : M₃) *ᵥ w = w := by
    intro w
    obtain ⟨d, hd, hdk⟩ := h.kap_surjective hinf (0, w)
    have h1 := h.kap_levi_conj g hd
    rw [h.kap_mul hinf (mul_mem hg hd) hgi, h.kap_mul hinf hg hd] at h1
    have h2 : kap C₂ ν₂ (leviHom φ he g) + kap C₂ ν₂ (leviHom φ he g)⁻¹ = 0 := by
      rw [← h.kap_mul hinf hg hgi, mul_inv_cancel, h.kap_eq_zero_iff]
      exact one_mem _
    rw [add_right_comm, h2, zero_add, hdk] at h1
    exact (congrArg Prod.snd h1).symm
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h1 := congrFun (hfix (Pi.single j 1)) i
  rw [mulVec_single_one, Matrix.col_apply] at h1
  rw [Units.val_one, h1, Matrix.one_apply, Pi.single_apply]

theorem LagBase.levi_eq_of_mem (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ)
    (hinf : L ⊓ zpowers z = ⊥) {m : G} {g g' : GL (Fin 3) (ZMod 2)}
    (hg : m * (leviHom φ he g)⁻¹ ∈ D₂) (hg' : m * (leviHom φ he g')⁻¹ ∈ D₂) : g = g' := by
  have h1 : leviHom φ he (g * g'⁻¹) ∈ D₂ := by
    have h2 := mul_mem (inv_mem hg) hg'
    rwa [show (m * (leviHom φ he g)⁻¹)⁻¹ * (m * (leviHom φ he g')⁻¹) =
      leviHom φ he g * (leviHom φ he g')⁻¹ by group, ← map_inv, ← map_mul] at h2
  exact mul_inv_eq_one.1 (h.eq_one_of_leviHom_mem hinf h1)

theorem LagBase.exists_leviPart (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ)
    (hinf : L ⊓ zpowers z = ⊥) :
    ∃ π : 𝒩₂ →* GL (Fin 3) (ZMod 2), ∀ m : 𝒩₂, (m : G) * (leviHom φ he (π m))⁻¹ ∈ D₂ := by
  have hex : ∀ m : 𝒩₂, ∃ g : GL (Fin 3) (ZMod 2), (m : G) * (leviHom φ he g)⁻¹ ∈ D₂ := by
    intro m
    obtain ⟨d, hd, g, hm⟩ := h.exists_levi m.2
    exact ⟨g, by rw [hm, mul_inv_cancel_right]; exact hd⟩
  choose f hf using hex
  refine ⟨MonoidHom.mk' f fun a b => ?_, hf⟩
  refine (h.levi_eq_of_mem hinf (hf (a * b)) ?_)
  have hla : leviHom φ he (f a) ∈ 𝒩₂ := leviHom_mem_normalizer_radSub φ he hzC hz _
  have h2 := mul_mem (hf a) (h.hD₂n _ hla _ (hf b))
  rwa [show (a : G) * (leviHom φ he (f a))⁻¹ * (leviHom φ he (f a) * ((b : G) *
      (leviHom φ he (f b))⁻¹) * (leviHom φ he (f a))⁻¹) =
      ((a * b : 𝒩₂) : G) * (leviHom φ he (f a * f b))⁻¹ by
    rw [map_mul, Subgroup.coe_mul]; group] at h2

theorem LagBase.mem_normalizer_D₂ (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ) {n : G} (hn : n ∈ 𝒩₂) :
    n ∈ normalizer (D₂ : Set G) := by
  rw [mem_normalizer_iff]
  intro d
  refine ⟨fun hd => h.hD₂n n hn d hd, fun hd => ?_⟩
  have h1 := h.hD₂n _ (inv_mem hn) _ hd
  rwa [show n⁻¹ * (n * d * n⁻¹) * n⁻¹⁻¹ = d by group] at h1

theorem LagBase.conj_tauHom_of_mul_inv_mem (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ) {x : G}
    {g : GL (Fin 3) (ZMod 2)} (hxg : x * (leviHom φ he g)⁻¹ ∈ D₂)
    (B : ↥(binarySymMatrices 3)) :
    x * tauHom φ he (Multiplicative.ofAdd B) * x⁻¹ =
      tauHom φ he (Multiplicative.ofAdd (symThreeCongr g B)) := by
  have hA : tauHom φ he (Multiplicative.ofAdd (symThreeCongr g B)) ∈ 𝒜₂ :=
    (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
  have hc := h.D₂A hxg hA
  calc x * tauHom φ he (Multiplicative.ofAdd B) * x⁻¹ =
      x * (leviHom φ he g)⁻¹ * (leviHom φ he g * tauHom φ he (Multiplicative.ofAdd B) *
        (leviHom φ he g)⁻¹) * (x * (leviHom φ he g)⁻¹)⁻¹ := by group
    _ = x * (leviHom φ he g)⁻¹ * tauHom φ he (Multiplicative.ofAdd (symThreeCongr g B)) *
        (x * (leviHom φ he g)⁻¹)⁻¹ := by rw [leviHom_conj_tauHom']
    _ = _ := by rw [hc, mul_inv_cancel_right]

theorem LagBase.nu_conj_of_mul_inv_mem (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ)
    (hinf : L ⊓ zpowers z = ⊥) {x : G} {g : GL (Fin 3) (ZMod 2)}
    (hxg : x * (leviHom φ he g)⁻¹ ∈ D₂) {y : G} (hy : y ∈ D₂) :
    ν₂ (x * y * x⁻¹) = symThreeCongr g (ν₂ y) := by
  have hl : leviHom φ he g ∈ 𝒩₂ := leviHom_mem_normalizer_radSub φ he hzC hz g
  have hly : leviHom φ he g * y * (leviHom φ he g)⁻¹ ∈ D₂ := h.hD₂n _ hl y hy
  have hx : x * y * x⁻¹ = x * (leviHom φ he g)⁻¹ * (leviHom φ he g * y * (leviHom φ he g)⁻¹) *
      (x * (leviHom φ he g)⁻¹)⁻¹ := by group
  have h0 : ν₂ (x * (leviHom φ he g)⁻¹) + ν₂ (x * (leviHom φ he g)⁻¹)⁻¹ = 0 := by
    rw [← h.nu_mul hinf hxg (inv_mem hxg), mul_inv_cancel]
    exact h.nu_eq_zero_of_mem hinf (one_mem _)
  rw [hx, h.nu_mul hinf (mul_mem hxg hly) (inv_mem hxg), h.nu_mul hinf hxg hly,
    nu_conj_levi he φ hzC hz h.hν₂z h.hD₂n g hy, add_right_comm, h0, zero_add]

theorem LagBase.card_inf_A₂_le [Finite G] (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ)
    {X : Subgroup G} (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) {x₀ : G} (hx₀ : x₀ ∈ X)
    {g : GL (Fin 3) (ZMod 2)} (hxg : x₀ * (leviHom φ he g)⁻¹ ∈ D₂)
    (hgU : g ∈ unitriangularGL 3 (ZMod 2)) (hg1 : g ≠ 1) :
    Nat.card (X ⊓ 𝒜₂ : Subgroup G) ≤ 16 := by
  classical
  have hex : ∀ y : (X ⊓ 𝒜₂ : Subgroup G), ∃ B : ↥(binarySymMatrices 3),
      tauHom φ he (Multiplicative.ofAdd B) = y := by
    intro y
    obtain ⟨B, hB⟩ := (mem_pullSub_iff φ he).1 (mem_inf.1 y.2).2
    exact ⟨Multiplicative.toAdd B, hB⟩
  choose B hB using hex
  have hfix : ∀ y, symThreeCongr g (B y) = B y := by
    intro y
    have h1 := h.conj_tauHom_of_mul_inv_mem hxg (B y)
    rw [hB y, hXc x₀ hx₀ y (mem_inf.1 y.2).1, mul_inv_cancel_right, ← hB y] at h1
    exact (Multiplicative.ofAdd.injective (tauHom_injective φ he h1)).symm
  have hmem : ∀ y, symCoord (B y : M₃) ∈ Finset.univ.filter fun x : SixBits =>
      (g : M₃) * symMat x * (g : M₃)ᵀ = symMat x := by
    intro y
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rw [symMat_symCoord (binarySym_transpose _)]
    have h1 := congrArg Subtype.val (hfix y)
    rwa [coe_symThreeCongr] at h1
  have hinj : Function.Injective fun y => (⟨symCoord (B y : M₃), hmem y⟩ :
      (Finset.univ.filter fun x : SixBits => (g : M₃) * symMat x * (g : M₃)ᵀ = symMat x)) := by
    intro y y' hyy
    have h1 := symCoord_injective (binarySym_transpose _) (binarySym_transpose _)
      (congrArg Subtype.val hyy)
    have h2 : B y = B y' := Subtype.ext h1
    apply Subtype.ext
    rw [← hB y, ← hB y', h2]
  refine (Nat.card_le_card_of_injective _ hinj).trans ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  exact card_fixed_le_sixteen (mem_unitriangularGL.1 hgU) (fun h1 => hg1 (Units.ext h1))

theorem LagBase.card_inf_D₂_le [Finite G] (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ)
    (hinf : L ⊓ zpowers z = ⊥) {X : Subgroup G} (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (hXsq : ∀ x ∈ X, x ^ 2 = 1) {x₀ : G} (hx₀ : x₀ ∈ X) {g : GL (Fin 3) (ZMod 2)}
    (hxg : x₀ * (leviHom φ he g)⁻¹ ∈ D₂) (hgU : g ∈ unitriangularGL 3 (ZMod 2)) (hg1 : g ≠ 1) :
    Nat.card (X ⊓ D₂ : Subgroup G) ≤ 4 * Nat.card (X ⊓ 𝒜₂ : Subgroup G) := by
  classical
  by_cases hXC : X ⊓ D₂ ≤ C₂
  · have hXE : ∀ y ∈ X ⊓ D₂, y ∈ E₂ := fun y hy =>
      (h.hinv y (hXC hy)).1 (hXsq y (mem_inf.1 hy).1)
    let f : (X ⊓ D₂ : Subgroup G) →* Multiplicative ↥(binarySymMatrices 3) :=
      MonoidHom.mk' (fun y => Multiplicative.ofAdd (ν₂ y)) fun a b => by
        rw [Subgroup.coe_mul, h.nu_mul hinf (mem_inf.1 a.2).2 (mem_inf.1 b.2).2, ofAdd_add]
    have hcard : Nat.card (X ⊓ D₂ : Subgroup G) = Nat.card f.ker * Nat.card f.range := by
      rw [← Subgroup.index_ker, Subgroup.card_mul_index]
    have hker : Nat.card f.ker ≤ Nat.card (X ⊓ 𝒜₂ : Subgroup G) := by
      have hmem : ∀ y : f.ker, ((y : (X ⊓ D₂ : Subgroup G)) : G) ∈ X ⊓ 𝒜₂ := by
        intro y
        have hy0 : ν₂ ((y : (X ⊓ D₂ : Subgroup G)) : G) = 0 :=
          Multiplicative.ofAdd.injective (MonoidHom.mem_ker.1 y.2)
        exact mem_inf.2 ⟨(mem_inf.1 (y : (X ⊓ D₂ : Subgroup G)).2).1,
          (h.hνk _ (hXC (y : (X ⊓ D₂ : Subgroup G)).2)).1 hy0⟩
      refine Nat.card_le_card_of_injective
        (fun y => (⟨_, hmem y⟩ : (X ⊓ 𝒜₂ : Subgroup G))) fun y y' hyy => ?_
      have h1 := congrArg (fun w : (X ⊓ 𝒜₂ : Subgroup G) => (w : G)) hyy
      exact Subtype.ext (Subtype.ext h1)
    have hmem : ∀ M : f.range, symCoord ((Multiplicative.toAdd
        (M : Multiplicative ↥(binarySymMatrices 3)) : ↥(binarySymMatrices 3)) : M₃) ∈
        Finset.univ.filter fun x : SixBits => x.1 = 0 ∧ x.2.1 = 0 ∧ x.2.2.1 = 0 ∧
          (g : M₃) * symMat x * (g : M₃)ᵀ = symMat x := by
      rintro ⟨_, y, rfl⟩
      have hfix : symThreeCongr g (ν₂ y) = ν₂ y := by
        have h1 := h.nu_conj_of_mul_inv_mem hinf hxg (mem_inf.1 y.2).2
        rw [hXc x₀ hx₀ y (mem_inf.1 y.2).1, mul_inv_cancel_right] at h1
        exact h1.symm
      have hdiag : symThreeDiag (ν₂ y : M₃) = 0 := (h.hδk _ (hXC y.2)).2 (hXE _ y.2)
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, congrFun hdiag 0, congrFun hdiag 1,
        congrFun hdiag 2, ?_⟩
      change (g : M₃) * symMat (symCoord (ν₂ y : M₃)) * (g : M₃)ᵀ =
        symMat (symCoord (ν₂ y : M₃))
      rw [symMat_symCoord (binarySym_transpose _)]
      have h1 := congrArg Subtype.val hfix
      rwa [coe_symThreeCongr] at h1
    have hinj : Function.Injective fun M : f.range => (⟨_, hmem M⟩ :
        (Finset.univ.filter fun x : SixBits => x.1 = 0 ∧ x.2.1 = 0 ∧ x.2.2.1 = 0 ∧
          (g : M₃) * symMat x * (g : M₃)ᵀ = symMat x)) := by
      intro M M' hMM
      have h1 := symCoord_injective (binarySym_transpose _) (binarySym_transpose _)
        (congrArg Subtype.val hMM)
      exact Subtype.ext (Multiplicative.toAdd.injective (Subtype.ext h1))
    have hran : Nat.card f.range ≤ 4 := by
      refine (Nat.card_le_card_of_injective _ hinj).trans ?_
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      exact card_fixed_alt_le_four (mem_unitriangularGL.1 hgU) (fun h1 => hg1 (Units.ext h1))
    rw [hcard, mul_comm 4]
    exact Nat.mul_le_mul hker hran
  · obtain ⟨p, hpXD, hpC⟩ := Set.not_subset.1 hXC
    have hc := (h.mem_D₂_cases (mem_inf.1 hpXD).2).resolve_left hpC
    have hle : C₂ ⊓ (X ⊓ D₂) ≤ X ⊓ 𝒜₂ := by
      intro q hq
      obtain ⟨hqC, hqXD⟩ := mem_inf.1 hq
      have hqX := (mem_inf.1 hqXD).1
      have hqE : q ∈ E₂ := (h.hinv q hqC).1 (hXsq q hqX)
      have e1 : p * q = q * p := hXc p (mem_inf.1 hpXD).1 q hqX
      have e2 : (z⁻¹ * p) * q = q * (z⁻¹ * p) := (h.comm_E₂ hqE hc).symm
      have hqz : z * q = q * z := by
        calc z * q = z * (q * (z⁻¹ * p)) * (z⁻¹ * p)⁻¹ := by group
          _ = z * ((z⁻¹ * p) * q) * (z⁻¹ * p)⁻¹ := by rw [e2]
          _ = p * q * (z⁻¹ * p)⁻¹ := by group
          _ = q * p * (z⁻¹ * p)⁻¹ := by rw [e1]
          _ = q * z := by group
      have hqR : q ∈ ℛ := by
        rw [← h.hD₂H]
        exact mem_inf.2 ⟨h.E₂D₂ hqE, mem_centralizer_singleton_iff.2 hqz.symm⟩
      refine mem_inf.2 ⟨hqX, ?_⟩
      rw [← h.hE₂R]
      exact mem_inf.2 ⟨hqE, hqR⟩
    have h1 := Subgroup.card_le_of_le hle
    have h2 : C₂.relIndex (X ⊓ D₂) ≤ 2 := by
      rw [← h.relIndex_C₂]
      exact Subgroup.relIndex_le_of_le_right inf_le_right (by rw [h.relIndex_C₂]; norm_num)
    have h3 := Subgroup.relIndex_mul_card (H := C₂) (K := X ⊓ D₂)
    have h4 := Nat.mul_le_mul h2 h1
    omega

theorem LagBase.eq_E₂_of_le_N₂_of_unitriangular [Finite G]
    (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ) (hinf : L ⊓ zpowers z = ⊥) {X : Subgroup G}
    (hXN : X ≤ 𝒩₂) (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hXsq : ∀ x ∈ X, x ^ 2 = 1)
    (hXcard : Nat.card X = 512) (π : 𝒩₂ →* GL (Fin 3) (ZMod 2))
    (hπ : ∀ m : 𝒩₂, (m : G) * (leviHom φ he (π m))⁻¹ ∈ D₂)
    (hU : ∀ x (hx : x ∈ X), π ⟨x, hXN hx⟩ ∈ unitriangularGL 3 (ZMod 2)) : X = E₂ := by
  by_cases hXD : X ≤ D₂
  · exact h.eq_E₂_of_le_D₂ hXD hXsq hXcard
  exfalso
  obtain ⟨x₀, hx₀X, hx₀D⟩ := Set.not_subset.1 hXD
  have hg1 : π ⟨x₀, hXN hx₀X⟩ ≠ 1 := by
    intro h1
    apply hx₀D
    have h2 := hπ ⟨x₀, hXN hx₀X⟩
    rwa [h1, map_one, inv_one, mul_one] at h2
  have hA := h.card_inf_A₂_le hXc hx₀X (hπ ⟨x₀, hXN hx₀X⟩) (hU x₀ hx₀X) hg1
  have hD := h.card_inf_D₂_le hinf hXc hXsq hx₀X (hπ ⟨x₀, hXN hx₀X⟩) (hU x₀ hx₀X) hg1
  let ρ : X →* GL (Fin 3) (ZMod 2) := π.comp (Subgroup.inclusion hXN)
  have hρU : ρ.range ≤ unitriangularGL 3 (ZMod 2) := by
    rintro _ ⟨y, rfl⟩
    exact hU y y.2
  have hρc : ∀ a ∈ ρ.range, ∀ b ∈ ρ.range, a * b = b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (Subtype.ext (hXc x x.2 y y.2))
  have h4 := card_le_four_of_le_unitriangularGL hρU hρc
  have hker : Nat.card ρ.ker ≤ Nat.card (X ⊓ D₂ : Subgroup G) := by
    have hmem : ∀ y : ρ.ker, ((y : X) : G) ∈ X ⊓ D₂ := by
      intro y
      refine mem_inf.2 ⟨(y : X).2, ?_⟩
      have h1 := hπ ⟨(y : X), hXN (y : X).2⟩
      have h2 : π ⟨(y : X), hXN (y : X).2⟩ = 1 := MonoidHom.mem_ker.1 y.2
      rwa [h2, map_one, inv_one, mul_one] at h1
    refine Nat.card_le_card_of_injective (fun y => (⟨_, hmem y⟩ : (X ⊓ D₂ : Subgroup G)))
      fun y y' hyy => ?_
    have h1 := congrArg (fun w : (X ⊓ D₂ : Subgroup G) => (w : G)) hyy
    exact Subtype.ext (Subtype.ext h1)
  have hcard : Nat.card X = Nat.card ρ.ker * Nat.card ρ.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have h5 := Nat.mul_le_mul (hker.trans (hD.trans (Nat.mul_le_mul_left 4 hA))) h4
  omega

theorem LagBase.eq_E₂_of_le_N₂ [Finite G] (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ)
    (hinf : L ⊓ zpowers z = ⊥) {X : Subgroup G}
    (hXN : X ≤ normalizer ((radSub φ z e : Subgroup G) : Set G))
    (hX : IsElementaryAbelian 2 X) (hXcard : Nat.card X = 512) : X = E₂ := by
  have := hX
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (isMulCommutative_iff.1 hX.toIsMulCommutative ⟨x, hx⟩ ⟨y, hy⟩)
  have hXsq : ∀ x ∈ X, x ^ 2 = 1 := fun x hx =>
    elemPow_eq_one_of_isElementaryAbelian (A := X) x hx
  obtain ⟨π, hπ⟩ := h.exists_leviPart hinf
  let ρ : X →* GL (Fin 3) (ZMod 2) := π.comp (Subgroup.inclusion hXN)
  have hW : IsPGroup 2 ρ.range :=
    (IsElementaryAbelian.isPGroup 2 X).of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  obtain ⟨k, hk⟩ := exists_conj_mem_unitriangularGL hW
  have hl : leviHom φ he k ∈ 𝒩₂ := leviHom_mem_normalizer_radSub φ he hzC hz k
  have hπl : π ⟨_, hl⟩ = k :=
    h.levi_eq_of_mem hinf (hπ ⟨_, hl⟩) (by rw [mul_inv_cancel]; exact one_mem _)
  set X' := X.map (MulAut.conj (leviHom φ he k)).toMonoidHom with hX'
  have hX'N : X' ≤ 𝒩₂ := by
    rintro _ ⟨y, hy, rfl⟩
    exact mul_mem (mul_mem hl (hXN hy)) (inv_mem hl)
  have hX'c : ∀ x ∈ X', ∀ y ∈ X', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hXc x hx y hy]
  have hX'sq : ∀ x ∈ X', x ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hXsq x hx, map_one]
  have hX'card : Nat.card X' = 512 := by
    rw [hX', Subgroup.card_map_of_injective (MulAut.conj _).injective, hXcard]
  have hU : ∀ x (hx : x ∈ X'), π ⟨x, hX'N hx⟩ ∈ unitriangularGL 3 (ZMod 2) := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : π ⟨_, hX'N ⟨y, hy, rfl⟩⟩ = π ⟨_, hl⟩ * π ⟨y, hXN hy⟩ * (π ⟨_, hl⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [h1, hπl]
    exact hk _ ⟨⟨y, hy⟩, rfl⟩
  have hE := h.eq_E₂_of_le_N₂_of_unitriangular hinf hX'N hX'c hX'sq hX'card π hπ hU
  have hlQ := h.mem_normalizer_D₂ (inv_mem hl)
  refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [hXcard, h.hE₂card])
  have h1 : leviHom φ he k * x * (leviHom φ he k)⁻¹ ∈ E₂ := by
    rw [← hE]
    exact ⟨x, hx, rfl⟩
  have h2 := h.conj_mem_E₂ hlQ h1
  rwa [inv_inv, show (leviHom φ he k)⁻¹ * (leviHom φ he k * x * (leviHom φ he k)⁻¹) *
    leviHom φ he k = x by group] at h2

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne
