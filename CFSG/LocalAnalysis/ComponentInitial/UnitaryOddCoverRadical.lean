module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFourCore
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCover

open Matrix CFSG.ClassicalGroups.UnitaryFlag MatrixExtension
open scoped commutatorElement

section Group

variable {G : Type*} [Group G]

theorem commutatorElement_mul_left' (a b c : G) : ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_mul_right' (a b c : G) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem conj_eq_of_mem_center {z : G} (hz : z ∈ Subgroup.center G) (g : G) :
    z * g * z⁻¹ = g := by
  rw [← Subgroup.mem_center_iff.mp hz g, mul_inv_cancel_right]

theorem conj_central {z : G} (hz : z ∈ Subgroup.center G) (g : G) : g * z * g⁻¹ = z := by
  rw [Subgroup.mem_center_iff.mp hz g, mul_inv_cancel_right]

theorem commutatorElement_central_mul {a b c d : G} (hc : c ∈ Subgroup.center G)
    (hd : d ∈ Subgroup.center G) : ⁅c * a, d * b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc c * a * (d * b) * (c * a)⁻¹ * (d * b)⁻¹
      = c * (a * (d * b) * a⁻¹) * c⁻¹ * (b⁻¹ * d⁻¹) := by group
    _ = a * (d * b) * a⁻¹ * (b⁻¹ * d⁻¹) := by rw [conj_eq_of_mem_center hc]
    _ = a * (d * (b * a⁻¹ * b⁻¹) * d⁻¹) := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [conj_eq_of_mem_center hd]; group

end Group

section General

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K} {r : ℕ}
  {E : Type*} [Group E] {θ : E →* hypPSU h r 1}

variable (θ) in
@[expose] def IsN (x : Fin r → K) (m : E) : Prop :=
  ∃ (C : Matrix (Fin r) (Fin r) K) (hC : IsRad h x C), θ m = hypProj h r 1 (nElt hC)

variable (θ) in
@[expose] def IsV (B : Matrix (Fin r) (Fin r) K) (t : E) : Prop :=
  ∃ hB : IsRad h 0 B, θ t = hypProj h r 1 (nElt hB)

variable (θ) in
@[expose] def preN : Subgroup E :=
  ((radN h r).map (hypProj h r 1)).comap θ

variable (θ) in
@[expose] def preV : Subgroup E :=
  ((radV h r).map (hypProj h r 1)).comap θ

theorem mem_preN {m : E} : m ∈ preN θ ↔ ∃ x, IsN θ x m := by
  constructor
  · rintro ⟨_, ⟨x, C, hC, rfl⟩, he⟩
    exact ⟨x, C, hC, he.symm⟩
  · rintro ⟨x, C, hC, he⟩
    exact ⟨_, nElt_mem_radN hC, he.symm⟩

theorem mem_preV {t : E} : t ∈ preV θ ↔ ∃ B, IsV θ B t := by
  constructor
  · rintro ⟨_, ⟨B, hB, rfl⟩, he⟩
    exact ⟨B, hB, he.symm⟩
  · rintro ⟨B, hB, he⟩
    exact ⟨_, nElt_mem_radV hB, he.symm⟩

theorem IsN.mem {x : Fin r → K} {m : E} (hm : IsN θ x m) : m ∈ preN θ :=
  mem_preN.mpr ⟨x, hm⟩

theorem IsV.mem {B : Matrix (Fin r) (Fin r) K} {t : E} (ht : IsV θ B t) : t ∈ preV θ :=
  mem_preV.mpr ⟨B, ht⟩

theorem preV_le_preN : preV θ ≤ preN θ :=
  Subgroup.comap_mono (Subgroup.map_mono radV_le_radN)

theorem IsN.congr {x y : Fin r → K} {m : E} (hm : IsN θ x m) (hxy : x = y) : IsN θ y m :=
  hxy ▸ hm

theorem IsV.congr {B B' : Matrix (Fin r) (Fin r) K} {t : E} (ht : IsV θ B t) (hB : B = B') :
    IsV θ B' t :=
  hB ▸ ht

theorem isN_zero_iff {m : E} : IsN θ 0 m ↔ m ∈ preV θ := by
  rw [mem_preV]
  constructor
  · rintro ⟨C, hC, he⟩
    exact ⟨C, hC, he⟩
  · rintro ⟨B, hB, he⟩
    exact ⟨B, hB, he⟩

theorem IsN.mul {x y : Fin r → K} {m m' : E} (hm : IsN θ x m) (hm' : IsN θ y m') :
    IsN θ (x + y) (m * m') := by
  obtain ⟨C, hC, he⟩ := hm
  obtain ⟨D, hD, he'⟩ := hm'
  exact ⟨_, isRad_mul hC hD, by rw [map_mul, he, he', ← map_mul, nElt_mul]⟩

theorem IsN.inv {x : Fin r → K} {m : E} (hm : IsN θ x m) : IsN θ (-x) m⁻¹ := by
  obtain ⟨C, hC, he⟩ := hm
  exact ⟨_, isRad_inv hC, by rw [map_inv, he, ← map_inv, nElt_inv]⟩

theorem IsN.inv_mul_mem {x : Fin r → K} {m m' : E} (hm : IsN θ x m) (hm' : IsN θ x m') :
    m⁻¹ * m' ∈ preV θ :=
  isN_zero_iff.mp ((hm.inv.mul hm').congr (neg_add_cancel x))

theorem IsV.mul {B B' : Matrix (Fin r) (Fin r) K} {t t' : E} (ht : IsV θ B t)
    (ht' : IsV θ B' t') : IsV θ (B + B') (t * t') := by
  obtain ⟨hB, he⟩ := ht
  obtain ⟨hB', he'⟩ := ht'
  have hBB : IsRad h 0 (B + B') := by
    have := isRad_mul hB hB'
    rwa [add_zero, zero_vecMulVec, sub_zero] at this
  refine ⟨hBB, ?_⟩
  rw [map_mul, he, he', ← map_mul, nElt_mul]
  exact congrArg _ (nElt_ext _ _ (add_zero 0) (by rw [zero_vecMulVec, sub_zero]))

theorem IsV.inv {B : Matrix (Fin r) (Fin r) K} {t : E} (ht : IsV θ B t) : IsV θ (-B) t⁻¹ := by
  obtain ⟨hB, he⟩ := ht
  have hB' : IsRad h 0 (-B) := by
    have := isRad_inv hB
    rwa [neg_zero, zero_vecMulVec, sub_zero] at this
  refine ⟨hB', ?_⟩
  rw [map_inv, he, ← map_inv, nElt_inv]
  exact congrArg _ (nElt_ext _ _ neg_zero (by rw [zero_vecMulVec, sub_zero]))

theorem isV_zero_iff {t : E} : IsV θ 0 t ↔ θ t = 1 := by
  constructor
  · rintro ⟨hB, he⟩
    rw [he, show nElt hB = 1 from nElt_zero h, map_one]
  · intro he
    exact ⟨isRad_zero h, by rw [he, nElt_zero, map_one]⟩

theorem IsV.map_inv_mul_eq_one {B : Matrix (Fin r) (Fin r) K} {t t' : E} (ht : IsV θ B t)
    (ht' : IsV θ B t') : θ (t⁻¹ * t') = 1 :=
  isV_zero_iff.mp ((ht.inv.mul ht').congr (neg_add_cancel B))

theorem exists_isN (hθ : Function.Surjective θ) (x : Fin r → K) : ∃ m, IsN θ x m := by
  obtain ⟨C, hC⟩ := exists_isRad (h := h) x
  obtain ⟨m, hm⟩ := hθ (hypProj h r 1 (nElt hC))
  exact ⟨m, C, hC, hm⟩

theorem exists_isV (hθ : Function.Surjective θ) {B : Matrix (Fin r) (Fin r) K}
    (hB : IsRad h 0 B) : ∃ t, IsV θ B t := by
  obtain ⟨t, ht⟩ := hθ (hypProj h r 1 (nElt hB))
  exact ⟨t, hB, ht⟩

theorem IsV.eq_of_isV (hr : 1 ≤ r) {B B' : Matrix (Fin r) (Fin r) K} {t : E} (ht : IsV θ B t)
    (ht' : IsV θ B' t) : B = B' := by
  obtain ⟨hB, he⟩ := ht
  obtain ⟨hB', he'⟩ := ht'
  have hinj := hypProj_injective_on h hr le_rfl
  have : (⟨nElt hB, nElt_mem_hypUnitriangular hB⟩ : hypUnitriangular h r 1) =
      ⟨nElt hB', nElt_mem_hypUnitriangular hB'⟩ :=
    hinj (Subtype.ext (by
      simp only [MonoidHom.subgroupMap_apply_coe]
      rw [← he, ← he']))
  exact (eq_of_nElt_eq (hC := hB) (hD := hB') (congrArg Subtype.val this)).2

theorem IsN.commutatorElement {x y : Fin r → K} {m m' : E} (hm : IsN θ x m) (hm' : IsN θ y m') :
    IsV θ (vecMulVec y (fun j => h.bar (x j)) - vecMulVec x fun j => h.bar (y j)) ⁅m, m'⁆ := by
  obtain ⟨C, hC, he⟩ := hm
  obtain ⟨D, hD, he'⟩ := hm'
  refine ⟨isRad_comm h x y, ?_⟩
  rw [map_commutatorElement, he, he', ← map_commutatorElement, commutatorElement_def,
    nElt_mul_comm hC hD,
    show ∀ a b c : hypSU h r 1, a * (b * c) * c⁻¹ * b⁻¹ = a from fun a b c => by group]

theorem IsN.conj {x : Fin r → K} {m g : E} (hm : IsN θ x m) (A : GL (Fin r) K)
    (hg : θ g = hypProj h r 1 (lHom h r A)) :
    IsN θ ((dval h (A : Matrix (Fin r) (Fin r) K))⁻¹ • ((A : Matrix (Fin r) (Fin r) K) *ᵥ x))
      (g * m * g⁻¹) := by
  obtain ⟨C, hC, he⟩ := hm
  obtain ⟨hC', he'⟩ := exists_lHom_mul_nElt A hC
  exact ⟨_, hC', by rw [map_mul, map_mul, map_inv, hg, he, ← map_inv, ← map_mul, ← map_mul, he']⟩

theorem IsV.conj {B : Matrix (Fin r) (Fin r) K} {t g : E} (ht : IsV θ B t) (A : GL (Fin r) K)
    (hg : θ g = hypProj h r 1 (lHom h r A)) :
    IsV θ (A * B * ((A : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ) (g * t * g⁻¹) := by
  obtain ⟨hB, he⟩ := ht
  obtain ⟨hB', he'⟩ := exists_lHom_mul_nElt A hB
  rw [mulVec_zero, smul_zero] at hB'
  refine ⟨hB', ?_⟩
  rw [map_mul, map_mul, map_inv, hg, he, ← map_inv, ← map_mul, ← map_mul, he']
  exact congrArg _ (nElt_ext _ _ (by rw [mulVec_zero, smul_zero]) rfl)

theorem commutatorElement_mem_center (hC : θ.ker ≤ Subgroup.center E) {t m : E}
    (ht : t ∈ preV θ) (hm : m ∈ preN θ) : ⁅t, m⁆ ∈ Subgroup.center E := by
  refine hC ?_
  obtain ⟨g, hg, hgt⟩ := ht
  obtain ⟨g', hg', hgm⟩ := hm
  rw [MonoidHom.mem_ker, map_commutatorElement, ← hgt, ← hgm, ← map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm_of_mem_radV hg hg'), map_one]

theorem commutatorElement_mem_preV {m m' : E} (hm : m ∈ preN θ) (hm' : m' ∈ preN θ) :
    ⁅m, m'⁆ ∈ preV θ := by
  obtain ⟨g, hg, hgm⟩ := hm
  obtain ⟨g', hg', hgm'⟩ := hm'
  refine ⟨⁅g, g'⁆, commutatorElement_mem_radV hg hg', ?_⟩
  rw [map_commutatorElement, hgm, hgm', map_commutatorElement]

theorem commutatorElement_eq_of_map_eq_left (hC : θ.ker ≤ Subgroup.center E) {t t' : E}
    (htt : θ t = θ t') (m : E) : ⁅t, m⁆ = ⁅t', m⁆ := by
  have hc : t⁻¹ * t' ∈ Subgroup.center E := hC (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, htt, inv_mul_cancel])
  have e : t' = (t⁻¹ * t') * t := by
    rw [← Subgroup.mem_center_iff.mp hc t]
    group
  rw [e, ← one_mul m, commutatorElement_central_mul hc (Subgroup.one_mem _), one_mul]

theorem mul_comm_of_commutatorElement_eq_one {a b : E} (hab : ⁅a, b⁆ = 1) : a * b = b * a :=
  commutatorElement_eq_one_iff_mul_comm.mp hab

end General

section FieldTwo

variable {K : Type} [Field K] [CharP K 2] {h : UnitaryFieldData 2 1 K} {r : ℕ}
  {E : Type*} [Group E] {θ : E →* hypPSU h r 1}

theorem isRad_zero_add {B B' : Matrix (Fin r) (Fin r) K} (hB : IsRad h 0 B) (hB' : IsRad h 0 B') :
    IsRad h 0 (B + B') := by
  rw [isRad_zero_iff] at hB hB' ⊢
  rw [hconj_add, hB, hB']

theorem isRad_zero_neg {B : Matrix (Fin r) (Fin r) K} (hB : IsRad h 0 B) : IsRad h 0 (-B) := by
  rw [isRad_zero_iff] at hB ⊢
  ext i j
  rw [hconj_apply, Matrix.neg_apply, Matrix.neg_apply, neg_sq, CharTwo.neg_eq, ← hconj_apply, hB]

theorem isRad_zero_hermH (x y : Fin r → K) : IsRad h 0 (hermH x y) := by
  have := isRad_comm h x y
  rwa [commMat_eq_hermH] at this

theorem nElt_hermH_mem_commutator (x y : Fin r → K) :
    nElt (isRad_zero_hermH (h := h) x y) ∈ ⁅radN h r, radN h r⁆ := by
  obtain ⟨C, hC⟩ := exists_isRad (h := h) x
  obtain ⟨D, hD⟩ := exists_isRad (h := h) y
  have hm := Subgroup.commutator_mem_commutator (nElt_mem_radN hC) (nElt_mem_radN hD)
  rw [commutatorElement_def, nElt_mul_comm hC hD,
    show ∀ a b c : hypSU h r 1, a * (b * c) * c⁻¹ * b⁻¹ = a from fun a b c => by group] at hm
  rwa [nElt_ext (isRad_comm h x y) (isRad_zero_hermH x y) rfl (commMat_eq_hermH h x y)] at hm

theorem radV_le_commutator : radV h r ≤ ⁅radN h r, radN h r⁆ := by
  rintro _ ⟨B, hB, rfl⟩
  let S : AddSubgroup (Matrix (Fin r) (Fin r) K) :=
    { carrier := {B | ∃ hB : IsRad h 0 B, nElt hB ∈ ⁅radN h r, radN h r⁆}
      zero_mem' := ⟨isRad_zero h, by rw [nElt_zero]; exact one_mem _⟩
      add_mem' := by
        rintro B B' ⟨hB, h1⟩ ⟨hB', h2⟩
        refine ⟨isRad_zero_add hB hB', ?_⟩
        have := mul_mem h1 h2
        rwa [nElt_mul, nElt_ext _ (isRad_zero_add hB hB') (add_zero 0)
          (by rw [zero_vecMulVec, sub_zero])] at this
      neg_mem' := by
        rintro B ⟨hB, h1⟩
        have hB' : IsRad h 0 (-B) := isRad_zero_neg hB
        refine ⟨hB', ?_⟩
        have := inv_mem h1
        rwa [nElt_inv, nElt_ext _ hB' neg_zero (by rw [zero_vecMulVec, sub_zero])] at this }
  have hK := card_eq_four h
  obtain ⟨ω, hω0, hω1⟩ := four_exists_omega hK
  have hω : ω + ω ^ 2 = 1 := by
    rw [four_omega_sq hK hω0 hω1]
    linear_combination four_add_self ω
  have hmem : B ∈ S := by
    refine herm_mem (S := S) (fun k => ?_) (fun i j _ u => ?_) (isRad_zero_iff.mp hB)
    · have e : hermD k = hermH (Pi.single k ω) (Pi.single k (1 : K)) := by
        rw [hermH_single, one_pow, mul_one, one_mul, ← single_add, hω, hermD]
      rw [e]
      exact ⟨_, nElt_hermH_mem_commutator _ _⟩
    · rw [hermO_eq_hermH]
      exact ⟨_, nElt_hermH_mem_commutator _ _⟩
  obtain ⟨hB', hmem'⟩ := hmem
  exact hmem'

variable (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)

omit [CharP K 2] in
include hC in
theorem mul_comm_commutatorElement_of_mem_preV {z m m' : E} (hz : z ∈ preV θ)
    (hm : m ∈ preN θ) (hm' : m' ∈ preN θ) : z * ⁅m, m'⁆ = ⁅m, m'⁆ * z := by
  have h1 : z * ⁅m, m'⁆ * z⁻¹ = ⁅m, m'⁆ := by
    rw [conjugate_commutatorElement,
      show z * m * z⁻¹ = ⁅z, m⁆ * m by rw [commutatorElement_def]; group,
      show z * m' * z⁻¹ = ⁅z, m'⁆ * m' by rw [commutatorElement_def]; group,
      commutatorElement_central_mul (commutatorElement_mem_center hC hz hm)
        (commutatorElement_mem_center hC hz hm')]
  calc z * ⁅m, m'⁆ = z * ⁅m, m'⁆ * z⁻¹ * z := by group
    _ = ⁅m, m'⁆ * z := by rw [h1]

include hθ hC in
theorem mul_comm_of_mem_preV {t z : E} (ht : t ∈ preV θ) (hz : z ∈ preV θ) : t * z = z * t := by
  have hle : ⁅preN θ, preN θ⁆ ≤ Subgroup.centralizer {z} := by
    rw [Subgroup.commutator_le]
    intro m hm m' hm'
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact mul_comm_commutatorElement_of_mem_preV hC hz hm hm'
  have hθt : θ t ∈ (⁅preN θ, preN θ⁆).map θ := by
    rw [Subgroup.map_commutator, preN, Subgroup.map_comap_eq_self_of_surjective hθ,
      ← Subgroup.map_commutator]
    obtain ⟨g, hg, hgt⟩ := ht
    exact ⟨g, radV_le_commutator hg, hgt⟩
  obtain ⟨s, hs, hst⟩ := hθt
  have hc : s⁻¹ * t ∈ Subgroup.center E := hC (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hst, inv_mul_cancel])
  have hsz : z * s = s * z := Subgroup.mem_centralizer_iff.mp (hle hs) z rfl
  have hcz : z * (s⁻¹ * t) = (s⁻¹ * t) * z := Subgroup.mem_center_iff.mp hc z
  calc t * z = s * ((s⁻¹ * t) * z) := by group
    _ = s * (z * (s⁻¹ * t)) := by rw [hcz]
    _ = (z * s) * (s⁻¹ * t) := by rw [hsz]; group
    _ = z * t := by group

omit [CharP K 2] in
include hC in
theorem commutatorElement_mul_preV {t t' m : E} (ht : t ∈ preV θ) (ht' : t' ∈ preV θ)
    (hm : m ∈ preN θ) : ⁅t * t', m⁆ = ⁅t, m⁆ * ⁅t', m⁆ := by
  rw [commutatorElement_mul_left', conj_central (commutatorElement_mem_center hC ht' hm)]
  exact Subgroup.mem_center_iff.mp (commutatorElement_mem_center hC ht hm) _

omit [CharP K 2] in
include hC in
theorem commutatorElement_preV_mul {t m m' : E} (ht : t ∈ preV θ) (hm' : m' ∈ preN θ) :
    ⁅t, m * m'⁆ = ⁅t, m⁆ * ⁅t, m'⁆ := by
  rw [commutatorElement_mul_right', conj_central (commutatorElement_mem_center hC ht hm')]

include hθ hC in
theorem commutatorElement_eq_of_isN {t m m' : E} {x : Fin r → K} (ht : t ∈ preV θ)
    (hm : IsN θ x m) (hm' : IsN θ x m') : ⁅t, m⁆ = ⁅t, m'⁆ := by
  have hτ := hm.inv_mul_mem hm'
  rw [show m' = m * (m⁻¹ * m') by group, commutatorElement_preV_mul hC ht
    (preV_le_preN hτ), commutatorElement_eq_one_iff_mul_comm.mpr
      (mul_comm_of_mem_preV hθ hC ht hτ), mul_one]

include hθ hC in
theorem commutatorElement_mul_preV_right {t m τ : E} (ht : t ∈ preV θ) (hτ : τ ∈ preV θ) :
    ⁅t, m * τ⁆ = ⁅t, m⁆ := by
  rw [commutatorElement_preV_mul hC ht (preV_le_preN hτ),
    commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm_of_mem_preV hθ hC ht hτ), mul_one]

include hθ hC in
theorem commutatorElement_eq_one_of_weight_N {t : E} (ht : t ∈ preV θ) {ψ : K → Fin r → K}
    (hψ : ∀ s s', ψ (s + s') = ψ s + ψ s') {g : E} {ζ : K} (hζ : ζ ≠ 1)
    (hgt : θ (g * t * g⁻¹) = θ t)
    (hgψ : ∀ s m, IsN θ (ψ s) m → IsN θ (ψ (ζ * s)) (g * m * g⁻¹)) {s : K} {m : E}
    (hm : IsN θ (ψ s) m) : ⁅t, m⁆ = 1 := by
  choose ℓ hℓ using fun s => exists_isN hθ (ψ s)
  have hF := SymplecticCoverFour.eq_one_of_add_of_mul_invariant (ψ := fun s => ⁅t, ℓ s⁆)
    (fun s s' => by
      rw [commutatorElement_eq_of_isN hθ hC ht (hℓ (s + s'))
        (((hℓ s).mul (hℓ s')).congr (hψ s s').symm),
        commutatorElement_preV_mul hC ht (hℓ s').mem])
    hζ (fun s => by
      have hc := commutatorElement_mem_center hC ht (hℓ s).mem
      change ⁅t, ℓ (ζ * s)⁆ = ⁅t, ℓ s⁆
      rw [← conj_central hc g, conjugate_commutatorElement,
        commutatorElement_eq_of_map_eq_left hC hgt,
        commutatorElement_eq_of_isN hθ hC ht (hgψ s _ (hℓ s)) (hℓ (ζ * s))]) s
  rw [commutatorElement_eq_of_isN hθ hC ht hm (hℓ s)]
  exact hF

include hθ hC in
theorem commutatorElement_eq_one_of_weight_V {m : E} (hm : m ∈ preN θ)
    {φ : K → Matrix (Fin r) (Fin r) K} (hφ : ∀ s s', φ (s + s') = φ s + φ s')
    (hφV : ∀ s, IsRad h 0 (φ s)) {g : E} {ζ : K} (hζ : ζ ≠ 1)
    (hgm : m⁻¹ * (g * m * g⁻¹) ∈ preV θ)
    (hgφ : ∀ s t, IsV θ (φ s) t → IsV θ (φ (ζ * s)) (g * t * g⁻¹)) {s : K} {t : E}
    (ht : IsV θ (φ s) t) : ⁅t, m⁆ = 1 := by
  choose ℓ hℓ using fun s => exists_isV hθ (hφV s)
  have heq : ∀ {B : Matrix (Fin r) (Fin r) K} {u u' : E}, IsV θ B u → IsV θ B u' →
      θ u = θ u' := fun hu hu' => by
    have := hu.map_inv_mul_eq_one hu'
    rwa [map_mul, map_inv, inv_mul_eq_one] at this
  have hG := SymplecticCoverFour.eq_one_of_add_of_mul_invariant (ψ := fun s => ⁅ℓ s, m⁆)
    (fun s s' => by
      rw [commutatorElement_eq_of_map_eq_left hC (heq (hℓ (s + s'))
        (((hℓ s).mul (hℓ s')).congr (hφ s s').symm)),
        commutatorElement_mul_preV hC (hℓ s).mem (hℓ s').mem hm])
    hζ (fun s => by
      have hc := commutatorElement_mem_center hC (hℓ s).mem hm
      change ⁅ℓ (ζ * s), m⁆ = ⁅ℓ s, m⁆
      have hx : g * ℓ s * g⁻¹ ∈ preV θ := (hgφ s _ (hℓ s)).mem
      rw [← conj_central hc g, conjugate_commutatorElement,
        show g * m * g⁻¹ = m * (m⁻¹ * (g * m * g⁻¹)) by group,
        commutatorElement_mul_preV_right hθ hC hx hgm,
        commutatorElement_eq_of_map_eq_left hC (heq (hgφ s _ (hℓ s)) (hℓ (ζ * s)))]) s
  rw [commutatorElement_eq_of_map_eq_left hC (heq ht (hℓ s))]
  exact hG

omit [CharP K 2] in
theorem IsV.map_eq {B : Matrix (Fin r) (Fin r) K} {u u' : E} (hu : IsV θ B u)
    (hu' : IsV θ B u') : θ u = θ u' := by
  have := hu.map_inv_mul_eq_one hu'
  rwa [map_mul, map_inv, inv_mul_eq_one] at this

omit [CharP K 2] in
theorem smul_single' (c : K) (k : Fin r) (s : K) :
    c • (Pi.single k s : Fin r → K) = Pi.single k (c * s) := by
  ext l
  by_cases hl : l = k
  · subst hl
    simp
  · simp [hl]

omit [CharP K 2] in
theorem IsN.conj_torus {k : Fin r} {s : K} {m g : E} (hm : IsN θ (Pi.single k s) m)
    (d : Fin r → Kˣ) (hg : θ g = hypProj h r 1 (lHom h r (hTorusGL d))) :
    IsN θ (Pi.single k ((∏ i, (d i : K))⁻¹ * d k * s)) (g * m * g⁻¹) := by
  refine (hm.conj _ hg).congr ?_
  rw [dval_eq_det, hTorusGL_det, hTorusGL_coe, diagonal_mulVec_single, smul_single', mul_assoc]

omit [CharP K 2] in
theorem IsV.conj_torus {B : Matrix (Fin r) (Fin r) K} {t g : E} (ht : IsV θ B t)
    (d : Fin r → Kˣ) (hg : θ g = hypProj h r 1 (lHom h r (hTorusGL d))) :
    IsV θ (diagonal (fun i => (d i : K)) * B * hconj (diagonal fun i => (d i : K)))
      (g * t * g⁻¹) := by
  refine (ht.conj _ hg).congr ?_
  rw [map_bar_transpose, hTorusGL_coe]

omit [CharP K 2] in
theorem prod_mulSingle_mul (a b : Fin r) (c c' : Kˣ) :
    ∏ i, (((Pi.mulSingle a c * Pi.mulSingle b c' : Fin r → Kˣ) i : Kˣ) : K) = c * c' := by
  rw [← Units.coe_prod]
  simp only [Pi.mul_apply, Finset.prod_mul_distrib, Finset.prod_pi_mulSingle',
    Finset.mem_univ, ite_true, Units.val_mul]

omit [CharP K 2] in
theorem mulSingle_mul_apply (a b k : Fin r) (c c' : Kˣ) :
    (((Pi.mulSingle a c * Pi.mulSingle b c' : Fin r → Kˣ) k : Kˣ) : K) =
      (if k = a then (c : K) else 1) * (if k = b then (c' : K) else 1) := by
  rw [Pi.mul_apply, Units.val_mul, Pi.mulSingle_apply, Pi.mulSingle_apply]
  split_ifs <;> simp

omit [CharP K 2] in
theorem exists_unit_ne_one (hK : Nat.card K = 4) :
    ∃ w : Kˣ, (w : K) ≠ 1 ∧ (w : K) ^ 2 ≠ 1 ∧ (w : K) ^ 3 = 1 := by
  obtain ⟨ω, hω0, hω1⟩ := four_exists_omega hK
  refine ⟨Units.mk0 ω hω0, hω1, fun h2 => hω1 ?_, four_pow_three hK hω0⟩
  have h3 := four_pow_three hK hω0
  rw [Units.val_mk0] at h2
  calc ω = ω ^ 3 / ω ^ 2 := by field_simp
    _ = 1 := by rw [h3, h2, div_one]

include hθ hC in
theorem commutatorElement_eq_one_of_isV_hermD (hr : 2 ≤ r) {i : Fin r} {t : E}
    (ht : IsV θ (hermD i) t) {k : Fin r} {s : K} {m : E} (hm : IsN θ (Pi.single k s) m) :
    ⁅t, m⁆ = 1 := by
  have hK := card_eq_four h
  obtain ⟨w, hw1, -, -⟩ := exists_unit_ne_one hK
  have : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr hr
  obtain ⟨j, hjk⟩ := exists_ne k
  set d : Fin r → Kˣ := Pi.mulSingle j w * Pi.mulSingle j 1 with hd
  obtain ⟨g, hg⟩ := hθ (hypProj h r 1 (lHom h r (hTorusGL d)))
  refine commutatorElement_eq_one_of_weight_N hθ hC ht.mem
    (ψ := fun s : K => (Pi.single k s : Fin r → K)) (fun s s' => by rw [Pi.single_add])
    (g := g) (ζ := (w : K)⁻¹) (inv_ne_one.mpr hw1) ?_ ?_ hm
  · refine (IsV.map_eq ((ht.conj_torus d hg).congr ?_) ht)
    exact diagonal_congr_hermD _ i (four_pow_three hK (d i).ne_zero)
  · intro s m hm
    refine (hm.conj_torus d hg).congr ?_
    rw [hd, prod_mulSingle_mul, mulSingle_mul_apply, ite_eq_right hjk.symm, ite_eq_right hjk.symm,
      Units.val_one, mul_one, mul_one, mul_one]

include hθ hC in
theorem commutatorElement_eq_one_of_isV_hermO {i j : Fin r} (hij : i ≠ j) {u : K} {t : E}
    (ht : IsV θ (hermO i j u) t) {k : Fin r} {s : K} {m : E} (hm : IsN θ (Pi.single k s) m) :
    ⁅t, m⁆ = 1 := by
  have hK := card_eq_four h
  obtain ⟨w, hw1, hw2, hw3⟩ := exists_unit_ne_one hK
  obtain ⟨c, c', hk, hζ⟩ : ∃ c c' : Kˣ, ((c : K) * c')⁻¹ *
      ((if k = i then (c : K) else 1) * (if k = j then (c' : K) else 1)) = 1 ∧
      (c : K) * (c' : K) ^ 2 ≠ 1 := by
    by_cases hki : k = i
    · refine ⟨w, 1, ?_, ?_⟩
      · simp only [ite_eq_left hki, Units.val_one, ite_self, mul_one]
        exact inv_mul_cancel₀ w.ne_zero
      · rwa [Units.val_one, one_pow, mul_one]
    by_cases hkj : k = j
    · refine ⟨1, w, ?_, ?_⟩
      · simp only [ite_eq_right hki, ite_eq_left hkj, Units.val_one, one_mul]
        exact inv_mul_cancel₀ w.ne_zero
      · rw [Units.val_one, one_mul]
        exact hw2
    · refine ⟨w, w ^ 2, ?_, ?_⟩
      · rw [ite_eq_right hki, ite_eq_right hkj, mul_one, mul_one, Units.val_pow_eq_pow_val,
          ← pow_succ', hw3, inv_one]
      · rw [Units.val_pow_eq_pow_val, ← pow_mul, ← pow_succ', show (2 * 2 + 1 : ℕ) = 3 + 2 by
          norm_num, pow_add, hw3, one_mul]
        exact hw2
  set d : Fin r → Kˣ := Pi.mulSingle i c * Pi.mulSingle j c' with hd
  obtain ⟨g, hg⟩ := hθ (hypProj h r 1 (lHom h r (hTorusGL d)))
  refine commutatorElement_eq_one_of_weight_V hθ hC hm.mem (φ := hermO i j) (hermO_add i j)
    (fun s => isRad_zero_iff.mpr (hconj_hermO hK i j s)) (g := g) (ζ := (c : K) * (c' : K) ^ 2)
    hζ ?_ ?_ ht
  · refine hm.inv_mul_mem ((hm.conj_torus d hg).congr ?_)
    rw [hd, prod_mulSingle_mul, mulSingle_mul_apply, hk, one_mul]
  · intro s t ht
    refine (ht.conj_torus d hg).congr ?_
    rw [diagonal_congr_hermO hK, hd, mulSingle_mul_apply, mulSingle_mul_apply, ite_eq_left rfl,
      ite_eq_right hij, ite_eq_right (Ne.symm hij), ite_eq_left rfl, mul_one, one_mul]

include hθ hC in
theorem commutatorElement_eq_one_of_single {t : E} (ht : t ∈ preV θ)
    (hgen : ∀ (k : Fin r) (s : K) (m : E), IsN θ (Pi.single k s) m → ⁅t, m⁆ = 1) {m : E}
    (hm : m ∈ preN θ) : ⁅t, m⁆ = 1 := by
  let S : AddSubgroup (Fin r → K) :=
    { carrier := {x | ∀ m, IsN θ x m → ⁅t, m⁆ = 1}
      zero_mem' := fun m hm => commutatorElement_eq_one_iff_mul_comm.mpr
        (mul_comm_of_mem_preV hθ hC ht (isN_zero_iff.mp hm))
      add_mem' := by
        intro x y hx hy m hm
        obtain ⟨m₁, hm₁⟩ := exists_isN hθ x
        have hm₂ : IsN θ y (m₁⁻¹ * m) := (hm₁.inv.mul hm).congr (by abel)
        rw [show m = m₁ * (m₁⁻¹ * m) by group, commutatorElement_preV_mul hC ht hm₂.mem,
          hx m₁ hm₁, hy _ hm₂, one_mul]
      neg_mem' := by
        intro x hx m hm
        have hm' : IsN θ x m⁻¹ := hm.inv.congr (neg_neg x)
        have h1 := commutatorElement_preV_mul hC ht (m := m) hm'.mem
        rw [mul_inv_cancel, commutatorElement_one_right, hx _ hm', mul_one] at h1
        exact h1.symm }
  obtain ⟨x, hx⟩ := mem_preN.mp hm
  have hxS : x ∈ S := by
    rw [← Finset.univ_sum_single x]
    exact AddSubgroup.sum_mem _ fun k _ => hgen k (x k)
  exact hxS m hx

include hθ hC in
theorem commutatorElement_eq_one_of_herm {m : E} (hm : m ∈ preN θ)
    (hD : ∀ (k : Fin r) (t : E), IsV θ (hermD k) t → ⁅t, m⁆ = 1)
    (hO : ∀ (i j : Fin r), i < j → ∀ (u : K) (t : E), IsV θ (hermO i j u) t → ⁅t, m⁆ = 1)
    {t : E} (ht : t ∈ preV θ) : ⁅t, m⁆ = 1 := by
  have hK := card_eq_four h
  let S : AddSubgroup (Matrix (Fin r) (Fin r) K) :=
    { carrier := {B | IsRad h 0 B ∧ ∀ t, IsV θ B t → ⁅t, m⁆ = 1}
      zero_mem' := ⟨isRad_zero h, fun t ht => commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_center_iff.mp (hC (isV_zero_iff.mp ht)) m).symm⟩
      add_mem' := by
        rintro B B' ⟨hB, h1⟩ ⟨hB', h2⟩
        refine ⟨isRad_zero_add hB hB', fun t ht => ?_⟩
        obtain ⟨t₁, ht₁⟩ := exists_isV hθ hB
        have ht₂ : IsV θ B' (t₁⁻¹ * t) := (ht₁.inv.mul ht).congr (by abel)
        rw [show t = t₁ * (t₁⁻¹ * t) by group, commutatorElement_mul_preV hC ht₁.mem ht₂.mem hm,
          h1 _ ht₁, h2 _ ht₂, one_mul]
      neg_mem' := by
        rintro B ⟨hB, h1⟩
        refine ⟨isRad_zero_neg hB, fun t ht => ?_⟩
        have ht' : IsV θ B t⁻¹ := ht.inv.congr (neg_neg B)
        have h2 := commutatorElement_mul_preV hC ht.mem ht'.mem hm
        rw [mul_inv_cancel, commutatorElement_one_left, h1 _ ht', mul_one] at h2
        exact h2.symm }
  obtain ⟨B, hB⟩ := mem_preV.mp ht
  have hBS : B ∈ S :=
    herm_mem (S := S) (fun k => ⟨isRad_zero_iff.mpr (hconj_hermD k), hD k⟩)
      (fun i j hij u => ⟨isRad_zero_iff.mpr (hconj_hermO hK i j u), hO i j hij u⟩)
      (isRad_zero_iff.mp hB.1)
  exact hBS.2 t hB

include hθ hC in
theorem mul_comm_of_mem_preV_of_mem_preN (hr : 2 ≤ r) {t m : E} (ht : t ∈ preV θ)
    (hm : m ∈ preN θ) : t * m = m * t := by
  refine commutatorElement_eq_one_iff_mul_comm.mp
    (commutatorElement_eq_one_of_herm hθ hC hm (fun k t' ht' => ?_) (fun i j hij u t' ht' => ?_) ht)
  · exact commutatorElement_eq_one_of_single hθ hC ht'.mem
      (fun _ _ _ hm' => commutatorElement_eq_one_of_isV_hermD hθ hC hr ht' hm') hm
  · exact commutatorElement_eq_one_of_single hθ hC ht'.mem
      (fun _ _ _ hm' => commutatorElement_eq_one_of_isV_hermO hθ hC hij.ne ht' hm') hm

end FieldTwo

end CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCover
