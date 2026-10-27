module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverRadical
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCoverLargePairing

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCover

open Matrix CFSG.ClassicalGroups.UnitaryFlag MatrixExtension
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] [CharP K 2] {h : UnitaryFieldData 2 f K} {r : ℕ}
  {E : Type*} [Group E] {θ : E →* hypPSU h r 1}

omit [CharP K 2] in
theorem isRad_zero_iff_isHerm {B : Matrix (Fin r) (Fin r) K} :
    IsRad h 0 B ↔ UnitaryEvenCover.IsHerm h B := by
  rw [IsRad, UnitaryEvenCover.IsHerm, zero_vecMulVec, neg_zero]

omit [CharP K 2] in
theorem isRad_zero_add_even {B B' : Matrix (Fin r) (Fin r) K} (hB : IsRad h 0 B)
    (hB' : IsRad h 0 B') : IsRad h 0 (B + B') :=
  isRad_zero_iff_isHerm.mpr (UnitaryEvenCover.isHerm_add (isRad_zero_iff_isHerm.mp hB)
    (isRad_zero_iff_isHerm.mp hB'))

omit [CharP K 2] in
theorem isRad_zero_neg_even {B : Matrix (Fin r) (Fin r) K} (hB : IsRad h 0 B) :
    IsRad h 0 (-B) :=
  isRad_zero_iff_isHerm.mpr (UnitaryEvenCover.isHerm_neg (isRad_zero_iff_isHerm.mp hB))

omit [CharP K 2] in
theorem nElt_comm_mem_commutator (x y : Fin r → K) :
    nElt (isRad_comm h x y) ∈ ⁅radN h r, radN h r⁆ := by
  obtain ⟨C, hC⟩ := exists_isRad (h := h) x
  obtain ⟨D, hD⟩ := exists_isRad (h := h) y
  have hm := Subgroup.commutator_mem_commutator (nElt_mem_radN hC) (nElt_mem_radN hD)
  rwa [commutatorElement_def, nElt_mul_comm hC hD,
    show ∀ a b c : hypSU h r 1, a * (b * c) * c⁻¹ * b⁻¹ = a from fun a b c => by group] at hm

theorem radV_le_commutator_even : radV h r ≤ ⁅radN h r, radN h r⁆ := by
  rintro _ ⟨B, hB, rfl⟩
  let S : AddSubgroup (Matrix (Fin r) (Fin r) K) :=
    { carrier := {B | ∃ hB : IsRad h 0 B, nElt hB ∈ ⁅radN h r, radN h r⁆}
      zero_mem' := ⟨isRad_zero h, by rw [nElt_zero]; exact one_mem _⟩
      add_mem' := by
        rintro B B' ⟨hB, h1⟩ ⟨hB', h2⟩
        refine ⟨isRad_zero_add_even hB hB', ?_⟩
        have := mul_mem h1 h2
        rwa [nElt_mul, nElt_ext _ (isRad_zero_add_even hB hB') (add_zero 0)
          (by rw [zero_vecMulVec, sub_zero])] at this
      neg_mem' := by
        rintro B ⟨hB, h1⟩
        have hB' : IsRad h 0 (-B) := isRad_zero_neg_even hB
        refine ⟨hB', ?_⟩
        have := inv_mem h1
        rwa [nElt_inv, nElt_ext _ hB' neg_zero (by rw [zero_vecMulVec, sub_zero])] at this }
  have hcomm : ∀ (x y : Fin r → K) (B : Matrix (Fin r) (Fin r) K),
      B = vecMulVec y (fun j => h.bar (x j)) - vecMulVec x (fun j => h.bar (y j)) → B ∈ S := by
    rintro x y B rfl
    exact ⟨isRad_comm h x y, nElt_comm_mem_commutator x y⟩
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hbs : ∀ (k : Fin r) (c : K),
      (fun j => h.bar ((Pi.single k c : Fin r → K) j)) = Pi.single k (h.bar c) := fun k c => by
    funext j
    exact Pi.apply_single (fun _ => h.bar) (fun _ => map_zero _) k c j
  have hmem : B ∈ S := by
    refine UnitaryEvenCover.herm_mem' (S := S) (fun k a ha => ?_) (fun i j _ a => ?_)
      (isRad_zero_iff_isHerm.mp hB)
    · obtain ⟨b, hb⟩ := h.traceLin_surjective ⟨a, ha⟩
      have hba : b + h.bar b = a := by
        have := congrArg Subtype.val hb
        rwa [UnitaryFieldData.coe_traceLin] at this
      refine hcomm (Pi.single k 1) (Pi.single k b) _ ?_
      rw [hbs, hbs, map_one, vecMulVec_single_single', vecMulVec_single_single',
        eq_sub_iff_add_eq, ← single_add]
      congr 1
      linear_combination -hba + h.bar b * h2
    · refine hcomm (Pi.single i a) (Pi.single j 1) _ ?_
      rw [hbs, hbs, map_one, vecMulVec_single_single', vecMulVec_single_single', one_mul,
        mul_one, UnitaryEvenCover.offH, sub_eq_add_neg, single_neg, CharTwo.neg_eq]
      exact add_comm _ _
  obtain ⟨hB', hmem'⟩ := hmem
  exact hmem'

variable (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)

omit [CharP K 2] in
include hC in
theorem mul_comm_commutatorElement_of_mem_preV_even {z m m' : E} (hz : z ∈ preV θ)
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
theorem mul_comm_of_mem_preV_even {t z : E} (ht : t ∈ preV θ) (hz : z ∈ preV θ) :
    t * z = z * t := by
  have hle : ⁅preN θ, preN θ⁆ ≤ Subgroup.centralizer {z} := by
    rw [Subgroup.commutator_le]
    intro m hm m' hm'
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact mul_comm_commutatorElement_of_mem_preV_even hC hz hm hm'
  have hθt : θ t ∈ (⁅preN θ, preN θ⁆).map θ := by
    rw [Subgroup.map_commutator, preN, Subgroup.map_comap_eq_self_of_surjective hθ,
      ← Subgroup.map_commutator]
    obtain ⟨g, hg, hgt⟩ := ht
    exact ⟨g, radV_le_commutator_even hg, hgt⟩
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
theorem commutatorElement_mul_preV_even {t t' m : E} (ht : t ∈ preV θ) (ht' : t' ∈ preV θ)
    (hm : m ∈ preN θ) : ⁅t * t', m⁆ = ⁅t, m⁆ * ⁅t', m⁆ := by
  rw [commutatorElement_mul_left', conj_central (commutatorElement_mem_center hC ht' hm)]
  exact Subgroup.mem_center_iff.mp (commutatorElement_mem_center hC ht hm) _

omit [CharP K 2] in
include hC in
theorem commutatorElement_preV_mul_even {t m m' : E} (ht : t ∈ preV θ) (hm' : m' ∈ preN θ) :
    ⁅t, m * m'⁆ = ⁅t, m⁆ * ⁅t, m'⁆ := by
  rw [commutatorElement_mul_right', conj_central (commutatorElement_mem_center hC ht hm')]

include hθ hC in
theorem commutatorElement_eq_of_isN_even {t m m' : E} {x : Fin r → K} (ht : t ∈ preV θ)
    (hm : IsN θ x m) (hm' : IsN θ x m') : ⁅t, m⁆ = ⁅t, m'⁆ := by
  have hτ := hm.inv_mul_mem hm'
  rw [show m' = m * (m⁻¹ * m') by group, commutatorElement_preV_mul_even hC ht
    (preV_le_preN hτ), commutatorElement_eq_one_iff_mul_comm.mpr
      (mul_comm_of_mem_preV_even hθ hC ht hτ), mul_one]

include hθ hC in
theorem commutatorElement_mul_preV_right_even {t m τ : E} (ht : t ∈ preV θ)
    (hτ : τ ∈ preV θ) : ⁅t, m * τ⁆ = ⁅t, m⁆ := by
  rw [commutatorElement_preV_mul_even hC ht (preV_le_preN hτ),
    commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm_of_mem_preV_even hθ hC ht hτ), mul_one]

omit [CharP K 2] in
theorem IsV.map_eq_even {B : Matrix (Fin r) (Fin r) K} {u u' : E} (hu : IsV θ B u)
    (hu' : IsV θ B u') : θ u = θ u' := by
  have := hu.map_inv_mul_eq_one hu'
  rwa [map_mul, map_inv, inv_mul_eq_one] at this

include hθ hC in
theorem commutatorElement_eq_one_of_weight_N_even {L : Type*} [Field L] {t : E}
    (ht : t ∈ preV θ) {ψ : L → Fin r → K} (hψ : ∀ s s', ψ (s + s') = ψ s + ψ s') {g : E}
    {ζ : L} (hζ : ζ ≠ 1) (hgt : θ (g * t * g⁻¹) = θ t)
    (hgψ : ∀ s m, IsN θ (ψ s) m → IsN θ (ψ (ζ * s)) (g * m * g⁻¹)) {s : L} {m : E}
    (hm : IsN θ (ψ s) m) : ⁅t, m⁆ = 1 := by
  choose ℓ hℓ using fun s => exists_isN hθ (ψ s)
  have hF := SymplecticCoverFour.eq_one_of_add_of_mul_invariant (ψ := fun s => ⁅t, ℓ s⁆)
    (fun s s' => by
      rw [commutatorElement_eq_of_isN_even hθ hC ht (hℓ (s + s'))
        (((hℓ s).mul (hℓ s')).congr (hψ s s').symm),
        commutatorElement_preV_mul_even hC ht (hℓ s').mem])
    hζ (fun s => by
      have hc := commutatorElement_mem_center hC ht (hℓ s).mem
      change ⁅t, ℓ (ζ * s)⁆ = ⁅t, ℓ s⁆
      rw [← conj_central hc g, conjugate_commutatorElement,
        commutatorElement_eq_of_map_eq_left hC hgt,
        commutatorElement_eq_of_isN_even hθ hC ht (hgψ s _ (hℓ s)) (hℓ (ζ * s))]) s
  rw [commutatorElement_eq_of_isN_even hθ hC ht hm (hℓ s)]
  exact hF

include hθ hC in
theorem commutatorElement_eq_one_of_weight_V_even {L : Type*} [Field L] {m : E}
    (hm : m ∈ preN θ) {φ : L → Matrix (Fin r) (Fin r) K} (hφ : ∀ s s', φ (s + s') = φ s + φ s')
    (hφV : ∀ s, IsRad h 0 (φ s)) {g : E} {ζ : L} (hζ : ζ ≠ 1)
    (hgm : m⁻¹ * (g * m * g⁻¹) ∈ preV θ)
    (hgφ : ∀ s t, IsV θ (φ s) t → IsV θ (φ (ζ * s)) (g * t * g⁻¹)) {s : L} {t : E}
    (ht : IsV θ (φ s) t) : ⁅t, m⁆ = 1 := by
  choose ℓ hℓ using fun s => exists_isV hθ (hφV s)
  have hG := SymplecticCoverFour.eq_one_of_add_of_mul_invariant (ψ := fun s => ⁅ℓ s, m⁆)
    (fun s s' => by
      rw [commutatorElement_eq_of_map_eq_left hC (IsV.map_eq_even (hℓ (s + s'))
        (((hℓ s).mul (hℓ s')).congr (hφ s s').symm)),
        commutatorElement_mul_preV_even hC (hℓ s).mem (hℓ s').mem hm])
    hζ (fun s => by
      have hc := commutatorElement_mem_center hC (hℓ s).mem hm
      change ⁅ℓ (ζ * s), m⁆ = ⁅ℓ s, m⁆
      have hx : g * ℓ s * g⁻¹ ∈ preV θ := (hgφ s _ (hℓ s)).mem
      rw [← conj_central hc g, conjugate_commutatorElement,
        show g * m * g⁻¹ = m * (m⁻¹ * (g * m * g⁻¹)) by group,
        commutatorElement_mul_preV_right_even hθ hC hx hgm,
        commutatorElement_eq_of_map_eq_left hC
          (IsV.map_eq_even (hgφ s _ (hℓ s)) (hℓ (ζ * s)))]) s
  rw [commutatorElement_eq_of_map_eq_left hC (IsV.map_eq_even ht (hℓ s))]
  exact hG

include hθ hC in
theorem commutatorElement_eq_one_of_single_even {t : E} (ht : t ∈ preV θ)
    (hgen : ∀ (k : Fin r) (s : K) (m : E), IsN θ (Pi.single k s) m → ⁅t, m⁆ = 1) {m : E}
    (hm : m ∈ preN θ) : ⁅t, m⁆ = 1 := by
  let S : AddSubgroup (Fin r → K) :=
    { carrier := {x | ∀ m, IsN θ x m → ⁅t, m⁆ = 1}
      zero_mem' := fun m hm => commutatorElement_eq_one_iff_mul_comm.mpr
        (mul_comm_of_mem_preV_even hθ hC ht (isN_zero_iff.mp hm))
      add_mem' := by
        intro x y hx hy m hm
        obtain ⟨m₁, hm₁⟩ := exists_isN hθ x
        have hm₂ : IsN θ y (m₁⁻¹ * m) := (hm₁.inv.mul hm).congr (by abel)
        rw [show m = m₁ * (m₁⁻¹ * m) by group, commutatorElement_preV_mul_even hC ht hm₂.mem,
          hx m₁ hm₁, hy _ hm₂, one_mul]
      neg_mem' := by
        intro x hx m hm
        have hm' : IsN θ x m⁻¹ := hm.inv.congr (neg_neg x)
        have h1 := commutatorElement_preV_mul_even hC ht (m := m) hm'.mem
        rw [mul_inv_cancel, commutatorElement_one_right, hx _ hm', mul_one] at h1
        exact h1.symm }
  obtain ⟨x, hx⟩ := mem_preN.mp hm
  have hxS : x ∈ S := by
    rw [← Finset.univ_sum_single x]
    exact AddSubgroup.sum_mem _ fun k _ => hgen k (x k)
  exact hxS m hx

include hθ hC in
theorem commutatorElement_eq_one_of_herm_even {m : E} (hm : m ∈ preN θ)
    (hD : ∀ (k : Fin r) (a : K), h.bar a = a → ∀ t : E, IsV θ (single k k a) t → ⁅t, m⁆ = 1)
    (hO : ∀ (i j : Fin r), i < j → ∀ (a : K) (t : E),
      IsV θ (UnitaryEvenCover.offH h i j a) t → ⁅t, m⁆ = 1)
    {t : E} (ht : t ∈ preV θ) : ⁅t, m⁆ = 1 := by
  let S : AddSubgroup (Matrix (Fin r) (Fin r) K) :=
    { carrier := {B | IsRad h 0 B ∧ ∀ t, IsV θ B t → ⁅t, m⁆ = 1}
      zero_mem' := ⟨isRad_zero h, fun t ht => commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_center_iff.mp (hC (isV_zero_iff.mp ht)) m).symm⟩
      add_mem' := by
        rintro B B' ⟨hB, h1⟩ ⟨hB', h2⟩
        refine ⟨isRad_zero_add_even hB hB', fun t ht => ?_⟩
        obtain ⟨t₁, ht₁⟩ := exists_isV hθ hB
        have ht₂ : IsV θ B' (t₁⁻¹ * t) := (ht₁.inv.mul ht).congr (by abel)
        rw [show t = t₁ * (t₁⁻¹ * t) by group,
          commutatorElement_mul_preV_even hC ht₁.mem ht₂.mem hm, h1 _ ht₁, h2 _ ht₂, one_mul]
      neg_mem' := by
        rintro B ⟨hB, h1⟩
        refine ⟨isRad_zero_neg_even hB, fun t ht => ?_⟩
        have ht' : IsV θ B t⁻¹ := ht.inv.congr (neg_neg B)
        have h2 := commutatorElement_mul_preV_even hC ht.mem ht'.mem hm
        rw [mul_inv_cancel, commutatorElement_one_left, h1 _ ht', mul_one] at h2
        exact h2.symm }
  obtain ⟨B, hB⟩ := mem_preV.mp ht
  have hBS : B ∈ S := UnitaryEvenCover.herm_mem' (S := S)
    (fun k a ha => ⟨isRad_zero_iff_isHerm.mpr (UnitaryEvenCover.isHerm_single ha), hD k a ha⟩)
    (fun i j hij a => ⟨isRad_zero_iff_isHerm.mpr (UnitaryEvenCover.isHerm_offH i j a),
      hO i j hij a⟩)
    (isRad_zero_iff_isHerm.mp hB.1)
  exact hBS.2 t hB

omit [CharP K 2] in
theorem dval_hTorusGL_of_fixed {d : Fin r → Kˣ} (hd : ∀ k, h.bar (d k : K) = d k) :
    dval h (hTorusGL d : Matrix (Fin r) (Fin r) K) = 1 := by
  rw [dval, hTorusGL_det, map_prod, Finset.prod_congr rfl fun k _ => hd k]
  exact div_self (Finset.prod_ne_zero_iff.mpr fun k _ => (d k).ne_zero)

omit [CharP K 2] in
theorem IsN.conj_hTorusGL {d : Fin r → Kˣ}
    (hdv : dval h (hTorusGL d : Matrix (Fin r) (Fin r) K) = 1) {k : Fin r} {s : K} {m g : E}
    (hm : IsN θ (Pi.single k s) m) (hg : θ g = hypProj h r 1 (lHom h r (hTorusGL d))) :
    IsN θ (Pi.single k ((d k : K) * s)) (g * m * g⁻¹) := by
  refine (hm.conj _ hg).congr ?_
  rw [hdv, inv_one, one_smul, hTorusGL_coe, diagonal_mulVec_single]

omit [CharP K 2] in
theorem IsV.conj_hTorusGL {B : Matrix (Fin r) (Fin r) K} {t g : E} (ht : IsV θ B t)
    (d : Fin r → Kˣ) (hg : θ g = hypProj h r 1 (lHom h r (hTorusGL d))) :
    IsV θ (diagonal (fun i => (d i : K)) * B * ((diagonal fun i => (d i : K)).map h.bar)ᵀ)
      (g * t * g⁻¹) := by
  refine (ht.conj _ hg).congr ?_
  rw [hTorusGL_coe]

omit [CharP K 2] in
theorem diagonal_congr_single' (d : Fin r → K) (k : Fin r) (a : K) :
    diagonal d * single k k a * ((diagonal d).map h.bar)ᵀ = single k k (d k * a * h.bar (d k)) := by
  rw [diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_single', single_mul_diagonal']

omit [CharP K 2] in
theorem exists_norm_one_ne_one : ∃ u : Kˣ, (u : K) ≠ 1 ∧ (u : K) * h.bar u = 1 := by
  obtain ⟨hcard, -⟩ := h.card_ker_normUnits_and_surjective
  have : Nontrivial (Units.map h.normHom).ker := by
    have : Finite (Units.map h.normHom).ker := by
      have := h.finite
      exact Subtype.finite
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    rw [hcard]
    have : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    omega
  obtain ⟨⟨u, hu⟩, hu1⟩ := exists_ne (1 : (Units.map h.normHom).ker)
  refine ⟨u, fun h1 => hu1 (Subtype.ext (Units.ext h1)), ?_⟩
  exact (h.mem_ker_normUnits).mp hu

include hθ hC in
theorem commutatorElement_eq_one_single_of_ne (hf : 2 ≤ f) {i k : Fin r} (hik : i ≠ k) {a : K}
    (ha : h.bar a = a) {t : E} (ht : IsV θ (single i i a) t) {s : K} {m : E}
    (hm : IsN θ (Pi.single k s) m) : ⁅t, m⁆ = 1 := by
  obtain ⟨σ, hσ, hσ1⟩ := UnitaryEvenCover.exists_fixed_unit (h := h) hf
  set d : Fin r → Kˣ := Pi.mulSingle i σ with hd
  have hdF := UnitaryEvenCover.mulSingle_fixed hσ i
  obtain ⟨g, hg⟩ := hθ (hypProj h r 1 (lHom h r (hTorusGL d)))
  have hσ2 : (σ : K) ^ 2 ∈ h.fixedField := by
    rw [UnitaryFieldData.mem_fixedField, map_pow, hσ]
  refine commutatorElement_eq_one_of_weight_V_even hθ hC hm.mem
    (φ := fun v : h.fixedField => single i i (v : K))
    (fun v v' => by rw [Subfield.coe_add, single_add])
    (fun v => isRad_zero_iff_isHerm.mpr (UnitaryEvenCover.isHerm_single v.2)) (g := g)
    (ζ := ⟨(σ : K) ^ 2, hσ2⟩) (fun h1 => UnitaryEvenCover.sq_ne_one_of_ne_one' hσ1
      (congrArg Subtype.val h1)) ?_ ?_ (s := ⟨a, ha⟩) ht
  · refine hm.inv_mul_mem ((hm.conj_hTorusGL (dval_hTorusGL_of_fixed hdF) hg).congr ?_)
    rw [UnitaryEvenCover.mulSingle_val, ite_eq_right hik.symm, one_mul]
  · intro v t' ht'
    refine (ht'.conj_hTorusGL d hg).congr ?_
    rw [UnitaryEvenCover.torusF_congr_single d hdF, hd, UnitaryEvenCover.mulSingle_val,
      ite_eq_left rfl, Subfield.coe_mul]

include hθ hC in
theorem commutatorElement_eq_one_single_self (hr : 2 ≤ r) {i : Fin r} {a : K}
    {t : E} (ht : IsV θ (single i i a) t) {s : K} {m : E} (hm : IsN θ (Pi.single i s) m) :
    ⁅t, m⁆ = 1 := by
  obtain ⟨u, hu1, hun⟩ := exists_norm_one_ne_one (h := h)
  have : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr hr
  obtain ⟨j, hji⟩ := exists_ne i
  set d : Fin r → Kˣ := Pi.mulSingle i u * Pi.mulSingle j u⁻¹ with hd
  have hdi : ((d i : Kˣ) : K) = u := by
    rw [hd, mulSingle_mul_apply, ite_eq_left rfl, ite_eq_right hji.symm, mul_one]
  have hdet : (hTorusGL d : Matrix (Fin r) (Fin r) K).det = 1 := by
    rw [hTorusGL_det, hd, prod_mulSingle_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨g, hg⟩ := hθ (hypProj h r 1 (lHom h r (hTorusGL d)))
  refine commutatorElement_eq_one_of_weight_N_even hθ hC ht.mem
    (ψ := fun s : K => (Pi.single i s : Fin r → K)) (fun s s' => by rw [Pi.single_add])
    (g := g) (ζ := (u : K)) hu1 ?_ ?_ hm
  · refine IsV.map_eq_even ((ht.conj_hTorusGL d hg).congr ?_) ht
    rw [diagonal_congr_single', hdi, mul_comm (u : K) a, mul_assoc, hun, mul_one]
  · intro s m hm
    refine (hm.conj_hTorusGL (dval_of_det_eq_one hdet) hg).congr ?_
    rw [hdi]

include hθ hC in
theorem commutatorElement_eq_one_offH_of_isN (hf : 2 ≤ f) {i j : Fin r} (hij : i ≠ j) {a : K}
    {t : E} (ht : IsV θ (UnitaryEvenCover.offH h i j a) t) {k : Fin r} {s : K} {m : E}
    (hm : IsN θ (Pi.single k s) m) : ⁅t, m⁆ = 1 := by
  obtain ⟨σ, hσ, hσ1⟩ := UnitaryEvenCover.exists_fixed_unit (h := h) hf
  obtain ⟨n, hn, hnk⟩ : ∃ n, (n = i ∨ n = j) ∧ n ≠ k := by
    by_cases hik : i = k
    · exact ⟨j, Or.inr rfl, fun hjk => hij (hik.trans hjk.symm)⟩
    · exact ⟨i, Or.inl rfl, hik⟩
  set d : Fin r → Kˣ := Pi.mulSingle n σ with hd
  have hdF := UnitaryEvenCover.mulSingle_fixed hσ n
  obtain ⟨g, hg⟩ := hθ (hypProj h r 1 (lHom h r (hTorusGL d)))
  have hζ : ((d i : Kˣ) : K) * (d j : K) = σ := by
    rw [hd, UnitaryEvenCover.mulSingle_val, UnitaryEvenCover.mulSingle_val]
    rcases hn with rfl | rfl
    · rw [ite_eq_left rfl, ite_eq_right (Ne.symm hij), mul_one]
    · rw [ite_eq_right hij, ite_eq_left rfl, one_mul]
  refine commutatorElement_eq_one_of_weight_V_even hθ hC hm.mem
    (φ := fun v : K => UnitaryEvenCover.offH h i j v)
    (fun v v' => by simp only [UnitaryEvenCover.offH, map_add, single_add]; abel)
    (fun v => isRad_zero_iff_isHerm.mpr (UnitaryEvenCover.isHerm_offH i j v)) (g := g)
    (ζ := (σ : K)) hσ1 ?_ ?_ ht
  · refine hm.inv_mul_mem ((hm.conj_hTorusGL (dval_hTorusGL_of_fixed hdF) hg).congr ?_)
    rw [UnitaryEvenCover.mulSingle_val, ite_eq_right hnk.symm, one_mul]
  · intro v t' ht'
    refine (ht'.conj_hTorusGL d hg).congr ?_
    rw [UnitaryEvenCover.torusF_congr_offH d hdF, hζ]

include hθ hC in
theorem mul_comm_of_mem_preV_of_mem_preN_even (hf : 2 ≤ f) (hr : 2 ≤ r) {t m : E}
    (ht : t ∈ preV θ) (hm : m ∈ preN θ) : t * m = m * t := by
  refine commutatorElement_eq_one_iff_mul_comm.mp
    (commutatorElement_eq_one_of_herm_even hθ hC hm (fun k a ha t' ht' => ?_)
      (fun i j hij a t' ht' => ?_) ht)
  · refine commutatorElement_eq_one_of_single_even hθ hC ht'.mem (fun l s m' hm' => ?_) hm
    by_cases hkl : k = l
    · subst hkl
      exact commutatorElement_eq_one_single_self hθ hC hr ht' hm'
    · exact commutatorElement_eq_one_single_of_ne hθ hC hf hkl ha ht' hm'
  · exact commutatorElement_eq_one_of_single_even hθ hC ht'.mem
      (fun l s m' hm' => commutatorElement_eq_one_offH_of_isN hθ hC hf hij.ne ht' hm') hm

end CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCover
