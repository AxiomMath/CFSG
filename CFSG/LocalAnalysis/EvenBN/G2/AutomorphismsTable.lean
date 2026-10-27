module

public import CFSG.LocalAnalysis.EvenBN.G2.Automorphisms
public import CFSG.LocalAnalysis.EvenBN.TwoF4.CommutatorMap

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.LocalAnalysis.EvenBN.TwoF4 (sectionCentralizer sectionCentralizer_le_normalizer_left
  sectionCentralizer_le_normalizer_right mem_sectionCentralizer_iff_of_le)
open scoped commutatorElement

namespace Model

section Torus

variable {K : Type} [Field K]

theorem torus_conj_g2N (t₁ t₂ : Kˣ) (A B C D E F : K) :
    torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂ * g2N A B C D E F *
        (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂)⁻¹ =
      g2N (((t₁ ^ (-1 : ℤ) * t₂ ^ (2 : ℤ) : Kˣ) : K) * A)
        (((t₁ ^ (2 : ℤ) * t₂ ^ (-3 : ℤ) : Kˣ) : K) * B)
        (((t₁ ^ (1 : ℤ) * t₂ ^ (-1 : ℤ) : Kˣ) : K) * C)
        (((t₁ ^ (0 : ℤ) * t₂ ^ (1 : ℤ) : Kˣ) : K) * D)
        (((t₁ ^ (-1 : ℤ) * t₂ ^ (3 : ℤ) : Kˣ) : K) * E)
        (((t₁ ^ (1 : ℤ) * t₂ ^ (0 : ℤ) : Kˣ) : K) * F) := by
  have h₁ := torus_conj_of (K := K) (m₁ := -1) (m₂ := 2) isRoot_g2r t₁ t₂ (by decide)
    (by decide)
  have h₂ := torus_conj_of (K := K) (m₁ := 2) (m₂ := -3) isRoot_g2a t₁ t₂ (by decide)
    (by decide)
  have h₃ := torus_conj_of (K := K) (m₁ := 1) (m₂ := -1) isRoot_g2u t₁ t₂ (by decide)
    (by decide)
  have h₄ := torus_conj_of (K := K) (m₁ := 0) (m₂ := 1) isRoot_g2v t₁ t₂ (by decide)
    (by decide)
  have h₅ := torus_conj_of (K := K) (m₁ := -1) (m₂ := 3) isRoot_g2b t₁ t₂ (by decide)
    (by decide)
  have h₆ := torus_conj_of (K := K) (m₁ := 1) (m₂ := 0) isRoot_g2c t₁ t₂ (by decide)
    (by decide)
  generalize torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂ = h at h₁ h₂ h₃ h₄ h₅ h₆ ⊢
  have e : ∀ x y : ModGL .G2 K, h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) :=
    fun x y => by group
  simp only [g2N, e, h₁, h₂, h₃, h₄, h₅, h₆]

end Torus

section ToolsA

variable
  {K : Type} [Field K] [Finite K]

theorem mem_sectionCentralizer_inn_iff {H₁ H₂ : Subgroup (ModGL .G2 K)} (h : H₂ ≤ H₁)
    {α : MulAut (adjointGroup .G2 K)} :
    α ∈ sectionCentralizer (inn H₁) (inn H₂) ↔
      ∀ x : adjointGroup .G2 K, (x : ModGL .G2 K) ∈ H₁ →
        ((x⁻¹ * α x : adjointGroup .G2 K) : ModGL .G2 K) ∈ H₂ := by
  have : Finite (MulAut (adjointGroup .G2 K)) := MulEquiv.finite_left
  have e : ∀ x : adjointGroup .G2 K, (MulAut.conj x)⁻¹ * α⁻¹⁻¹ * MulAut.conj x * α⁻¹ =
      MulAut.conj (x⁻¹ * α x) := fun x => by
    rw [inv_inv, map_mul, map_inv, ← mulAut_mul_conj_mul_inv, mul_assoc, mul_assoc, mul_assoc]
  rw [← inv_mem_iff, mem_sectionCentralizer_iff_of_le (inn_mono h)]
  constructor
  · intro hα x hx
    have := hα _ (conj_mem_inn hx)
    rwa [e, conj_mem_inn_iff] at this
  · intro hα u hu
    obtain ⟨x, hx, rfl⟩ := mem_inn.1 hu
    rw [e, conj_mem_inn_iff]
    exact hα x hx

theorem conj_mem_normalizer_inn_iff {H : Subgroup (ModGL .G2 K)} (hHC : H ≤ adjointGroup .G2 K)
    {g : adjointGroup .G2 K} :
    MulAut.conj g ∈ normalizer (inn H : Set (MulAut (adjointGroup .G2 K))) ↔
      (g : ModGL .G2 K) ∈ normalizer (H : Set (ModGL .G2 K)) := by
  rw [mem_normalizer_inn_iff, mem_normalizer_iff]
  constructor
  · intro h y
    by_cases hy : y ∈ adjointGroup .G2 K
    · have := h ⟨y, hy⟩
      rw [MulAut.conj_apply, coe_mul, coe_mul, coe_inv] at this
      exact this.symm
    · refine ⟨fun h' => absurd (hHC h') hy, fun h' => absurd ?_ hy⟩
      have := mul_mem (mul_mem (inv_mem g.2) (hHC h')) g.2
      rwa [show (g : ModGL .G2 K)⁻¹ * (g * y * (g : ModGL .G2 K)⁻¹) * g = y by group] at this
  · intro h x
    rw [MulAut.conj_apply, coe_mul, coe_mul, coe_inv]
    exact (h x).symm

theorem mem_normalizer_inn_of_mem_sectionCentralizer {H₁ H₂ E : Subgroup (ModGL .G2 K)}
    (h₂ : H₂ ≤ E) (h₁ : E ≤ H₁) {α : MulAut (adjointGroup .G2 K)}
    (hα : α ∈ sectionCentralizer (inn H₁) (inn H₂)) :
    α ∈ normalizer (inn E : Set (MulAut (adjointGroup .G2 K))) := by
  have hα' := (mem_sectionCentralizer_inn_iff (h₂.trans h₁)).1 hα
  have hα'' := (mem_sectionCentralizer_inn_iff (h₂.trans h₁)).1 (inv_mem hα)
  rw [mem_normalizer_inn_iff]
  intro x
  constructor
  · intro hx
    have h1 := h₂ (hα'' (α x) (h₁ hx))
    rw [MulAut.inv_apply_self, coe_mul, coe_inv] at h1
    have := mul_mem hx h1
    rwa [mul_inv_cancel_left] at this
  · intro hx
    have h1 := h₂ (hα' x (h₁ hx))
    rw [coe_mul, coe_inv] at h1
    have := mul_mem hx h1
    rwa [mul_inv_cancel_left] at this

theorem inn_le_sectionCentralizer {H₁ H₂ R : Subgroup (ModGL .G2 K)} (h : H₂ ≤ H₁)
    (hR : ∀ y ∈ H₁, y ∈ adjointGroup .G2 K → ∀ s ∈ R, y⁻¹ * (s * y * s⁻¹) ∈ H₂) :
    inn R ≤ sectionCentralizer (inn H₁) (inn H₂) := by
  intro α hα
  obtain ⟨s, hs, rfl⟩ := mem_inn.1 hα
  rw [mem_sectionCentralizer_inn_iff h]
  intro x hx
  rw [coe_mul, coe_inv, MulAut.conj_apply, coe_mul, coe_mul, coe_inv]
  exact hR _ hx x.2 _ hs

theorem inn_le_sectionCentralizer_of_commutator {H₁ H₂ R : Subgroup (ModGL .G2 K)} (h : H₂ ≤ H₁)
    (hR : ∀ y ∈ H₁, ∀ s ∈ R, ⁅y, s⁆ ∈ H₂) :
    inn R ≤ sectionCentralizer (inn H₁) (inn H₂) :=
  inn_le_sectionCentralizer h fun y hy _ s hs => by
    have := hR _ (inv_mem hy) s hs
    rw [commutatorElement_def, inv_inv] at this
    simpa only [mul_assoc] using this

end ToolsA

section ToolsF

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem coe_conj_borel_apply (k : ℕ) (t₁ t₂ : Kˣ) (A B C D E F : K)
    (hg : torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂ * g2N A B C D E F ∈
      adjointGroup .G2 K) (a b c d e f : K) (hx : g2N a b c d e f ∈ adjointGroup .G2 K) :
    (((MulAut.conj (⟨_, hg⟩ : adjointGroup .G2 K) * fieldAut K ^ k)
      (⟨_, hx⟩ : adjointGroup .G2 K) : adjointGroup .G2 K) : ModGL .G2 K) =
      torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂ *
        (g2N A B C D E F * g2N (a ^ 2 ^ k) (b ^ 2 ^ k) (c ^ 2 ^ k) (d ^ 2 ^ k) (e ^ 2 ^ k)
          (f ^ 2 ^ k) * (g2N A B C D E F)⁻¹) *
        (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂)⁻¹ := by
  rw [coe_conj_mul_fieldAut_pow_apply, units_map_entrywise_g2N]
  simp only [frobeniusEquiv_pow_apply]
  group

theorem coe_conj_mul_fieldAut_pow_pinnedX (g : adjointGroup .G2 K) (k : ℕ)
    (s : Fin Tag.G2.rank → ℤ) (c : K) :
    (((MulAut.conj g * fieldAut K ^ k)
      (⟨pinnedX .G2 K s c, pinnedX_mem_adjointGroup s c⟩ : adjointGroup .G2 K) :
        adjointGroup .G2 K) : ModGL .G2 K) =
      (g : ModGL .G2 K) * pinnedX .G2 K s (c ^ 2 ^ k) * (g : ModGL .G2 K)⁻¹ := by
  rw [MulAut.mul_apply, MulAut.conj_apply, coe_mul, coe_mul, coe_inv, fieldAut_pow_pinnedX]

theorem mem_normalizer_of_conj_mul_fieldAut_pow {H : Subgroup (ModGL .G2 K)}
    (hHC : H ≤ adjointGroup .G2 K)
    (hH : ∀ k : ℕ, H.map (Units.map (entrywiseHom (frobeniusEquiv K 2 ^ k).toRingHom)) = H)
    {g : adjointGroup .G2 K} {k : ℕ}
    (h : MulAut.conj g * fieldAut K ^ k ∈ normalizer (inn H : Set (MulAut (adjointGroup .G2 K)))) :
    (g : ModGL .G2 K) ∈ normalizer (H : Set (ModGL .G2 K)) := by
  rw [← conj_mem_normalizer_inn_iff hHC]
  have := mul_mem h (inv_mem (fieldAut_pow_mem_normalizer_inn hHC hH k))
  rwa [mul_inv_cancel_right] at this

end ToolsF

section RankOne

theorem SL2_eq_one_of_commute {K : Type} [Field K] [CharP K 2] {m : SL2 K}
    (hu : m * uSL 1 = uSL 1 * m) (hv : m * vSL 1 = vSL 1 * m) : m = 1 := by
  have hu' : ((m * uSL 1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) =
      ((uSL 1 * m : SL2 K) : Matrix (Fin 2) (Fin 2) K) := by rw [hu]
  have hv' : ((m * vSL 1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) =
      ((vSL 1 * m : SL2 K) : Matrix (Fin 2) (Fin 2) K) := by rw [hv]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at hu' hv'
  have e1 := congrFun (congrFun hu' 0) 0
  have e2 := congrFun (congrFun hu' 0) 1
  have e3 := congrFun (congrFun hv' 0) 0
  simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two] at e1 e2 e3
  have hdet := m.2
  rw [Matrix.det_fin_two, e1, e3] at hdet
  simp only [mul_zero, sub_zero] at hdet
  rw [e3, add_zero, zero_add] at e2
  rw [← e2] at hdet
  have h00 : (m : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := eq_one_of_mul_self_eq_one_two hdet
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using h00
  · simpa using e3
  · simpa using e1
  · simpa [← e2] using h00

theorem eq_one_of_commute_of_mem_range {K : Type} {G : Type*} [Field K] [CharP K 2] [Group G]
    {ρ : SL2 K →* G} (hρ : Function.Injective ρ) {l : G} (hl : l ∈ ρ.range)
    (hu : l * ρ (uSL 1) = ρ (uSL 1) * l) (hv : l * ρ (vSL 1) = ρ (vSL 1) * l) : l = 1 := by
  obtain ⟨m, rfl⟩ := hl
  rw [← map_mul ρ, ← map_mul ρ] at hu hv
  rw [SL2_eq_one_of_commute (hρ hu) (hρ hv), map_one]

end RankOne

section Sections

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_borel_form {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    {H : Subgroup (ModGL .G2 K)} (hHC : H ≤ adjointGroup .G2 K)
    (hH : ∀ k : ℕ, H.map (Units.map (entrywiseHom (frobeniusEquiv K 2 ^ k).toRingHom)) = H)
    (hNB : adjointGroup .G2 K ⊓ normalizer (H : Set (ModGL .G2 K)) ≤ borelGroup .G2 K)
    {α : MulAut (adjointGroup .G2 K)}
    (hα : α ∈ normalizer (inn H : Set (MulAut (adjointGroup .G2 K)))) :
    ∃ (t₁ t₂ : Kˣ) (A B C D E F : K) (hg : torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂ *
      g2N A B C D E F ∈ adjointGroup .G2 K) (k : ℕ), k < n ∧
        α = MulAut.conj (⟨_, hg⟩ : adjointGroup .G2 K) * fieldAut K ^ k := by
  obtain ⟨⟨g, hgC⟩, k, hk, rfl⟩ := exists_eq_conj_mul_fieldAut_pow hK hn α
  have hgN := mem_normalizer_of_conj_mul_fieldAut_pow hHC hH hα
  obtain ⟨h, hh, u, hu, rfl⟩ := exists_torus_mul_of_mem_borel (hNB ⟨hgC, hgN⟩)
  obtain ⟨t₁, t₂, rfl⟩ := exists_eq_torusElt_mul hh
  obtain ⟨A, B, C, D, E, F, rfl⟩ := mem_S.1 hu
  exact ⟨t₁, t₂, A, B, C, D, E, F, hgC, k, hk, rfl⟩

theorem eq_one_of_forall_mul_pow_eq {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) {k : ℕ}
    (hk : k < n) {χ : K} (h : ∀ c : K, χ * c ^ 2 ^ k = c) : χ = 1 ∧ k = 0 := by
  have h1 : χ = 1 := by simpa using h 1
  refine ⟨h1, eq_zero_of_forall_pow_eq hK hn hk fun c => ?_⟩
  simpa [h1] using h c

theorem exists_borel_form₂ {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    {H₁ H₂ : Subgroup (ModGL .G2 K)} (h₁C : H₁ ≤ adjointGroup .G2 K)
    (h₂C : H₂ ≤ adjointGroup .G2 K)
    (h₁ : ∀ k : ℕ, H₁.map (Units.map (entrywiseHom (frobeniusEquiv K 2 ^ k).toRingHom)) = H₁)
    (h₂ : ∀ k : ℕ, H₂.map (Units.map (entrywiseHom (frobeniusEquiv K 2 ^ k).toRingHom)) = H₂)
    (hNB : adjointGroup .G2 K ⊓ normalizer (H₁ : Set (ModGL .G2 K)) ⊓
      normalizer (H₂ : Set (ModGL .G2 K)) ≤ borelGroup .G2 K)
    {α : MulAut (adjointGroup .G2 K)}
    (hα₁ : α ∈ normalizer (inn H₁ : Set (MulAut (adjointGroup .G2 K))))
    (hα₂ : α ∈ normalizer (inn H₂ : Set (MulAut (adjointGroup .G2 K)))) :
    ∃ (t₁ t₂ : Kˣ) (A B C D E F : K) (hg : torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂ *
      g2N A B C D E F ∈ adjointGroup .G2 K) (k : ℕ), k < n ∧
        α = MulAut.conj (⟨_, hg⟩ : adjointGroup .G2 K) * fieldAut K ^ k := by
  obtain ⟨⟨g, hgC⟩, k, hk, rfl⟩ := exists_eq_conj_mul_fieldAut_pow hK hn α
  have hg₁ := mem_normalizer_of_conj_mul_fieldAut_pow h₁C h₁ hα₁
  have hg₂ := mem_normalizer_of_conj_mul_fieldAut_pow h₂C h₂ hα₂
  obtain ⟨h, hh, u, hu, rfl⟩ := exists_torus_mul_of_mem_borel (hNB ⟨⟨hgC, hg₁⟩, hg₂⟩)
  obtain ⟨t₁, t₂, rfl⟩ := exists_eq_torusElt_mul hh
  obtain ⟨A, B, C, D, E, F, rfl⟩ := mem_S.1 hu
  exact ⟨t₁, t₂, A, B, C, D, E, F, hgC, k, hk, rfl⟩

omit
  [Finite K] [CharP K 2] in
theorem torus_char_of_mem_torusFix {s : Fin Tag.G2.rank → ℤ} (hs : IsRoot .G2 s)
    {m₁ m₂ : ℤ} (h₁ : ∑ j, Tag.G2.cartan g2ia j * s j = m₁)
    (h₂ : ∑ j, Tag.G2.cartan g2ir j * s j = m₂) {h : ModGL .G2 K} (hh : h ∈ torusFix K s) :
    ∃ t₁ t₂ : Kˣ, h = torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂ ∧
      t₁ ^ m₁ * t₂ ^ m₂ = 1 := by
  obtain ⟨t₁, t₂, rfl⟩ := exists_eq_torusElt_mul hh.1
  exact ⟨t₁, t₂, rfl, torus_char_eq_one hs t₁ t₂ h₁ h₂
    (mem_centralizer_iff.1 hh.2 _ (mem_rootSubgroup.2 ⟨1, rfl⟩))⟩

theorem sectionCentralizer_S_F_le {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    sectionCentralizer (inn (S K)) (inn (Model.F K)) ≤ inn (S K) := by
  intro α hα
  obtain ⟨t₁, t₂, A, B, C, D, E, F, hg, k, hk, rfl⟩ := exists_borel_form hK hn
    (S_le_adjointGroup K) (fun k => map_entrywise_S _) (adjointGroup_inf_normalizer_S.1.le)
    (sectionCentralizer_le_normalizer_left _ _ hα)
  rw [mem_sectionCentralizer_inn_iff F_le_S] at hα
  have h0 : (0 : K) ^ 2 ^ k = 0 := zero_pow (pow_ne_zero k two_ne_zero)
  obtain ⟨hχr, rfl⟩ := eq_one_of_forall_mul_pow_eq hK hn hk fun c => by
    have hx : g2N c (0 : K) 0 0 0 0 ∈ adjointGroup .G2 K :=
      S_le_adjointGroup K (g2N_mem_posUnipotent _ _ _ _ _ _)
    have := hα ⟨_, hx⟩ (g2N_mem_posUnipotent _ _ _ _ _ _)
    rw [coe_mul, coe_inv, coe_conj_borel_apply, g2N_conj_coords, torus_conj_g2N, g2N_inv_coords,
      g2N_mul_coords, g2N_mem_F_iff] at this
    exact (CharTwo.add_eq_zero.1 this.1).symm
  obtain ⟨hχa, -⟩ := eq_one_of_forall_mul_pow_eq hK hn hk fun c => by
    have hx : g2N (0 : K) c 0 0 0 0 ∈ adjointGroup .G2 K :=
      S_le_adjointGroup K (g2N_mem_posUnipotent _ _ _ _ _ _)
    have := hα ⟨_, hx⟩ (g2N_mem_posUnipotent _ _ _ _ _ _)
    rw [coe_mul, coe_inv, coe_conj_borel_apply, g2N_conj_coords, torus_conj_g2N, g2N_inv_coords,
      g2N_mul_coords, g2N_mem_F_iff] at this
    exact (CharTwo.add_eq_zero.1 this.2).symm
  have hr : t₁ ^ (-1 : ℤ) * t₂ ^ (2 : ℤ) = 1 := Units.ext (by rw [Units.val_one]; exact hχr)
  have ha : t₁ ^ (2 : ℤ) * t₂ ^ (-3 : ℤ) = 1 := Units.ext (by rw [Units.val_one]; exact hχa)
  rw [zpow_neg_one, inv_mul_eq_one] at hr
  subst hr
  rw [← zpow_mul, ← zpow_add] at ha
  norm_num at ha
  subst ha
  rw [pow_zero, mul_one]
  refine conj_mem_inn ?_
  simp only [one_zpow, torusElt_one, one_mul]
  exact g2N_mem_posUnipotent _ _ _ _ _ _

theorem yamada_3_23_S_F {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    sectionCentralizer (inn (S K)) (inn (Model.F K)) = inn (S K) := by
  refine le_antisymm (sectionCentralizer_S_F_le hK hn)
    (inn_le_sectionCentralizer_of_commutator F_le_S fun y hy s hs => ?_)
  obtain ⟨a, b, c, d, e, f, rfl⟩ := mem_S.1 hy
  obtain ⟨A, B, C, D, E, F, rfl⟩ := mem_S.1 hs
  rw [g2N_commutator_coords, g2N_mem_F_iff]
  exact ⟨rfl, rfl⟩

theorem sectionCentralizer_D_U_le {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    sectionCentralizer (inn (Model.D K)) (inn (U K)) ≤ inn (Model.D K) := by
  intro α hα
  obtain ⟨t₁, t₂, A, B, C, D, E, F, hg, k, hk, rfl⟩ := exists_borel_form hK hn
    X_le_adjointGroup (fun k => map_entrywise_X _) adjointGroup_inf_normalizer_X.le
    (mem_normalizer_inn_of_mem_sectionCentralizer (U_le_Y.trans Y_le_X) (X_le_F.trans F_le_D) hα)
  rw [mem_sectionCentralizer_inn_iff U_le_D] at hα
  have h0 : (0 : K) ^ 2 ^ k = 0 := zero_pow (pow_ne_zero k two_ne_zero)
  obtain ⟨hχa, rfl⟩ := eq_one_of_forall_mul_pow_eq hK hn hk fun c => by
    have hx : g2N (0 : K) c 0 0 0 0 ∈ adjointGroup .G2 K := D_le_adjointGroup (g2N_mem_D_iff.2 rfl)
    have := hα ⟨_, hx⟩ (g2N_mem_D_iff.2 rfl)
    rw [coe_mul, coe_inv, coe_conj_borel_apply, g2N_conj_coords, torus_conj_g2N, g2N_inv_coords,
      g2N_mul_coords, g2N_mem_U_iff] at this
    exact (CharTwo.add_eq_zero.1 this.2.1).symm
  have hx1 : g2N (0 : K) 1 0 0 0 0 ∈ adjointGroup .G2 K := D_le_adjointGroup (g2N_mem_D_iff.2 rfl)
  have hA : A = 0 := by
    have := hα ⟨_, hx1⟩ (g2N_mem_D_iff.2 rfl)
    rw [coe_mul, coe_inv, coe_conj_borel_apply, g2N_conj_coords, torus_conj_g2N, g2N_inv_coords,
      g2N_mul_coords, g2N_mem_U_iff] at this
    have h3 := this.2.2.1
    simp only [pow_zero, pow_one,
      mul_zero, mul_one, add_zero, zero_add] at h3
    exact (mul_eq_zero.1 h3).resolve_left (Units.ne_zero _)
  subst hA
  have hχu : ((t₁ ^ (1 : ℤ) * t₂ ^ (-1 : ℤ) : Kˣ) : K) = 1 := by
    have hx : g2N (0 : K) 0 1 0 0 0 ∈ adjointGroup .G2 K := D_le_adjointGroup (g2N_mem_D_iff.2 rfl)
    have := hα ⟨_, hx⟩ (g2N_mem_D_iff.2 rfl)
    rw [coe_mul, coe_inv, coe_conj_borel_apply, g2N_conj_coords, torus_conj_g2N, g2N_inv_coords,
      g2N_mul_coords, g2N_mem_U_iff] at this
    have h3 := this.2.2.1
    simp only [pow_zero, pow_one,
      mul_zero, mul_one, add_zero, zero_add] at h3
    exact (CharTwo.add_eq_zero.1 h3).symm
  have hu : t₁ ^ (1 : ℤ) * t₂ ^ (-1 : ℤ) = 1 := Units.ext (by rw [Units.val_one]; exact hχu)
  have ha : t₁ ^ (2 : ℤ) * t₂ ^ (-3 : ℤ) = 1 := Units.ext (by rw [Units.val_one]; exact hχa)
  rw [zpow_one, zpow_neg_one, mul_inv_eq_one] at hu
  subst hu
  rw [← zpow_add] at ha
  norm_num at ha
  subst ha
  rw [pow_zero, mul_one]
  refine conj_mem_inn ?_
  simp only [torusElt_one, one_mul]
  exact g2N_mem_D_iff.2 rfl

theorem yamada_3_23_D_U {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    sectionCentralizer (inn (Model.D K)) (inn (U K)) = inn (Model.D K) := by
  refine le_antisymm (sectionCentralizer_D_U_le hK hn)
    (inn_le_sectionCentralizer_of_commutator U_le_D fun y hy s hs => ?_)
  obtain ⟨b, c, d, e, f, rfl⟩ := mem_D.1 hy
  obtain ⟨B, C, D, E, F, rfl⟩ := mem_D.1 hs
  rw [g2N_commutator_coords, g2N_mem_U_iff]
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩ <;> ring

theorem sectionCentralizer_M_W_le {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    sectionCentralizer (inn (M K)) (inn (W K)) ≤ inn (M K) := by
  intro α hα
  obtain ⟨t₁, t₂, A, B, C, D, E, F, hg, k, hk, rfl⟩ := exists_borel_form hK hn
    F_le_adjointGroup (fun k => map_entrywise_F _) adjointGroup_inf_normalizer_F.le
    (mem_normalizer_inn_of_mem_sectionCentralizer W_le_F F_le_M hα)
  rw [mem_sectionCentralizer_inn_iff (W_le_F.trans F_le_M)] at hα
  have h0 : (0 : K) ^ 2 ^ k = 0 := zero_pow (pow_ne_zero k two_ne_zero)
  obtain ⟨hχr, rfl⟩ := eq_one_of_forall_mul_pow_eq hK hn hk fun c => by
    have hx : g2N c (0 : K) 0 0 0 0 ∈ adjointGroup .G2 K := M_le_adjointGroup (g2N_mem_M_iff.2 rfl)
    have := hα ⟨_, hx⟩ (g2N_mem_M_iff.2 rfl)
    rw [coe_mul, coe_inv, coe_conj_borel_apply, g2N_conj_coords, torus_conj_g2N, g2N_inv_coords,
      g2N_mul_coords, g2N_mem_W_iff] at this
    exact (CharTwo.add_eq_zero.1 this.1).symm
  have hx1 : g2N (1 : K) 0 0 0 0 0 ∈ adjointGroup .G2 K := M_le_adjointGroup (g2N_mem_M_iff.2 rfl)
  have hB : B = 0 := by
    have := hα ⟨_, hx1⟩ (g2N_mem_M_iff.2 rfl)
    rw [coe_mul, coe_inv, coe_conj_borel_apply, g2N_conj_coords, torus_conj_g2N, g2N_inv_coords,
      g2N_mul_coords, g2N_mem_W_iff] at this
    have h3 := this.2.2
    simp only [pow_zero, pow_one,
      mul_zero, zero_mul, mul_one, add_zero, zero_add] at h3
    exact (mul_eq_zero.1 h3).resolve_left (Units.ne_zero _)
  subst hB
  have hχu : ((t₁ ^ (1 : ℤ) * t₂ ^ (-1 : ℤ) : Kˣ) : K) = 1 := by
    have hx : g2N (0 : K) 0 1 0 0 0 ∈ adjointGroup .G2 K := M_le_adjointGroup (g2N_mem_M_iff.2 rfl)
    have := hα ⟨_, hx⟩ (g2N_mem_M_iff.2 rfl)
    rw [coe_mul, coe_inv, coe_conj_borel_apply, g2N_conj_coords, torus_conj_g2N, g2N_inv_coords,
      g2N_mul_coords, g2N_mem_W_iff] at this
    have h3 := this.2.2
    simp only [pow_zero, pow_one,
      mul_zero, mul_one, add_zero, zero_add] at h3
    exact (CharTwo.add_eq_zero.1 h3).symm
  have hu : t₁ ^ (1 : ℤ) * t₂ ^ (-1 : ℤ) = 1 := Units.ext (by rw [Units.val_one]; exact hχu)
  have hr : t₁ ^ (-1 : ℤ) * t₂ ^ (2 : ℤ) = 1 := Units.ext (by rw [Units.val_one]; exact hχr)
  rw [zpow_one, zpow_neg_one, mul_inv_eq_one] at hu
  subst hu
  rw [← zpow_add] at hr
  norm_num at hr
  subst hr
  rw [pow_zero, mul_one]
  refine conj_mem_inn ?_
  simp only [torusElt_one, one_mul]
  exact g2N_mem_M_iff.2 rfl

theorem yamada_3_23_M_W {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    sectionCentralizer (inn (M K)) (inn (W K)) = inn (M K) := by
  refine le_antisymm (sectionCentralizer_M_W_le hK hn)
    (inn_le_sectionCentralizer_of_commutator (W_le_F.trans F_le_M) fun y hy s hs => ?_)
  obtain ⟨a, c, d, e, f, rfl⟩ := mem_M.1 hy
  obtain ⟨A, C, D, E, F, rfl⟩ := mem_M.1 hs
  rw [g2N_commutator_coords, g2N_mem_W_iff]
  refine ⟨rfl, rfl, ?_⟩
  ring

omit [Finite K] in
theorem adjointGroup_inf_normalizer_U_inf_normalizer_Y :
    adjointGroup .G2 K ⊓ normalizer (U K : Set (ModGL .G2 K)) ⊓
      normalizer (Y K : Set (ModGL .G2 K)) ≤ borelGroup .G2 K := by
  rintro g ⟨⟨hg, hgU⟩, hgY⟩
  obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl, hw⟩ :=
    exists_bruhat_of_mem_normalizer AS81.G2.borelGroup_le_normalizer_g2BCGroup hg hgY
  have hY : ∀ γ, IsRoot .G2 γ → pinnedX .G2 K γ 1 ∈ Y K → (w • γ = g2b ∨ w • γ = g2c) :=
    fun γ hγ h => AS81.G2.eq_b_or_c_of_pinnedX_mem (IsRoot.smul hγ w) (hw γ hγ h)
  have hw' := AS81.G2.weyl_eq_of_bc (hY _ isRoot_g2b (AS81.G2.pinnedX_b_mem_g2BCGroup 1))
    (hY _ isRoot_g2c (AS81.G2.pinnedX_c_mem_g2BCGroup 1))
  have hnU : canonicalRep (coxeterSystem .G2) K w ∈ normalizer (U K : Set (ModGL .G2 K)) := by
    have e : canonicalRep (coxeterSystem .G2) K w =
        b₁⁻¹ * (b₁ * canonicalRep (coxeterSystem .G2) K w * b₂) * b₂⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (borelGroup_le_normalizer_U hb₁)) hgU)
      (inv_mem (borelGroup_le_normalizer_U hb₂))
  have hc : pinnedX .G2 K (w • g2c) 1 ∈ U K := by
    rw [← canonicalRep_conj w isRoot_g2c 1]
    exact (mem_normalizer_iff.mp hnU _).mp (mem_rootSubgroup.2 ⟨1, rfl⟩)
  have hwc := roots_U (IsRoot.smul isRoot_g2c w) hc
  rcases hw' with rfl | rfl
  · rw [canonicalRep_one, mul_one]
    exact mul_mem hb₁ hb₂
  · exfalso
    have h1 : simple .G2 g2ia • g2c = g2b := by
      rw [simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    rw [h1] at hwc
    exact absurd hwc (by decide)

theorem centralizer_Y_le {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    centralizer (inn (Y K) : Set (MulAut (adjointGroup .G2 K))) ≤ inn (M K ⊔ (J₁ K ⊓ J₅ K)) := by
  intro α hα
  have hfix := mem_centralizer_inn_iff.1 hα
  have hnorm : ∀ {H : Subgroup (ModGL .G2 K)}, H ≤ Y K →
      α ∈ normalizer (inn H : Set (MulAut (adjointGroup .G2 K))) := fun hHY =>
    mem_normalizer_inn_iff.2 fun x => ⟨fun h => by
      have h2 : α x = x := α.injective (hfix _ (hHY h))
      rwa [h2] at h, fun h => by
      rw [hfix x (hHY h)]
      exact h⟩
  obtain ⟨t₁, t₂, A, B, C, D, E, F, hg, k, hk, rfl⟩ := exists_borel_form₂ hK hn
    (U_le_adjointGroup K) Y_le_adjointGroup (fun k => map_entrywise_U _)
    (fun k => map_entrywise_Y _) adjointGroup_inf_normalizer_U_inf_normalizer_Y (hnorm U_le_Y)
    (hnorm le_rfl)
  have h0 : (0 : K) ^ 2 ^ k = 0 := zero_pow (pow_ne_zero k two_ne_zero)
  have hY : ∀ e f : K, g2N 0 0 0 0 e f ∈ Y K := fun e f => g2N_mem_Y_iff.2 ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨hχb, rfl⟩ := eq_one_of_forall_mul_pow_eq hK hn hk fun c => by
    have := congrArg Subtype.val (hfix ⟨_, Y_le_adjointGroup (hY c 0)⟩ (hY c 0))
    rw [coe_conj_borel_apply, g2N_conj_coords, torus_conj_g2N] at this
    obtain ⟨-, -, -, -, h5, -⟩ := g2N_injective this
    simp only [h0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      add_zero, zero_add] at h5
    exact h5
  have hB : B = 0 := by
    have := congrArg Subtype.val (hfix ⟨_, Y_le_adjointGroup (hY 1 0)⟩ (hY 1 0))
    rw [coe_conj_borel_apply, g2N_conj_coords, torus_conj_g2N] at this
    obtain ⟨-, -, -, -, -, h6⟩ := g2N_injective this
    simp only [pow_zero, pow_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, mul_one, add_zero, zero_add] at h6
    exact (mul_eq_zero.1 h6).resolve_left (Units.ne_zero _)
  subst hB
  have hχc : ((t₁ ^ (1 : ℤ) * t₂ ^ (0 : ℤ) : Kˣ) : K) = 1 := by
    have := congrArg Subtype.val (hfix ⟨_, Y_le_adjointGroup (hY 0 1)⟩ (hY 0 1))
    rw [coe_conj_borel_apply, g2N_conj_coords, torus_conj_g2N] at this
    obtain ⟨-, -, -, -, -, h6⟩ := g2N_injective this
    simp only [pow_zero, pow_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, zero_mul, mul_one, add_zero, zero_add] at h6
    exact h6
  have hJ1 : torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂ ∈ J₁ K :=
    mem_torusFix_of (m₁ := 1) (m₂ := 0) isRoot_g2c t₁ t₂ (by decide) (by decide)
      (Units.ext (by rw [Units.val_one]; exact hχc))
  have hJ5 : torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂ ∈ J₅ K :=
    mem_torusFix_of (m₁ := -1) (m₂ := 3) isRoot_g2b t₁ t₂ (by decide) (by decide)
      (Units.ext (by rw [Units.val_one]; exact hχb))
  rw [pow_zero, mul_one]
  exact conj_mem_inn (mul_mem (mem_sup_right ⟨hJ1, hJ5⟩) (mem_sup_left (g2N_mem_M_iff.2 rfl)))

theorem yamada_3_23_Y {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    centralizer (inn (Y K) : Set (MulAut (adjointGroup .G2 K))) = inn (M K ⊔ (J₁ K ⊓ J₅ K)) := by
  refine le_antisymm (centralizer_Y_le hK hn) ((inn_mono ?_).trans inn_centralizer_le)
  refine sup_le (fun m hm => mem_centralizer_iff.2 fun y hy => ?_) fun h hh =>
    mem_centralizer_iff.2 fun y hy => ?_
  · rw [← M_inf_centralizer_M] at hy
    exact (mem_centralizer_iff.1 hy.2 m hm).symm
  · rw [← rootSubgroup_b_sup_U] at hy
    have hle : rootSubgroup .G2 K g2b ⊔ U K ≤ centralizer ({h} : Set (ModGL .G2 K)) :=
      sup_le (fun z hz => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hh.2.2 z hz))
        fun z hz => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hh.1.2 z hz)
    exact mem_centralizer_singleton_iff.1 (hle hy)

theorem sectionCentralizer_W_Y_le {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    sectionCentralizer (inn (W K)) (inn (Y K)) ≤ inn (M K ⊔ leviB K) := by
  intro α hα
  obtain ⟨⟨g, hgC⟩, k, hk, rfl⟩ := exists_eq_conj_mul_fieldAut_pow hK hn α
  have hgN := mem_normalizer_of_conj_mul_fieldAut_pow W_le_adjointGroup
    (fun k => map_entrywise_W _) (sectionCentralizer_le_normalizer_left _ _ hα)
  have hgW : g ∈ M K ⊔ (leviB K ⊔ J₄ K) := by
    rw [← (yamada_3_13_3 (K := K)).2.1]
    exact ⟨hgC, hgN⟩
  have hJ4M : J₄ K ≤ normalizer (M K : Set (ModGL .G2 K)) := fun j hj =>
    borelGroup_le_normalizer_M (mem_sup_left hj.1)
  have hJ4B : J₄ K ≤ normalizer (leviB K : Set (ModGL .G2 K)) := fun j hj =>
    centralizer_le_normalizer (leviB K) (J₄_le_centralizer_leviB hj)
  obtain ⟨m, hm, a, ha, rfl⟩ := Common.exists_mul_of_le_normalizer
    (sup_le leviB_le_normalizer_M hJ4M) g hgW
  obtain ⟨l, hl, j, hj, rfl⟩ := Common.exists_mul_of_le_normalizer hJ4B a ha
  obtain ⟨t₁, t₂, rfl, hχa⟩ := torus_char_of_mem_torusFix (m₁ := 2) (m₂ := -3) isRoot_g2a
    (by decide) (by decide) hj
  rw [mem_sectionCentralizer_inn_iff Y_le_W] at hα
  obtain ⟨A, C, D, E, F, rfl⟩ := mem_M.1 hm
  have key : ∀ c : K, (pinnedX .G2 K g2v c)⁻¹ * ((g2N A 0 C D E F * (l *
      (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂))) * pinnedX .G2 K g2v (c ^ 2 ^ k) *
        (g2N A 0 C D E F * (l * (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂)))⁻¹) ∈ Y K :=
      fun c => by
    have hxW : pinnedX .G2 K g2v c ∈ W K := pinnedX_v_mem_g2ShortRadical c
    have := hα ⟨_, pinnedX_mem_adjointGroup g2v c⟩ hxW
    rwa [coe_mul, coe_inv, coe_conj_mul_fieldAut_pow_pinnedX] at this
  obtain ⟨hχv, rfl⟩ := eq_one_of_forall_mul_pow_eq hK hn hk fun c => by
    have := key c
    have e1 : g2N A 0 C D E F * (l * (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂)) *
        pinnedX .G2 K g2v (c ^ 2 ^ k) *
          (g2N A 0 C D E F * (l * (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂)))⁻¹ =
        g2N A 0 C D E F * (l * (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂ *
          pinnedX .G2 K g2v (c ^ 2 ^ k) *
            (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂)⁻¹) * l⁻¹) *
          (g2N A 0 C D E F)⁻¹ := by
      group
    have hlv := (commute_of_mem_g2RankOne_a hl
      (((t₁ ^ (0 : ℤ) * t₂ ^ (1 : ℤ) : Kˣ) : K) * c ^ 2 ^ k)).eq
    rw [e1, torus_conj_of (m₁ := 0) (m₂ := 1) isRoot_g2v t₁ t₂ (by decide) (by decide),
      hlv, mul_inv_cancel_right, pinnedX_v_eq_g2N, pinnedX_v_eq_g2N, g2N_conj_coords,
      g2N_inv_coords, g2N_mul_coords, g2N_mem_Y_iff] at this
    have h4 := this.2.2.2
    simp only [mul_zero, add_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow] at h4
    exact (CharTwo.add_eq_zero.1 h4).symm
  have ht₂ : t₂ = 1 := Units.ext (by simpa using hχv)
  subst ht₂
  have ht₁ : t₁ = 1 := by
    rw [one_zpow, mul_one, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast] at hχa
    exact units_eq_one_of_sq_eq_one hχa
  subst ht₁
  rw [pow_zero, mul_one]
  refine conj_mem_inn ?_
  simp only [torusElt_one, mul_one]
  exact mul_mem (mem_sup_left (g2N_mem_M_iff.2 rfl)) (mem_sup_right hl)

theorem yamada_3_23_W_Y {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    sectionCentralizer (inn (W K)) (inn (Y K)) = inn (M K ⊔ leviB K) := by
  refine le_antisymm (sectionCentralizer_W_Y_le hK hn) ?_
  rw [inn_sup M_le_adjointGroup (leviB_le_adjointGroup K)]
  refine sup_le (inn_le_sectionCentralizer_of_commutator Y_le_W fun y hy s hs => ?_)
    (inn_le_sectionCentralizer Y_le_W fun y hy _ l hl => ?_)
  · obtain ⟨d, e, f, rfl⟩ := mem_W.1 hy
    obtain ⟨A, C, D, E, F, rfl⟩ := mem_M.1 hs
    rw [g2N_commutator_coords, g2N_mem_Y_iff]
    refine ⟨rfl, rfl, ?_, ?_⟩ <;> ring
  · obtain ⟨d, e, f, rfl⟩ := mem_W.1 hy
    have hsplit : g2N (0 : K) 0 0 d e f = pinnedX .G2 K g2v d * g2N 0 0 0 0 e f := by
      rw [pinnedX_v_eq_g2N, g2N_mul_coords]
      refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
    have hy₀ : g2N (0 : K) 0 0 0 e f ∈ Y K := g2N_mem_Y_iff.2 ⟨rfl, rfl, rfl, rfl⟩
    have hly : l * g2N 0 0 0 0 e f * l⁻¹ ∈ Y K :=
      (mem_normalizer_iff.1 (AS81.G2.g2RankOne_a_le_normalizer hl) _).1 hy₀
    have hcomm : l * pinnedX .G2 K g2v d = pinnedX .G2 K g2v d * l :=
      (commute_of_mem_g2RankOne_a hl d).eq
    rw [hsplit]
    have e2 : (pinnedX .G2 K g2v d * g2N 0 0 0 0 e f)⁻¹ *
        (l * (pinnedX .G2 K g2v d * g2N 0 0 0 0 e f) * l⁻¹) =
          (g2N 0 0 0 0 e f)⁻¹ * (l * g2N 0 0 0 0 e f * l⁻¹) := by
      calc (pinnedX .G2 K g2v d * g2N 0 0 0 0 e f)⁻¹ *
            (l * (pinnedX .G2 K g2v d * g2N 0 0 0 0 e f) * l⁻¹) =
            (g2N 0 0 0 0 e f)⁻¹ * (pinnedX .G2 K g2v d)⁻¹ * (l * pinnedX .G2 K g2v d) *
              g2N 0 0 0 0 e f * l⁻¹ := by group
        _ = (g2N 0 0 0 0 e f)⁻¹ * (pinnedX .G2 K g2v d)⁻¹ * (pinnedX .G2 K g2v d * l) *
              g2N 0 0 0 0 e f * l⁻¹ := by rw [hcomm]
        _ = (g2N 0 0 0 0 e f)⁻¹ * (l * g2N 0 0 0 0 e f * l⁻¹) := by group
    rw [e2]
    exact mul_mem (inv_mem hy₀) hly

end Sections

section Levi

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit
  [Finite K] [CharP K 2] in
theorem units_map_entrywise_mem_leviA (σ : K ≃+* K) {x : ModGL .G2 K} (hx : x ∈ leviA K) :
    Units.map (entrywiseHom σ.toRingHom) x ∈ leviA K := by
  have hle : leviA K ≤ (leviA K).comap (Units.map (entrywiseHom σ.toRingHom)) := by
    rw [leviA, g2RankOne_r_eq, closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [SetLike.mem_coe, mem_comap, units_map_entrywise_pinnedX]
      exact subset_closure (Or.inl ⟨_, rfl⟩)
    · rw [SetLike.mem_coe, mem_comap, units_map_entrywise_pinnedX]
      exact subset_closure (Or.inr ⟨_, rfl⟩)
  exact hle hx

omit
  [Finite K] [CharP K 2] in
theorem units_map_entrywise_mem_leviB (σ : K ≃+* K) {x : ModGL .G2 K} (hx : x ∈ leviB K) :
    Units.map (entrywiseHom σ.toRingHom) x ∈ leviB K := by
  have hle : leviB K ≤ (leviB K).comap (Units.map (entrywiseHom σ.toRingHom)) := by
    rw [leviB, g2RankOne_a_eq, closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [SetLike.mem_coe, mem_comap, units_map_entrywise_pinnedX]
      exact subset_closure (Or.inl ⟨_, rfl⟩)
    · rw [SetLike.mem_coe, mem_comap, units_map_entrywise_pinnedX]
      exact subset_closure (Or.inr ⟨_, rfl⟩)
  exact hle hx

theorem M_inf_leviB : M K ⊓ leviB K = ⊥ := by
  obtain ⟨-, -, -, -, -, -, hinf, -, hL, -⟩ := even_G2_highest_short_root_centralizer K
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxM, hxL⟩ := mem_inf.1 hx
  obtain ⟨A, C, D, E, F, rfl⟩ := mem_M.1 hxM
  have h1 : ⁅g2N A 0 C D E F, g2N (0 : K) 0 0 1 0 0⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm, ← pinnedX_v_eq_g2N]
    exact (hL _ hxL 1).eq
  obtain ⟨-, -, h5, h6⟩ := coords_of_commutator_eq_one h1
  simp only [mul_zero, zero_mul, mul_one, add_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow] at h5 h6
  subst h5 h6
  rw [← hinf]
  exact ⟨g2N_mem_W_iff.2 ⟨rfl, rfl, rfl⟩, hxL⟩

theorem sectionCentralizer_DA_D_le {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    sectionCentralizer (inn (Model.D K ⊔ leviA K)) (inn (Model.D K)) ≤
      inn (Model.D K ⊔ J₃ K) := by
  intro α hα
  obtain ⟨⟨g, hgC⟩, k, hk, rfl⟩ := exists_eq_conj_mul_fieldAut_pow hK hn α
  have hgN := mem_normalizer_of_conj_mul_fieldAut_pow D_le_adjointGroup
    (fun k => map_entrywise_D _) (sectionCentralizer_le_normalizer_right _ _ hα)
  have hgD : g ∈ Model.D K ⊔ (leviA K ⊔ J₃ K) := by
    rw [← (yamada_3_13_2 (K := K)).2.1]
    exact ⟨hgC, hgN⟩
  have hJ3D : J₃ K ≤ normalizer (Model.D K : Set (ModGL .G2 K)) := fun j hj =>
    borelGroup_le_normalizer_D (mem_sup_left hj.1)
  have hJ3A : J₃ K ≤ normalizer (leviA K : Set (ModGL .G2 K)) := fun j hj =>
    centralizer_le_normalizer (leviA K) (J₃_le_centralizer_leviA hj)
  obtain ⟨d, hd, a, ha, rfl⟩ := Common.exists_mul_of_le_normalizer
    (sup_le g2RankOne_r_le_normalizer hJ3D) g hgD
  obtain ⟨l, hl, j, hj, rfl⟩ := Common.exists_mul_of_le_normalizer hJ3A a ha
  rw [mem_sectionCentralizer_inn_iff le_sup_left] at hα
  obtain ⟨-, -, -, -, -, hnorm, hinf, ⟨ρ, hρu, hρv, hρr, hρi⟩, -, -, -, -⟩ :=
    even_G2_highest_long_root_centralizer K
  have key : ∀ x : adjointGroup .G2 K, (x : ModGL .G2 K) ∈ leviA K →
      l * Units.map (entrywiseHom (frobeniusEquiv K 2 ^ k).toRingHom) (x : ModGL .G2 K) * l⁻¹ =
        x := by
    intro x hx
    have h1 := hα x (mem_sup_right hx)
    rw [coe_mul, coe_inv, coe_conj_mul_fieldAut_pow_apply] at h1
    have hyA := units_map_entrywise_mem_leviA (frobeniusEquiv K 2 ^ k) hx
    set y := Units.map (entrywiseHom (frobeniusEquiv K 2 ^ k).toRingHom) (x : ModGL .G2 K)
      with hy
    have hjy : j * y = y * j := (mem_centralizer_iff.1 (J₃_le_centralizer_leviA hj) y hyA).symm
    have hzA : l * y * l⁻¹ ∈ leviA K := mul_mem (mul_mem hl hyA) (inv_mem hl)
    have h1' : (x : ModGL .G2 K)⁻¹ * (d * (l * j) * y * (d * (l * j))⁻¹) ∈ Model.D K := h1
    have e : (x : ModGL .G2 K)⁻¹ * (d * (l * j) * y * (d * (l * j))⁻¹) =
        ((x : ModGL .G2 K)⁻¹ * (l * y * l⁻¹)) *
          ((l * y * l⁻¹)⁻¹ * d * (l * y * l⁻¹) * d⁻¹) := by
      calc (x : ModGL .G2 K)⁻¹ * (d * (l * j) * y * (d * (l * j))⁻¹) =
          (x : ModGL .G2 K)⁻¹ * d * l * (j * y) * j⁻¹ * l⁻¹ * d⁻¹ := by group
        _ = (x : ModGL .G2 K)⁻¹ * d * l * (y * j) * j⁻¹ * l⁻¹ * d⁻¹ := by rw [hjy]
        _ = _ := by group
    rw [e] at h1'
    have h2 : (l * y * l⁻¹)⁻¹ * d * (l * y * l⁻¹) * d⁻¹ ∈ Model.D K := by
      have := (mem_normalizer_iff.1 (inv_mem (hnorm hzA)) d).1 hd
      rw [inv_inv] at this
      exact mul_mem this (inv_mem hd)
    have h3 : (x : ModGL .G2 K)⁻¹ * (l * y * l⁻¹) ∈ Model.D K ⊓ leviA K := by
      refine mem_inf.2 ⟨?_, mul_mem (inv_mem hx) hzA⟩
      have := mul_mem h1' (inv_mem h2)
      rwa [mul_inv_cancel_right] at this
    rw [hinf, mem_bot, inv_mul_eq_one] at h3
    exact h3.symm
  have hr : ∀ c : K, l * pinnedX .G2 K g2r (c ^ 2 ^ k) * l⁻¹ = pinnedX .G2 K g2r c := fun c => by
    have := key ⟨_, pinnedX_mem_adjointGroup g2r c⟩ (pinnedX_r_mem_leviA c)
    rwa [units_map_entrywise_pinnedX, frobeniusEquiv_pow_apply] at this
  have hnrA : ∀ c : K, pinnedX .G2 K g2nr c ∈ leviA K := fun c => by
    rw [leviA, g2RankOne_r_eq]
    exact subset_closure (Or.inr ⟨c, rfl⟩)
  have hnr : ∀ c : K, l * pinnedX .G2 K g2nr (c ^ 2 ^ k) * l⁻¹ = pinnedX .G2 K g2nr c :=
    fun c => by
      have := key ⟨_, pinnedX_mem_adjointGroup g2nr c⟩ (hnrA c)
      rwa [units_map_entrywise_pinnedX, frobeniusEquiv_pow_apply] at this
  have hl1 : l = 1 := by
    refine eq_one_of_commute_of_mem_range hρi (by rw [hρr]; exact hl) ?_ ?_
    · rw [hρu]
      have := hr 1
      rw [one_pow] at this
      calc l * pinnedX .G2 K g2r 1 = l * pinnedX .G2 K g2r 1 * l⁻¹ * l := by group
        _ = pinnedX .G2 K g2r 1 * l := by rw [this]
    · rw [hρv]
      have := hnr 1
      rw [one_pow] at this
      calc l * pinnedX .G2 K g2nr 1 = l * pinnedX .G2 K g2nr 1 * l⁻¹ * l := by group
        _ = pinnedX .G2 K g2nr 1 * l := by rw [this]
  subst hl1
  have hk0 : k = 0 := eq_zero_of_forall_pow_eq hK hn hk fun c =>
    pinnedX_injective .G2 K g2r (by simpa using hr c)
  subst hk0
  rw [pow_zero, mul_one]
  refine conj_mem_inn (mul_mem (mem_sup_left hd) ?_)
  rw [one_mul]
  exact mem_sup_right hj

theorem sectionCentralizer_MB_M_le {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    sectionCentralizer (inn (M K ⊔ leviB K)) (inn (M K)) ≤ inn (M K ⊔ J₄ K) := by
  intro α hα
  obtain ⟨⟨g, hgC⟩, k, hk, rfl⟩ := exists_eq_conj_mul_fieldAut_pow hK hn α
  have hgN := mem_normalizer_of_conj_mul_fieldAut_pow M_le_adjointGroup
    (fun k => map_entrywise_M _) (sectionCentralizer_le_normalizer_right _ _ hα)
  have hgM : g ∈ M K ⊔ (leviB K ⊔ J₄ K) := by
    rw [← (yamada_3_13_3 (K := K)).2.2.1]
    exact ⟨hgC, hgN⟩
  have hJ4M : J₄ K ≤ normalizer (M K : Set (ModGL .G2 K)) := fun j hj =>
    borelGroup_le_normalizer_M (mem_sup_left hj.1)
  have hJ4B : J₄ K ≤ normalizer (leviB K : Set (ModGL .G2 K)) := fun j hj =>
    centralizer_le_normalizer (leviB K) (J₄_le_centralizer_leviB hj)
  obtain ⟨m, hm, a, ha, rfl⟩ := Common.exists_mul_of_le_normalizer
    (sup_le leviB_le_normalizer_M hJ4M) g hgM
  obtain ⟨l, hl, j, hj, rfl⟩ := Common.exists_mul_of_le_normalizer hJ4B a ha
  rw [mem_sectionCentralizer_inn_iff le_sup_left] at hα
  obtain ⟨-, -, -, -, -, -, -, ⟨ρ, hρu, hρv, hρr, hρi⟩, -, -⟩ :=
    even_G2_highest_short_root_centralizer K
  have key : ∀ x : adjointGroup .G2 K, (x : ModGL .G2 K) ∈ leviB K →
      l * Units.map (entrywiseHom (frobeniusEquiv K 2 ^ k).toRingHom) (x : ModGL .G2 K) * l⁻¹ =
        x := by
    intro x hx
    have h1 := hα x (mem_sup_right hx)
    rw [coe_mul, coe_inv, coe_conj_mul_fieldAut_pow_apply] at h1
    have hyB := units_map_entrywise_mem_leviB (frobeniusEquiv K 2 ^ k) hx
    set y := Units.map (entrywiseHom (frobeniusEquiv K 2 ^ k).toRingHom) (x : ModGL .G2 K)
      with hy
    have hjy : j * y = y * j := (mem_centralizer_iff.1 (J₄_le_centralizer_leviB hj) y hyB).symm
    have hzB : l * y * l⁻¹ ∈ leviB K := mul_mem (mul_mem hl hyB) (inv_mem hl)
    have h1' : (x : ModGL .G2 K)⁻¹ * (m * (l * j) * y * (m * (l * j))⁻¹) ∈ M K := h1
    have e : (x : ModGL .G2 K)⁻¹ * (m * (l * j) * y * (m * (l * j))⁻¹) =
        ((x : ModGL .G2 K)⁻¹ * (l * y * l⁻¹)) *
          ((l * y * l⁻¹)⁻¹ * m * (l * y * l⁻¹) * m⁻¹) := by
      calc (x : ModGL .G2 K)⁻¹ * (m * (l * j) * y * (m * (l * j))⁻¹) =
          (x : ModGL .G2 K)⁻¹ * m * l * (j * y) * j⁻¹ * l⁻¹ * m⁻¹ := by group
        _ = (x : ModGL .G2 K)⁻¹ * m * l * (y * j) * j⁻¹ * l⁻¹ * m⁻¹ := by rw [hjy]
        _ = _ := by group
    rw [e] at h1'
    have h2 : (l * y * l⁻¹)⁻¹ * m * (l * y * l⁻¹) * m⁻¹ ∈ M K := by
      have := (mem_normalizer_iff.1 (inv_mem (leviB_le_normalizer_M hzB)) m).1 hm
      rw [inv_inv] at this
      exact mul_mem this (inv_mem hm)
    have h3 : (x : ModGL .G2 K)⁻¹ * (l * y * l⁻¹) ∈ M K ⊓ leviB K := by
      refine mem_inf.2 ⟨?_, mul_mem (inv_mem hx) hzB⟩
      have := mul_mem h1' (inv_mem h2)
      rwa [mul_inv_cancel_right] at this
    rw [M_inf_leviB, mem_bot, inv_mul_eq_one] at h3
    exact h3.symm
  have ha' : ∀ c : K, l * pinnedX .G2 K g2a (c ^ 2 ^ k) * l⁻¹ = pinnedX .G2 K g2a c := fun c => by
    have := key ⟨_, pinnedX_mem_adjointGroup g2a c⟩ (pinnedX_mem_leviB c).1
    rwa [units_map_entrywise_pinnedX, frobeniusEquiv_pow_apply] at this
  have hna : ∀ c : K, l * pinnedX .G2 K g2na (c ^ 2 ^ k) * l⁻¹ = pinnedX .G2 K g2na c :=
    fun c => by
      have := key ⟨_, pinnedX_mem_adjointGroup g2na c⟩ (pinnedX_mem_leviB c).2
      rwa [units_map_entrywise_pinnedX, frobeniusEquiv_pow_apply] at this
  have hl1 : l = 1 := by
    refine eq_one_of_commute_of_mem_range hρi (by rw [hρr]; exact hl) ?_ ?_
    · rw [hρu]
      have := ha' 1
      rw [one_pow] at this
      calc l * pinnedX .G2 K g2a 1 = l * pinnedX .G2 K g2a 1 * l⁻¹ * l := by group
        _ = pinnedX .G2 K g2a 1 * l := by rw [this]
    · rw [hρv]
      have := hna 1
      rw [one_pow] at this
      calc l * pinnedX .G2 K g2na 1 = l * pinnedX .G2 K g2na 1 * l⁻¹ * l := by group
        _ = pinnedX .G2 K g2na 1 * l := by rw [this]
  subst hl1
  have hk0 : k = 0 := eq_zero_of_forall_pow_eq hK hn hk fun c =>
    pinnedX_injective .G2 K g2a (by simpa using ha' c)
  subst hk0
  rw [pow_zero, mul_one]
  refine conj_mem_inn (mul_mem (mem_sup_left hm) ?_)
  rw [one_mul]
  exact mem_sup_right hj

theorem yamada_3_23_3 {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    ⁅adjointGroup .G2 K ⊓ normalizer (U K : Set (ModGL .G2 K)),
        adjointGroup .G2 K ⊓ normalizer (U K : Set (ModGL .G2 K))⁆ = Model.D K ⊔ leviA K ∧
      sectionCentralizer (inn (Model.D K ⊔ leviA K)) (inn (Model.D K)) =
        inn (Model.D K ⊔ J₃ K) ∧
      ⁅adjointGroup .G2 K ⊓ normalizer (Y K : Set (ModGL .G2 K)),
        adjointGroup .G2 K ⊓ normalizer (Y K : Set (ModGL .G2 K))⁆ = M K ⊔ leviB K ∧
      sectionCentralizer (inn (M K ⊔ leviB K)) (inn (M K)) = inn (M K ⊔ J₄ K) := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hUD : adjointGroup .G2 K ⊓ normalizer (U K : Set (ModGL .G2 K)) =
      adjointGroup .G2 K ⊓ normalizer (Model.D K : Set (ModGL .G2 K)) :=
    (yamada_3_13_2 (K := K)).1.trans (yamada_3_13_2 (K := K)).2.1.symm
  have hYM : adjointGroup .G2 K ⊓ normalizer (Y K : Set (ModGL .G2 K)) =
      adjointGroup .G2 K ⊓ normalizer (M K : Set (ModGL .G2 K)) :=
    (yamada_3_13_3 (K := K)).1.trans (yamada_3_13_3 (K := K)).2.2.1.symm
  have hDN : Model.D K ⊔ leviA K ≤ normalizer (Model.D K : Set (ModGL .G2 K)) :=
    sup_le le_normalizer g2RankOne_r_le_normalizer
  have hMN : M K ⊔ leviB K ≤ normalizer (M K : Set (ModGL .G2 K)) :=
    sup_le le_normalizer leviB_le_normalizer_M
  refine ⟨by rw [hUD]; exact (yamada_3_13_4_D hK4).1,
    le_antisymm (sectionCentralizer_DA_D_le hK hn) ?_,
    by rw [hYM]; exact (yamada_3_13_4_M hK4).1,
    le_antisymm (sectionCentralizer_MB_M_le hK hn) ?_⟩
  · rw [inn_sup D_le_adjointGroup (torusFix_le_adjointGroup K g2r)]
    refine sup_le (inn_le_sectionCentralizer le_sup_left fun y hy _ s hs => ?_)
      (inn_le_sectionCentralizer le_sup_left fun y hy _ j hj => ?_)
    · have := (mem_normalizer_iff.1 (inv_mem (hDN hy)) s).1 hs
      rw [inv_inv] at this
      rw [show y⁻¹ * (s * y * s⁻¹) = y⁻¹ * s * y * s⁻¹ by group]
      exact mul_mem this (inv_mem hs)
    · obtain ⟨d, hd, l, hl, rfl⟩ := Common.exists_mul_of_le_normalizer
        g2RankOne_r_le_normalizer y hy
      have hjl : j * l = l * j := (mem_centralizer_iff.1 (J₃_le_centralizer_leviA hj) l hl).symm
      have hjd : j * d * j⁻¹ ∈ Model.D K :=
        (mem_normalizer_iff.1 (borelGroup_le_normalizer_D (mem_sup_left hj.1)) d).1 hd
      have e : (d * l)⁻¹ * (j * (d * l) * j⁻¹) = l⁻¹ * (d⁻¹ * (j * d * j⁻¹)) * l := by
        calc (d * l)⁻¹ * (j * (d * l) * j⁻¹) = l⁻¹ * d⁻¹ * (j * d * j⁻¹) * (j * l) * j⁻¹ := by
              group
          _ = l⁻¹ * d⁻¹ * (j * d * j⁻¹) * (l * j) * j⁻¹ := by rw [hjl]
          _ = _ := by group
      rw [e]
      have := (mem_normalizer_iff.1 (inv_mem (g2RankOne_r_le_normalizer hl)) _).1
        (mul_mem (inv_mem hd) hjd)
      rwa [inv_inv] at this
  · rw [inn_sup M_le_adjointGroup (torusFix_le_adjointGroup K g2a)]
    refine sup_le (inn_le_sectionCentralizer le_sup_left fun y hy _ s hs => ?_)
      (inn_le_sectionCentralizer le_sup_left fun y hy _ j hj => ?_)
    · have := (mem_normalizer_iff.1 (inv_mem (hMN hy)) s).1 hs
      rw [inv_inv] at this
      rw [show y⁻¹ * (s * y * s⁻¹) = y⁻¹ * s * y * s⁻¹ by group]
      exact mul_mem this (inv_mem hs)
    · obtain ⟨m, hm, l, hl, rfl⟩ := Common.exists_mul_of_le_normalizer leviB_le_normalizer_M y hy
      have hjl : j * l = l * j := (mem_centralizer_iff.1 (J₄_le_centralizer_leviB hj) l hl).symm
      have hjm : j * m * j⁻¹ ∈ M K :=
        (mem_normalizer_iff.1 (borelGroup_le_normalizer_M (mem_sup_left hj.1)) m).1 hm
      have e : (m * l)⁻¹ * (j * (m * l) * j⁻¹) = l⁻¹ * (m⁻¹ * (j * m * j⁻¹)) * l := by
        calc (m * l)⁻¹ * (j * (m * l) * j⁻¹) = l⁻¹ * m⁻¹ * (j * m * j⁻¹) * (j * l) * j⁻¹ := by
              group
          _ = l⁻¹ * m⁻¹ * (j * m * j⁻¹) * (l * j) * j⁻¹ := by rw [hjl]
          _ = _ := by group
      rw [e]
      have := (mem_normalizer_iff.1 (inv_mem (leviB_le_normalizer_M hl)) _).1
        (mul_mem (inv_mem hm) hjm)
      rwa [inv_inv] at this

end Levi

section Core

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite K] in
theorem S_isPGroup : IsPGroup 2 (S K) := fun x =>
  ⟨3, Subtype.ext (by rw [coe_pow, coe_one]; exact pow_eight_eq_one_of_mem_S x.2)⟩

omit [Finite K] in
theorem inn_isPGroup {R : Subgroup (ModGL .G2 K)} (hRS : R ≤ S K) : IsPGroup 2 (inn R) := by
  intro x
  obtain ⟨g, hg, hgx⟩ := mem_inn.1 x.2
  refine ⟨3, Subtype.ext ?_⟩
  have h8 : g ^ 8 = 1 :=
    Subtype.ext (by rw [coe_pow, coe_one]; exact pow_eight_eq_one_of_mem_S (hRS hg))
  rw [coe_pow, coe_one, ← hgx, ← map_pow, show 2 ^ 3 = 8 by norm_num, h8, map_one]

theorem S_inf_J : S K ⊓ Model.J K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥(S K ⊓ Model.J K) := S_isPGroup.to_le inf_le_left
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hp
  have hdvd : Nat.card (S K ⊓ Model.J K : Subgroup (ModGL .G2 K)) ∣ Nat.card (Model.J K) :=
    Subgroup.card_dvd_of_le inf_le_right
  have hodd := not_dvd_card_torusGroup (τ := .G2) (K := K) 2
  rcases m with _ | m
  · exact Subgroup.eq_bot_of_card_eq _ (by rw [hm, pow_zero])
  · rw [hm] at hdvd
    exact absurd (dvd_trans (dvd_pow_self 2 (Nat.succ_ne_zero m)) hdvd) hodd

omit
  [Finite K] [CharP K 2] in
theorem units_map_entrywise_mem_torusFix (σ : K ≃+* K) {s : Fin Tag.G2.rank → ℤ}
    {h : ModGL .G2 K} (hh : h ∈ torusFix K s) :
    Units.map (entrywiseHom σ.toRingHom) h ∈ torusFix K s := by
  refine ⟨entrywise_mem_torusGroup hh.1, mem_centralizer_iff.2 fun y hy => ?_⟩
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hy
  have := congrArg (Units.map (entrywiseHom σ.toRingHom))
    (mem_centralizer_iff.1 hh.2 _ (mem_rootSubgroup.2 ⟨σ.symm c, rfl⟩))
  rwa [map_mul, map_mul, units_map_entrywise_pinnedX, RingEquiv.apply_symm_apply] at this

theorem le_S_of_isPGroup {O : Subgroup (ModGL .G2 K)} (hOC : O ≤ adjointGroup .G2 K)
    (hp : IsPGroup 2 O) (hS : S K ≤ normalizer (O : Set (ModGL .G2 K))) : O ≤ S K :=
  le_sup_left.trans (eq_S_of_isPGroup (sup_le hOC (S_le_adjointGroup K)) le_sup_right
    (hp.to_sup_of_normal_left' S_isPGroup hS)).le

theorem le_D_of_isPGroup {O : Subgroup (ModGL .G2 K)} (hOC : O ≤ adjointGroup .G2 K)
    (hp : IsPGroup 2 O) (hS : S K ≤ normalizer (O : Set (ModGL .G2 K)))
    (hw : wa K ∈ normalizer (O : Set (ModGL .G2 K))) : O ≤ Model.D K := by
  intro x hx
  have hwx := le_S_of_isPGroup hOC hp hS ((mem_normalizer_iff.1 hw x).1 hx)
  obtain ⟨A, q, hq, rfl⟩ := exists_pinnedX_r_mul_of_mem_posUnipotent
    (le_S_of_isPGroup hOC hp hS hx)
  have h1 : wa K * pinnedX .G2 K g2r A * (wa K)⁻¹ = pinnedX .G2 K (-g2r) A := by
    rw [wa, ← canonicalRep_simple (coxeterSystem .G2) K g2ir, canonicalRep_conj _ isRoot_g2r A]
    congr 1
    rw [simple_smul]
    exact List.ofFn_injective (by decide +kernel)
  obtain ⟨B, C, D, E, F, rfl⟩ := mem_D.1 hq
  have h2 : wa K * g2N 0 B C D E F * (wa K)⁻¹ ∈ Model.D K := by
    rw [wa, weylElt_r_conj_g2N]
    exact g2N_mem_D_iff.2 rfl
  have e : pinnedX .G2 K (-g2r) A = (wa K * (pinnedX .G2 K g2r A * g2N 0 B C D E F) * (wa K)⁻¹) *
      (wa K * g2N 0 B C D E F * (wa K)⁻¹)⁻¹ := by
    rw [← h1]
    group
  have h3 : pinnedX .G2 K (-g2r) A ∈ S K := by
    rw [e]
    exact mul_mem hwx (inv_mem (D_le_S h2))
  have hA : A = 0 := pinnedX_injective .G2 K _ ((eq_one_of_mem_borel_of_mem_neg
    (posUnipotent_le_borelGroup h3) (pinnedX_neg_mem_negUnipotent (Or.inl rfl) A)).trans
      (pinnedX_zero .G2 K _).symm)
  rw [hA, pinnedX_zero, one_mul]
  exact g2N_mem_D_iff.2 rfl

theorem le_M_of_isPGroup {O : Subgroup (ModGL .G2 K)} (hOC : O ≤ adjointGroup .G2 K)
    (hp : IsPGroup 2 O) (hS : S K ≤ normalizer (O : Set (ModGL .G2 K)))
    (hw : wb K ∈ normalizer (O : Set (ModGL .G2 K))) : O ≤ M K := by
  intro x hx
  have hwx := le_S_of_isPGroup hOC hp hS ((mem_normalizer_iff.1 hw x).1 hx)
  obtain ⟨q, hq, B, rfl⟩ := exists_mul_pinnedX_a_of_mem_posUnipotent
    (le_S_of_isPGroup hOC hp hS hx)
  have h1 : wb K * pinnedX .G2 K g2a B * (wb K)⁻¹ = pinnedX .G2 K (-g2a) B := by
    rw [wb, ← canonicalRep_simple (coxeterSystem .G2) K g2ia, canonicalRep_conj _ isRoot_g2a B]
    congr 1
    rw [simple_smul]
    exact List.ofFn_injective (by decide +kernel)
  obtain ⟨A, C, D, E, F, rfl⟩ := mem_M.1 hq
  have h2 : wb K * g2N A 0 C D E F * (wb K)⁻¹ ∈ M K := by
    rw [wb, weylElt_a_conj_g2N]
    exact g2N_mem_M_iff.2 rfl
  have e : pinnedX .G2 K (-g2a) B = (wb K * g2N A 0 C D E F * (wb K)⁻¹)⁻¹ *
      (wb K * (g2N A 0 C D E F * pinnedX .G2 K g2a B) * (wb K)⁻¹) := by
    rw [← h1]
    group
  have h3 : pinnedX .G2 K (-g2a) B ∈ S K := by
    rw [e]
    exact mul_mem (inv_mem (M_le_S h2)) hwx
  have hB : B = 0 := pinnedX_injective .G2 K _ ((eq_one_of_mem_borel_of_mem_neg
    (posUnipotent_le_borelGroup h3) (pinnedX_neg_mem_negUnipotent (Or.inr (Or.inl rfl)) B)).trans
      (pinnedX_zero .G2 K _).symm)
  rw [hB, pinnedX_zero, mul_one]
  exact g2N_mem_M_iff.2 rfl

theorem pCoreOf_normalizer_eq {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    {B : Subgroup (MulAut (adjointGroup .G2 K))} (hB : inner (adjointGroup .G2 K) ≤ B)
    {H R Jc : Subgroup (ModGL .G2 K)} (hHC : H ≤ adjointGroup .G2 K)
    (hH : ∀ k : ℕ, H.map (Units.map (entrywiseHom (frobeniusEquiv K 2 ^ k).toRingHom)) = H)
    (hRS : R ≤ S K)
    (hR : ∀ k : ℕ, R.map (Units.map (entrywiseHom (frobeniusEquiv K 2 ^ k).toRingHom)) = R)
    (hRN : R ≤ normalizer (H : Set (ModGL .G2 K)))
    (hNR : adjointGroup .G2 K ⊓ normalizer (H : Set (ModGL .G2 K)) ≤
      normalizer (R : Set (ModGL .G2 K)))
    (hcore : ∀ O : Subgroup (ModGL .G2 K), O ≤ adjointGroup .G2 K → IsPGroup 2 O →
      adjointGroup .G2 K ⊓ normalizer (H : Set (ModGL .G2 K)) ≤
        normalizer (O : Set (ModGL .G2 K)) → O ≤ R)
    (hJc : Jc ≤ adjointGroup .G2 K ⊓ normalizer (H : Set (ModGL .G2 K)))
    (hfix : ∀ g : adjointGroup .G2 K, (g : ModGL .G2 K) ∈ normalizer (H : Set (ModGL .G2 K)) →
      ∀ k < n, (∀ h : adjointGroup .G2 K, (h : ModGL .G2 K) ∈ Jc →
        (g : ModGL .G2 K) * Units.map (entrywiseHom (frobeniusEquiv K 2 ^ k).toRingHom)
          (h : ModGL .G2 K) * (g : ModGL .G2 K)⁻¹ * (h : ModGL .G2 K)⁻¹ ∈ R) → k = 0) :
    CFSG.Open.pCoreOf 2 (B ⊓ normalizer (inn H : Set (MulAut (adjointGroup .G2 K)))) =
      inn R := by
  have : Finite (MulAut (adjointGroup .G2 K)) := MulEquiv.finite_left
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRC : R ≤ adjointGroup .G2 K := hRS.trans (S_le_adjointGroup K)
  set P := B ⊓ normalizer (inn H : Set (MulAut (adjointGroup .G2 K))) with hP
  have hconjP : ∀ g : adjointGroup .G2 K, (g : ModGL .G2 K) ∈ normalizer (H : Set (ModGL .G2 K)) →
      MulAut.conj g ∈ P := fun g hg => ⟨hB ⟨g, rfl⟩, (conj_mem_normalizer_inn_iff hHC).2 hg⟩
  apply le_antisymm
  · set O := CFSG.Open.pCoreOf 2 P with hO
    have hOP : O ≤ P := LieType.BorelTits.pCoreOf_le 2 P
    have hPO : P ≤ normalizer (O : Set (MulAut (adjointGroup .G2 K))) :=
      LieType.BorelTits.le_normalizer_pCoreOf 2 P
    have hOp : IsPGroup 2 O := LieType.BorelTits.pCoreOf_isPGroup 2 P
    set O₀ : Subgroup (ModGL .G2 K) := (O.comap
      (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K))).map
        (adjointGroup .G2 K).subtype with hO₀
    have hO₀C : O₀ ≤ adjointGroup .G2 K := by
      rintro _ ⟨g, -, rfl⟩
      exact g.2
    have hmem : ∀ z : adjointGroup .G2 K, (z : ModGL .G2 K) ∈ O₀ ↔ MulAut.conj z ∈ O :=
      fun z => ⟨fun ⟨w, hw, hwz⟩ => by rwa [← Subtype.ext hwz], fun h => ⟨z, h, rfl⟩⟩
    have hO₀N : adjointGroup .G2 K ⊓ normalizer (H : Set (ModGL .G2 K)) ≤
        normalizer (O₀ : Set (ModGL .G2 K)) := by
      intro g hg
      obtain ⟨hgC, hgH⟩ := mem_inf.1 hg
      have h1 := hPO (hconjP ⟨g, hgC⟩ hgH)
      rw [mem_normalizer_iff]
      intro y
      by_cases hy : y ∈ adjointGroup .G2 K
      · have h2 := mem_normalizer_iff.1 h1 (MulAut.conj ⟨y, hy⟩)
        rw [← map_inv, ← map_mul, ← map_mul] at h2
        exact (hmem ⟨y, hy⟩).trans (h2.trans (hmem _).symm)
      · refine ⟨fun h => absurd (hO₀C h) hy, fun h => absurd ?_ hy⟩
        have := mul_mem (mul_mem (inv_mem hgC) (hO₀C h)) hgC
        rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at this
    have hO₀R := hcore O₀ hO₀C ((hOp.comap_of_injective _ conj_injective).map _) hO₀N
    have hOinner : O ⊓ inner (adjointGroup .G2 K) ≤ inn R := by
      rintro α ⟨hαO, ⟨g, rfl⟩⟩
      exact conj_mem_inn (hO₀R ((hmem g).2 hαO))
    intro α hα
    obtain ⟨g, k, hk, rfl⟩ := exists_eq_conj_mul_fieldAut_pow hK hn α
    have hgH := mem_normalizer_of_conj_mul_fieldAut_pow hHC hH (hOP hα).2
    have hk0 : k = 0 := hfix g hgH k hk fun h hhJ => by
      have hhP : MulAut.conj h ∈ P := hconjP h (hJc hhJ).2
      have hc : (MulAut.conj g * fieldAut K ^ k) * MulAut.conj h *
          (MulAut.conj g * fieldAut K ^ k)⁻¹ * (MulAut.conj h)⁻¹ ∈
            O ⊓ inner (adjointGroup .G2 K) := by
        refine mem_inf.2 ⟨?_, ?_⟩
        · have h1 : MulAut.conj h * (MulAut.conj g * fieldAut K ^ k)⁻¹ * (MulAut.conj h)⁻¹ ∈ O :=
            (mem_normalizer_iff.1 (hPO hhP) _).1 (inv_mem hα)
          have := mul_mem hα h1
          simpa only [mul_assoc] using this
        · rw [mulAut_mul_conj_mul_inv, ← map_inv, ← map_mul]
          exact ⟨_, rfl⟩
      have h2 := hOinner hc
      rw [mulAut_mul_conj_mul_inv, ← map_inv, ← map_mul, conj_mem_inn_iff] at h2
      rwa [coe_mul, coe_inv, coe_conj_mul_fieldAut_pow_apply] at h2
    subst hk0
    rw [pow_zero, mul_one] at hα ⊢
    exact hOinner ⟨hα, ⟨g, rfl⟩⟩
  · refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ (inn_isPGroup hRS)
    · intro α hα
      obtain ⟨r, hr, rfl⟩ := mem_inn.1 hα
      exact hconjP r (hRN hr)
    · intro α hα
      obtain ⟨g, k, -, rfl⟩ := exists_eq_conj_mul_fieldAut_pow hK hn α
      have hgH := mem_normalizer_of_conj_mul_fieldAut_pow hHC hH hα.2
      exact mul_mem ((conj_mem_normalizer_inn_iff hRC).2 (hNR ⟨g.2, hgH⟩))
        (fieldAut_pow_mem_normalizer_inn hRC hR k)

theorem eq_zero_of_fix_torusFix {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) {k : ℕ}
    (hk : k < n) {s : Fin Tag.G2.rank → ℤ}
    (hbot : zpowers (fieldAut K) ⊓
      centralizer (inn (torusFix K s) : Set (MulAut (adjointGroup .G2 K))) = ⊥)
    (hfix : ∀ h : adjointGroup .G2 K, (h : ModGL .G2 K) ∈ torusFix K s →
      Units.map (entrywiseHom (frobeniusEquiv K 2 ^ k).toRingHom) (h : ModGL .G2 K) = h) :
    k = 0 := by
  have h1 : fieldAut K ^ k ∈ zpowers (fieldAut K) ⊓
      centralizer (inn (torusFix K s) : Set (MulAut (adjointGroup .G2 K))) :=
    ⟨pow_mem (mem_zpowers _) k, mem_centralizer_inn_iff.2 fun x hx =>
      Subtype.ext (by rw [coe_fieldAut_pow_apply]; exact hfix x hx)⟩
  rw [hbot, mem_bot] at h1
  have h2 := (fieldAut_pow_mem_inner_iff hK hn k).1 (h1 ▸ one_mem _)
  exact Nat.eq_zero_of_dvd_of_lt h2 hk

theorem yamada_3_23_1 {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    {B : Subgroup (MulAut (adjointGroup .G2 K))} (hB : inner (adjointGroup .G2 K) ≤ B) :
    CFSG.Open.pCoreOf 2 (B ⊓ normalizer (inn (S K) : Set (MulAut (adjointGroup .G2 K)))) =
        inn (S K) ∧
      CFSG.Open.pCoreOf 2 (B ⊓ normalizer (inn (U K) : Set (MulAut (adjointGroup .G2 K)))) =
        inn (Model.D K) ∧
      CFSG.Open.pCoreOf 2 (B ⊓ normalizer (inn (Y K) : Set (MulAut (adjointGroup .G2 K)))) =
        inn (M K) := by
  obtain ⟨hJ1, -, hJ3, hJ4, -, -⟩ := yamada_3_19_2 hK hn
  have hBS : borelGroup .G2 K ≤ normalizer (S K : Set (ModGL .G2 K)) := by
    rw [← (adjointGroup_inf_normalizer_S (K := K)).1]
    exact inf_le_right
  have hJS : ∀ {s : Fin Tag.G2.rank → ℤ}, torusFix K s ≤ borelGroup .G2 K := fun h =>
    mem_sup_left h.1
  have hentJ : ∀ (k : ℕ) {h : ModGL .G2 K}, h ∈ Model.J K →
      Units.map (entrywiseHom (frobeniusEquiv K 2 ^ k).toRingHom) h ∈ Model.J K :=
    fun k h hh => entrywise_mem_torusGroup hh
  refine ⟨?_, ?_, ?_⟩
  · refine pCoreOf_normalizer_eq hK hn hB (S_le_adjointGroup K) (fun k => map_entrywise_S _)
      le_rfl (fun k => map_entrywise_S _) le_normalizer inf_le_right
      (fun O hOC hp hN => le_S_of_isPGroup hOC hp
        ((le_inf (S_le_adjointGroup K) le_normalizer).trans hN))
      (le_inf (torusFix_le_adjointGroup K g2c) ((hJS).trans hBS)) fun g hgS k hk hfix => ?_
    have hgB : (g : ModGL .G2 K) ∈ borelGroup .G2 K := by
      rw [← (adjointGroup_inf_normalizer_S (K := K)).1]
      exact ⟨g.2, hgS⟩
    refine eq_zero_of_fix_torusFix hK hn hk hJ1 fun h hh => ?_
    have hσh := hentJ k hh.1
    set σh := Units.map (entrywiseHom (frobeniusEquiv K 2 ^ k).toRingHom) (h : ModGL .G2 K)
    have h1 : ⁅(g : ModGL .G2 K), σh⁆ ∈ S K :=
      commutator_borelGroup_le (commutator_mem_commutator hgB (mem_sup_left hσh))
    have h2 := hfix h hh
    have h3 : σh * (h : ModGL .G2 K)⁻¹ ∈ S K ⊓ Model.J K := by
      refine mem_inf.2 ⟨?_, mul_mem hσh (inv_mem hh.1)⟩
      have := mul_mem (inv_mem h1) h2
      rwa [commutatorElement_def, show ((g : ModGL .G2 K) * σh * (g : ModGL .G2 K)⁻¹ * σh⁻¹)⁻¹ *
        ((g : ModGL .G2 K) * σh * (g : ModGL .G2 K)⁻¹ * (h : ModGL .G2 K)⁻¹) =
          σh * (h : ModGL .G2 K)⁻¹ by group] at this
    rw [S_inf_J, mem_bot, mul_inv_eq_one] at h3
    exact h3
  · have hUN : adjointGroup .G2 K ⊓ normalizer (U K : Set (ModGL .G2 K)) =
        adjointGroup .G2 K ⊓ normalizer (Model.D K : Set (ModGL .G2 K)) :=
      (yamada_3_13_2 (K := K)).1.trans (yamada_3_13_2 (K := K)).2.1.symm
    have hSU : S K ≤ normalizer (U K : Set (ModGL .G2 K)) := fun x hx =>
      borelGroup_le_normalizer_U (mem_sup_right hx)
    have hwa : wa K ∈ adjointGroup .G2 K ⊓ normalizer (U K : Set (ModGL .G2 K)) := by
      rw [(yamada_3_13_2 (K := K)).1]
      exact mem_sup_right (mem_sup_left (weylElt_mem_g2RankOne g2ir 1))
    refine pCoreOf_normalizer_eq hK hn hB (U_le_adjointGroup K) (fun k => map_entrywise_U _)
      D_le_S (fun k => map_entrywise_D _) (D_le_S.trans hSU) (hUN ▸ inf_le_right)
      (fun O hOC hp hN => le_D_of_isPGroup hOC hp ((le_inf (S_le_adjointGroup K) hSU).trans hN)
        (hN hwa))
      (le_inf (torusFix_le_adjointGroup K g2r) (hJS.trans borelGroup_le_normalizer_U))
      fun g hgU k hk hfix => ?_
    have hgD : (g : ModGL .G2 K) ∈ Model.D K ⊔ (leviA K ⊔ J₃ K) := by
      rw [← (yamada_3_13_2 (K := K)).1]
      exact ⟨g.2, hgU⟩
    have hJ3D : J₃ K ≤ normalizer (Model.D K : Set (ModGL .G2 K)) := fun j hj =>
      borelGroup_le_normalizer_D (mem_sup_left hj.1)
    have hJ3A : J₃ K ≤ normalizer (leviA K : Set (ModGL .G2 K)) := fun j hj =>
      centralizer_le_normalizer (leviA K) (J₃_le_centralizer_leviA hj)
    obtain ⟨d, hd, a, ha, hga⟩ := Common.exists_mul_of_le_normalizer
      (sup_le g2RankOne_r_le_normalizer hJ3D) _ hgD
    obtain ⟨l, hl, j, hj, rfl⟩ := Common.exists_mul_of_le_normalizer hJ3A a ha
    refine eq_zero_of_fix_torusFix hK hn hk hJ3 fun h hh => ?_
    have hσh := units_map_entrywise_mem_torusFix (frobeniusEquiv K 2 ^ k) hh
    set σh := Units.map (entrywiseHom (frobeniusEquiv K 2 ^ k).toRingHom) (h : ModGL .G2 K)
    have h2 := hfix h hh
    rw [hga] at h2
    have hlσ : l * σh = σh * l := mem_centralizer_iff.1 (J₃_le_centralizer_leviA hσh) l hl
    have hjσ : j * σh = σh * j := J_comm hj.1 hσh.1
    have e : d * (l * j) * σh * (d * (l * j))⁻¹ * (h : ModGL .G2 K)⁻¹ =
        d * σh * d⁻¹ * (h : ModGL .G2 K)⁻¹ := by
      calc d * (l * j) * σh * (d * (l * j))⁻¹ * (h : ModGL .G2 K)⁻¹ =
          d * l * (j * σh) * j⁻¹ * l⁻¹ * d⁻¹ * (h : ModGL .G2 K)⁻¹ := by group
        _ = d * (l * σh) * l⁻¹ * d⁻¹ * (h : ModGL .G2 K)⁻¹ := by rw [hjσ]; group
        _ = d * σh * d⁻¹ * (h : ModGL .G2 K)⁻¹ := by rw [hlσ]; group
    rw [e] at h2
    have h3 : σh * d * σh⁻¹ ∈ Model.D K :=
      (mem_normalizer_iff.1 (borelGroup_le_normalizer_D (mem_sup_left hσh.1)) d).1 hd
    have h4 : σh * (h : ModGL .G2 K)⁻¹ ∈ S K ⊓ Model.J K := by
      refine mem_inf.2 ⟨D_le_S ?_, mul_mem hσh.1 (inv_mem hh.1)⟩
      have := mul_mem (mul_mem h3 (inv_mem hd)) h2
      rwa [show σh * d * σh⁻¹ * d⁻¹ * (d * σh * d⁻¹ * (h : ModGL .G2 K)⁻¹) =
        σh * (h : ModGL .G2 K)⁻¹ by group] at this
    rw [S_inf_J, mem_bot, mul_inv_eq_one] at h4
    exact h4
  · have hYN : adjointGroup .G2 K ⊓ normalizer (Y K : Set (ModGL .G2 K)) =
        adjointGroup .G2 K ⊓ normalizer (M K : Set (ModGL .G2 K)) :=
      (yamada_3_13_3 (K := K)).1.trans (yamada_3_13_3 (K := K)).2.2.1.symm
    have hBY := AS81.G2.borelGroup_le_normalizer_g2BCGroup (K := K)
    have hSY : S K ≤ normalizer (Y K : Set (ModGL .G2 K)) := fun x hx =>
      hBY (mem_sup_right hx)
    have hwb : wb K ∈ adjointGroup .G2 K ⊓ normalizer (Y K : Set (ModGL .G2 K)) := by
      rw [(yamada_3_13_3 (K := K)).1]
      exact mem_sup_right (mem_sup_left (weylElt_mem_g2RankOne g2ia 1))
    refine pCoreOf_normalizer_eq hK hn hB Y_le_adjointGroup (fun k => map_entrywise_Y _)
      M_le_S (fun k => map_entrywise_M _) (M_le_S.trans hSY) (hYN ▸ inf_le_right)
      (fun O hOC hp hN => le_M_of_isPGroup hOC hp ((le_inf (S_le_adjointGroup K) hSY).trans hN)
        (hN hwb))
      (le_inf (torusFix_le_adjointGroup K g2a) (hJS.trans hBY)) fun g hgY k hk hfix => ?_
    have hgM : (g : ModGL .G2 K) ∈ M K ⊔ (leviB K ⊔ J₄ K) := by
      rw [← (yamada_3_13_3 (K := K)).1]
      exact ⟨g.2, hgY⟩
    have hJ4M : J₄ K ≤ normalizer (M K : Set (ModGL .G2 K)) := fun j hj =>
      borelGroup_le_normalizer_M (mem_sup_left hj.1)
    have hJ4B : J₄ K ≤ normalizer (leviB K : Set (ModGL .G2 K)) := fun j hj =>
      centralizer_le_normalizer (leviB K) (J₄_le_centralizer_leviB hj)
    obtain ⟨m, hm, a, ha, hga⟩ := Common.exists_mul_of_le_normalizer
      (sup_le leviB_le_normalizer_M hJ4M) _ hgM
    obtain ⟨l, hl, j, hj, rfl⟩ := Common.exists_mul_of_le_normalizer hJ4B a ha
    refine eq_zero_of_fix_torusFix hK hn hk hJ4 fun h hh => ?_
    have hσh := units_map_entrywise_mem_torusFix (frobeniusEquiv K 2 ^ k) hh
    set σh := Units.map (entrywiseHom (frobeniusEquiv K 2 ^ k).toRingHom) (h : ModGL .G2 K)
    have h2 := hfix h hh
    rw [hga] at h2
    have hlσ : l * σh = σh * l := mem_centralizer_iff.1 (J₄_le_centralizer_leviB hσh) l hl
    have hjσ : j * σh = σh * j := J_comm hj.1 hσh.1
    have e : m * (l * j) * σh * (m * (l * j))⁻¹ * (h : ModGL .G2 K)⁻¹ =
        m * σh * m⁻¹ * (h : ModGL .G2 K)⁻¹ := by
      calc m * (l * j) * σh * (m * (l * j))⁻¹ * (h : ModGL .G2 K)⁻¹ =
          m * l * (j * σh) * j⁻¹ * l⁻¹ * m⁻¹ * (h : ModGL .G2 K)⁻¹ := by group
        _ = m * (l * σh) * l⁻¹ * m⁻¹ * (h : ModGL .G2 K)⁻¹ := by rw [hjσ]; group
        _ = m * σh * m⁻¹ * (h : ModGL .G2 K)⁻¹ := by rw [hlσ]; group
    rw [e] at h2
    have h3 : σh * m * σh⁻¹ ∈ M K :=
      (mem_normalizer_iff.1 (borelGroup_le_normalizer_M (mem_sup_left hσh.1)) m).1 hm
    have h4 : σh * (h : ModGL .G2 K)⁻¹ ∈ S K ⊓ Model.J K := by
      refine mem_inf.2 ⟨M_le_S ?_, mul_mem hσh.1 (inv_mem hh.1)⟩
      have := mul_mem (mul_mem h3 (inv_mem hm)) h2
      rwa [show σh * m * σh⁻¹ * m⁻¹ * (m * σh * m⁻¹ * (h : ModGL .G2 K)⁻¹) =
        σh * (h : ModGL .G2 K)⁻¹ by group] at this
    rw [S_inf_J, mem_bot, mul_inv_eq_one] at h4
    exact h4

end Core

end Model

namespace G2Data

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K)

theorem act_mem_inn_iff {H : Subgroup (ModGL .G2 K)} {x : G} (hx : x ∈ normalizer (L : Set G)) :
    d.act ⟨x, hx⟩ ∈ Model.inn H ↔ x ∈ d.image H ⊔ centralizer (L : Set G) := by
  constructor
  · intro h
    obtain ⟨g, hg, hge⟩ := Model.mem_inn.1 h
    have h1 : d.act (⟨d.emb g, le_normalizer (d.emb_mem g)⟩⁻¹ * ⟨x, hx⟩) = 1 := by
      rw [map_mul, map_inv, act_emb, hge, inv_mul_cancel]
    have h2 := (d.act_eq_one_iff _).1 h1
    rw [coe_mul, coe_inv] at h2
    rw [show x = d.emb g * ((d.emb g)⁻¹ * x) by group]
    exact mul_mem_sup (d.emb_mem_image hg) h2
  · intro hxs
    set T : Subgroup G := ((Model.inn H).comap d.act).map (normalizer (L : Set G)).subtype
      with hT
    have hHT : d.image H ≤ T := by
      intro y hy
      obtain ⟨g, hg, rfl⟩ := d.mem_image.1 hy
      refine ⟨⟨d.emb g, le_normalizer (d.emb_mem g)⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_comap, act_emb]
      exact Model.conj_mem_inn hg
    have hCT : centralizer (L : Set G) ≤ T := by
      intro c hc
      refine ⟨⟨c, centralizer_le_normalizer L hc⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_comap, (d.act_eq_one_iff _).2 hc]
      exact one_mem _
    obtain ⟨y, hy, hyx⟩ := sup_le hHT hCT hxs
    have hyx' : y = ⟨x, hx⟩ := Subtype.ext hyx
    rw [← hyx']
    exact hy

variable
  [Finite K]

theorem act_mem_sectionCentralizer_iff {H₁ H₂ : Subgroup (ModGL .G2 K)} (h : H₂ ≤ H₁)
    {x : G} (hx : x ∈ normalizer (L : Set G)) :
    d.act ⟨x, hx⟩ ∈ sectionCentralizer (Model.inn H₁) (Model.inn H₂) ↔
      ∀ y ∈ d.image H₁, y⁻¹ * (x * y * x⁻¹) ∈ d.image H₂ := by
  rw [Model.mem_sectionCentralizer_inn_iff h]
  constructor
  · intro hα y hy
    obtain ⟨g, hg, rfl⟩ := d.mem_image.1 hy
    have := d.emb_mem_image (hα g hg)
    rwa [map_mul, map_inv, d.emb_act_apply] at this
  · intro hα g hg
    have := hα _ (d.emb_mem_image hg)
    rw [← map_inv, show x * d.emb g * x⁻¹ = d.emb (d.act ⟨x, hx⟩ g) from
      (d.emb_act_apply ⟨x, hx⟩ g).symm, ← map_mul] at this
    exact d.emb_mem_image_iff.1 this

theorem act_sectionCentralizer_eq {H₁ H₂ R : Subgroup (ModGL .G2 K)} (h : H₂ ≤ H₁)
    (hR : sectionCentralizer (Model.inn H₁) (Model.inn H₂) = Model.inn R) {x : G}
    (hx : x ∈ normalizer (L : Set G)) :
    (∀ y ∈ d.image H₁, y⁻¹ * (x * y * x⁻¹) ∈ d.image H₂) ↔
      x ∈ d.image R ⊔ centralizer (L : Set G) := by
  rw [← d.act_mem_sectionCentralizer_iff h hx, hR, d.act_mem_inn_iff hx]

end G2Data

end CFSG.LocalAnalysis.EvenBN.G2
