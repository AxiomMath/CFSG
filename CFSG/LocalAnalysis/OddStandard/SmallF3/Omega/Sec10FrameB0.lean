module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelB0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Comb

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.ComponentClassification.GSThmB

local notation "P45" => Equiv.Perm (Fin 45)

theorem isEvenVec_add_vec {n : ℕ} {v w : Fin n → ZMod 2} (hv : IsEvenVec v) (hw : IsEvenVec w) :
    IsEvenVec (v + w) := by
  unfold IsEvenVec at *
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, hv, hw, add_zero]

namespace PspFrame

variable {G : Type} [Group G] {L : Subgroup G} (F : PspFrame L) {X : Subgroup G}

theorem comm_img_iff (hX : X ≤ L) :
    (∀ p ∈ F.img X, ∀ q ∈ F.img X, p * q = q * p) ↔ ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
  constructor
  · intro h x hx y hy
    have := h (F.ψ ⟨x, hX hx⟩) ((psi_mem_img (F := F)).2 hx) (F.ψ ⟨y, hX hy⟩)
      ((psi_mem_img (F := F)).2 hy)
    rw [← map_mul, ← map_mul] at this
    exact congrArg Subtype.val (F.ψ_injective this)
  · intro h p hp q hq
    obtain ⟨l, hl, rfl⟩ := mem_img.1 hp
    obtain ⟨l', hl', rfl⟩ := mem_img.1 hq
    rw [← map_mul, ← map_mul]
    exact congrArg F.ψ (Subtype.ext (h _ hl _ hl'))

theorem sq_img_iff (hX : X ≤ L) : (∀ p ∈ F.img X, p * p = 1) ↔ ∀ x ∈ X, x * x = 1 := by
  constructor
  · intro h x hx
    have := h (F.ψ ⟨x, hX hx⟩) ((psi_mem_img (F := F)).2 hx)
    rw [← map_mul, ← map_one F.ψ] at this
    exact congrArg Subtype.val (F.ψ_injective this)
  · intro h p hp
    obtain ⟨l, hl, rfl⟩ := mem_img.1 hp
    rw [← map_mul, ← map_one F.ψ]
    exact congrArg F.ψ (Subtype.ext (h _ hl))

theorem isElemAbelian_img_iff (hX : X ≤ L) :
    CFSG.Open.IsElemAbelian 2 (F.img X) ↔ CFSG.Open.IsElemAbelian 2 X := by
  unfold CFSG.Open.IsElemAbelian
  rw [isMulCommutative_iff_of_setLike, isMulCommutative_iff_of_setLike, F.comm_img_iff hX]
  simp only [pow_two]
  rw [F.sq_img_iff hX]


theorem pre_B0_le {P : Subgroup G} (hP : F.img P = QT0.originalSubgroup) (hPL : P ≤ L) :
    F.pre B0 ≤ P := by
  rw [← img_le_img_iff (F := F) (pre_le B0) hPL, img_pre B0_le_P, hP]
  exact B0_le_T0

theorem card_pre_B0 : Nat.card (F.pre B0) = 2 ^ 4 := by
  rw [← F.card_img (pre_le B0), img_pre B0_le_P, card_B0]

theorem isElemAbelian_pre_B0 : CFSG.Open.IsElemAbelian 2 (F.pre B0) := by
  refine (F.isElemAbelian_img_iff (pre_le B0)).1 ?_
  rw [img_pre B0_le_P]
  exact isElemAbelian_B0

theorem isMaxElemAbelianIn_pre {P : Subgroup G} (hP : F.img P = QT0.originalSubgroup)
    (hPL : P ≤ L) : IsMaxElemAbelianIn P (F.pre B0) := by
  refine ⟨F.pre_B0_le hP hPL, F.isElemAbelian_pre_B0, fun B' hB'P hB' => ?_⟩
  have hB'L : B' ≤ L := hB'P.trans hPL
  have h1 := (F.isElemAbelian_img_iff hB'L).2 hB'
  have h2 : F.img B' ≤ QT0.originalSubgroup := hP ▸ img_mono hB'P
  have h3 := card_le_of_abelian h2 (isMulCommutative_iff_of_setLike.1 h1.1)
  rw [← F.card_img hB'L, F.card_pre_B0]
  exact h3

theorem eq_pre_B0_of_abelian {P A : Subgroup G} (hP : F.img P = QT0.originalSubgroup)
    (hPL : P ≤ L) (hAP : A ≤ P) (hc : IsMulCommutative A) (hcard : Nat.card A = 2 ^ 4) :
    A = F.pre B0 := by
  have hAL : A ≤ L := hAP.trans hPL
  have h1 : F.img A ≤ QT0.originalSubgroup := hP ▸ img_mono hAP
  have h2 : ∀ p ∈ F.img A, ∀ q ∈ F.img A, p * q = q * p :=
    (F.comm_img_iff hAL).2 (isMulCommutative_iff_of_setLike.1 hc)
  have h3 : F.img A = B0 :=
    eq_B0_of_abelian h1 h2 (by rw [F.card_img hAL, hcard])
  rw [← h3, pre_img hAL]

theorem eq_pre_B0_of_isMax {P A : Subgroup G} (hP : F.img P = QT0.originalSubgroup)
    (hPL : P ≤ L) (hA : IsMaxElemAbelianIn P A) : A = F.pre B0 := by
  obtain ⟨hAP, hAE, hmax⟩ := hA
  have hAL : A ≤ L := hAP.trans hPL
  have h1 : F.img A ≤ QT0.originalSubgroup := hP ▸ img_mono hAP
  have hE := (F.isElemAbelian_img_iff hAL).2 hAE
  have hle := card_le_of_abelian h1 (isMulCommutative_iff_of_setLike.1 hE.1)
  rw [F.card_img hAL] at hle
  have hge := hmax (F.pre B0) (F.pre_B0_le hP hPL) F.isElemAbelian_pre_B0
  rw [F.card_pre_B0] at hge
  exact F.eq_pre_B0_of_abelian hP hPL hAP hAE.1 (le_antisymm hle hge)

theorem jElem_eq {P : Subgroup G} (hP : F.img P = QT0.originalSubgroup) (hPL : P ≤ L) :
    JElem P = F.pre B0 := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨A, hA, hx⟩
    rw [F.eq_pre_B0_of_isMax hP hPL hA] at hx
    exact hx
  · intro x hx
    exact Subgroup.subset_closure ⟨F.pre B0, F.isMaxElemAbelianIn_pre hP hPL, hx⟩

theorem centralizer_pre_B0 :
    centralizer (F.pre B0 : Set G) ⊓ L = F.pre B0 := by
  ext x
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hc, hL⟩
    refine mem_pre.2 ⟨hL, centralizer_B0_le (QP45_le_QA45 (F.ψ_mem ⟨x, hL⟩)) fun b hb => ?_⟩
    obtain ⟨l, rfl⟩ := F.ψ_surj (B0_le_P hb)
    have h1 := Subgroup.mem_centralizer_iff.1 hc (l : G) (mem_pre.2 ⟨l.2, hb⟩)
    have h2 : l * ⟨x, hL⟩ = ⟨x, hL⟩ * l := Subtype.ext h1
    rw [← map_mul, ← map_mul, h2]
  · intro hx
    have hL : x ∈ L := pre_le B0 hx
    refine ⟨Subgroup.mem_centralizer_iff.2 fun h hh => ?_, hL⟩
    have hc := (F.comm_img_iff (pre_le B0)).1 (by
      rw [img_pre B0_le_P]
      exact fun p hp q hq => B0_comm hp hq)
    exact hc h hh x hx

theorem exists_phiL : ∃ φ : (Fin 5 → ZMod 2) → ↥L, ∀ v, IsEvenVec v → F.ψ (φ v) = phiB v := by
  have h : ∀ v : Fin 5 → ZMod 2, ∃ l : ↥L, IsEvenVec v → F.ψ l = phiB v := by
    intro v
    by_cases hv : IsEvenVec v
    · obtain ⟨l, hl⟩ := F.ψ_surj (B0_le_P (phiB_mem_B0 hv))
      exact ⟨l, fun _ => hl⟩
    · exact ⟨1, fun h => absurd h hv⟩
  choose φ hφ using h
  exact ⟨φ, hφ⟩

theorem phi_conj_eq (y : ↥(normalizer (L : Set G))) (l l' : ↥L)
    (h : F.φ y * F.ψ l * (F.φ y)⁻¹ = F.ψ l') : (y : G) * (l : G) * (y : G)⁻¹ = (l' : G) := by
  have h1 := F.psi_conjL y l
  rw [h] at h1
  exact congrArg Subtype.val (F.ψ_injective h1)

theorem phi_conj_mem_B0 (y : ↥(normalizer (L : Set G)))
    (hy : (y : G) ∈ normalizer (F.pre B0 : Set G)) {b : P45} (hb : b ∈ B0) :
    F.φ y * b * (F.φ y)⁻¹ ∈ B0 := by
  obtain ⟨l, rfl⟩ := F.ψ_surj (B0_le_P hb)
  have h1 : (y : G) * l * (y : G)⁻¹ ∈ F.pre B0 :=
    (Subgroup.mem_normalizer_iff.1 hy (l : G)).1 (mem_pre.2 ⟨l.2, hb⟩)
  rw [← F.psi_conjL y l]
  exact (mem_pre.1 h1).2

theorem phi_conj_inv_mem_B0 (y : ↥(normalizer (L : Set G)))
    (hy : (y : G) ∈ normalizer (F.pre B0 : Set G)) {b : P45} (hb : b ∈ B0) :
    (F.φ y)⁻¹ * b * F.φ y ∈ B0 := by
  have h1 : ((y⁻¹ : ↥(normalizer (L : Set G))) : G) ∈ normalizer (F.pre B0 : Set G) :=
    Subgroup.inv_mem _ hy
  have h2 := F.phi_conj_mem_B0 y⁻¹ h1 hb
  rwa [map_inv, inv_inv] at h2

theorem conj_phiL {φL : (Fin 5 → ZMod 2) → ↥L} (hφ : ∀ v, IsEvenVec v → F.ψ (φL v) = phiB v)
    (y : ↥(normalizer (L : Set G))) (σ : Equiv.Perm (Fin 5))
    (hact : ∀ v, F.φ y * phiB v * (F.φ y)⁻¹ = phiB (permVec σ v)) {v : Fin 5 → ZMod 2}
    (hv : IsEvenVec v) :
    (y : G) * (φL v : G) * (y : G)⁻¹ = (φL (permVec σ v) : G) := by
  apply F.phi_conj_eq y (φL v) (φL (permVec σ v))
  rw [hφ v hv, hφ (permVec σ v) (isEvenVec_permVec σ hv)]
  exact hact v

end PspFrame

end CFSG.OddStandard.SmallF3.Omega
