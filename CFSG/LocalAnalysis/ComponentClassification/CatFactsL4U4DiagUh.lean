module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUg
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagLe
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUd
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUe

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace DiagU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks StabU ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem not_mem_commutator_CAU (hp2 : p ≠ 2) (hq3 : p ^ f % 4 = 3) (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {l : K} (hl0 : l ≠ 0) {A : GL (Fin 4) K} {z : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    (hz : IsCU h A z) (hAP : (A : Matrix (Fin 4) (Fin 4) K) * P = P * X1 l)
    {J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hJU : ∀ c : K, thU p f K (uU h P hP c) ∈ J') (hJL : ∀ c : K, thU p f K (uL h P hP c) ∈ J')
    (hzJ : z ∈ CAU J') (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) : z ∉ ⁅CAU J', CAU J'⁆ := by
  classical
  have : Finite K := h.finite
  have hzA : z ∈ CAU J' ⊓ InnU p f K h := Subgroup.mem_inf.2 ⟨hzJ, A, hz⟩
  have hnorm : ∀ g ∈ CAU J', ∀ a ∈ CAU J' ⊓ InnU p f K h,
      g * a * g⁻¹ ∈ CAU J' ⊓ InnU p f K h := fun g hg a ha =>
    Subgroup.mem_inf.2 ⟨(mul_mem (mul_mem hg (Subgroup.mem_inf.1 ha).1) (inv_mem hg) :
      g * a * g⁻¹ ∈ CAU J'), (InnU_normal h hp2).conj_mem _ (Subgroup.mem_inf.1 ha).2 g⟩
  have hcent : ∀ g ∈ CAU J', g * z = z * g := by
    intro g hg
    have h1 : (g * z * g⁻¹) ^ 2 = 1 := by rw [conj_pow, hz2, mul_one, mul_inv_cancel]
    rcases eq_one_or_eq_of_sq_AU h hp2 P hP hl0 hz hAP hJU hJL (hnorm g hg z hzA) h1 with
      h2 | h2
    · exfalso
      apply hz1
      have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
      rw [this, h2]
      group
    · calc g * z = g * z * g⁻¹ * g := by group
        _ = z * g := by rw [h2]
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd
    (Nat.card_pos (α := MulAut (StatedProj (StatedSU 4 (p ^ f) K)))).ne'
  have hpow : ∀ a ∈ CAU J' ⊓ InnU p f K h, a ^ m = 1 ∨ a ^ m = z := by
    intro a ha
    have h1 : (a ^ m) ^ (2 ^ k) = 1 := by
      rw [← pow_mul, mul_comm, ← hkm, pow_card_eq_one']
    have h2 := DiagL.sq_eq_one_of_pow_two_pow
      (fun b hb hb4 => sq_eq_one_of_pow_four_AU h hp2 hq3 P hP hJU hJL hb hb4) k _
      (pow_mem ha m) h1
    exact eq_one_or_eq_of_sq_AU h hp2 P hP hl0 hz hAP hJU hJL (pow_mem ha m) h2
  have hidx : ∀ g ∈ CAU J', ∀ k ∈ CAU J', g ∉ CAU J' ⊓ InnU p f K h →
      k ∉ CAU J' ⊓ InnU p f K h → g⁻¹ * k ∈ CAU J' ⊓ InnU p f K h :=
    fun g hg k hk hgA hkA => inv_mul_mem_AU h hp2 P hP hJU hJL hg hk hgA hkA
  have hcA : ∀ g ∈ CAU J', ∀ k ∈ CAU J', ⁅g, k⁆ ∈ CAU J' ⊓ InnU p f K h := fun g hg k hk =>
    Subgroup.mem_inf.2 ⟨(by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hg hk) (inv_mem hg)) (inv_mem hk) : ⁅g, k⁆ ∈ CAU J'),
      commutator_mem_InnU h hp2 g k⟩
  have hzm : z ^ m ≠ 1 := by
    obtain ⟨j, rfl⟩ := hm
    rw [pow_succ, pow_mul, hz2, one_pow, one_mul]
    exact hz1
  exact DiagL.not_mem_commutator_of_pow hnorm
    (fun a ha b hb => mul_comm_of_mem_AU h hp2 P hP hJU hJL ha hb) hcent hpow hidx hcA hzm

end DiagU

namespace AZ

@[expose] noncomputable def actE {H X : Type*} [Group H] [Group X] {L : Subgroup H} [L.Normal]
    (e : ↥L ≃* X) : H →* MulAut X :=
  (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

theorem actE_apply {H X : Type*} [Group H] [Group X] {L : Subgroup H} [L.Normal]
    (e : ↥L ≃* X) (g : H) (x : ↥L) : actE e g (e x) = e (MulAut.conjNormal g x) := by
  change e (MulAut.conjNormal g (e.symm (e x))) = _
  rw [MulEquiv.symm_apply_apply]

theorem eq_one_of_actE_eq_one {H X : Type*} [Group H] [Group X] {L : Subgroup H} [L.Normal]
    (hC : Subgroup.centralizer (L : Set H) = ⊥) (e : ↥L ≃* X) {g : H} (hg : actE e g = 1) :
    g = 1 := by
  have hmem : g ∈ Subgroup.centralizer (L : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun φ : MulAut X => φ (e ⟨x, hx⟩)) hg
    simp only [actE_apply, MulAut.one_apply] at h1
    have h2 := congrArg Subtype.val (e.injective h1)
    rw [MulAut.conjNormal_apply] at h2
    calc x * g = g * x * g⁻¹ * g := by rw [h2]
      _ = g * x := by group
  rw [hC, Subgroup.mem_bot] at hmem
  exact hmem

theorem image_facts {H X : Type*} [Group H] [Group X] {L : Subgroup H} [L.Normal]
    (e : ↥L ≃* X) {J : Subgroup H} (hJL : J ≤ L) :
    (⁅J, J⁆ = J → ⁅(J.subgroupOf L).map e.toMonoidHom, (J.subgroupOf L).map e.toMonoidHom⁆ =
      (J.subgroupOf L).map e.toMonoidHom) ∧
    Nat.card ((J.subgroupOf L).map e.toMonoidHom) = Nat.card J ∧
    ∀ g : H, (∀ j ∈ J, g * j * g⁻¹ = j) →
      ∀ x ∈ (J.subgroupOf L).map e.toMonoidHom, actE e g x = x := by
  refine ⟨fun hJp => ?_, ?_, ?_⟩
  · have hXp : ⁅J.subgroupOf L, J.subgroupOf L⁆ = J.subgroupOf L := by
      apply Subgroup.map_injective L.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hJL, hJp]
    rw [← Subgroup.map_commutator, hXp]
  · rw [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJL).toEquiv]
  · rintro g hg _ ⟨z, hz, rfl⟩
    change actE e g (e z) = e z
    rw [actE_apply]
    congr 1
    exact Subtype.ext (by rw [MulAut.conjNormal_apply]; exact hg _ (Subgroup.mem_subgroupOf.1 hz))

end AZ

namespace DiagU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks StabU ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
  Subgroup
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K]

theorem diag_U4 (h : UnitaryFieldData p f K) {H : Type} [Group H] {L : Subgroup H} [L.Normal]
    (hC : centralizer (L : Set H) = ⊥) (hp2 : p ≠ 2) (hq3 : p ^ f % 4 = 3)
    (e : ↥L ≃* StatedProj (StatedSU 4 (p ^ f) K)) {α β ξ : H} (hαα : α * α = 1) (hα1 : α ≠ 1)
    (hαc : α = ⁅β, ξ⁆) {J₁ : Subgroup H} (hJL : J₁ ≤ L) (hJα : J₁ ≤ centralizer {α})
    (hJp : ⁅J₁, J₁⁆ = J₁) (hcard : (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) ≤ 2 * Nat.card J₁)
    {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) (hsq : s ∣ (p ^ f) ^ 2 + 1) {y : H} (hyJ : y ∈ J₁)
    (hy : orderOf y = s) :
    2 * Nat.card J₁ ≤ (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) ∧
      (β ∈ centralizer (J₁ : Set H) → ξ ∈ centralizer (J₁ : Set H) → False) := by
  classical
  set Φ := AZ.actE e with hΦ
  obtain ⟨A, hA⟩ : Φ α ∈ InnU p f K h := by
    rw [hαc, map_commutatorElement]
    exact commutator_mem_InnU h hp2 _ _
  have hα1' : Φ α ≠ 1 := fun h1 => hα1 (AZ.eq_one_of_actE_eq_one hC e h1)
  have hα2 : Φ α ^ 2 = 1 := by rw [← map_pow, sq, hαα, map_one]
  have hyL : y ∈ L := hJL hyJ
  obtain ⟨hperf, hcJ, hfix⟩ := AZ.image_facts e hJL
  set J' := (J₁.subgroupOf L).map e.toMonoidHom with hJ'
  have hconj : ∀ g : H, g ∈ centralizer (J₁ : Set H) → ∀ j ∈ J₁, g * j * g⁻¹ = j := by
    intro g hg j hj
    have := mem_centralizer_iff.mp hg j hj
    rw [← this]; group
  have hαfix : ∀ j ∈ J₁, α * j * α⁻¹ = j := by
    intro j hj
    have := mem_centralizer_singleton_iff.mp (hJα hj)
    rw [← this]; group
  have hy' : e ⟨y, hyL⟩ ∈ J' := ⟨⟨y, hyL⟩, mem_subgroupOf.2 hyJ, rfl⟩
  have hys : orderOf (e ⟨y, hyL⟩) = s := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy]
  obtain ⟨l, P, hbl, hP, hAP⟩ := exists_hyp_of_diag h hp2 hA hα1' hα2 hs hs2 hsq hys
    (hfix α hαfix _ hy')
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hbl
    exact zero_ne_one (neg_eq_zero.1 hbl.symm).symm
  obtain ⟨hJU, hJL', hle⟩ := eq_of_perfect_diag h hp2 P hP hl0 hA hAP (hfix α hαfix) (hperf hJp)
    (by rw [hcJ]; exact hcard)
  refine ⟨hcJ ▸ hle, fun hβ hξ => ?_⟩
  have hmem : ∀ g ∈ centralizer (J₁ : Set H), Φ g ∈ CAU J' := fun g hg x hx =>
    hfix g (hconj g hg) x hx
  apply not_mem_commutator_CAU h hp2 hq3 P hP hl0 hA hAP hJU hJL' (hfix α hαfix) hα1' hα2
  rw [hαc, map_commutatorElement]
  exact commutator_mem_commutator (hmem β hβ) (hmem ξ hξ)

end DiagU

end CFSG.ComponentClassification.CatFactsL4U4
