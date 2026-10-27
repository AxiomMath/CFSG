module

public import CFSG.ClassicalInvolution.RouteD.NonClassicalLocal
public import CFSG.ClassicalInvolution.RouteD.TypeUChain

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD
open scoped MatrixGroups
open Matrix

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem eq_of_mem_of_orderOf_eq_two (h2 : (2 : GaloisField p f) ≠ 0) {L : Subgroup G}
    (hL : classicalInvolutionOddCore L = ⊥) {z : G} (hz : IsClassicalMember p f L z) {y : G}
    (hy : y ∈ L) (hy2 : orderOf y = 2) : y = z := by
  obtain ⟨e⟩ := hz.nonempty_equiv_sl2 hL
  have key : ∀ {y : G} (hy : y ∈ L) (hy2 : orderOf y = 2), e ⟨y, hy⟩ = -1 := by
    intro y hy hy2
    have hyy : y * y = 1 := by
      rw [← pow_two]
      have := pow_orderOf_eq_one y
      rwa [hy2] at this
    have h1 : (⟨y, hy⟩ : ↥L) * ⟨y, hy⟩ = 1 := Subtype.ext hyy
    have h3 : e ⟨y, hy⟩ * e ⟨y, hy⟩ = 1 := by rw [← map_mul, h1, map_one]
    rcases sl2_sq_eq_one h2 h3 with h | h
    · exfalso
      have : (⟨y, hy⟩ : ↥L) = 1 := e.injective (by rw [h, map_one])
      have h4 : y = 1 := congrArg Subtype.val this
      rw [h4, orderOf_one] at hy2
      omega
    · exact h
  have := e.injective ((key hy hy2).trans (key hz.mem hz.orderOf_eq_two).symm)
  exact congrArg Subtype.val this

theorem le_centralizer_pair_mul_iff {z w : G} {L : Subgroup G}
    (hz : L ≤ Subgroup.centralizer ({z} : Set G)) :
    L ≤ Subgroup.centralizer ({z * w} : Set G) ↔ L ≤ Subgroup.centralizer ({w} : Set G) := by
  constructor
  · intro h n hn
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (h hn)
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp (hz hn)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h3 : z * (n * w) = z * (w * n) := by
      calc z * (n * w) = (z * n) * w := by rw [mul_assoc]
        _ = (n * z) * w := by rw [h2]
        _ = n * (z * w) := by rw [mul_assoc]
        _ = (z * w) * n := h1
        _ = z * (w * n) := by rw [mul_assoc]
    exact mul_left_cancel h3
  · intro h n hn
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (h hn)
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp (hz hn)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc n * (z * w) = (n * z) * w := by rw [mul_assoc]
      _ = (z * n) * w := by rw [h2]
      _ = z * (n * w) := by rw [mul_assoc]
      _ = z * (w * n) := by rw [h1]
      _ = (z * w) * n := by rw [mul_assoc]

theorem centralizingMembers_mul_iff {Ω : Set (Subgroup G)} {z w : G} {L : Subgroup G} :
    L ∈ centralizingMembers Ω {z * w, z} ↔ L ∈ centralizingMembers Ω {z, w} := by
  rw [mem_centralizingMembers_pair, mem_centralizingMembers_pair]
  constructor
  · rintro ⟨⟨hL, h1⟩, h2⟩
    exact ⟨⟨hL, h2⟩, (le_centralizer_pair_mul_iff h2).mp h1⟩
  · rintro ⟨⟨hL, h1⟩, h2⟩
    exact ⟨⟨hL, (le_centralizer_pair_mul_iff h1).mpr h2⟩, h1⟩

theorem blockMat_four_neg_mul {F : Type*} [Field F] :
    blockMat (F := F) 4 0 (-1 : Matrix (Fin 2) (Fin 2) F) *
      blockMat 4 2 (-1 : Matrix (Fin 2) (Fin 2) F) = -1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, blockMat_apply, Matrix.one_apply]

theorem UCtx.partner_le_centralizer_mul {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G} {m : ℕ}
    (c : UCtx p f m Ω K z) (nd : UNodes c) {a : ℕ} (ha : a < m) {β : Subgroup G} (hβΩ : β ∈ Ω)
    (hpK : ∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W K β)
    (hphan : ∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W β (nd.j a)) :
    β ≤ Subgroup.centralizer ({z * nd.w a} : Set G) := by
  classical
  have h2 : (2 : GaloisField p (2 * f)) ≠ 0 := c.h2
  have h2' : (2 : GaloisField p f) ≠ 0 := two_ne_zero_of_charP_ne_two c.hp2
  let U : Fin (1 + 2) → Subgroup G := ![K, β, nd.j a]
  have hUΩ : ∀ i, U i ∈ Ω := by
    intro i
    fin_cases i
    · exact c.hK
    · exact hβΩ
    · exact (nd.mem a ha).1
  have hcomm : ∀ i j : Fin (1 + 2), (i : ℕ) + 1 < j → Commutes (U i) (U j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    exact nd.commK a ha
  have hpair : ∀ i j : Fin (1 + 2), (j : ℕ) = i + 1 → ∃ W : Subgroup G,
      UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W (U i) (U j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · exact hpK
    · exact hphan
  obtain ⟨ψ, hker, -, hblk⟩ := exists_psi_of_chainU c.hq (m := 1) (by norm_num) (U := U)
    (fun i => nonempty_su_two_equiv_of_member c.hq c.hΩ c.hex (hUΩ i)) hcomm hpair
  set N : Su (GaloisField p (2 * f)) p f 2 := negOneSU (GaloisField p (2 * f)) p f with hN
  set a₀ : Su (GaloisField p (2 * f)) p f (3 + 1) :=
    blockEmb2 (GaloisField p (2 * f)) p f 3 0 N with ha₀
  set a₂ : Su (GaloisField p (2 * f)) p f (3 + 1) :=
    blockEmb2 (GaloisField p (2 * f)) p f 3 2 N with ha₂
  have hψa₀ : ψ a₀ ∈ K := by
    have : ψ a₀ ∈ U 0 := hblk 0 ▸ ⟨a₀, ⟨N, rfl⟩, rfl⟩
    exact this
  have hψa₂ : ψ a₂ ∈ nd.j a := by
    have : ψ a₂ ∈ U 2 := hblk 2 ▸ ⟨a₂, ⟨N, rfl⟩, rfl⟩
    exact this
  have hn3 : 3 ≤ 3 + 1 := by norm_num
  have hs0 : suMat a₀ = blockMat 4 0 (-1 : Matrix (Fin 2) (Fin 2) (GaloisField p (2 * f))) := by
    show blockMat 4 0 (suMat N) = _
    rw [hN, suMat_negOneSU]
  have hs2 : suMat a₂ = blockMat 4 2 (-1 : Matrix (Fin 2) (Fin 2) (GaloisField p (2 * f))) := by
    show blockMat 4 2 (suMat N) = _
    rw [hN, suMat_negOneSU]
  have hnc0 : a₀ ∉ Subgroup.center (Su (GaloisField p (2 * f)) p f (3 + 1)) := by
    intro hz
    obtain ⟨cc, hcc⟩ := Transfer.exists_scalar_of_mem_center_su c.card_eq c.hq hn3 hz
    have h00 := congrFun (congrFun hcc 0) 0
    have h22 := congrFun (congrFun hcc 2) 2
    rw [hs0] at h00 h22
    simp [blockMat_apply, Matrix.scalar_apply] at h00 h22
    exact h2 (by linear_combination h22 - h00)
  have hnc2 : a₂ ∉ Subgroup.center (Su (GaloisField p (2 * f)) p f (3 + 1)) := by
    intro hz
    obtain ⟨cc, hcc⟩ := Transfer.exists_scalar_of_mem_center_su c.card_eq c.hq hn3 hz
    have h00 := congrFun (congrFun hcc 0) 0
    have h22 := congrFun (congrFun hcc 2) 2
    rw [hs2] at h00 h22
    simp [blockMat_apply, Matrix.scalar_apply] at h00 h22
    exact h2 (by linear_combination h00 - h22)
  have hsq : ∀ i : Fin 3, blockEmb2 (GaloisField p (2 * f)) p f 3 i N *
      blockEmb2 (GaloisField p (2 * f)) p f 3 i N = 1 := by
    intro i
    rw [← map_mul, hN, negOneSU_mul_self, map_one]
  have hord : ∀ b : Su (GaloisField p (2 * f)) p f (3 + 1), b * b = 1 →
      b ∉ Subgroup.center _ → orderOf (ψ b) = 2 := by
    intro b hb hnz
    refine orderOf_eq_prime ?_ (fun h => hnz (hker (MonoidHom.mem_ker.mpr h)))
    rw [pow_two, ← map_mul, hb, map_one]
  have hz_eq : ψ a₀ = z :=
    eq_of_mem_of_orderOf_eq_two h2' (c.hex K c.hK) c.hz hψa₀ (hord a₀ (hsq 0) hnc0)
  have hw_eq : ψ a₂ = nd.w a :=
    eq_of_mem_of_orderOf_eq_two h2' (c.hex (nd.j a) (nd.mem a ha).1) (nd.isCl a ha) hψa₂
      (hord a₂ (hsq 2) hnc2)
  have hxz : z * nd.w a = ψ (a₀ * a₂) := by rw [map_mul, hz_eq, hw_eq]
  have hprod : suMat (a₀ * a₂) = -1 := by
    rw [suMat_mul, hs0, hs2]
    exact blockMat_four_neg_mul
  intro y hy
  have hy1 : y ∈ U 1 := hy
  have hy2 : y ∈ (blockEmb2 (GaloisField p (2 * f)) p f 3 1).range.map ψ :=
    (hblk 1).symm ▸ hy1
  obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hy2
  rw [Subgroup.mem_centralizer_singleton_iff, hxz, ← map_mul, ← map_mul]
  have hcomm : blockEmb2 (GaloisField p (2 * f)) p f 3 1 A * (a₀ * a₂) =
      a₀ * a₂ * blockEmb2 (GaloisField p (2 * f)) p f 3 1 A := by
    apply suMat_injective
    have h1 : suMat (blockEmb2 (GaloisField p (2 * f)) p f 3 1 A * (a₀ * a₂)) =
        - suMat (blockEmb2 (GaloisField p (2 * f)) p f 3 1 A) := by
      rw [suMat_mul, hprod, mul_neg, mul_one]
    have h2 : suMat (a₀ * a₂ * blockEmb2 (GaloisField p (2 * f)) p f 3 1 A) =
        - suMat (blockEmb2 (GaloisField p (2 * f)) p f 3 1 A) := by
      rw [suMat_mul, hprod, neg_mul, one_mul]
    rw [h1, h2]
  exact congrArg ψ hcomm

end CFSG.ClassicalInvolution.RouteD.NonClassical
