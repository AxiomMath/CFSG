module

public import CFSG.ClassicalInvolution.Asc77.AscT7DRGrp
public import CFSG.ClassicalInvolution.Asc77.AscT7F2Out

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7G2

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


section Act

open T7F2 T7DR
open scoped commutatorElement

variable {R N : Subgroup G} {a b : G} {n : ℕ}

theorem squaresSub_le_zpowers_sq (c : QuatCoord R a b n) :
    squaresSub R ≤ Subgroup.zpowers (a ^ 2) := by
  rw [squaresSub, Subgroup.closure_le]
  rintro x ⟨r, hr, rfl⟩
  rcases c.cover r hr with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · refine ⟨i, ?_⟩
    simp only
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add]
    congr 1
    push_cast
    ring
  · have h := c.sq_mul i
    rw [h]
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := c.hn; omega⟩
    have e : a ^ (2 ^ (n' + 1)) = (a ^ 2) ^ (2 ^ n') := by rw [← pow_mul, pow_succ']
    rw [e]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

theorem zpow_odd_not_mem_zpowers_sq (c : QuatCoord R a b n) {j : ℤ} (hj : Odd j) :
    a ^ j ∉ Subgroup.zpowers (a ^ 2) := by
  rintro ⟨k, hk⟩
  simp only at hk
  have h1 : a ^ (2 * k) = a ^ j := by
    rw [← hk, zpow_mul]
    norm_cast
  rw [c.zpow_eq_iff] at h1
  have h2 : (2 : ℤ) ∣ 2 * k - j := by
    refine dvd_trans ?_ h1
    exact dvd_pow_self 2 (by omega)
  have h3 : (2 : ℤ) ∣ j := by
    have h4 : (2 : ℤ) ∣ 2 * k := dvd_mul_right 2 k
    have := dvd_sub h4 h2
    simpa using this
  exact (Int.not_even_iff_odd.mpr hj) (even_iff_two_dvd.mpr h3)

theorem exists_comm_not_mem {z : G} (hR : IsQuatSub R) (hz : IsUniqueInvolution R z)
    (hRN : R ≤ N) (hN2 : IsPGroup 2 N) (hNR : ∀ y ∈ N, conjSub y R = R)
    (hF : ∀ y ∈ N, ¬ IsFAut R y) {m : G} (hm : m ∈ N)
    (hmn : m ∉ R ⊔ (N ⊓ Subgroup.centralizer (R : Set G))) :
    ∃ r ∈ R, ⁅m, r⁆ ∉ squaresSub R := by
  obtain ⟨a, b, n, c, hinv⟩ := exists_coord hR hz hN2 hNR
  have s : Out.Setting R N a b n := ⟨c, hRN, hNR, hinv⟩
  have hH := Out.Hsub_le_sup s hF hN2
  obtain ⟨i, j, hi, hia, hjb⟩ := s.coord_of_mem hm
  have hjodd : Odd j := by
    by_contra hev
    rw [Int.not_odd_iff_even] at hev
    exact hmn (hH ((Out.mem_Hsub s).mpr ⟨hm, j, hev, hjb⟩))
  refine ⟨b, c.hb, fun hmem => ?_⟩
  have hcomm : ⁅m, b⁆ = a ^ (-j) := by
    rw [commutatorElement_def, hjb]
    calc b * a ^ j * b⁻¹ = a ^ (-j) := c.conj_zpow j
      _ = a ^ (-j) := rfl
  rw [hcomm] at hmem
  exact zpow_odd_not_mem_zpowers_sq c (j := -j) (by simpa using hjodd.neg) 
    (squaresSub_le_zpowers_sq c hmem)

theorem squaresSub_conj_mem {R R' : Subgroup G} {g : G} (hg : ∀ r ∈ R, g * r * g⁻¹ ∈ R') {x : G}
    (hx : x ∈ squaresSub R) : g * x * g⁻¹ ∈ squaresSub R' := by
  have hle : squaresSub R ≤ (squaresSub R').comap (MulAut.conj g).toMonoidHom := by
    rw [squaresSub, Subgroup.closure_le]
    rintro y ⟨r, hr, rfl⟩
    show g * (r * r) * g⁻¹ ∈ squaresSub R'
    have e : g * (r * r) * g⁻¹ = (g * r * g⁻¹) * (g * r * g⁻¹) := by group
    rw [e]
    exact square_mem_squaresSub (hg r hr)
  exact hle hx

theorem not_isFAut_of_card_eight {R : Subgroup G} (hR2 : IsPGroup 2 R) (h8 : Nat.card ↥R = 8)
    (a : G) : ¬ IsFAut R a := by
  rintro ⟨-, -, Q, R₁, -, hQ, hR₁, hcard⟩
  have hR₁eq : R₁ = R := (hR₁.2.2 R le_rfl hR2 hR₁.1).symm
  have h8Q := hQ.eight_le
  rw [hR₁eq, h8] at hcard
  omega

theorem commutator_mem_squaresSub {R : Subgroup G} {x y : G} (hx : x ∈ R) (hy : y ∈ R) :
    ⁅x, y⁆ ∈ squaresSub R := by
  have e : ⁅x, y⁆ = (x * x) * ((x⁻¹ * y) * (x⁻¹ * y)) * (y⁻¹ * y⁻¹)⁻¹⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (square_mem_squaresSub hx)
    (square_mem_squaresSub (R.mul_mem (R.inv_mem hx) hy))) ?_
  rw [inv_inv]
  exact square_mem_squaresSub (R.inv_mem hy)

end Act

end T7G2

end CFSG.ClassicalInvolution.Asc77
