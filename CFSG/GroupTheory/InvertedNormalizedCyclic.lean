module

public import Mathlib.GroupTheory.Index
import CFSG.GroupTheory.HyperplaneGeneration
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.GroupTheory

theorem inv_conj_inv_mul_conj {G : Type*} [Group G] {a x : G} (ha : a * a = 1) :
    a * (x⁻¹ * (a * x * a⁻¹)) * a⁻¹ = (x⁻¹ * (a * x * a⁻¹))⁻¹ := by
  have ha' : a⁻¹ = a := mul_eq_one_iff_inv_eq.mp ha
  rw [ha']
  calc
    a * (x⁻¹ * (a * x * a)) * a
        = a * x⁻¹ * a * x * (a * a) := by group
    _ = a * x⁻¹ * a * x := by rw [ha, mul_one]
    _ = (a * x * a)⁻¹ * x := by
      rw [mul_inv_rev, mul_inv_rev, ha']
      group
    _ = (x⁻¹ * (a * x * a))⁻¹ := by group

theorem conj_mul_conj_of_commute {G : Type*} [Group G] {a m x : G}
    (hmx : m * x * m⁻¹ = x) (hma : m * a = a * m) :
    m * (x⁻¹ * (a * x * a⁻¹)) * m⁻¹ = x⁻¹ * (a * x * a⁻¹) := by
  have hmx' : m * x⁻¹ * m⁻¹ = x⁻¹ := by
    calc
      m * x⁻¹ * m⁻¹ = (m * x * m⁻¹)⁻¹ := by group
      _ = x⁻¹ := by rw [hmx]
  have hma' : m * a * m⁻¹ = a := by
    rw [hma]
    group
  calc
    m * (x⁻¹ * (a * x * a⁻¹)) * m⁻¹
        = (m * x⁻¹ * m⁻¹) * (m * a * m⁻¹) * (m * x * m⁻¹) *
            (m * a * m⁻¹)⁻¹ := by group
    _ = x⁻¹ * a * x * a⁻¹ := by rw [hmx', hmx, hma']
    _ = x⁻¹ * (a * x * a⁻¹) := by group

theorem exists_inverted_of_index_two {G : Type*} [Group G] {R L : Subgroup G}
    (hLR : L ≤ Subgroup.normalizer (R : Set G))
    (hLc : ∀ ℓ ∈ L, ∀ m ∈ L, ℓ * m = m * ℓ) (hL2 : ∀ ℓ ∈ L, ℓ * ℓ = 1)
    {B : Subgroup L} (hB : B.index = 2) {a : L} (ha : a ∉ B) {x : G} (hx : x ∈ R)
    (hfix : ∀ m ∈ B, (m : G) * x * (m : G)⁻¹ = x)
    (hax : (a : G) * x * (a : G)⁻¹ ≠ x) :
    ∃ y ∈ R, y ≠ 1 ∧ (a : G) * y * (a : G)⁻¹ = y⁻¹ ∧
      ∀ l : L, (l : G) * y * (l : G)⁻¹ = y ∨
        (l : G) * y * (l : G)⁻¹ = y⁻¹ := by
  classical
  let y : G := x⁻¹ * ((a : G) * x * (a : G)⁻¹)
  have ha2 : (a : G) * (a : G) = 1 := hL2 (a : G) a.2
  have hconj : (a : G) * x * (a : G)⁻¹ ∈ R :=
    (Subgroup.mem_normalizer_iff.mp (hLR a.2) x).1 hx
  have hyR : y ∈ R := R.mul_mem (R.inv_mem hx) hconj
  have hyne : y ≠ 1 := by
    intro hy1
    apply hax
    have hxy : x * y = (a : G) * x * (a : G)⁻¹ := by
      dsimp [y]
      group
    rw [hy1, mul_one] at hxy
    exact hxy.symm
  refine ⟨y, hyR, hyne, inv_conj_inv_mul_conj ha2, ?_⟩
  intro l
  by_cases hlB : l ∈ B
  · left
    exact conj_mul_conj_of_commute (hfix l hlB) (hLc (l : G) l.2 (a : G) a.2)
  · right
    have hlaB : l * a ∈ B := by
      rw [Subgroup.mul_mem_iff_of_index_two hB]
      exact iff_of_false hlB ha
    let m : L := l * a
    have hfixm : (m : G) * x * (m : G)⁻¹ = x := hfix m hlaB
    have hcomm : (m : G) * (a : G) = (a : G) * (m : G) :=
      hLc (m : G) m.2 (a : G) a.2
    have hym : (m : G) * y * (m : G)⁻¹ = y :=
      conj_mul_conj_of_commute hfixm hcomm
    have hlma : (l : G) = (m : G) * (a : G) := by
      dsimp [m]
      rw [mul_assoc, ha2, mul_one]
    calc
      (l : G) * y * (l : G)⁻¹
          = (m : G) * (a : G) * y * ((m : G) * (a : G))⁻¹ := by rw [hlma]
      _ = (m : G) * ((a : G) * y * (a : G)⁻¹) * (m : G)⁻¹ := by group
      _ = (m : G) * y⁻¹ * (m : G)⁻¹ := by rw [inv_conj_inv_mul_conj ha2]
      _ = ((m : G) * y * (m : G)⁻¹)⁻¹ := by group
      _ = y⁻¹ := by rw [hym]

theorem exists_inverted_of_conj_ne {G : Type*} [Group G] [Finite G] {R L : Subgroup G}
    (hR : Odd (Nat.card R)) (hLR : L ≤ Subgroup.normalizer (R : Set G))
    (hLc : ∀ ℓ ∈ L, ∀ m ∈ L, ℓ * m = m * ℓ) (hL2 : ∀ ℓ ∈ L, ℓ * ℓ = 1)
    {α x : G} (hα : α ∈ L) (hx : x ∈ R) (hαx : α * x * α⁻¹ ≠ x) :
    ∃ y ∈ R, y ≠ 1 ∧ α * y * α⁻¹ = y⁻¹ ∧
      ∀ ℓ ∈ L, ℓ * y * ℓ⁻¹ = y ∨ ℓ * y * ℓ⁻¹ = y⁻¹ := by
  classical
  haveI : Fact (L ≤ Subgroup.normalizer (R : Set G)) := ⟨hLR⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let a : ↥L := ⟨α, hα⟩
  have ha1 : a ≠ 1 := by
    intro h
    apply hαx
    have hα1 : α = 1 := by simpa [a] using congrArg Subtype.val h
    rw [hα1]
    group
  haveI : Nontrivial ↥L := ⟨a, 1, ha1⟩
  haveI : IsMulCommutative ↥L :=
    IsMulCommutative.of_comm fun l m => Subtype.ext (hLc l l.2 m m.2)
  haveI : IsElementaryAbelian 2 ↥L := by
    refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_of_forall_pow_eq_one ?_
    intro l
    apply Subtype.ext
    simpa [pow_two] using hL2 l l.2
  have hoddR : ¬ 2 ∣ Nat.card ↥R := hR.not_two_dvd_nat
  have hgen : (⨆ (B : Subgroup ↥L) (_ : B.index = 2),
      fixedPointSubgroup B ↥R) = ⊤ :=
    CFSG.SolvableHall.coprime_hyperplane_generation (A := ↥L) (p := 2) (H := ↥R) hoddR
  have hsmul : ∀ (l : ↥L) (r : ↥R),
      ((l • r : ↥R) : G) = (l : G) * (r : G) * (l : G)⁻¹ :=
    fun l r => Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe L R l r
  have hex : ∃ (B : Subgroup ↥L), B.index = 2 ∧ a ∉ B ∧
      ∃ r : ↥R, r ∈ fixedPointSubgroup B ↥R ∧ a • r ≠ r := by
    by_contra hno
    push Not at hno
    have hle : (⨆ (B : Subgroup ↥L) (_ : B.index = 2),
        fixedPointSubgroup B ↥R) ≤ fixedPointSubgroup (Subgroup.zpowers a) ↥R := by
      refine iSup₂_le fun B hB => ?_
      intro r hr
      change ∀ b : ↥B, b • r = r at hr
      rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff]
      by_cases haB : a ∈ B
      · simpa using hr ⟨a, haB⟩
      · exact hno B hB haB r hr
    have hxmem : (⟨x, hx⟩ : ↥R) ∈ (⨆ (B : Subgroup ↥L) (_ : B.index = 2),
        fixedPointSubgroup B ↥R) := by
      rw [hgen]
      exact Subgroup.mem_top _
    have hxC := hle hxmem
    have hfixx : a • (⟨x, hx⟩ : ↥R) = ⟨x, hx⟩ :=
      (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a _).mp hxC
    apply hαx
    calc
      α * x * α⁻¹ = ((a • (⟨x, hx⟩ : ↥R) : ↥R) : G) := by rw [hsmul]
      _ = x := by rw [hfixx]
  obtain ⟨B, hB, haB, r, hrB, hrmoved⟩ := hex
  have hfixB : ∀ m ∈ B, (m : G) * (r : G) * (m : G)⁻¹ = (r : G) := by
    intro m hm
    have h := (FixedPoints.mem_subgroup ↥B ↥R r).mp hrB ⟨m, hm⟩
    rw [← hsmul m r]
    simpa only [Subgroup.smul_def] using congrArg Subtype.val h
  have hmoved : (a : G) * (r : G) * (a : G)⁻¹ ≠ (r : G) := by
    intro h
    apply hrmoved
    apply Subtype.ext
    rw [hsmul a r]
    exact h
  obtain ⟨y, hyR, hyne, hyinv, hyall⟩ :=
    exists_inverted_of_index_two (R := R) (L := L) hLR hLc hL2 hB haB r.2 hfixB hmoved
  refine ⟨y, hyR, hyne, ?_, ?_⟩
  · simpa using hyinv
  · intro ℓ hℓ
    simpa using hyall ⟨ℓ, hℓ⟩

end CFSG.GroupTheory

end
