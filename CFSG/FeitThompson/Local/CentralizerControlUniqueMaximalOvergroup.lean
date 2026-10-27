module

public import CFSG.FeitThompson.Definitions.UniqueMaximalOvergroup
public import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
import CFSG.FeitThompson.Local.InvariantControlUniqueMaximalOvergroup
import CFSG.FeitThompson.Local.CoprimePlaneGeneratesSolvableGroup
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Local.ElementaryAbelianCubeInvariantPlane

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type*} [Group G] [Finite G] {p d : ℕ} {M B : Subgroup G}

omit [Finite G] in
theorem exists_le_natCard_eq_sq (hp : p.Prime) (hBp : IsPGroup p ↥B)
    (hB : p ^ 2 ≤ Nat.card ↥B) : ∃ E ≤ B, Nat.card ↥E = p ^ 2 := by
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card hp hBp hB
  refine ⟨Subgroup.map B.subtype H, Subgroup.map_subtype_le H, ?_⟩
  rw [Subgroup.card_map_of_injective B.subtype_injective, hH]

theorem le_of_coprime_of_le_normalizer (hp : p.Prime)
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hBe : IsElementaryAbelian p B) (hBcard : Nat.card ↥B = p ^ d) (hd : 2 ≤ d)
    (hcent : ∀ b ∈ B, b ≠ 1 → centralizer ({b} : Set G) ≤ M)
    {K : Subgroup G} (hKp : p.Coprime (Nat.card ↥K)) (hBK : B ≤ normalizer (K : Set G)) :
    K ≤ M := by
  have hpB : p ∣ Nat.card ↥B := by rw [hBcard]; exact dvd_pow_self p (by omega)
  have hpK : ¬ p ∣ Nat.card ↥K := hp.coprime_iff_not_dvd.mp hKp
  have hKne : K ≠ ⊤ := by
    rintro rfl
    exact hpK (by rw [Subgroup.card_top]; exact hpB.trans B.card_subgroup_dvd_card)
  have := hsolv K hKne
  obtain ⟨E, hEB, hEcard⟩ := exists_le_natCard_eq_sq hp hBe.isPGroup
    (hBcard ▸ Nat.pow_le_pow_right hp.one_lt.le hd)
  have hEK : E ≤ normalizer (K : Set G) := hEB.trans hBK
  have hexp : ∀ a : ↥E, a ^ p = 1 := fun a =>
    Subtype.ext (by simpa using hBe.pow_eq_one (hEB a.2))
  have hsup := iSup_autFixedSubgroup_eq_top hp hEcard hexp (conjOnNormalized K hEK) hpK
  have key : Subgroup.map K.subtype (⊤ : Subgroup ↥K) ≤ M := by
    rw [← hsup]
    simp only [Subgroup.map_iSup]
    refine iSup₂_le fun a ha => ?_
    rintro x ⟨y, hy, rfl⟩
    have hcomm : (a : G) * (y : G) * (a : G)⁻¹ = (y : G) := by
      have h := congrArg (fun z : ↥K => (z : G)) (mem_autFixedSubgroup.mp hy)
      rwa [conjOnNormalized_apply_coe] at h
    refine hcent (a : G) (hEB a.2) (by simpa using ha) ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp hcomm).symm
  rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at key

theorem isUniqueMaximalOvergroup_of_centralizer_le [IsSimpleGroup G] (hp : p.Prime)
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hM : IsCoatom M) (hBe : IsElementaryAbelian p B) (hBcard : Nat.card ↥B = p ^ d) (hd : 2 ≤ d)
    (hBM : B ≤ M) (hcent : ∀ b ∈ B, b ≠ 1 → centralizer ({b} : Set G) ≤ M) :
    IsUniqueMaximalOvergroup B M :=
  isUniqueMaximalOvergroup_of_control_le_elementaryAbelian hp hna hodd hsolv hM hBe hBcard hd hBM
    fun _ hKp hBK => le_of_coprime_of_le_normalizer hp hsolv hBe hBcard hd hcent hKp hBK

theorem isUniqueMaximalOvergroup_of_centralizer_le_pi [IsSimpleGroup G] (hp : p.Prime)
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hM : IsCoatom M) (hBiso : Nonempty (↥B ≃* (Fin d → Multiplicative (ZMod p)))) (hd : 2 ≤ d)
    (hBM : B ≤ M) (hcent : ∀ b ∈ B, b ≠ 1 → centralizer ({b} : Set G) ≤ M) :
    IsUniqueMaximalOvergroup B M := by
  have := Fact.mk hp
  obtain ⟨e⟩ := hBiso
  have hBcard : Nat.card ↥B = p ^ d := by rw [Nat.card_congr e.toEquiv]; simp
  exact isUniqueMaximalOvergroup_of_centralizer_le hp hna hodd hsolv hM
    (isElementaryAbelian_of_nonempty_mulEquiv_pi ⟨e⟩) hBcard hd hBM hcent

end

end CFSG.FeitThompson
