module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpSub

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

variable {A : Type} [Group A] {z : A} {p : ℕ} {X J : Subgroup A}

@[expose] def secMk (z : A) (X J : Subgroup A) (y : A) (hy : y ∈ secY z X J) : secB z X J :=
  QuotientGroup.mk ⟨y, hy⟩

theorem secMk_mul {y y' : A} (hy : y ∈ secY z X J) (hy' : y' ∈ secY z X J) :
    secMk z X J (y * y') ((secY z X J).mul_mem hy hy') = secMk z X J y hy * secMk z X J y' hy' := rfl

theorem secMk_inv {y : A} (hy : y ∈ secY z X J) :
    secMk z X J y⁻¹ ((secY z X J).inv_mem hy) = (secMk z X J y hy)⁻¹ := rfl

theorem secMk_one : secMk z X J 1 (secY z X J).one_mem = 1 := rfl

theorem secMk_pow {y : A} (hy : y ∈ secY z X J) (n : ℕ) :
    secMk z X J (y ^ n) ((secY z X J).pow_mem hy n) = (secMk z X J y hy) ^ n := rfl

theorem secMk_congr {y y' : A} (h : y = y') (hy : y ∈ secY z X J) (hy' : y' ∈ secY z X J) :
    secMk z X J y hy = secMk z X J y' hy' := by
  subst h
  rfl

theorem secMk_z : secMk z X J z (z_mem_secY z X J) = secZ z X J := rfl

theorem secMk_eq_iff {y y' : A} (hy : y ∈ secY z X J) (hy' : y' ∈ secY z X J) :
    secMk z X J y hy = secMk z X J y' hy' ↔
      (⟨y, hy⟩ : ↥(secY z X J))⁻¹ * ⟨y', hy'⟩ ∈ pPrimeCore 2 ↥(secY z X J) :=
  QuotientGroup.eq

theorem secMk_eq_one_iff {y : A} (hy : y ∈ secY z X J) :
    secMk z X J y hy = 1 ↔ (⟨y, hy⟩ : ↥(secY z X J)) ∈ pPrimeCore 2 ↥(secY z X J) :=
  QuotientGroup.eq_one_iff _

theorem secMk_surjective (b : secB z X J) : ∃ (y : A) (hy : y ∈ secY z X J), b = secMk z X J y hy := by
  obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨y, hy, rfl⟩

theorem mem_secJ_iff {b : secB z X J} :
    b ∈ secJ z X J ↔ ∃ (j : A) (hj : j ∈ J), b = secMk z X J j (J_le_secY z X J hj) := by
  constructor
  · intro hb
    obtain ⟨⟨y, hy⟩, hyJ, rfl⟩ := Subgroup.mem_map.mp hb
    exact ⟨y, hyJ, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact Subgroup.mem_map.mpr ⟨⟨j, J_le_secY z X J hj⟩, hj, rfl⟩

theorem mem_secX_iff {b : secB z X J} :
    b ∈ secX z X J ↔ ∃ (x : A) (hx : x ∈ X), b = secMk z X J x (X_le_secY z X J hx) := by
  constructor
  · intro hb
    obtain ⟨⟨y, hy⟩, hyX, rfl⟩ := Subgroup.mem_map.mp hb
    exact ⟨y, hyX, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact Subgroup.mem_map.mpr ⟨⟨x, X_le_secY z X J hx⟩, hx, rfl⟩

theorem secMk_mem_secJ {j : A} (hj : j ∈ J) : secMk z X J j (J_le_secY z X J hj) ∈ secJ z X J :=
  mem_secJ_iff.mpr ⟨j, hj, rfl⟩

theorem secMk_mem_secX {x : A} (hx : x ∈ X) : secMk z X J x (X_le_secY z X J hx) ∈ secX z X J :=
  mem_secX_iff.mpr ⟨x, hx, rfl⟩

theorem N_comm_J [Finite A] (h : SubHyp z p X J) {n : ↥(secY z X J)} (hn : n ∈ pPrimeCore 2 ↥(secY z X J))
    {j : A} (hj : j ∈ J) : (n : A) * j = j * (n : A) := by
  have hh := absHyp_of_subHyp h
  have := hh.normal
  have hc := SubAbs.inf_pPrimeCore_le_centralizer' hh.quasi ⊤ ⟨mem_top n, hn⟩
  have := mem_centralizer_iff.mp hc ⟨j, J_le_secY z X J hj⟩ hj
  exact (congrArg Subtype.val this).symm

theorem N_odd [Finite A] : Odd (Nat.card (pPrimeCore 2 ↥(secY z X J))) :=
  SubAbs.pPrimeCore_odd

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
