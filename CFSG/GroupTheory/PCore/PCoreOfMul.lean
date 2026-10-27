module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.GroupTheory

open CFSG.Open

variable {G : Type*} [Group G] {p : ℕ}

theorem commutator_mem_pCoreOf_of_mem_mul {L : Subgroup G} {y c : G}
    (hy : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf p L)
    (hyO : y ∈ Subgroup.normalizer (pCoreOf p L : Set G))
    (hn : c⁻¹ * y ∈ pCoreOf p L) :
    ∀ l ∈ L, c * l * c⁻¹ * l⁻¹ ∈ pCoreOf p L := by
  intro l hl
  have hQL : pCoreOf p L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le p L
  set n : G := c⁻¹ * y with hn_def
  have hce : c = y * n⁻¹ := by rw [hn_def]; group
  have hm : n⁻¹ ∈ pCoreOf p L := (pCoreOf p L).inv_mem hn
  have hmL : n⁻¹ ∈ L := hQL hm
  have hconj : l * (n⁻¹)⁻¹ * l⁻¹ ∈ pCoreOf p L := by
    have hnorm : l ∈ Subgroup.normalizer (pCoreOf p L : Set G) :=
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf p L) hl
    exact (Subgroup.mem_normalizer_iff.mp hnorm (n⁻¹)⁻¹).mp ((pCoreOf p L).inv_mem hm)
  have hmconj : n⁻¹ * l * (n⁻¹)⁻¹ * l⁻¹ ∈ pCoreOf p L := by
    rw [show n⁻¹ * l * (n⁻¹)⁻¹ * l⁻¹ = n⁻¹ * (l * (n⁻¹)⁻¹ * l⁻¹) by group]
    exact (pCoreOf p L).mul_mem hm hconj
  have h1 : y * (n⁻¹ * l * (n⁻¹)⁻¹ * l⁻¹) * y⁻¹ ∈ pCoreOf p L :=
    (Subgroup.mem_normalizer_iff.mp hyO _).mp hmconj
  have h2 : y * l * y⁻¹ * l⁻¹ ∈ pCoreOf p L := hy l hl
  have heq : c * l * c⁻¹ * l⁻¹ =
      (y * (n⁻¹ * l * (n⁻¹)⁻¹ * l⁻¹) * y⁻¹) * (y * l * y⁻¹ * l⁻¹) := by
    rw [hce]
    group
  rw [heq]
  exact (pCoreOf p L).mul_mem h1 h2

theorem pow_mem_pCoreOf_of_mem_mul {L : Subgroup G} {y c : G} {q : ℕ}
    (hq : y ^ q = 1) (hn : c⁻¹ * y ∈ pCoreOf p L)
    (hc : c ∈ Subgroup.normalizer (pCoreOf p L : Set G))
    (hy : y ∈ Subgroup.normalizer (pCoreOf p L : Set G)) :
    c ^ q ∈ pCoreOf p L := by
  classical
  let M : Subgroup G := Subgroup.normalizer (pCoreOf p L)
  let O : Subgroup ↥M := (pCoreOf p L).subgroupOf M
  haveI : O.Normal := (Subgroup.normal_subgroupOf_iff
    (Subgroup.le_normalizer (H := pCoreOf p L))).mpr
    (fun h k hh hk => (Subgroup.mem_normalizer_iff.mp hk h).mp hh)
  let cM : ↥M := ⟨c, hc⟩
  let yM : ↥M := ⟨y, hy⟩
  have hmemO : cM⁻¹ * yM ∈ O := by
    change (⟨c, hc⟩ : ↥M)⁻¹ * (⟨y, hy⟩ : ↥M) ∈ O
    rw [Subgroup.mem_subgroupOf]
    simpa using hn
  have hmk : QuotientGroup.mk' O cM = QuotientGroup.mk' O yM := by
    have h1 : (QuotientGroup.mk' O cM)⁻¹ * QuotientGroup.mk' O yM = 1 := by
      rw [← map_inv, ← map_mul]
      exact (QuotientGroup.eq_one_iff _).mpr hmemO
    calc QuotientGroup.mk' O cM
        = QuotientGroup.mk' O cM * ((QuotientGroup.mk' O cM)⁻¹ *
            QuotientGroup.mk' O yM) := by rw [h1, mul_one]
      _ = QuotientGroup.mk' O yM := by group
  have hpow : QuotientGroup.mk' O (⟨c ^ q, M.pow_mem hc q⟩ : ↥M) = 1 := by
    change QuotientGroup.mk' O (cM ^ q) = 1
    rw [map_pow]
    rw [hmk]
    rw [← map_pow]
    change QuotientGroup.mk' O (yM ^ q) = 1
    rw [show yM ^ q = (⟨y ^ q, M.pow_mem hy q⟩ : ↥M) from rfl]
    have hyq1 : (⟨y ^ q, M.pow_mem hy q⟩ : ↥M) = 1 := Subtype.ext (by simpa using hq)
    rw [hyq1, map_one]
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hpow)

end CFSG.GroupTheory
