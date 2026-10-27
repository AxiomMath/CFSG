module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IDict
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Conj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec4IActs_mul_cent_iff {L : Subgroup G} {c s : G}
    (hc : c ∈ centralizer (L : Set G))
    (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) (y : ProjOrth Sec4IQ) :
    Sec4IActs e (s * c) y ↔ Sec4IActs e s y := by
  have hcN : c ∈ normalizer (L : Set G) := Subgroup.centralizer_le_normalizer (L : Set G) hc
  have key : ∀ l : ↥L, c * (l : G) * c⁻¹ = (l : G) := by
    intro l
    have hcl : (l : G) * c = c * (l : G) := Subgroup.mem_centralizer_iff.mp hc l l.2
    rw [← hcl]
    group
  have hsc : ∀ l : ↥L, (s * c) * (l : G) * (s * c)⁻¹ = s * (l : G) * s⁻¹ := by
    intro l
    rw [show (s * c) * (l : G) * (s * c)⁻¹ = s * (c * (l : G) * c⁻¹) * s⁻¹ by group,
      key l]
  constructor
  · rintro ⟨hsN, h⟩
    refine ⟨?_, fun l l' hl' => h l l' (by rw [hl', hsc l])⟩
    have hsplit : s = (s * c) * c⁻¹ := by group
    rw [hsplit]
    exact Subgroup.mul_mem _ hsN (Subgroup.inv_mem _ hcN)
  · rintro ⟨hsN, h⟩
    exact ⟨Subgroup.mul_mem _ hsN hcN, fun l l' hl' => h l l' (by rw [hl', hsc l])⟩

theorem sec4F_type_excl [Finite G] {L : Subgroup G} (hL : IsOmega7Group L) {s : G} {r r' : ℕ}
    {α α' : ℤˣ} (hr : r = 2 ∨ r = 4 ∨ r = 6) (hr' : r' = 2 ∨ r' = 4 ∨ r' = 6)
    (h : InducesTypeSome L s 7 1 r α) (h' : InducesTypeSome L s 7 1 r' α') :
    r = r' ∧ α = α' := by
  obtain ⟨e⟩ := sec4I_exists_model hL
  obtain ⟨y, hy, hty⟩ := (sec4I_inducesTypeSome_iff e hr).mp h
  obtain ⟨y', hy', hty'⟩ := (sec4I_inducesTypeSome_iff e hr').mp h'
  have hyy : y = y' := hy.unique hy'
  rw [← hyy] at hty'
  exact eq_of_hasType_seven sec4IQ_nondegenerate sec4IQ_finrank hty hty' hr hr'

theorem sec4F_type_conj_norm [Finite G] {L : Subgroup G} (hL : IsOmega7Group L) {n s : G}
    (hn : n ∈ normalizer (L : Set G)) {r : ℕ} {α : ℤˣ} (hr : r = 2 ∨ r = 4 ∨ r = 6)
    (h : InducesTypeSome L s 7 1 r α) : InducesTypeSome L (n * s * n⁻¹) 7 1 r α := by
  obtain ⟨e⟩ := sec4I_exists_model hL
  obtain ⟨y, hy, hty⟩ := (sec4I_inducesTypeSome_iff e hr).mp h
  obtain ⟨yn, hyn⟩ := exists_sec4IActs e hn
  have hacts : Sec4IActs e (n * s * n⁻¹) (yn * y * yn⁻¹) := (hyn.mul hy).mul hyn.inv
  refine (sec4I_inducesTypeSome_iff e hr).mpr ⟨yn * y * yn⁻¹, hacts, ?_⟩
  have hconj := sec4I_hasType_mulEquiv sec4IQ_nondegenerate sec4IQ_finrank sec4IQ_quadSign
    (MulAut.conj yn) hr hty
  rwa [MulAut.conj_apply] at hconj

theorem sec4F_conjugate_conjugate (L : Subgroup G) (g h : G) :
    CFSG.conjugate (CFSG.conjugate L g) h = CFSG.conjugate L (g * h) := by
  ext x
  simp only [mem_conjugate_iff]
  rw [show g * (h * x * h⁻¹) * g⁻¹ = (g * h) * x * (g * h)⁻¹ by group]

theorem sec4F_type_mul_cent_iff [Finite G] {L : Subgroup G} (hL : IsOmega7Group L) {s c : G}
    (hc : c ∈ centralizer (L : Set G)) {r : ℕ} {α : ℤˣ} (hr : r = 2 ∨ r = 4 ∨ r = 6) :
    InducesTypeSome L (s * c) 7 1 r α ↔ InducesTypeSome L s 7 1 r α := by
  obtain ⟨e⟩ := sec4I_exists_model hL
  rw [sec4I_inducesTypeSome_iff e hr, sec4I_inducesTypeSome_iff e hr]
  constructor
  · rintro ⟨y, hy, hty⟩
    exact ⟨y, (sec4IActs_mul_cent_iff hc e y).mp hy, hty⟩
  · rintro ⟨y, hy, hty⟩
    exact ⟨y, (sec4IActs_mul_cent_iff hc e y).mpr hy, hty⟩

end CFSG.OddStandard.SmallF3.Omega
