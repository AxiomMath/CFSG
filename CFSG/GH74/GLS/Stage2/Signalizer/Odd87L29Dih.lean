module

public import CFSG.GH74.GLS.Stage2.Local.Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore

public section

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

private theorem exists_eq_r_of_mem_zpowers_r_one {k : ℕ} {x : DihedralGroup k}
    (hx : x ∈ zpowers (DihedralGroup.r 1 : DihedralGroup k)) :
    ∃ i : ZMod k, x = DihedralGroup.r i := by
  obtain ⟨n, rfl⟩ := hx
  exact ⟨n, DihedralGroup.r_one_zpow n⟩

private theorem sr_mul_r_mul_inv {k : ℕ} (j i : ZMod k) :
    (DihedralGroup.sr j : DihedralGroup k) * DihedralGroup.r i * (DihedralGroup.sr j)⁻¹ =
      (DihedralGroup.r i)⁻¹ := by
  simp [DihedralGroup.sr_mul_r, DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr,
    DihedralGroup.inv_r]

theorem subgroup_dihedralGroup {k : ℕ} [NeZero k] (Y : Subgroup (DihedralGroup k)) :
    IsCyclic ↥Y ∨ ∃ m : ℕ, 2 ≤ m ∧ Nonempty (↥Y ≃* DihedralGroup m) := by
  classical
  set R : Subgroup (DihedralGroup k) := zpowers (DihedralGroup.r 1) with hR
  have : IsCyclic ↥(Y ⊓ R) := Subgroup.isCyclic_of_le (inf_le_right : Y ⊓ R ≤ R)
  obtain ⟨ρ, hρ⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top (Y ⊓ R)).1 inferInstance
  have hρmem : ρ ∈ Y ⊓ R := hρ ▸ mem_zpowers ρ
  have hρY : ρ ∈ Y := hρmem.1
  have hρR : ρ ∈ R := hρmem.2
  by_cases hYR : Y ≤ R
  · left
    exact (Subgroup.isCyclic_iff_exists_zpowers_eq_top Y).2 ⟨ρ, hρ.trans (inf_eq_left.2 hYR)⟩
  obtain ⟨s, hsY, hsR⟩ := IsConcreteLE.not_le_iff_exists.1 hYR
  obtain ⟨j, rfl⟩ : ∃ j, s = DihedralGroup.sr j := by
    cases s with
    | r i => exact absurd (GorensteinWalter.r_mem_zpowers_r_one i) hsR
    | sr j => exact ⟨j, rfl⟩
  let ρ' : ↥Y := ⟨ρ, hρY⟩
  let σ' : ↥Y := ⟨DihedralGroup.sr j, hsY⟩
  have hgen : (⊤ : Subgroup ↥Y) = zpowers ρ' ⊔ zpowers σ' := by
    refine Eq.symm (eq_top_iff.2 ?_)
    rintro ⟨y, hy⟩ -
    cases y with
    | r i =>
      have h1 : DihedralGroup.r i ∈ zpowers ρ := by
        rw [hρ]; exact ⟨hy, GorensteinWalter.r_mem_zpowers_r_one i⟩
      obtain ⟨n, hn⟩ := h1
      exact Subgroup.mem_sup_left ⟨n, Subtype.ext hn⟩
    | sr i =>
      have h0 : DihedralGroup.sr j * DihedralGroup.sr i ∈ Y := Y.mul_mem hsY hy
      have h1 : DihedralGroup.r (i - j) ∈ zpowers ρ := by
        rw [hρ]
        refine ⟨?_, GorensteinWalter.r_mem_zpowers_r_one _⟩
        simpa [DihedralGroup.sr_mul_sr] using h0
      obtain ⟨n, hn⟩ := h1
      replace hn : ρ ^ n = DihedralGroup.r (i - j) := hn
      have h2 : (⟨DihedralGroup.sr i, hy⟩ : ↥Y) = σ' * ρ' ^ n := by
        refine Subtype.ext ?_
        simp only [Subgroup.coe_mul, Subgroup.coe_zpow, σ', ρ']
        rw [hn, DihedralGroup.sr_mul_r]
        simp
      rw [h2]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (mem_zpowers σ'))
        (Subgroup.mem_sup_left (zpow_mem_zpowers ρ' n))
  have hσ2 : σ' ^ 2 = 1 := Subtype.ext (by simp [σ', pow_two])
  have hrel : σ' * ρ' * σ'⁻¹ = ρ'⁻¹ := by
    obtain ⟨i, hi⟩ := exists_eq_r_of_mem_zpowers_r_one hρR
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, σ', ρ']
    rw [hi]
    exact sr_mul_r_mul_inv j i
  have hσρ : σ' ∉ zpowers ρ' := by
    rintro ⟨n, hn⟩
    have h1 := congrArg Subtype.val hn
    simp only [Subgroup.coe_zpow, σ', ρ'] at h1
    exact GorensteinWalter.sr_not_mem_zpowers_r_one j (h1 ▸ zpow_mem hρR n)
  obtain ⟨e⟩ := GorensteinWalter.dihedral_of_generators_of_not_mem ρ' σ' hgen hσ2 hrel hσρ
  rcases Nat.lt_or_ge (orderOf ρ') 2 with hlt | hge
  · left
    have h1 : orderOf ρ' = 1 := by have := orderOf_pos ρ'; omega
    rw [h1] at e
    exact e.isCyclic.2 (DihedralGroup.isCyclic_iff.2 rfl)
  · right
    exact ⟨orderOf ρ', hge, ⟨e⟩⟩

theorem subgroup_of_dihedral {P : Type} [Group P] (hP : IsDihedral P) (Y : Subgroup P) :
    IsCyclic ↥Y ∨ IsDihedral ↥Y := by
  obtain ⟨m, k, hmk, hk2, ⟨e⟩⟩ := hP
  have : NeZero k := ⟨by omega⟩
  let Y' : Subgroup (DihedralGroup k) := Y.map e.toMonoidHom
  let eY : ↥Y ≃* ↥Y' := Subgroup.equivMapOfInjective Y e.toMonoidHom e.injective
  rcases subgroup_dihedralGroup Y' with h | ⟨n, hn, ⟨f⟩⟩
  · exact Or.inl (eY.isCyclic.2 h)
  · exact Or.inr ⟨2 * n, n, rfl, hn, ⟨eY.trans f⟩⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
