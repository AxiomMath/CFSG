module

public import CFSG.GH74.GLS.SP.Local.SPLA
public import CFSG.GH74.GLS.SP.Local.SPLCtStage
public import CFSG.GH74.GLS.SP.Local.SPLCtW
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement
open CFSG.GH74.GLS.IVK.Proofs2 (dihedral_central_unique)

section CtT2

variable {G : Type} [Group G] [Finite G] {D : SPLNot1 G} {T T₀ T₁ : Subgroup G} {y : G}

omit [Finite G] in
theorem SPLCtT.t_central (hT : SPLCtT D T T₀ T₁ y) : ∀ c ∈ T, c * D.t = D.t * c := fun _ hc =>
  mem_centralizer_singleton_iff.mp (hT.T_le hc)

omit [Finite G] in
theorem SPLCtT.y_not_mem (hs : SPLSetup D.toSPLNot0) (hT : SPLCtT D T T₀ T₁ y) : y ∉ T₀ ⊔ T₁ := by
  intro hy
  obtain ⟨x₀, hx₀, t₁, ht₁, hyx'⟩ := mem_sup_of_commute hT.T₀_T₁ hy
  have hn3 : 3 ≤ D.n := three_le_n D.toSPLNot0 hs.odd_q hs.q_ge
  have hT₀T : T₀ ≤ T := fun c hc => ((hT.T₀_mem c).mp hc).1
  have hyY : y ∈ T₀ ⊔ zpowers y := Subgroup.mem_sup_right (mem_zpowers y)
  have hYT : T₀ ⊔ zpowers y ≤ T := sup_le hT₀T (zpowers_le.mpr hT.y_mem)
  have ht₁ne : t₁ ≠ 1 := by
    intro h1
    have hyT₀ : y ∈ T₀ := by rw [hyx', h1, mul_one]; exact hx₀
    have hYeq : T₀ ⊔ zpowers y = T₀ := sup_eq_left.mpr (zpowers_le.mpr hyT₀)
    have h1' := CtW.card_of_isDihedralOrder hT.T₀y_dih
    have h2' := CtW.card_of_isDihedralOrder hT.T₀_dih
    rw [hYeq] at h1'
    rw [h1'] at h2'
    have h3 : 2 ^ (D.n - 1) < 2 ^ D.n := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have htne : D.t ≠ 1 := by
    intro h1
    have := hs.syl.t_ord
    rw [h1, orderOf_one] at this
    omega
  have ht₁c : ∀ g ∈ T₀ ⊔ zpowers y, g * t₁ = t₁ * g := by
    have hc : x₀ * t₁ = t₁ * x₀ := hT.T₀_T₁ x₀ hx₀ t₁ ht₁
    have hle : T₀ ⊔ zpowers y ≤ centralizer ({t₁} : Set G) := by
      refine sup_le (fun a ha => mem_centralizer_singleton_iff.mpr (hT.T₀_T₁ a ha t₁ ht₁)) ?_
      rw [zpowers_le]
      refine mem_centralizer_singleton_iff.mpr ?_
      calc y * t₁ = x₀ * t₁ * t₁ := by rw [← hyx']
        _ = t₁ * x₀ * t₁ := by rw [hc]
        _ = t₁ * (x₀ * t₁) := by group
        _ = t₁ * y := by rw [← hyx']
    intro g hg
    exact mem_centralizer_singleton_iff.mp (hle hg)
  have htc : ∀ g ∈ T₀ ⊔ zpowers y, g * D.t = D.t * g := fun g hg => hT.t_central g (hYT hg)
  have htY : D.t ∈ T₀ ⊔ zpowers y := Subgroup.mem_sup_left hT.t_T₀
  have ht₁Y : t₁ ∈ T₀ ⊔ zpowers y := by
    have : t₁ = x₀⁻¹ * y := by rw [hyx']; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hx₀)) hyY
  obtain ⟨k, hk, -, ⟨φ⟩⟩ := hT.T₀y_dih
  have hk3 : 3 ≤ k := by
    have h1 : 2 ^ D.n = 2 * 2 ^ (D.n - 1) := by
      obtain ⟨j, hj⟩ : ∃ j, D.n = j + 1 := ⟨D.n - 1, by omega⟩
      rw [hj, Nat.add_sub_cancel, pow_succ]; ring
    have h2 : 4 ≤ 2 ^ (D.n - 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (D.n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hcen := dihedral_central_unique (P := ↥(T₀ ⊔ zpowers y)) hk3 φ
    (z := ⟨t₁, ht₁Y⟩) (z' := ⟨D.t, htY⟩)
    (fun h => ht₁ne (congrArg Subtype.val h)) (fun h => Subtype.ext (ht₁c h h.2))
    (fun h => htne (congrArg Subtype.val h)) (fun h => Subtype.ext (htc h h.2))
  have ht₁t : t₁ = D.t := congrArg Subtype.val hcen
  have : D.t ∈ T₀ ⊓ T₁ := ⟨hT.t_T₀, ht₁t ▸ ht₁⟩
  rw [hT.T₀_inf_T₁, Subgroup.mem_bot] at this
  exact htne this

end CtT2

end CFSG.GH74.GLS.SP.Local
