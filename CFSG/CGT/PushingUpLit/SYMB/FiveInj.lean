module

public import CFSG.CGT.PushingUpLit.SYMB.FiveUp
public import CFSG.CGT.PushingUpLit.SYMB.FiveY

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T V : Subgroup Γ}
  {φ : ↥G →* Equiv.Perm (Fin 5)} {ψ : ↥V →* ↥(G6.coreMod 5)} {T' : Set (Equiv.Perm (Fin 5))}
  {S : SymSetting G T V 5 φ ψ T'} {V₁ : Subgroup Γ}

omit [Finite Γ] in
theorem V1Iso.fixed_of_comm (hV : V1Iso S V₁) {x c : Γ} (hxG : x ∈ G) (hc : c ∈ V₁)
    (hcx : c * x = x * c) :
    ψ ⟨c, hV.le hc⟩ ∈ Delta5Swaps.Fixed (Subgroup.zpowers (φ ⟨x, hxG⟩)) := by
  rw [Delta5Swaps.Fixed_zpowers]
  have h1 := hV.psi_conj hxG hc
  have h2 : x * c * x⁻¹ = c := by
    rw [← hcx]
    group
  have h3 : ψ ⟨x * c * x⁻¹, S.data.conj_mem hxG (hV.le hc)⟩ = ψ ⟨c, hV.le hc⟩ := by
    congr 1
    exact Subtype.ext h2
  rw [h3] at h1
  exact h1.symm

theorem eq_cent_sup (hV : V1Iso S V₁) {A : Subgroup Γ} (hA : IsMaxElemAbelian T A) {x : Γ}
    (hxA : x ∈ A) (hxG : x ∈ G) {P : Subgroup (Equiv.Perm (Fin 5))}
    (hPc : ∀ p ∈ P, p * φ ⟨x, hxG⟩ = φ ⟨x, hxG⟩ * p)
    (hPA : imgG G φ A ≤ P ⊔ Subgroup.zpowers (φ ⟨x, hxG⟩)) :
    A = (Up φ ψ V₁ A P ⊓ Subgroup.centralizer ({x} : Set Γ)) ⊔ Subgroup.zpowers x := by
  have hAG : A ≤ G := hA.1.trans S.sylow.1
  have hx2 : x * x = 1 := elemAb_sq hA.2.1 hxA
  have hτ : φ ⟨x, hxG⟩ * φ ⟨x, hxG⟩ = 1 := by
    rw [← map_mul]
    have : (⟨x, hxG⟩ : ↥G) * ⟨x, hxG⟩ = 1 := Subtype.ext hx2
    rw [this, map_one]
  set D : Subgroup Γ := A ⊓ preimG G φ P with hD
  have hDU : D ≤ Up φ ψ V₁ A P := le_sup_right
  apply le_antisymm
  · intro a haA
    have haG : a ∈ G := hAG haA
    have hax : a * x = x * a := elemAb_comm hA.2.1 haA hxA
    have hmem : φ ⟨a, haG⟩ ∈ P ⊔ Subgroup.zpowers (φ ⟨x, hxG⟩) :=
      hPA (mem_imgG.2 ⟨a, haG, haA, rfl⟩)
    rcases sup_zpowers_cases hτ hPc hmem with h | h
    · refine Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨hDU ⟨haA, mem_preimG.2 ⟨haG, h⟩⟩,
        Subgroup.mem_centralizer_iff.2 ?_⟩)
      intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      exact hax.symm
    · have haxA : a * x ∈ A := A.mul_mem haA hxA
      have haxG : a * x ∈ G := G.mul_mem haG hxG
      have hφax : φ ⟨a * x, haxG⟩ = φ ⟨a, haG⟩ * φ ⟨x, hxG⟩ := by
        rw [← map_mul]
        rfl
      have hC : a * x ∈ Up φ ψ V₁ A P ⊓ Subgroup.centralizer ({x} : Set Γ) := by
        refine Subgroup.mem_inf.2 ⟨hDU ⟨haxA, mem_preimG.2 ⟨haxG, ?_⟩⟩,
          Subgroup.mem_centralizer_iff.2 ?_⟩
        · rw [hφax]
          exact h
        · intro y hy
          rw [Set.mem_singleton_iff.1 hy]
          calc x * (a * x) = (x * a) * x := by group
            _ = (a * x) * x := by rw [hax]
      have : a = (a * x) * x⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hC)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)))
  · refine sup_le ?_ ((Subgroup.zpowers_le).2 hxA)
    rintro u ⟨hu, hux⟩
    have huxc : u * x = x * u := (Subgroup.mem_centralizer_iff.1 hux x rfl).symm
    have hn : Cfix ψ V₁ P ≤ Subgroup.normalizer (D : Set Γ) :=
      le_normalizer_of_commute fun c hc d hd => hV.comm_Cfix_preimG hc (Subgroup.mem_inf.1 hd).2
    have hu' : u ∈ ((Cfix ψ V₁ P ⊔ D : Subgroup Γ) : Set Γ) := hu
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn] at hu'
    obtain ⟨c, hc, w, hw, rfl⟩ := hu'
    have hwA : w ∈ A := (Subgroup.mem_inf.1 hw).1
    have hwx : w * x = x * w := elemAb_comm hA.2.1 hwA hxA
    have hcx : c * x = x * c := by
      have h1 : c * (w * x) = x * c * w := by
        calc c * (w * x) = (c * w) * x := by group
          _ = x * (c * w) := huxc
          _ = x * c * w := by group
      rw [hwx] at h1
      have h2 : c * x * w = x * c * w := by
        calc c * x * w = c * (x * w) := by group
          _ = x * c * w := h1
      exact mul_right_cancel h2
    have hcV₁ : c ∈ V₁ := Cfix_le P hc
    have hfixP : ψ ⟨c, hV.le hcV₁⟩ ∈ Delta5Swaps.Fixed P := (mem_Cfix.1 hc).2.2
    have hfixτ := hV.fixed_of_comm hxG hcV₁ hcx
    have hfix : ψ ⟨c, hV.le hcV₁⟩ ∈ Delta5Swaps.Fixed (imgG G φ A) := by
      refine Delta5Swaps.Fixed_anti hPA ?_
      rw [Delta5Swaps.Fixed_sup]
      exact ⟨hfixP, hfixτ⟩
    have hcA : c ∈ A := by
      have : c ∈ V₁ ⊓ A := by
        rw [V₁_inf_eq S hV hA]
        exact mem_Cfix.2 ⟨hV.le hcV₁, hcV₁, hfix⟩
      exact this.2
    exact A.mul_mem hcA hwA

theorem eq_of_Up_eq (hV : V1Iso S V₁) {A₁ A₂ : Subgroup Γ} (hA₁ : IsMaxElemAbelian T A₁)
    (hA₂ : IsMaxElemAbelian T A₂) {x : Γ} (hx₁ : x ∈ A₁) (hx₂ : x ∈ A₂) (hxG : x ∈ G)
    {P : Subgroup (Equiv.Perm (Fin 5))} (hPc : ∀ p ∈ P, p * φ ⟨x, hxG⟩ = φ ⟨x, hxG⟩ * p)
    (hP₁ : imgG G φ A₁ ≤ P ⊔ Subgroup.zpowers (φ ⟨x, hxG⟩))
    (hP₂ : imgG G φ A₂ ≤ P ⊔ Subgroup.zpowers (φ ⟨x, hxG⟩))
    (h : Up φ ψ V₁ A₁ P = Up φ ψ V₁ A₂ P) : A₁ = A₂ := by
  rw [eq_cent_sup hV hA₁ hx₁ hxG hPc hP₁, eq_cent_sup hV hA₂ hx₂ hxG hPc hP₂, h]

end CFSG.CGT.PushingUpLit.SYMB
