module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S11Count

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup

section Cover

variable {B : Type} [Group B] [Finite B] {X H : Type} [Group X] [Group H]

theorem card_range_mul_card_le (κ : B →* X) (ρ : B →* H) (F : Subgroup B)
    (hFκ : ∀ f ∈ F, κ f = 1) (hFρ : ∀ f ∈ F, ρ f = 1 → f = 1) :
    Nat.card ↥κ.range * Nat.card ↥F ≤ Nat.card ↥ρ.range * Nat.card ↥(ρ.ker.map κ) := by
  set K : Subgroup B := κ.ker with hK
  set N : Subgroup B := ρ.ker with hN
  set M : Subgroup B := K ⊓ N with hM
  have h1 : Nat.card K * Nat.card κ.range = Nat.card B := Subgroup.card_ker_mul_card_range κ
  have h2 : Nat.card N * Nat.card ρ.range = Nat.card B := Subgroup.card_ker_mul_card_range ρ
  have h3 : Nat.card (κ.comp N.subtype).ker * Nat.card (κ.comp N.subtype).range = Nat.card N :=
    Subgroup.card_ker_mul_card_range (κ.comp N.subtype)
  have h4 : (κ.comp N.subtype).range = N.map κ := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h5 : Nat.card (κ.comp N.subtype).ker = Nat.card M := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.2, x.1.2⟩
        invFun := fun x => ⟨⟨x.1, x.2.2⟩, x.2.1⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  have h6 : Nat.card F * Nat.card M ≤ Nat.card K := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective
      (fun p : F × M => (⟨(p.1 : B) * (p.2 : B), ?_⟩ : K)) ?_
    · exact (by
        have := hFκ _ p.1.2
        have h' : κ (p.2 : B) = 1 := p.2.2.1
        show κ ((p.1 : B) * (p.2 : B)) = 1
        rw [map_mul, this, h', one_mul])
    · intro p q hpq
      have h : (p.1 : B) * (p.2 : B) = (q.1 : B) * (q.2 : B) := congrArg Subtype.val hpq
      have hn : (q.1 : B)⁻¹ * (p.1 : B) = (q.2 : B) * (p.2 : B)⁻¹ := by
        calc (q.1 : B)⁻¹ * (p.1 : B)
            = (q.1 : B)⁻¹ * ((p.1 : B) * (p.2 : B)) * (p.2 : B)⁻¹ := by group
          _ = (q.1 : B)⁻¹ * ((q.1 : B) * (q.2 : B)) * (p.2 : B)⁻¹ := by rw [h]
          _ = (q.2 : B) * (p.2 : B)⁻¹ := by group
      have hmem : (q.1 : B)⁻¹ * (p.1 : B) ∈ F := F.mul_mem (F.inv_mem q.1.2) p.1.2
      have hρ1 : ρ ((q.1 : B)⁻¹ * (p.1 : B)) = 1 := by
        rw [hn, map_mul, map_inv]
        have a : ρ (q.2 : B) = 1 := q.2.2.2
        have b : ρ (p.2 : B) = 1 := p.2.2.2
        rw [a, b]; simp
      have h1' := hFρ _ hmem hρ1
      have hp : (p.1 : B) = q.1 := by
        have := congrArg ((q.1 : B) * ·) h1'
        simpa using this
      have hp2 : (p.2 : B) = q.2 := by
        rw [hp] at h
        exact mul_left_cancel h
      exact Prod.ext (Subtype.ext hp) (Subtype.ext hp2)
  have hMpos : 0 < Nat.card M := Nat.card_pos
  have key : Nat.card κ.range * Nat.card F * Nat.card M ≤
      Nat.card ρ.range * Nat.card (N.map κ) * Nat.card M := by
    calc Nat.card κ.range * Nat.card F * Nat.card M
        = Nat.card κ.range * (Nat.card F * Nat.card M) := by ring
      _ ≤ Nat.card κ.range * Nat.card K := Nat.mul_le_mul_left _ h6
      _ = Nat.card B := by rw [mul_comm]; exact h1
      _ = Nat.card N * Nat.card ρ.range := h2.symm
      _ = Nat.card M * Nat.card (N.map κ) * Nat.card ρ.range := by
        rw [← h3, h4, h5]
      _ = Nat.card ρ.range * Nat.card (N.map κ) * Nat.card M := by ring
  exact Nat.le_of_mul_le_mul_right key hMpos

end Cover

section Centralizer

open Wreath Equiv

theorem card_centralizer_base_swap (σ : Equiv.Perm (Fin 5)) (hσ : σ.IsSwap) :
    Nat.card ↥(Subgroup.centralizer ({Wreath.base σ σ} : Set (Wr2 (Equiv.Perm (Fin 5))))) =
      288 := by
  rw [Wreath.card_centralizer_base_self, s11_card_centralizer_swap σ hσ]
  norm_num

theorem card_centralizer_base_swap_inf_DE4 (σ : Equiv.Perm (Fin 5)) (hσ : σ.IsSwap) :
    Nat.card ↥(Subgroup.centralizer ({Wreath.base σ σ} : Set (Wr2 (Equiv.Perm (Fin 5)))) ⊓
      DE4) = 144 := by
  set C : Subgroup (Wr2 (Perm (Fin 5))) := Subgroup.centralizer ({Wreath.base σ σ} : Set _)
  have hC := card_centralizer_base_swap σ hσ
  let g : C →* ℤˣ := sgnProd.comp C.subtype
  have h1 : Nat.card g.ker * Nat.card g.range = Nat.card C :=
    Subgroup.card_ker_mul_card_range g
  have hsign : Perm.sign σ = -1 := by
    obtain ⟨i, j, hij, rfl⟩ := hσ
    exact Perm.sign_swap hij
  have hrange : g.range = ⊤ := by
    rw [eq_top_iff]
    intro u _
    have hg : g ⟨Wreath.base σ 1, Wreath.base_mem_centralizer_base_self σ⟩ = -1 := by
      show sgnProd (Wreath.base σ 1) = -1
      rw [sgnProd_base, hsign]; simp
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact one_mem _
    · exact ⟨_, hg⟩
  have h2 : Nat.card g.range = 2 := by
    rw [hrange]
    simp [Nat.card_eq_fintype_card, Fintype.card_units_int]
  have h3 : g.ker = (C ⊓ DE4).subgroupOf C := by
    ext x
    simp [Subgroup.mem_subgroupOf, mem_DE4, g]
  have h4 : Nat.card g.ker = Nat.card ↥(C ⊓ DE4) := by
    rw [h3]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h2, hC, h4] at h1
  omega

end Centralizer

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
