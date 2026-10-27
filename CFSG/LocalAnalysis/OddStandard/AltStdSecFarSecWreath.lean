module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarSecTri
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarWreath

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm

section Gen

variable {X : Type*} [Group X]

theorem exists_not_comm_of_alt {B : Subgroup X} {n : ℕ} (hn : 4 ≤ n)
    (e : B ≃* alternatingGroup (Fin n)) : ∃ a ∈ B, ∃ b ∈ B, a * b ≠ b * a := by
  have hc := center_eq_bot_of_alt hn e
  have : Nontrivial (alternatingGroup (Fin n)) :=
    alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; omega)
  have : Nontrivial B := e.toEquiv.nontrivial
  obtain ⟨x, hx⟩ := exists_ne (1 : B)
  have hxc : x ∉ center B := by
    rw [hc, mem_bot]
    exact hx
  rw [mem_center_iff] at hxc
  push Not at hxc
  obtain ⟨y, hy⟩ := hxc
  exact ⟨y, y.2, x, x.2, fun h => hy (Subtype.ext h)⟩

theorem two_mul_factorial_lt_add_two {k : ℕ} (hk : 1 ≤ k) : 2 * k.factorial < (k + 2).factorial := by
  rw [Nat.factorial_succ, Nat.factorial_succ]
  have hpos := Nat.factorial_pos k
  have h6 : 6 ≤ (k + 1 + 1) * (k + 1) := by nlinarith
  calc 2 * k.factorial < 6 * k.factorial := by omega
    _ ≤ ((k + 1 + 1) * (k + 1)) * k.factorial := Nat.mul_le_mul_right _ h6
    _ = (k + 1 + 1) * ((k + 1) * k.factorial) := by ring

end Gen

section Wr

variable {G : Type} [Group G] [Finite G] {z : G} {m : ℕ} (O : OverData G z m)
  {R : Subgroup (Perm (Fin (m + 3)))} (hR : SecR m R)

theorem secLq_injective (hm : 6 ≤ m) :
    Function.Injective ((QuotientGroup.mk' (CFSG.oddCore (secQ (secP O R)))).comp
      (secIncl O hR _ altSub_compl_le)) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have h1 : secIncl O hR _ altSub_compl_le y ∈ CFSG.oddCore (secQ (secP O R)) :=
    (QuotientGroup.eq_one_iff _).1 hy
  have h2 : secIncl O hR _ altSub_compl_le y ∈ secL O hR ⊓ CFSG.oddCore (secQ (secP O R)) :=
    Subgroup.mem_inf.2 ⟨⟨y, rfl⟩, h1⟩
  rw [secL_inf_oddCore O hR hm, mem_bot] at h2
  exact secIncl_injective O hR _ _ (h2.trans (map_one _).symm)

theorem not_wreath_of_order (hm : 10 ≤ m) :
    ¬ WreathOutcome
      (QuotientGroup.mk (secT O hR) : secQ (secP O R) ⧸ CFSG.oddCore (secQ (secP O R)))
      ((secB O hR).map (QuotientGroup.mk' (CFSG.oddCore (secQ (secP O R))))) (m - 3) := by
  intro hW
  set π := QuotientGroup.mk' (CFSG.oddCore (secQ (secP O R))) with hπ
  set ψ := π.comp (secIncl O hR _ altSub_compl_le) with hψ
  have hψi : Function.Injective ψ := secLq_injective O hR (by omega)
  set L := ψ.range with hL
  have eL : L ≃* alternatingGroup (Fin (m - 1)) :=
    (MonoidHom.ofInjective hψi).symm.trans
      ((altSubEquiv _).trans (Equiv.altCongrHom (finCongr (card_fourSet_compl (by omega)))))
  have : IsSimpleGroup L := isSimpleGroup_of_alt (by omega) eL
  obtain ⟨eA⟩ := (exactShape_secQ O hR (by omega)).iso
  refine false_of_wreath_of_big (by omega : 7 ≤ m - 3) hW (L := L) ?_ ?_ ?_
    (exists_not_comm_of_alt (by omega) eA)
  ·
    apply closure_eq_top_of_simple
    · intro a x hx
      change Odd (orderOf (a * x * a⁻¹))
      rw [orderOf_conj']
      exact hx
    · have h3 : (swap (⟨4, by omega⟩ : Fin (m + 3)) ⟨5, by omega⟩ *
          swap (⟨4, by omega⟩ : Fin (m + 3)) ⟨6, by omega⟩).IsThreeCycle :=
        isThreeCycle_swap_mul_swap_same (fin_ne_mk (by simp)) (fin_ne_mk (by simp))
          (fin_ne_mk (by simp))
      have hmem : swap (⟨4, by omega⟩ : Fin (m + 3)) ⟨5, by omega⟩ *
          swap (⟨4, by omega⟩ : Fin (m + 3)) ⟨6, by omega⟩ ∈ altSub (fourSet (m + 3))ᶜ := by
        rw [mem_altSub]
        refine ⟨h3.sign, fun i hi => ?_⟩
        have hi' : (i : ℕ) < 4 := by simpa [mem_fourSet] using hi
        have h46 : swap (⟨4, by omega⟩ : Fin (m + 3)) ⟨6, by omega⟩ i = i :=
          swap_apply_of_ne_of_ne (fin_ne_mk (by omega)) (fin_ne_mk (by omega))
        rw [Perm.mul_apply, h46]
        exact swap_apply_of_ne_of_ne (fin_ne_mk (by omega)) (fin_ne_mk (by omega))
      set c : ↥(altSub (fourSet (m + 3))ᶜ) := ⟨_, hmem⟩ with hc
      have hoc : orderOf c = 3 := by
        rw [hc, Subgroup.orderOf_mk, h3.orderOf]
      have hcL : ψ c ∈ L := MonoidHom.mem_range.2 ⟨c, rfl⟩
      have hox : orderOf (⟨ψ c, hcL⟩ : L) = 3 := by
        rw [Subgroup.orderOf_mk, orderOf_injective ψ hψi c, hoc]
      refine ⟨⟨ψ c, hcL⟩, ?_, ?_⟩
      · change Odd (orderOf (⟨ψ c, hcL⟩ : L))
        rw [hox]
        decide
      · intro h
        rw [h, orderOf_one] at hox
        omega
  ·
    intro x hx
    obtain ⟨b, ⟨σ, rfl⟩, rfl⟩ := hx
    refine ⟨⟨σ, altSub_mono fourTail_subset_compl σ.2⟩, ?_⟩
    change π (secIncl O hR _ altSub_compl_le _) = π (secPsi O hR σ)
    exact congrArg π (secIncl_congr O hR _ _ rfl)
  ·
    rw [Nat.card_congr eL.toEquiv]
    have : Nontrivial (Fin (m - 1)) := Fin.nontrivial_iff_two_le.2 (by omega)
    have h2 := two_mul_nat_card_alternatingGroup (α := Fin (m - 1))
    rw [Nat.card_perm, Nat.card_fin] at h2
    have h3 := two_mul_factorial_lt_add_two (k := m - 3) (by omega)
    rw [show m - 3 + 2 = m - 1 by omega] at h3
    omega

theorem l0Normal_of_not_hn (htri : ExactShapeTrichotomy)
    (hK : CFSG.SectionRank.IsKGroupCat ↥(centralizer (secP O R : Set G))) (hm : 12 ≤ m)
    (hHN : m - 3 = 10 → ¬ HNOutcome
      (QuotientGroup.mk (secT O hR) : secQ (secP O R) ⧸ CFSG.oddCore (secQ (secP O R)))) :
    L0Normal O R :=
  l0Normal_of_secL O hR
    (conj_mem_secL_of_not O hR htri hK hm (not_wreath_of_order O hR (by omega)) hHN) (by omega)

end Wr

end CFSG.OddStandard.AltStdSec
