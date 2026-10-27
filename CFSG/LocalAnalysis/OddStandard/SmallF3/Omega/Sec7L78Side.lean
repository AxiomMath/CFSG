module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L78Act
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

structure Sec7L78Side (L P B A : Subgroup G) (c : G) : Prop where
  om : IsOm6P L
  syl : IsSylow2Of P L
  norm : IsNormalE16In P B
  A_N : A ≤ normalizer (L : Set G)
  inf_eq : A ⊓ L = B
  c_mem : c ∈ A
  c_cent : c ∈ centralizer (L : Set G)
  c_ord : orderOf c = 2
  A_cent : ∀ a ∈ A, a ∈ centralizer (L : Set G) → a = 1 ∨ a = c
  A_comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  A_sq : ∀ a ∈ A, a * a = 1

theorem sec7l78_act_of_aut_B [Finite G] (hP : Asc82Tab6P) {L P B : Subgroup G} (hL : IsOm6P L)
    (hPL : IsSylow2Of P L) (hB : IsNormalE16In P B) :
    ∃ φ : (Fin 5 → ZMod 2) → G, Sec7E16Act (L ⊓ normalizer (B : Set G)) B φ := by
  obtain ⟨-, hCB, φ, hφ⟩ := hP.aut_B G L hL P hPL B hB
  refine ⟨φ, ?_, hB.2.1, fun x hx => hCB ▸ ⟨hx.1.1, hx.2⟩, hφ⟩
  exact le_inf (hB.1.trans hPL.1) Subgroup.le_normalizer

theorem Sec7L78Side.decomp [Finite G] (hP : Asc82Tab6P) {L P B A : Subgroup G} {c : G}
    (hs : Sec7L78Side L P B A c) :
    ∀ a ∈ A, ∃ u ∈ A, (∀ n ∈ L ⊓ normalizer (B : Set G), u * n = n * u) ∧
      ∃ b ∈ B, a = u * b := by
  have hBA : B ≤ A := (le_of_eq hs.inf_eq.symm).trans inf_le_left
  intro a ha
  have haN : a ∈ normalizer (L : Set G) := hs.A_N ha
  have haB : ∀ b ∈ B, a * b = b * a := fun b hb => hs.A_comm a ha b (hBA hb)
  rcases hP.cent_B G L hs.om P hs.syl B hs.norm a haN haB with
    ⟨b, hb, hbc⟩ | ⟨b, hb, _, hc⟩
  · refine ⟨a * b⁻¹, mul_mem ha (inv_mem (hBA hb)), ?_, b, hb, by group⟩
    intro n hn
    rcases hs.A_cent (a * b⁻¹) (mul_mem ha (inv_mem (hBA hb))) hbc with h1 | h1
    · rw [h1]; simp
    · rw [h1]
      exact (mem_centralizer_iff.mp hs.c_cent n hn.1).symm
  · refine ⟨a * b⁻¹, mul_mem ha (inv_mem (hBA hb)), ?_, b, hb, by group⟩
    intro n hn
    exact hc n hn

theorem Sec7L78Side.type [Finite G] (hP : Asc82Tab6P) {L P B A : Subgroup G} {c : G}
    (hs : Sec7L78Side L P B A c) {x : G} (hx : x ∈ A)
    (hxc : ∀ n ∈ L ⊓ normalizer (B : Set G), x * n = n * x) (hx1 : x ≠ 1) (hxc' : x ≠ c) :
    ∃ α : ℤˣ, InducesTypeSome L x 6 1 1 α := by
  have hBA : B ≤ A := (le_of_eq hs.inf_eq.symm).trans inf_le_left
  obtain ⟨φ, hφ⟩ := sec7l78_act_of_aut_B hP hs.om hs.syl hs.norm
  have hxN : x ∈ normalizer (L : Set G) := hs.A_N hx
  have hxB : ∀ b ∈ B, x * b = b * x := fun b hb => hs.A_comm x hx b (hBA hb)
  rcases hP.cent_B G L hs.om P hs.syl B hs.norm x hxN hxB with
    ⟨b, hb, hbc⟩ | ⟨b, hb, ht, hc⟩
  · have huA : x * b⁻¹ ∈ A := mul_mem hx (inv_mem (hBA hb))
    rcases hs.A_cent (x * b⁻¹) huA hbc with h1 | h1
    · have hxb : x = b := by
        calc x = x * b⁻¹ * b := by group
          _ = 1 * b := by rw [h1]
          _ = b := by simp
      have hb_comm : ∀ n ∈ L ⊓ normalizer (B : Set G), n * b = b * n := by
        intro n hn
        rw [← hxb]
        exact (hxc n hn).symm
      exact absurd (hxb.trans (hφ.cent_N hb hb_comm)) hx1
    · have hxcb : x = c * b := by
        calc x = x * b⁻¹ * b := by group
          _ = c * b := by rw [h1]
      have hbc_eq : b = c⁻¹ * x := by rw [hxcb]; group
      have hb_comm : ∀ n ∈ L ⊓ normalizer (B : Set G), n * b = b * n := by
        intro n hn
        have hnL : n ∈ L := hn.1
        have hcn : Commute c n :=
          (commute_iff_eq c n).mpr (mem_centralizer_iff.mp hs.c_cent n hnL).symm
        have hxn : Commute x n := (commute_iff_eq x n).mpr (hxc n hn)
        have hbn : Commute b n := by
          rw [hbc_eq]
          exact (hcn.inv_left).mul_left hxn
        exact hbn.eq.symm
      exact absurd (hxcb.trans (by rw [hφ.cent_N hb hb_comm, mul_one])) hxc'
  · have hb_comm : ∀ n ∈ L ⊓ normalizer (B : Set G), n * b = b * n := by
      intro n hn
      have hxn : Commute x n := (commute_iff_eq x n).mpr (hxc n hn)
      have hun : Commute (x * b⁻¹) n := (commute_iff_eq (x * b⁻¹) n).mpr (hc n hn)
      have hb_eq : b = (x * b⁻¹)⁻¹ * x := by group
      have hbn : Commute b n := by
        rw [hb_eq]
        exact (hun.inv_left).mul_left hxn
      exact hbn.eq.symm
    have hb1 : b = 1 := hφ.cent_N hb hb_comm
    rcases ht with ⟨α, hα⟩
    exact ⟨α, by simpa [hb1] using hα⟩

end CFSG.OddStandard.SmallF3.Omega
