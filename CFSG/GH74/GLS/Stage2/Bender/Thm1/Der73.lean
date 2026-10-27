module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Choice
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Closed
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Helpers
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section L73

variable {G : Type} [Group G]

theorem isCoatom_conjugate {M : Subgroup G} (hM : IsCoatom M) (g : G) : IsCoatom (conjugate M g) :=
  (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup (MulAut.conj g⁻¹)) M).2 hM

theorem le_normalizer_conjugate {H K : Subgroup G} (h : H ≤ normalizer (K : Set G)) (g : G) :
    conjugate H g ≤ normalizer ((conjugate K g : Subgroup G) : Set G) := by
  intro x hx
  rw [mem_conjugate_iff] at hx
  rw [mem_normalizer_iff]
  intro y
  rw [mem_conjugate_iff, mem_conjugate_iff]
  have h1 := (mem_normalizer_iff.mp (h hx) (g * y * g⁻¹))
  have h2 : g * (x * y * x⁻¹) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ := by group
  rw [h2]
  exact h1

end L73

section L73b

variable {G : Type} [Group G] [Finite G]

theorem lemma7_3_of (hB14 : Bender14) (h1123 : IG_11_23) : Lemma7_3 := by
  intro G _ _ z k S M p hC V hV hCv g hVg
  have hodd : Odd (Nat.card ↥(Fm M)) := odd_card_Fm hC.hyp hC.mem
  have hVn : V ≤ normalizer ((conjugate (Fm M) g : Subgroup G) : Set G) :=
    hVg.trans (le_normalizer_conjugate (le_normalizer_Fm M) g)
  have hcop : Nat.Coprime 2 (Nat.card ↥(conjugate (Fm M) g)) := by
    have : Nat.card ↥(conjugate (Fm M) g) = Nat.card ↥(Fm M) :=
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    rw [this]
    exact Nat.coprime_two_left.mpr hodd
  have hsum := h1123 G 2 Nat.prime_two V (conjugate (Fm M) g) hV.1 (by rw [hV.2]; norm_num) hcop hVn
  have hFgM : conjugate (Fm M) g ≤ M :=
    hsum.trans (iSup₂_le fun v hv => inf_le_right.trans (hCv v hv.1 hv.2))
  have hFN : Fm M ≤ conjugate M g⁻¹ := by
    intro x hx
    rw [mem_conjugate_iff]
    have h1 : g⁻¹ * x * g ∈ conjugate (Fm M) g := by
      rw [mem_conjugate_iff]
      have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rw [this]
      exact hx
    have := hFgM h1
    simpa using this
  have hLinks : Links M (conjugate M g⁻¹) :=
    ⟨⊥, bot_le, inf_le_left.trans ((hC.Fs_eq hC.mem).le.trans hFN)⟩
  have hnp : ¬ ∃ q : ℕ, q.Prime ∧ IsPGroup q ↥(Fs M) := by
    rintro ⟨q, hq, hqP⟩
    rw [hC.Fs_eq hC.mem] at hqP
    exact not_isPGroup_of_twoPrimes hC.twoPrimes hq hqP
  have hEm : Em M = ⊥ := by
    have hodd' : Odd (Nat.card ↥(generalizedFitting ↥M)) := by
      rw [← card_Fs, hC.Fs_eq hC.mem]
      exact hodd
    rw [Em_def, layer_eq_bot_of_odd hodd', Subgroup.map_bot]
  have hres := (hB14 G hC.ctx.std.kps M (conjugate M g⁻¹) hC.coatom (isCoatom_conjugate hC.coatom g⁻¹) hLinks hnp).2
    g⁻¹ rfl hEm
  exact (Subgroup.inv_mem_iff M).mp hres

end L73b

end CFSG.GH74.GLS.Stage2.Bender.Thm1
