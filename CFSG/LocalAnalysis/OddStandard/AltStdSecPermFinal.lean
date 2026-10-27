module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecPermSec
public import CFSG.LocalAnalysis.OddStandard.AltStdSecHer

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup AltStdBal

section Three

variable {X : Type} [Group X] [Finite X] {A : Subgroup X} {n : ℕ}
  (e : A ≃* alternatingGroup (Fin n))

omit [Finite X] in
theorem corr_altSub_le_oddCoreOf {S : Finset (Fin n)} (hS : S.card = 3) :
    corr (X := X) e (altSub S) ≤
      oddCoreOf (centralizer (corr (X := X) e (altSub S) : Set X)) := by
  set R : Subgroup X := corr e (altSub S) with hR
  have hRabel : ∀ r ∈ R, ∀ r' ∈ R, r * r' = r' * r :=
    corr_comm e (fun g hg g' hg' => altSub_comm_of_card_three hS hg hg')
  have hRC : R ≤ centralizer (R : Set X) := fun r hr => by
    rw [mem_centralizer_iff]
    intro r' hr'
    exact hRabel r' hr' r hr
  let N₀ : Subgroup ↥(centralizer (R : Set X)) := R.subgroupOf (centralizer (R : Set X))
  have hN₀ : N₀.Normal := by
    refine ⟨fun m hm x => ?_⟩
    have hm' : (m : X) ∈ R := hm
    have hx : ((x : X)) ∈ centralizer (R : Set X) := x.2
    have hc : (m : X) * x = x * m := mem_centralizer_iff.1 hx _ hm'
    show (x : X) * m * (x : X)⁻¹ ∈ R
    rw [mul_inv_eq_iff_eq_mul.2 hc.symm]
    exact hm'
  have hcard : Nat.card N₀ = 3 := by
    have h1 : Nat.card N₀ = Nat.card R := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv
    have h2 : Nat.card R = Nat.card (altSub S) :=
      Nat.card_congr (corrEquiv (X := X) e (altSub_le_alternatingGroup S)).toEquiv
    rw [h1, h2, card_altSub_of_card_three hS]
  have hodd : Odd (Nat.card N₀) := by rw [hcard]; decide
  have hle : N₀ ≤ CFSG.oddCore ↥(centralizer (R : Set X)) := le_sSup ⟨hN₀, hodd⟩
  intro x hx
  exact ⟨⟨x, hRC hx⟩, hle (show (⟨x, hRC hx⟩ : ↥(centralizer (R : Set X))) ∈ N₀ from hx), rfl⟩

end Three

section Hyps

variable {X : Type} [Group X] {t : X} {A : Subgroup X} {n : ℕ}
  (h : ExactShape t A n) (e : A ≃* alternatingGroup (Fin n))

theorem eight_le_of_cards {S : Finset (Fin n)} {a b : ℕ} (hS : a ≤ S.card) (hSc : b ≤ Sᶜ.card)
    (hab : 8 ≤ a + b) : 8 ≤ n := by
  have := Finset.card_add_card_compl S
  simp only [Fintype.card_fin] at this
  omega

include h in
theorem hnorm_root {S : Finset (Fin n)} (hS : 4 ≤ S.card) (hSc : 4 ≤ Sᶜ.card) :
    centralizer ({t} : Set X) ⊓ centralizer (corr (X := X) e (altSub S) : Set X) ≤
      normalizer (corr (X := X) e (altSub Sᶜ) : Set X) :=
  hnorm_of_perm e (eight_le_of_cards hS hSc (by omega)) h (altSub_le_alternatingGroup S)
    (fun σ hσ => mem_normalizer_altSub
      (compl_iff_of_fixes ((mem_centralizer_altSub_iff hS).1 hσ)))

include h in
theorem hcc_root {S : Finset (Fin n)} (hS : 4 ≤ S.card) (hSc : 4 ≤ Sᶜ.card) :
    centralizer (corr (X := X) e (altSub Sᶜ) : Set X) ⊓ centralizer ({t} : Set X) ⊓
      centralizer (corr (X := X) e (altSub S) : Set X) ≤ zpowers t :=
  hcc_of_perm e (eight_le_of_cards hS hSc (by omega)) h (altSub_le_alternatingGroup S)
    (altSub_le_alternatingGroup Sᶜ) (fun σ hσT hσR => by
      have h1 := (mem_centralizer_altSub_iff hSc).1 hσT
      have h2 := (mem_centralizer_altSub_iff hS).1 hσR
      refine Equiv.ext fun i => ?_
      by_cases hi : i ∈ S
      · simpa using h2 i hi
      · simpa using h1 i (by simpa using hi))

include h in
theorem hnorm_three {S : Finset (Fin n)} (hS : S.card = 3) (hSc : 5 ≤ Sᶜ.card) :
    centralizer ({t} : Set X) ⊓ centralizer (corr (X := X) e (altSub S) : Set X) ≤
      normalizer (corr (X := X) e (altSub Sᶜ) : Set X) :=
  hnorm_of_perm e (eight_le_of_cards (le_of_eq hS.symm) hSc (by omega)) h
    (altSub_le_alternatingGroup S)
    (fun σ hσ => mem_normalizer_altSub (T := Sᶜ) (fun i => by
      simpa using (mem_iff_of_centralizer_altSub_card_three hS hσ i).not))

include h in
theorem hcc_three {S : Finset (Fin n)} (hS : S.card = 3) (hSc : 5 ≤ Sᶜ.card) :
    centralizer (corr (X := X) e (altSub Sᶜ) : Set X) ⊓ centralizer ({t} : Set X) ⊓
      centralizer (corr (X := X) e (altSub S) : Set X) ≤
      zpowers t ⊔ corr (X := X) e (altSub S) :=
  hcc_of_perm_le e (eight_le_of_cards (le_of_eq hS.symm) hSc (by omega)) h
    (altSub_le_alternatingGroup S) (altSub_le_alternatingGroup Sᶜ)
    (fun σ hσT hσR => by
      have h1 := (mem_centralizer_altSub_iff (by omega : 4 ≤ Sᶜ.card)).1 hσT
      refine mem_altSub_of_card_three hS (fun i hi => h1 i (by simpa using hi))
        (fun x hx y hy z hz hxy hyz hxz => ?_)
      exact (mem_centralizer_iff.1 hσR _ (cyc3_mem_altSub hx hy hz hxy hyz hxz)).symm)

end Hyps

section Final

variable {X : Type} [Group X] [Finite X] {t : X} {A : Subgroup X} {n : ℕ}

theorem exactShape_section_root (h : ExactShape t A n) (e : A ≃* alternatingGroup (Fin n))
    {S : Finset (Fin n)} (hS : 4 ≤ S.card) (hSc : 5 ≤ n - S.card)
    (ht : t ∈ centralizer (corr (X := X) e (altSub S) : Set X)) :
    ExactShape
      (QuotientGroup.mk (⟨t, ht⟩ : ↥(centralizer (corr (X := X) e (altSub S) : Set X))) :
        Sec X (corr (X := X) e (altSub S)))
      (((corr (X := X) e (altSub Sᶜ)).subgroupOf
          (centralizer (corr (X := X) e (altSub S) : Set X))).map
        (QuotientGroup.mk' (CFSG.oddCore ↥(centralizer (corr (X := X) e (altSub S) : Set X)))))
      (n - S.card) := by
  have hSc' : 5 ≤ Sᶜ.card := by rw [card_compl_fin]; exact hSc
  have hdisj : ∀ g ∈ altSub S, ∀ g' ∈ altSub Sᶜ, g * g' = g' * g := fun g hg g' hg' =>
    comm_of_altSub_disjoint disjoint_compl_right hg hg'
  have hBA := corr_le_centralizer_corr (X := X) e hdisj
  obtain ⟨eB⟩ := exists_equiv_corr_altSub (X := X) e Sᶜ
  have := exactShape_section h hBA ⟨eB⟩ hSc' (hnorm_root h e hS (by omega))
    ((hcc_root h e hS (by omega)).trans le_sup_left) ht
  rwa [card_compl_fin] at this

theorem exactShape_section_three (h : ExactShape t A n) (e : A ≃* alternatingGroup (Fin n))
    {S : Finset (Fin n)} (hS : S.card = 3) (hSc : 5 ≤ n - S.card)
    (ht : t ∈ centralizer (corr (X := X) e (altSub S) : Set X)) :
    ExactShape
      (QuotientGroup.mk (⟨t, ht⟩ : ↥(centralizer (corr (X := X) e (altSub S) : Set X))) :
        Sec X (corr (X := X) e (altSub S)))
      (((corr (X := X) e (altSub Sᶜ)).subgroupOf
          (centralizer (corr (X := X) e (altSub S) : Set X))).map
        (QuotientGroup.mk' (CFSG.oddCore ↥(centralizer (corr (X := X) e (altSub S) : Set X)))))
      (n - S.card) := by
  have hSc' : 5 ≤ Sᶜ.card := by rw [card_compl_fin]; exact hSc
  have hdisj : ∀ g ∈ altSub S, ∀ g' ∈ altSub Sᶜ, g * g' = g' * g := fun g hg g' hg' =>
    comm_of_altSub_disjoint disjoint_compl_right hg hg'
  have hBA := corr_le_centralizer_corr (X := X) e hdisj
  obtain ⟨eB⟩ := exists_equiv_corr_altSub (X := X) e Sᶜ
  have := exactShape_section h hBA ⟨eB⟩ hSc' (hnorm_three h e hS hSc')
    ((hcc_three h e hS hSc').trans (sup_le_sup_left (corr_altSub_le_oddCoreOf e hS) _)) ht
  rwa [card_compl_fin] at this

end Final

end CFSG.OddStandard.AltStdSec
