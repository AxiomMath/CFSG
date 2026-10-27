module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Recognition.HSMultiplier
  Matrix

section Conj

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f s y n : G} {S₀ : Subgroup G}


theorem exists_conj_coord (hHN : HNCentralizerFacts) (h : Sect7Hyps G L f s y S₀ n) :
    ∃ (M : ModelData G L y) (c : G), c * f ^ 2 = f ^ 2 * c ∧
      Sect8Hyp ((basisCoord M.hΛ h.four M.ι).conj c) f n S₀ := by
  have hF : FourHyp G L f := h.four
  obtain ⟨hΛ, ι, y₁, hy₁mem, hy₁L, hy₁sq, hy₁conj⟩ :=
    exists_model hHN hF h.yy h.y_not h.cent_eq h.quot
  let M : ModelData G L y := ⟨hΛ, ι, y₁, hy₁mem, hy₁L, hy₁sq, hy₁conj⟩
  have hLF : ListFacts := Certificates.certificate26753
  have hshat : ∀ A ∈ shatList, A ∈ q0List :=
    (Certificates.certificate26420 : Q0Facts).shat_sub
  obtain ⟨hactN, hcent⟩ := ModelData.count_core hF h.yy h.yf h.cent_eq M
  have hreal := ModelData.real_q0 hF h.yy h.yf h.cent_eq M
  have hf := f_mem_E M.hΛ hF M.ι
  have hvec := vec_f M.hΛ hF M.ι
  set C₁ := basisCoord M.hΛ hF M.ι with hC₁
  set S₁ := S1sub C₁ (f ^ 2) hLF with hS₁
  have hcard : Nat.card S₁ = 4096 :=
    card_S1sub C₁ hLF hshat hcent hreal (pow_mem hf 2)
  have hS₁N : S₁ ≤ centralizer ({f ^ 2} : Set G) := fun x hx => mem_centralizer_singleton_iff.2 hx.1
  have hS₁p : IsPGroup 2 S₁ := IsPGroup.of_card (n := 12) (by rw [hcard]; norm_num)
  have hLc : L ≤ centralizer ({f ^ 2} : Set G) := by
    intro l hl
    rw [mem_centralizer_singleton_iff]
    exact ((show Commute l f from comm_f_of_mem hF hl).pow_right 2).eq
  have hLN : L.relIndex (centralizer ({f ^ 2} : Set G)) ≤ 4 :=
    relindex_le_four_of_inv hLc (fun l hl => comm_f_of_mem hF hl) hF.sq_mem h.yy
      (y_mem_normalizer hF h.cent_eq) h.cent_eq h.yf
  have hL : Nat.card L = 88704000 := by
    rw [Nat.card_congr M.ι.toEquiv]
    exact M.hΛ.card_eq
  have hS₀card : Nat.card S₀ ≤ Nat.card S₁ := by
    rw [hcard]
    exact card_two_subgroup_le h.S₀_t h.pgroup hLN hL
  obtain ⟨g, hgN, hg⟩ := exists_conj_of_card_le h.S₀_t hS₁N h.pgroup h.rel hS₁p hS₀card
  have hneg : ∃ u ∈ S₁, u * f * u⁻¹ = f⁻¹ := by
    obtain ⟨A, hA, hA22⟩ := hLF.shat_neg
    obtain ⟨x, hxc, hxn, hxA⟩ := hreal A (hshat A hA)
    refine ⟨x, ⟨hxc, hxn, hxA ▸ hA⟩, ?_⟩
    rcases conj_f_cases hF hxc with h1 | h1
    · exfalso
      have h2 := C₁.vec_conj hxn hf
      rw [h1, hvec, hxA, fVec_eq, Matrix.mulVec_single_one] at h2
      have h3 := congrFun h2 2
      simp only [Matrix.col_apply, Pi.single_eq_same] at h3
      rw [hA22] at h3
      revert h3
      decide
    · exact h1
  obtain ⟨c, hcc, hcf, hc⟩ := exists_conj_fixing_f hF (S₀ := S₀) (S₁ := S₁)
    (fun x (hx : x ∈ S₁) => hx.1) hneg
    (mem_centralizer_singleton_iff.1 hgN) hg
  exact ⟨M, c, hcc, sect8Hyp_conj hLF hshat hf hvec hcent hactN hreal
    (fun x hx => mem_centralizer_singleton_iff.1 (h.S₀_t hx)) h.n_norm hcc hcf hc⟩

end Conj

section Transfer

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f s y n : G} {S₀ : Subgroup G}

theorem ZData.congr_E {C C' : ECoord G} (hE : C.E = C'.E) {r w ρ : G}
    (hz : ZData C L f y r w ρ) : ZData C' L f y r w ρ := by
  unfold ZData SAU.IsW SAU.M0 Cl16 at *
  rw [← hE]
  exact hz

theorem ECoord.E_eq_of_sect8Hyp {C C' : ECoord G}
    (h : Sect8Hyp C f n S₀) (h' : Sect8Hyp C' f n S₀) : C'.E = C.E := by
  have hLF : ListFacts := Certificates.certificate26753
  have hle : C'.E ≤ C.E := by
    refine C.le_of_abelian_of_mat_mem C'.E (fun a ha b hb => C'.comm ha hb)
      (le_of_eq C'.natCard_E.symm) (fun x hx => h.S₀_norm x (h'.E_le hx))
      (fun x hx => h.actS x (h'.E_le hx)) (fun x hx hx1 => ?_) hLF.Sub
    exact h.centN x (h.S₀_cent x (h'.E_le hx))
      ((C.mat_eq_one_iff (h.S₀_norm x (h'.E_le hx))).1 hx1)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [C.natCard_E, C'.natCard_E])


theorem zdata_holds (hHN : HNCentralizerFacts) (H : Sect7Hyps G L f s y S₀ n) {C : ECoord G}
    (h : Sect8Hyp C f n S₀) : ∃ r w ρ : G, ZData C L f y r w ρ := by
  obtain ⟨M, c, hcc, hC'⟩ := exists_conj_coord hHN H
  have hz := (zdata_model H.four H.yy H.yf H.cent_eq M).conj H hcc
  exact ⟨_, _, _, hz.congr_E (ECoord.E_eq_of_sect8Hyp h hC')⟩

end Transfer

end CFSG.EvenSporadicStandard.TwoHS
