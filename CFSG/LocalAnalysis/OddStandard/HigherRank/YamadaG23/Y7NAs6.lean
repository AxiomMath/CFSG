module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NAs4
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NAs5

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {t g : G} {Lam P S U P1 : Subgroup G}

private lemma eq_two_pow_seven_of_dvd {n : ℕ} (hdvd : 2 ^ 6 ∣ n) (hle : n ≤ 2 ^ 7)
    (hlt : 2 ^ 6 < n) : n = 2 ^ 7 := by
  obtain ⟨k, rfl⟩ := hdvd
  norm_num at hle hlt ⊢
  omega

namespace NtAbs

theorem case1_g0 (h : NtAbs t g Lam P S U P1)
    (hc : Nat.card ↥(conjSub t (centIn P1 Lam)) = 2 ^ 7) :
    ∃ g0 : G, g0 ∈ conjSub t (centIn P1 Lam) ∧ g0 ^ 2 = 1 ∧ g0 ∉ U ∧
      conjSub t (centIn P1 Lam) = U ⊔ zpowers g0 ∧ g0 * (t * g0 * t⁻¹) = g := by
  have hwr : Wr7 t (normIn P1 Lam) (conjSub t (centIn P1 Lam)) :=
    ⟨h.t_sq, h.case1_direct hc⟩
  have hgmem : g ∈ normIn P1 Lam ⊓ centralizer ({t} : Set G) :=
    ⟨h.g_mem_P0, Subgroup.mem_centralizer_singleton_iff.mpr h.tg.symm⟩
  obtain ⟨g0, hg0eq⟩ := hwr.centEquiv.surjective ⟨g, hgmem⟩
  have hg0val : (g0 : G) * (t * (g0 : G) * t⁻¹) = g := by
    have h1 : ((hwr.centEquiv g0 :
        ↥(normIn P1 Lam ⊓ centralizer ({t} : Set G))) : G) =
        (g0 : G) * (t * (g0 : G) * t⁻¹) := hwr.centEquiv_apply g0
    have h2 : ((hwr.centEquiv g0 :
        ↥(normIn P1 Lam ⊓ centralizer ({t} : Set G))) : G) = g :=
      congrArg (fun z : ↥(normIn P1 Lam ⊓ centralizer ({t} : Set G)) => (z : G)) hg0eq
    exact h1.symm.trans h2
  have hv_mem : t * (g0 : G) * t⁻¹ ∈ conjSub t (conjSub t (centIn P1 Lam)) :=
    (mem_conjSub_iff' t (conjSub t (centIn P1 Lam)) _).mpr ⟨(g0 : G), g0.2, rfl⟩
  have hcomm : (g0 : G) * (t * (g0 : G) * t⁻¹) = (t * (g0 : G) * t⁻¹) * (g0 : G) :=
    hwr.direct.2.2 (g0 : G) g0.2 _ hv_mem
  have hsq : (g0 : G) ^ 2 * (t * (g0 : G) * t⁻¹) ^ 2 = 1 := by
    have hmul := Commute.mul_pow hcomm 2
    rw [← hmul, hg0val, h.g_sq]
  have hg0sq : (g0 : G) ^ 2 = 1 := by
    have h1 : (g0 : G) ^ 2 ∈ conjSub t (centIn P1 Lam) :=
      (conjSub t (centIn P1 Lam)).pow_mem g0.2 2
    have h2 : (t * (g0 : G) * t⁻¹) ^ 2 ∈ conjSub t (conjSub t (centIn P1 Lam)) :=
      (conjSub t (conjSub t (centIn P1 Lam))).pow_mem hv_mem 2
    exact (hwr.unique h1 (conjSub t (centIn P1 Lam)).one_mem h2
      (conjSub t (conjSub t (centIn P1 Lam))).one_mem (by simpa using hsq)).1
  have hg0notU : (g0 : G) ∉ U := by
    intro hg0U
    have hvP : t * (g0 : G) * t⁻¹ ∈ P :=
      h.wr.le_left.2 ((mem_conjSub_iff' t U _).mpr ⟨(g0 : G), hg0U, rfl⟩)
    have hgP : g ∈ P := by
      rw [← hg0val]
      exact P.mul_mem (h.wr.le_left.1 hg0U) hvP
    have hgcent : g ∈ centEl P t :=
      ⟨hgP, Subgroup.mem_centralizer_singleton_iff.mpr h.tg.symm⟩
    rw [h.cent] at hgcent
    exact h.g_not_S hgcent
  have hsup_le : U ⊔ zpowers (g0 : G) ≤ conjSub t (centIn P1 Lam) :=
    sup_le h.U_le_U0 (Subgroup.zpowers_le.mpr g0.2)
  have hlt : U < U ⊔ zpowers (g0 : G) := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    refine hg0notU ?_
    have hmem : (g0 : G) ∈ U ⊔ zpowers (g0 : G) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers (g0 : G))
    rwa [← heq] at hmem
  have hcard_lt : 2 ^ 6 < Nat.card ↥(U ⊔ zpowers (g0 : G)) := by
    have := Subgroup.card_lt_of_lt hlt
    rwa [h.card_U] at this
  have hdvd : 2 ^ 6 ∣ Nat.card ↥(U ⊔ zpowers (g0 : G)) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : U ≤ U ⊔ zpowers (g0 : G))
    rwa [h.card_U] at this
  have hcard_le : Nat.card ↥(U ⊔ zpowers (g0 : G)) ≤ 2 ^ 7 := by
    have := Subgroup.card_le_of_le hsup_le
    rwa [hc] at this
  have hcard_eq : Nat.card ↥(U ⊔ zpowers (g0 : G)) = 2 ^ 7 :=
    eq_two_pow_seven_of_dvd hdvd hcard_le hcard_lt
  have hsup_eq : U ⊔ zpowers (g0 : G) = conjSub t (centIn P1 Lam) :=
    Subgroup.eq_of_le_of_card_ge hsup_le (by rw [hc, hcard_eq])
  exact ⟨(g0 : G), g0.2, hg0sq, hg0notU, hsup_eq.symm, hg0val⟩

theorem cases (h : NtAbs t g Lam P S U P1) :
    (∃ g0 : G, g0 ∈ conjSub t (centIn P1 Lam) ∧ g0 ^ 2 = 1 ∧ g0 ∉ U ∧
        conjSub t (centIn P1 Lam) = U ⊔ zpowers g0 ∧ g0 * (t * g0 * t⁻¹) = g ∧
        IsInternalDirect (normIn P1 Lam) (conjSub t (centIn P1 Lam))
          (conjSub t (conjSub t (centIn P1 Lam))) ∧
        Nonempty (↥(conjSub t (centIn P1 Lam)) ≃* ↥(S ⊔ zpowers g))) ∨
      (conjSub t (centIn P1 Lam) = U ∧ normIn P1 Lam = P ⊔ zpowers g) := by
  rcases h.card_U0_cases with hc | hc
  · exact Or.inr (h.case2 hc)
  · obtain ⟨g0, hg0, hg0sq, hg0notU, hU0eq, hg0g⟩ := h.case1_g0 hc
    exact Or.inl ⟨g0, hg0, hg0sq, hg0notU, hU0eq, hg0g, h.case1_direct hc, h.case1_iso hc⟩

end NtAbs

end CFSG.OddStandard.HigherRank.YamadaG23
