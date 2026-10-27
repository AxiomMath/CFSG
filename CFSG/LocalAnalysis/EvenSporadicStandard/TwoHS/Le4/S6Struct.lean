module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S6Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.Tight

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 CFSG.EvenSmallLie

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.card_four_structure (h : StdHyp G L)
    (hZ : Nat.card (center L) = 2) (S : Sylow 2 (centralizer (L : Set G)))
    (hS : Nat.card S = 4) :
    ∃ f : G, orderOf f = 4 ∧ centralizer (L : Set G) = zpowers f ∧
      (center L).map L.subtype = zpowers (f ^ 2) ∧
      centralizer ({f ^ 2} : Set G) = normalizer (L : Set G) := by
  classical
  obtain ⟨z, hz2, hZz⟩ := exists_map_center_eq_zpowers hZ
  have hzZ : z ∈ (center L).map L.subtype := hZz ▸ mem_zpowers z
  have hzC : z ∈ centralizer (L : Set G) := ((map_center_eq_inf_centralizer L) ▸ hzZ).2
  have hzL : z ∈ L := ((map_center_eq_inf_centralizer L) ▸ hzZ).1
  obtain ⟨S', hS'cyc, hzS'⟩ := h.exists_cyclic_sylow_mem hzC hz2
  have hE := h.centralizer_inf_centralizer_eq_map_sylow hzC hz2 S' hS'cyc hzS'
  have hCH : centralizer (L : Set G) ≤ centralizer ({z} : Set G) := fun c hc =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 hc) z hzL).symm
  rw [inf_eq_left.2 hCH] at hE
  have hcard : Nat.card (S' : Subgroup (centralizer (L : Set G))) = 4 := by
    rw [← hS]; exact Nat.card_congr (Sylow.equiv S' S).toEquiv
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (S' : Subgroup (centralizer (L : Set G))))
  set f : G := ((g : centralizer (L : Set G)) : G) with hfdef
  have hf4 : orderOf f = 4 := by
    have h1 : orderOf g = Nat.card (S' : Subgroup (centralizer (L : Set G))) :=
      orderOf_eq_card_of_forall_mem_zpowers hg
    rw [hcard] at h1
    rw [hfdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact h1
  have hCf : centralizer (L : Set G) = zpowers f := by
    refine hE.trans (le_antisymm ?_ ?_)
    · rintro _ ⟨s, hs, rfl⟩
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hg ⟨s, hs⟩)
      refine mem_zpowers_iff.2 ⟨k, ?_⟩
      have := congrArg (fun y : (S' : Subgroup (centralizer (L : Set G))) =>
        ((y : centralizer (L : Set G)) : G)) hk
      simpa [hfdef] using this
    · intro x hx
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
      exact ⟨(g : centralizer (L : Set G)) ^ k, Subgroup.zpow_mem _ g.2 k, by simp [hfdef]⟩
  have hzf : z = f ^ 2 := by
    have hzz : z * z = 1 := by
      have := pow_orderOf_eq_one z
      rwa [hz2, sq] at this
    rcases eq_one_or_eq_sq_of_mem_zpowers hf4 (hCf ▸ hzC) hzz with h1 | h1
    · rw [h1, orderOf_one] at hz2
      omega
    · exact h1
  have hNC : normalizer (L : Set G) ≤ centralizer ({z} : Set G) := by
    intro n hn
    rw [mem_centralizer_singleton_iff]
    have hcomm : ∀ l ∈ L, l * (n * z * n⁻¹) = (n * z * n⁻¹) * l := by
      intro l hl
      have hl' : n⁻¹ * l * n ∈ L := (mem_normalizer_iff.1 hn _).2 (by
        have : n * (n⁻¹ * l * n) * n⁻¹ = l := by group
        rw [this]; exact hl)
      have hz' : (n⁻¹ * l * n) * z = z * (n⁻¹ * l * n) := mem_centralizer_iff.1 hzC _ hl'
      calc l * (n * z * n⁻¹) = n * ((n⁻¹ * l * n) * z) * n⁻¹ := by group
        _ = n * (z * (n⁻¹ * l * n)) * n⁻¹ := by rw [hz']
        _ = (n * z * n⁻¹) * l := by group
    have hnz : n * z * n⁻¹ ∈ (center L).map L.subtype := by
      rw [map_center_eq_inf_centralizer]
      refine ⟨(mem_normalizer_iff.1 hn z).1 hzL, mem_centralizer_iff.2 fun l hl => ?_⟩
      exact hcomm l hl
    rw [hZz] at hnz
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hz2 hnz with h1 | h1
    · exfalso
      have : z = 1 := by
        have h2 : n⁻¹ * (n * z * n⁻¹) * n = z := by group
        rw [h1] at h2
        simpa using h2.symm
      rw [this, orderOf_one] at hz2
      omega
    · calc n * z = (n * z * n⁻¹) * n := by group
        _ = z * n := by rw [h1]
  refine ⟨f, hf4, hCf, ?_, ?_⟩
  · rw [← hzf]; exact hZz
  · rw [← hzf]; exact le_antisymm (h.centralizer_le_normalizer hzC hz2) hNC

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.exists_tight_four (h : StdHyp G L)
    (hFG : FoursGroupCondition L) (S : Sylow 2 (centralizer (L : Set G))) (hS : Nat.card S = 4) :
    ∃ g' c s : G, c ∈ centralizer (L : Set G) ∧ g' * c * g'⁻¹ = s ∧ orderOf s = 4 ∧
      s ∈ normalizer (L : Set G) ∧
      (∀ y ∈ zpowers s, y ∈ centralizer (L : Set G) → y = 1) ∧
      ∀ x : G, x * s ^ 2 = s ^ 2 * x → x * s * x⁻¹ ∈ zpowers s := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hset := h.toStandardSetting
  have hSc := hset.isCyclic_sylow S
  have hS4 : 4 ≤ Nat.card S := hS.ge
  by_cases hall : ∀ g : G, g ∉ normalizer (L : Set G) → ∀ P : Subgroup G,
      P ≤ (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ⊓ normalizer (L : Set G) →
      IsPGroup 2 P → Nat.card P ≤ 2
  · exact (hset.false_of_forall_card_le_two hFG S hS4 hall).elim
  · push Not at hall
    obtain ⟨g, hg, P, hP, hP2, hPcard⟩ := hall
    have hP4 : 4 ≤ Nat.card P := by
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP2
      rw [hm] at hPcard ⊢
      rcases m with _ | _ | m
      · norm_num at hPcard
      · norm_num at hPcard
      · calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨g', hg', R, T, hRC, hR, hRcard, hTg, hTN, hT, hTcard, hRT⟩ :=
      exists_full_conj_centralized hset.standard S hSc hg (hP.trans inf_le_left)
        (hP.trans inf_le_right) hP2 hP4
    obtain ⟨s, m, hm2, hmS, hs, hsT, hTcyc, hsN, hTC, hnorm⟩ :=
      h.exists_tight_cyclic S hSc hS4 hg' hTg hTN hT hTcard
    have hm : m = 2 := by
      have : 2 ^ m = 2 ^ 2 := by rw [← hmS, hS]; norm_num
      exact Nat.pow_right_injective le_rfl this
    subst hm
    have hsord : orderOf s = 4 := by rw [hs]; norm_num
    obtain ⟨c, hcC, hc⟩ := Subgroup.mem_map.mp (hTg hsT)
    have hc' : g' * c * g'⁻¹ = s := by simpa [MulAut.conj_apply] using hc
    have hTeq : T = zpowers s := by
      refine (Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hsT) ?_).symm
      rw [Nat.card_zpowers, hsord, hTcard, hS]
    refine ⟨g', c, s, hcC, hc', hsord, hsN, ?_, ?_⟩
    · intro y hy hyC
      exact hTC y (hTeq ▸ hy) hyC
    · intro x hx
      have := hnorm x (by simpa using hx) s hsT
      rw [hTeq] at this
      exact this

end CFSG.EvenSporadicStandard.TwoHS
