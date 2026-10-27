module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19MinSwap
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15Setup
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19MinBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Norm

variable {G : Type} [Group G]

theorem commutator_sup_sup_eq_bot' {A B C D : Subgroup G} (h1 : ⁅A, C⁆ = ⊥) (h2 : ⁅A, D⁆ = ⊥)
    (h3 : ⁅B, C⁆ = ⊥) (h4 : ⁅B, D⁆ = ⊥) : ⁅A ⊔ B, C ⊔ D⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h1 h2 h3 h4 ⊢
  refine sup_le ?_ ?_
  · rw [Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.le_centralizer_iff.mp h1) (Subgroup.le_centralizer_iff.mp h2)
  · rw [Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.le_centralizer_iff.mp h3) (Subgroup.le_centralizer_iff.mp h4)

theorem conjugate_sup' (A B : Subgroup G) (g : G) :
    CFSG.conjugate (A ⊔ B) g = CFSG.conjugate A g ⊔ CFSG.conjugate B g :=
  Subgroup.map_sup A B _

variable [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK i : G} {Ki KP R2 : Subgroup G}

theorem Ident2519.three_dvd_card (hid : Ident2519 N t i Ki KP R2) : 3 ∣ Nat.card KP := by
  obtain ⟨A, hA, -, hA9⟩ := hid.three_rank
  have : Nat.card A ∣ Nat.card KP := Subgroup.card_dvd_of_le hA
  rw [hA9] at this
  exact (by norm_num : 3 ∣ 9).trans this

theorem Ident2519.center_three_conj (hid : Ident2519 N t i Ki KP R2) (g : G) :
    ∀ x ∈ CFSG.conjugate KP g, (∀ y ∈ CFSG.conjugate KP g, y * x = x * y) → x ^ 3 = 1 →
      x = 1 := by
  intro x hx hc hx3
  have hgx : g * x * g⁻¹ ∈ KP := BenderBranch.mem_conjugate_iff.mp hx
  have hcen : g * x * g⁻¹ ∈ centerOf KP := by
    refine ⟨hgx, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g ∈ CFSG.conjugate KP g := by
      rw [BenderBranch.mem_conjugate_iff]
      simpa [mul_assoc] using hy
    have hh := hc _ hy'
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [hh]
      _ = (g * x * g⁻¹) * y := by group
  have h3 : (g * x * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3]; group
  have h1 := hid.center_three _ hcen h3
  calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
    _ = 1 := by rw [h1]; group

theorem Ident2519.mem_normalizer_K (hid : Ident2519 N t i Ki KP R2) {c : G} (hct : c * t = t * c)
    (hc : c ∈ Subgroup.normalizer (KP : Set G)) : c ∈ Subgroup.normalizer (N.K : Set G) := by
  rw [hid.K_eq]
  refine CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf_normalizer_contains _ ?_
  exact mem_normalizer_inf' hc
    (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hct))

theorem Ident2519.commutator_conj_eq_bot (hid : Ident2519 N t i Ki KP R2) (hti : t * i = i * t)
    (ht2 : t * t = 1) {c : G} (hci : c * i = i * c) (hct : c * t = t * c)
    (hne : CFSG.conjugate KP c ≠ KP) : ⁅KP, CFSG.conjugate KP c⁆ = ⊥ := by
  have hcomp : ∀ g : G, g * i = i * g →
      IsComponentIn (CFSG.conjugate Ki g) (Subgroup.centralizer ({i} : Set G)) := fun g hg =>
    isComponentIn_centralizer_conj g (by
      calc g⁻¹ * i * g = g⁻¹ * (i * g) := by group
        _ = g⁻¹ * (g * i) := by rw [hg]
        _ = i := by group) hid.comp
  have hKc := hcomp c hci
  have hKt := hcomp t hti
  rcases hid.shape with ⟨hne1, hKPeq, -⟩ | ⟨hKPeq, -⟩
  · rw [hKPeq] at hne ⊢
    have hconj_t : ∀ H : Subgroup G,
        CFSG.conjugate (CFSG.conjugate H t) c = CFSG.conjugate (CFSG.conjugate H c) t := by
      intro H
      rw [BenderBranch.conjugate_conjugate, BenderBranch.conjugate_conjugate, hct]
    have hKtt : CFSG.conjugate (CFSG.conjugate Ki t) t = Ki := by
      rw [BenderBranch.conjugate_conjugate, ht2, BenderBranch.conjugate_one]
    have hBc : IsComponentIn (CFSG.conjugate (CFSG.conjugate Ki t) c)
        (Subgroup.centralizer ({i} : Set G)) :=
      isComponentIn_centralizer_conj c (by
        calc c⁻¹ * i * c = c⁻¹ * (i * c) := by group
          _ = c⁻¹ * (c * i) := by rw [hci]
          _ = i := by group) hKt
    rw [conjugate_sup'] at hne ⊢
    set A := Ki with hA
    set B := CFSG.conjugate Ki t with hB
    set A' := CFSG.conjugate Ki c with hA'
    set B' := CFSG.conjugate B c with hB'
    have hB'eq : B' = CFSG.conjugate A' t := hconj_t Ki
    have hA'A : A' ≠ A := by
      intro h
      apply hne
      have : B' = B := by rw [hB'eq, h]
      rw [h, this]
    have hA'B : A' ≠ B := by
      intro h
      apply hne
      have : B' = A := by rw [hB'eq, h, hB, hKtt]
      rw [h, this, sup_comm]
    have hB'A : B' ≠ A := by
      intro h
      apply hA'B
      have : CFSG.conjugate B' t = A' := by
        rw [hB'eq, BenderBranch.conjugate_conjugate, ht2, BenderBranch.conjugate_one]
      rw [← this, h]
    have hB'B : B' ≠ B := by
      intro h
      apply hA'A
      have : CFSG.conjugate B' t = A' := by
        rw [hB'eq, BenderBranch.conjugate_conjugate, ht2, BenderBranch.conjugate_one]
      rw [← this, h]
      exact hKtt
    have hAcomp : IsComponentIn A (Subgroup.centralizer ({i} : Set G)) := hid.comp
    refine commutator_sup_sup_eq_bot' ?_ ?_ ?_ ?_
    · exact (BenderBranch.eq_or_commute_of_isComponentIn hAcomp hKc).resolve_left
        fun h => hA'A h.symm
    · exact (BenderBranch.eq_or_commute_of_isComponentIn hAcomp hBc).resolve_left
        fun h => hB'A h.symm
    · exact (BenderBranch.eq_or_commute_of_isComponentIn hKt hKc).resolve_left
        fun h => hA'B h.symm
    · exact (BenderBranch.eq_or_commute_of_isComponentIn hKt hBc).resolve_left
        fun h => hB'B h.symm
  · rw [hKPeq] at hne ⊢
    exact (BenderBranch.eq_or_commute_of_isComponentIn hid.comp hKc).resolve_left
      fun h => hne h.symm

theorem Ident2519.mem_normalizer_K_of_commute (hid : Ident2519 N t i Ki KP R2)
    (h : Lv2518 N t zK) (hi : Hyp2519 N i) {c : G} (hcS : c ∈ N.S) (hci : c * i = i * c) :
    c ∈ Subgroup.normalizer (N.K : Set G) := by
  by_contra hcK
  have hf := h.facts2511
  have hct : c * t = t * c := (N.t_comm_of_mem_S hf hcS).symm
  have hti : t * i = i * t := N.t_comm_of_mem_S hf hi.mem_S
  have hcKP : c ∉ Subgroup.normalizer (KP : Set G) := fun hc => hcK (hid.mem_normalizer_K hct hc)
  have hne : CFSG.conjugate KP c ≠ KP := fun e =>
    hcKP (BenderBranch.conjugate_eq_iff_mem_normalizer.mp e)
  have hcomm := hid.commutator_conj_eq_bot hti (N.t_mul_self' hf) hci hct hne
  have he : CFSG.Assembly.evenRank G ≤ 2 := hs.setting.qtke.2.2
  have hinv : c⁻¹ * i * c = i := by
    calc c⁻¹ * i * c = c⁻¹ * (i * c) := by group
      _ = c⁻¹ * (c * i) := by rw [hci]
      _ = i := by group
  have hCc : CFSG.conjugate (Subgroup.centralizer ({i} : Set G)) c =
      Subgroup.centralizer ({i} : Set G) := by
    rw [BenderBranch.conjugate_centralizer_singleton, hinv]
  have hord : orderOf i = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hi.sq_eq_one hi.ne_one
  refine Unc25K1.false_of_commuting_copy he (X := Subgroup.centralizer ({i} : Set G))
    (K := KP) (K' := CFSG.conjugate KP c) (pCoreOf_centralizer_ne_bot hord) hid.KP_le ?_ hcomm
    hid.three_rank ?_ (hid.center_three_conj c)
  · have := BenderBranch.conjugate_mono hid.KP_le c
    rwa [hCc] at this
  · rw [BenderBranch.card_conjugate]
    exact hid.three_dvd_card

end Norm

end CFSG.QuasithinUnique
