module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.QTwoProduct
public import CFSG.LocalAnalysis.EvenBN.Common.SwapUnique
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.QTwoEndgame

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem perfect_le_of_le_centralizer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {H : Subgroup G} (hH : H ≤ centralizer ({t} : Set G)) (hp : ⁅H, H⁆ = H) : H ≤ L := by
  have h1 : H ≤ L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) := by
    calc H = ⁅H, H⁆ := hp.symm
      _ ≤ ⁅centralizer ({t} : Set G), centralizer ({t} : Set G)⁆ := commutator_mono hH hH
      _ ≤ _ := h.commutator_le_sup_kernel d
  calc H = ⁅H, H⁆ := hp.symm
    _ ≤ L := h.commutator_le_of_le_sup_kernel h1

theorem ordTrialityD4_sq_lt (a : ℤ) (ha : 4 ≤ a) :
    (a ^ 6 * (a ^ 4 + a ^ 2 + 1) * (a ^ 3 - 1) * (a - 1)) ^ 2 <
      a ^ 12 * (a ^ 8 + a ^ 4 + 1) * (a ^ 6 - 1) * (a ^ 2 - 1) := by
  have e : a ^ 12 * (a ^ 8 + a ^ 4 + 1) * (a ^ 6 - 1) * (a ^ 2 - 1) -
      (a ^ 6 * (a ^ 4 + a ^ 2 + 1) * (a ^ 3 - 1) * (a - 1)) ^ 2 =
      a ^ 12 * (a - 1) * (a ^ 3 - 1) * (a ^ 4 + a ^ 2 + 1) *
        (2 * a * (a ^ 4 + 1) * (a ^ 2 - a + 1)) := by ring
  have h1 : 0 < a := by omega
  have h2 : 0 < a - 1 := by omega
  have h3 : 0 < a ^ 3 - 1 := by nlinarith [pow_pos h1 3, sq_nonneg (a - 1), sq_nonneg a]
  have h4 : 0 < a ^ 2 - a + 1 := by nlinarith
  have : 0 < a ^ 12 * (a - 1) * (a ^ 3 - 1) * (a ^ 4 + a ^ 2 + 1) *
      (2 * a * (a ^ 4 + 1) * (a ^ 2 - a + 1)) := by positivity
  linarith

theorem ordTrialityD4_lt_two_mul_sq (a : ℤ) (ha : 4 ≤ a) :
    a ^ 12 * (a ^ 8 + a ^ 4 + 1) * (a ^ 6 - 1) * (a ^ 2 - 1) <
      2 * (a ^ 6 * (a ^ 4 + a ^ 2 + 1) * (a ^ 3 - 1) * (a - 1)) ^ 2 := by
  have e : 2 * (a ^ 6 * (a ^ 4 + a ^ 2 + 1) * (a ^ 3 - 1) * (a - 1)) ^ 2 -
      a ^ 12 * (a ^ 8 + a ^ 4 + 1) * (a ^ 6 - 1) * (a ^ 2 - 1) =
      a ^ 12 * (a - 1) * (a ^ 3 - 1) * (a ^ 4 + a ^ 2 + 1) *
        (a ^ 8 - 3 * a ^ 7 + 3 * a ^ 6 - 4 * a ^ 5 + 2 * a ^ 4 - 4 * a ^ 3 + 3 * a ^ 2 - 3 * a +
          1) := by
    ring
  have h1 : 0 < a := by omega
  have h2 : 0 < a - 1 := by omega
  have h3 : 0 < a ^ 3 - 1 := by nlinarith [pow_pos h1 3, sq_nonneg (a - 1), sq_nonneg a]
  have hP : 0 < a ^ 8 - 3 * a ^ 7 + 3 * a ^ 6 - 4 * a ^ 5 + 2 * a ^ 4 - 4 * a ^ 3 + 3 * a ^ 2 -
      3 * a + 1 := by
    obtain ⟨z, rfl⟩ : ∃ z, a = z + 4 := ⟨a - 4, by ring⟩
    have hz : 0 ≤ z := by omega
    ring_nf
    positivity
  have : 0 < a ^ 12 * (a - 1) * (a ^ 3 - 1) * (a ^ 4 + a ^ 2 + 1) *
      (a ^ 8 - 3 * a ^ 7 + 3 * a ^ 6 - 4 * a ^ 5 + 2 * a ^ 4 - 4 * a ^ 3 + 3 * a ^ 2 - 3 * a +
        1) := by
    positivity
  linarith

theorem not_sq_dvd_ordTrialityD4 {q : ℕ} (hq : 2 ≤ q) :
    ¬ ordTrialityD4 q ^ 2 ∣ ordTrialityD4 (q ^ 2) := by
  intro hdvd
  set a : ℕ := q ^ 2 with ha
  have ha4 : 4 ≤ a := by nlinarith
  have hA : ordTrialityD4 q = a ^ 6 * (a ^ 4 + a ^ 2 + 1) * (a ^ 3 - 1) * (a - 1) := by
    unfold ordTrialityD4
    rw [show q ^ 12 = a ^ 6 by rw [ha, ← pow_mul], show q ^ 8 = a ^ 4 by rw [ha, ← pow_mul],
      show q ^ 4 = a ^ 2 by rw [ha, ← pow_mul], show q ^ 6 = a ^ 3 by rw [ha, ← pow_mul]]
  have hB : ordTrialityD4 (q ^ 2) =
      a ^ 12 * (a ^ 8 + a ^ 4 + 1) * (a ^ 6 - 1) * (a ^ 2 - 1) := rfl
  have h1a : 1 ≤ a := by omega
  have h1 : 1 ≤ a ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ a ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hlt1 := ordTrialityD4_sq_lt (a : ℤ) (by exact_mod_cast ha4)
  have hlt2 := ordTrialityD4_lt_two_mul_sq (a : ℤ) (by exact_mod_cast ha4)
  have c1 : ((ordTrialityD4 q : ℕ) : ℤ) ^ 2 < ((ordTrialityD4 (q ^ 2) : ℕ) : ℤ) := by
    rw [hA, hB]
    push_cast [Nat.cast_sub h1, Nat.cast_sub h1a, Nat.cast_sub h2, Nat.cast_sub h3]
    exact hlt1
  have c2 : ((ordTrialityD4 (q ^ 2) : ℕ) : ℤ) < 2 * ((ordTrialityD4 q : ℕ) : ℤ) ^ 2 := by
    rw [hA, hB]
    push_cast [Nat.cast_sub h1, Nat.cast_sub h1a, Nat.cast_sub h2, Nat.cast_sub h3]
    exact hlt2
  have d1 : ordTrialityD4 q ^ 2 < ordTrialityD4 (q ^ 2) := by exact_mod_cast c1
  have d2 : ordTrialityD4 (q ^ 2) < 2 * ordTrialityD4 q ^ 2 := by exact_mod_cast c2
  have hne : ordTrialityD4 (q ^ 2) ≠ 0 := by omega
  have := Nat.eq_of_dvd_of_lt_two_mul hne hdvd d2
  omega

namespace PerfectLeSup

section Generic

variable {G : Type*} [Group G]

theorem commutator_le_of_relIndex_eq_two {H K : Subgroup G} (h2 : H.relIndex K = 2) :
    ⁅K, K⁆ ≤ H := by
  have hsq : ∀ a ∈ K, a * a ∈ H := fun a ha =>
    mem_subgroupOf.1 (Subgroup.mul_self_mem_of_index_two (H := H.subgroupOf K) h2 ⟨a, ha⟩)
  rw [commutator_le]
  intro a ha b hb
  have e : ⁅a, b⁆ = (a * a) * ((a⁻¹ * b) * (a⁻¹ * b)) * (b⁻¹ * b⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact mul_mem (mul_mem (hsq a ha) (hsq _ (mul_mem (inv_mem ha) hb))) (hsq _ (inv_mem hb))

theorem mul_comm_of_inf_centralizer_eq_bot [Finite G] {A : Subgroup G} {x : G}
    (hx : x ∈ normalizer (A : Set G)) (hx2 : x * x = 1)
    (hC : A ⊓ centralizer ({x} : Set G) = ⊥) : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hconj : ∀ b ∈ A, x * b * x⁻¹ ∈ A := fun b hb => (mem_normalizer_iff.1 hx b).1 hb
  let φ : A → A := fun b => ⟨(b : G)⁻¹ * (x * b * x⁻¹), mul_mem (inv_mem b.2) (hconj b b.2)⟩
  have hinj : Function.Injective φ := by
    intro b b' hbb
    have e : (b : G)⁻¹ * (x * b * x⁻¹) = (b' : G)⁻¹ * (x * b' * x⁻¹) := congrArg Subtype.val hbb
    have e1 : (b' : G) * (b : G)⁻¹ * x = x * ((b' : G) * (b : G)⁻¹) := by
      calc (b' : G) * (b : G)⁻¹ * x = b' * ((b : G)⁻¹ * (x * b * x⁻¹)) * x * (b : G)⁻¹ := by
            group
        _ = b' * ((b' : G)⁻¹ * (x * b' * x⁻¹)) * x * (b : G)⁻¹ := by rw [e]
        _ = x * ((b' : G) * (b : G)⁻¹) := by group
    have hc : (b' : G) * (b : G)⁻¹ ∈ A ⊓ centralizer ({x} : Set G) :=
      mem_inf.2 ⟨mul_mem b'.2 (inv_mem b.2), mem_centralizer_singleton_iff.2 e1⟩
    rw [hC, mem_bot, mul_inv_eq_one] at hc
    exact Subtype.ext hc.symm
  have hsurj := Finite.injective_iff_surjective.1 hinj
  have hinv : ∀ a ∈ A, x * a * x⁻¹ = a⁻¹ := by
    intro a ha
    obtain ⟨b, hb⟩ := hsurj ⟨a, ha⟩
    have e : a = (b : G)⁻¹ * (x * b * x⁻¹) := (congrArg Subtype.val hb).symm
    rw [e, hxinv]
    calc x * ((b : G)⁻¹ * (x * b * x)) * x = x * (b : G)⁻¹ * x * b * (x * x) := by group
      _ = x⁻¹ * (b : G)⁻¹ * x⁻¹ * b := by rw [hx2, mul_one, hxinv]
      _ = ((b : G)⁻¹ * (x * b * x))⁻¹ := by group
  intro a ha b hb
  have h1 := hinv (a * b) (mul_mem ha hb)
  rw [show x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) by group, hinv a ha, hinv b hb,
    mul_inv_rev] at h1
  calc a * b = (b⁻¹ * a⁻¹)⁻¹ := by group
    _ = (a⁻¹ * b⁻¹)⁻¹ := by rw [h1]
    _ = b * a := by group

theorem exists_mul_centralizer_of_perfect {X M : Subgroup G} [Group.IsSolvable (Outer X)]
    (hM : ⁅M, M⁆ = M) (hMX : M ≤ normalizer (X : Set G)) {x : G} (hx : x ∈ M) :
    ∃ a ∈ X, ∃ c ∈ centralizer (X : Set G), x = a * c := by
  haveI : Group.IsPerfect M := (Common.isPerfect_subgroup_iff_commutator_eq M).2 hM
  obtain ⟨a, ha⟩ := CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner
    (X.normalizerMonoidHom.comp (inclusion hMX)) ⟨x, hx⟩
  refine ⟨a, a.2, (a : G)⁻¹ * x, mem_centralizer_iff.2 fun g hg => ?_, by group⟩
  have h1 : x * g * x⁻¹ = a * g * (a : G)⁻¹ :=
    congrArg (fun f : MulAut X => ((f ⟨g, hg⟩ : X) : G)) ha
  calc g * ((a : G)⁻¹ * x) = (a : G)⁻¹ * (a * g * (a : G)⁻¹) * x := by group
    _ = (a : G)⁻¹ * (x * g * x⁻¹) * x := by rw [h1]
    _ = (a : G)⁻¹ * x * g := by group

end Generic

end PerfectLeSup

theorem perfect_le_sup_of_le_normalizer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {G₀ : Subgroup G} (e : G₀ ≃* L) (hq : CFSG.Open.IsQuasisimple G₀)
    (h₁₂ : G₀.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₀ : Set G))
    (hLG : L ≤ G₀ ⊔ G₀.map (MulAut.conj t).toMonoidHom) {H : Subgroup G}
    (hH : H ≤ normalizer ((G₀ ⊔ G₀.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hp : ⁅H, H⁆ = H) : H ≤ G₀ ⊔ G₀.map (MulAut.conj t).toMonoidHom := by
  have htt := h.t_mul_t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  set G₂ : Subgroup G := G₀.map (MulAut.conj t).toMonoidHom with hG₂
  obtain ⟨hperf, hbot, hn₁⟩ :=
    SeitzReduction.F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple hq
  have hn₂ := SeitzReduction.F4Pilot.dichotomy_map_mulAut (MulAut.conj t) hn₁
  have hcomm : ∀ a ∈ G₀, ∀ b ∈ G₂, a * b = b * a := fun a ha b hb =>
    mem_centralizer_iff.1 (h₁₂ hb) a ha
  have hne : G₀ ≠ G₂ := by
    intro e
    apply hbot
    have h11 : G₀ ≤ centralizer (G₀ : Set G) := by
      calc G₀ = G₂ := e
        _ ≤ centralizer (G₀ : Set G) := h₁₂
    rw [← hperf, commutator_eq_bot_iff_le_centralizer.2 h11]
  have hperm : ∀ x ∈ normalizer ((G₀ ⊔ G₂ : Subgroup G) : Set G),
      G₀.map (MulAut.conj x).toMonoidHom = G₀ ∨ G₀.map (MulAut.conj x).toMonoidHom = G₂ :=
    fun x hx => SeitzReduction.F4Pilot.map_conj_eq_or_eq_of_perfect h₁₂ hperf hbot hn₁ hn₂ hx
  have hHN : H ≤ normalizer (G₀ : Set G) ⊓ normalizer (G₂ : Set G) := by
    have h2 := SeitzReduction.F4Pilot.relIndex_inf_normalizer_eq_two_of_swap htt rfl hne hperm
    rw [← SeitzReduction.F4Pilot.inf_normalizer_eq_of_swap htt rfl hne hperm]
    calc H = ⁅H, H⁆ := hp.symm
      _ ≤ _ := (commutator_mono hH hH).trans
        (PerfectLeSup.commutator_le_of_relIndex_eq_two h2)
  haveI hsolvL : Group.IsSolvable (Outer L) := by
    haveI := mulAutConj_range_normal (G := ↥L)
    haveI : IsCyclic (Outer L) := d.isCyclic_quotient_range_conj
    infer_instance
  haveI hsolv₀ : Group.IsSolvable (Outer G₀) :=
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv e.symm
  let e₂ : G₀ ≃* G₂ := Subgroup.equivMapOfInjective G₀ _ (MulAut.conj t).injective
  haveI hsolv₂ : Group.IsSolvable (Outer G₂) :=
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv e₂
  set C₀ : Subgroup G := centralizer (G₀ : Set G) ⊓ centralizer (G₂ : Set G) with hC₀
  have hmemG₂ : ∀ a ∈ G₀, t * a * t⁻¹ ∈ G₂ := fun a ha => ⟨a, ha, rfl⟩
  have hmemG₀ : ∀ b ∈ G₂, t⁻¹ * b * t ∈ G₀ := by
    rintro _ ⟨a, ha, rfl⟩
    change t⁻¹ * (t * a * t⁻¹) * t ∈ G₀
    rw [show t⁻¹ * (t * a * t⁻¹) * t = a by group]
    exact ha
  have htC₀ : t ∈ normalizer (C₀ : Set G) := by
    refine mem_normalizer_fintype fun c hc => ?_
    have hc₁ := (mem_inf.1 hc).1
    have hc₂ := (mem_inf.1 hc).2
    refine mem_inf.2 ⟨mem_centralizer_iff.2 fun a ha => ?_, mem_centralizer_iff.2 fun b hb => ?_⟩
    · have hat : t⁻¹ * a * t ∈ G₂ := by
        rw [show t⁻¹ * a * t = t * a * t⁻¹ by rw [htinv]]
        exact hmemG₂ a ha
      have := mem_centralizer_iff.1 hc₂ _ hat
      calc a * (t * c * t⁻¹) = t * ((t⁻¹ * a * t) * c) * t⁻¹ := by group
        _ = t * (c * (t⁻¹ * a * t)) * t⁻¹ := by rw [this]
        _ = t * c * t⁻¹ * a := by group
    · have hbt := hmemG₀ b hb
      have := mem_centralizer_iff.1 hc₁ _ hbt
      calc b * (t * c * t⁻¹) = t * ((t⁻¹ * b * t) * c) * t⁻¹ := by group
        _ = t * (c * (t⁻¹ * b * t)) * t⁻¹ := by rw [this]
        _ = t * c * t⁻¹ * b := by group
  have htG₀ : t ∉ centralizer (G₀ : Set G) := by
    intro ht
    apply hne
    refine le_antisymm (fun a ha => ?_) ?_
    · have e : t * a * t⁻¹ = a := by
        rw [← mem_centralizer_iff.1 ht a ha, mul_inv_cancel_right]
      exact e ▸ hmemG₂ a ha
    · rintro _ ⟨a, ha, rfl⟩
      change t * a * t⁻¹ ∈ G₀
      rw [← mem_centralizer_iff.1 ht a ha, mul_inv_cancel_right]
      exact ha
  have hC₀t : C₀ ⊓ centralizer ({t} : Set G) = ⊥ := by
    refine eq_bot_iff.2 fun c hc => ?_
    obtain ⟨hcC₀, hct⟩ := mem_inf.1 hc
    have hcL : c ∈ centralizer (L : Set G) := by
      refine mem_centralizer_iff.2 fun l hl => ?_
      have hle : G₀ ⊔ G₂ ≤ centralizer ({c} : Set G) := sup_le
        (fun a ha => mem_centralizer_singleton_iff.2
          (mem_centralizer_iff.1 (mem_inf.1 hcC₀).1 a ha))
        (fun b hb => mem_centralizer_singleton_iff.2
          (mem_centralizer_iff.1 (mem_inf.1 hcC₀).2 b hb))
      exact mem_centralizer_singleton_iff.1 (hle (hLG hl))
    have hk : c ∈ zpowers t := (h.centralizer_L_inf_of_data d).le (mem_inf.2 ⟨hcL, hct⟩)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hk
    rcases h.zpow_eq_one_or_eq k with h1 | h1
    · rw [h1]
      exact one_mem _
    · rw [h1] at hcC₀
      exact absurd (mem_inf.1 hcC₀).1 htG₀
  have hab := PerfectLeSup.mul_comm_of_inf_centralizer_eq_bot htC₀ htt hC₀t
  have hdec : ∀ x ∈ H, ∃ g ∈ G₀ ⊔ G₂, ∃ c ∈ C₀, x = g * c := by
    intro x hx
    obtain ⟨a₁, ha₁, c₁, hc₁, e₁⟩ :=
      PerfectLeSup.exists_mul_centralizer_of_perfect (X := G₀) hp (hHN.trans inf_le_left) hx
    obtain ⟨a₂, ha₂, c₂, hc₂, e₂⟩ :=
      PerfectLeSup.exists_mul_centralizer_of_perfect (X := G₂) hp (hHN.trans inf_le_right) hx
    have h12 : a₁ * a₂ = a₂ * a₁ := hcomm a₁ ha₁ a₂ ha₂
    refine ⟨a₁ * a₂, mul_mem (mem_sup_left ha₁) (mem_sup_right ha₂), (a₁ * a₂)⁻¹ * x,
      mem_inf.2 ⟨?_, ?_⟩, by group⟩
    · have e : (a₁ * a₂)⁻¹ * x = a₂⁻¹ * c₁ := by rw [e₁]; group
      rw [e]
      exact mul_mem (inv_mem (mem_centralizer_iff.2 fun g hg => hcomm g hg a₂ ha₂)) hc₁
    · have e : (a₁ * a₂)⁻¹ * x = a₁⁻¹ * c₂ := by rw [h12, e₂]; group
      rw [e]
      exact mul_mem (inv_mem (mem_centralizer_iff.2 fun g hg => (hcomm a₁ ha₁ g hg).symm)) hc₂
  have hcen : ∀ c ∈ C₀, ∀ g ∈ G₀ ⊔ G₂, c * g = g * c := by
    intro c hc g hg
    have hle : G₀ ⊔ G₂ ≤ centralizer ({c} : Set G) := sup_le
      (fun a ha => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (mem_inf.1 hc).1 a ha))
      (fun b hb => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (mem_inf.1 hc).2 b hb))
    exact (mem_centralizer_singleton_iff.1 (hle hg)).symm
  calc H = ⁅H, H⁆ := hp.symm
    _ ≤ G₀ ⊔ G₂ := by
      rw [commutator_le]
      intro x hx y hy
      obtain ⟨g, hg, c, hc, rfl⟩ := hdec x hx
      obtain ⟨g', hg', c', hc', rfl⟩ := hdec y hy
      rw [commutatorElement_mul_mul_of_commute' (hcen c hc g' hg') (hab c hc c' hc')
        (hcen c' hc' g hg), commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hg hg') (inv_mem hg)) (inv_mem hg')

section Fixed


open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
open CFSG.ComponentClassification.OuterAutomorphisms (inner) in
theorem lieModel_fixedSubgroup_of_outer_involution {X : Type} [Group X] {f : ℕ} (hf : 1 ≤ f)
    (hX : CFSG.Blueprint.LieModel X .trialityD4 0 2 f) (α : MulAut X) (hα2 : α ^ 2 = 1)
    (hαo : α ∉ (MulAut.conj : X →* MulAut X).range) :
    Even f ∧ CFSG.Blueprint.LieModel ↥(α.toMonoidHom.eqLocus (MonoidHom.id X)) .trialityD4 0 2
      (f / 2) := by
  have htw : TwistedChevalleyModel X .D4 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hX).2
  obtain ⟨M, _, _, σ, hM, hσ, ⟨E⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf htw
  have hβ2 : MulAut.congr E α ^ 2 = 1 := by
    rw [← map_pow, hα2, map_one]
  have hβo : MulAut.congr E α ∉ inner (graphFixedRootGroup TwistTag.D4 M σ.toRingHom) := by
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  exact ⟨(even_triality_outer_involutions_canonical_field hf M hM σ hσ _ hβ2 hβo).1,
    LieType.CurtisTits.lieModel_of_mulEquiv
      (ComponentClassification.CatLeafProof.fixedSubgroupCongrEquiv E α).symm
      (lieModel_fixedSubgroup_outer_involution hf hM σ hσ _ hβ2 hβo)⟩

end Fixed

section Cert


open CFSG.Blueprint CFSG.LieType.Steinberg.TwistedD4 in
theorem perfect_and_card_of_lieModel {Y : Type} [Group Y] {e : ℕ} (he : 1 ≤ e)
    (hY : CFSG.Blueprint.LieModel Y .trialityD4 0 2 e) :
    Group.IsPerfect Y ∧ Nat.card Y = ordTrialityD4 (2 ^ e) := by
  obtain ⟨d⟩ := nonempty_trialityD4Data_of_lieModel he hY
  refine ⟨?_, by rw [d.card_eq]; unfold ordTrialityD4; ring⟩
  obtain ⟨-, K, _, _, hK, σ, hσq, ⟨eqv⟩⟩ : ChevalleyExceptionalModel Y .trialityD4 2 e :=
    GH74.chevalleyExceptionalModel_of_lieModel (by decide) hY
  have hq : 2 ≤ 2 ^ e :=
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hK' : Nat.card K = (2 ^ e) ^ 3 := hK
  have hperf : Group.IsPerfect (twistedGroup σ) := twistedGroup_isPerfect_of_card hq hK' hσq
  let eD := twistedGroupEquivDerived σ hq hK' hσq
  have h1 : Group.IsPerfect ↥⁅twistedFixedGroup .D4 K σ, twistedFixedGroup .D4 K σ⁆ :=
    Group.IsPerfect.ofSurjective (f := eD.toMonoidHom) eD.surjective
  have h2 : Group.IsPerfect (DerivedCentralQuotient (twistedFixedGroup .D4 K σ)) := inferInstance
  exact Group.IsPerfect.ofSurjective (f := eqv.symm.toMonoidHom) eqv.symm.surjective

theorem inner_or_outer_D4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) {X : Subgroup G}
    (e : L ≃* X) {x : G} (hxX : x ∈ normalizer (X : Set G)) (hx2 : x * x = 1) :
    (∃ E : Subgroup G, E ≤ X ∧ E ≤ centralizer ({x} : Set G) ∧ IsElemAbelian 2 E ∧
        Nat.card E = (2 ^ f) ^ 5) ∨
      (Even f ∧ ∃ D : Subgroup G, D ≤ X ∧ D ≤ centralizer ({x} : Set G) ∧ ⁅D, D⁆ = D ∧
        Nat.card D = ordTrialityD4 (2 ^ (f / 2)) ∧
        ∃ E : Subgroup G, E ≤ D ∧ IsElemAbelian 2 E ∧ Nat.card E = (2 ^ (f / 2)) ^ 5) := by
  classical
  obtain ⟨α, hαg⟩ : ∃ α : MulAut X, ∀ a : X, ((α a : X) : G) = x * a * x⁻¹ :=
    ⟨X.normalizerMonoidHom ⟨x, hxX⟩, fun a => rfl⟩
  have hα2 : α ^ 2 = 1 := by
    refine MulEquiv.ext fun a => Subtype.ext ?_
    change ((α (α a) : X) : G) = ((a : X) : G)
    rw [hαg, hαg]
    calc x * (x * (a : G) * x⁻¹) * x⁻¹ = (x * x) * (a : G) * (x * x)⁻¹ := by group
      _ = a := by rw [hx2, inv_one, one_mul, mul_one]
  let dX : TrialityD4Data X (2 ^ f) := d.ofMulEquiv e
  have hZ : center X = ⊥ := dX.center_eq_bot_of_data
  by_cases hin : α ∈ (MulAut.conj : X →* MulAut X).range
  ·
    left
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 hin
    have ha2 : a * a = 1 := by
      have hz : a * a ∈ center X := by
        rw [mem_center_iff]
        intro b
        have h1 : (MulAut.conj (a * a)) b = b := by
          rw [map_mul, ha, MulAut.mul_apply]
          have := congrArg (fun β : MulAut X => β b) hα2
          simpa [sq] using this
        rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at h1
        exact h1.symm
      rw [hZ, mem_bot] at hz
      exact hz
    have ha2' : (a : G) * a = 1 := congrArg Subtype.val ha2
    obtain ⟨E, hE, haE, hEX, hEcard⟩ := dX.exists_isElemAbelian_le_of_mem a.2 ha2'
    refine ⟨E, hEX, ?_, hE, hEcard⟩
    intro b hb
    rw [mem_centralizer_singleton_iff]
    have hba : b * (a : G) = (a : G) * b :=
      mem_centralizer_singleton_iff.1 (le_centralizer_of_isElemAbelian_D4 hE haE hb)
    have h1 : x * b * x⁻¹ = b := by
      calc x * b * x⁻¹ = ((α ⟨b, hEX hb⟩ : X) : G) := (hαg ⟨b, hEX hb⟩).symm
        _ = ((MulAut.conj a ⟨b, hEX hb⟩ : X) : G) := by rw [ha]
        _ = (a : G) * b * (a : G)⁻¹ := rfl
        _ = b := by rw [← hba]; group
    calc b * x = (x * b * x⁻¹) * x := by rw [h1]
      _ = x * b := by group
  ·
    right
    have hX : CFSG.Blueprint.LieModel X .trialityD4 0 2 f := h.model.of_mulEquiv e
    obtain ⟨hfe, hF⟩ := lieModel_fixedSubgroup_of_outer_involution h.one_le hX α hα2 hin
    refine ⟨hfe, ?_⟩
    have hf2 : 1 ≤ f / 2 := by
      have := h.one_le
      obtain ⟨k, hk⟩ := hfe
      omega
    obtain ⟨hFp, hFc⟩ := perfect_and_card_of_lieModel hf2 hF
    set F : Subgroup X := α.toMonoidHom.eqLocus (MonoidHom.id X)
    have hFcomm : ⁅F, F⁆ = F := Subgroup.isPerfect_iff.1 hFp
    obtain ⟨dF⟩ := nonempty_trialityD4Data_of_lieModel hf2 hF
    obtain ⟨E₀, hE₀, -, hE₀c⟩ := dF.exists_isElemAbelian_of_mul_self (y := 1) (mul_one 1)
    refine ⟨F.map X.subtype, map_subtype_le F, ?_, ?_, ?_,
      (E₀.map F.subtype).map X.subtype, map_mono (map_subtype_le E₀), ?_, ?_⟩
    ·
      rintro _ ⟨y, hy, rfl⟩
      rw [mem_centralizer_singleton_iff]
      have hyα : α y = y := hy
      have h1 : x * (y : G) * x⁻¹ = y := by
        rw [← hαg, hyα]
      show (y : G) * x = x * (y : G)
      calc (y : G) * x = (x * (y : G) * x⁻¹) * x := by rw [h1]
        _ = x * (y : G) := by group
    · rw [← map_commutator, hFcomm]
    · rw [card_map_of_injective X.subtype_injective]
      exact hFc
    · exact CFSG.SectionRank.isElemAbelian_map
        (CFSG.SectionRank.isElemAbelian_map hE₀ F.subtype) X.subtype
    · rw [card_map_of_injective X.subtype_injective, card_map_of_injective F.subtype_injective,
        hE₀c]

theorem false_of_normalizes_both (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {G₀ : Subgroup G} (e : G₀ ≃* L)
    (h₁₂ : G₀.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₀ : Set G)) (g : G)
    (h₁ : t ∈ normalizer ((G₀.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G))
    (h₂ : t ∈ normalizer (((G₀.map (MulAut.conj t).toMonoidHom).map (MulAut.conj g).toMonoidHom :
      Subgroup G) : Set G)) : False := by
  have htt := h.t_mul_t
  set X₁ : Subgroup G := G₀.map (MulAut.conj g).toMonoidHom with hX₁
  set X₂ : Subgroup G :=
    (G₀.map (MulAut.conj t).toMonoidHom).map (MulAut.conj g).toMonoidHom with hX₂
  let e₁ : L ≃* X₁ := e.symm.trans
    (G₀.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
  let e₂ : L ≃* X₂ := e.symm.trans
    ((G₀.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).trans
      ((G₀.map (MulAut.conj t).toMonoidHom).equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective))
  have hcomm : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    have hab := mem_centralizer_iff.1 (h₁₂ ⟨b, hb, rfl⟩) a ha
    change (MulAut.conj g) a * (MulAut.conj g) ((MulAut.conj t) b) =
      (MulAut.conj g) ((MulAut.conj t) b) * (MulAut.conj g) a
    rw [← map_mul, ← map_mul]
    exact congrArg (MulAut.conj g) hab
  have hinf : X₁ ⊓ X₂ = ⊥ := by
    refine le_bot_iff.1 fun z hz => ?_
    have hzc : (e₁.symm ⟨z, hz.1⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro l
      apply e₁.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subtype.ext (hcomm _ (e₁ l).2 z hz.2)
    rw [h.center_eq, mem_bot] at hzc
    have hz1 : (⟨z, hz.1⟩ : X₁) = 1 := by
      have := congrArg e₁ hzc
      rwa [MulEquiv.apply_symm_apply, map_one] at this
    exact mem_bot.2 (congrArg Subtype.val hz1)
  have key : ∀ E₁ E₂ : Subgroup G, E₁ ≤ X₁ → E₂ ≤ X₂ → E₁ ≤ centralizer ({t} : Set G) →
      E₂ ≤ centralizer ({t} : Set G) → IsElemAbelian 2 E₁ → IsElemAbelian 2 E₂ →
      2 * (2 ^ f) ^ 5 < Nat.card E₁ * Nat.card E₂ → False := by
    intro E₁ E₂ hE₁ hE₂ hE₁t hE₂t hE₁a hE₂a hlt
    have hc : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a := fun a ha b hb =>
      hcomm a (hE₁ ha) b (hE₂ hb)
    have hEinf : E₁ ⊓ E₂ = ⊥ := by
      refine le_bot_iff.1 fun z hz => ?_
      have : z ∈ X₁ ⊓ X₂ := ⟨hE₁ hz.1, hE₂ hz.2⟩
      rwa [hinf] at this
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E₁ E₂ hc
    rw [hEinf, Subgroup.card_bot, mul_one] at hcard
    have hEt : E₂ ≤ centralizer (E₁ : Set G) := fun b hb =>
      mem_centralizer_iff.2 fun a ha => hc a ha b hb
    have : CFSG.IsElementaryAbelian 2 E₁ := isElementaryAbelian_of_isElemAbelian' hE₁a
    have : CFSG.IsElementaryAbelian 2 E₂ := isElementaryAbelian_of_isElemAbelian' hE₂a
    have hEE : IsElemAbelian 2 (E₁ ⊔ E₂ : Subgroup G) :=
      isElemAbelian_of_isElementaryAbelian' (CFSG.IsElementaryAbelian.sup_of_le_centralizer hEt)
    obtain ⟨hb1, hb2⟩ := h.card_le_of_isElemAbelian d (sup_le hE₁t hE₂t) hEE
    have hle := hb1.trans (Nat.mul_le_mul_left 2 hb2)
    rw [hcard] at hle
    exact absurd hlt (not_lt.2 hle)
  have hq5 : 2 * (2 ^ f) ^ 5 < (2 ^ f) ^ 5 * (2 ^ f) ^ 5 := two_mul_pow_five_lt_D4 d.two_le_q
  have hApos : 0 < (2 ^ f) ^ 5 := by positivity
  have hmixed : Even f → 2 * (2 ^ f) ^ 5 < (2 ^ f) ^ 5 * (2 ^ (f / 2)) ^ 5 := by
    intro hfe
    have hf2 : 1 ≤ f / 2 := by
      have := h.one_le
      obtain ⟨k, hk⟩ := hfe
      omega
    have h2 : 2 < (2 ^ (f / 2)) ^ 5 := by
      have : 2 ≤ 2 ^ (f / 2) := Nat.le_self_pow (by omega) 2 |>.trans' (by norm_num) |>.trans le_rfl
      calc 2 < 2 ^ 5 := by norm_num
        _ ≤ (2 ^ (f / 2)) ^ 5 := Nat.pow_le_pow_left this 5
    calc 2 * (2 ^ f) ^ 5 = (2 ^ f) ^ 5 * 2 := by ring
      _ < (2 ^ f) ^ 5 * (2 ^ (f / 2)) ^ 5 := Nat.mul_lt_mul_of_pos_left h2 hApos
  rcases inner_or_outer_D4 h d e₁ h₁ htt with
      ⟨E₁, hE₁X, hE₁t, hE₁a, hE₁c⟩ |
        ⟨hfe, D₁, hD₁X, hD₁t, hD₁p, hD₁c, E₁, hE₁D, hE₁a, hE₁c⟩ <;>
    rcases inner_or_outer_D4 h d e₂ h₂ htt with
      ⟨E₂, hE₂X, hE₂t, hE₂a, hE₂c⟩ |
        ⟨hfe', D₂, hD₂X, hD₂t, hD₂p, hD₂c, E₂, hE₂D, hE₂a, hE₂c⟩
  · exact key E₁ E₂ hE₁X hE₂X hE₁t hE₂t hE₁a hE₂a (by rw [hE₁c, hE₂c]; exact hq5)
  · refine key E₁ E₂ hE₁X (hE₂D.trans hD₂X) hE₁t (hE₂D.trans hD₂t) hE₁a hE₂a ?_
    rw [hE₁c, hE₂c]
    exact hmixed hfe'
  · refine key E₁ E₂ (hE₁D.trans hD₁X) hE₂X (hE₁D.trans hD₁t) hE₂t hE₁a hE₂a ?_
    rw [hE₁c, hE₂c]
    have := hmixed hfe
    linarith [mul_comm ((2 ^ f) ^ 5) ((2 ^ (f / 2)) ^ 5)]
  ·
    have hc : ∀ a ∈ D₁, ∀ b ∈ D₂, a * b = b * a := fun a ha b hb =>
      hcomm a (hD₁X ha) b (hD₂X hb)
    have hDinf : D₁ ⊓ D₂ = ⊥ := by
      refine le_bot_iff.1 fun z hz => ?_
      have : z ∈ X₁ ⊓ X₂ := ⟨hD₁X hz.1, hD₂X hz.2⟩
      rwa [hinf] at this
    have hperf : ⁅D₁ ⊔ D₂, D₁ ⊔ D₂⁆ = D₁ ⊔ D₂ :=
      le_antisymm (commutator_le_self _)
        (sup_le (hD₁p.ge.trans (commutator_mono le_sup_left le_sup_left))
          (hD₂p.ge.trans (commutator_mono le_sup_right le_sup_right)))
    have hsub : D₁ ⊔ D₂ ≤ L := perfect_le_of_le_centralizer h d (sup_le hD₁t hD₂t) hperf
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute D₁ D₂ hc
    rw [hDinf, Subgroup.card_bot, mul_one, hD₁c, hD₂c] at hcard
    have hdvd := Subgroup.card_dvd_of_le hsub
    rw [hcard] at hdvd
    have hf2 : 2 ≤ 2 ^ (f / 2) := by
      have := h.one_le
      obtain ⟨k, hk⟩ := hfe
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (f / 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hq2 : (2 ^ (f / 2)) ^ 2 = 2 ^ f := by
      rw [← pow_mul]
      obtain ⟨k, hk⟩ := hfe
      congr 1
      omega
    refine not_sq_dvd_ordTrialityD4 hf2 ?_
    rw [hq2, sq]
    convert hdvd using 1
    unfold ordTrialityD4
    rw [d.card_eq]
    ring

theorem false_of_productConfig (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {G₀ : Subgroup G} (hcomm : ⁅G₀, G₀.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    [Group.IsPerfect G₀]
    (hL : (Common.diagonalHom G₀ t hcomm).range = L)
    (hN : normalizer ((yamadaR d t : Subgroup G) : Set G) ≤
      normalizer ((G₀ ⊔ G₀.map (MulAut.conj t⁻¹).toMonoidHom : Subgroup G) : Set G)) : False := by
  have := h.simple
  have htt := h.t_mul_t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  obtain ⟨-, e, -⟩ := h.yamada_7_25 d hcomm hL
  haveI hLq : IsSimpleGroup (L ⧸ center L) := h.std.1.2
  have hLs : IsSimpleGroup L :=
    ((QuotientGroup.quotientMulEquivOfEq h.center_eq).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  have hLab : ¬ ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := by
    intro hc
    obtain ⟨x, hx, y, hy, hxy⟩ := h.exists_mul_ne_mul_of_mem_L
    exact hxy (hc x hx y hy)
  have hLeven : Even (Nat.card L) := by
    rw [d.card_eq]
    have h2 : Even ((2 ^ f) ^ 12) :=
      Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by have := h.one_le; omega⟩, by norm_num⟩
    exact ((h2.mul_right _).mul_right _).mul_right _
  have hZ0 : center G₀ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxe : e x ∈ center L := by
      rw [mem_center_iff]
      intro l
      obtain ⟨a, rfl⟩ := e.surjective l
      rw [← map_mul, ← map_mul, mem_center_iff.1 hx a]
    rw [h.center_eq, mem_bot] at hxe
    exact mem_bot.2 (e.injective (by rw [hxe, map_one]))
  have hZ : Odd (Nat.card (center G₀)) := by
    rw [hZ0, Subgroup.card_bot]
    exact odd_one
  have hq : CFSG.Open.IsQuasisimple G₀ := by
    refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
    exact (((QuotientGroup.quotientMulEquivOfEq hZ0).trans QuotientGroup.quotientBot).trans
      e).symm.symm.isSimpleGroup
  have h₁₂ : G₀.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₀ : Set G) := by
    have h1 : G₀.map (MulAut.conj t⁻¹).toMonoidHom ≤ centralizer (G₀ : Set G) := by
      rw [commutator_comm] at hcomm
      exact commutator_eq_bot_iff_le_centralizer.1 hcomm
    rwa [htinv] at h1
  have hδ : ∀ x ∈ G₀, x * (t * x * t⁻¹) ∈ L := by
    intro x hx
    rw [← hL]
    exact ⟨⟨x, hx⟩, by rw [Common.diagonalHom_apply, htinv]⟩
  have hsurj : ∀ y ∈ L, ∃ x ∈ G₀, x * (t * x * t⁻¹) = y := by
    intro y hy
    rw [← hL] at hy
    obtain ⟨⟨x, hx⟩, hxy⟩ := hy
    refine ⟨x, hx, ?_⟩
    rw [← hxy, Common.diagonalHom_apply, htinv]
  have hLG : L ≤ G₀ ⊔ G₀.map (MulAut.conj t).toMonoidHom := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hsurj y hy
    exact mul_mem (mem_sup_left hx) (mem_sup_right ⟨x, hx, rfl⟩)
  have hR : IsSylowOf 2 (yamadaR d t) (L ⊔ zpowers t) := by
    have := h.isSylowOf_yamadaR d
    rwa [h.centralizer_L_inf_of_data d] at this
  have hNR : normalizer ((yamadaR d t : Subgroup G) : Set G) ≤
      normalizer ((G₀ ⊔ G₀.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
    simpa only [htinv] using hN
  exact Common.false_of_swap_configuration h.ht hLs hLab hLeven h.L_le_centralizer
    (fun H hH hp => perfect_le_of_le_centralizer h d hH hp) hq hZ h₁₂ hδ hsurj hR hNR
    (fun H hH hp => perfect_le_sup_of_le_normalizer h d e hq h₁₂ hLG hH hp)
    (fun g h₁ h₂ => false_of_normalizes_both h d e h₁₂ g h₁ h₂)

end Cert

end CFSG.LocalAnalysis.EvenBN.TrialityD4
