module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Rank
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitSevenP0

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X]

structure A7Data (t : X) (L : Subgroup X) where
  config : Config t L
  syl : Sylow 2 ↥(centralizer ({t} : Set X))
  ψ : ↥(Config.sylowIn syl) →* Perm (Fin 7)
  ψ_eq_one_iff : ∀ g : ↥(Config.sylowIn syl), ψ g = 1 ↔ (g : X) ∈ coreActionKernel L
  ψ_mem_alternatingGroup : ∀ g : ↥(Config.sylowIn syl), (g : X) ∈ L →
    ψ g ∈ alternatingGroup (Fin 7)
  ψ_mem_P0 : ∀ g : ↥(Config.sylowIn syl), ψ g ∈ P0
  exists_ψ_eq : ∀ σ ∈ R0, ∃ g : ↥(Config.sylowIn syl), (g : X) ∈ L ∧ ψ g = σ

@[expose] noncomputable def Config.a7Data [Finite X] {t : X} {L : Subgroup X} (h : Config t L)
    (e : L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7))
    (T : Sylow 2 ↥(centralizer ({t} : Set X))) : A7Data t L :=
  have hex := h.exists_good_action e T
  have hTN : Config.sylowIn T ≤ normalizer (L : Set X) :=
    (Config.sylowIn_le T).trans h.le_normalizer
  { config := h
    syl := T
    ψ := (Classical.choose hex).comp (Subgroup.inclusion hTN)
    ψ_eq_one_iff := fun g => (Classical.choose_spec hex).1 _
    ψ_mem_alternatingGroup := fun _ hg => (Classical.choose_spec hex).2.1 _ hg
    ψ_mem_P0 := fun g => (Classical.choose_spec hex).2.2.1 _ g.2
    exists_ψ_eq := fun σ hσ => by
      obtain ⟨g, hg, hgσ⟩ := (Classical.choose_spec hex).2.2.2 σ hσ
      exact ⟨⟨g, hg.1⟩, hg.2, hgσ⟩ }

namespace A7Data

variable {t : X} {L : Subgroup X} (A : A7Data t L)

abbrev T : Subgroup X := Config.sylowIn A.syl

abbrev R : Subgroup X := A.T ⊓ L

abbrev K : Subgroup X := A.T ⊓ coreActionKernel L

include A in
theorem orderOf_t : orderOf t = 2 := A.config.orderOf_eq

theorem t_mem_T : t ∈ A.T := A.config.mem_sylow A.syl

theorem t_mem_K : t ∈ A.K := A.config.mem_inf_kernel A.syl

instance isCyclic_K : IsCyclic A.K := A.config.isCyclic_inf_kernel A.syl

theorem card_R [Finite X] : Nat.card A.R = 8 := A.config.card_inf_L A.syl

theorem T_le_centralizer : A.T ≤ centralizer ({t} : Set X) := Config.sylowIn_le _

theorem isPGroup_T : IsPGroup 2 A.T := Config.isPGroup_sylowIn _

theorem commute_of_mem_R_of_mem_K [Finite X] {r k : X} (hr : r ∈ A.R) (hk : k ∈ A.K) :
    r * k = k * r :=
  Config.commute_inf_L_inf_kernel A.syl hr hk

theorem commute_t {g : X} (hg : g ∈ A.T) : g * t = t * g :=
  mem_centralizer_singleton_iff.mp (A.T_le_centralizer hg)

theorem K_inf_L [Finite X] : A.K ⊓ L = ⊥ := A.config.inf_kernel_inf_L A.syl

include A in
theorem t_not_mem_L [Finite X] : t ∉ L := A.config.not_mem

theorem mem_K_iff {g : X} (hg : g ∈ A.T) : g ∈ A.K ↔ A.ψ ⟨g, hg⟩ = 1 := by
  rw [A.ψ_eq_one_iff]
  exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩

theorem ψ_mem_R0 {g : X} (hg : g ∈ A.R) : A.ψ ⟨g, hg.1⟩ ∈ R0 :=
  ⟨A.ψ_mem_P0 _, A.ψ_mem_alternatingGroup _ hg.2⟩

theorem eq_of_ψ_eq [Finite X] {g₁ g₂ : X} (h₁ : g₁ ∈ A.R) (h₂ : g₂ ∈ A.R)
    (h : A.ψ ⟨g₁, h₁.1⟩ = A.ψ ⟨g₂, h₂.1⟩) : g₁ = g₂ := by
  have hm : g₁⁻¹ * g₂ ∈ A.R := mul_mem (inv_mem h₁) h₂
  have hK : g₁⁻¹ * g₂ ∈ A.K := by
    rw [A.mem_K_iff hm.1]
    have : (⟨g₁⁻¹ * g₂, hm.1⟩ : A.T) = (⟨g₁, h₁.1⟩ : A.T)⁻¹ * ⟨g₂, h₂.1⟩ := rfl
    rw [this, map_mul, map_inv, h, inv_mul_cancel]
  have : g₁⁻¹ * g₂ ∈ A.K ⊓ L := ⟨hK, hm.2⟩
  rw [A.K_inf_L, mem_bot, inv_mul_eq_one] at this
  exact this

theorem pow_four_mem_K {g : X} (hg : g ∈ A.T) : g ^ 4 ∈ A.K := by
  have hm : g ^ 4 ∈ A.T := pow_mem hg 4
  rw [A.mem_K_iff hm]
  have : (⟨g ^ 4, hm⟩ : A.T) = (⟨g, hg⟩ : A.T) ^ 4 := rfl
  rw [this, map_pow]
  exact pow_four_eq_one_of_mem_P0 (A.ψ_mem_P0 _)

variable [Finite X]

theorem eq_t_of_mem_K {k : X} (hk : k ∈ A.K) (hk2 : k ^ 2 = 1) (hk1 : k ≠ 1) : k = t := by
  classical
  have : Fintype A.K := Fintype.ofFinite _
  have ho : orderOf k = 2 := orderOf_eq_prime hk2 hk1
  have hk' : orderOf (⟨k, hk⟩ : A.K) = 2 := by rw [Subgroup.orderOf_mk, ho]
  have ht' : orderOf (⟨t, A.t_mem_K⟩ : A.K) = 2 := by rw [Subgroup.orderOf_mk, A.orderOf_t]
  have hd : 2 ∣ Fintype.card A.K := by
    rw [← hk', ← Nat.card_eq_fintype_card]
    exact orderOf_dvd_natCard _
  have h1 := IsCyclic.card_orderOf_eq_totient hd
  rw [Nat.totient_two] at h1
  have := Finset.card_le_one.mp h1.le ⟨k, hk⟩ (by simp [hk']) ⟨t, A.t_mem_K⟩ (by simp [ht'])
  exact congrArg Subtype.val this

omit [Finite X] in
theorem exists_mem_R_ψ_eq {σ : Perm (Fin 7)} (hσ : σ ∈ R0) :
    ∃ r : X, ∃ hr : r ∈ A.R, A.ψ ⟨r, hr.1⟩ = σ := by
  obtain ⟨g, hgL, hgσ⟩ := A.exists_ψ_eq σ hσ
  exact ⟨g, ⟨g.2, hgL⟩, hgσ⟩

omit [Finite X] in
theorem sq_mem_K_of_commute {g : X} (hg : g ∈ A.T) (hgR : ∀ r ∈ A.R, g * r = r * g) :
    g ^ 2 ∈ A.K := by
  obtain ⟨r, hr, hrσ⟩ := A.exists_mem_R_ψ_eq c0_b0_mem_R0
  have hm : g ^ 2 ∈ A.T := pow_mem hg 2
  rw [A.mem_K_iff hm]
  have : (⟨g ^ 2, hm⟩ : A.T) = (⟨g, hg⟩ : A.T) ^ 2 := rfl
  rw [this, map_pow]
  refine sq_eq_one_of_mem_P0_of_commute (A.ψ_mem_P0 _) ?_
  rw [← hrσ, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hgR r hr)

theorem _root_.CFSG.ComponentClassification.HSFLit.exists_mem_normalizer_not_mem
    {G : Type*} [Group G] [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P)
    (hne : ∀ S : Sylow 2 G, (S : Subgroup G) ≠ P) :
    ∃ w : G, w ∈ normalizer (P : Set G) ∧ w ∉ P ∧ IsPGroup 2 (P ⊔ zpowers w : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  set Q : Subgroup G := (S : Subgroup G) with hQ
  have hlt : P.subgroupOf Q < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne S (le_antisymm (fun g hg => ?_) hS)
    have h1 : (⟨g, hg⟩ : Q) ∈ P.subgroupOf Q := by rw [htop]; exact mem_top _
    exact h1
  have : Group.IsNilpotent Q := S.isPGroup'.isNilpotent
  obtain ⟨w, hwN, hwP⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  refine ⟨w, ?_, hwP, ?_⟩
  · rw [mem_normalizer_iff]
    intro g
    by_cases hgS : g ∈ Q
    · have := (mem_normalizer_iff.mp hwN) ⟨g, hgS⟩
      simpa only [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using this
    · constructor
      · intro hg
        exact absurd (hS hg) hgS
      · intro hg
        have h1 : (w : G) * g * (w : G)⁻¹ ∈ Q := hS hg
        have h2 := mul_mem (mul_mem (inv_mem w.2) h1) w.2
        rw [show (w : G)⁻¹ * ((w : G) * g * (w : G)⁻¹) * (w : G) = g by group] at h2
        exact absurd h2 hgS
  · refine S.isPGroup'.to_le (sup_le hS ?_)
    rw [zpowers_le]
    exact w.2

theorem exists_sylow_eq_of_fix (hfix : ∀ w : X, w ∈ normalizer (A.T : Set X) → w * t * w⁻¹ = t) :
    ∃ S : Sylow 2 X, (S : Subgroup X) = A.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  push Not at hne
  obtain ⟨w, hwN, hwT, hwp⟩ := exists_mem_normalizer_not_mem A.isPGroup_T hne
  have hwC : w ∈ centralizer ({t} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    have := hfix w hwN
    calc w * t = w * t * w⁻¹ * w := by group
      _ = t * w := by rw [this]
  have hle : A.T ⊔ zpowers w ≤ centralizer ({t} : Set X) :=
    sup_le A.T_le_centralizer (zpowers_le.mpr hwC)
  have hQ : IsPGroup 2 ((A.T ⊔ zpowers w).subgroupOf (centralizer ({t} : Set X))) :=
    hwp.comap_of_injective _ (subtype_injective _)
  have hsyl : (A.syl : Subgroup _) ≤ (A.T ⊔ zpowers w).subgroupOf (centralizer ({t} : Set X)) := by
    intro c hc
    exact le_sup_left (a := A.T) ⟨c, hc, rfl⟩
  have heq := A.syl.is_maximal' hQ hsyl
  have hw' : (⟨w, hwC⟩ : centralizer ({t} : Set X)) ∈
      (A.T ⊔ zpowers w).subgroupOf (centralizer ({t} : Set X)) :=
    le_sup_right (a := A.T) (mem_zpowers w)
  rw [heq] at hw'
  exact hwT ⟨_, hw', rfl⟩

theorem gen4_of_fix (e : L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7))
    (hfix : ∀ w : X, w ∈ normalizer (A.T : Set X) → w * t * w⁻¹ = t) (P : Subgroup X)
    (hP : IsPGroup 2 P) : ∃ s : Finset X, s.card ≤ 4 ∧ closure (s : Set X) = P := by
  obtain ⟨S, hS⟩ := A.exists_sylow_eq_of_fix hfix
  exact A.config.gen4_of_coe_sylow_eq e A.syl S hS P hP

omit [Finite X] in
theorem conj_mem_T {w g : X} (hw : w ∈ normalizer (A.T : Set X)) (hg : g ∈ A.T) :
    w * g * w⁻¹ ∈ A.T :=
  (mem_normalizer_iff.mp hw g).mp hg

omit [Finite X] in
theorem conj_inv_mem_T {w g : X} (hw : w ∈ normalizer (A.T : Set X)) (hg : g ∈ A.T) :
    w⁻¹ * g * w ∈ A.T := by
  have := A.conj_mem_T (inv_mem hw) hg
  rwa [inv_inv] at this

omit [Finite X] in
include A in
theorem conj_t_sq (w : X) : (w * t * w⁻¹) ^ 2 = 1 := by
  rw [conj_pow, ← A.orderOf_t, pow_orderOf_eq_one, mul_one, mul_inv_cancel]

omit [Finite X] in
include A in
theorem conj_t_ne_one (w : X) : w * t * w⁻¹ ≠ 1 := by
  intro h
  have : t = 1 := by
    calc t = w⁻¹ * (w * t * w⁻¹) * w := by group
      _ = 1 := by rw [h]; group
  have h2 := A.orderOf_t
  rw [this, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem fix_of_pow_four {g : X} (hg : g ∈ A.T) (hgt : g ^ 4 = t) (w : X)
    (hw : w ∈ normalizer (A.T : Set X)) : w * t * w⁻¹ = t := by
  have hK : w * t * w⁻¹ ∈ A.K := by
    have h4 : w * t * w⁻¹ = (w * g * w⁻¹) ^ 4 := by rw [conj_pow, hgt]
    rw [h4]
    exact A.pow_four_mem_K (A.conj_mem_T hw hg)
  exact A.eq_t_of_mem_K hK (A.conj_t_sq w) (A.conj_t_ne_one w)

theorem fix_of_sq {g : X} (hg : g ∈ A.T) (hgt : g ^ 2 = t)
    (hgc : ∀ i ∈ A.T, i ^ 2 = 1 → g * i = i * g) (w : X) (hw : w ∈ normalizer (A.T : Set X)) :
    w * t * w⁻¹ = t := by
  set g' := w * g * w⁻¹ with hg'
  have hg'T : g' ∈ A.T := A.conj_mem_T hw hg
  have hg'c : ∀ i ∈ A.T, i ^ 2 = 1 → g' * i = i * g' := by
    intro i hi hi2
    have hi' : w⁻¹ * i * w ∈ A.T := A.conj_inv_mem_T hw hi
    have hi'2 : (w⁻¹ * i * w) ^ 2 = 1 := by
      rw [show w⁻¹ * i * w = w⁻¹ * i * w⁻¹⁻¹ by rw [inv_inv], conj_pow, hi2]; group
    have h := hgc _ hi' hi'2
    calc g' * i = w * (g * (w⁻¹ * i * w)) * w⁻¹ := by rw [hg']; group
      _ = w * ((w⁻¹ * i * w) * g) * w⁻¹ := by rw [h]
      _ = i * g' := by rw [hg']; group
  have hK : w * t * w⁻¹ ∈ A.K := by
    obtain ⟨r, hr, hrσ⟩ := A.exists_mem_R_ψ_eq c0_b0_mem_R0
    have hr2 : r ^ 2 = 1 := by
      have hm : r ^ 2 ∈ A.R := pow_mem hr 2
      refine A.eq_of_ψ_eq hm (one_mem _) ?_
      have : (⟨r ^ 2, hm.1⟩ : A.T) = (⟨r, hr.1⟩ : A.T) ^ 2 := rfl
      rw [this, map_pow, hrσ]
      exact (show (c0 * b0) ^ 2 = 1 by decide).trans (map_one A.ψ).symm
    have hm : g' ^ 2 ∈ A.T := pow_mem hg'T 2
    have : w * t * w⁻¹ = g' ^ 2 := by rw [hg', conj_pow, hgt]
    rw [this, A.mem_K_iff hm]
    have : (⟨g' ^ 2, hm⟩ : A.T) = (⟨g', hg'T⟩ : A.T) ^ 2 := rfl
    rw [this, map_pow]
    refine sq_eq_one_of_mem_P0_of_commute (A.ψ_mem_P0 _) ?_
    rw [← hrσ, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hg'c r hr.1 hr2)
  exact A.eq_t_of_mem_K hK (A.conj_t_sq w) (A.conj_t_ne_one w)

end A7Data

end CFSG.ComponentClassification.HSFLit
