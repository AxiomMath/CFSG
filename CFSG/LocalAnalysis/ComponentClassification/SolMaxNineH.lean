module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36X
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36ZA
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallA

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

theorem pow_five_of_pow_five_pow {π : Perm (Fin 9)} {k : ℕ} (h : π ^ 5 ^ k = 1) : π ^ 5 = 1 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Equiv.Perm.pow_prime_eq_one_iff]
  intro c hc
  have h1 : c ∣ 5 ^ k := (Equiv.Perm.dvd_of_mem_cycleType hc).trans (orderOf_dvd_of_pow_eq_one h)
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp h1
  have h2 : 2 ≤ 5 ^ j := Equiv.Perm.two_le_of_mem_cycleType hc
  have h3 : 5 ^ j ≤ 9 := by
    have h4 := Equiv.Perm.le_card_support_of_mem_cycleType hc
    have h5 := Finset.card_le_univ π.support
    rw [Fintype.card_fin] at h5
    omega
  have hj1 : j ≠ 0 := by
    rintro rfl
    norm_num at h2
  have hj2 : j < 2 := by
    by_contra h
    push Not at h
    have h4 : 5 ^ 2 ≤ 5 ^ j := Nat.pow_le_pow_right (by norm_num) h
    have h5 : (5 : ℕ) ^ 2 = 25 := by norm_num
    omega
  have : j = 1 := by omega
  subst this
  exact pow_one 5

theorem exists_common_fixed_of_odd {α : Type*} [Fintype α] [DecidableEq α] {S : Finset α}
    (hS : Odd S.card) {v₁ v₂ : Perm α} (h₁ : v₁ * v₁ = 1) (h₂ : v₂ * v₂ = 1)
    (h12 : v₁ * v₂ = v₂ * v₁) (hS₁ : ∀ x, v₁ x ∈ S ↔ x ∈ S) (hS₂ : ∀ x, v₂ x ∈ S ↔ x ∈ S) :
    ∃ p ∈ S, v₁ p = p ∧ v₂ p = p := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set w₁ : Perm {x // x ∈ S} := v₁.subtypePerm hS₁ with hw₁def
  have hw₁ : w₁ ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq]
    apply Equiv.ext
    intro x
    apply Subtype.ext
    show v₁ (v₁ (x : α)) = x
    rw [← Perm.mul_apply, h₁, Perm.one_apply]
  have hmod := Equiv.Perm.card_compl_support_modEq hw₁
  set F₁ : Finset α := S.filter (fun x => v₁ x = x) with hF₁def
  have hF₁card : F₁.card = w₁.supportᶜ.card := by
    rw [hF₁def]
    refine Finset.card_bij (fun x hx => ⟨x, (Finset.mem_filter.mp hx).1⟩) (fun x hx => ?_)
      (fun x _ y _ h => congrArg Subtype.val h) (fun y hy => ⟨(y : α), ?_, rfl⟩)
    · rw [Finset.mem_compl, Perm.mem_support, not_not]
      exact Subtype.ext (Finset.mem_filter.mp hx).2
    · rw [Finset.mem_compl, Perm.mem_support, not_not] at hy
      exact Finset.mem_filter.mpr ⟨y.2, congrArg Subtype.val hy⟩
  have hF₁odd : Odd F₁.card := by
    rw [hF₁card]
    have h1 : Fintype.card {x // x ∈ S} = S.card := Fintype.card_coe S
    have h2 : w₁.supportᶜ.card % 2 = Fintype.card {x // x ∈ S} % 2 := hmod
    rw [Nat.odd_iff] at hS ⊢
    omega
  have hF₂ : ∀ x, v₂ x ∈ F₁ ↔ x ∈ F₁ := by
    intro x
    simp only [hF₁def, Finset.mem_filter]
    have h3 : v₁ (v₂ x) = v₂ (v₁ x) := by rw [← Perm.mul_apply, h12, Perm.mul_apply]
    constructor
    · rintro ⟨hx, hx'⟩
      refine ⟨(hS₂ x).mp hx, ?_⟩
      rw [h3] at hx'
      exact v₂.injective hx'
    · rintro ⟨hx, hx'⟩
      exact ⟨(hS₂ x).mpr hx, by rw [h3, hx']⟩
  set w₂ : Perm {x // x ∈ F₁} := v₂.subtypePerm hF₂ with hw₂def
  have hw₂ : ∀ x, w₂ (w₂ x) = x := by
    intro x
    apply Subtype.ext
    show v₂ (v₂ (x : α)) = x
    rw [← Perm.mul_apply, h₂, Perm.one_apply]
  have hodd : Odd (Nat.card {x // x ∈ F₁}) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact hF₁odd
  obtain ⟨⟨p, hp⟩, hpfix⟩ := exists_apply_eq_of_odd_card hodd w₂ hw₂
  rw [hF₁def, Finset.mem_filter] at hp
  obtain ⟨hpS, hp1⟩ := hp
  exact ⟨p, hpS, hp1, congrArg Subtype.val hpfix⟩

variable {X : Type} [Group X]

theorem map_conj_centralizer (Q : Subgroup X) (x : X) :
    (centralizer (Q : Set X)).map (MulAut.conj x).toMonoidHom =
      centralizer ((Q.map (MulAut.conj x).toMonoidHom : Subgroup X) : Set X) := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨q, hq, rfl⟩
    have h1 := mem_centralizer_iff.mp hw q hq
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc x * q * x⁻¹ * (x * w * x⁻¹) = x * (q * w) * x⁻¹ := by group
      _ = x * (w * q) * x⁻¹ := by rw [h1]
      _ = x * w * x⁻¹ * (x * q * x⁻¹) := by group
  · intro hy
    refine ⟨x⁻¹ * y * x, mem_centralizer_iff.mpr fun q hq => ?_, by
      simp [MulAut.conj_apply, mul_assoc]⟩
    have h1 := mem_centralizer_iff.mp hy (x * q * x⁻¹) ⟨q, hq, rfl⟩
    calc q * (x⁻¹ * y * x) = x⁻¹ * ((x * q * x⁻¹) * y) * x := by group
      _ = x⁻¹ * (y * (x * q * x⁻¹)) * x := by rw [h1]
      _ = x⁻¹ * y * x * q := by group

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem exists_coreSection_of_conj (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) {M : Subgroup X}
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)) (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    {Q : Subgroup X} (hQH : Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hQK : Q ≤ UnbalancedLayer.coreActionKernel M) (hQ2 : IsPGroup 2 Q) (htQ : t ∈ Q)
    {a g s : X} (haQ : a ∈ Q) (hgs : g⁻¹ * a * g = s) (hs1 : s ≠ 1) :
    ∃ N : Subgroup X, N ≤ centralizer ({s} : Set X) ∧
      centralizer ({s} : Set X) ≤ normalizer (N : Set X) ∧
      Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin n)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := GSLit.fixedLayer M Q with hLdef
  obtain ⟨-, hLC, hpc, θL, -⟩ :=
    S.layer_facts_of_sup h33 h35 hT13 hML hSch hMH hMpc hHN θ hsup hQH hQK hQ2 htQ
  set T := Q.map (MulAut.conj g⁻¹).toMonoidHom with hTdef
  set K := L.map (MulAut.conj g⁻¹).toMonoidHom with hKdef
  have hCT : (centralizer (Q : Set X)).map (MulAut.conj g⁻¹).toMonoidHom =
      centralizer (T : Set X) := map_conj_centralizer Q g⁻¹
  have hKT : K ≤ centralizer (T : Set X) := by
    rw [← hCT]
    exact map_mono hLC
  have hKpc : IsPComponent 2 (K.subgroupOf (centralizer (T : Set X))) := by
    have h1 := isPComponent_map_conj hLC hpc g⁻¹
    rwa [hCT] at h1
  let φ : ↥L ≃* ↥K :=
    L.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  let θK : ↥K ⧸ pPrimeCore 2 ↥K ≃* alternatingGroup (Fin n) := (Sol78.coreQuotCongr φ).symm.trans θL
  have hsT : s ∈ T := ⟨a, haQ, by rw [← hgs]; simp⟩
  have hT1 : T ≠ ⊥ := by
    intro h
    have h1 := hsT
    rw [h, mem_bot] at h1
    exact hs1 h1
  have hT2 : IsPGroup 2 T := hQ2.map _
  have hs2 : IsPGroup 2 (zpowers s) := hT2.to_le (zpowers_le.mpr hsT)
  have hS1 : zpowers s ≠ ⊥ := fun h => hs1 (zpowers_eq_bot.mp h)
  have hCs : centralizer ((zpowers s : Subgroup X) : Set X) = centralizer ({s} : Set X) :=
    UnbalancedLayer.centralizer_zpowers_eq s
  have hKs : K ≤ centralizer ((zpowers s : Subgroup X) : Set X) := by
    rw [hCs]
    exact hKT.trans (centralizer_le (Set.singleton_subset_iff.mpr hsT))
  have hYN : centralizer ({s} : Set X) ≤ normalizer ((zpowers s : Subgroup X) : Set X) := by
    rw [← hCs]
    exact Subgroup.centralizer_le_normalizer _
  have hnorm := Sol78H.le_normalizer_core_sup_of_thm13 hT13 hML hSch S.nonab S.kProper S.unbal
    S.notU S.pair.2.1 S.pair.2.2.1 ⟨t, J, S.pair.1⟩ S.pair.2.2.2.1 hT1 hT2 ⟨hKT, hKpc⟩ ⟨θK⟩
    hS1 hs2 hKs hCs.le hYN
  set Y := centralizer ({s} : Set X) with hYdef
  set O := GH74.GLS.pPrimeCoreOf 2 Y with hOdef
  set Z : Subgroup X := O ⊔ K with hZdef
  have hOY : O ≤ Y := map_subtype_le _
  have hKY : K ≤ Y := hCs ▸ hKs
  have hZY : Z ≤ Y := sup_le hOY hKY
  have hKZ : K ≤ Z := le_sup_right
  have hOZ : O ≤ (pPrimeCore 2 ↥Z).map Z.subtype := by
    refine le_pPrimeCore_map le_sup_left
      (fun x hx => le_normalizer_pPrimeCore (le_normalizer (hZY hx))) ?_
    rw [hOdef, GH74.GLS.pPrimeCoreOf, card_map_of_injective Y.subtype_injective]
    exact pPrimeCore_coprime_card
  have hsupZ : K ⊔ (pPrimeCore 2 ↥Z).map Z.subtype = Z :=
    le_antisymm (sup_le hKZ (map_subtype_le _)) (sup_le (hOZ.trans le_sup_right) le_sup_left)
  obtain ⟨θZ, -⟩ := exists_coreQuot_of_sup' hKZ hsupZ θK
  exact ⟨Z, hZY, hnorm, ⟨θZ⟩⟩

end Sig36

end CFSG.ComponentClassification.SolMax
