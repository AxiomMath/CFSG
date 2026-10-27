module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsA6Model
public import CFSG.RankThree.PartOne.KS.PKitLines

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.Unc25K1.A6Model

@[expose] def tAddI : P10 := A6Models.perm10 [[0, 3, 6], [1, 4, 7], [2, 5, 8]]

@[expose] def e0Gen : List P10 :=
  [1, tAddI, tAddI ^ 2, A6Models.tAdd, A6Models.tAdd * tAddI, A6Models.tAdd * tAddI ^ 2,
    A6Models.tAdd ^ 2, A6Models.tAdd ^ 2 * tAddI, A6Models.tAdd ^ 2 * tAddI ^ 2]

@[expose] def e0Codes : List (List ℕ) := e0Gen.map code

@[expose] def E0 : Subgroup P10 := Subgroup.closure {A6Models.tAdd, tAddI}

theorem e0Codes_mul : ∀ c ∈ e0Codes, ∀ d ∈ e0Codes, Core.cmul c d ∈ e0Codes := by decide +kernel

theorem e0Codes_nodup : e0Codes.Nodup := by decide +kernel

theorem e0Codes_length : e0Codes.length = 9 := by decide +kernel

theorem tAdd_code_mem : code A6Models.tAdd ∈ e0Codes := by decide +kernel

theorem tAddI_code_mem : code tAddI ∈ e0Codes := by decide +kernel

theorem e0Gen_mem : ∀ p ∈ e0Gen, p ∈ E0 := by
  have h1 : A6Models.tAdd ∈ E0 := Subgroup.subset_closure (by simp)
  have h2 : tAddI ∈ E0 := Subgroup.subset_closure (by simp)
  intro p hp
  simp only [e0Gen, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact h2
  · exact pow_mem h2 2
  · exact h1
  · exact mul_mem h1 h2
  · exact mul_mem h1 (pow_mem h2 2)
  · exact pow_mem h1 2
  · exact mul_mem (pow_mem h1 2) h2
  · exact mul_mem (pow_mem h1 2) (pow_mem h2 2)

theorem mem_E0_iff {x : P10} : x ∈ E0 ↔ code x ∈ e0Codes := by
  constructor
  · intro hx
    have hsub : (Subgroup.closure {A6Models.tAdd, tAddI}).toSubmonoid =
        Submonoid.closure {A6Models.tAdd, tAddI} := Subgroup.closure_toSubmonoid_of_finite
    have hx' : x ∈ Submonoid.closure {A6Models.tAdd, tAddI} := by rw [← hsub]; exact hx
    refine Submonoid.closure_induction (motive := fun m _ => code m ∈ e0Codes) ?_ ?_ ?_ hx'
    · rintro m (rfl | rfl)
      · exact tAdd_code_mem
      · exact tAddI_code_mem
    · rw [code_one]; decide +kernel
    · intro m n _ _ hm hn
      rw [code_mul]
      exact e0Codes_mul _ hm _ hn
  · intro hx
    simp only [e0Codes, List.mem_map] at hx
    obtain ⟨p, hp, hpx⟩ := hx
    have : p = x := code_injective hpx
    exact this ▸ e0Gen_mem p hp

theorem card_E0 : Nat.card E0 = 9 := by
  rw [card_eq_of_code_mem e0Codes_nodup (fun x => mem_E0_iff) ?_, e0Codes_length]
  intro c hc
  simp only [e0Codes, List.mem_map] at hc
  obtain ⟨p, hp, rfl⟩ := hc
  exact ⟨p, e0Gen_mem p hp, rfl⟩

theorem E0_le_psl29 : E0 ≤ A6Models.psl29 := by
  intro x hx
  rw [mem_E0_iff] at hx
  rw [mem_psl29_iff]
  have : ∀ c ∈ e0Codes, c ∈ Core.pslLit := by decide +kernel
  exact this _ hx

theorem exists_E0_of_code {c : List ℕ} (hc : c ∈ e0Codes) : ∃ x ∈ E0, code x = c := by
  simp only [e0Codes, List.mem_map] at hc
  obtain ⟨p, hp, rfl⟩ := hc
  exact ⟨p, e0Gen_mem p hp, rfl⟩

@[expose] def nrmE0 (c : List ℕ) : Bool :=
  e0Codes.all fun e => e0Codes.any fun e' => Core.cmul c e == Core.cmul e' c

@[expose] def ord8 (c : List ℕ) : Bool :=
  Core.cpow c 8 == Core.cid && Core.cpow c 4 != Core.cid

theorem match_check : (Core.autL.filter fun c => nrmE0 c && ord8 c).all (fun c₁ =>
    (Core.autL.filter fun c => nrmE0 c && ord8 c).all fun c₂ =>
      e0Codes.any fun e => [1, 3, 5, 7].any fun k => c₁ == Core.cmul e (Core.cpow c₂ k)) = true := by
  decide +kernel

theorem nrmE0_of_mem {b : P10} (h : ∀ e ∈ E0, b * e * b⁻¹ ∈ E0) : nrmE0 (code b) = true := by
  unfold nrmE0
  rw [List.all_eq_true]
  intro e he
  obtain ⟨x, hx, rfl⟩ := exists_E0_of_code he
  have h1 := (mem_E0_iff).1 (h x hx)
  simp only [e0Codes, List.mem_map] at h1
  obtain ⟨p, hp, hpe⟩ := h1
  rw [List.any_eq_true]
  refine ⟨code p, List.mem_map_of_mem hp, ?_⟩
  rw [beq_iff_eq, ← code_mul, ← code_mul]
  congr 1
  rw [code_injective hpe]
  group

theorem match_E0 {b₁ b₂ : P10} (h₁ : b₁ ∈ A6Models.autA6) (h₂ : b₂ ∈ A6Models.autA6)
    (n₁ : ∀ e ∈ E0, b₁ * e * b₁⁻¹ ∈ E0) (n₂ : ∀ e ∈ E0, b₂ * e * b₂⁻¹ ∈ E0)
    (o₁ : b₁ ^ 8 = 1) (o₁' : b₁ ^ 4 ≠ 1) (o₂ : b₂ ^ 8 = 1) (o₂' : b₂ ^ 4 ≠ 1) :
    ∃ e ∈ E0, ∃ k : ℕ, Odd k ∧ b₁ = e * b₂ ^ k := by
  have hord : ∀ b : P10, b ^ 8 = 1 → b ^ 4 ≠ 1 → ord8 (code b) = true := by
    intro b h8 h4
    have h8' : Core.cpow (code b) 8 = Core.cid := by rw [← code_pow, h8, code_one]
    have h4' : Core.cpow (code b) 4 ≠ Core.cid := by
      rw [← code_pow]
      intro h
      apply h4
      apply code_injective
      rw [h, code_one]
    unfold ord8
    simp [h8', h4']
  have hm1 : (nrmE0 (code b₁) && ord8 (code b₁)) = true := by
    rw [Bool.and_eq_true]; exact ⟨nrmE0_of_mem n₁, hord b₁ o₁ o₁'⟩
  have hm2 : (nrmE0 (code b₂) && ord8 (code b₂)) = true := by
    rw [Bool.and_eq_true]; exact ⟨nrmE0_of_mem n₂, hord b₂ o₂ o₂'⟩
  have h := List.all_eq_true.1 match_check (code b₁)
    (List.mem_filter.2 ⟨code_mem_autL h₁, hm1⟩)
  have h' := List.all_eq_true.1 h (code b₂) (List.mem_filter.2 ⟨code_mem_autL h₂, hm2⟩)
  rw [List.any_eq_true] at h'
  obtain ⟨c, hc, h''⟩ := h'
  rw [List.any_eq_true] at h''
  obtain ⟨k, hk, h3⟩ := h''
  obtain ⟨e, he, rfl⟩ := exists_E0_of_code hc
  refine ⟨e, he, k, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> decide
  · apply code_injective
    rw [beq_iff_eq] at h3
    rw [code_mul, code_pow]
    exact h3

section Transport

open Subgroup

theorem exists_iso_E0 {G : Type*} [Group G] {I E : Subgroup G} (hEI : E ≤ I)
    (hE9 : Nat.card E = 9) (hI : Nonempty (↥I ≃* alternatingGroup (Fin 6))) :
    ∃ φ : ↥I ≃* ↥A6Models.psl29, (∀ k : ↥I, (k : G) ∈ E → ((φ k : ↥A6Models.psl29) : P10) ∈ E0) ∧
      ∀ e₀ ∈ E0, ∃ k : ↥I, (k : G) ∈ E ∧ ((φ k : ↥A6Models.psl29) : P10) = e₀ := by
  obtain ⟨-, ψ, -, -⟩ := exists_pslEquiv
  obtain ⟨e⟩ := hI
  set φ₀ : ↥I ≃* ↥A6Models.psl29 := e.trans ψ.symm with hφ₀
  set P := A6Models.psl29 with hP
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : (Nat.card ↥P).factorization 3 = 2 := by
    rw [card_psl29, show (360 : ℕ) = 3 ^ 2 * 40 by norm_num]
    exact CFSG.RankThree.PartOne.factorization_pow_mulG Nat.prime_three (by norm_num)
  set E' : Subgroup ↥I := E.subgroupOf I with hE'
  have hE'card : Nat.card E' = 9 := by
    rw [hE', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEI).toEquiv, hE9]
  set Ê : Subgroup ↥P := E'.map φ₀.toMonoidHom with hÊ
  have hÊcard : Nat.card Ê = 9 := by
    rw [hÊ, Subgroup.card_map_of_injective φ₀.injective, hE'card]
  set E0' : Subgroup ↥P := E0.subgroupOf P with hE0'
  have hE0'card : Nat.card E0' = 9 := by
    rw [hE0', Nat.card_congr (Subgroup.subgroupOfEquivOfLe E0_le_psl29).toEquiv, card_E0]
  let S₁ : Sylow 3 ↥P := Sylow.ofCard Ê (by rw [hÊcard, hfac]; norm_num)
  let S₂ : Sylow 3 ↥P := Sylow.ofCard E0' (by rw [hE0'card, hfac]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥P S₁ S₂
  have hmem : ∀ x ∈ Ê, (MulAut.conj g) x ∈ E0' := by
    intro x hx
    have h1 : (MulAut.conj g) x ∈ (g • S₁ : Sylow 3 ↥P) := by
      have := Set.smul_mem_smul_set (a := MulAut.conj g) (show x ∈ (S₁ : Set ↥P) from hx)
      rw [← Sylow.coe_smul] at this
      exact this
    rw [hg] at h1
    exact h1
  set φ : ↥I ≃* ↥P := φ₀.trans (MulAut.conj g) with hφ
  have hφapp : ∀ k : ↥I, ((φ k : ↥P) : P10) = (g : P10) * ((φ₀ k : ↥P) : P10) * (g : P10)⁻¹ :=
    fun k => rfl
  have hmapeq : Ê.map (MulAut.conj g).toMonoidHom = E0' := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hmem x hx
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hÊcard, hE0'card]
  refine ⟨φ, fun k hk => ?_, fun e₀ he₀ => ?_⟩
  · have hk' : φ₀ k ∈ Ê := ⟨k, (Subgroup.mem_subgroupOf).2 hk, rfl⟩
    have := hmem _ hk'
    rw [hE0', Subgroup.mem_subgroupOf] at this
    exact this
  · have h1 : (⟨e₀, E0_le_psl29 he₀⟩ : ↥P) ∈ E0' := by
      rw [hE0', Subgroup.mem_subgroupOf]; exact he₀
    rw [← hmapeq] at h1
    obtain ⟨y, hy, hyk⟩ := h1
    obtain ⟨k', hk', rfl⟩ := hy
    refine ⟨k', ?_, ?_⟩
    · exact (Subgroup.mem_subgroupOf).1 hk'
    · have := congrArg (fun z : ↥P => (z : P10)) hyk
      exact (hφapp k').trans (by simpa using this)

theorem exists_match_pgl {G : Type*} [Group G] {I E : Subgroup G} (hEI : E ≤ I)
    (hE9 : Nat.card E = 9) (hI : Nonempty (↥I ≃* alternatingGroup (Fin 6)))
    {u v : G} (huI : u ∈ normalizer (I : Set G)) (huE : u ∈ normalizer (E : Set G))
    (hvI : v ∈ normalizer (I : Set G)) (hvE : v ∈ normalizer (E : Set G))
    (hu8 : u ^ 8 = 1) (hu4 : u ^ 4 ∉ centralizer (I : Set G))
    (hv8 : v ^ 8 = 1) (hv4 : v ^ 4 ∉ centralizer (I : Set G)) :
    ∃ x ∈ E, ∃ k : ℕ, Odd k ∧ u * (x * v ^ k)⁻¹ ∈ centralizer (I : Set G) := by
  obtain ⟨φ, hφE, hφsurj⟩ := exists_iso_E0 hEI hE9 hI
  let γ : normalizer (I : Set G) →* MulAut ↥I := I.normalizerMonoidHom
  have hγ : ∀ (w : normalizer (I : Set G)) (k : ↥I),
      ((γ w k : ↥I) : G) = (w : G) * k * (w : G)⁻¹ := fun w k => rfl
  let Θ := thetaEquiv φ
  have hspec : ∀ (w : normalizer (I : Set G)) (k : ↥I),
      ((φ (γ w k) : ↥A6Models.psl29) : P10) = ((Θ (γ w) : ↥A6Models.autA6) : P10) *
        ((φ k : ↥A6Models.psl29) : P10) * ((Θ (γ w) : ↥A6Models.autA6) : P10)⁻¹ :=
    fun w k => thetaEquiv_spec φ (γ w) k
  have hdata : ∀ (w : normalizer (I : Set G)), (w : G) ∈ normalizer (E : Set G) →
      (∀ e ∈ E0, ((Θ (γ w) : ↥A6Models.autA6) : P10) * e *
        ((Θ (γ w) : ↥A6Models.autA6) : P10)⁻¹ ∈ E0) := by
    intro w hw e he
    obtain ⟨k, hkE, hk⟩ := hφsurj e he
    rw [← hk, ← hspec]
    apply hφE
    rw [hγ]
    exact (Subgroup.mem_normalizer_iff.1 hw k).1 hkE
  have hord8 : ∀ w : normalizer (I : Set G), (w : G) ^ 8 = 1 →
      ((Θ (γ w) : ↥A6Models.autA6) : P10) ^ 8 = 1 := by
    intro w hw
    have h1 : Θ (γ w) ^ 8 = 1 := by
      rw [← map_pow, ← map_pow]
      have : w ^ 8 = 1 := Subtype.ext (by simpa using hw)
      rw [this, map_one, map_one]
    simpa using congrArg Subtype.val h1
  have hord4 : ∀ w : normalizer (I : Set G), (w : G) ^ 4 ∉ centralizer (I : Set G) →
      ((Θ (γ w) : ↥A6Models.autA6) : P10) ^ 4 ≠ 1 := by
    intro w hw h
    apply hw
    have h1 : Θ (γ w) ^ 4 = 1 := Subtype.ext (by simpa using h)
    have h2 : (γ w) ^ 4 = 1 := Θ.injective (by rw [map_pow, h1, map_one])
    have h2' : γ (w ^ 4) = 1 := by rw [map_pow]; exact h2
    rw [mem_centralizer_iff]
    intro i hi
    have h3 := congrArg (fun z : MulAut ↥I => ((z ⟨i, hi⟩ : ↥I) : G)) h2'
    simp only [hγ, MulAut.one_apply] at h3
    have h4 : ((w ^ 4 : normalizer (I : Set G)) : G) = (w : G) ^ 4 := rfl
    rw [h4, mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  set wu : normalizer (I : Set G) := ⟨u, huI⟩ with hwu
  set wv : normalizer (I : Set G) := ⟨v, hvI⟩ with hwv
  have hnu := hdata wu huE
  have hnv := hdata wv hvE
  have hbuA : ((Θ (γ wu) : ↥A6Models.autA6) : P10) ∈ A6Models.autA6 := (Θ (γ wu)).2
  have hbvA : ((Θ (γ wv) : ↥A6Models.autA6) : P10) ∈ A6Models.autA6 := (Θ (γ wv)).2
  obtain ⟨e₀, he₀, k, hk, hbk⟩ := match_E0 hbuA hbvA hnu hnv (hord8 wu hu8) (hord4 wu hu4)
    (hord8 wv hv8) (hord4 wv hv4)
  obtain ⟨k₁, hk₁E, hk₁⟩ := hφsurj e₀ he₀
  have hxN : ((k₁ : ↥I) : G) ∈ normalizer (I : Set G) := Subgroup.le_normalizer k₁.2
  set wx : normalizer (I : Set G) := ⟨(k₁ : G), hxN⟩ with hwx
  have hΘx : Θ (γ wx) = ⟨e₀, E0_le_psl29.trans psl29_le_autA6 he₀⟩ := by
    apply thetaEquiv_eq φ (γ wx) ⟨e₀, E0_le_psl29.trans psl29_le_autA6 he₀⟩
    intro k'
    have h1 : γ wx k' = k₁ * k' * k₁⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv]
    show _ = e₀ * _ * e₀⁻¹
    rw [← hk₁]
    simp
  have hγeq : γ wu = γ (wx * wv ^ k) := by
    apply Θ.injective
    rw [map_mul, map_pow, map_mul, map_pow, hΘx]
    apply Subtype.ext
    simpa using hbk
  refine ⟨(k₁ : G), hk₁E, k, hk, ?_⟩
  have hwN : (k₁ : G) * v ^ k ∈ normalizer (I : Set G) :=
    Subgroup.mul_mem _ hxN (Subgroup.pow_mem _ hvI k)
  rw [mem_centralizer_iff]
  intro i hi
  have hinv : ((k₁ : G) * v ^ k)⁻¹ ∈ normalizer (I : Set G) := Subgroup.inv_mem _ hwN
  have hi' : ((k₁ : G) * v ^ k)⁻¹ * i * ((k₁ : G) * v ^ k) ∈ I := by
    have := (Subgroup.mem_normalizer_iff.1 hinv i).1 hi
    simpa using this
  have h5 := congrArg (fun z : MulAut ↥I => ((z ⟨_, hi'⟩ : ↥I) : G)) hγeq
  simp only [hγ] at h5
  have h6 : ((wx * wv ^ k : normalizer (I : Set G)) : G) = (k₁ : G) * v ^ k := rfl
  rw [h6] at h5
  have h5' : u * (((k₁ : G) * v ^ k)⁻¹ * i * ((k₁ : G) * v ^ k)) * u⁻¹ =
      ((k₁ : G) * v ^ k) * (((k₁ : G) * v ^ k)⁻¹ * i * ((k₁ : G) * v ^ k)) *
        ((k₁ : G) * v ^ k)⁻¹ := h5
  generalize (k₁ : G) * v ^ k = w at h5' hwN hinv hi' ⊢
  have hh : u * (w⁻¹ * i * w) * u⁻¹ = i := by rw [h5']; group
  calc i * (u * w⁻¹) = (u * (w⁻¹ * i * w) * u⁻¹) * (u * w⁻¹) := by rw [hh]
    _ = u * w⁻¹ * i := by group

end Transport

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
