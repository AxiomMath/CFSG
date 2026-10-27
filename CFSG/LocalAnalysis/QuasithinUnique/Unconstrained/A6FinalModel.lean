module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FinalFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsModel4

public section

namespace CFSG.QuasithinUnique.A6Facts

open Equiv

@[expose] def NormKlein (r a : P10) : Prop := ∀ e, KleinMem r e → ∃ e', KleinMem r e' ∧ a * e = e' * a

theorem mem_normKlein_X {r a e : P10} :
    Core.cmul (code a) (code e) ∈ (Core.kleinOf (code r)).map (fun e' => Core.cmul e' (code a)) ↔
      ∃ e', KleinMem r e' ∧ a * e = e' * a := by
  constructor
  · intro hmem
    obtain ⟨c, hc, hceq⟩ := List.mem_map.mp hmem
    obtain ⟨e', he', rfl⟩ := klein_code_mem.mp hc
    refine ⟨e', he', ?_⟩
    apply code_injective
    rw [code_mul, code_mul]
    exact hceq.symm
  · rintro ⟨e', he', h⟩
    refine List.mem_map.mpr ⟨code e', klein_code_mem.mpr ⟨e', he', rfl⟩, ?_⟩
    rw [← code_mul, ← code_mul, h]

theorem normKlein_iff {r a : P10} :
    Core.normKlein (code r) (code a) = true ↔ NormKlein r a := by
  unfold Core.normKlein NormKlein
  simp only [Bool.and_eq_true, List.contains_iff_mem]
  have hrz : Core.cmul (code r) Core.zbC = code (r * zb) := by rw [code_mul, zb_code]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩ e he
    rcases he with rfl | rfl | rfl | rfl
    · exact ⟨1, Or.inl rfl, by simp⟩
    · exact mem_normKlein_X.mp (by rw [zb_code]; exact h2)
    · exact mem_normKlein_X.mp h1
    · exact mem_normKlein_X.mp (by rw [← hrz]; exact h3)
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact mem_normKlein_X.mpr (h r (Or.inr (Or.inr (Or.inl rfl))))
    · rw [← zb_code]
      exact mem_normKlein_X.mpr (h zb (Or.inr (Or.inl rfl)))
    · rw [hrz]
      exact mem_normKlein_X.mpr (h (r * zb) (Or.inr (Or.inr (Or.inr rfl))))

theorem exists_normData {r : P10} (hr : IsRefl r) :
    ∃ e ∈ Core.normData, e.1 = code r := by
  have h := Core.norm_data_refl
  have hmem : code r ∈ Core.dLit.filter Core.isRefl := by
    rw [List.mem_filter]
    exact ⟨List.contains_iff_mem.mp (by
      have := isRefl_of hr
      unfold Core.isRefl at this
      simp only [Bool.and_eq_true] at this
      exact this.1.1.1), isRefl_of hr⟩
  rw [← h] at hmem
  obtain ⟨e, he, hee⟩ := List.mem_map.mp hmem
  exact ⟨e, he, hee⟩

theorem normData_psl {r ψ : P10} {e : List ℕ × List (List ℕ) × List (List ℕ)} (he : e ∈ Core.normData)
    (her : e.1 = code r) :
    code ψ ∈ e.2.1 ↔ ψ ∈ A6Models.psl29 ∧ NormKlein r ψ := by
  have hall := Core.norm_data_ok
  rw [List.all_eq_true] at hall
  have h := hall e he
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [h.1, List.mem_filter, ← mem_psl29_iff, her, ← normKlein_iff]

theorem normData_P0 {r π : P10} {e : List ℕ × List (List ℕ) × List (List ℕ)} (he : e ∈ Core.normData)
    (her : e.1 = code r) :
    code π ∈ e.2.2 ↔ π ∈ P0 ∧ NormKlein r π := by
  have hall := Core.norm_data_ok
  rw [List.all_eq_true] at hall
  have h := hall e he
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [h.2, List.mem_filter, ← mem_P0_iff, her, ← normKlein_iff]

theorem normData_psl' {r : P10} {e : List ℕ × List (List ℕ) × List (List ℕ)} (he : e ∈ Core.normData)
    (her : e.1 = code r) {c : List ℕ} (hc : c ∈ e.2.1) :
    ∃ ψ, ψ ∈ A6Models.psl29 ∧ NormKlein r ψ ∧ code ψ = c := by
  have hall := Core.norm_data_ok
  rw [List.all_eq_true] at hall
  have h := hall e he
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [h.1, List.mem_filter] at hc
  obtain ⟨ψ, hψ, rfl⟩ := exists_psl29_of_code hc.1
  rw [her] at hc
  exact ⟨ψ, hψ, normKlein_iff.mp hc.2, rfl⟩

theorem normData_P0' {r : P10} {e : List ℕ × List (List ℕ) × List (List ℕ)} (he : e ∈ Core.normData)
    (her : e.1 = code r) {c : List ℕ} (hc : c ∈ e.2.2) :
    ∃ π, π ∈ P0 ∧ NormKlein r π ∧ code π = c := by
  have hall := Core.norm_data_ok
  rw [List.all_eq_true] at hall
  have h := hall e he
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [h.2, List.mem_filter] at hc
  obtain ⟨π, hπ, rfl⟩ := exists_P0_of_code (by simpa using hc.1)
  rw [her] at hc
  exact ⟨π, hπ, normKlein_iff.mp hc.2, rfl⟩

theorem klein_comm_mem {r τ ψ : P10} (hr : IsRefl r) (hτ : InE4 τ) (hψ : ψ ∈ A6Models.psl29)
    (hn : NormKlein r ψ) : ∃ ε, KleinMem r ε ∧ ψ * τ = τ * ε * ψ := by
  obtain ⟨e, he, her⟩ := exists_normData hr
  have hall := Core.klein_comm_check
  rw [List.all_eq_true] at hall
  have h1 := hall e he
  rw [List.all_eq_true] at h1
  have h2 := h1 (code ψ) ((normData_psl he her).mpr ⟨hψ, hn⟩)
  rw [List.all_eq_true] at h2
  have h3 := h2 (code τ) ((inE4_iff τ).1 hτ)
  rw [List.any_eq_true] at h3
  obtain ⟨c, hc, hceq⟩ := h3
  rw [her] at hc
  obtain ⟨ε, hε, rfl⟩ := klein_code_mem.mp hc
  refine ⟨ε, hε, ?_⟩
  rw [beq_iff_eq] at hceq
  apply code_injective
  simp only [code_mul]
  exact hceq

theorem norm_decomp {r α : P10} (hr : IsRefl r) (hα : α ∈ A6Models.autA6) (hn : NormKlein r α) :
    ∃ ψ π, ψ ∈ A6Models.psl29 ∧ π ∈ P0 ∧ NormKlein r ψ ∧ NormKlein r π ∧ α = ψ * π := by
  obtain ⟨e, he, her⟩ := exists_normData hr
  have h := Core.norm_decomp_check e he (code α) (code_mem_autL hα)
  rw [her, normKlein_iff.mpr hn] at h
  simp only [Bool.not_true, Bool.false_or, List.contains_iff_mem] at h
  unfold Core.normProds at h
  obtain ⟨c, hc, hmem⟩ := List.mem_flatMap.mp h
  obtain ⟨d, hd, hdeq⟩ := List.mem_map.mp hmem
  obtain ⟨ψ, hψ, hψn, rfl⟩ := normData_psl' he her hc
  obtain ⟨π, hπ, hπn, rfl⟩ := normData_P0' he her hd
  refine ⟨ψ, π, hψ, hπ, hψn, hπn, ?_⟩
  apply code_injective
  rw [code_mul]
  exact hdeq.symm

theorem norm_comm_e4 {r p τ : P10} (hr : IsRefl r) (hp : p ∈ P0) (hn : NormKlein r p) (hτ : InE4 τ) :
    p * τ = τ * p := by
  obtain ⟨e, he, her⟩ := exists_normData hr
  have hall := Core.norm_comm_e4_check
  rw [List.all_eq_true] at hall
  have h1 := hall e he
  rw [List.all_eq_true] at h1
  have h2 := h1 (code p) ((normData_P0 he her).mpr ⟨hp, hn⟩)
  rw [List.all_eq_true] at h2
  have h3 := h2 (code τ) ((inE4_iff τ).1 hτ)
  rw [beq_iff_eq] at h3
  apply code_injective
  rw [code_mul, code_mul]
  exact h3

end CFSG.QuasithinUnique.A6Facts
