module

public import Certificates.Data.Kernel.PermCent.OuterRepC
public import CFSG.Certificates.Kernel.PermCent.CVSound
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.Certificates.Kernel.PkCV.OutR

open Subgroup

section Pred

variable {G : Type*} [Group G]

@[expose] def Fix3 (P : Subgroup G) (v ψ : G) : Prop :=
  ∀ c ∈ P, c ^ 3 = 1 → c * v = v * c → ψ * c = c * ψ

@[expose] def OutCent3At (P A : Subgroup G) (τ : G) : Prop :=
  ∀ ψ ∈ A, Fix3 P τ ψ → ψ = 1 ∨ ψ = τ

@[expose] def BangAt (P : Subgroup G) (τ : G) : Prop :=
  ∃ l ∈ P, ∃ c₁ ∈ P, ∃ c₂ ∈ P, c₁ ^ 3 = 1 ∧ c₂ ^ 3 = 1 ∧ c₁ ≠ 1 ∧ c₂ ≠ 1 ∧ c₁ * τ = τ * c₁ ∧
    c₂ * τ = τ * c₂ ∧ (c₁ * c₂) ^ 2 = 1 ∧ c₁ * c₂ ≠ 1 ∧ τ * l * τ⁻¹ * l⁻¹ = c₁ * c₂

@[expose] def InnerSqAt (P A : Subgroup G) (v : G) : Prop :=
  ∀ ψ ∈ A, Fix3 P v ψ → (ψ ^ 2 = 1 ∨ ψ ^ 2 = v) ∧ (ψ ∈ P → ψ ^ 2 = 1 → ψ = 1 ∨ ψ = v)

@[expose] def CycAt (P A : Subgroup G) (v : G) : Prop :=
  ∃ φ ∈ A, ∀ ψ ∈ A, Fix3 P v ψ → ∃ k : ℕ, ψ = φ ^ k

variable {P A : Subgroup G}

theorem fix3_map (φ : G ≃* G) (hP : ∀ y, φ y ∈ P ↔ y ∈ P) {v ψ : G} (h : Fix3 P v ψ) :
    Fix3 P (φ v) (φ ψ) := by
  intro c hc hc3 hcv
  obtain ⟨c, rfl⟩ := φ.surjective c
  have h3 : c ^ 3 = 1 := φ.injective (by rw [map_pow, hc3, map_one])
  have hv : c * v = v * c := φ.injective (by rw [map_mul, map_mul, hcv])
  rw [← map_mul, ← map_mul, h c ((hP c).1 hc) h3 hv]

theorem bangAt_map (φ : G ≃* G) (hP : ∀ y, φ y ∈ P ↔ y ∈ P) {τ : G} (h : BangAt P (φ τ)) :
    BangAt P τ := by
  obtain ⟨l, hl, c₁, hc₁, c₂, hc₂, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  obtain ⟨l, rfl⟩ := φ.surjective l
  obtain ⟨c₁, rfl⟩ := φ.surjective c₁
  obtain ⟨c₂, rfl⟩ := φ.surjective c₂
  refine ⟨l, (hP l).1 hl, c₁, (hP c₁).1 hc₁, c₂, (hP c₂).1 hc₂,
    φ.injective (by rw [map_pow, h1, map_one]), φ.injective (by rw [map_pow, h2, map_one]),
    fun e => h3 (by rw [e, map_one]), fun e => h4 (by rw [e, map_one]),
    φ.injective (by rw [map_mul, map_mul, h5]), φ.injective (by rw [map_mul, map_mul, h6]),
    φ.injective (by rw [map_pow, map_mul, h7, map_one]),
    fun e => h8 (by rw [← map_mul, e, map_one]), φ.injective ?_⟩
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, h9, map_mul]

section Map

variable (φ : G ≃* G) (hP : ∀ y, φ y ∈ P ↔ y ∈ P) (hA : ∀ y, φ y ∈ A ↔ y ∈ A)
include hP hA

theorem outCent3At_map {τ : G} (h : OutCent3At P A (φ τ)) : OutCent3At P A τ := by
  intro ψ hψ hfix
  rcases h (φ ψ) ((hA ψ).2 hψ) (fix3_map φ hP hfix) with e | e
  · exact Or.inl (φ.injective (by rw [e, map_one]))
  · exact Or.inr (φ.injective e)

theorem innerSqAt_map {v : G} (h : InnerSqAt P A (φ v)) : InnerSqAt P A v := by
  intro ψ hψ hfix
  obtain ⟨h1, h2⟩ := h (φ ψ) ((hA ψ).2 hψ) (fix3_map φ hP hfix)
  refine ⟨?_, fun hψP hψ2 => ?_⟩
  · rcases h1 with e | e
    · exact Or.inl (φ.injective (by rw [map_pow, e, map_one]))
    · exact Or.inr (φ.injective (by rw [map_pow, e]))
  · rcases h2 ((hP ψ).2 hψP) (by rw [← map_pow, hψ2, map_one]) with e | e
    · exact Or.inl (φ.injective (by rw [e, map_one]))
    · exact Or.inr (φ.injective e)

theorem cycAt_map {v : G} (h : CycAt P A (φ v)) : CycAt P A v := by
  obtain ⟨φ₀, hφ₀, hall⟩ := h
  obtain ⟨φ₁, rfl⟩ := φ.surjective φ₀
  refine ⟨φ₁, (hA φ₁).1 hφ₀, fun ψ hψ hfix => ?_⟩
  obtain ⟨k, hk⟩ := hall (φ ψ) ((hA ψ).2 hψ) (fix3_map φ hP hfix)
  exact ⟨k, φ.injective (by rw [hk, map_pow])⟩

end Map

theorem conj_mem_iff (hnorm : ∀ g ∈ A, ∀ y ∈ P, g * y * g⁻¹ ∈ P) {g : G} (hg : g ∈ A) :
    ∀ y, MulAut.conj g y ∈ P ↔ y ∈ P := by
  intro y
  rw [MulAut.conj_apply]
  refine ⟨fun h => ?_, hnorm g hg y⟩
  have h1 := hnorm g⁻¹ (A.inv_mem hg) _ h
  have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
  rwa [e] at h1

theorem conj_mem_iff_self {g : G} (hg : g ∈ A) : ∀ y, MulAut.conj g y ∈ A ↔ y ∈ A := by
  intro y
  rw [MulAut.conj_apply]
  refine ⟨fun h => ?_, fun h => A.mul_mem (A.mul_mem hg h) (A.inv_mem hg)⟩
  have h1 := A.mul_mem (A.mul_mem (A.inv_mem hg) h) hg
  have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
  rwa [e] at h1

variable (hnorm : ∀ g ∈ A, ∀ y ∈ P, g * y * g⁻¹ ∈ P) {g x : G} (hg : g ∈ A)
include hnorm hg

theorem outCent3At_of_conj (h : OutCent3At P A (g * x * g⁻¹)) : OutCent3At P A x :=
  outCent3At_map (MulAut.conj g) (conj_mem_iff hnorm hg) (conj_mem_iff_self hg) h

theorem bangAt_of_conj (h : BangAt P (g * x * g⁻¹)) : BangAt P x :=
  bangAt_map (MulAut.conj g) (conj_mem_iff hnorm hg) h

theorem innerSqAt_of_conj (h : InnerSqAt P A (g * x * g⁻¹)) : InnerSqAt P A x :=
  innerSqAt_map (MulAut.conj g) (conj_mem_iff hnorm hg) (conj_mem_iff_self hg) h

theorem cycAt_of_conj (h : CycAt P A (g * x * g⁻¹)) : CycAt P A x :=
  cycAt_map (MulAut.conj g) (conj_mem_iff hnorm hg) (conj_mem_iff_self hg) h

end Pred

section Tests

variable {n : Nat} [Small n]

theorem fixC_iff (cs : List (CV n)) (ψ : CV n) :
    fixC cs ψ = true ↔ ∀ c ∈ cs, ψ * c = c * ψ := by
  simp only [fixC, List.all_eq_true, eq22C_eq, decide_eq_true_eq]

theorem inC_iff (L : List (CV n)) (x : CV n) : inC L x = true ↔ x ∈ L := by
  simp only [inC, List.any_eq_true, decide_eq_true_eq, exists_eq_right]

theorem ev_eq_one_iff (a : CV n) : ev a = 1 ↔ a = 1 := by
  rw [← ev_one, ev_injective.eq_iff]

theorem ev_comm_iff (a b : CV n) : ev a * ev b = ev b * ev a ↔ a * b = b * a := by
  rw [← ev_mul, ← ev_mul, ev_injective.eq_iff]

theorem ev_pow_eq_one_iff (a : CV n) (k : Nat) : ev a ^ k = 1 ↔ a ^ k = 1 := by
  rw [ev_pow', ev_eq_one_iff]

theorem ev_sq (a : CV n) : ev a ^ 2 = ev (a * a) := by rw [pow_two, ev_mul]

theorem sub3C_iff (cs : List (CV n)) (τ : CV n) :
    sub3C cs τ = true ↔ ∀ c ∈ cs, c ^ 3 = 1 ∧ c * τ = τ * c := by
  simp only [sub3C, List.all_eq_true, Bool.and_eq_true, powOneC_eq, eq22C_eq, decide_eq_true_eq]

variable {P A S : Subgroup (Equiv.Perm (Fin n))}

theorem pass_split {LA LS gs csO csI pl : List (CV n)} {τ v : CV n}
    (h : passA LA LS gs csO csI pl τ v = true) :
    (∀ ψ ∈ LA, outT csO τ ψ = true) ∧ (∀ ψ ∈ LA, innerT csI v ψ = true) ∧
      (∀ ψ ∈ LA, cycT csI pl ψ = true) ∧ (∀ ψ ∈ LA, centT LS gs ψ = true) ∧
      (∀ ψ ∈ LA, sqT LS gs ψ = true) := by
  simp only [passA, List.all_eq_true, Bool.and_eq_true] at h
  exact ⟨fun ψ hψ => (h ψ hψ).1.1.1.1, fun ψ hψ => (h ψ hψ).1.1.1.2, fun ψ hψ => (h ψ hψ).1.1.2,
    fun ψ hψ => (h ψ hψ).1.2, fun ψ hψ => (h ψ hψ).2⟩

theorem fixC_of_fix3 {cs : List (CV n)} {τ : CV n} (hsub : sub3C cs τ = true)
    (hcP : ∀ c ∈ cs, ev c ∈ P) {ψ : CV n} (h : Fix3 P (ev τ) (ev ψ)) : fixC cs ψ = true := by
  rw [fixC_iff]
  intro c hc
  obtain ⟨h3, hcτ⟩ := (sub3C_iff cs τ).1 hsub c hc
  exact (ev_comm_iff ψ c).1 (h (ev c) (hcP c hc) ((ev_pow_eq_one_iff c 3).2 h3)
    ((ev_comm_iff c τ).2 hcτ))

variable {LA : List (CV n)} (hLA : ∀ x ∈ A, ∃ y ∈ LA, ev y = x)
include hLA

theorem outCent3_of_pass {csO : List (CV n)} {τ : CV n} (hsub : sub3C csO τ = true)
    (hcP : ∀ c ∈ csO, ev c ∈ P) (h : ∀ ψ ∈ LA, outT csO τ ψ = true) :
    OutCent3At P A (ev τ) := by
  intro x hx hfix
  obtain ⟨ψ, hψ, rfl⟩ := hLA x hx
  have h1 := h ψ hψ
  simp only [outT, fixC_of_fix3 hsub hcP hfix, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    decide_eq_true_eq] at h1
  rcases h1 with rfl | rfl
  · exact Or.inl ev_one
  · exact Or.inr rfl

theorem innerSq_of_pass {csI : List (CV n)} {v : CV n} (hsub : sub3C csI v = true)
    (hcP : ∀ c ∈ csI, ev c ∈ P) (h : ∀ ψ ∈ LA, innerT csI v ψ = true) :
    InnerSqAt P A (ev v) := by
  intro x hx hfix
  obtain ⟨ψ, hψ, rfl⟩ := hLA x hx
  have h1 := h ψ hψ
  simp only [innerT, fixC_of_fix3 hsub hcP hfix, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at h1
  obtain ⟨h2, h3⟩ := h1
  rw [ev_sq, ev_eq_one_iff, ev_injective.eq_iff]
  refine ⟨h2, fun _ hψ2 => ?_⟩
  rcases h3 with (h3 | rfl) | rfl
  · exact absurd hψ2 h3
  · exact Or.inl ev_one
  · exact Or.inr rfl

theorem cyc_of_pass {csI pl : List (CV n)} {v φ : CV n} (hsub : sub3C csI v = true)
    (hcP : ∀ c ∈ csI, ev c ∈ P) (hφ : ev φ ∈ A) (hpl : ∀ p ∈ pl, ∃ k : ℕ, p = φ ^ k)
    (h : ∀ ψ ∈ LA, cycT csI pl ψ = true) : CycAt P A (ev v) := by
  refine ⟨ev φ, hφ, fun x hx hfix => ?_⟩
  obtain ⟨ψ, hψ, rfl⟩ := hLA x hx
  have h1 := h ψ hψ
  simp only [cycT, fixC_of_fix3 hsub hcP hfix, Bool.not_true, Bool.false_or, inC_iff] at h1
  obtain ⟨k, rfl⟩ := hpl ψ h1
  exact ⟨k, (ev_pow' φ k).symm⟩

variable {LS gs : List (CV n)} (hLS : ∀ y ∈ LS, ev y ∈ S) (hgs : ∀ g ∈ gs, ev g ∈ S)
include hLS hgs

theorem sylCent_of_pass (h : ∀ ψ ∈ LA, centT LS gs ψ = true) :
    ∀ ψ ∈ A, (∀ q ∈ S, q * ψ = ψ * q) → ψ ∈ S := by
  intro x hx hc
  obtain ⟨ψ, hψ, rfl⟩ := hLA x hx
  have hf : fixC gs ψ = true := by
    rw [fixC_iff]
    intro g hg
    exact (ev_comm_iff ψ g).1 (hc (ev g) (hgs g hg)).symm
  have h1 := h ψ hψ
  simp only [centT, hf, Bool.not_true, Bool.false_or, inC_iff] at h1
  exact hLS ψ h1

omit hLS in
theorem sylSq_of_pass (hLS' : ∀ x ∈ S, ∃ y ∈ LS, ev y = x)
    (hgen : S ≤ closure {σ | σ ∈ gs.map ev}) (h : ∀ ψ ∈ LA, sqT LS gs ψ = true) :
    ∀ ψ ∈ A, ψ ∉ P → (∀ q ∈ S, ψ * q * ψ⁻¹ ∈ S) → ∀ v ∈ S, v ^ 2 = 1 → v ≠ 1 →
      (∀ c ∈ P, c ^ 3 = 1 → c * v = v * c → ψ * c = c * ψ) → ψ ^ 2 = v →
      ∀ q ∈ S, q * v = v * q := by
  intro x hx _ hnorm v hv hv2 hv1 _ hxv
  obtain ⟨ψ, hψ, rfl⟩ := hLA x hx
  subst hxv
  have inS : ∀ z : CV n, ev z ∈ S → inC LS z = true := fun z hz => by
    obtain ⟨y, hy, e⟩ := hLS' _ hz
    rw [inC_iff, ← ev_injective e]
    exact hy
  have hc : (!decide (ψ * ψ = 1) && decide (ψ * ψ * (ψ * ψ) = 1) && inC LS (ψ * ψ) &&
      gs.all fun q => inC LS (ψ * q * ψ⁻¹)) = true := by
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
      List.all_eq_true]
    rw [ev_sq] at hv hv1 hv2
    refine ⟨⟨⟨fun e => hv1 (by rw [e, ev_one]), ?_⟩, inS _ hv⟩, fun q hq => inS _ ?_⟩
    · rw [pow_two, ← ev_mul, ev_eq_one_iff] at hv2
      exact hv2
    · rw [ev_mul, ev_mul, ev_inv]
      exact hnorm _ (hgs q hq)
  have h1 := h ψ hψ
  simp only [sqT, hc, Bool.not_true, Bool.false_or, fixC_iff] at h1
  have hcl : closure {σ | σ ∈ gs.map ev} ≤ centralizer {ev ψ ^ 2} := by
    rw [closure_le]
    intro σ hσ
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hσ
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff, ev_sq, ev_comm_iff]
    exact (h1 g hg).symm
  intro q hq
  have := hcl (hgen hq)
  rwa [mem_centralizer_singleton_iff] at this

end Tests

section Witness

variable {n : Nat} [Small n] {P S : Subgroup (Equiv.Perm (Fin n))}

theorem bang_of_check {τ l c₁ c₂ : CV n} (hl : ev l ∈ P) (hc₁ : ev c₁ ∈ P) (hc₂ : ev c₂ ∈ P)
    (h : bangC τ l c₁ c₂ = true) : BangAt P (ev τ) := by
  simp only [bangC, Bool.and_eq_true, powOneC_eq, eq22C_eq, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨ev l, hl, ev c₁, hc₁, ev c₂, hc₂, (ev_pow_eq_one_iff _ 3).2 h1,
    (ev_pow_eq_one_iff _ 3).2 h2, fun e => h3 ((ev_eq_one_iff _).1 e),
    fun e => h4 ((ev_eq_one_iff _).1 e), (ev_comm_iff _ _).2 h5, (ev_comm_iff _ _).2 h6, ?_, ?_, ?_⟩
  · rw [ev_mul', ev_pow_eq_one_iff]
    exact h7
  · rw [ev_mul', Ne, ev_eq_one_iff]
    exact h8
  · rw [← ev_inv, ← ev_inv, ← ev_mul, ← ev_mul, ← ev_mul, ← ev_mul, h9]

theorem word_of_check {s0 a b : CV n} (ha : ev a ∈ P) (hb : ev b ∈ P)
    (h : wordWC s0 a b = true) :
    ∃ a ∈ P, ∃ b ∈ P, a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a * ev s0 = ev s0 * a ∧
      b * ev s0 = ev s0 * b ∧ (a * b) ^ 3 = ev s0 := by
  simp only [wordWC, Bool.and_eq_true, powOneC_eq, eq22C_eq, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨ev a, ha, ev b, hb, (ev_pow_eq_one_iff _ 3).2 h1, (ev_pow_eq_one_iff _ 3).2 h2,
    fun e => h3 ((ev_eq_one_iff _).1 e), fun e => h4 ((ev_eq_one_iff _).1 e),
    (ev_comm_iff _ _).2 h5, (ev_comm_iff _ _).2 h6, ?_⟩
  rw [pow_three', ← ev_mul, ← ev_mul, ← ev_mul, h7]

theorem conj4_of_check {LS refs : List (CV n)} (hLS' : ∀ x ∈ S, ∃ y ∈ LS, ev y = x)
    (hrefs : ∀ c ∈ refs, ev c ∈ P) (h : conj4C LS refs = true) :
    ∀ a ∈ S, a ^ 4 = 1 → a ^ 2 ≠ 1 →
      (∀ c ∈ P, c ^ 3 = 1 → c * a ^ 2 = a ^ 2 * c → c * a = a * c) →
      ∃ k ∈ P, k⁻¹ * a * k ∈ S ∧ ∀ y ∈ S, y * (k⁻¹ * a * k) = (k⁻¹ * a * k) * y := by
  intro x hx h4 h2 hfix
  exfalso
  obtain ⟨a, ha, rfl⟩ := hLS' x hx
  have h1 := List.all_eq_true.1 h a ha
  have h4' : powOneC a 4 = true := by
    rw [powOneC_eq, decide_eq_true_eq]
    exact (ev_pow_eq_one_iff a 4).1 h4
  have h2' : powOneC a 2 = false := by
    rw [powOneC_eq, decide_eq_false_iff_not]
    exact fun e => h2 ((ev_pow_eq_one_iff a 2).2 e)
  rw [h4', h2'] at h1
  simp only [Bool.not_false, Bool.and_true, Bool.true_and, Bool.not_true, Bool.false_or,
    List.any_eq_true, Bool.and_eq_true, powOneC_eq, eq22C_eq, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at h1
  obtain ⟨c, hc, ⟨hc3, hca⟩, hna⟩ := h1
  refine hna ((ev_comm_iff c a).1 (hfix (ev c) (hrefs c hc) ((ev_pow_eq_one_iff c 3).2 hc3) ?_))
  rw [ev_sq, ev_comm_iff]
  exact hca

end Witness

end CFSG.Certificates.Kernel.PkCV.OutR

end
