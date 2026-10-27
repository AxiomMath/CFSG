module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBI2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBI1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzDefs

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped Pointwise

section Chart

variable {G : Type} [Group G] [Finite G] {c : Bool} {T₂ P : Subgroup G} {x₁ x₂ t q s lam : G}
  {β : ℕ → G}

theorem fzb_chart_card (hβ : FzbChart c T₂ P x₁ x₂ t q s lam β) (X : Subgroup G) :
    Nat.card {x : ℕ // x < 1024 ∧ β x ∈ X} = Nat.card ↥(T₂ ⊓ X) := by
  let f : {x : ℕ // x < 1024 ∧ β x ∈ X} → ↥(T₂ ⊓ X) :=
    fun x => ⟨β x, ⟨hβ.mem x x.2.1, x.2.2⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply Subtype.ext
      exact hβ.inj a.1 a.2.1 b.1 b.2.1 (by simpa [f] using congrArg Subtype.val hab)
    · intro g
      obtain ⟨x, hx, hxβ⟩ := hβ.surj g.1 g.2.1
      refine ⟨⟨x, hx, ?_⟩, ?_⟩
      · rw [hxβ]
        exact g.2.2
      · apply Subtype.ext
        exact hxβ
  exact Nat.card_congr (Equiv.ofBijective f hf)

theorem fzb_chart_comm (hβ : FzbChart c T₂ P x₁ x₂ t q s lam β)
    (hlt : ∀ x < 1024, ∀ y < 1024, fzbMul c x y < 1024) {x y : ℕ} (hx : x < 1024)
    (hy : y < 1024) : fzbMul c x y = fzbMul c y x ↔ β x * β y = β y * β x := by
  have hxy := hβ.mul x hx y hy
  have hyx := hβ.mul y hy x hx
  constructor
  · intro h
    rw [← hxy, ← hyx, h]
  · intro h
    exact hβ.inj _ (hlt x hx y hy) _ (hlt y hy x hx) (by rw [hxy, hyx, h])

theorem fzb_chart_conj (hβ : FzbChart c T₂ P x₁ x₂ t q s lam β)
    (hlt : ∀ x < 1024, ∀ y < 1024, fzbMul c x y < 1024) {g x y : ℕ} (hg : g < 1024)
    (hx : x < 1024) (hy : y < 1024) :
    fzbMul c g x = fzbMul c y g ↔ β g * β x * (β g)⁻¹ = β y := by
  have hgx := hβ.mul g hg x hx
  have hyg := hβ.mul y hy g hg
  have heq : fzbMul c g x = fzbMul c y g ↔
      β (fzbMul c g x) = β (fzbMul c y g) := by
    constructor
    · exact congrArg β
    · intro h
      exact hβ.inj _ (hlt g hg x hx) _ (hlt y hy g hg) h
  rw [heq, hgx, hyg]
  exact (mul_inv_eq_iff_eq_mul (a := β g * β x) (b := β g) (c := β y)).symm

theorem fzb_subgroup_of_codes (hβ : FzbChart c T₂ P x₁ x₂ t q s lam β)
    (hlt : ∀ x < 1024, ∀ y < 1024, fzbMul c x y < 1024) {A : Finset ℕ} (h0 : 0 ∈ A)
    (hA : ∀ x ∈ A, x < 1024) (hmul : ∀ x ∈ A, ∀ y ∈ A, fzbMul c x y ∈ A) :
    ∃ E : Subgroup G, E ≤ T₂ ∧ Nat.card E = A.card ∧ ∀ x < 1024, β x ∈ E ↔ x ∈ A := by
  let S : Set G := {g | ∃ x ∈ A, β x = g}
  have hS1 : S.Nonempty := ⟨1, 0, h0, hβ.one⟩
  have hS2 : S * S = S := by
    ext g
    constructor
    · intro hg
      rw [Set.mem_mul] at hg
      obtain ⟨a, ⟨x, hxA, rfl⟩, b, ⟨y, hyA, rfl⟩, rfl⟩ := hg
      exact ⟨fzbMul c x y, hmul x hxA y hyA, hβ.mul x (hA x hxA) y (hA y hyA)⟩
    · intro hg
      obtain ⟨x, hxA, rfl⟩ := hg
      rw [Set.mem_mul]
      exact ⟨1, ⟨0, h0, hβ.one⟩, β x, ⟨x, hxA, rfl⟩, one_mul _⟩
  let E : Subgroup G := subgroupOfIdempotent S hS1 hS2
  refine ⟨E, ?_, ?_, ?_⟩
  · intro g hg
    change g ∈ S at hg
    obtain ⟨x, hxA, rfl⟩ := hg
    exact hβ.mem x (hA x hxA)
  · let f : {x : ℕ // x ∈ A} → E :=
      fun x => ⟨β x, show β x ∈ S from ⟨x, x.2, rfl⟩⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        apply Subtype.ext
        exact hβ.inj a.1 (hA a.1 a.2) b.1 (hA b.1 b.2)
          (by simpa [f] using congrArg (fun z : E => (z : G)) hab)
      · intro g
        have hgS : (g : G) ∈ S := g.2
        obtain ⟨x, hxA, hxβ⟩ := hgS
        exact ⟨⟨x, hxA⟩, by apply Subtype.ext; exact hxβ⟩
    calc Nat.card E = Nat.card {x : ℕ // x ∈ A} :=
          (Nat.card_congr (Equiv.ofBijective f hf)).symm
      _ = A.card := Nat.card_eq_finsetCard A
  · intro x hx
    constructor
    · intro hxE
      have hxS : β x ∈ S := hxE
      obtain ⟨x', hx'A, hx'β⟩ := hxS
      have hxx : x' = x := hβ.inj x' (hA x' hx'A) x hx hx'β
      simpa [hxx] using hx'A
    · intro hxA
      change β x ∈ S
      exact ⟨x, hxA, rfl⟩

theorem fzb_exists_M (hβ : FzbChart c T₂ P x₁ x₂ t q s lam β) (hF : FzbFactsGen c)
    (hcard : Nat.card T₂ = 2 ^ 10) :
    ∃ M : Subgroup G, M ≤ T₂ ∧ M.relIndex T₂ = 2 ∧ ∀ x < 1024, β x ∈ M ↔ fzbIsM x := by
  let A : Finset ℕ := (Finset.range 1024).filter fzbIsM
  have h0 : 0 ∈ A := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr (by norm_num), by norm_num [fzbIsM]⟩
  have hA : ∀ x ∈ A, x < 1024 := by
    intro x hx
    exact Finset.mem_range.mp (Finset.mem_filter.mp hx).1
  have hmul : ∀ x ∈ A, ∀ y ∈ A, fzbMul c x y ∈ A := by
    intro x hx y hy
    rw [Finset.mem_filter] at hx hy ⊢
    exact ⟨Finset.mem_range.mpr (hF.mul_lt x (Finset.mem_range.mp hx.1) y
        (Finset.mem_range.mp hy.1)),
      hF.M_mul x (Finset.mem_range.mp hx.1) hx.2 y (Finset.mem_range.mp hy.1) hy.2⟩
  obtain ⟨M, hMle, hMcard, hMmem⟩ := fzb_subgroup_of_codes hβ hF.mul_lt h0 hA hmul
  refine ⟨M, hMle, ?_, ?_⟩
  · have hAcard : A.card = 512 := by simpa only [A] using hF.card_M
    have hcard' : Nat.card T₂ = 1024 := by rw [hcard]; norm_num
    have hrel := Subgroup.relIndex_mul_card (H := M) (K := T₂)
    have hinf : M ⊓ T₂ = M := le_antisymm inf_le_left (le_inf le_rfl hMle)
    rw [hinf, hMcard, hAcard, hcard'] at hrel
    omega
  · intro x hx
    rw [hMmem x hx]
    change x ∈ (Finset.range 1024).filter fzbIsM ↔ fzbIsM x
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩

end Chart

section Struct

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}
  {T₂ P : Subgroup G} {q s : G}

theorem fzb_sylow_T2 (hS : FzbStruct t S x₁ x₂ lam rho tau T₂ P q s)
    (h2 : ¬ 2 ^ 11 ∣ Nat.card G) : FzSylow T₂ := by
  refine ⟨hS.isPGroup, ?_⟩
  intro hdvd
  apply h2
  obtain ⟨k, hk⟩ := hdvd
  have hc := Subgroup.index_mul_card (H := T₂)
  rw [hS.card_T₂] at hc
  refine ⟨k, ?_⟩
  rw [← hc, hk]
  ring

theorem fzb_nonab (h : Ctx t L S x₁ x₂ lam rho tau) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  have hcomm : lam * x₁ = x₁ * lam := hc lam x₁
  have hx : x₂ = x₁ := by
    rw [← h.wreath.conj_x₁, hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hbot : x₁ ∈ (⊥ : Subgroup G) := by
    rw [← h.wreath.inf_eq_bot]
    exact ⟨Subgroup.mem_zpowers x₁, by rw [hx]; exact Subgroup.mem_zpowers x₁⟩
  have hone : x₁ = 1 := by simpa using hbot
  have h4 : orderOf x₁ = 4 := h.wreath.ord_x₁
  rw [hone, orderOf_one] at h4
  norm_num at h4

end Struct

end CFSG.OddStandard.SmallF3.FritzII
