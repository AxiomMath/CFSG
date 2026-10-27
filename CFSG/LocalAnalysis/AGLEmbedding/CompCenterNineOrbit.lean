module

public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

public section

namespace CFSG.AGLEmbedding.CompCenterNine

theorem card_pow_eq_one_eq_index {G : Type*} [Group G] [Finite G] {n : ℕ} (P : G →* G)
    (hP : ∀ g, P g = g ^ n) : Nat.card {g : G // g ^ n = 1} = P.range.index := by
  have h1 := Subgroup.card_ker_mul_card_range P
  have h2 := P.range.card_mul_index
  have h3 : Nat.card {g : G // g ^ n = 1} = Nat.card P.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight fun g => by rw [MonoidHom.mem_ker, hP])
  rw [h3]
  refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := P.range)) ?_
  rw [h1, ← h2, mul_comm]

theorem card_pow_eq_one_le_of_surjective {A B : Type*} [Group A] [Group B] [Finite A]
    (hA : ∀ a b : A, a * b = b * a) (φ : A →* B) (hφ : Function.Surjective φ) (n : ℕ) :
    Nat.card {b : B // b ^ n = 1} ≤ Nat.card {a : A // a ^ n = 1} := by
  have : Finite B := Finite.of_surjective φ hφ
  have hB : ∀ a b : B, a * b = b * a := by
    intro a b
    obtain ⟨a, rfl⟩ := hφ a
    obtain ⟨b, rfl⟩ := hφ b
    rw [← map_mul, ← map_mul, hA]
  let PA : A →* A := MonoidHom.mk' (fun a => a ^ n) fun a b => Commute.mul_pow (hA a b) n
  let PB : B →* B := MonoidHom.mk' (fun a => a ^ n) fun a b => Commute.mul_pow (hB a b) n
  rw [card_pow_eq_one_eq_index PA (fun _ => rfl), card_pow_eq_one_eq_index PB (fun _ => rfl),
    ← Subgroup.index_comap_of_surjective (H := PB.range) hφ]
  have hle : PA.range ≤ PB.range.comap φ := by
    rintro _ ⟨a, rfl⟩
    exact ⟨φ a, (map_pow φ a n).symm⟩
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.index_dvd_of_le hle)

variable {X : Type*} [Group X] [Finite X]

theorem centralizer_le_ker_of_transitive {O : Type*} [Group O] [Finite O] (E : Subgroup X)
    (hE9 : Nat.card E = 9) (Φ : X →* O) (hO : Nat.card O ≤ 8)
    (hker : ∀ x : X, Φ x = 1 → ∀ e ∈ E, x * e * x⁻¹ = e)
    (htr : ∀ e ∈ E, e ≠ 1 → ∀ f ∈ E, f ≠ 1 → ∃ n : X, n * e * n⁻¹ = f) {e : X} (he : e ∈ E)
    (he1 : e ≠ 1) : Subgroup.centralizer {e} ≤ Φ.ker ∧ Function.Surjective Φ := by
  classical
  set C := Subgroup.centralizer ({e} : Set X) with hC
  have hKC : Φ.ker ≤ C := fun x hx => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    have h := hker x hx e he
    calc x * e = x * e * x⁻¹ * x := by group
      _ = e * x := by rw [h]
  have hconj : ∀ f : {f : E // f ≠ 1}, ∃ n : X, n * e * n⁻¹ = f.1 := fun f =>
    htr e he he1 f.1 f.1.2 fun h => f.2 (Subtype.ext h)
  let g : {f : E // f ≠ 1} → X ⧸ C := fun f => ((hconj f).choose : X ⧸ C)
  have hg : Function.Injective g := by
    intro f f' hff'
    have h := QuotientGroup.eq.mp hff'
    rw [hC, Subgroup.mem_centralizer_singleton_iff] at h
    have h1 := (hconj f).choose_spec
    have h2 := (hconj f').choose_spec
    set n := (hconj f).choose
    set n' := (hconj f').choose
    apply Subtype.ext
    apply Subtype.ext
    rw [← h1, ← h2]
    calc n * e * n⁻¹ = n * (e * (n⁻¹ * n')) * (n⁻¹ * n')⁻¹ * n⁻¹ := by group
      _ = n * (n⁻¹ * n' * e) * (n⁻¹ * n')⁻¹ * n⁻¹ := by rw [h]
      _ = n' * e * n'⁻¹ := by group
  have hcard8 : 8 ≤ Nat.card {f : E // f ≠ 1} := by
    let o : E → Option {f : E // f ≠ 1} := fun f => if h : f = 1 then none else some ⟨f, h⟩
    have ho : Function.Injective o := by
      intro f f' hff'
      by_cases hf : f = 1 <;> by_cases hf' : f' = 1 <;> simp_all [o]
    have := Nat.card_le_card_of_injective o ho
    rw [Finite.card_option, hE9] at this
    omega
  have hCidx : 8 ≤ C.index := by
    rw [Subgroup.index_eq_card]
    exact hcard8.trans (Nat.card_le_card_of_injective g hg)
  have hKidx : Φ.ker.index ≤ 8 := by
    rw [Subgroup.index_ker]
    exact (Subgroup.card_le_card_group _).trans hO
  have hrel := Subgroup.relIndex_mul_index hKC
  have hrel0 : Φ.ker.relIndex C ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hrel
    exact Subgroup.index_ne_zero_of_finite hrel.symm
  have hrel1 : Φ.ker.relIndex C = 1 := by
    by_contra hne
    have h2 : 2 * C.index ≤ Φ.ker.relIndex C * C.index :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  refine ⟨Subgroup.relIndex_eq_one.mp hrel1, ?_⟩
  rw [← MonoidHom.range_eq_top, ← Subgroup.card_eq_iff_eq_top]
  refine le_antisymm (Subgroup.card_le_card_group _) ?_
  rw [← Subgroup.index_ker, ← hrel, hrel1, one_mul]
  omega

theorem inv_of_involution_of_transitive {O : Type*} [Group O] [Finite O] (E : Subgroup X)
    (hEn : ∀ n : X, ∀ e ∈ E, n * e * n⁻¹ ∈ E) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE9 : Nat.card E = 9) (Φ : X →* O) (hO : Nat.card O ≤ 8)
    (hker : ∀ x : X, Φ x = 1 → ∀ e ∈ E, x * e * x⁻¹ = e)
    (htr : ∀ e ∈ E, e ≠ 1 → ∀ f ∈ E, f ≠ 1 → ∃ n : X, n * e * n⁻¹ = f) {x : X}
    (hx1 : Φ x ≠ 1) (hx2 : Φ x ^ 2 = 1) {e : X} (he : e ∈ E) : x * e * x⁻¹ = e⁻¹ := by
  have hxe : x * e * x⁻¹ ∈ E := hEn x e he
  have hsq : (x * x) * e * (x * x)⁻¹ = e := hker (x * x) (by rw [map_mul, ← sq, hx2]) e he
  set u := e * (x * e * x⁻¹) with hu
  have huE : u ∈ E := E.mul_mem he hxe
  have hxu : x * u * x⁻¹ = u := by
    calc x * u * x⁻¹ = (x * e * x⁻¹) * ((x * x) * e * (x * x)⁻¹) := by rw [hu]; group
      _ = (x * e * x⁻¹) * e := by rw [hsq]
      _ = u := by rw [hu, hEc _ hxe e he]
  by_contra hne
  have hu1 : u ≠ 1 := by
    intro h1
    apply hne
    rw [hu] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hxC : x ∈ Subgroup.centralizer ({u} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * u = x * u * x⁻¹ * x := by group
      _ = u * x := by rw [hxu]
  exact hx1 ((centralizer_le_ker_of_transitive E hE9 Φ hO hker htr huE hu1).1 hxC)

theorem exists_not_conj_of_two_involutions {O : Type*} [Group O] [Finite O] (E : Subgroup X)
    (hEn : ∀ n : X, ∀ e ∈ E, n * e * n⁻¹ ∈ E) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE9 : Nat.card E = 9) (Φ : X →* O) (hO : Nat.card O ≤ 8)
    (hker : ∀ x : X, Φ x = 1 → ∀ e ∈ E, x * e * x⁻¹ = e) {a b : O} (ha : a ≠ 1) (hb : b ≠ 1)
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) (hab : a ≠ b) :
    ∃ e ∈ E, e ≠ 1 ∧ ∃ f ∈ E, f ≠ 1 ∧ ∀ n : X, n * e * n⁻¹ ≠ f := by
  by_contra hcon
  push Not at hcon
  obtain ⟨e₀, he₀, he₀1⟩ : ∃ e ∈ E, e ≠ 1 := by
    have hne : E ≠ ⊥ := by
      rintro rfl
      rw [Subgroup.card_bot] at hE9
      omega
    obtain ⟨e, he1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    exact ⟨e, e.2, fun h => he1 (Subtype.ext h)⟩
  have hreg := centralizer_le_ker_of_transitive E hE9 Φ hO hker hcon he₀ he₀1
  obtain ⟨x, rfl⟩ := hreg.2 a
  obtain ⟨y, rfl⟩ := hreg.2 b
  have hx := inv_of_involution_of_transitive E hEn hEc hE9 Φ hO hker hcon ha ha2 he₀
  have hy := inv_of_involution_of_transitive E hEn hEc hE9 Φ hO hker hcon hb hb2 he₀
  have hyx : y⁻¹ * x ∈ Subgroup.centralizer ({e₀} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y⁻¹ * x * e₀ = y⁻¹ * (x * e₀ * x⁻¹) * x := by group
      _ = y⁻¹ * (y * e₀ * y⁻¹) * x := by rw [hx, hy]
      _ = e₀ * (y⁻¹ * x) := by group
  have h1 := hreg.1 hyx
  rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h1
  exact hab h1.symm

end CFSG.AGLEmbedding.CompCenterNine
