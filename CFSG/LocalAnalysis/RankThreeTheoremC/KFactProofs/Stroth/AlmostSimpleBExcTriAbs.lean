module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBG2Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup
open scoped Pointwise

section

theorem exists_normalized_two_group {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (C : Subgroup X) (N : Subgroup C) [N.Normal] (hodd : ¬ Odd (Nat.card N))
    (hcop : Nat.Coprime p (Nat.card N)) (P : Sylow p C) :
    ∃ R : Subgroup X, R ≠ ⊥ ∧ IsPGroup 2 R ∧
      (P : Subgroup C).map C.subtype ≤ Subgroup.normalizer (R : Set X) := by
  classical
  have h2 : 2 ∣ Nat.card N := (Nat.not_odd_iff_even.1 hodd).two_dvd
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_normalized_of_isPGroup (ℓ := 2) N (P : Subgroup C)
    P.isPGroup' hcop
  have hSne : (S : Subgroup N) ≠ ⊥ := by
    intro h0
    have h1 : Nat.card (S : Subgroup N) = 1 := by rw [h0]; simp
    rw [Sylow.card_eq_multiplicity] at h1
    have hf : 1 ≤ (Nat.card N).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2
    have := Nat.one_lt_pow (by omega : (Nat.card N).factorization 2 ≠ 0) (by norm_num : 1 < 2)
    omega
  set A : Subgroup C := (S : Subgroup N).map N.subtype with hA
  set R : Subgroup X := A.map C.subtype with hR
  have hR2 : IsPGroup 2 R := by
    intro x
    obtain ⟨_, ⟨s, hs, rfl⟩, hx⟩ := x.2
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
    refine ⟨k, ?_⟩
    have hk' : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hx, ← map_pow, ← map_pow, hk', map_one, map_one]
  have hRne : R ≠ ⊥ := by
    intro h0
    apply hSne
    have h1 : A = ⊥ := (Subgroup.map_eq_bot_iff_of_injective A C.subtype_injective).1 h0
    exact (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).1 h1
  exact ⟨R, hRne, hR2, (Subgroup.map_mono hS).trans (Subgroup.le_normalizer_map C.subtype)⟩

theorem false_of_sylow_subgroup {C G : Type*} [Group C] [Finite C] [Group G] {p : ℕ}
    (hp : p.Prime) (P : Sylow p C) (φ : C →* G) (hφ : Function.Injective φ)
    (E : Subgroup G) (hEφ : E ≤ φ.range) (hEp : ∀ y ∈ E, y ^ p = 1) {m : ℕ}
    (hP : ∀ E' : Subgroup G, E' ≤ (P : Subgroup C).map φ → (∀ y ∈ E', y ^ p = 1) →
      Nat.card E' ≤ m)
    (hE : m < Nat.card E) : False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set E₁ : Subgroup C := E.comap φ with hE₁
  have hE₁exp : ∀ e ∈ E₁, e ^ p = 1 := fun e he =>
    hφ (by rw [map_pow, map_one]; exact hEp _ he)
  have hE₁p : IsPGroup p E₁ := by
    intro y
    refine ⟨1, ?_⟩
    rw [pow_one]
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hE₁exp _ y.2
  have hmap : E₁.map φ = E := Subgroup.map_comap_eq_self hEφ
  have hcard : Nat.card E₁ = Nat.card E := by
    rw [← hmap, Subgroup.card_map_of_injective hφ]
  obtain ⟨Q, hQ⟩ := hE₁p.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C P Q
  set E₂ : Subgroup C := E₁.map (MulAut.conj g⁻¹).toMonoidHom with hE₂
  have hE₂P : E₂ ≤ (P : Subgroup C) := by
    rintro _ ⟨e, he, rfl⟩
    have heQ : e ∈ (Q : Subgroup C) := hQ he
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
      MulAut.smul_def, MulAut.conj_apply] at heQ
    simpa [MulAut.conj_apply] using heQ
  have hcard2 : Nat.card E₂ = Nat.card E := by
    rw [hE₂, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hcard]
  have hle : (E₂.map φ) ≤ (P : Subgroup C).map φ := Subgroup.map_mono hE₂P
  have hexp : ∀ y ∈ E₂.map φ, y ^ p = 1 := by
    rintro _ ⟨e, ⟨e₁, he₁, rfl⟩, rfl⟩
    rw [← map_pow, ← map_pow, hE₁exp e₁ he₁, map_one, map_one]
  have h3 := hP _ hle hexp
  rw [Subgroup.card_map_of_injective hφ, hcard2] at h3
  omega

end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
