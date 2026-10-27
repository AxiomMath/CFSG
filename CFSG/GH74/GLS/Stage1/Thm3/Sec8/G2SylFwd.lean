module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2SylCore
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier

public section

open Subgroup

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl

theorem ShapeConds.map {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) {S A : Subgroup X}
    {a t y : X} {n : ℕ} (h : ShapeConds S A a t y n) :
    ShapeConds (S.map φ.toMonoidHom) (A.map φ.toMonoidHom) (φ a) (φ t) (φ y) n := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  have hconj : φ (t⁻¹ * a * t) = (φ t)⁻¹ * φ a * φ t := by simp [map_mul, map_inv]
  have hinj : Function.Injective φ.toMonoidHom := φ.injective
  have hz : ∀ x : X, (zpowers x).map φ.toMonoidHom = zpowers (φ x) :=
    fun x => MonoidHom.map_zpowers _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, h1]
  · rw [h2, Subgroup.map_sup, hz, hz, hconj]
  · rw [← hconj, ← hz, ← hz, ← Subgroup.map_inf_eq _ _ _ hinj, h3, Subgroup.map_bot]
  · rw [← hconj, ← map_mul, ← map_mul, h4]
  · rw [← map_mul, h5, map_one]
  · rw [← map_mul, h6, map_one]
  · rw [← map_mul, ← map_mul, h7]
  · intro hc; apply h8; exact φ.injective (by rw [hc, map_one])
  · intro hc; apply h9; exact φ.injective (by rw [hc, map_one])
  · intro hc; apply h10; exact φ.injective hc
  · rw [← hz, ← hz, ← Subgroup.map_sup, ← Subgroup.map_inf_eq _ _ _ hinj, h11, Subgroup.map_bot]
  · rintro _ ⟨x, hx, rfl⟩
    change φ y * φ x * φ y = (φ x)⁻¹
    rw [← map_mul, ← map_mul, h12 x hx, map_inv]
  · rw [h13, h2, Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup, hz, hz, hz, hz, hconj]

theorem three_le_factorization_sq_sub_one {q : ℕ} (hq : q % 2 = 1) (hq1 : 1 < q) :
    3 ≤ (q ^ 2 - 1).factorization 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, q = 2 * k + 1 := ⟨q / 2, by omega⟩
  have hne : (2 * k + 1) ^ 2 - 1 ≠ 0 := by
    have : 1 < (2 * k + 1) ^ 2 := Nat.one_lt_pow (by norm_num) hq1
    omega
  have hdvd : 2 ^ 3 ∣ (2 * k + 1) ^ 2 - 1 := by
    obtain ⟨r, hr⟩ := Nat.even_mul_succ_self k
    refine ⟨r, ?_⟩
    have h1 : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
    omega
  exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).1 hdvd

section Fwd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem g2_sylow_shapeConds_fwd :
    ∀ (Gs : Type) [Group Gs] [Finite Gs] (p f : ℕ), p.Prime → p ≠ 2 → 0 < f →
      LieModel Gs .G2 0 p f → ∀ S' : Sylow 2 Gs, ∃ (A : Subgroup Gs) (a t y : Gs) (n : ℕ),
        2 ≤ n ∧ ShapeConds (S' : Subgroup Gs) A a t y n ∧
          ((p ^ f) ^ 2 - 1).factorization 2 = n + 1 := by
  intro Gs _ _ p f hp hp2 hf hL S'
  have hm : ChevalleyExceptionalModel Gs .G2 p f := by
    rcases hL with ⟨ht, -⟩ | ⟨-, -, hm⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact hm
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨K, _, _, hcard, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm.2
  have hodd : Nat.card K % 2 = 1 := by
    rw [hcard]; exact Nat.odd_iff.1 ((hp.odd_of_ne_two hp2).pow)
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have h3 := three_le_factorization_sq_sub_one hodd hq1
  have hval : (Nat.card K ^ 2 - 1).factorization 2 = ((Nat.card K ^ 2 - 1).factorization 2 - 1) + 1 := by
    omega
  obtain ⟨T, A₀, a₀, t₀, y₀, hS₀⟩ :=
    exists_sylow_shapeConds_adjointG2 K hodd ((Nat.card K ^ 2 - 1).factorization 2 - 1) hval
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T' : Sylow 2 ↥(adjointGroup .G2 K) := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S'
  have hT' : (T' : Subgroup ↥(adjointGroup .G2 K)) = (S' : Subgroup Gs).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(adjointGroup .G2 K) T T'
  have hTT' : (T : Subgroup ↥(adjointGroup .G2 K)).map (MulAut.conj g).toMonoidHom =
      (T' : Subgroup ↥(adjointGroup .G2 K)) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  let ψ : ↥(adjointGroup .G2 K) ≃* Gs := (MulAut.conj g).trans e.symm
  have hψ : (T : Subgroup ↥(adjointGroup .G2 K)).map ψ.toMonoidHom = (S' : Subgroup Gs) := by
    have h1 : ψ.toMonoidHom = e.symm.toMonoidHom.comp (MulAut.conj g).toMonoidHom := rfl
    rw [h1, ← Subgroup.map_map, hTT', hT', Subgroup.map_map]
    have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id Gs := by ext x; simp
    rw [this, Subgroup.map_id]
  have hsc := ShapeConds.map ψ hS₀
  rw [hψ] at hsc
  refine ⟨_, _, _, _, (Nat.card K ^ 2 - 1).factorization 2 - 1, by omega, hsc, ?_⟩
  rw [← hcard]; exact hval

end Fwd

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl
