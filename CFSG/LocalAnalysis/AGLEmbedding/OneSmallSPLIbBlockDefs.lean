module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section
namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def KFactBlockCentRankIb : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), IsComponentOf L ⊤ →
    IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → IsParabolicTwo L J → J ≠ L →
    (∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y)) →
    ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ D : Subgroup Y, ⁅D, D⁆ = D → D ≤ J ⊔ Subgroup.centralizer (L : Set Y) →
    (∀ A : Subgroup Y, A ≤ D → IsPGroup p A → IsCyclic A) →
    (∀ V : Subgroup Y, V ≤ J → ⁅V, V⁆ = V → ∀ k : ℕ, p ^ k ∣ Nat.card V →
      p ^ k ∣ Nat.card D) →
    ∀ x ∈ D, x ^ p = 1 → x ∉ Subgroup.centralizer (L : Set Y) →
    (∀ W : Subgroup Y, W ≤ L → ⁅W, W⁆ = W → W ≤ Subgroup.centralizer ({x} : Set Y) → W = ⊥) →
    ∀ E : Subgroup Y, E ≤ Subgroup.normalizer (L : Set Y) →
      E ≤ Subgroup.centralizer (D : Set Y) → IsElemAbelian p E → Nat.card E = p ^ 2 →
      (E ⊓ (L ⊔ Subgroup.centralizer (L : Set Y)) = ⊥ ∨
        E ≤ J ⊔ Subgroup.centralizer (L : Set Y)) →
      E ⊓ Subgroup.centralizer (L : Set Y) ≠ ⊥

@[expose] def KFactBlockCentCycIb : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), IsComponentOf L ⊤ →
    IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → IsParabolicTwo L J → J ≠ L →
    (∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y)) →
    ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ D : Subgroup Y, ⁅D, D⁆ = D → D ≤ J ⊔ Subgroup.centralizer (L : Set Y) →
    (∀ A : Subgroup Y, A ≤ D → IsPGroup p A → IsCyclic A) →
    (∀ V : Subgroup Y, V ≤ J → ⁅V, V⁆ = V → ∀ k : ℕ, p ^ k ∣ Nat.card V →
      p ^ k ∣ Nat.card D) →
    ∀ x ∈ D, x ^ p = 1 → x ∉ Subgroup.centralizer (L : Set Y) →
    (∀ W : Subgroup Y, W ≤ L → ⁅W, W⁆ = W → W ≤ Subgroup.centralizer ({x} : Set Y) → W = ⊥) →
    ∀ E : Subgroup Y, E ≤ Subgroup.normalizer (L : Set Y) → IsPGroup p E →
      (∃ u ∈ E, ∀ e ∈ E, ∃ k : ℕ, e * (u ^ k)⁻¹ ∈ L ⊔ Subgroup.centralizer (L : Set Y)) ∧
      (E ≤ J ⊔ Subgroup.centralizer (L : Set Y) → E ≤ Subgroup.centralizer (D : Set Y) →
        ∃ u ∈ E, ∀ e ∈ E, ∃ k : ℕ, e * (u ^ k)⁻¹ ∈ Subgroup.centralizer (L : Set Y))

section Count

variable {Y : Type*} [Group Y] [Finite Y]

theorem card_le_mul_card_inf_of_cov {p : ℕ} (hp : 0 < p) {E N : Subgroup Y} {u : Y}
    (hu : u ∈ E) (hup : u ^ p = 1) (hcov : ∀ e ∈ E, ∃ k : ℕ, e * (u ^ k)⁻¹ ∈ N) :
    Nat.card E ≤ p * Nat.card (E ⊓ N : Subgroup Y) := by
  classical
  let f : Fin p × ↥(E ⊓ N) → ↥E := fun x =>
    ⟨(x.2 : Y) * u ^ (x.1 : ℕ), E.mul_mem x.2.2.1 (E.pow_mem hu _)⟩
  have hf : Function.Surjective f := by
    rintro ⟨e, he⟩
    obtain ⟨k, hk⟩ := hcov e he
    have hkm : u ^ k = u ^ (k % p) := by
      conv_lhs => rw [← Nat.div_add_mod k p, pow_add, pow_mul, hup, one_pow, one_mul]
    have hmem : e * (u ^ k)⁻¹ ∈ E ⊓ N := ⟨E.mul_mem he (E.inv_mem (E.pow_mem hu k)), hk⟩
    refine ⟨(⟨k % p, Nat.mod_lt k hp⟩, ⟨e * (u ^ k)⁻¹, hmem⟩), Subtype.ext ?_⟩
    show e * (u ^ k)⁻¹ * u ^ (k % p) = e
    rw [← hkm, inv_mul_cancel_right]
  have h1 := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin p), Fintype.card_fin] at h1

theorem card_le_of_cov_of_inf_eq_bot {p : ℕ} (hp : 0 < p) {E N : Subgroup Y} {u : Y}
    (hu : u ∈ E) (hup : u ^ p = 1) (hcov : ∀ e ∈ E, ∃ k : ℕ, e * (u ^ k)⁻¹ ∈ N)
    (hEN : E ⊓ N = ⊥) : Nat.card E ≤ p := by
  have h := card_le_mul_card_inf_of_cov hp hu hup hcov
  rwa [hEN, Subgroup.card_bot, mul_one] at h

end Count

theorem kFactBlockCentRankIb_of_cyc (h : KFactBlockCentCycIb) : KFactBlockCentRankIb := by
  intro Y _ _ L J hL hcl hpar hne hnB p hp hp5 D hDp hDJ hDcyc hDpart x hxD hxp hxC hxW E hEL hED
    hEel hEcard hdisj hEC
  have hEp : IsPGroup p E := fun e => ⟨1, Subtype.ext (by simpa using hEel.2 e e.2)⟩
  have hpp : p < p ^ 2 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  obtain ⟨ha, hb⟩ := h Y L J hL hcl hpar hne hnB p hp hp5 D hDp hDJ hDcyc hDpart x hxD hxp hxC hxW
    E hEL hEp
  rcases hdisj with h0 | hJ
  · obtain ⟨u, hu, hcov⟩ := ha
    have := card_le_of_cov_of_inf_eq_bot hp.pos hu (hEel.2 u hu) hcov h0
    omega
  · obtain ⟨u, hu, hcov⟩ := hb hJ hED
    have := card_le_of_cov_of_inf_eq_bot hp.pos hu (hEel.2 u hu) hcov hEC
    omega

end CFSG.AGLEmbedding
