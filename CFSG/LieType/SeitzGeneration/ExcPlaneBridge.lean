module

public import CFSG.LieType.SeitzGeneration.ExcParabolicModel
public import CFSG.LieType.SeitzGeneration.Inner
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LieType.SeitzGeneration.Defs

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2 CFSG.PreuniquenessRankFour.Helpers

theorem isElemAbelian_of_le {G : Type*} [Group G] {p : ℕ} {E F : Subgroup G} (hEF : E ≤ F)
    (hF : IsElemAbelian p F) : IsElemAbelian p E := CFSG.Open.IsElemAbelian.mono hF hEF

theorem isPGroup_of_isElemAbelian {G : Type*} [Group G] {p : ℕ} {F : Subgroup G}
    (hF : IsElemAbelian p F) : IsPGroup p F := CFSG.Open.IsElemAbelian.isPGroup hF

theorem exists_isElemAbelian_card_of_le {G : Type*} [Group G] {p k : ℕ} (hp : p.Prime)
    {F : Subgroup G} (hF : IsElemAbelian p F) (hk : p ^ k ≤ Nat.card F) :
    ∃ E : Subgroup G, E ≤ F ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k := by
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite F := Nat.finite_of_card_ne_zero (by have := pow_pos hp.pos k; omega)
  obtain ⟨n, hn⟩ := (isPGroup_of_isElemAbelian hF).exists_card_eq
  have hkn : k ≤ n := by
    by_contra h
    have : p ^ n < p ^ k := Nat.pow_lt_pow_right hp.one_lt (not_le.mp h)
    omega
  obtain ⟨E', hE'⟩ := Sylow.exists_subgroup_card_pow_prime (G := F) p
    (show p ^ k ∣ Nat.card F from ⟨p ^ (n - k), by rw [hn, ← pow_add]; congr 1; omega⟩)
  exact ⟨E'.map F.subtype, Subgroup.map_subtype_le E',
    isElemAbelian_of_le (Subgroup.map_subtype_le E') hF,
    by rw [Subgroup.card_map_of_injective F.subtype_injective, hE']⟩

theorem exists_isElemAbelian_card_of_not_rankLE2 {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (h : ¬ RankLE2 p G) :
    (∃ E : Subgroup G, IsElemAbelian p E ∧ Nat.card E = p ^ 2) ∧
      ∃ E : Subgroup G, IsElemAbelian p E ∧ Nat.card E = p ^ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, hF, hlt⟩ : ∃ F : Subgroup G, IsElemAbelian p F ∧ p ^ 2 < Nat.card F := by
    unfold RankLE2 at h
    push Not at h
    exact h
  have hfin : Finite F := Nat.finite_of_card_ne_zero (by have := pow_pos hp.pos 2; omega)
  obtain ⟨n, hn⟩ := (isPGroup_of_isElemAbelian hF).exists_card_eq
  have h2n : 2 < n := by
    by_contra hn2
    have : p ^ n ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos (not_lt.mp hn2)
    omega
  have h3 : p ^ 3 ≤ Nat.card F := hn ▸ Nat.pow_le_pow_right hp.pos h2n
  obtain ⟨E₂, -, hE₂, hc₂⟩ := exists_isElemAbelian_card_of_le hp hF hlt.le
  obtain ⟨E₃, -, hE₃, hc₃⟩ := exists_isElemAbelian_card_of_le hp hF h3
  exact ⟨⟨E₂, hE₂, hc₂⟩, ⟨E₃, hE₃, hc₃⟩⟩

theorem rankLE2_of_noPowThree {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (h : ∀ E : Subgroup G, (∀ x ∈ E, x ^ p = 1) → Nat.card E = p ^ 3 → False) :
    RankLE2 p G := by
  by_contra hr
  obtain ⟨-, E, hE, hc⟩ := exists_isElemAbelian_card_of_not_rankLE2 hp hr
  exact h E hE.2 hc

theorem rankLE2_of_injective {K L : Type*} [Group K] [Group L] (f : K →* L)
    (hf : Function.Injective f) {p : ℕ} (hp : p.Prime)
    (h : ∀ E : Subgroup L, (∀ x ∈ E, x ^ p = 1) → Nat.card E = p ^ 3 → False) :
    RankLE2 p K := by
  refine rankLE2_of_noPowThree hp fun E hE hc => h (E.map f) ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE x hx, map_one]
  · rw [Subgroup.card_map_of_injective hf, hc]

theorem RankLE2.of_injective {K L : Type*} [Group K] [Group L] {p : ℕ} (f : K →* L)
    (hf : Function.Injective f) (h : RankLE2 p L) : RankLE2 p K := fun F hF => by
  have := h (F.map f) (elementary_abelian_map p hF f)
  rwa [Subgroup.card_map_of_injective hf] at this

theorem rankLE2_of_elemAbelian_cyclic {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (h : ∀ F : Subgroup G, IsElemAbelian p F → IsCyclic F) : RankLE2 p G := by
  intro F hF
  have := h F hF
  have hexp : Monoid.exponent F ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by simpa using hF.2 x x.2)
  rw [← IsCyclic.exponent_eq_card]
  exact (Nat.le_of_dvd hp.pos hexp).trans (Nat.le_self_pow two_ne_zero p)

theorem odd_card_of_isElemAbelian {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {F : Subgroup G} (hF : IsElemAbelian p F) : Odd (Nat.card F) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := (isPGroup_of_isElemAbelian hF).exists_card_eq
  rw [hn]
  exact (hp.eq_two_or_odd'.resolve_left hp2).pow

theorem conj_injective_of_center_eq_bot {K : Type*} [Group K] (h : Subgroup.center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  have hmem : c ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro n
    have h1 := DFunLike.congr_fun hc n
    rw [MulAut.conj_apply, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  rwa [h, Subgroup.mem_bot] at hmem

theorem exists_plane_of_subgroup {K : Type*} [Group K] {p : ℕ}
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) {E₀ R : Subgroup K}
    (hE₀ : IsElemAbelian p E₀) (hcard : Nat.card E₀ = p ^ 2)
    (hn : E₀ ≤ Subgroup.normalizer (R : Set K)) :
    ∃ E : Subgroup (MulAut K), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      E ≤ (MulAut.conj : K →* MulAut K).range ∧ ∀ ε ∈ E, R.map ε.toMonoidHom = R := by
  refine ⟨E₀.map (MulAut.conj : K →* MulAut K), elementary_abelian_map p hE₀ _, ?_,
    Subgroup.map_le_range _ _, ?_⟩
  · rw [Subgroup.card_map_of_injective hinj, hcard]
  · rintro _ ⟨g, hg, rfl⟩
    have hgn : g ∈ Subgroup.normalizer (R : Set K) := hn hg
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 hgn y).1 hy
    · intro hx
      refine ⟨g⁻¹ * x * g, (Subgroup.mem_normalizer_iff.1 hgn _).2 ?_, ?_⟩
      · have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
        rw [this]
        exact hx
      · show g * (g⁻¹ * x * g) * g⁻¹ = x
        group

theorem exists_plane_of_native {C G : Type*} [Group C] [Group G] {N : Subgroup G} (e : C ≃* N)
    (hZ : Subgroup.center N = ⊥) {r p : ℕ} {A R : Subgroup G} (hAN : A ≤ N)
    (hA : IsElemAbelian p A) (hAcard : Nat.card A = p ^ 2) (hRN : R ≤ N) (hRp : IsPGroup r R)
    (hR : R ≠ ⊥) (hAR : A ≤ Subgroup.normalizer (R : Set G)) :
    ∃ E : Subgroup (MulAut C), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      E ≤ (MulAut.conj : C →* MulAut C).range ∧
        ∃ R' : Subgroup C, R' ≠ ⊥ ∧ IsPGroup r R' ∧ ∀ ε ∈ E, R'.map ε.toMonoidHom = R' := by
  let ι : C →* G := N.subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hrange : ∀ {H : Subgroup G}, H ≤ N → H ≤ ι.range := fun {H} hH x hx =>
    ⟨e.symm ⟨x, hH hx⟩, by simp [ι]⟩
  have hmapA : (A.comap ι).map ι = A := Subgroup.map_comap_eq_self (hrange hAN)
  have hmapR : (R.comap ι).map ι = R := Subgroup.map_comap_eq_self (hrange hRN)
  have hinj : Function.Injective (MulAut.conj : C →* MulAut C) :=
    conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot hZ)
  have hA₀ : IsElemAbelian p (A.comap ι) := isElemAbelian_comap_of_injective ι hι hA
  have hA₀card : Nat.card (A.comap ι) = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hι, hmapA, hAcard]
  have hR₀p : IsPGroup r (R.comap ι) :=
    hRp.of_injective (ι.subgroupComap R) fun x y h => by
      have h' := congrArg Subtype.val h
      exact Subtype.ext (hι h')
  have hR₀ : R.comap ι ≠ ⊥ := fun h => hR (by rw [← hmapR, h, Subgroup.map_bot])
  have hn : A.comap ι ≤ Subgroup.normalizer ((R.comap ι : Subgroup C) : Set C) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h := Subgroup.mem_normalizer_iff.1 (hAR hc) (ι x)
    simpa [map_mul, map_inv] using h
  obtain ⟨E, hE, hEc, hEin, hEn⟩ := exists_plane_of_subgroup hinj hA₀ hA₀card hn
  exact ⟨E, hE, hEc, hEin, R.comap ι, hR₀, hR₀p, hEn⟩

end CFSG.LieType.SeitzGeneration
