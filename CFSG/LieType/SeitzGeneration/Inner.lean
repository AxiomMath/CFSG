module

public import CFSG.Assembly.Defs
public import CFSG.LieType.SeitzGeneration.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Confinement

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2

theorem conj_injective_of_simple_perfect {K : Type*} [Group K] [IsSimpleGroup K]
    (hperf : commutator K = ⊤) : Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MulAut.conj : K →* MulAut K).ker with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : K, a * b = b * a := fun a b => by
      have ha : a ∈ (MulAut.conj : K →* MulAut K).ker := h ▸ Subgroup.mem_top a
      have := congrArg (fun φ : MulAut K => φ b) ha
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc a * b = a * b * a⁻¹ * a := by group
        _ = b * a := by rw [this]
    have hbot : commutator K = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro g _
      rw [Subgroup.mem_centralizer_iff]
      intro h _
      exact (hcomm h g)
    have htb : (⊤ : Subgroup K) = ⊥ := hperf.symm.trans hbot
    obtain ⟨x, hx⟩ := exists_ne (1 : K)
    have hx' : x ∈ (⊥ : Subgroup K) := htb ▸ Subgroup.mem_top x
    exact hx (Subgroup.mem_bot.mp hx')

theorem conj_injective_of_simple_of_range_ne_bot {K : Type*} [Group K] [IsSimpleGroup K]
    (h : (MulAut.conj : K →* MulAut K).range ≠ ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MulAut.conj : K →* MulAut K).ker with h' | h'
  · exact h'
  · exact absurd (MonoidHom.range_eq_bot_iff.mpr (MonoidHom.ker_eq_top_iff.mp h')) h

theorem range_conj_ne_bot_of_inner {K : Type*} [Group K] {p : ℕ} (hp : p.Prime)
    {E : Subgroup (MulAut K)} (hc : Nat.card E = p ^ 2)
    (hinner : E ≤ (MulAut.conj : K →* MulAut K).range) :
    (MulAut.conj : K →* MulAut K).range ≠ ⊥ := by
  intro hbot
  have hEbot : E = ⊥ := le_bot_iff.mp (hbot ▸ hinner)
  rw [hEbot, Subgroup.card_bot] at hc
  have := hp.one_lt
  nlinarith

theorem conj_injective_of_mulEquiv {K P : Type*} [Group K] [Group P] (e : K ≃* P)
    (h : Function.Injective (MulAut.conj : P →* MulAut P)) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hP : MulAut.conj (e g) = MulAut.conj (1 : P) := by
    rw [map_one]
    ext y
    have := congrArg (fun φ : MulAut K => φ (e.symm y)) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this ⊢
    simpa using congrArg e this
  exact e.injective (by rw [h hP, map_one])

theorem isElemAbelian_comap_conj {K : Type*} [Group K] {p : ℕ}
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.comap (MulAut.conj : K →* MulAut K)) := by
  obtain ⟨⟨hc⟩, hx⟩ := hE
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx' => ?_⟩
  · apply Subtype.ext
    apply hinj
    have := hc.comm ⟨MulAut.conj (a : K), a.2⟩ ⟨MulAut.conj (b : K), b.2⟩
    have h := congrArg Subtype.val this
    change MulAut.conj ((a : K) * b) = MulAut.conj ((b : K) * a)
    rw [map_mul, map_mul]
    exact h
  · apply hinj
    rw [map_pow, map_one]
    exact hx _ hx'

theorem planeGen_of_inner_model {K P : Type*} [Group K] [Group P] {p : ℕ}
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) (e : K ≃* P)
    (hP : ∀ E₁ : Subgroup P, IsElemAbelian p E₁ → Nat.card E₁ = p ^ 2 →
      Subgroup.closure {k' : P | ∃ x ∈ E₁, x ≠ 1 ∧ k' * x = x * k'} = ⊤)
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hinner : E ≤ (MulAut.conj : K →* MulAut K).range) : PlaneGen E := by
  set E₀ : Subgroup K := E.comap (MulAut.conj : K →* MulAut K) with hE₀
  have hmap : E₀.map (MulAut.conj : K →* MulAut K) = E := Subgroup.map_comap_eq_self hinner
  have hE₀el : IsElemAbelian p E₀ := isElemAbelian_comap_conj hinj hE
  have hE₀card : Nat.card E₀ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap, hc]
  have hE₁el : IsElemAbelian p (E₀.map e.toMonoidHom) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE₀el _
  have hE₁card : Nat.card (E₀.map e.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective e.injective, hE₀card]
  have h1 := hP _ hE₁el hE₁card
  have hle : (⊤ : Subgroup P) ≤
      (Subgroup.closure {k : K | ∃ x ∈ E₀, x ≠ 1 ∧ k * x = x * k}).map e.toMonoidHom := by
    rw [MonoidHom.map_closure, ← h1]
    refine Subgroup.closure_mono ?_
    rintro k' ⟨_, ⟨x, hx, rfl⟩, hx1, hk⟩
    refine ⟨e.symm k', ⟨x, hx, ?_, ?_⟩, by simp⟩
    · rintro rfl
      exact hx1 (map_one _)
    · apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hk
  have h2 : Subgroup.closure {k : K | ∃ x ∈ E₀, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
    rw [eq_top_iff]
    intro k _
    obtain ⟨c, hc', hck⟩ := hle (Subgroup.mem_top (e k))
    exact (e.injective hck) ▸ hc'
  rw [PlaneGen, eq_top_iff, ← h2, Subgroup.closure_le]
  intro k ⟨x, hx, hx1, hk⟩
  refine mem_planeClosure_of_fixed (E := E) (e := MulAut.conj x) ?_ ?_ ?_
  · exact hx
  · intro h
    exact hx1 (hinj (by simpa using h))
  · rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
    exact hk.symm

theorem planeGen_of_inner {K : Type*} [Group K] {p : ℕ}
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    (hK : ∀ E₁ : Subgroup K, IsElemAbelian p E₁ → Nat.card E₁ = p ^ 2 →
      Subgroup.closure {k' : K | ∃ x ∈ E₁, x ≠ 1 ∧ k' * x = x * k'} = ⊤)
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hinner : E ≤ (MulAut.conj : K →* MulAut K).range) : PlaneGen E :=
  planeGen_of_inner_model hinj (MulEquiv.refl K) hK hE hc hinner

end CFSG.LieType.SeitzGeneration
