module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Escape

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G]

theorem le_of_inf_ne_bot_of_normalizer_le {p : ℕ} (hp : p.Prime) {M : Subgroup G}
    (hN : ∀ Y : Subgroup G, Y ≤ M → IsPGroup p Y → Y ≠ ⊥ → Subgroup.normalizer (Y : Set G) ≤ M)
    {S : Subgroup G} (hS : IsPGroup p S) (hSM : S ⊓ M ≠ ⊥) : S ≤ M := by
  have : Fact p.Prime := ⟨hp⟩
  exact le_of_normalizer_inf_le hS fun x hx =>
    hN (S ⊓ M) inf_le_right (hS.to_le inf_le_left) hSM hx.2

omit [Finite G] in
theorem mem_normalizer_of_map_conj_eq {S : Subgroup G} {h : G}
    (hS : S.map (MulAut.conj h).toMonoidHom = S) : h ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · intro hs
    rw [← hS]
    exact ⟨s, hs, by simp⟩
  · intro hs
    rw [← hS] at hs
    obtain ⟨s', hs', hss⟩ := hs
    have : s' = s := by
      have h1 : h * s' * h⁻¹ = h * s * h⁻¹ := by simpa using hss
      simpa using h1
    exact this ▸ hs'

theorem stronglyEmbedded_of_normalizer_le {p : ℕ} (hp : p.Prime) {M : Subgroup G} (hM : M ≠ ⊤)
    (P : Sylow p G) (hPM : (P : Subgroup G) ≤ M) (hP1 : (P : Subgroup G) ≠ ⊥)
    (hN : ∀ Y : Subgroup G, Y ≤ M → IsPGroup p Y → Y ≠ ⊥ → Subgroup.normalizer (Y : Set G) ≤ M) :
    GLBStronglyEmbedded p M := by
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨hM, ?_, ?_⟩
  · have h1 : p ∣ Nat.card (P : Subgroup G) := by
      rcases P.isPGroup'.card_eq_or_dvd with h | h
      · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hP1
      · exact h
    exact h1.trans (Subgroup.card_dvd_of_le hPM)
  · intro g hg hdvd
    apply hg
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(M ⊓ GLBConj g M)) p hdvd
    set x0 : G := (x : G) with hx0
    have hx0o : orderOf x0 = p := by rw [hx0, Subgroup.orderOf_coe]; exact hx
    have hx0M : x0 ∈ M := x.2.1
    have hx01 : x0 ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hx0o
      exact hp.one_lt.ne hx0o
    obtain ⟨m, hmM, hmx⟩ := (Subgroup.mem_map.mp x.2.2)
    have hmx' : m = g * x0 * g⁻¹ := by
      have : g⁻¹ * m * g = x0 := by simpa [MulAut.conj_apply] using hmx
      calc m = g * (g⁻¹ * m * g) * g⁻¹ := by group
        _ = g * x0 * g⁻¹ := by rw [this]
    have hm1 : m ≠ 1 := by
      rw [hmx']
      intro h1
      apply hx01
      simpa using h1
    have hmp : m ^ p = 1 := by
      rw [hmx']
      have : (g * x0 * g⁻¹) ^ p = g * x0 ^ p * g⁻¹ := by
        rw [conj_pow]
      rw [this, ← hx0o, pow_orderOf_eq_one]
      simp
    have hZp : IsPGroup p (Subgroup.zpowers m) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, orderOf_eq_prime hmp hm1]
      simp
    obtain ⟨S₂, hS₂⟩ := hZp.exists_le_sylow
    have hmS₂ : m ∈ (S₂ : Subgroup G) := hS₂ (Subgroup.mem_zpowers m)
    have hS₂M : (S₂ : Subgroup G) ≤ M := by
      refine le_of_inf_ne_bot_of_normalizer_le hp hN S₂.isPGroup' ?_
      intro hbot
      have : m ∈ (S₂ : Subgroup G) ⊓ M := ⟨hmS₂, hmM⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact hm1 this
    set S₃ : Subgroup G := (S₂ : Subgroup G).map (MulAut.conj g⁻¹).toMonoidHom with hS₃
    have hS₃p : IsPGroup p S₃ := S₂.isPGroup'.map _
    have hx0S₃ : x0 ∈ S₃ := ⟨m, hmS₂, by
      rw [hmx']; simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]; group⟩
    have hS₃M : S₃ ≤ M := by
      refine le_of_inf_ne_bot_of_normalizer_le hp hN hS₃p ?_
      intro hbot
      have : x0 ∈ S₃ ⊓ M := ⟨hx0S₃, hx0M⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact hx01 this
    obtain ⟨c, hc⟩ := exists_conjugate_le_sylow_of_le p S₂ hS₂M hS₃M hS₃p
    have hcard : Nat.card (S₃.map (MulAut.conj (c : G)).toMonoidHom) = Nat.card (S₂ : Subgroup G) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj (c : G)).injective,
        Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    have heq : S₃.map (MulAut.conj (c : G)).toMonoidHom = (S₂ : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge hc (le_of_eq hcard.symm)
    have hnorm : (c : G) * g⁻¹ ∈ Subgroup.normalizer ((S₂ : Subgroup G) : Set G) := by
      refine mem_normalizer_of_map_conj_eq ?_
      have h1 : (S₂ : Subgroup G).map (MulAut.conj ((c : G) * g⁻¹)).toMonoidHom =
          S₃.map (MulAut.conj (c : G)).toMonoidHom := by
        rw [hS₃, Subgroup.map_map]
        congr 1
        ext y
        simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
          MulAut.conj_apply, mul_inv_rev, inv_inv]
        group
      rw [h1, heq]
    have hS₂1 : (S₂ : Subgroup G) ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.mem_bot] at hmS₂
      exact hm1 hmS₂
    have hcg : (c : G) * g⁻¹ ∈ M := hN S₂ hS₂M S₂.isPGroup' hS₂1 hnorm
    have : g⁻¹ ∈ M := by
      have := M.mul_mem (M.inv_mem c.2) hcg
      simpa [mul_assoc] using this
    simpa using M.inv_mem this

omit [Finite G] in
theorem mem_of_map_conj_le_of_stronglyEmbedded {p : ℕ} (hp : p.Prime) {M Y A' : Subgroup G}
    (hM : GLBStronglyEmbedded p M) (hY : IsPGroup p Y) (hY1 : Y ≠ ⊥) (hYM : Y ≤ M)
    (hA' : A' ≤ M) {g : G} (hg : Y.map (MulAut.conj g).toMonoidHom ≤ A') : g ∈ M := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hgM
  have hle : Y ≤ M ⊓ GLBConj g M := by
    refine le_inf hYM ?_
    intro y hy
    refine ⟨g * y * g⁻¹, hA' (hg ⟨y, hy, rfl⟩), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  apply hM.2.2 g hgM
  have hpY : p ∣ Nat.card Y := by
    rcases hY.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hY1
    · exact h
  exact hpY.trans (Subgroup.card_dvd_of_le hle)

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
