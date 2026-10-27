module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsCases
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsLifts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Solomon.Coordinator

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {x : X} {π : Bool} {p f : ℕ}
  {K : Type} [Field K] {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L}

theorem LModel.exists_isFieldAt [L.Normal] (M : LModel L π p f K ν)
    (hC : centralizer (L : Set X) = ⊥) (hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3) :
    ∃ (φ : X) (σ : K ≃+* K) (H : GL (Fin 3) K), φ ^ 3 = 1 ∧ IsFieldAt ν φ σ H := by
  obtain ⟨A, hA, hA27⟩ := exists_elemAbelian_27 hX
  by_contra hno
  push Not at hno
  have hlift : ∀ a ∈ A, ∃ y, IsLiftAt ν a y := fun a ha => by
    rcases M.dichotomy (hA.2 a ha) with h' | ⟨σ, H, h'⟩
    · exact h'
    · exact absurd h' (hno a σ H (hA.2 a ha))
  have h9 := M.card_le_nine_of_isLiftAt hA (fun a _ hac => by
    rw [hC] at hac
    exact Subgroup.mem_bot.1 hac) hlift
  omega

theorem LModel.exists_conj_conjBy (M : LModel L π p f K ν) {g H : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) (hH : H ∈ glPi π 3 (p ^ f) K) {a b c : Kˣ}
    (hD : diagUnits a b c ∈ slPi π 3 (p ^ f) K) :
    ∃ l ∈ L, l * ((ν (M.conjBy hg ⟨diagUnits a b c, hD⟩) : ↥L) : X) * l⁻¹ =
      ((ν (M.conjBy hH ⟨diagUnits a b c, hD⟩) : ↥L) : X) := by
  obtain ⟨l₁, hl₁, h₁⟩ := M.exists_conj_diag hg hD
  obtain ⟨l₂, hl₂, h₂⟩ := M.exists_conj_diag hH hD
  refine ⟨l₂ * l₁⁻¹, mul_mem hl₂ (inv_mem hl₁), ?_⟩
  rw [← h₁, ← h₂]
  group

theorem LModel.false_of_proj_inner (h : T29Setup X L x) (M : LModel L π p f K ν)
    (hproj : ∀ s ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K), ν s = 1) (hxL : x ∈ L) {φ : X}
    {σ : K ≃+* K} {H : GL (Fin 3) K} (hφ3 : φ ^ 3 = 1) (hφ : IsFieldAt ν φ σ H) : False := by
  haveI hLn : L.Normal := h.normal
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau M.piField M.modThree
  have hφL := M.not_mem_of_isFieldAt hφ
  have hσ := hφ.order
  obtain ⟨s, hs⟩ := M.surj ⟨x, hxL⟩
  have hsx : ((ν s : ↥L) : X) = x := by rw [hs]
  have hs3 : (s : GL (Fin 3) K) ^ 3 ∈ StatedScalars (Fin 3) K := by
    have : ν (s ^ 3) = 1 := by
      rw [map_pow]
      apply Subtype.ext
      rw [Subgroup.coe_pow, hsx, T29Setup.pow_three h, Subgroup.coe_one]
    have := M.ker_scalar _ this
    simpa using this
  have hsZ : (s : GL (Fin 3) K) ∉ zPi π 3 (p ^ f) K := by
    intro hz
    apply T29Setup.ne_one h
    rw [← hsx, M.map_eq_one_of_mem_statedScalars hproj
      (mem_statedScalars_of_mem_zPi M.piField M.modThree hτ hτ1 hz), Subgroup.coe_one]
  have hsH : (s : GL (Fin 3) K) ∈ glPi π 3 (p ^ f) K := slPi_le_glPi M.hπ s.2
  have hs3Z : (s : GL (Fin 3) K) ^ 3 ∈ zPi π 3 (p ^ f) K := by
    rw [zPi_eq M.hπ M.hq' hτ hτ1]
    exact Subgroup.mem_inf.2 ⟨pow_mem hsH 3, hs3⟩
  have hconj : ∀ {a : X} {k : X}, k * a * k⁻¹ = x →
      3 ≤ CFSG.Open.pRank 3 (centralizer ({a} : Set X)) → False := by
    intro a k hk h3
    have hle := le_pRank_centralizer_of_mulEquiv (MulAut.conj k⁻¹) x
    simp only [MulAut.conj_apply, inv_inv] at hle
    rw [show k⁻¹ * x * k = a by rw [← hk]; group] at hle
    have := h.cent
    omega
  rcases (rank3II_4_10_two M.piField M.modThree hτ hτ1 hsH hsZ hs3Z).1
      ⟨s, s.2, fun m _ => rfl⟩ with ⟨y, ⟨z, hz, rfl⟩, g, hg, hD⟩ |
      ⟨⟨y, ⟨z, hz, rfl⟩, g, hg, e, he, hD⟩, -⟩
  ·
    obtain ⟨w, -, hw⟩ := diagTau_eq_diagUnits' hτ
    have hDs : diagUnits w (w ^ 2) 1 ∈ slPi π 3 (p ^ f) K := by
      rw [← hw]
      exact diagTau_mem_slPi M.hπ M.hq' hτ
    have hsg : ν s = ν (M.conjBy hg ⟨diagUnits w (w ^ 2) 1, hDs⟩) := by
      have hz' := mem_statedScalars_of_mem_zPi M.piField M.modThree hτ hτ1 hz
      have : ν (s * (M.conjBy hg ⟨diagUnits w (w ^ 2) 1, hDs⟩)⁻¹) = 1 := by
        refine M.map_eq_one_of_mem_statedScalars hproj ?_
        rw [Subgroup.coe_mul, Subgroup.coe_inv, M.coe_conjBy]
        show (s : GL (Fin 3) K) * (g * diagUnits w (w ^ 2) 1 * g⁻¹)⁻¹ ∈ StatedScalars (Fin 3) K
        rw [← hw, ← hD, show (s : GL (Fin 3) K) * (g * (g⁻¹ * (↑s * z) * g) * g⁻¹)⁻¹ =
          (s : GL (Fin 3) K) * z⁻¹ * (s : GL (Fin 3) K)⁻¹ by group]
        exact (conj_mem_statedScalars_iff _ _).2 (inv_mem hz')
      rw [map_mul, map_inv, mul_inv_eq_one] at this
      exact this
    obtain ⟨l, hl, hlx⟩ := M.exists_conj_conjBy hg hφ.mem hDs
    have hpair : IsE9Pair L ((ν (M.conjBy hφ.mem ⟨diagUnits w (w ^ 2) 1, hDs⟩) : ↥L) : X)
        ((ν (M.conjBy hφ.mem ⟨cycThree, cycThree_mem_slPi M.hπ⟩) : ↥L) : X) := by
      refine M.isE9Pair_of_mod hproj ?_
      simp only [M.coe_conjBy]
      rw [← hw]
      exact (isPairMod_diagTau_cycThree hτ hτ1).conj H
    have h3 := hpair.three_le_left hφ3 hφL
      (hφ.commute_conjBy M hDs (by rw [← hw]; exact frobGL_diagTau hσ hτ))
      (hφ.commute_conjBy M _ (frobGL_cycThree σ))
    refine hconj (k := l⁻¹) ?_ h3
    rw [← hlx, ← hsg, hsx]
    group
  ·
    have he3 : (e : K) ^ 3 = 1 := by
      rcases he with he | he <;> rw [he]
      · exact hτ
      · rw [← pow_mul, pow_mul', hτ, one_pow]
    have he3' : e ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, he3, Units.val_one])
    have he1 : e ≠ 1 := by
      rintro rfl
      rw [Units.val_one] at he
      rcases he with he | he
      · exact hτ1 he.symm
      · apply hτ1
        calc τ = τ ^ 3 / τ ^ 2 := by
              have hτ0 : τ ≠ 0 := by
                rintro rfl
                simp at hτ
              field_simp
          _ = 1 := by rw [hτ, ← he, div_one]
    obtain ⟨ξ, -, hξ⟩ := exists_scalar_of_mem_zPi M.piField M.modThree hτ hτ1 hz
    set D₀ := diagUnits (e * ξ⁻¹) ξ⁻¹ ξ⁻¹ with hD₀
    have hz' := mem_statedScalars_of_mem_zPi M.piField M.modThree hτ hτ1 hz
    have hsD : (s : GL (Fin 3) K) = g * D₀ * g⁻¹ := by
      have h1 : D₀ = diagE e * z⁻¹ := by
        rw [← hξ, ← map_inv, scalar_eq_diagUnits, diagE, diagUnits_mul, one_mul]
      have hc : g * z⁻¹ * g⁻¹ = z⁻¹ :=
        mul_inv_eq_iff_eq_mul.2 (commute_of_mem_statedScalars (inv_mem hz') g)
      rw [h1, ← hD]
      calc (s : GL (Fin 3) K) = (s * z) * (g * z⁻¹ * g⁻¹) := by rw [hc]; group
        _ = g * (g⁻¹ * (s * z) * g * z⁻¹) * g⁻¹ := by group
    have hDs : D₀ ∈ slPi π 3 (p ^ f) K := by
      have := conj_mem_slPi M.hπ (inv_mem hg) s.2
      rw [hsD, inv_inv] at this
      convert this using 1
      group
    have hsg : s = M.conjBy hg ⟨D₀, hDs⟩ := Subtype.ext (by rw [M.coe_conjBy]; exact hsD)
    obtain ⟨w, -, hw⟩ := diagTau_eq_diagUnits' hτ
    have hDτ : diagUnits w (w ^ 2) 1 ∈ slPi π 3 (p ^ f) K := by
      rw [← hw]
      exact diagTau_mem_slPi M.hπ M.hq' hτ
    obtain ⟨l, hl, hlx⟩ := M.exists_conj_conjBy hg hφ.mem hDs
    have hpair : IsE9Pair L ((ν (M.conjBy hφ.mem ⟨diagUnits w (w ^ 2) 1, hDτ⟩) : ↥L) : X)
        ((ν (M.conjBy hφ.mem ⟨D₀, hDs⟩) : ↥L) : X) := by
      refine M.isE9Pair_of_mod hproj ?_
      simp only [M.coe_conjBy]
      rw [← hw]
      exact (isPairMod_diagTau_diag hτ hτ1 he3' he1 (ζ := ξ⁻¹)).conj H
    have hfix : frobGL σ D₀ * D₀⁻¹ ∈ StatedScalars (Fin 3) K := by
      have hσe : Units.map (σ : K →* K) e = e :=
        Units.ext (ringAut_apply_eq_of_pow_three hσ he3)
      rw [hD₀, frobGL_diagUnits, diagUnits_inv, diagUnits_mul, map_mul, hσe,
        diagUnits_mem_statedScalars_iff]
      have key : Units.map (σ : K →* K) ξ⁻¹ * ξ⁻¹⁻¹ =
          e * Units.map (σ : K →* K) ξ⁻¹ * (e * ξ⁻¹)⁻¹ := by
        rw [inv_inv, mul_inv_rev, inv_inv, mul_comm e (Units.map (σ : K →* K) ξ⁻¹), mul_assoc,
          ← mul_assoc e ξ e⁻¹, mul_comm e ξ, mul_assoc ξ e e⁻¹, mul_inv_cancel, mul_one]
      exact ⟨key, key⟩
    have h3 := hpair.three_le_right hφ3 hφL
      (hφ.commute_conjBy M hDτ (by rw [← hw]; exact frobGL_diagTau hσ hτ))
      (hφ.commute_conjBy_mod M hproj hDs hfix)
    refine hconj (k := l⁻¹) ?_ h3
    rw [← hlx, ← hsg, hsx]
    group

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
