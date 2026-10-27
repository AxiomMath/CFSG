module

public import CFSG.CharacterTheory.Wreathed.FourPointTwelveCharactersCore
public import CFSG.CharacterTheory.Wreathed.FourPointTwelveCharactersFourth

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.FourPointTwelveCharacters

namespace ColumnData

variable {ι : Type*} {D : ColumnData ι} {κ lam γ : ι} {pβ pκ pl δ q₂ q₃ : ℤ}

theorem Stage1.values (h : D.Valid) (hS : D.Stage1 κ lam γ pβ pκ pl δ q₂ q₃) :
    ∃ ψ, rest11 D κ lam γ = {ψ} ∧ (D.cs ψ = 1 ∨ D.cs ψ = -1) ∧ D.cj ψ = ψ ∧
      Row8 D D.p₀ 1 (-1) (-1) (-1) 1 1 1 1 ∧
      Row8 D D.β₁ pβ (-pβ) (-pβ) (-pβ) (-pβ) (-pβ) (-pβ) (-pβ) ∧
      Row8 D κ pκ pκ pκ pκ 0 pκ 0 0 ∧ Row8 D lam pl pl pl pl 0 (-pl) 0 0 ∧
      Row8 D γ 0 0 0 0 (2 * δ) (2 * δ) (2 * δ) (2 * δ) ∧
      Row8 D ψ 0 0 0 0 0 0 0 (D.cs ψ) ∧ Row8 D D.η₁ 0 (2 * D.ε) 0 0 0 0 0 0 ∧
      Row8 D (D.cj D.η₁) 0 0 0 (2 * D.ε) 0 0 0 0 ∧
      Row8 D D.χ₂ 0 0 q₂ 0 (D.c₁ D.χ₂) 0 (D.c₁ D.χ₂ - 1) 0 ∧
      Row8 D (D.cj D.χ₂) 0 0 q₂ 0 (D.c₁ D.χ₂ - 1) 0 (D.c₁ D.χ₂) 0 ∧
      Row8 D D.χ₃ 0 0 q₃ 0 (D.c₁ D.χ₃) 0 (D.c₁ D.χ₃ - 1) 0 ∧
      Row8 D (D.cj D.χ₃) 0 0 q₃ 0 (D.c₁ D.χ₃ - 1) 0 (D.c₁ D.χ₃) 0 ∧
      (D.c₁ D.χ₂ = 0 ∨ D.c₁ D.χ₂ = 1) ∧ (D.c₁ D.χ₃ = 0 ∨ D.c₁ D.χ₃ = 1) := by
  obtain ⟨hc₁γ, hc₁κ, hc₁l, hcsκ, hcsl, hcsγ, ψ, hR, hψ1, hc₁ψ, hc₃ψ, hcjψ⟩ := hS.final h
  obtain ⟨hc₁β, hc₁η, ha₂, ha₃, -⟩ := hS.c₁_values h
  obtain ⟨e2, e3, e2', e3', eη, eη3, eη3'⟩ := hS.c₁_pairs h
  obtain ⟨hcsβ, hcs2, hcs3, hcsη, -⟩ := hS.cs_values h
  obtain ⟨h1B, h2B, h3B⟩ := h.six_mem
  have hψR : ψ ∈ rest11 D κ lam γ := by
    rw [hR]
    exact Finset.mem_singleton_self ψ
  obtain ⟨hψB, hPψ, -, hL₁ψ, hL₂ψ, hL₃ψ, hc₂ψ, -⟩ := hS.mem_rest hψR
  obtain ⟨rβ1, rβ2, rβ3, rβ4, rβ5⟩ := hS.row_β
  obtain ⟨rκ1, rκ2, rκ3, rκ4, rκ5⟩ := hS.row_κ
  obtain ⟨rl1, rl2, rl3, rl4, rl5⟩ := hS.row_lam
  obtain ⟨j1, j2, j3, j4, j5⟩ := hS.row_χ₂
  obtain ⟨k1, k2, k3, k4, k5⟩ := hS.row_χ₂'
  obtain ⟨l1, l2, l3, l4, l5⟩ := hS.row_χ₃
  obtain ⟨m1, m2, m3, m4, m5⟩ := hS.row_χ₃'
  obtain ⟨n1, n2, n3, n4, n5⟩ := hS.row_η
  obtain ⟨o1, o2, o3, o4, o5⟩ := hS.row_η'
  obtain ⟨g1, g2, g3, g4, g5⟩ := hS.row_γ
  have hoffJ : ∀ χ ∈ D.B, D.Q χ = 0 → D.c₁ χ = D.c₃ χ := by
    intro χ hχ hQ
    have hne : ∀ ξ, D.Q ξ ≠ 0 → χ ≠ ξ := fun ξ hξ e => hξ (by rw [← e, hQ])
    exact h.c₁₃_values.2.2.2.2 χ hχ (hne _ hS.Q_J.1) (hne _ hS.Q_J.2.1) (hne _ hS.Q_J.2.2.1)
      (hne _ hS.Q_J.2.2.2)
  have hc₃β : D.c₃ D.β₁ = -pβ := by rw [← hoffJ _ h.β_mem hS.Q_E.1, hc₁β]
  have hc₃κ : D.c₃ κ = 0 := by rw [← hoffJ _ hS.κ_mem hS.Q_E.2.1, hc₁κ]
  have hc₃l : D.c₃ lam = 0 := by rw [← hoffJ _ hS.lam_mem hS.Q_E.2.2, hc₁l]
  have hc₃γ : D.c₃ γ = 2 * δ := by rw [← hoffJ _ hS.γ_mem hS.Q_H.2.2, hc₁γ]
  have hcs2' : D.cs (D.cj D.χ₂) = 0 := by rw [h.cs_cj _ h2B, hcs2]
  have hcs3' : D.cs (D.cj D.χ₃) = 0 := by rw [h.cs_cj _ h3B, hcs3]
  have hcsη' : D.cs (D.cj D.η₁) = 0 := by rw [h.cs_cj _ h.η_mem, hcsη]
  have hc₃2' : D.c₃ (D.cj D.χ₂) = D.c₁ D.χ₂ := h.c₃_cj _ h2B
  have hc₃3' : D.c₃ (D.cj D.χ₃) = D.c₁ D.χ₃ := h.c₃_cj _ h3B
  refine ⟨ψ, hR, hψ1, hcjψ, ⟨h.P_p, h.L₁_p, h.L₂_p, h.L₃_p, h.c₁_p, h.c₂_p, h.c₃_p, h.cs_p⟩,
    ⟨rβ1, rβ2, rβ3, rβ4, hc₁β, rβ5, hc₃β, hcsβ⟩, ⟨rκ1, rκ2, rκ3, rκ4, hc₁κ, rκ5, hc₃κ, hcsκ⟩,
    ⟨rl1, rl2, rl3, rl4, hc₁l, rl5, hc₃l, hcsl⟩, ⟨g1, g2, g3, g4, hc₁γ, g5, hc₃γ, hcsγ⟩,
    ⟨hPψ, hL₁ψ, hL₂ψ, hL₃ψ, hc₁ψ, hc₂ψ, hc₃ψ, rfl⟩,
    ⟨n1, n2, n3, n4, hc₁η, n5, by rw [eη3, hc₁η], hcsη⟩,
    ⟨o1, o2, o3, o4, by rw [eη, hc₁η], o5, by rw [eη3', hc₁η], hcsη'⟩,
    ⟨j1, j2, j3, j4, rfl, j5, e2', hcs2⟩, ⟨k1, k2, k3, k4, e2, k5, hc₃2', hcs2'⟩,
    ⟨l1, l2, l3, l4, rfl, l5, e3', hcs3⟩, ⟨m1, m2, m3, m4, e3, m5, hc₃3', hcs3'⟩, ha₂, ha₃⟩

theorem Stage1.B_eq (h : D.Valid) (hS : D.Stage1 κ lam γ pβ pκ pl δ q₂ q₃) {ψ : ι}
    (hR : rest11 D κ lam γ = {ψ}) :
    D.B = (list11 D κ lam γ).toFinset ∪ {ψ} := by
  rw [← hR, rest11, Finset.union_sdiff_of_subset (hS.list11_subset h)]

theorem Stage1.nodup12 (hS : D.Stage1 κ lam γ pβ pκ pl δ q₂ q₃) {ψ : ι}
    (hR : rest11 D κ lam γ = {ψ}) : (list11 D κ lam γ ++ [ψ]).Nodup := by
  have hψ : ψ ∈ rest11 D κ lam γ := by
    rw [hR]
    exact Finset.mem_singleton_self ψ
  rw [rest11, Finset.mem_sdiff, List.mem_toFinset] at hψ
  rw [List.nodup_append]
  refine ⟨hS.nodup, List.nodup_singleton ψ, ?_⟩
  intro a ha b hb hab
  rw [List.mem_singleton] at hb
  subst hb hab
  exact hψ.2 ha

theorem Stage1.sum_eq12 (h : D.Valid) (hS : D.Stage1 κ lam γ pβ pκ pl δ q₂ q₃) {ψ : ι}
    (hR : rest11 D κ lam γ = {ψ}) (f : ι → ℤ) :
    ∑ χ ∈ D.B, f χ = f D.p₀ + f D.β₁ + f κ + f lam + f D.χ₂ + f (D.cj D.χ₂) + f D.χ₃ +
      f (D.cj D.χ₃) + f D.η₁ + f (D.cj D.η₁) + f γ + f ψ := by
  rw [hS.sum_eq h, hR, Finset.sum_singleton]

theorem Stage1.select (h : D.Valid) (hS : D.Stage1 κ lam γ pβ pκ pl δ q₂ q₃) :
    ∃ ψ, rest11 D κ lam γ = {ψ} ∧ (D.cs ψ = 1 ∨ D.cs ψ = -1) ∧ D.cj ψ = ψ ∧
      Row8 D D.β₁ pβ (-pβ) (-pβ) (-pβ) (-pβ) (-pβ) (-pβ) (-pβ) ∧
      Row8 D κ pκ pκ pκ pκ 0 pκ 0 0 ∧ Row8 D lam pl pl pl pl 0 (-pl) 0 0 ∧
      Row8 D γ 0 0 0 0 (2 * δ) (2 * δ) (2 * δ) (2 * δ) ∧
      Row8 D ψ 0 0 0 0 0 0 0 (D.cs ψ) ∧ Row8 D D.η₁ 0 (2 * D.ε) 0 0 0 0 0 0 ∧
      SmallRow D D.χ₂ q₂ (2 * D.c₁ D.χ₂ - 1) ∧ SmallRow D D.χ₃ q₃ (2 * D.c₁ D.χ₃ - 1) ∧
      ((2 * D.c₁ D.χ₂ - 1 = -q₂ ∧ 2 * D.c₁ D.χ₃ - 1 = q₃) ∨
        (2 * D.c₁ D.χ₂ - 1 = q₂ ∧ 2 * D.c₁ D.χ₃ - 1 = -q₃)) ∧
      1 + pβ * D.d D.β₁ + pκ * D.d κ + pl * D.d lam = 0 ∧
      -1 - pβ * D.d D.β₁ + pκ * D.d κ + pl * D.d lam + 2 * D.ε * D.d D.η₁ = 0 ∧
      -1 - pβ * D.d D.β₁ + pκ * D.d κ + pl * D.d lam + 2 * (q₂ * D.d D.χ₂) +
        2 * (q₃ * D.d D.χ₃) = 0 ∧
      1 - pβ * D.d D.β₁ + pκ * D.d κ - pl * D.d lam + 2 * δ * D.d γ = 0 ∧
      1 - pβ * D.d D.β₁ + 2 * δ * D.d γ + (2 * D.c₁ D.χ₂ - 1) * D.d D.χ₂ +
        (2 * D.c₁ D.χ₃ - 1) * D.d D.χ₃ = 0 ∧
      1 - pβ * D.d D.β₁ + 2 * δ * D.d γ + D.cs ψ * D.d ψ = 0 := by
  obtain ⟨ψ, hR, hψ1, hcjψ, r0, rβ, rκ, rl, rγ, rψ, rη, rη', r2, r2', r3, r3', ha₂, ha₃⟩ :=
    hS.values h
  obtain ⟨h1B, h2B, h3B⟩ := h.six_mem
  have hsum := hS.sum_eq12 h hR
  obtain ⟨P0, L10, L20, L30, a10, a20, a30, s0⟩ := r0
  obtain ⟨Pβ, L1β, L2β, L3β, a1β, a2β, a3β, sβ⟩ := rβ
  obtain ⟨Pκ, L1κ, L2κ, L3κ, a1κ, a2κ, a3κ, sκ⟩ := rκ
  obtain ⟨Pl, L1l, L2l, L3l, a1l, a2l, a3l, sl⟩ := rl
  obtain ⟨Pγ, L1γ, L2γ, L3γ, a1γ, a2γ, a3γ, sγ⟩ := rγ
  obtain ⟨Pψ, L1ψ, L2ψ, L3ψ, a1ψ, a2ψ, a3ψ, -⟩ := rψ
  obtain ⟨Pη, L1η, L2η, L3η, a1η, a2η, a3η, sη⟩ := rη
  obtain ⟨Pη', L1η', L2η', L3η', a1η', a2η', a3η', sη'⟩ := rη'
  obtain ⟨P2, L12, L22, L32, -, a22, a32, s2⟩ := r2
  obtain ⟨P2', L12', L22', L32', a12', a22', a32', s2'⟩ := r2'
  obtain ⟨P3, L13, L23, L33, -, a23, a33, s3⟩ := r3
  obtain ⟨P3', L13', L23', L33', a13', a23', a33', s3'⟩ := r3'
  have hU := h.ReU
  rw [hsum] at hU
  rw [L20, s0, a20, a10, a30, L2β, sβ, a2β, a1β, a3β, L2κ, sκ, a2κ, a1κ, a3κ, L2l, sl, a2l, a1l,
    a3l, L22, s2, a22, a32, L22', s2', a22', a12', a32', L23, s3, a23, a33, L23', s3', a23', a13',
    a33', L2η, sη, a2η, a1η, a3η, L2η', sη', a2η', a1η', a3η', L2γ, sγ, a2γ, a1γ, a3γ, L2ψ, a2ψ,
    a1ψ, a3ψ] at hU
  have hpl2 : pl ^ 2 = 1 := by rcases hS.pl_val with e | e <;> rw [e] <;> norm_num
  have hδ2 : δ ^ 2 = 1 := by rcases hS.δ_val with e | e <;> rw [e] <;> norm_num
  have hψ2 : D.cs ψ ^ 2 = 1 := by rcases hψ1 with e | e <;> rw [e] <;> norm_num
  have hU' : (2 * D.c₁ D.χ₂ - 1 - q₂) * (2 * D.c₁ D.χ₂ - 1 - q₂) +
      (2 * D.c₁ D.χ₃ - 1 - q₃) * (2 * D.c₁ D.χ₃ - 1 - q₃) = 4 := by
    linarith only [hU, hpl2, hδ2, hψ2]
  have hσ₂ : 2 * D.c₁ D.χ₂ - 1 = 1 ∨ 2 * D.c₁ D.χ₂ - 1 = -1 := by
    rcases ha₂ with e | e <;> rw [e] <;> norm_num
  have hσ₃ : 2 * D.c₁ D.χ₃ - 1 = 1 ∨ 2 * D.c₁ D.χ₃ - 1 = -1 := by
    rcases ha₃ with e | e <;> rw [e] <;> norm_num
  have hsel' := sign_pair_select hσ₂ hS.q₂_val hσ₃ hS.q₃_val hU'
  have hd2 := h.d_cj _ h2B
  have hd3 := h.d_cj _ h3B
  have hdη := h.d_cj _ h.η_mem
  have eP := h.Pd
  rw [hsum, P0, Pβ, Pκ, Pl, P2, P2', P3, P3', Pη, Pη', Pγ, Pψ, h.d_p] at eP
  have eL₁ := h.L₁d
  rw [hsum, L10, L1β, L1κ, L1l, L12, L12', L13, L13', L1η, L1η', L1γ, L1ψ, h.d_p] at eL₁
  have eL₂ := h.L₂d
  rw [hsum, L20, L2β, L2κ, L2l, L22, L22', L23, L23', L2η, L2η', L2γ, L2ψ, h.d_p, hd2,
    hd3] at eL₂
  have eC₂ := h.c₂d
  rw [hsum, a20, a2β, a2κ, a2l, a22, a22', a23, a23', a2η, a2η', a2γ, a2ψ, h.d_p] at eC₂
  have eC₁ := h.c₁d
  rw [hsum, a10, a1β, a1κ, a1l, a12', a13', a1η, a1η', a1γ, a1ψ, h.d_p, hd2, hd3] at eC₁
  have eCs := h.csd
  rw [hsum, s0, sβ, sκ, sl, s2, s2', s3, s3', sη, sη', sγ, h.d_p] at eCs
  refine ⟨ψ, hR, hψ1, hcjψ, ⟨Pβ, L1β, L2β, L3β, a1β, a2β, a3β, sβ⟩,
    ⟨Pκ, L1κ, L2κ, L3κ, a1κ, a2κ, a3κ, sκ⟩, ⟨Pl, L1l, L2l, L3l, a1l, a2l, a3l, sl⟩,
    ⟨Pγ, L1γ, L2γ, L3γ, a1γ, a2γ, a3γ, sγ⟩, ⟨Pψ, L1ψ, L2ψ, L3ψ, a1ψ, a2ψ, a3ψ, rfl⟩,
    ⟨Pη, L1η, L2η, L3η, a1η, a2η, a3η, sη⟩, ⟨P2, L12, L22, L32, a22, s2, by rw [a32]; ring,
      by rw [a32]; ring⟩, ⟨P3, L13, L23, L33, a23, s3, by rw [a33]; ring, by rw [a33]; ring⟩,
    hsel', by linarith only [eP], by linarith only [eL₁], by linarith only [eL₂],
    by linarith only [eC₂], by linarith only [eC₁], by linarith only [eCs]⟩

theorem Stage1.classified_of (h : D.Valid) (hS : D.Stage1 κ lam γ pβ pκ pl δ q₂ q₃) {ψ ξκ ξl : ι}
    (hR : rest11 D κ lam γ = {ψ}) (hψ1 : D.cs ψ = 1 ∨ D.cs ψ = -1) (hcjψ : D.cj ψ = ψ)
    (hξ : (ξκ = D.χ₂ ∧ ξl = D.χ₃) ∨ (ξκ = D.χ₃ ∧ ξl = D.χ₂))
    (rβ : Row8 D D.β₁ pβ (-pβ) (-pβ) (-pβ) (-pβ) (-pβ) (-pβ) (-pβ))
    (rκ : Row8 D κ pκ pκ pκ pκ 0 pκ 0 0) (rl : Row8 D lam pl pl pl pl 0 (-pl) 0 0)
    (rγ : Row8 D γ 0 0 0 0 (2 * δ) (2 * δ) (2 * δ) (2 * δ))
    (rψ : Row8 D ψ 0 0 0 0 0 0 0 (D.cs ψ)) (rη : Row8 D D.η₁ 0 (2 * D.ε) 0 0 0 0 0 0)
    (rξκ : SmallRow D ξκ (-pκ) pκ) (rξl : SmallRow D ξl (-pl) (-pl))
    (hP : 1 + pβ * D.d D.β₁ + pκ * D.d κ + pl * D.d lam = 0)
    (hη : D.ε * D.d D.η₁ = 1 + pβ * D.d D.β₁) (hγ : δ * D.d γ = -1 - pκ * D.d κ)
    (hψ : D.cs ψ * D.d ψ = 1 + pβ * D.d D.β₁ + 2 * (pκ * D.d κ))
    (hdκ : D.d ξκ = D.d κ) (hdl : D.d ξl = D.d lam) :
    D.Classified D.β₁ κ lam γ ψ ξκ ξl pβ pκ pl δ (D.cs ψ) := by
  obtain ⟨h1B, h2B, h3B⟩ := h.six_mem
  have hB := hS.B_eq h hR
  have hnd := hS.nodup12 hR
  have hUim : D.Uim ξκ = 1 ∧ D.Uim ξl = 1 := by
    rcases hξ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨h.Uim₂, h.Uim₃⟩
    · exact ⟨h.Uim₃, h.Uim₂⟩
  have hperm : (list11 D κ lam γ ++ [ψ]).Perm
      [D.p₀, D.β₁, κ, lam, γ, ψ, D.η₁, D.cj D.η₁, ξκ, D.cj ξκ, ξl, D.cj ξl] := by
    rw [List.perm_iff_count]
    intro a
    rcases hξ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [list11, List.cons_append, List.nil_append, List.count_cons, List.count_nil] <;>
      omega
  have hnd' : [D.p₀, D.β₁, κ, lam, γ, ψ, D.η₁, D.cj D.η₁, ξκ, D.cj ξκ, ξl, D.cj ξl].Nodup :=
    (List.Perm.nodup_iff hperm).mp hnd
  have hBeq : D.B = {D.p₀, D.β₁, κ, lam, γ, ψ, D.η₁, D.cj D.η₁, ξκ, D.cj ξκ, ξl, D.cj ξl} := by
    have e : (list11 D κ lam γ).toFinset ∪ {ψ} = (list11 D κ lam γ ++ [ψ]).toFinset := by
      rw [List.toFinset_append]
      simp
    rw [hB, e, List.toFinset_eq_of_perm _ _ hperm]
    simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq]
  have hE : D.B.filter (fun χ => D.P χ ≠ 0) = {D.p₀, D.β₁, κ, lam} := by
    ext χ
    rw [Finset.mem_filter, hBeq]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    have hP0 : D.P D.p₀ ≠ 0 := by rw [h.P_p]; norm_num
    have hPβ := h.β_P
    have hPκ : D.P κ ≠ 0 := by rw [rκ.1]; rcases hS.pκ_val with e | e <;> rw [e] <;> norm_num
    have hPl : D.P lam ≠ 0 := by rw [rl.1]; rcases hS.pl_val with e | e <;> rw [e] <;> norm_num
    have hPη' : D.P (D.cj D.η₁) = 0 := by rw [h.P_cj _ h.η_mem, rη.1]
    have hPξκ' : D.P (D.cj ξκ) = 0 := by
      rcases hξ with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · rw [h.P_cj _ h2B, rξκ.1]
      · rw [h.P_cj _ h3B, rξκ.1]
    have hPξl' : D.P (D.cj ξl) = 0 := by
      rcases hξ with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · rw [h.P_cj _ h3B, rξl.1]
      · rw [h.P_cj _ h2B, rξl.1]
    constructor
    · rintro ⟨hχ, hPχ⟩
      rcases hχ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact absurd rγ.1 hPχ
      · exact absurd rψ.1 hPχ
      · exact absurd rη.1 hPχ
      · exact absurd hPη' hPχ
      · exact absurd rξκ.1 hPχ
      · exact absurd hPξκ' hPχ
      · exact absurd rξl.1 hPχ
      · exact absurd hPξl' hPχ
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨Or.inl rfl, hP0⟩
      · exact ⟨Or.inr (Or.inl rfl), hPβ⟩
      · exact ⟨Or.inr (Or.inr (Or.inl rfl)), hPκ⟩
      · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), hPl⟩
  have hJ : D.B.filter (fun χ => D.Q χ ≠ 0) = {ξκ, D.cj ξκ, ξl, D.cj ξl} := by
    ext χ
    rw [Finset.mem_filter]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hχ, hQ⟩
      have := (h.Q_ne_zero_iff hχ).mp hQ
      rcases hξ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
    · intro hχ
      have hχB : χ ∈ D.B := by
        rcases hξ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases hχ with rfl | rfl | rfl | rfl <;>
          first | exact h2B | exact h3B | exact h.cj_mem _ h2B | exact h.cj_mem _ h3B
      refine ⟨hχB, (h.Q_ne_zero_iff hχB).mpr ?_⟩
      rcases hξ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
  exact { signs := ⟨hS.pβ_val, hS.pκ_val, hS.pl_val, hS.δ_val, hψ1⟩
          B_eq := hBeq
          nodup := hnd'
          real := ⟨hS.cj_β, hS.cj_κ, hS.cj_lam, hS.cj_γ, hcjψ⟩
          row_β := rβ
          row_κ := rκ
          row_lam := rl
          row_γ := rγ
          row_ψ := rψ
          row_η := rη
          row_ξκ := rξκ
          row_ξl := rξl
          Uim_ξ := hUim
          deg_P := hP
          deg_η := hη
          deg_γ := hγ
          deg_ψ := hψ
          deg_ξκ := hdκ
          deg_ξl := hdl
          E_eq := hE
          J_eq := hJ }

theorem Valid.classified (h : D.Valid) : ∃ κ lam γ ψ ξκ ξl : ι, ∃ pβ pκ pl δ ζ : ℤ,
    D.Classified D.β₁ κ lam γ ψ ξκ ξl pβ pκ pl δ ζ := by
  obtain ⟨κ, lam, γ, pβ, pκ, pl, δ, q₂, q₃, hS⟩ := h.exists_Stage1
  obtain ⟨ψ, hR, hψ1, hcjψ, rβ, rκ, rl, rγ, rψ, rη, r2, r3, hsel, eP, eL₁, eL₂, eC₂, eC₁,
    eCs⟩ := hS.select h
  obtain ⟨h1B, h2B, h3B⟩ := h.six_mem
  have hdκ := h.d_pos κ hS.κ_mem
  have hdl := h.d_pos lam hS.lam_mem
  have hd2 := h.d_pos _ h2B
  have hd3 := h.d_pos _ h3B
  rcases hsel with ⟨e2, e3⟩ | ⟨e2, e3⟩
  · rw [e2, e3] at eC₁
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := degree_solve hS.pκ_val hS.pl_val hS.q₂_val
      hS.q₃_val hdκ hdl hd2 hd3 eP eL₁ eL₂ eC₂ (by linarith only [eC₁]) eCs
    refine ⟨κ, lam, γ, ψ, D.χ₂, D.χ₃, pβ, pκ, pl, δ, D.cs ψ,
      hS.classified_of h hR hψ1 hcjψ (Or.inl ⟨rfl, rfl⟩) rβ rκ rl rγ rψ rη ?_ ?_ eP f1 f2 f3 f4
        f6⟩
    · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := r2
      exact ⟨a1, a2, by rw [a3, f5], a4, a5, a6, a7, by rw [a8, e2, f5, neg_neg]⟩
    · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := r3
      exact ⟨a1, a2, by rw [a3, f7], a4, a5, a6, a7, by rw [a8, e3, f7]⟩
  · rw [e2, e3] at eC₁
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := degree_solve (q₂ := q₃) (q₃ := q₂)
      (d₂ := D.d D.χ₃) (d₃ := D.d D.χ₂) hS.pκ_val hS.pl_val hS.q₃_val hS.q₂_val hdκ hdl hd3
      hd2 eP eL₁ (by linarith only [eL₂]) eC₂ (by linarith only [eC₁]) eCs
    refine ⟨κ, lam, γ, ψ, D.χ₃, D.χ₂, pβ, pκ, pl, δ, D.cs ψ,
      hS.classified_of h hR hψ1 hcjψ (Or.inr ⟨rfl, rfl⟩) rβ rκ rl rγ rψ rη ?_ ?_ eP f1 f2 f3 f4
        f6⟩
    · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := r3
      exact ⟨a1, a2, by rw [a3, f5], a4, a5, a6, a7, by rw [a8, e3, f5, neg_neg]⟩
    · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := r2
      exact ⟨a1, a2, by rw [a3, f7], a4, a5, a6, a7, by rw [a8, e2, f7]⟩

end ColumnData

end CFSG.Wreathed.FourPointTwelveCharacters
