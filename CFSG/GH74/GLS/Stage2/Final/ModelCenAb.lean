module

public import CFSG.GH74.GLS.Stage2.Final.ModelLUElts
public import CFSG.LocalAnalysis.SectionRank.Ccomm.LinearTwo
public import CFSG.GH74.GLS.Stage2.Final.ModelComps

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup CFSG.GH74.GLS.LU.Local

variable {F : Type} [Field F]

theorem iota1_comm_diag_iff (M : ModelData F) (a : ↥M.H2) {g₁ g₂ : GL (Fin 2) F}
    (h : diagGL g₁ g₂ ∈ M.K4) :
    iota1 M a * mkP M ⟨diagGL g₁ g₂, h⟩ = mkP M ⟨diagGL g₁ g₂, h⟩ * iota1 M a ↔
      (a : GL (Fin 2) F) * g₁ = g₁ * (a : GL (Fin 2) F) := by
  have hx : iota1 M a = mkP M ⟨diagGL (a : GL (Fin 2) F) 1, M.blkL_mem_K4 a.2⟩ := iota1_apply M a
  rw [hx, mkP_comm_iff]
  have key : ∀ κ : Fˣ,
      ((⟨diagGL g₁ g₂, h⟩ : ↥M.K4) : GL (Fin 4) F)⁻¹ *
        ((⟨diagGL (a : GL (Fin 2) F) 1, M.blkL_mem_K4 a.2⟩ : ↥M.K4) : GL (Fin 4) F)⁻¹ *
        (((⟨diagGL g₁ g₂, h⟩ : ↥M.K4) : GL (Fin 4) F) *
          ((⟨diagGL (a : GL (Fin 2) F) 1, M.blkL_mem_K4 a.2⟩ : ↥M.K4) : GL (Fin 4) F)) =
        Matrix.GeneralLinearGroup.scalar (Fin 4) κ ↔
      g₁⁻¹ * (a : GL (Fin 2) F)⁻¹ * (g₁ * (a : GL (Fin 2) F)) = sc2 κ ∧ (1 : GL (Fin 2) F) = sc2 κ := by
    intro κ
    have e : ((⟨diagGL g₁ g₂, h⟩ : ↥M.K4) : GL (Fin 4) F)⁻¹ *
        ((⟨diagGL (a : GL (Fin 2) F) 1, M.blkL_mem_K4 a.2⟩ : ↥M.K4) : GL (Fin 4) F)⁻¹ *
        (((⟨diagGL g₁ g₂, h⟩ : ↥M.K4) : GL (Fin 4) F) *
          ((⟨diagGL (a : GL (Fin 2) F) 1, M.blkL_mem_K4 a.2⟩ : ↥M.K4) : GL (Fin 4) F)) =
        diagGL (g₁⁻¹ * (a : GL (Fin 2) F)⁻¹ * (g₁ * (a : GL (Fin 2) F))) 1 := by
      show (diagGL g₁ g₂)⁻¹ * (diagGL (a : GL (Fin 2) F) 1)⁻¹ *
        (diagGL g₁ g₂ * diagGL (a : GL (Fin 2) F) 1) = _
      rw [diagGL_inv, diagGL_inv, diagGL_mul, diagGL_mul, diagGL_mul]
      congr 1
      simp
    rw [e, scalar4_eq]
    constructor
    · intro h'
      obtain ⟨h1, h2⟩ := diagGL_inj h'
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      rw [h1, ← h2]
  constructor
  · rintro ⟨κ, hκ⟩
    obtain ⟨h1, h2⟩ := (key κ).1 hκ
    have hX : g₁⁻¹ * (a : GL (Fin 2) F)⁻¹ * (g₁ * (a : GL (Fin 2) F)) = 1 := by rw [h1, ← h2]
    exact (commute_of_inv_mul_eq_one hX).symm
  · intro h'
    refine ⟨1, (key 1).2 ⟨?_, by rw [sc2_one]⟩⟩
    rw [sc2_one, ← h']
    group

theorem card_K1_eq (M : ModelData F) : Nat.card ↥(K1 M) = Nat.card ↥M.H2 :=
  (Nat.card_congr (MonoidHom.ofInjective (iota1_injective M)).toEquiv).symm

theorem card_K2_eq (M : ModelData F) : Nat.card ↥(K2 M) = Nat.card ↥M.H2 :=
  (Nat.card_congr (MonoidHom.ofInjective (iota2_injective M)).toEquiv).symm

theorem yP_comm_K1 (M : ModelData F) {x : PG M} (hx : x ∈ K1 M) : yP M * x = x * yP M := by
  obtain ⟨a, rfl⟩ := hx
  rw [← iota1_negOne M, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  show (-1 : GL (Fin 2) F) * (a : GL (Fin 2) F) = (a : GL (Fin 2) F) * (-1)
  simp

theorem normalizer_K1_le_C0 [Finite F] {M : ModelData F} (hG : GoodModel M) {s : PG M}
    (hs : s ∈ Subgroup.normalizer (K1 M : Set (PG M))) : s ∈ C0 M := by
  have h2 := hG.two_ne_zero
  have hy1 : yP M ∈ K1 M := ⟨⟨-1, M.neg_one_mem_H2⟩, iota1_negOne M⟩
  have hs' := (Subgroup.mem_normalizer_iff.1 hs)
  have hsy : s * yP M * s⁻¹ ∈ K1 M := (hs' _).1 hy1
  have hcen : ∀ k ∈ K1 M, k * (s * yP M * s⁻¹) = (s * yP M * s⁻¹) * k := by
    intro k hk
    have hk' : s⁻¹ * k * s ∈ K1 M := (hs' _).2 (by
      have e : s * (s⁻¹ * k * s) * s⁻¹ = k := by group
      rw [e]; exact hk)
    have h1 := yP_comm_K1 M hk'
    calc k * (s * yP M * s⁻¹) = s * (s⁻¹ * k * s) * yP M * s⁻¹ := by group
      _ = s * (yP M * (s⁻¹ * k * s)) * s⁻¹ := by rw [h1]; group
      _ = (s * yP M * s⁻¹) * k := by group
  have hzc : (⟨s * yP M * s⁻¹, hsy⟩ : ↥(K1 M)) ∈ Subgroup.center ↥(K1 M) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcen g g.2)
  have hmem : s * yP M * s⁻¹ ∈ Subgroup.zpowers (yP M) := by
    have := cen_range hG (iota1 M) (iota1_injective M) (iota1_negOne M)
    rw [← this]
    exact ⟨⟨s * yP M * s⁻¹, hsy⟩, hzc, rfl⟩
  have hne : s * yP M * s⁻¹ ≠ 1 := by
    intro h
    have : yP M = 1 := by
      have e : yP M = s⁻¹ * (s * yP M * s⁻¹) * s := by group
      rw [e, h]; group
    exact yP_ne_one M h2 this
  have hconj : s * yP M * s⁻¹ = yP M := by
    rcases mem_zpowers_of_sq_one (yP_sq M) hmem with h | h
    · exact absurd h hne
    · exact h
  have hsCg : s ∈ Cg M := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [mul_inv_eq_iff_eq_mul] at hconj
    exact hconj
  by_contra hs0
  have hH : ((C0 M).subgroupOf (Cg M)).index = 2 := index_C0_Cg M h2
  have hmul := (Subgroup.mul_mem_iff_of_index_two hH (a := ⟨(tP M)⁻¹, (Cg M).inv_mem (tP_mem_Cg M)⟩)
    (b := ⟨s, hsCg⟩)).2 (by
      simp only [Subgroup.mem_subgroupOf]
      constructor
      · intro h
        exact absurd ((C0 M).inv_mem_iff.1 h) (tP_not_mem_C0 M h2)
      · intro h
        exact absurd h hs0)
  have hc0 : (tP M)⁻¹ * s ∈ C0 M := by
    have := Subgroup.mem_subgroupOf.1 hmul
    simpa using this
  have hs_eq : tP M = s * ((tP M)⁻¹ * s)⁻¹ := by group
  have htN : tP M ∈ Subgroup.normalizer (K1 M : Set (PG M)) := by
    rw [hs_eq]
    exact (Subgroup.normalizer (K1 M : Set (PG M))).mul_mem hs
      ((Subgroup.normalizer (K1 M : Set (PG M))).inv_mem (normalizer_K1_of_C0 M h2 hc0))
  have htN' := Subgroup.mem_normalizer_iff.1 htN
  have hK21 : K2 M ≤ K1 M := by
    intro x hx
    rw [← tP_swap M] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    rw [← hyx]
    exact (htN' y).1 hy
  have hK : K2 M = K1 M :=
    Subgroup.eq_of_le_of_card_ge hK21 (by rw [card_K1_eq, card_K2_eq])
  exact K1_ne_K2 hG hK.symm

theorem luCenAb_K1 [Finite F] {M : ModelData F} (hG : GoodModel M) :
    LUCenAb (⊤ : Subgroup (PG M)) (K1 M) := by
  intro s _ hsn hnc a ha b hb hac hbc
  obtain ⟨k, hkK, hnk⟩ := hnc
  obtain ⟨g, hg, rfl⟩ := normalizer_K1_le_C0 hG hsn
  have hcomm : (g : GL (Fin 4) F) * yGL F = yGL F * g := congrArg Subtype.val (mem_Dsub.1 hg)
  obtain ⟨g₁, g₂, hgd, hg₁, hg₂, hdet⟩ := M.exists_diagGL_of_comm hG.two_ne_zero g.2 hcomm
  have hgK : diagGL g₁ g₂ ∈ M.K4 := hgd ▸ g.2
  have hg' : mkP M g = mkP M ⟨diagGL g₁ g₂, hgK⟩ := by
    congr 1; exact Subtype.ext hgd
  obtain ⟨A, rfl⟩ := ha
  obtain ⟨B, rfl⟩ := hb
  obtain ⟨K', rfl⟩ := hkK
  rw [hg'] at hac hbc hnk
  have hA : (A : GL (Fin 2) F) * g₁ = g₁ * (A : GL (Fin 2) F) := (iota1_comm_diag_iff M A hgK).1 hac
  have hB : (B : GL (Fin 2) F) * g₁ = g₁ * (B : GL (Fin 2) F) := (iota1_comm_diag_iff M B hgK).1 hbc
  have hnsc : ¬ ∃ c : F, (g₁ : Matrix (Fin 2) (Fin 2) F) = c • 1 := by
    rintro ⟨c, hc⟩
    apply hnk
    have hK' : (K' : GL (Fin 2) F) * g₁ = g₁ * (K' : GL (Fin 2) F) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hc]
      simp
    exact ((iota1_comm_diag_iff M K' hgK).2 hK').symm
  have hAB := CFSG.SectionRank.Ccomm.commute_of_commute_nonscalar hnsc
    (A := (g₁ : Matrix (Fin 2) (Fin 2) F)) (B := ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
    (C := ((B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
    (by have := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) hA.symm
        simpa using this)
    (by have := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) hB.symm
        simpa using this)
  have hAB' : A * B = B * A := Subtype.ext (Units.ext (by simpa using hAB))
  rw [← map_mul, ← map_mul, hAB']

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
