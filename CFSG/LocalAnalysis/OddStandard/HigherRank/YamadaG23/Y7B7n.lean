module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7k
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7l

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_cover_gen (c : Ctx7 G L) (hb : B5Std c) {k : G} (hkN : k ∈ normIn L c.s.fr.B)
    (htrans : ∀ u ∈ y7bBM c.s, u ∉ M3 c.s → ∀ v ∈ y7bBM c.s, v ∉ M3 c.s →
      ∃ i : ℕ, v⁻¹ * (k ^ i * u * (k ^ i)⁻¹) ∈ M3 c.s)
    {Y Z : Subgroup G} (hYX7 : Y ≤ X7 c.s) (hkY : k ∈ normalizer (Y : Set G))
    (hZ : ∀ y ∈ Y, ⁅y, c.s.t⁆ ∈ M3 c.s → y ∈ Z) {u : G} (hu : u ∈ Y)
    (hut : ⁅u, c.s.t⁆ ∉ M3 c.s) :
    ∀ y ∈ Y, y ∈ Z ∨ ∃ i : ℕ, ∃ a ∈ Z, y = k ^ i * u * (k ^ i)⁻¹ * a := by
  intro y hy
  by_cases hyt : ⁅y, c.s.t⁆ ∈ M3 c.s
  · exact Or.inl (hZ y hy hyt)
  · right
    have hy7 : y ∈ X7 c.s := hYX7 hy
    have hu7 : u ∈ X7 c.s := hYX7 hu
    have huBM : ⁅u, c.s.t⁆ ∈ y7bBM c.s :=
      y7b_comm_t_mem_BM c hb u (y7b_X7_le_X c hu7)
    have hyBM : ⁅y, c.s.t⁆ ∈ y7bBM c.s :=
      y7b_comm_t_mem_BM c hb y (y7b_X7_le_X c hy7)
    obtain ⟨i, hi⟩ := htrans ⁅u, c.s.t⁆ huBM hut ⁅y, c.s.t⁆ hyBM hyt
    have hkiN : k ^ i ∈ normIn L c.s.fr.B := Subgroup.pow_mem (normIn L c.s.fr.B) hkN i
    have hkiH : k ^ i ∈ c.s.H := (s3_L_le_H c.s hb.hH.hS) hkiN.1
    have hkiX : k ^ i ∈ y7bX c.s := y7b_N_le_X c hb ⟨hkiH, hkiN.2⟩
    have hkiY : k ^ i ∈ normalizer (Y : Set G) :=
      Subgroup.pow_mem (normalizer (Y : Set G)) hkY i
    have hxY : k ^ i * u * (k ^ i)⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hkiY u).mp hu
    have hx7 : k ^ i * u * (k ^ i)⁻¹ ∈ X7 c.s := hYX7 hxY
    have hxcomm : ⁅k ^ i * u * (k ^ i)⁻¹, c.s.t⁆ = k ^ i * ⁅u, c.s.t⁆ * (k ^ i)⁻¹ :=
      y7b_comm_conj_of_mem_H c hkiH u
    haveI := y7b_M3_normal_BM c hb
    obtain ⟨θ, hθ, -⟩ := y7b_exists_theta c hb
    let u1 : ↥(y7bBM c.s) :=
      ⟨k ^ i * ⁅u, c.s.t⁆ * (k ^ i)⁻¹,
        y7b_X_norm_BM c hb (k ^ i) hkiX ⁅u, c.s.t⁆ huBM⟩
    let u2 : ↥(y7bBM c.s) := ⟨⁅y, c.s.t⁆, hyBM⟩
    have hxθ : θ ⟨k ^ i * u * (k ^ i)⁻¹, hx7⟩ = QuotientGroup.mk u1 := by
      refine (hθ _ u1).mpr ?_
      dsimp only [u1]
      rw [hxcomm, inv_mul_cancel]
      exact (M3 c.s).one_mem
    have hyθ : θ ⟨y, hy7⟩ = QuotientGroup.mk u2 := by
      refine (hθ _ u2).mpr ?_
      dsimp only [u2]
      rw [inv_mul_cancel]
      exact (M3 c.s).one_mem
    have hmk : (QuotientGroup.mk u1 : ↥(y7bBM c.s) ⧸ (M3 c.s).subgroupOf (y7bBM c.s)) =
        QuotientGroup.mk u2 := by
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_inv, Subgroup.coe_mul]
      dsimp only [u1, u2]
      simpa only [mul_inv_rev, inv_inv] using (M3 c.s).inv_mem hi
    have hprod : θ (⟨k ^ i * u * (k ^ i)⁻¹, hx7⟩⁻¹ * ⟨y, hy7⟩) = 1 := by
      rw [map_mul, map_inv, hxθ, hyθ, hmk]
      simp
    have hgM3 : ⁅((⟨k ^ i * u * (k ^ i)⁻¹, hx7⟩⁻¹ * ⟨y, hy7⟩ : ↥(X7 c.s)) : G),
        c.s.t⁆ ∈ M3 c.s := by
      have h1 : θ (⟨k ^ i * u * (k ^ i)⁻¹, hx7⟩⁻¹ * ⟨y, hy7⟩) =
          QuotientGroup.mk (1 : ↥(y7bBM c.s)) := by simpa using hprod
      have h := (hθ _ (1 : ↥(y7bBM c.s))).mp h1
      simpa using h
    refine ⟨i, (k ^ i * u * (k ^ i)⁻¹)⁻¹ * y, hZ _ ?_ ?_, ?_⟩
    · exact Y.mul_mem (Y.inv_mem hxY) hy
    · simpa using hgM3
    · group

theorem y7b_extCtx1 (c : Ctx7 G L) (hb : B5Std c) :
    ExtCtx (y7bW c.s) (y7bX0 c.s) (X7 c.s) (normIn c.s.H c.s.fr.B) := by
  refine ⟨y7b_W_le_X0 c hb, y7b_X0_le_X7 c hb, ?_, ?_, ?_, ?_, ?_, y7b_X0_cosets c hb⟩
  · intro n hn y hy
    exact y7b_X7_normal c hb n (y7b_N_le_X c hb hn) y hy
  · intro y hy p hp
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp (y7b_X7_le_X c hy)).1 p).mp hp
  · intro n hn p hp
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp (y7b_N_le_X c hb hn)).1 p).mp hp
  · intro y hy a ha
    exact y7b_X0_normal c hb y (y7b_X7_le_X c hy) a ha
  · intro n hn a ha
    exact y7b_X0_normal c hb n (y7b_N_le_X c hb hn) a ha

theorem y7b_cover1 (c : Ctx7 G L) (hb : B5Std c) {u : G} (hu : u ∈ X7 c.s)
    (hut : ⁅u, c.s.t⁆ ∉ M3 c.s) :
    ∀ y ∈ X7 c.s, y ∈ y7bX0 c.s ∨
      ∃ m ∈ normIn c.s.H c.s.fr.B, ∃ a ∈ y7bX0 c.s, y = m * u * m⁻¹ * a := by
  obtain ⟨k, hkN, -, -, htrans, -, -⟩ := y7b_exists_k c hb
  have hLH : L ≤ c.s.H := s3_L_le_H c.s hb.hH.hS
  have hkNH : k ∈ normIn c.s.H c.s.fr.B := ⟨hLH hkN.1, hkN.2⟩
  have hkY : k ∈ normalizer (X7 c.s : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    exact y7b_X7_normal c hb k (y7b_N_le_X c hb hkNH) x hx
  have hcov := y7b_cover_gen c hb hkN htrans (Y := X7 c.s) (Z := y7bX0 c.s)
    le_rfl hkY (fun y hy hyM3 => (y7b_X0_iff c hb hy).mpr hyM3) hu hut
  intro y hy
  rcases hcov y hy with h | ⟨i, a, ha, hy_eq⟩
  · exact Or.inl h
  · exact Or.inr ⟨k ^ i, Subgroup.pow_mem (normIn c.s.H c.s.fr.B) hkNH i, a, ha, hy_eq⟩

theorem y7b_X7_sq_mem_W (c : Ctx7 G L) (hb : B5Std c) : ∀ y ∈ X7 c.s, y ^ 2 ∈ y7bW c.s := by
  obtain ⟨m₀, hm₀M4, hm₀sq, -, hm₀t⟩ := y7b_exists_seed c hb
  have hm₀X7 : m₀ ∈ X7 c.s := y7b_M4_le_X7 c hb hm₀M4
  exact ext_sq (y7b_extCtx1 c hb) hm₀X7 (by rw [hm₀sq]; exact (y7bW c.s).one_mem)
    (y7b_cover1 c hb hm₀X7 hm₀t)

theorem y7b_X7_isPGroup (c : Ctx7 G L) (hb : B5Std c) : IsPGroup 2 ↥(X7 c.s) := by
  intro g
  have hg2 : (g : G) ^ 2 ∈ y7bW c.s := y7b_X7_sq_mem_W c hb (g : G) g.2
  obtain ⟨j, hj⟩ := y7b_W_isPGroup c hb (⟨(g : G) ^ 2, hg2⟩ : ↥(y7bW c.s))
  have hj' : ((g : G) ^ 2) ^ (2 ^ j) = 1 := by
    have h := congrArg Subtype.val hj
    simpa using h
  refine ⟨j + 1, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  have h2 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
  rw [h2, pow_mul, hj']

end CFSG.OddStandard.HigherRank.YamadaG23
