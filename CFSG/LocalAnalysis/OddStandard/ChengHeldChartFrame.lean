module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldChartPos
public import CFSG.LocalAnalysis.OddStandard.ChengHeldFrameKer

public section

namespace CFSG.OddStandard.ChengHeld.M1b

open Subgroup CFSG.Open CFSG.OddStandard.ChengHeldData
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.L34Facts.Real

section KerLe

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

theorem nf_zero_zz (a b : ZMod 4) : nf l 0 a b = zz l a b := by
  have : tw 0 = [] := by decide
  rw [nf, this]
  show l 1 * zz l a b = zz l a b
  rw [map_one, one_mul]

theorem nfM_zero_zz (a b : ZMod 4) : nfM l ((0 : ℕ), a, b) = zz l a b := nf_zero_zz a b

theorem zz_zero_eq_pow (c : ZMod 4) : zz l 0 c = zz l 0 1 ^ c.val := by
  rw [zz_pow]
  simp

theorem zz_zero_three_pow (n : ℕ) : zz l 0 3 ^ n = zz l 0 (3 * n) := by
  rw [zz_pow]
  simp [mul_comm]

theorem ker_le_zpowers4 (h : IsQSetting q l) {α : ℕ} (hα : α ≤ 1)
    (hstd : ∀ a b : ZMod 4, zz l a b = 1 ↔ inK (kapOf α) a b) :
    ∀ e ∈ q.ker, e ∈ zpowers (nfM l (frM α 0)) := by
  intro e he
  obtain ⟨i, j, rfl⟩ := (mem_ker_iff h.ql h.lsurj h.three).1 he
  rw [← zz_ofNat]
  interval_cases α
  · have h0 : zz l (i : ZMod 4) (-(2 * (i : ZMod 4))) = 1 := by
      rw [hstd]
      refine ⟨(i : ZMod 4), by simp [kapOf], ?_⟩
      show (i : ZMod 4) * (kapOf 0).2 = -(2 * (i : ZMod 4))
      simp only [kapOf, ite_true]
      generalize (i : ZMod 4) = a
      revert a
      decide
    have h1 : zz l (i : ZMod 4) (j : ZMod 4) = zz l 0 ((j : ZMod 4) + 2 * (i : ZMod 4)) := by
      have := congrArg (· * zz l 0 ((j : ZMod 4) + 2 * (i : ZMod 4))) h0
      simp only [one_mul, zz_mul] at this
      rw [← this]
      congr 1 <;> ring
    rw [h1, zz_zero_eq_pow]
    have : nfM l (frM 0 0) = zz l 0 1 := by simp [frM, nfM_zero_zz]
    rw [this]
    exact pow_mem (mem_zpowers _) _
  · have h0 : zz l (i : ZMod 4) 0 = 1 := by
      rw [hstd]
      exact ⟨(i : ZMod 4), by simp [kapOf], by simp [kapOf]⟩
    have h1 : zz l (i : ZMod 4) (j : ZMod 4) = zz l 0 (j : ZMod 4) := by
      have := congrArg (· * zz l 0 (j : ZMod 4)) h0
      simp only [one_mul, zz_mul] at this
      rw [← this]
      congr 1 <;> ring
    rw [h1, zz_zero_eq_pow]
    have h3 : nfM l (frM 1 0) = zz l 0 3 := by simp [frM, nfM_zero_zz]
    rw [h3]
    have h4 : zz l 0 1 = zz l 0 3 ^ 3 := by
      rw [zz_zero_three_pow]
      congr 1
    rw [h4, ← pow_mul]
    exact pow_mem (mem_zpowers _) _

theorem ker_le_zpowers2 (h : IsQSetting q l)
    (hstd : ∀ a b : ZMod 4, zz l a b = 1 ↔ b.val % 2 = 0) :
    ∀ e ∈ q.ker, e ∈ zpowers (nfM l (frM 2 0)) := by
  intro e he
  obtain ⟨i, j, rfl⟩ := (mem_ker_iff h.ql h.lsurj h.three).1 he
  rw [← zz_ofNat]
  have h0 : zz l (i : ZMod 4) 0 = 1 := by rw [hstd]; simp
  have h1 : zz l (i : ZMod 4) (j : ZMod 4) = zz l 0 (j : ZMod 4) := by
    have := congrArg (· * zz l 0 (j : ZMod 4)) h0
    simp only [one_mul, zz_mul] at this
    rw [← this]
    congr 1 <;> ring
  rw [h1, zz_zero_eq_pow]
  have : nfM l (frM 2 0) = zz l 0 1 := by simp [frM, nfM_zero_zz]
  rw [this]
  exact pow_mem (mem_zpowers _) _

theorem nfM_frM_zero_mem_ker (h : IsQSetting q l) (α : ℕ) : nfM l (frM α 0) ∈ q.ker := by
  unfold frM
  split_ifs <;> simpa [nfM_zero_zz] using zz_mem_ker h _ _

theorem card_ker_eq_orderOf (h : IsQSetting q l) {α : ℕ}
    (hle : ∀ e ∈ q.ker, e ∈ zpowers (nfM l (frM α 0))) :
    Nat.card ↥q.ker = orderOf (nfM l (frM α 0)) := by
  have heq : q.ker = zpowers (nfM l (frM α 0)) :=
    le_antisymm (fun e he => hle e he) ((zpowers_le).2 (nfM_frM_zero_mem_ker h α))
  rw [heq, Nat.card_zpowers]

end KerLe

section FrameDataSection

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}
  {d : Datum A}

structure FrameData (P : Pos d) (α : ℕ) where
  p : ℕ → ↥d.S
  hp : ∀ i, jS d (p i) = nfM P.l (frM α i)

theorem exists_frameData (P : Pos d) (α : ℕ) : Nonempty (FrameData P α) := by
  have hex : ∀ i, ∃ s : ↥d.S, jS d s = nfM P.l (frM α i) := by
    intro i
    have hq : P.q (nfM P.l (frM α i)) ∈ T0 := by
      rw [q_nfM P.isQ (frM_lt α i)]
      exact tg_mem_T0 _ (frM_lt α i)
    obtain ⟨p, hpS, hpA, hpe⟩ := (P.hT _).1 hq
    exact ⟨⟨p, hpS⟩, hpe⟩
  choose p hp using hex
  exact ⟨⟨p, hp⟩⟩

variable {P : Pos d} {α : ℕ} (F : FrameData P α)

theorem jS_evalE (τ : Tm) :
    jS d (evalE F.p τ) = evalE (fun i => nfM P.l (frM α i)) τ := by
  rw [evalE_map (jS d) F.p τ]
  simp only [F.hp]

theorem S_rel {τ₁ τ₂ : Tm}
    (h : evalE (fun i => nfM P.l (frM α i)) τ₁ = evalE (fun i => nfM P.l (frM α i)) τ₂) :
    evalE F.p τ₁ = evalE F.p τ₂ :=
  jS_injective d (by rw [jS_evalE F, jS_evalE F, h])

theorem G_rel {τ₁ τ₂ : Tm}
    (h : evalE (fun i => nfM P.l (frM α i)) τ₁ = evalE (fun i => nfM P.l (frM α i)) τ₂) :
    evalE (fun i => (F.p i : G)) τ₁ = evalE (fun i => (F.p i : G)) τ₂ := by
  have h1 := evalE_map d.S.subtype F.p τ₁
  have h2 := evalE_map d.S.subtype F.p τ₂
  simp only [Subgroup.coe_subtype] at h1 h2
  rw [← h1, ← h2, S_rel F h]


theorem frM_fst_one (α : ℕ) : (frM α 1).1 = 4 := by unfold frM; split_ifs <;> rfl
theorem frM_fst_two (α : ℕ) : (frM α 2).1 = 8 := by unfold frM; split_ifs <;> rfl

theorem closure_frame (hC : ChCoverParts)
    (hkle : ∀ e ∈ P.q.ker, e ∈ zpowers (nfM P.l (frM α 0))) :
    closure ({(F.p 0 : G), (F.p 1 : G), (F.p 2 : G), (F.p 3 : G), (F.p 4 : G), (F.p 5 : G),
      (F.p 6 : G)} : Set G) = d.S := by
  apply le_antisymm
  · rw [closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact (F.p _).2
  · set H : Subgroup ↥d.S := closure {F.p 0, F.p 1, F.p 2, F.p 3, F.p 4, F.p 5, F.p 6} with hH
    have hmem : ∀ i, F.p i ∈ H → wordPerm (tg (frM α i).1) ∈ H.map (P.q.comp (jS d)) := fun i hi =>
      ⟨F.p i, hi, by simp [F.hp, q_nfM P.isQ (frM_lt α i)]⟩
    have hp0 : F.p 0 ∈ H := subset_closure (by simp)
    have hp1 : F.p 1 ∈ H := subset_closure (by simp)
    have hp2 : F.p 2 ∈ H := subset_closure (by simp)
    have hp3 : F.p 3 ∈ H := subset_closure (by simp)
    have hp4 : F.p 4 ∈ H := subset_closure (by simp)
    have hp5 : F.p 5 ∈ H := subset_closure (by simp)
    have hp6 : F.p 6 ∈ H := subset_closure (by simp)
    have hT0 : T0 ≤ H.map (P.q.comp (jS d)) := by
      rw [← closure_frTg hC.gen, closure_le]
      rintro _ ⟨w, hw, rfl⟩
      simp only [frTg, frIdx, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff,
        or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [frM_fst_one] using hmem 1 hp1
      · simpa [frM_fst_two] using hmem 2 hp2
      · simpa [frM] using hmem 3 hp3
      · simpa [frM] using hmem 4 hp4
      · simpa [frM] using hmem 5 hp5
      · simpa [frM] using hmem 6 hp6
    have hHtop : H = ⊤ := by
      refine eq_top_iff.2 fun s _ => ?_
      have hsT : P.q (jS d s) ∈ T0 := (P.hT _).2 ⟨s, s.2, d.S_le_A s.2, rfl⟩
      obtain ⟨h0, hh0, hq0⟩ := hT0 hsT
      have hk : (jS d h0)⁻¹ * jS d s ∈ P.q.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        have : P.q (jS d h0) = P.q (jS d s) := hq0
        rw [this, inv_mul_cancel]
      obtain ⟨n, hn⟩ := mem_zpowers_iff.1 (hkle _ hk)
      have h1 : jS d s = jS d (h0 * F.p 0 ^ n) := by
        rw [map_mul, map_zpow, F.hp 0, hn]
        group
      rw [jS_injective d h1]
      exact H.mul_mem hh0 (zpow_mem hp0 n)
    intro x hx
    have h1 : (⟨x, hx⟩ : ↥d.S) ∈ H := hHtop ▸ mem_top _
    have h2 := Subgroup.mem_map_of_mem d.S.subtype h1
    rw [hH, MonoidHom.map_closure] at h2
    simpa [Set.image_insert_eq] using h2

end FrameDataSection

end CFSG.OddStandard.ChengHeld.M1b
