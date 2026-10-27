module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSzGroup
public import CFSG.Sporadic.Schreier.RuOrbLBase

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction.RuSz

open Subgroup CFSG.Blueprint CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.RuSchreier CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen
open CFSG.Sporadic.Th (Rep)
open CFSG.EvenSporadicStandard.TwoRu.HypOne (lGens lGensInv letterG)

section Generic

theorem eq_top_of_index_le {K : Type*} [Group K] [Finite K] [IsSimpleGroup K] {H : Subgroup K}
    {n : ℕ} (h : H.index ≤ n) (hn : n.factorial < Nat.card K) : H = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with h0 | h0
  · exfalso
    have h1 := H.index_normalCore_le_factorial_index
    rw [h0, Subgroup.index_bot] at h1
    have h2 : H.index.factorial ≤ n.factorial := Nat.factorial_le h
    omega
  · have := H.normalCore_le
    rw [h0] at this
    exact top_le_iff.1 this

theorem eq_of_card_eq_of_card_le {G : Type*} [Group G] [Finite G] {K L X : Subgroup G}
    [IsSimpleGroup K] (hKL : K ≤ L) (hXL : X ≤ L) (h4 : Nat.card L = 4 * Nat.card K)
    (hbig : Nat.factorial 4 < Nat.card K) (hX : Nat.card X = Nat.card K) : X = K := by
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hL : K.relIndex L = 4 := by
    have h := K.relIndex_mul_card (K := L)
    rw [inf_eq_left.2 hKL, h4] at h
    exact Nat.eq_of_mul_eq_mul_right hKpos h
  have hle : K.relIndex X ≤ K.relIndex L :=
    Subgroup.relIndex_le_of_le_right hXL (by
      unfold Subgroup.relIndex
      exact Subgroup.index_ne_zero_of_finite)
  have h1 := K.relIndex_mul_card (K := X)
  have h2 := X.relIndex_mul_card (K := K)
  rw [inf_comm] at h2
  have hapos : 0 < Nat.card ↥(K ⊓ X) := Nat.card_pos
  have heq : X.relIndex K = K.relIndex X := by
    have : X.relIndex K * Nat.card ↥(K ⊓ X) = K.relIndex X * Nat.card ↥(K ⊓ X) := by
      rw [h2, h1, hX]
    exact Nat.eq_of_mul_eq_mul_right hapos this
  have hidx : (X.subgroupOf K).index ≤ 4 := by
    have : X.relIndex K ≤ 4 := heq ▸ hL ▸ hle
    exact this
  have htop := eq_top_of_index_le hidx hbig
  have hKX : K ≤ X := Subgroup.subgroupOf_eq_top.1 htop
  exact (Subgroup.eq_of_le_of_card_ge hKX hX.le).symm

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] {H : Subgroup G} [Finite H] {g : G}
    (h : ∀ k ∈ H, g * k * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨k, hk, rfl⟩
    exact h k hk
  have hcard : Nat.card ↥(H.map (MulAut.conj g).toMonoidHom) = Nat.card H :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have heq : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨h k, fun hk => ?_⟩
  rw [← heq] at hk
  obtain ⟨k', hk', hkk⟩ := hk
  have : k' = k := by
    have h' : g * k' * g⁻¹ = g * k * g⁻¹ := hkk
    simpa using h'
  exact this ▸ hk'

end Generic

section Normal

theorem kG_mem (w : String) : kG w ∈ K0 := by
  refine wordProd_mem (K := K0) (fun i => ?_) _
  unfold img2
  split_ifs
  · exact subset_closure (Set.mem_insert _ _)
  · exact subset_closure (Set.mem_insert_of_mem _ rfl)

theorem conj_normWords : ∀ c ∈ normWords,
    ggL c.1 * (if c.2.1 then tG else sG) * (ggL c.1)⁻¹ = kG c.2.2 := by
  intro c hc
  have hi : c.1 < lGens.size := by
    rw [lGens_size]
    revert c
    decide
  have hg := CFSG.EvenSporadicStandard.RuStd.lGens_rep c.1 hi
  have h := szChecks.2.2.2.1
  simp only [ruSzNormOK, List.all_eq_true] at h
  have hX : Rep 4060 (if c.2.1 then tTab else sTab) (if c.2.1 then tG else sG) := by
    split_ifs
    · exact rep_t.1
    · exact rep_s.1
  have hrep : Rep 4060 (conjTab c.1 (if c.2.1 then tTab else sTab))
      (ggL c.1 * (if c.2.1 then tG else sG) * (ggL c.1)⁻¹) :=
    CFSG.Sporadic.Th.Rep.compT (CFSG.Sporadic.Th.Rep.compT hg.1 hX) hg.2.1
  exact eq_of_rep_tblEq hrep (rep_kTab c.2.2) (h c hc)

theorem conj_mem_K0 {g : Equiv.Perm (Fin 4060)} (hs : g * sG * g⁻¹ ∈ K0)
    (ht : g * tG * g⁻¹ ∈ K0) : ∀ k ∈ K0, g * k * g⁻¹ ∈ K0 := by
  intro k hk
  rw [K0] at hk
  induction hk using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact hs
    · exact ht
  | one => simp
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact mul_mem hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hx

theorem ggL_conj_mem {i : ℕ} (hi : i < 3) : ∀ k ∈ K0, ggL i * k * (ggL i)⁻¹ ∈ K0 := by
  have h := conj_normWords
  have hs : ggL i * sG * (ggL i)⁻¹ ∈ K0 ∧ ggL i * tG * (ggL i)⁻¹ ∈ K0 := by
    interval_cases i
    · have h1 := h (0, false, "bbabbabaBabaBabaBaBababbab") (by simp [normWords])
      have h2 := h (0, true, "abbaBabaBabbaBababbaBaba") (by simp [normWords])
      simp only [Bool.false_eq_true, ↓reduceIte] at h1
      simp only [↓reduceIte] at h2
      exact ⟨h1 ▸ kG_mem _, h2 ▸ kG_mem _⟩
    · have h1 := h (1, false, "aBabbabaBabbabaBabbaba") (by simp [normWords])
      have h2 := h (1, true, "BabbabaBabaBabbaBabbabbab") (by simp [normWords])
      simp only [Bool.false_eq_true, ↓reduceIte] at h1
      simp only [↓reduceIte] at h2
      exact ⟨h1 ▸ kG_mem _, h2 ▸ kG_mem _⟩
    · have h1 := h (2, false, "babbabaBabbabaBabbaB") (by simp [normWords])
      have h2 := h (2, true, "BabaBaBababbaBabbaBaba") (by simp [normWords])
      simp only [Bool.false_eq_true, ↓reduceIte] at h1
      simp only [↓reduceIte] at h2
      exact ⟨h1 ▸ kG_mem _, h2 ▸ kG_mem _⟩
  exact conj_mem_K0 hs.1 hs.2

theorem K0_finite : Finite K0 := Nat.finite_of_card_ne_zero (by rw [card_K0]; norm_num)

theorem ruL_le_normalizer : ruL ≤ Subgroup.normalizer (K0 : Set (Equiv.Perm (Fin 4060))) := by
  have := K0_finite
  rw [ruL, closure_le]
  intro g hg
  obtain ⟨i, hi, rfl⟩ := ruLGens_getD_eq hg
  exact mem_normalizer_of_conj_mem (ggL_conj_mem hi)

theorem K0_normal : (K0.subgroupOf ruL).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer K0_le_L).2 ruL_le_normalizer

theorem card_ruL_eq : Nat.card ruL = 4 * Nat.card K0 := by
  rw [card_K0, card_ruL]

theorem eq_K0_of_card {X : Subgroup (Equiv.Perm (Fin 4060))} (hXL : X ≤ ruL)
    (hX : Nat.card X = 29120) : X = K0 := by
  haveI := K0_simple
  haveI := K0_finite
  have : Finite (Equiv.Perm (Fin 4060)) := inferInstance
  exact eq_of_card_eq_of_card_le K0_le_L hXL card_ruL_eq (by rw [card_K0]; norm_num)
    (by rw [hX, card_K0])

end Normal

section Cent

theorem bG_ne_one : bG ≠ 1 := by
  have h := szChecks.2.2.2.2.1
  simp only [ruSzCentOK, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ne_one_of_tblEq_false (by norm_num) rep_b.1 h.1.1.1.2

theorem bG_ne_a0 : bG ≠ ruA0 := by
  have h := szChecks.2.2.2.2.1
  simp only [ruSzCentOK, Bool.and_eq_true, Bool.not_eq_true'] at h
  intro hb
  have hrep : Rep 4060 (CFSG.EvenSporadicStandard.TwoRu.HypOne.tblOfArr ruA0A) bG :=
    hb ▸ CFSG.EvenSporadicStandard.TwoRu.HypOne.rep_tblOfArr rep_ruA0
  have := tblEq_of_rep rep_b.1 hrep
  rw [h.1.1.2] at this
  cases this

theorem bG_comm_sG : bG * sG = sG * bG := by
  have h := szChecks.2.2.2.2.1
  simp only [ruSzCentOK, Bool.and_eq_true] at h
  exact eq_of_rep_tblEq (CFSG.Sporadic.Th.Rep.compT rep_b.1 rep_s.1)
    (CFSG.Sporadic.Th.Rep.compT rep_s.1 rep_b.1) h.1.2

theorem bG_comm_tG : bG * tG = tG * bG := by
  have h := szChecks.2.2.2.2.1
  simp only [ruSzCentOK, Bool.and_eq_true] at h
  exact eq_of_rep_tblEq (CFSG.Sporadic.Th.Rep.compT rep_b.1 rep_t.1)
    (CFSG.Sporadic.Th.Rep.compT rep_t.1 rep_b.1) h.2

theorem comm_K0_of_comm_gens {x : Equiv.Perm (Fin 4060)} (hs : x * sG = sG * x)
    (ht : x * tG = tG * x) : ∀ k ∈ K0, x * k = k * x := by
  intro k hk
  rw [K0] at hk
  induction hk using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact hs
    · exact ht
  | one => simp
  | mul y z _ _ hy hz =>
    calc x * (y * z) = (x * y) * z := by rw [mul_assoc]
      _ = (y * x) * z := by rw [hy]
      _ = y * (x * z) := by rw [mul_assoc]
      _ = y * (z * x) := by rw [hz]
      _ = (y * z) * x := by rw [mul_assoc]
  | inv y _ hy =>
    have : x * y⁻¹ = y⁻¹ * x := by
      calc x * y⁻¹ = y⁻¹ * (y * x) * y⁻¹ := by group
        _ = y⁻¹ * (x * y) * y⁻¹ := by rw [hy]
        _ = y⁻¹ * x := by group
    exact this

theorem bG_comm_K0 : ∀ k ∈ K0, bG * k = k * bG := comm_K0_of_comm_gens bG_comm_sG bG_comm_tG

theorem ruA0_comm_K0 : ∀ k ∈ K0, ruA0 * k = k * ruA0 := fun k hk =>
  (Subgroup.mem_centralizer_singleton_iff.1 (ruL_le_centralizer (K0_le_L hk)).2).symm

end Cent

end CFSG.EvenSporadicStandard.Induction.RuSz
