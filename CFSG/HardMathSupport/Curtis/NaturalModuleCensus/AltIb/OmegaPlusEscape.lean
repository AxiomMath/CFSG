module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusBase
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OrthEscape

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (flagStabilizer)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (flag stabilizer mem_stabilizer
  mem_flag_of_le mem_isoFlag isoFlag)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.SpCell
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic

variable {n : ℕ} {F : Type} [Field F]

theorem exists_fixed_congr {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {p : ℕ}
    (hp : (p : K) ≠ 0) {g : V →ₗ[K] V} (hg : g ^ p = 1) {A B : Submodule K V} (hAB : A ≤ B)
    (hstep : ∀ b ∈ B, g b - b ∈ A) {b : V} (hb : b ∈ B) :
    ∃ a ∈ B, g a = a ∧ a - (p : K) • b ∈ A := by
  have hmem : ∀ j : ℕ, (g ^ j) b ∈ B ∧ (g ^ j) b - b ∈ A := by
    intro j
    induction j with
    | zero => exact ⟨by simpa using hb, by simp⟩
    | succ j ih =>
      have h1 : g ((g ^ j) b) - (g ^ j) b ∈ A := hstep _ ih.1
      have h2 : (g ^ (j + 1)) b = g ((g ^ j) b) := by rw [pow_succ', Module.End.mul_apply]
      refine ⟨?_, ?_⟩
      · rw [h2]
        have : g ((g ^ j) b) = (g ((g ^ j) b) - (g ^ j) b) + (g ^ j) b := by abel
        rw [this]
        exact B.add_mem (hAB h1) ih.1
      · rw [h2]
        have : g ((g ^ j) b) - b = (g ((g ^ j) b) - (g ^ j) b) + ((g ^ j) b - b) := by abel
        rw [this]
        exact A.add_mem h1 ih.2
  set a : V := ∑ j ∈ Finset.range p, (g ^ j) b with ha
  have haB : a ∈ B := B.sum_mem fun j _ => (hmem j).1
  have hgsum : g a = a := by
    obtain ⟨n, hn⟩ : ∃ n, p = n + 1 := ⟨p - 1, by
      have : p ≠ 0 := fun h0 => hp (by simp [h0])
      omega⟩
    have hpb : (g ^ p) b = b := by rw [hg]; rfl
    have h1 : g a = ∑ j ∈ Finset.range p, (g ^ (j + 1)) b := by
      rw [ha, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pow_succ', Module.End.mul_apply]
    rw [h1, ha, hn, Finset.sum_range_succ, Finset.sum_range_succ' (fun j => (g ^ j) b) n]
    have : (g ^ (n + 1)) b = (g ^ 0) b := by rw [← hn, hpb]; simp
    rw [this]
  have hdiff : a - (p : K) • b ∈ A := by
    have : a - (p : K) • b = ∑ j ∈ Finset.range p, ((g ^ j) b - b) := by
      rw [Finset.sum_sub_distrib, ha]
      simp [Nat.cast_smul_eq_nsmul K]
    rw [this]
    exact A.sum_mem fun j _ => (hmem j).2
  exact ⟨a, haB, hgsum, hdiff⟩

theorem spLev_inl_eq_cnt {S : Finset ℕ} (j : Fin n) : spLev n S (Sum.inl j) = cnt S j := by
  by_cases h : cnt S j < S.card
  · exact (step_range h (Sum.inl j)).2 ⟨⟨j, rfl⟩, rfl⟩
  · have h' : cnt S j = S.card := le_antisymm (cnt_le_card S j) (not_lt.1 h)
    rw [h']
    apply (top_range _).2
    obtain ⟨k, hk⟩ := exists_topEmb_eq (S := S) (a := j) h'
    exact ⟨Sum.inl k, by simp [topσ, hk]⟩

theorem false_of_step_escape_D {S : Finset ℕ} [Finite F] [CharP F 2] (hn : 4 ≤ n)
    (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ n) {p : ℕ} (hp : Odd p) (hp0 : (p : F) ≠ 0)
    {x : ↥(Om n F)} (hxp : x ^ p = 1)
    (hfix : ∀ g : ↥(Om n F), g * x = x * g → g ∈ JO n F S)
    {ℓ : ℕ} (hℓ : ℓ < S.card) (hxJ : x ∈ JO n F S)
    (hx1 : stepHom hS hℓ (jToJfl S ⟨x, hxJ⟩) = 1)
    (hk : 2 ≤ Fintype.card (StepCoord n S ℓ)) : False := by
  obtain ⟨a₁, a₂, hlt⟩ : ∃ a₁ a₂ : StepCoord n S ℓ, a₁.1 < a₂.1 := by
    obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.1 (by omega : 1 < Fintype.card (StepCoord n S ℓ))
    rcases lt_trichotomy a.1 b.1 with h | h | h
    · exact ⟨a, b, h⟩
    · exact absurd (Subtype.ext h) hab
    · exact ⟨b, a, h⟩
  set M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
    ((x : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) with hM
  have hxsJ : omSp x ∈ Jfl n F S := hxJ
  have hMs : spMat (omSp x : StatedSp n F) = M := rfl
  have hMp : M ^ p = 1 := by
    rw [← hMs, ← spMat_pow, ← map_pow, hxp, map_one, spMat_one]
  have hbt : M.BlockTriangular (spLev n S) := spMat_blockTriangular hS hxsJ
  have hgi : ∀ i ∈ S, (omSp x : StatedSp n F) ∈ stabilizer n F (isoFlag n F i) := fun i hi => by
    have := SymplecticHigher.mem_flagStabilizer.mp hxsJ i hi
    rwa [flag_eq_isoFlag (hS i hi).2] at this
  have hT : (S.filter (fun j => (a₂.1 : ℕ) < j)).Nonempty := by
    obtain ⟨i, hiS, hai⟩ := exists_cut_of_cnt_lt_card S (a := a₂.1) (by rw [a₂.2]; exact hℓ)
    exact ⟨i, Finset.mem_filter.2 ⟨hiS, hai⟩⟩
  set i := (S.filter (fun j => (a₂.1 : ℕ) < j)).min' hT with hi
  have hi' := Finset.min'_mem _ hT
  rw [← hi] at hi'
  obtain ⟨hiS, hai⟩ := Finset.mem_filter.1 hi'
  have hmin : ∀ i' ∈ S, (a₂.1 : ℕ) < i' → i ≤ i' := fun i' hi'S hai' =>
    Finset.min'_le _ _ (Finset.mem_filter.2 ⟨hi'S, hai'⟩)
  set B : Submodule F (Fin n ⊕ Fin n → F) := isoFlag n F i with hB
  set A : Submodule F (Fin n ⊕ Fin n → F) := B ⊓ levelSpace (spLev n S) ℓ with hA
  have hsubB : ∀ b ∈ B, b ∈ levelSpace (K := F) (spLev n S) (ℓ + 1) := by
    intro b hb
    rw [hB, mem_isoFlag] at hb
    rw [mem_levelSpace]
    intro u hu
    rcases u with j | j
    · apply hb.2
      by_contra hji
      push Not at hji
      have hlt' : cnt S a₂.1 < cnt S j := by
        have : spLev n S (Sum.inl j) = cnt S j := spLev_inl_eq_cnt j
        rw [a₂.2]; omega
      obtain ⟨i', hi'S, hai', hi'j⟩ := exists_cut_of_cnt_lt S hlt'
      have := hmin i' hi'S hai'
      omega
    · exact hb.1 j
  have hblk : ∀ u v, spLev n S u = ℓ → spLev n S v = ℓ → M u v =
      (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) u v := fun u v hu hv =>
    spMat_apply_eq_of_stepHom_eq_one hS hℓ hx1 u v hu hv
  have hstep : ∀ b ∈ B, M.mulVecLin b - b ∈ A := by
    intro b hb
    refine ⟨?_, ?_⟩
    · have h1 : M *ᵥ b ∈ B := spMat_mulVec_mem_of_mem_stabilizer (hgi i hiS) hb
      rw [Matrix.mulVecLin_apply]
      exact B.sub_mem h1 hb
    · rw [Matrix.mulVecLin_apply]
      exact mulVec_sub_mem_levelSpace hbt hblk (hsubB b hb)
  have hbB : ∀ a : StepCoord n S ℓ, (a.1 : ℕ) < i →
      (Pi.single (Sum.inl a.1) 1 : Fin n ⊕ Fin n → F) ∈ B := fun a hai => by
    have := single_mem_flag (K := F) (hS i hiS).2 a.1 a.1.2 hai
    rwa [flag_eq_isoFlag (hS i hiS).2] at this
  have hA0 : ∀ v ∈ A, ∀ a : StepCoord n S ℓ, v (Sum.inl a.1) = 0 := fun v hv a =>
    hv.2 (Sum.inl a.1) (by rw [spLev_inl_eq_cnt, a.2])
  have hai₁ : (a₁.1 : ℕ) < i := lt_trans hlt hai
  obtain ⟨u₁, hu₁B, hu₁g, hu₁A⟩ := exists_fixed_congr hp0 (mulVecLin_pow_eq_one hMp)
    (inf_le_left : A ≤ B) hstep (hbB a₁ hai₁)
  obtain ⟨u₂, hu₂B, hu₂g, hu₂A⟩ := exists_fixed_congr hp0 (mulVecLin_pow_eq_one hMp)
    (inf_le_left : A ≤ B) hstep (hbB a₂ hai)
  have hu₁1 : u₁ (Sum.inl a₁.1) = (p : F) := by
    have := hA0 _ hu₁A a₁
    simpa [sub_eq_zero] using this
  have hu₁2 : u₁ (Sum.inl a₂.1) = 0 := by
    have := hA0 _ hu₁A a₂
    have hne : (Sum.inl a₂.1 : Fin n ⊕ Fin n) ≠ Sum.inl a₁.1 := fun h =>
      absurd (Sum.inl_injective h) (ne_of_gt hlt)
    simpa [Pi.single_apply, hne, sub_eq_zero] using this
  have hu₂1 : u₂ (Sum.inl a₁.1) = 0 := by
    have := hA0 _ hu₂A a₁
    have hne : (Sum.inl a₁.1 : Fin n ⊕ Fin n) ≠ Sum.inl a₂.1 := fun h =>
      absurd (Sum.inl_injective h) (ne_of_lt hlt)
    simpa [Pi.single_apply, hne, sub_eq_zero] using this
  have hu₂2 : u₂ (Sum.inl a₂.1) = (p : F) := by
    have := hA0 _ hu₂A a₂
    simpa [sub_eq_zero] using this
  have hindep : LinearIndependent F ![u₁, u₂] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrFun hst (Sum.inl a₁.1)
    have h2 := congrFun hst (Sum.inl a₂.1)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hu₁1, hu₁2, hu₂1, hu₂2,
      mul_zero, add_zero, zero_add] at h1 h2
    exact ⟨(mul_eq_zero.1 h1).resolve_right hp0, (mul_eq_zero.1 h2).resolve_right hp0⟩
  set W₁ : Submodule F (Fin n ⊕ Fin n → F) := LinearMap.ker (M.mulVecLin - LinearMap.id) with hW₁
  have hW₁mem : ∀ v, v ∈ W₁ ↔ M *ᵥ v = v := fun v => by
    rw [hW₁, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.mulVecLin_apply, LinearMap.id_apply,
      sub_eq_zero]
  have hspan : Submodule.span F (Set.range ![u₁, u₂]) ≤ B ⊓ W₁ := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    fin_cases k
    · exact ⟨hu₁B, (hW₁mem _).2 (by simpa using hu₁g)⟩
    · exact ⟨hu₂B, (hW₁mem _).2 (by simpa using hu₂g)⟩
  have hdim : 2 ≤ Module.finrank F ↥(B ⊓ W₁) := by
    have h1 := Submodule.finrank_mono hspan
    rw [finrank_span_eq_card hindep] at h1
    simpa using h1
  have hFQ : ∀ w ∈ B, (quadPlusForm n F).Q w = 0 := by
    intro w hw
    rw [hB, mem_isoFlag] at hw
    show ∑ j, w (.inl j) * w (.inr j) = 0
    exact Finset.sum_eq_zero fun j _ => by rw [hw.1 j, mul_zero]
  refine false_of_fixed_escape_omega (quadPlusForm n F) (x : GL (Fin n ⊕ Fin n) F)
    (by simp; omega) hp (by rw [← Subgroup.coe_pow, hxp]; rfl)
    (fun v => om_preserves x.2 v) hW₁mem hFQ hdim ?_
  intro g hg hgM w hw
  have hgx : (⟨g, hg⟩ : ↥(Om n F)) * x = x * ⟨g, hg⟩ := Subtype.ext hgM
  have hgJ := hfix _ hgx
  have hgst := SymplecticHigher.mem_flagStabilizer.mp hgJ i hiS
  rw [flag_eq_isoFlag (hS i hiS).2] at hgst
  exact spMat_mulVec_mem_of_mem_stabilizer (g := omSp ⟨g, hg⟩) hgst hw

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell
