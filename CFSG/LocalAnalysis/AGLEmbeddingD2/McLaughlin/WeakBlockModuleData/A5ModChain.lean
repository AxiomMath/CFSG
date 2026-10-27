module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5ModCert

@[expose] public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5Mod

open Matrix

section Abstract

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [DistribMulAction A5 W]
  [SMulCommClass A5 (ZMod 2) W]

def IsSimpleMod (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [DistribMulAction A5 W] : Prop :=
  ∀ S : Submodule (ZMod 2) W, (∀ g : A5, ∀ w ∈ S, g • w ∈ S) → S = ⊥ ∨ S = ⊤

def Wle (y : Fin 15 → W) (i : ℕ) : Submodule (ZMod 2) W :=
  Submodule.span (ZMod 2) {z | ∃ k : Fin 15, (blk k : ℕ) < i ∧ z = y k}

theorem Wle_invariant (y : Fin 15 → W) (hR1 : ∀ g k, g • y k = ∑ l, Mt g l k • y l) (i : ℕ) :
    ∀ g : A5, ∀ w ∈ Wle y i, g • w ∈ Wle y i := by
  intro g w hw
  induction hw using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨k, hk, rfl⟩ := hz
    rw [hR1]
    refine Submodule.sum_mem _ fun l _ => ?_
    by_cases h0 : Mt g l k = 0
    · rw [h0, zero_smul]; exact Submodule.zero_mem _
    · have hle : ¬ blk k < blk l := fun h => h0 (Mt_tri g l k h)
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, ?_, rfl⟩)
      have : blk l ≤ blk k := not_lt.mp hle
      have : (blk l : ℕ) ≤ blk k := this
      omega
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ _ ha

theorem Wle_zero (y : Fin 15 → W) : Wle y 0 = ⊥ := by
  unfold Wle
  rw [Submodule.span_eq_bot]
  rintro z ⟨k, hk, -⟩
  omega

theorem Wle_six (y : Fin 15 → W) (hR2 : Submodule.span (ZMod 2) (Set.range y) = ⊤) :
    Wle y 6 = ⊤ := by
  rw [eq_top_iff, ← hR2]
  refine Submodule.span_mono ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨k, by have := (blk k).2; omega, rfl⟩

theorem exists_block (hs : IsSimpleMod W) [Nontrivial W] (y : Fin 15 → W)
    (hR1 : ∀ g k, g • y k = ∑ l, Mt g l k • y l)
    (hR2 : Submodule.span (ZMod 2) (Set.range y) = ⊤) :
    ∃ b : Fin 6, (∀ k, blk k < b → y k = 0) ∧
      Submodule.span (ZMod 2) {z | ∃ k : Fin 15, blk k = b ∧ z = y k} = ⊤ := by
  classical
  have hex : ∃ i, Wle y i ≠ ⊥ := ⟨6, by rw [Wle_six y hR2]; exact top_ne_bot⟩
  set i₀ := Nat.find hex with hi₀
  have hi₀ne : Wle y i₀ ≠ ⊥ := Nat.find_spec hex
  have hi₀pos : i₀ ≠ 0 := fun h => hi₀ne (h ▸ Wle_zero y)
  have hi₀le : i₀ ≤ 6 := Nat.find_min' hex (by rw [Wle_six y hR2]; exact top_ne_bot)
  have hlt : Wle y (i₀ - 1) = ⊥ := by
    by_contra h
    exact Nat.find_min hex (by omega) h
  have htop : Wle y i₀ = ⊤ :=
    (hs _ (Wle_invariant y hR1 i₀)).resolve_left hi₀ne
  refine ⟨⟨i₀ - 1, by omega⟩, ?_, ?_⟩
  · intro k hk
    have hk' : (blk k : ℕ) < i₀ - 1 := hk
    have : y k ∈ Wle y (i₀ - 1) := Submodule.subset_span ⟨k, hk', rfl⟩
    rw [hlt] at this
    exact (Submodule.mem_bot _).mp this
  · rw [eq_top_iff, ← htop]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, hk, rfl⟩
    by_cases h : blk k = ⟨i₀ - 1, by omega⟩
    · exact Submodule.subset_span ⟨k, h, rfl⟩
    · have hk0 : (blk k : ℕ) < i₀ - 1 := by
        have : (blk k : ℕ) ≠ i₀ - 1 := fun e => h (Fin.ext e)
        omega
      have : y k ∈ Wle y (i₀ - 1) := Submodule.subset_span ⟨k, hk0, rfl⟩
      rw [hlt] at this
      rw [(Submodule.mem_bot _).mp this]
      exact Submodule.zero_mem _

end Abstract

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5Mod
