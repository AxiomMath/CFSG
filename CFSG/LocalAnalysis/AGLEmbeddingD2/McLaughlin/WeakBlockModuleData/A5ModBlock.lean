module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5ModChain
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

@[expose] public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5Mod

open Matrix

theorem exists_dot_zero_of_lt_top_field {F : Type} [Field F] {n : ℕ}
    (K : Submodule F (Fin n → F)) (hK : K < ⊤) :
    ∃ f : Fin n → F, f ≠ 0 ∧ ∀ x ∈ K, ∑ i, f i * x i = 0 := by
  obtain ⟨φ, hφ0, hφK⟩ := Submodule.exists_le_ker_of_lt_top K hK
  have e : ∀ i : Fin n, (Pi.single i (1 : F) : Fin n → F) = fun j => if i = j then 1 else 0 := by
    intro i; ext j; simp [Pi.single_apply, eq_comm]
  refine ⟨fun i => φ (Pi.single i 1), ?_, ?_⟩
  · intro h
    apply hφ0
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ φ x]
    simp only [LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h1 := congrFun h i
    simp only [e, Pi.zero_apply] at h1
    rw [h1, smul_zero]
  · intro x hx
    have := hφK hx
    rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ φ x] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [e, smul_eq_mul, mul_comm]

theorem simpleBlk_invariant {ρ : A5 → Fin 4 → Fin 4 → ZMod 2} (h : SimpleBlk ρ)
    (K : Submodule (ZMod 2) (Fin 4 → ZMod 2))
    (hK : ∀ g c, c ∈ K → (fun s => ∑ t, ρ g s t * c t) ∈ K) : K = ⊥ ∨ K = ⊤ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hb, ht⟩ := hcon
  obtain ⟨x, hxK, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hf0, hfK⟩ := exists_dot_zero_of_lt_top_field K (lt_top_iff_ne_top.mpr ht)
  obtain ⟨g, hg⟩ := h x f hx0 hf0
  have := hfK _ (hK g x hxK)
  rw [this] at hg
  exact zero_ne_one hg

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [DistribMulAction A5 W]
  [SMulCommClass A5 (ZMod 2) W]

theorem block4_equiv (hs : IsSimpleMod W) [Nontrivial W] (o : ℕ) (ho : o + 4 ≤ 15) (b : Fin 6)
    (hb : ∀ k : Fin 15, blk k = b ↔ o ≤ (k : ℕ) ∧ (k : ℕ) < o + 4)
    (hsb : SimpleBlk (bm o)) (y : Fin 15 → W)
    (hR1 : ∀ g k, g • y k = ∑ l, Mt g l k • y l) (hy0 : ∀ k, blk k < b → y k = 0)
    (hspan : Submodule.span (ZMod 2) {z | ∃ k : Fin 15, blk k = b ∧ z = y k} = ⊤) :
    ∃ ψ : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] W,
      ∀ g c, ψ (fun s => ∑ t, bm o g s t * c t) = g • ψ c := by
  classical
  let ι : Fin 4 → Fin 15 := fun t => ⟨o + t, by omega⟩
  have hι : Function.Injective ι := fun a b h => by
    have := congrArg Fin.val h
    simp only [ι] at this
    exact Fin.ext (by omega)
  have hιb : ∀ t, blk (ι t) = b := fun t => (hb _).mpr ⟨by simp [ι], by simp [ι]⟩
  let z : Fin 4 → W := fun t => y (ι t)
  have hrel : ∀ g t, g • z t = ∑ s, bm o g s t • z s := by
    intro g t
    simp only [z]
    rw [hR1]
    refine (Fintype.sum_of_injective ι hι _ _ ?_ ?_).symm
    · intro l hl
      have hlb : blk l ≠ b := fun h => hl ⟨⟨(l : ℕ) - o, by have := (hb l).mp h; omega⟩, by
        apply Fin.ext; have := (hb l).mp h; simp [ι]; omega⟩
      rcases lt_or_gt_of_ne hlb with h | h
      · rw [hy0 l h, smul_zero]
      · rw [Mt_tri g l (ι t) (by rw [hιb]; exact h), zero_smul]
    · intro s
      simp [bm, ι, show o + 4 ≤ 15 from ho]
  let ψ : (Fin 4 → ZMod 2) →ₗ[ZMod 2] W := Fintype.linearCombination (ZMod 2) z
  have hψapp : ∀ c, ψ c = ∑ t, c t • z t := fun c => by
    simp [ψ, Fintype.linearCombination_apply]
  have hψsurj : Function.Surjective ψ := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, eq_top_iff, ← hspan]
    refine Submodule.span_mono ?_
    rintro _ ⟨k, hk, rfl⟩
    have h := (hb k).mp hk
    exact ⟨⟨(k : ℕ) - o, by omega⟩, by simp only [z, ι]; congr 1; ext; simp; omega⟩
  have hψeq : ∀ g c, ψ (fun s => ∑ t, bm o g s t * c t) = g • ψ c := by
    intro g c
    calc ψ (fun s => ∑ t, bm o g s t * c t)
        = ∑ s, (∑ t, bm o g s t * c t) • z s := hψapp _
      _ = ∑ s, ∑ t, (bm o g s t * c t) • z s := by simp_rw [Finset.sum_smul]
      _ = ∑ t, ∑ s, (c t * bm o g s t) • z s := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
          rw [mul_comm]
      _ = ∑ t, c t • ∑ s, bm o g s t • z s := by simp_rw [mul_smul, Finset.smul_sum]
      _ = ∑ t, c t • g • z t := by simp_rw [← hrel]
      _ = g • ∑ t, c t • z t := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [smul_comm g (c t)]
      _ = g • ψ c := by rw [hψapp]
  have hker : LinearMap.ker ψ = ⊥ := by
    rcases simpleBlk_invariant hsb (LinearMap.ker ψ) (fun g c hc => by
      rw [LinearMap.mem_ker] at hc ⊢
      rw [hψeq, hc, smul_zero]) with h | h
    · exact h
    · exfalso
      have h0 : ∀ c, ψ c = 0 := fun c => by
        have : c ∈ LinearMap.ker ψ := by rw [h]; exact Submodule.mem_top
        exact this
      obtain ⟨w, hw⟩ := exists_ne (0 : W)
      obtain ⟨c, rfl⟩ := hψsurj w
      exact hw (h0 c)
  have hinj : Function.Injective ψ := fun a b hab => by
    have : a - b ∈ LinearMap.ker ψ := by rw [LinearMap.mem_ker, map_sub, hab, sub_self]
    rw [hker, Submodule.mem_bot] at this
    exact sub_eq_zero.mp this
  exact ⟨LinearEquiv.ofBijective ψ ⟨hinj, hψsurj⟩, hψeq⟩

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5Mod
