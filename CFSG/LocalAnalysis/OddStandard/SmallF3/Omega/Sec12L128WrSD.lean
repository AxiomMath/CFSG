module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open scoped Pointwise

theorem sec128_internal_semidirect_hom {G : Type} [Group G] {H K M : Subgroup G}
    (hKH : K ≤ normalizer (H : Set G)) (hHK : H ⊓ K = ⊥) (hM : H ⊔ K = M)
    {W : Type} [Group W] (ι : ↥H →* W) (κ : ↥K →* W)
    (hcomp : ∀ (k : ↥K) (h h' : ↥H), (h' : G) = (k : G) * (h : G) * (k : G)⁻¹ →
      ι h' = κ k * ι h * (κ k)⁻¹) :
    ∃ ψ : ↥M →* W, (∀ (h : ↥H) (hm : (h : G) ∈ M), ψ ⟨(h : G), hm⟩ = ι h) ∧
      ∀ (k : ↥K) (hm : (k : G) ∈ M), ψ ⟨(k : G), hm⟩ = κ k := by
  classical
  have hMset : (↑M : Set G) = (H : Set G) * (K : Set G) := by
    rw [← hM, Subgroup.coe_mul_of_right_le_normalizer_left H K hKH]
  have huniq : ∀ (h h' : ↥H) (k k' : ↥K),
      (h : G) * (k : G) = (h' : G) * (k' : G) → h = h' ∧ k = k' := by
    intro h h' k k' heq
    have key : (h' : G)⁻¹ * (h : G) = (k' : G) * (k : G)⁻¹ := by
      have hc := congrArg (fun x : G => (h' : G)⁻¹ * x * (k : G)⁻¹) heq
      simpa [mul_assoc] using hc
    have hmem : (h' : G)⁻¹ * (h : G) ∈ H ⊓ K := by
      refine ⟨H.mul_mem (H.inv_mem h'.2) h.2, ?_⟩
      rw [key]
      exact K.mul_mem k'.2 (K.inv_mem k.2)
    rw [hHK, Subgroup.mem_bot] at hmem
    have hh : h = h' := Subtype.ext (inv_mul_eq_one.mp hmem).symm
    have hk : (k' : G) = (k : G) := by
      refine mul_inv_eq_one.mp ?_
      rw [← key]
      exact hmem
    exact ⟨hh, Subtype.ext hk.symm⟩
  have hdec : ∀ m : ↥M, ∃ p : ↥H × ↥K, (m : G) = (p.1 : G) * (p.2 : G) := by
    intro m
    have hm : (m : G) ∈ (H : Set G) * (K : Set G) := by
      rw [← hMset]
      exact m.2
    obtain ⟨h, hh, k, hk, heq⟩ := Set.mem_mul.mp hm
    exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), heq.symm⟩
  let p : ↥M → ↥H × ↥K := fun m => Classical.choose (hdec m)
  have hp : ∀ m : ↥M, (m : G) = (p m).1 * (p m).2 := fun m => Classical.choose_spec (hdec m)
  let ψ : ↥M → W := fun m => ι (p m).1 * κ (p m).2
  have hψ : ∀ (m : ↥M) (h : ↥H) (k : ↥K), (m : G) = (h : G) * (k : G) →
      ψ m = ι h * κ k := by
    intro m h k hk
    have heq : ((p m).1 : G) * ((p m).2 : G) = (h : G) * (k : G) := by
      rw [← hp m, hk]
    obtain ⟨e1, e2⟩ := huniq (p m).1 h (p m).2 k heq
    dsimp only [ψ]
    rw [e1, e2]
  have hmap_mul : ∀ m m' : ↥M, ψ (m * m') = ψ m * ψ m' := by
    intro m m'
    set h : ↥H := (p m).1 with hh
    set k : ↥K := (p m).2 with hk
    set h' : ↥H := (p m').1 with hh'
    set k' : ↥K := (p m').2 with hk'
    have hpm : (m : G) = (h : G) * (k : G) := by
      rw [hh, hk]
      exact hp m
    have hpm' : (m' : G) = (h' : G) * (k' : G) := by
      rw [hh', hk']
      exact hp m'
    let h'' : ↥H := ⟨(k : G) * (h' : G) * (k : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hKH k.2) (h' : G)).mp h'.2⟩
    have hh''coe : (h'' : G) = (k : G) * (h' : G) * (k : G)⁻¹ := rfl
    have hdecomp : ((m * m' : ↥M) : G) = ((h * h'' : ↥H) : G) * ((k * k' : ↥K) : G) := by
      simp only [Subgroup.coe_mul, hh''coe]
      rw [hpm, hpm']
      group
    have h1 := hψ (m * m') (h * h'') (k * k') hdecomp
    have h2 := hψ m h k hpm
    have h3 := hψ m' h' k' hpm'
    rw [h1, h2, h3, map_mul, map_mul, hcomp k h' h'' rfl]
    group
  refine ⟨MonoidHom.mk' ψ hmap_mul, ?_, ?_⟩
  · intro h hm
    have h := hψ ⟨(h : G), hm⟩ h 1 (by simp)
    simpa using h
  · intro k hm
    have h := hψ ⟨(k : G), hm⟩ 1 k (by simp)
    simpa using h

end CFSG.OddStandard.SmallF3.Omega
