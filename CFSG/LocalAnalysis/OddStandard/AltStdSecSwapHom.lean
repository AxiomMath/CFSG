module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecSwapDefs
public import CFSG.LocalAnalysis.OddStandard.AltStdSecSwapPerm

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm

variable {G : Type*} [Group G]

namespace SwapData

variable {a : G} {N : ℕ}

@[expose] def hom (D : SwapData a N) : Perm (Fin N) →* G :=
  D.S.subtype.comp D.ι.toMonoidHom

theorem hom_apply (D : SwapData a N) (σ : Perm (Fin N)) : D.hom σ = (D.ι σ : G) := rfl

theorem hom_injective (D : SwapData a N) : Function.Injective D.hom :=
  Subtype.val_injective.comp D.ι.injective

theorem hom_mem (D : SwapData a N) (σ : Perm (Fin N)) : D.hom σ ∈ D.S := (D.ι σ).2

theorem mem_partners_iff (D : SwapData a N) {x : G} :
    x ∈ Partners a ↔ ∃ τ : Perm (Fin N), τ.IsSwap ∧ D.hom τ = x := by
  rw [D.part]
  exact ⟨fun ⟨τ, hτ, h⟩ => ⟨τ, hτ, h.symm⟩, fun ⟨τ, hτ, h⟩ => ⟨τ, hτ, h.symm⟩⟩

theorem partners_subset (D : SwapData a N) {x : G} (hx : x ∈ Partners a) : x ∈ D.S := by
  obtain ⟨τ, -, rfl⟩ := D.mem_partners_iff.1 hx
  exact D.hom_mem τ

theorem exists_completion (D : SwapData a N) {k : ℕ} (hk : 2 ≤ k) {t : ℕ → G}
    (ht : ∀ i < k, t i ∈ Partners a)
    (hcomm : ∀ i j, i + 2 ≤ j → j < k → t i * t j = t j * t i)
    (hne : ∀ i j, i < k → j < k → i ≠ j → t i ≠ t j)
    {c : G} (hc : c ∈ Partners a) (hcne : ∀ i < k, c ≠ t i)
    (hccomm : ∀ i < k, c * t i = t i * c) :
    ∃ d ∈ Partners a, (t (k - 1) * d) ^ 3 = 1 ∧ (d * c) ^ 3 = 1 ∧
      (∀ i, i + 2 ≤ k → d * t i = t i * d) ∧ (∀ i < k, d ≠ t i) ∧ d ≠ c := by
  classical
  have hpre : ∀ i, ∃ τ : Perm (Fin N), i < k → τ.IsSwap ∧ D.hom τ = t i := by
    intro i
    by_cases hi : i < k
    · obtain ⟨τ, hτ, h⟩ := D.mem_partners_iff.1 (ht i hi)
      exact ⟨τ, fun _ => ⟨hτ, h⟩⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose τ hτ using hpre
  obtain ⟨γ, hγ, hγc⟩ := D.mem_partners_iff.1 hc
  have hinj := D.hom_injective
  obtain ⟨δ, hδ, h1, h2, h3, h4, h5⟩ := exists_swap_completion (α := Fin N) hk (t := τ)
    (fun i hi => (hτ i hi).1)
    (fun i j hij hj => hinj (by
      rw [map_mul, map_mul, (hτ i (by omega)).2, (hτ j hj).2]
      exact hcomm i j hij hj))
    (fun i j hi hj hij h => hne i j hi hj hij (by
      rw [← (hτ i hi).2, ← (hτ j hj).2, h]))
    hγ (fun i hi h => hcne i hi (by rw [← hγc, ← (hτ i hi).2, h]))
    (fun i hi => hinj (by
      rw [map_mul, map_mul, hγc, (hτ i hi).2]
      exact hccomm i hi))
  refine ⟨D.hom δ, D.mem_partners_iff.2 ⟨δ, hδ, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have := congrArg D.hom h1
    rwa [map_pow, map_mul, map_one, (hτ (k - 1) (by omega)).2] at this
  · have := congrArg D.hom h2
    rwa [map_pow, map_mul, map_one, hγc] at this
  · intro i hi
    have := congrArg D.hom (h3 i hi)
    rwa [map_mul, map_mul, (hτ i (by omega)).2] at this
  · intro i hi h
    exact h4 i hi (hinj (by rw [h, (hτ i hi).2]))
  · intro h
    exact h5 (hinj (by rw [h, hγc]))

theorem commute_of_chain_three (D : SwapData a N) {u v w s : G} (hu : u ∈ Partners a)
    (hv : v ∈ Partners a) (hw : w ∈ Partners a) (hs : s ∈ Partners a) (huv : u ≠ v)
    (hvw : v ≠ w) (huw : u ≠ w) (h3uv : (u * v) ^ 3 = 1) (h3vw : (v * w) ^ 3 = 1)
    (hcuw : u * w = w * u) (hsu : s * u = u * s) (hsw : s * w = w * s) (hsune : s ≠ u)
    (hswne : s ≠ w) : s * v = v * s := by
  obtain ⟨u', hu', rfl⟩ := D.mem_partners_iff.1 hu
  obtain ⟨v', hv', rfl⟩ := D.mem_partners_iff.1 hv
  obtain ⟨w', hw', rfl⟩ := D.mem_partners_iff.1 hw
  obtain ⟨s', hs', rfl⟩ := D.mem_partners_iff.1 hs
  have hinj := D.hom_injective
  have := AltStdSec.commute_of_chain_three hu' hv' hw' hs'
    (fun h => huv (by rw [h])) (fun h => hvw (by rw [h])) (fun h => huw (by rw [h]))
    (hinj (by rw [map_pow, map_mul, map_one]; exact h3uv))
    (hinj (by rw [map_pow, map_mul, map_one]; exact h3vw))
    (hinj (by rw [map_mul, map_mul]; exact hcuw))
    (hinj (by rw [map_mul, map_mul]; exact hsu))
    (hinj (by rw [map_mul, map_mul]; exact hsw))
    (fun h => hsune (by rw [h])) (fun h => hswne (by rw [h]))
  have := congrArg D.hom this
  rwa [map_mul, map_mul] at this

theorem isSwap_of_conj (D : SwapData a N) {N' : ℕ} {M : Subgroup G} (e : Perm (Fin N') ≃* M)
    (ha : a ∈ M) (ha1 : a ≠ 1) (ha2 : a * a = 1)
    (hconj : ∀ s : Perm (Fin N'), s.IsSwap → IsConj a (e s : G)) :
    (e.symm ⟨a, ha⟩).IsSwap := by
  set π : Perm (Fin N') := e.symm ⟨a, ha⟩ with hπdef
  have hπa : (e π : G) = a := by rw [hπdef, MulEquiv.apply_symm_apply]
  have hπ : π * π = 1 := by
    apply e.injective
    rw [map_mul, map_one]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_one]
    rw [hπa]
    exact ha2
  let B : Subgroup (Perm (Fin N')) := D.S.comap (M.subtype.comp e.toMonoidHom)
  have hB : ∀ s : Perm (Fin N'), s.IsSwap → s * π = π * s → s ≠ π → s ∈ B := by
    intro s hs hcomm hne
    have hpart : (e s : G) ∈ Partners a := by
      refine ⟨(hconj s hs), ?_, ?_⟩
      · intro h
        apply hne
        apply e.injective
        apply Subtype.ext
        rw [h, hπa]
      · have := congrArg (fun y : Perm (Fin N') => ((e y : M) : G)) hcomm
        simp only [map_mul, Subgroup.coe_mul] at this
        rw [hπa] at this
        exact this
    exact D.partners_subset hpart
  rcases mem_of_involution hπ hB with h | h
  · exfalso
    have hmem : a ∈ D.S := by
      have : (e π : G) ∈ D.S := h
      rwa [hπa] at this
    have : a ∈ zpowers a ⊓ D.S := ⟨mem_zpowers a, hmem⟩
    rw [D.disj] at this
    exact ha1 (by simpa using this)
  · exact h

end SwapData

end CFSG.OddStandard.AltStdSec
