module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLevi
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrIso

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open CFSG.AGLEmbedding.ParabPrime
open scoped commutatorElement Pointwise

section Map

variable {A B : Type*} [Group A] [Group B] (f : A →* B)

theorem map_perfectJoin_le {J : Subgroup A} {J' : Subgroup B} (h : J.map f ≤ J') :
    (perfectJoin J).map f ≤ perfectJoin J' :=
  le_perfectJoin ((Subgroup.map_mono (perfectJoin_le J)).trans h) (by
    rw [← Subgroup.map_commutator, perfectJoin_perfect])

theorem map_twoCore_le {J : Subgroup A} {J' : Subgroup B} (h : J.map f ≤ J') :
    (twoCore J).map f ≤ twoCore J' := by
  rw [Subgroup.map_le_iff_le_comap]
  refine (Subgroup.closure_le _).2 ?_
  rintro g (hg | ⟨hgJ, k, hk⟩)
  · exact perfectJoin_le_twoCore J' (map_perfectJoin_le f h ⟨g, hg, rfl⟩)
  · exact twoElems_subset_twoCore J' ⟨h ⟨g, hgJ, rfl⟩, k, by rw [← map_pow, hk, map_one]⟩

end Map

section Power

variable {G : Type*} [Group G]

theorem powerMap_of_torus {J N T : Subgroup G}
    (hJN : J ≤ Subgroup.normalizer (N : Set G))
    (hdec : ∀ x ∈ J, ∃ t ∈ T, ∃ n ∈ N, x = t * n) (hTJ : T ≤ J) {f : G →* G}
    (hfJ : J.map f ≤ J) (hfN : N.map f ≤ N) {k : ℕ}
    (hk : ∀ t ∈ T, f t * (t ^ k)⁻¹ ∈ N) : ∀ x ∈ J, f x * (x ^ k)⁻¹ ∈ N := by
  have : (N.subgroupOf J).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hJN
  set φ : ↥J →* ↥J ⧸ N.subgroupOf J := QuotientGroup.mk' _ with hφ
  have key : ∀ (a b : G) (ha : a ∈ J) (hb : b ∈ J), φ ⟨a, ha⟩ = φ ⟨b, hb⟩ → a * b⁻¹ ∈ N := by
    intro a b ha hb h
    have h1 : φ (⟨a, ha⟩ * ⟨b, hb⟩⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)
  have key' : ∀ (a b : G) (ha : a ∈ J) (hb : b ∈ J), a * b⁻¹ ∈ N → φ ⟨a, ha⟩ = φ ⟨b, hb⟩ := by
    intro a b ha hb h
    have h1 : φ (⟨a, ha⟩ * ⟨b, hb⟩⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 h)
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  intro x hx
  obtain ⟨t, ht, n, hn, rfl⟩ := hdec x hx
  have htJ : t ∈ J := hTJ ht
  have hfxJ : f (t * n) ∈ J := hfJ ⟨_, hx, rfl⟩
  have hftJ : f t ∈ J := hfJ ⟨t, htJ, rfl⟩
  have hfnN : f n ∈ N := hfN ⟨n, hn, rfl⟩
  have h1 : φ ⟨t * n, hx⟩ = φ ⟨t, htJ⟩ := by
    refine key' _ _ hx htJ ?_
    exact (Subgroup.mem_normalizer_iff.1 (hJN htJ) n).1 hn
  have h2 : φ ⟨f (t * n), hfxJ⟩ = φ ⟨f t, hftJ⟩ := by
    refine key' _ _ hfxJ hftJ ?_
    rw [map_mul]
    simpa [mul_assoc] using (Subgroup.mem_normalizer_iff.1 (hJN hftJ) (f n)).1 hfnN
  have h3 : φ ⟨f t, hftJ⟩ = φ ⟨t ^ k, J.pow_mem htJ k⟩ := key' _ _ hftJ (J.pow_mem htJ k) (hk t ht)
  have h4 : φ ⟨(t * n) ^ k, J.pow_mem hx k⟩ = φ ⟨t ^ k, J.pow_mem htJ k⟩ := by
    have e1 : (⟨(t * n) ^ k, J.pow_mem hx k⟩ : ↥J) = ⟨t * n, hx⟩ ^ k := rfl
    have e2 : (⟨t ^ k, J.pow_mem htJ k⟩ : ↥J) = ⟨t, htJ⟩ ^ k := rfl
    rw [e1, e2, map_pow, map_pow, h1]
  exact key _ _ hfxJ (J.pow_mem hx k) (h2.trans (h3.trans h4.symm))

end Power

section Aut

variable {Y : Type*} [Group Y]

theorem iff_of_mem_normalizer_map_conj
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y)) {J : Subgroup Y} {α : MulAut Y}
    (hα : α ∈ Subgroup.normalizer
      ((J.map (MulAut.conj : Y →* MulAut Y) : Subgroup (MulAut Y)) : Set (MulAut Y))) :
    ∀ z, z ∈ J ↔ α z ∈ J := by
  intro z
  have h := (Subgroup.mem_normalizer_iff.1 hα) (MulAut.conj z)
  rw [aut_mul_conj_mul_inv, Subgroup.mem_map_iff_mem hinj, Subgroup.mem_map_iff_mem hinj] at h
  exact h

theorem exists_conj_mul_normalizes [Finite Y] (S₀ : Sylow 2 Y) {J : Subgroup Y}
    (hSJ : (S₀ : Subgroup Y) ≤ J) (α : MulAut Y) (hα : J.map α.toMonoidHom = J) :
    ∃ j ∈ J, (S₀ : Subgroup Y).map (MulAut.conj j * α).toMonoidHom = S₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S₂ : Sylow 2 Y := α • S₀ with hS₂
  have hS₂c : (S₂ : Subgroup Y) = (S₀ : Subgroup Y).map α.toMonoidHom := rfl
  have hS₂J : (S₂ : Subgroup Y) ≤ J := by
    rw [hS₂c]
    exact (Subgroup.map_mono hSJ).trans hα.le
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J (S₂.subtype hS₂J) (S₀.subtype hSJ)
  rw [Sylow.smul_subtype hS₂J] at hg
  have hg' := Sylow.subtype_injective hg
  refine ⟨g, g.2, ?_⟩
  have h2 : ((g • S₂ : Sylow 2 Y) : Subgroup Y) = (S₀ : Subgroup Y) :=
    congrArg (fun P : Sylow 2 Y => (P : Subgroup Y)) hg'
  have h3 : (MulAut.conj (g : Y) * α).toMonoidHom =
      (MulAut.conj (g : Y)).toMonoidHom.comp α.toMonoidHom := by
    ext x
    rfl
  rw [h3, ← Subgroup.map_map, ← hS₂c]
  exact h2

end Aut

end CFSG.AGLEmbedding.ParabAutIrr
