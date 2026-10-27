module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bLoc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.LocalAnalysis.GLTheoremA

section Generic

variable {S : Type} [Group S] [Finite S]

theorem finite_mulAut_of_finite : Finite (MulAut S) :=
  Finite.of_injective (fun α : MulAut S => (α : S → S)) DFunLike.coe_injective

theorem card_le_prime_mul_inf_inner {p : ℕ} (hp : p.Prime) (hcyc : IsCyclic (Outer S))
    {A : Subgroup (MulAut S)} (hA : IsElemAbelian p A) :
    Nat.card A ≤ p * Nat.card ↥(A ⊓ inner S) := by
  classical
  haveI : Finite (MulAut S) := finite_mulAut_of_finite
  haveI := hcyc
  let φ : ↥A →* Outer S := (QuotientGroup.mk' (inner S)).comp A.subtype
  have h1 := Subgroup.card_ker_mul_card_range φ
  have hker : Nat.card φ.ker = Nat.card ↥(A ⊓ inner S) := by
    have hk : φ.ker = (A ⊓ inner S).subgroupOf A := by
      ext a
      simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rw [hk]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hrange : Nat.card φ.range ≤ p := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := φ.range)
    have hord : orderOf g = Nat.card φ.range := orderOf_eq_card_of_forall_mem_zpowers hg
    obtain ⟨a, ha⟩ := g.2
    have hgp : g ^ p = 1 := by
      apply Subtype.ext
      have : (a ^ p : ↥A) = 1 := Subtype.ext (hA.2 a a.2)
      calc ((g ^ p : φ.range) : Outer S) = (g : Outer S) ^ p := rfl
        _ = φ a ^ p := by rw [ha]
        _ = φ (a ^ p) := (map_pow φ a p).symm
        _ = 1 := by rw [this, map_one]
    have hdvd : Nat.card φ.range ∣ p := hord ▸ orderOf_dvd_of_pow_eq_one hgp
    exact Nat.le_of_dvd hp.pos hdvd
  calc Nat.card A = Nat.card φ.ker * Nat.card φ.range := h1.symm
    _ = Nat.card ↥(A ⊓ inner S) * Nat.card φ.range := by rw [hker]
    _ ≤ Nat.card ↥(A ⊓ inner S) * p := Nat.mul_le_mul_left _ hrange
    _ = p * Nat.card ↥(A ⊓ inner S) := Nat.mul_comm _ _

theorem inner_part_elemAbelian {p : ℕ} (hZ : Subgroup.center S = ⊥) {A : Subgroup (MulAut S)}
    (hA : IsElemAbelian p A) :
    IsElemAbelian p (A.comap (MulAut.conj : S →* MulAut S)) ∧
      Nat.card (A.comap (MulAut.conj : S →* MulAut S)) = Nat.card ↥(A ⊓ inner S) := by
  have hcjinj : Function.Injective (MulAut.conj : S →* MulAut S) :=
    conj_injective_of_center_eq_bot hZ
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · apply Subtype.ext
    apply hcjinj
    change MulAut.conj ((a : S) * b) = MulAut.conj ((b : S) * a)
    rw [map_mul, map_mul]
    exact isElemAbelian_commute hA a.2 b.2
  · apply hcjinj
    rw [map_pow, map_one]
    exact hA.2 _ hx
  · refine Nat.card_congr (Equiv.ofBijective
      (fun s : A.comap (MulAut.conj : S →* MulAut S) =>
        (⟨MulAut.conj (s : S), s.2, ⟨s, rfl⟩⟩ : ↥(A ⊓ inner S)))
      ⟨fun s t hst => Subtype.ext (hcjinj (congrArg Subtype.val hst)), fun α => ?_⟩)
    obtain ⟨s, hs⟩ := α.2.2
    exact ⟨⟨s, by rw [Subgroup.mem_comap, hs]; exact α.2.1⟩, Subtype.ext hs⟩

end Generic

end CFSG.LocalAnalysis.GLTheoremA.HDesc
