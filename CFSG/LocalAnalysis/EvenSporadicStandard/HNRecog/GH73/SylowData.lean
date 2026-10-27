module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.S8Facts

public section

namespace CFSG.EvenSporadicStandard.HNRecog.GH73

open CFSG.GH74.Uniqueness.SU.SU5

structure A8SylowData (X : Type) [Group X] : Prop where
  card_eq : ∃ j : ℕ, Nat.card X = 64 * (2 * j + 1)
  card_sylow : ∀ S : Sylow 2 X, Nat.card ↥(S : Subgroup X) = 64
  card_center : ∀ S : Sylow 2 X, Nat.card (Subgroup.center ↥(S : Subgroup X)) = 2
  no_order_eight : ∀ x : X, orderOf x ≠ 8
  exists_e16 : ∃ E : Subgroup X, Nat.card E = 16 ∧ ∀ x ∈ E, x ^ 2 = 1
  exists_noncomm : ∀ S : Sylow 2 X, ∃ a ∈ (S : Subgroup X), ∃ b ∈ (S : Subgroup X),
    a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a * b ≠ b * a
  gen_four : ∀ P : Subgroup X, IsPGroup 2 P →
    ∃ s : Finset X, s.card ≤ 4 ∧ Subgroup.closure (s : Set X) = P

theorem A8SylowData.of_sylow {X : Type} [Group X] [Finite X] (S : Sylow 2 X)
    (h : IsA8Type ↥(S : Subgroup X)) : A8SylowData X := by
  classical
  haveI : Finite (Sylow 2 X) := Sylow.finite_of_finiteIndex S
  have hT : ∀ T : Sylow 2 X, IsA8Type ↥(T : Subgroup X) := by
    intro T
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S T
    obtain ⟨Q, ⟨e⟩⟩ := h
    rw [← hg]
    exact ⟨Q, ⟨(S.equivSMul g).symm.trans e⟩⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨j, hj⟩ :=
      (Nat.not_even_iff_odd.mp fun he => S.not_dvd_index (even_iff_two_dvd.mp he) : Odd S.index)
    refine ⟨j, ?_⟩
    rw [← Subgroup.card_mul_index (S : Subgroup X), IsA8Type.card_eq h, hj]
  · intro T
    exact IsA8Type.card_eq (hT T)
  · intro T
    exact IsA8Type.card_center (hT T)
  · intro x hx
    have hP : IsPGroup 2 (Subgroup.zpowers x : Subgroup X) := by
      apply IsPGroup.of_card (n := 3)
      rw [Nat.card_zpowers, hx]
      norm_num
    obtain ⟨T, hTle⟩ := hP.exists_le_sylow
    have hxT : x ∈ (T : Subgroup X) := hTle (Subgroup.mem_zpowers x)
    have h4 : (⟨x, hxT⟩ : ↥(T : Subgroup X)) ^ 4 = 1 := IsA8Type.pow_four (hT T) _
    have hx4 : x ^ 4 = 1 := by simpa using h4
    have hdvd : orderOf x ∣ 4 := orderOf_dvd_of_pow_eq_one hx4
    rw [hx] at hdvd
    norm_num at hdvd
  · obtain ⟨E, hEcard, hEsq⟩ := IsA8Type.exists_e16 h
    refine ⟨E.map (S : Subgroup X).subtype, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective (S : Subgroup X).subtype_injective, hEcard]
    · intro y hy
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hy
      have := hEsq e he
      simpa using congrArg (Subtype.val) this
  · intro T
    obtain ⟨a, b, ha, hb, hab⟩ := IsA8Type.exists_noncomm_involutions (hT T)
    refine ⟨(a : X), a.2, (b : X), b.2, ?_, ?_, fun hc => hab (Subtype.ext ?_)⟩
    · simpa using congrArg (fun z : ↥(T : Subgroup X) => (z : X)) ha
    · simpa using congrArg (fun z : ↥(T : Subgroup X) => (z : X)) hb
    · simpa using hc
  ·
    intro P hP
    obtain ⟨T, hPT⟩ := hP.exists_le_sylow
    let R : Subgroup ↥(T : Subgroup X) := P.subgroupOf (T : Subgroup X)
    obtain ⟨s, hscard, hsgen⟩ := IsA8Type.gen_four (hT T) R
    refine ⟨s.image (T : Subgroup X).subtype, Finset.card_image_le.trans hscard, ?_⟩
    rw [Finset.coe_image, ← MonoidHom.map_closure, hsgen,
      Subgroup.map_subgroupOf_eq_of_le hPT]

end CFSG.EvenSporadicStandard.HNRecog.GH73
