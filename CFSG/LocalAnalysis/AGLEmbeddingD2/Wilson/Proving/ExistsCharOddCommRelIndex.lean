module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.FixedPointFreeInvolution
public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

open Subgroup

theorem eq_one_of_sq_and_odd_pow {G : Type*} [Group G] {x : G} {m : ℕ} (hm : Odd m)
    (h2 : x ^ 2 = 1) (hm1 : x ^ m = 1) : x = 1 := by
  have hd1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have hd2 : orderOf x ∣ m := orderOf_dvd_of_pow_eq_one hm1
  have hcop : Nat.Coprime 2 m := Nat.coprime_two_left.mpr hm
  have hg := Nat.dvd_gcd hd1 hd2
  rw [hcop.gcd_eq_one] at hg
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)

theorem exists_normal_index_two_odd {G : Type*} [Group G] [Finite G] (Q : Sylow 2 G)
    (hQ : Nat.card (Q : Subgroup G) = 2)
    (hP : Subgroup.normalizer (Q : Subgroup G) ≤ Subgroup.centralizer (Q : Set G)) :
    ∃ K : Subgroup G, K.Normal ∧ K.index = 2 ∧ Odd (Nat.card K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : IsComplement' (MonoidHom.transferSylow Q hP).ker (Q : Subgroup G) :=
    MonoidHom.ker_transferSylow_isComplement' Q hP
  have hcard : Nat.card (MonoidHom.transferSylow Q hP).ker * Nat.card (Q : Subgroup G) = Nat.card G :=
    hc.card_mul_card
  have hpos : 0 < Nat.card (MonoidHom.transferSylow Q hP).ker := Nat.card_pos
  have hKidx : (MonoidHom.transferSylow Q hP).ker.index = 2 := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [Subgroup.index_mul_card, ← hcard, hQ]
    ring
  have hQidx : (Q : Subgroup G).index = Nat.card (MonoidHom.transferSylow Q hP).ker := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := (Q : Subgroup G)))
    rw [Subgroup.index_mul_card, ← hcard]
  refine ⟨(MonoidHom.transferSylow Q hP).ker, inferInstance, hKidx, ?_⟩
  have hnd := Sylow.not_dvd_index Q
  rw [hQidx] at hnd
  exact Nat.odd_iff.mpr (by omega)

theorem mem_of_pow_odd_eq_one_of_index_two {G : Type*} [Group G] [Finite G] (K : Subgroup G)
    [K.Normal] (hK : K.index = 2) {y : G} {m : ℕ} (hm : Odd m) (hym : y ^ m = 1) : y ∈ K := by
  have hcard : Nat.card (G ⧸ K) = 2 := by rw [← Subgroup.index_eq_card]; exact hK
  have h2 : (QuotientGroup.mk' K y) ^ 2 = 1 := by
    have := pow_card_eq_one' (G := G ⧸ K) (x := QuotientGroup.mk' K y)
    rwa [hcard] at this
  have hm' : (QuotientGroup.mk' K y) ^ m = 1 := by
    rw [← map_pow, hym, map_one]
  have h1 := eq_one_of_sq_and_odd_pow hm h2 hm'
  rw [QuotientGroup.mk'_apply] at h1
  exact (QuotientGroup.eq_one_iff y).mp h1

theorem exists_char_odd_comm_relIndex_le_two {Γ : Type*} [Group Γ] (N : Subgroup Γ) [Finite N]
    (t : Γ) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htN : ∀ n ∈ N, t * n * t⁻¹ ∈ N)
    (hC : ∀ n ∈ N, t * n = n * t → n = 1 ∨ n = t) :
    ∃ A : Subgroup Γ, A ≤ N ∧
      (∀ g : Γ, (∀ n ∈ N, g * n * g⁻¹ ∈ N) → ∀ a ∈ A, g * a * g⁻¹ ∈ A) ∧
      Odd (Nat.card A) ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ A.relIndex N ≤ 2 := by
  classical
  by_cases htN' : t ∈ N
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨T, hTval⟩ : ∃ T : N, (T : Γ) = t := ⟨⟨t, htN'⟩, rfl⟩
    have hT2 : T ^ 2 = 1 := Subtype.ext (by simp [hTval, ht2])
    have hT1 : T ≠ 1 := fun h => ht1 (by rw [← hTval, h]; simp)
    have hord : orderOf T = 2 := orderOf_eq_prime hT2 hT1
    have hTp : IsPGroup 2 (zpowers T) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
    obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hTp
    have hTQ : T ∈ (Q : Subgroup N) := hQ (mem_zpowers T)
    have : Nontrivial (Q : Subgroup N) :=
      ⟨⟨⟨T, hTQ⟩, (1 : (Q : Subgroup N)), fun h => hT1 (congrArg Subtype.val h)⟩⟩
    have := IsPGroup.center_nontrivial Q.isPGroup'
    obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (1 : Subgroup.center (Q : Subgroup N))
    have hxc : ∀ g : (Q : Subgroup N), g * x = x * g := fun g => Subgroup.mem_center_iff.mp hx g
    have hxN : ∀ g : (Q : Subgroup N), (g : N) * (x : N) = (x : N) * (g : N) :=
      fun g => congrArg Subtype.val (hxc g)
    have hxΓ : ((x : N) : Γ) ≠ 1 := by
      intro h
      apply hx1
      exact Subtype.ext (Subtype.ext (Subtype.ext (by simpa using h)))
    have hxT : (x : N) = T := by
      have hxt : t * ((x : N) : Γ) = ((x : N) : Γ) * t := by
        have := congrArg Subtype.val (hxN ⟨T, hTQ⟩)
        simpa [hTval] using this
      rcases hC _ (x : N).2 hxt with h | h
      · exact absurd h hxΓ
      · exact Subtype.ext (h.trans hTval.symm)
    have hTcomm : ∀ y ∈ (Q : Subgroup N), y * T = T * y := by
      intro y hy
      have := hxN ⟨y, hy⟩
      rw [hxT] at this
      exact this
    have hQset : ∀ y ∈ (Q : Subgroup N), y = 1 ∨ y = T := by
      intro y hy
      have hΓ : t * ((y : N) : Γ) = ((y : N) : Γ) * t := by
        have h := congrArg Subtype.val (hTcomm y hy)
        simp only [Subgroup.coe_mul, hTval] at h
        exact h.symm
      rcases hC _ (y : N).2 hΓ with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext (h.trans hTval.symm))
    have hQeq : (Q : Subgroup N) = zpowers T := by
      apply le_antisymm
      · intro y hy
        rcases hQset y hy with h | h
        · rw [h]; exact one_mem _
        · rw [h]; exact mem_zpowers T
      · exact hQ
    have hcardQ : Nat.card (Q : Subgroup N) = 2 := by
      rw [hQeq, Nat.card_zpowers, hord]
    have hP : Subgroup.normalizer (Q : Subgroup N) ≤ Subgroup.centralizer (Q : Set N) := by
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hh' : h ∈ (Q : Subgroup N) := hh
      rcases hQset h hh' with h1 | h1
      · rw [h1]; simp
      · rw [h1]
        rcases hQset _ ((Subgroup.mem_normalizer_iff.mp hg T).mp hTQ) with h2 | h2
        · exfalso
          have h3 : g * T = g * 1 := by
            rw [mul_one]; exact mul_inv_eq_one.mp h2
          exact hT1 (mul_left_cancel h3)
        · exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    obtain ⟨K, hKn, hKidx, hKodd⟩ := exists_normal_index_two_odd Q hcardQ hP
    have := hKn
    obtain ⟨A, hAdef⟩ : ∃ A : Subgroup Γ, A = K.map N.subtype := ⟨_, rfl⟩
    have hmem : ∀ a : Γ, a ∈ A ↔ ∃ k ∈ K, ((k : N) : Γ) = a := by
      intro a
      rw [hAdef, Subgroup.mem_map]
      exact Iff.rfl
    have hAN : A ≤ N := by
      rw [hAdef]
      exact Subgroup.map_subtype_le K
    have : Finite A :=
      Finite.of_injective (fun a : A => (⟨a.1, hAN a.2⟩ : N))
        (fun a b h => Subtype.ext (congrArg (fun z : N => (z : Γ)) h))
    have htM : ∀ m ∈ A, t * m * t⁻¹ ∈ A := by
      intro m hm
      obtain ⟨k, hk, rfl⟩ := (hmem m).mp hm
      refine (hmem _).mpr ⟨T * k * T⁻¹, hKn.conj_mem k hk T, ?_⟩
      simp [hTval]
    have hfix : ∀ m ∈ A, t * m = m * t → m = 1 := by
      intro m hm hcm
      obtain ⟨k, hk, rfl⟩ := (hmem m).mp hm
      rcases hC _ (k : N).2 hcm with h | h
      · exact h
      · exfalso
        have hkT : k = T := Subtype.ext (h.trans hTval.symm)
        have hTK : T ∈ K := by
          rw [← hkT]
          exact hk
        have hTm : T ^ Nat.card K = 1 := by
          have h := pow_card_eq_one' (G := K) (x := ⟨T, hTK⟩)
          have h' := congrArg (fun z : K => (z : N)) h
          simp only [Subgroup.coe_pow, Subgroup.coe_one] at h'
          exact h'
        exact hT1 (eq_one_of_sq_and_odd_pow hKodd hT2 hTm)
    obtain ⟨hcommA, hoddA⟩ := commute_odd_of_fixedPointFree_involution A t ht2 htM hfix
    have hkm : ∀ k ∈ K, ((k : N) : Γ) ^ Nat.card K = 1 := by
      intro k hk
      have h := pow_card_eq_one' (G := K) (x := ⟨k, hk⟩)
      have h' := congrArg (fun z : K => ((z : N) : Γ)) h
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at h'
      exact h'
    have hinv : ∀ g : Γ, (∀ n ∈ N, g * n * g⁻¹ ∈ N) → ∀ a ∈ A, g * a * g⁻¹ ∈ A := by
      intro g hg a ha
      obtain ⟨k, hk, rfl⟩ := (hmem a).mp ha
      have hy : g * ((k : N) : Γ) * g⁻¹ ∈ N := hg _ (k : N).2
      obtain ⟨y, hyval⟩ : ∃ y : N, ((y : N) : Γ) = g * ((k : N) : Γ) * g⁻¹ :=
        ⟨⟨_, hy⟩, rfl⟩
      have hym : y ^ Nat.card K = 1 :=
        Subtype.ext (by simp [hyval, conj_pow, hkm k hk])
      have hyK : y ∈ K := mem_of_pow_odd_eq_one_of_index_two K hKidx hKodd hym
      exact (hmem _).mpr ⟨y, hyK, hyval⟩
    have hsub : A.subgroupOf N = K := by
      ext x
      rw [Subgroup.mem_subgroupOf, hmem]
      constructor
      · rintro ⟨k, hk, hkx⟩
        rw [← Subtype.ext hkx]
        exact hk
      · intro hx
        exact ⟨x, hx, rfl⟩
    refine ⟨A, hAN, hinv, hoddA, hcommA, ?_⟩
    simp [Subgroup.relIndex, hsub, hKidx]
  ·
    have hfix : ∀ m ∈ N, t * m = m * t → m = 1 := by
      intro m hm hcm
      rcases hC m hm hcm with h | h
      · exact h
      · exact absurd (h ▸ hm) htN'
    obtain ⟨hcomm, hodd⟩ := commute_odd_of_fixedPointFree_involution N t ht2 htN hfix
    refine ⟨N, le_rfl, fun g hg a ha => hg a ha, hodd, hcomm, ?_⟩
    rw [Subgroup.relIndex_self]
    norm_num

end CFSG.AGLEmbeddingD2.Wilson.Proving

end
