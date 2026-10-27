module

public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralRotationInvolutionStructure
public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralCentralTransferKernel
public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicSylowComplement

public section

namespace CFSG.Semidihedral.Principal

open scoped Pointwise

variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
theorem mem_sylow_of_mem_center_of_orderOf_eq {t : H} (ht : t ∈ Subgroup.center H) {k : ℕ}
    (htk : orderOf t = 2 ^ k) (S : Sylow 2 H) : t ∈ (S : Subgroup H) := by
  have hT : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, htk])
  have : (Subgroup.zpowers t).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr ht)
  have heq := S.is_maximal' (S.isPGroup'.to_sup_of_normal_right hT) le_sup_left
  rw [← heq]
  exact (le_sup_right : Subgroup.zpowers t ≤ (S : Subgroup H) ⊔ Subgroup.zpowers t)
    (Subgroup.mem_zpowers t)

theorem dihedral_central_involution_normal_odd_complement (S : Sylow 2 H) {n : ℕ} (hn : 2 ≤ n)
    (hS : Nonempty (DihedralGroup (2 ^ (n - 1)) ≃* (S : Subgroup H)))
    (ht : ∃ t ∈ Subgroup.center H, orderOf t = 2) :
    ∃ (N : Subgroup H) (_ : N.Normal),
      (Odd (Nat.card N) ∧ ∃ k : ℕ, N.index = 2 ^ k) ∧
      (∀ N' : Subgroup H, N'.Normal → Odd (Nat.card N') → (∃ k : ℕ, N'.index = 2 ^ k) →
        N' = N) ∧
      N.Characteristic ∧ (∀ x : H, x ∈ N ↔ Odd (orderOf x)) ∧
      (N : Set H) * (S : Set H) = Set.univ ∧ N ⊓ (S : Subgroup H) = ⊥ ∧
      Function.Bijective ((QuotientGroup.mk' N).comp (S : Subgroup H).subtype) := by
  obtain ⟨t, htc, ht2⟩ := ht
  have htS : t ∈ (S : Subgroup H) :=
    mem_sylow_of_mem_center_of_orderOf_eq htc (k := 1) (by rw [ht2, pow_one]) S
  set z : (S : Subgroup H) := ⟨t, htS⟩ with hz
  have hz2 : orderOf z = 2 := by rw [hz, Subgroup.orderOf_mk, ht2]
  have hzS : z ∈ Subgroup.center (S : Subgroup H) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp htc g)
  obtain ⟨A, hAcyc, hAindex, hAcard, hout, hzA⟩ : ∃ A : Subgroup (S : Subgroup H),
      IsCyclic A ∧ A.index = 2 ∧ 2 ≤ Nat.card A ∧
        (∀ x : (S : Subgroup H), x ∉ A → orderOf x = 2) ∧ z ∈ A := by
    obtain ⟨⟨r, s, hr, hs, hrel, hgen⟩, hall⟩ := dihedral_rotation_involution_structure hn hS
    obtain ⟨-, hrindex, -, ⟨hz'A, -, -⟩, hinvol, -, hV4, hcenter, -, -⟩ :=
      hall r s hr hs hrel hgen
    rcases (by omega : n = 2 ∨ 3 ≤ n) with h2 | h3
    · have hK4 := hV4 h2
      refine ⟨Subgroup.zpowers z, inferInstance, ?_, ?_, ?_, Subgroup.mem_zpowers z⟩
      · have h := Subgroup.card_mul_index (Subgroup.zpowers z)
        rw [Nat.card_zpowers, hz2, hK4.card_four] at h
        omega
      · rw [Nat.card_zpowers, hz2]
      · intro x hx
        refine orderOf_eq_prime ?_ fun h => hx (h ▸ Subgroup.one_mem _)
        have h := Monoid.pow_exponent_eq_one x
        rwa [hK4.exponent_two] at h
    · refine ⟨Subgroup.zpowers r, inferInstance, hrindex, ?_, hinvol, ?_⟩
      · rw [Nat.card_zpowers, hr]
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      · have h : z ∈ Subgroup.zpowers (r ^ 2 ^ (n - 2)) := hcenter h3 ▸ hzS
        exact Subgroup.zpowers_le.mpr hz'A h
  have : A.Normal := Subgroup.normal_of_index_eq_two hAindex
  obtain ⟨K, hKindex, hinf, P, hP⟩ : ∃ K : Subgroup H, K.index = 2 ∧
      (S : Subgroup H) ⊓ K = A.map (S : Subgroup H).subtype ∧
      ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = A.map (S : Subgroup H).subtype := by
    obtain ⟨-, -, -, hKindex, hinf, -, P, hP⟩ :=
      dihedral_central_involution_transfer_kernel S A hAcyc hAindex hAcard hout z hzA hz2 htc
    exact ⟨_, hKindex, hinf, P, hP⟩
  have : K.Normal := Subgroup.normal_of_index_eq_two hKindex
  have hA'cyc : IsCyclic (A.map (S : Subgroup H).subtype) :=
    (MulEquiv.isCyclic (A.equivMapOfInjective _ (S : Subgroup H).subtype_injective)).mp hAcyc
  have hPcyc : IsCyclic (P : Subgroup K) :=
    (MulEquiv.isCyclic ((P : Subgroup K).equivMapOfInjective K.subtype
      K.subtype_injective)).mpr (hP ▸ hA'cyc)
  obtain ⟨N₀, _, ⟨hN₀odd, k, hk⟩, -, -, hmemN₀, -, -, hbijN₀⟩ :=
    cyclicSylowTwo_normal_odd_complement P hPcyc
  set N : Subgroup H := N₀.map K.subtype with hNdef
  have hKmem : ∀ x : H, Odd (orderOf x) → x ∈ K := by
    intro x hx
    have hq : QuotientGroup.mk' K x = 1 :=
      hom_eq_one_of_odd_orderOf (IsPGroup.of_card (n := 1) (by
        rw [← Subgroup.index_eq_card, hKindex, pow_one])) (QuotientGroup.mk' K) x hx
    exact (QuotientGroup.eq_one_iff x).mp hq
  have hmemN : ∀ x : H, x ∈ N ↔ Odd (orderOf x) := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
      exact (hmemN₀ y).mp hy
    · intro hx
      have hxK := hKmem x hx
      refine ⟨⟨x, hxK⟩, (hmemN₀ _).mpr ?_, rfl⟩
      rwa [Subgroup.orderOf_mk]
  have hNnormal : N.Normal := by
    refine ⟨fun x hx g => (hmemN _).mpr ?_⟩
    have h := (MulAut.conj g).orderOf_eq x
    rw [MulAut.conj_apply] at h
    rw [h]
    exact (hmemN x).mp hx
  have hNcard : Nat.card N = Nat.card N₀ := Subgroup.card_map_of_injective K.subtype_injective
  have hNindex : N.index = 2 ^ (k + 1) := by
    rw [hNdef, Subgroup.index_map_subtype, hk, hKindex, pow_succ]
  have hdisj : Disjoint N (S : Subgroup H) := by
    rw [Subgroup.disjoint_def]
    intro x hxN hxS
    have hodd := (hmemN x).mp hxN
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp S.isPGroup' ⟨x, hxS⟩
    rw [Subgroup.orderOf_mk] at hj
    rw [hj] at hodd
    have hj0 : j = 0 := by
      by_contra h
      exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' h).mpr even_two)
    rw [hj0, pow_zero] at hj
    exact orderOf_eq_one_iff.mp hj
  have hcardK : Nat.card K = Nat.card N₀ * Nat.card (P : Subgroup K) := by
    rw [← Subgroup.card_mul_index N₀, Subgroup.index_eq_card,
      ← Nat.card_eq_of_bijective _ hbijN₀]
  have hcardP : Nat.card (P : Subgroup K) = Nat.card A := by
    rw [← Subgroup.card_map_of_injective K.subtype_injective, hP,
      Subgroup.card_map_of_injective (S : Subgroup H).subtype_injective]
  have hcardS : Nat.card (S : Subgroup H) = Nat.card A * 2 := by
    rw [← Subgroup.card_mul_index A, hAindex]
  have hcardH : Nat.card H = Nat.card K * 2 := by
    rw [← Subgroup.card_mul_index K, hKindex]
  have hmul : Nat.card N * Nat.card (S : Subgroup H) = Nat.card H := by
    rw [hNcard, hcardS, hcardH, hcardK, hcardP]
    ring
  have hcomp : N.IsComplement' (S : Subgroup H) :=
    Subgroup.isComplement'_of_card_mul_and_disjoint hmul hdisj
  refine ⟨N, hNnormal, ⟨hNcard ▸ hN₀odd, k + 1, hNindex⟩, ?_, ?_, hmemN,
    Subgroup.IsComplement.mul_eq hcomp, disjoint_iff.mp hcomp.disjoint,
    Subgroup.isComplement_subgroup_right_iff_bijective.mp hcomp.symm⟩
  · intro N' hN' hN'odd ⟨k', hk'⟩
    apply le_antisymm
    · intro x hx
      exact (hmemN x).mpr (hN'odd.of_dvd_nat (N'.orderOf_dvd_natCard hx))
    · intro x hx
      have hq : QuotientGroup.mk' N' x = 1 :=
        hom_eq_one_of_odd_orderOf (IsPGroup.of_card (n := k') hk') (QuotientGroup.mk' N') x
          ((hmemN x).mp hx)
      exact (QuotientGroup.eq_one_iff x).mp hq
  · constructor
    intro φ
    ext x
    change φ x ∈ N ↔ x ∈ N
    rw [hmemN, hmemN, φ.orderOf_eq]

end CFSG.Semidihedral.Principal
