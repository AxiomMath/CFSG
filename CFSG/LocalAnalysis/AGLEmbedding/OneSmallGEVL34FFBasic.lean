module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UPrimeExcL34
public import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

namespace L34FF

variable {G : Type*} [Group G] [Finite G]

theorem relIndex_left_sup {A B : Subgroup G} (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    A.relIndex (A ⊔ B) = (A ⊓ B).relIndex B := by
  have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hB
  have h1 := Subgroup.relIndex_mul_card A (A ⊔ B)
  have h2 := Subgroup.relIndex_mul_card (A ⊓ B) B
  rw [inf_of_le_left le_sup_left] at h1
  rw [inf_of_le_left inf_le_right] at h2
  have hpos : 0 < Nat.card A * Nat.card (A ⊓ B : Subgroup G) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc A.relIndex (A ⊔ B) * (Nat.card A * Nat.card (A ⊓ B : Subgroup G))
      = Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) := by rw [← h1]; ring
    _ = Nat.card A * Nat.card B := h
    _ = (A ⊓ B).relIndex B * (Nat.card A * Nat.card (A ⊓ B : Subgroup G)) := by
      rw [← h2]; ring

theorem relIndex_right_sup {A B : Subgroup G} (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    B.relIndex (A ⊔ B) = (A ⊓ B).relIndex A := by
  have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hB
  have h1 := Subgroup.relIndex_mul_card B (A ⊔ B)
  have h2 := Subgroup.relIndex_mul_card (A ⊓ B) A
  rw [inf_of_le_left le_sup_right] at h1
  rw [inf_of_le_left inf_le_left] at h2
  have hpos : 0 < Nat.card B * Nat.card (A ⊓ B : Subgroup G) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc B.relIndex (A ⊔ B) * (Nat.card B * Nat.card (A ⊓ B : Subgroup G))
      = Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) := by rw [← h1]; ring
    _ = Nat.card A * Nat.card B := h
    _ = (A ⊓ B).relIndex A * (Nat.card B * Nat.card (A ⊓ B : Subgroup G)) := by
      rw [← h2]; ring

theorem mem_of_mem_sup_of_pow_prime_pow {q a : ℕ} {N U : Subgroup G}
    (hUN : U ≤ Subgroup.normalizer (N : Set G)) (hU : Nat.Coprime (Nat.card U) q) {x : G}
    (hx : x ∈ N ⊔ U) (hxq : x ^ q ^ a = 1) : x ∈ N := by
  set S := N ⊔ U with hS
  have hSN : S ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hUN
  have : (N.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hSN
  have hm : (N.subgroupOf S).index ∣ Nat.card U := by
    change N.relIndex (N ⊔ U) ∣ Nat.card U
    rw [relIndex_left_sup hUN]
    exact Subgroup.relIndex_dvd_card _ _
  set y := QuotientGroup.mk' (N.subgroupOf S) (⟨x, hx⟩ : S) with hy
  have hy1 : y ^ (N.subgroupOf S).index = 1 := by
    rw [hy, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.pow_index_mem _ _
  have hy2 : y ^ q ^ a = 1 := by
    rw [hy, ← map_pow]
    have : (⟨x, hx⟩ : S) ^ q ^ a = 1 := Subtype.ext (by simpa using hxq)
    rw [this, map_one]
  have hcop : Nat.Coprime (N.subgroupOf S).index (q ^ a) :=
    Nat.Coprime.pow_right a (Nat.Coprime.coprime_dvd_left hm hU)
  have ho : orderOf y = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hy1) hcop)
      (orderOf_dvd_of_pow_eq_one hy2)
  have h1 : y = 1 := orderOf_eq_one_iff.mp ho
  rw [hy, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem isSylowTwoOf_inf_of_le_of_normalizes {V D N : Subgroup G} (hV : IsSylowTwoOf V D)
    (hND : N ≤ D)
    (hVN : V ≤ Subgroup.normalizer (N : Set G)) : IsSylowTwoOf (V ⊓ N) N := by
  refine ⟨inf_le_right, hV.2.1.to_le inf_le_left, fun h2 => hV.2.2 ?_⟩
  change 2 ∣ V.relIndex D
  have e : (V ⊓ N).relIndex N = V.relIndex (N ⊔ V) := by
    rw [relIndex_right_sup hVN, inf_comm]
  rw [← Subgroup.relIndex_mul_relIndex V (N ⊔ V) D le_sup_right (sup_le hND hV.1)]
  exact Dvd.dvd.mul_right (e ▸ h2) _

omit [Finite G] in
theorem isKGroup_of_catalogSimpleSections_finite {X : Type} [Group X] [Finite X]
    (h : CatalogSimpleSections X) : CFSG.IsKGroup X :=
  CFSG.KCore.KGroupNonab.kGroupAllSimple CFSG.Assembly.inCatalog_isoInvariant
    CFSG.Assembly.inCatalog_containsAbelianSimple (catalogSimpleSections_iff_isKGroup.mp h)

theorem nonempty_quotient_primeComplementCore_mulEquiv {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] {p : ℕ} (hp : p.Prime) (f : A →* B) (hf : Function.Surjective f)
    (hker : Nat.Coprime p (Nat.card f.ker)) :
    Nonempty (A ⧸ primeComplementCore (G := A) p ≃* B ⧸ primeComplementCore (G := B) p) := by
  have : Fact p.Prime := ⟨hp⟩
  set OB := primeComplementCore (G := B) p with hOB
  set φ := (QuotientGroup.mk' OB).comp f with hφdef
  have hφ : Function.Surjective φ := (QuotientGroup.mk'_surjective OB).comp hf
  have hk : φ.ker = OB.comap f := by
    ext x
    simp [φ, QuotientGroup.eq_one_iff]
  have hcopB := primeComplementCore_coprime (G := B) p
  have hkerφ : φ.ker = primeComplementCore (G := A) p := by
    rw [hk]
    apply le_antisymm
    · refine normal_coprime_le_primeComplementCore p _ (Subgroup.Normal.comap inferInstance f) ?_
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro hdvd
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
      have hfx : f x ∈ OB := x.2
      have h1 : orderOf (f x) = 1 := by
        have h2 : orderOf (f x) ∣ p := by
          rw [← hx, ← Subgroup.orderOf_coe]
          exact orderOf_map_dvd f x
        have h3 : orderOf (f x) ∣ Nat.card OB := Subgroup.orderOf_dvd_natCard OB hfx
        exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hcopB) h3
      have hxk : (x : A) ∈ f.ker := MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp h1)
      have h4 : orderOf (x : A) ∣ Nat.card f.ker := Subgroup.orderOf_dvd_natCard f.ker hxk
      rw [Subgroup.orderOf_coe, hx] at h4
      exact (Nat.Prime.coprime_iff_not_dvd hp).mp hker h4
    · have hmap : (primeComplementCore (G := A) p).map f ≤ OB :=
        normal_coprime_le_primeComplementCore p _
          (Subgroup.Normal.map inferInstance f hf)
          (Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ f)
            (primeComplementCore_coprime (G := A) p))
      exact fun x hx => hmap ⟨x, hx, rfl⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerφ.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

omit [Finite G] in
theorem isLinThreeFour_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (hB : IsLinThreeFour B) : IsLinThreeFour A := by
  obtain ⟨d, hd, ⟨φ⟩⟩ := hB
  exact ⟨d, hd, ⟨e.trans φ⟩⟩

omit [Finite G] in
theorem primeComplementCore_three_eq_bot_of_isLinThreeFour {K : Type} [Group K] [Finite K]
    (hK : IsLinThreeFour K) :
    primeComplementCore (G := K) 3 = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T⟩ : Nonempty (Sylow 3 K) := inferInstance
  refine KFactProofs.UPrimeExcL34.eq_bot_of_le_normalizer_of_isLinThreeFour hK
    (KFactProofs.UPrimeExcL34.card_sylow_three_of_isLinThreeFour hK T)
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (primeComplementCore_coprime 3)) ?_
  rw [Subgroup.normalizer_eq_top_iff.mpr (primeComplementCore_normal 3)]
  exact le_top

omit [Finite G] in
theorem isLinThreeFour_quotient {A K : Type} [Group A] [Group K] [Finite A] [Finite K]
    (hK : IsLinThreeFour K) (f : A →* K) (hf : Function.Surjective f)
    (hker : Nat.Coprime 3 (Nat.card f.ker)) :
    IsLinThreeFour (A ⧸ primeComplementCore (G := A) 3) := by
  obtain ⟨e⟩ := nonempty_quotient_primeComplementCore_mulEquiv Nat.prime_three f hf hker
  exact isLinThreeFour_of_equiv (e.trans ((QuotientGroup.quotientMulEquivOfEq
    (primeComplementCore_three_eq_bot_of_isLinThreeFour hK)).trans QuotientGroup.quotientBot)) hK

end L34FF

end CFSG.AGLEmbedding
