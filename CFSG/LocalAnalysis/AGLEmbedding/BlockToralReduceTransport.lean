module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase
public import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitParab

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect)

namespace ToralReduce

variable {Y : Type} [Group Y] {L : Subgroup Y} {K : Type} [Field K]

@[expose] def censusHom (φ : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL 3 K) :
    ↥L →* projectiveSL 3 K :=
  φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))

variable (φ : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL 3 K)

theorem censusHom_surjective : Function.Surjective (censusHom φ) :=
  φ.surjective.comp (QuotientGroup.mk'_surjective _)

theorem censusHom_eq_iff {a b : ↥L} : censusHom φ a = censusHom φ b ↔ a⁻¹ * b ∈
    Subgroup.center ↥L := by
  show φ (QuotientGroup.mk' _ a) = φ (QuotientGroup.mk' _ b) ↔ _
  rw [φ.injective.eq_iff, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]

theorem censusHom_eq_one_iff {a : ↥L} : censusHom φ a = 1 ↔ a ∈ Subgroup.center ↥L := by
  rw [← map_one (censusHom φ), censusHom_eq_iff]
  simp

theorem eq_of_censusHom_eq_of_pow {m : ℕ} (hm : Nat.Coprime m (Nat.card (Subgroup.center ↥L)))
    {a b : ↥L} (ha : a ^ m = 1) (hb : b ^ m = 1) (h : censusHom φ a = censusHom φ b) : a = b := by
  have hz := (censusHom_eq_iff φ).mp h
  have hcomm : Commute a (a⁻¹ * b) := Subgroup.mem_center_iff.mp hz a
  have hzm : (a⁻¹ * b) ^ m = 1 := by
    have h1 : b ^ m = a ^ m * (a⁻¹ * b) ^ m := by
      rw [← hcomm.mul_pow, mul_inv_cancel_left]
    rwa [ha, hb, one_mul, eq_comm] at h1
  have hz1 : (⟨a⁻¹ * b, hz⟩ : Subgroup.center ↥L) = 1 := by
    rw [← orderOf_eq_one_iff]
    refine Nat.eq_one_of_dvd_coprimes hm (orderOf_dvd_of_pow_eq_one ?_) (orderOf_dvd_natCard _)
    exact Subtype.ext hzm
  have := congrArg Subtype.val hz1
  simp only [OneMemClass.coe_one] at this
  exact (inv_mul_eq_one.mp this)

theorem eq_of_censusHom_eq_of_two (hodd : Odd (Nat.card (Subgroup.center ↥L))) {a b : ↥L}
    (ha : ∃ k : ℕ, a ^ 2 ^ k = 1) (hb : ∃ k : ℕ, b ^ 2 ^ k = 1)
    (h : censusHom φ a = censusHom φ b) : a = b := by
  obtain ⟨k, hk⟩ := ha
  obtain ⟨m, hm⟩ := hb
  refine eq_of_censusHom_eq_of_pow φ (m := 2 ^ (k + m))
    (Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)) ?_ ?_ h
  · rw [pow_add, pow_mul, hk, one_pow]
  · rw [pow_add, mul_comm, pow_mul, hm, one_pow]

theorem censusHom_mem_normalizer_iff (hodd : Odd (Nat.card (Subgroup.center ↥L)))
    {T : Subgroup Y} (hT : IsSylowTwoOf T L) (l : ↥L) :
    censusHom φ l ∈ Subgroup.normalizer
      (((T.subgroupOf L).map (censusHom φ) : Subgroup _) : Set (projectiveSL 3 K)) ↔
      (l : Y) ∈ Subgroup.normalizer (T : Set Y) := by
  have h2 : ∀ t ∈ T, ∃ k : ℕ, t ^ 2 ^ k = 1 := fun t ht => by
    obtain ⟨k, hk⟩ := hT.2.1 ⟨t, ht⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  constructor
  · have key : ∀ m : ↥L, censusHom φ m ∈ Subgroup.normalizer
        (((T.subgroupOf L).map (censusHom φ) : Subgroup _) : Set (projectiveSL 3 K)) →
        ∀ h ∈ T, (m : Y) * h * (m : Y)⁻¹ ∈ T := by
      intro m hm h hh
      have h1 := (Subgroup.mem_normalizer_iff.mp hm (censusHom φ ⟨h, hT.1 hh⟩)).mp ⟨_, hh, rfl⟩
      rw [← map_inv, ← map_mul, ← map_mul] at h1
      obtain ⟨t, ht, hte⟩ := h1
      obtain ⟨k, hk⟩ := h2 h hh
      have heq := eq_of_censusHom_eq_of_two φ hodd (a := t) (b := m * ⟨h, hT.1 hh⟩ * m⁻¹)
        (h2 _ ht |>.imp fun k hk => Subtype.ext (by simpa using hk))
        ⟨k, Subtype.ext (by simp [conj_pow, hk])⟩ hte
      have := congrArg Subtype.val heq
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      rw [← this]
      exact ht
    intro hl
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨key l hl h, fun hh => ?_⟩
    have := key l⁻¹ (by rw [map_inv]; exact Subgroup.inv_mem _ hl) _ hh
    simpa [mul_assoc] using this
  · have key : ∀ m : ↥L, (m : Y) ∈ Subgroup.normalizer (T : Set Y) →
        ∀ y ∈ (T.subgroupOf L).map (censusHom φ),
          censusHom φ m * y * (censusHom φ m)⁻¹ ∈ (T.subgroupOf L).map (censusHom φ) := by
      rintro m hm _ ⟨t, ht, rfl⟩
      refine ⟨m * t * m⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      show ((m * t * m⁻¹ : ↥L) : Y) ∈ T
      simpa using (Subgroup.mem_normalizer_iff.mp hm t).mp ht
    intro hl
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key l hl y, fun hy => ?_⟩
    have := key l⁻¹ (by simpa using Subgroup.inv_mem _ hl) _ hy
    simpa [mul_assoc] using this

theorem center_le_of_isParabolicTwo {J : Subgroup Y} (hP : IsParabolicTwo L J) {z : ↥L}
    (hz : z ∈ Subgroup.center ↥L) : (z : Y) ∈ J := by
  obtain ⟨-, T, hT, hTJ⟩ := hP
  refine hTJ ⟨z.2, Subgroup.mem_normalizer_iff.mpr fun h => ?_⟩
  by_cases hh : h ∈ L
  · have hc := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨h, hh⟩)
    simp only [Subgroup.coe_mul] at hc
    rw [← hc, mul_inv_cancel_right]
  · constructor
    · intro ht
      exact absurd (hT.1 ht) hh
    · intro ht
      have := L.mul_mem (L.mul_mem (L.inv_mem z.2) (hT.1 ht)) z.2
      rw [show (z : Y)⁻¹ * (z * h * (z : Y)⁻¹) * z = h by group] at this
      exact absurd this hh

theorem censusHom_mem_map_iff {J : Subgroup Y} (hP : IsParabolicTwo L J) {l : ↥L} :
    censusHom φ l ∈ (J.subgroupOf L).map (censusHom φ) ↔ (l : Y) ∈ J := by
  refine ⟨fun ⟨j, hj, hjl⟩ => ?_, fun hl => ⟨l, hl, rfl⟩⟩
  have hz := center_le_of_isParabolicTwo hP ((censusHom_eq_iff φ).mp hjl)
  have := J.mul_mem (show (j : Y) ∈ J from hj) hz
  simpa using this

theorem exists_eq_map_conj_projStabilizer [Finite Y] [Finite K] [CharP K 2] {J : Subgroup Y}
    (hCP : CompParab L J) : ∃ (g : projectiveSL 3 K) (d : ℕ), (d = 1 ∨ d = 2) ∧
      (J.subgroupOf L).map (censusHom φ) =
        (projStabilizer (flagSpace 3 K d)).map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hTJ⟩ := hCP.parab.2
  have hT2 : IsPGroup 2 ((T.subgroupOf L).map (censusHom φ)) :=
    (hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm).map _
  have hidx : ¬ 2 ∣ ((T.subgroupOf L).map (censusHom φ)).index := fun h =>
    hT.2.2 (h.trans (Subgroup.index_map_dvd _ (censusHom_surjective φ)))
  let Tsyl : Sylow 2 (projectiveSL 3 K) := hT2.toSylow hidx
  have hnorm := censusHom_mem_normalizer_iff φ hCP.odd hT
  refine LinearThreeKit.eq_map_conj_projStabilizer_of_sylow 2 Tsyl _ ?_ ?_ ?_
  · intro y hy
    obtain ⟨l, rfl⟩ := censusHom_surjective φ y
    exact ⟨l, hTJ ⟨l.2, (hnorm l).mp hy⟩, rfl⟩
  · intro heq
    apply hCP.ne_borel T hT
    ext l
    constructor
    · intro hl
      have h1 : censusHom φ ⟨l, hCP.parab.1 hl⟩ ∈ (J.subgroupOf L).map (censusHom φ) :=
        ⟨_, hl, rfl⟩
      rw [heq] at h1
      exact ⟨hCP.parab.1 hl, (hnorm _).mp h1⟩
    · rintro ⟨hlL, hlN⟩
      have h1 : censusHom φ ⟨l, hlL⟩ ∈ Subgroup.normalizer
          ((Tsyl : Subgroup (projectiveSL 3 K)) : Set (projectiveSL 3 K)) :=
        (hnorm ⟨l, hlL⟩).mpr hlN
      rw [← heq, censusHom_mem_map_iff φ hCP.parab] at h1
      exact h1
  · intro htop
    apply hCP.ne_top
    refine le_antisymm hCP.parab.1 fun l hl => ?_
    have h1 : censusHom φ ⟨l, hl⟩ ∈ (J.subgroupOf L).map (censusHom φ) := htop ▸ Subgroup.mem_top _
    exact (censusHom_mem_map_iff φ hCP.parab).mp h1

end ToralReduce

end CFSG.AGLEmbedding
