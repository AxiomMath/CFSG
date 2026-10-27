module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OrthogonalRank
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeCensus
public import CFSG.Quasithin.EmptyFaithful.S152XA5
public import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.LocalAnalysis.SectionRank.TwoGenerators

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.SectionRank.ClassicalEven CFSG.Assembly.LowTwoRank Matrix

theorem three_le_pRank_psu_two {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 4)
    (hn : 4 ≤ n) :
    3 ≤ Open.pRank 3 (⊤ : Subgroup (Open.StatedProj (Open.StatedSU n (2 ^ 1) K))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [hcard])
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hζq : ζ ^ (2 ^ 1 + 1) = 1 := by norm_num; exact hζ3
  have hq : 2 ^ 1 ≠ 0 := by norm_num
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  have h2 : 2 < n := by omega
  have h3 : 3 < n := by omega
  exact three_le_pRank_torus (ι := Fin n) (by norm_num) hζ (i₀ := ⟨0, h0⟩) (i₁ := ⟨1, h1⟩)
    (i₂ := ⟨2, h2⟩) (i₃ := ⟨3, h3⟩) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (by simp [Fin.ext_iff]) fun j => torusDiag_mem_SU hq (prod_torusVec ζ j _)
      (by rw [torusVec_pow, hζq, torusVec_one])

theorem two_le_pRank_of_gens {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {x y : G} (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : Commute x y)
    (hx1 : x ≠ 1) (hy1 : ∀ n : ℕ, x ^ n ≠ y) :
    2 ≤ Open.pRank p (⊤ : Subgroup G) :=
  CFSG.SectionRank.two_le_pRank_top_of_commute hx hy hxy hx1 hy1

theorem two_le_pRank_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] {H : Subgroup (GL ι K)} {p : ℕ} [hp : Fact p.Prime] {x y : GL ι K}
    (hxH : x ∈ H) (hyH : y ∈ H) (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : Commute x y)
    (hx1 : x ∉ Assembly.LowTwoRank.StatedScalars ι K)
    (hy1 : ∀ n : ℕ, ∀ c ∈ Assembly.LowTwoRank.StatedScalars ι K, x ^ n * c ≠ y) :
    2 ≤ Open.pRank p (⊤ : Subgroup (Assembly.LowTwoRank.StatedProj H)) := by
  let N := (Assembly.LowTwoRank.StatedScalars ι K).subgroupOf H
  let π : H →* Assembly.LowTwoRank.StatedProj H := QuotientGroup.mk' N
  have hpow : ∀ (a : GL ι K) (ha : a ∈ H), a ^ p = 1 → π ⟨a, ha⟩ ^ p = 1 := fun a ha h => by
    rw [← map_pow]
    have : (⟨a, ha⟩ : H) ^ p = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact h)
    rw [this, map_one]
  have hcomm : ∀ (a b : GL ι K) (ha : a ∈ H) (hb : b ∈ H), Commute a b →
      Commute (π ⟨a, ha⟩) (π ⟨b, hb⟩) := fun a b ha hb h =>
    Commute.map (show Commute (⟨a, ha⟩ : H) ⟨b, hb⟩ from Subtype.ext h.eq) π
  have hmem : ∀ u v : H, π u = π v → ((u : GL ι K)⁻¹ * v) ∈ Assembly.LowTwoRank.StatedScalars ι K := fun u v h => by
    change QuotientGroup.mk' N u = QuotientGroup.mk' N v at h
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at h
    simpa using h
  refine two_le_pRank_of_gens (hpow x hxH hx) (hpow y hyH hy) (hcomm _ _ _ _ hxy) (fun h => hx1 ?_)
    (fun n h => ?_)
  · have := hmem _ _ (h.trans (map_one π).symm)
    simpa using this
  · rw [← map_pow] at h
    have := hmem _ _ h
    simp only [SubgroupClass.coe_pow] at this
    exact hy1 n _ this (mul_inv_cancel_left _ _)

theorem two_le_pRank_three_of_rotGL {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] {H : Subgroup (GL ι K)} {e : Fin 2 ⊕ Fin 2 → ι} (he : Function.Injective e)
    (hH : ∀ k, rotGL (e (.inl k)) (e (.inr k)) ∈ H) :
    2 ≤ Open.pRank 3 (⊤ : Subgroup (Assembly.LowTwoRank.StatedProj H)) := by
  have hne : ∀ a b : Fin 2 ⊕ Fin 2, a ≠ b → e a ≠ e b := fun _ _ h => he.ne h
  exact two_le_pRank_statedProj (hH 0) (hH 1) (rotGL_pow_three _ _) (rotGL_pow_three _ _)
    (rotGL_commute (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
      (hne _ _ (by decide)))
    (fun hx => mul_scalar_ne (g := 1) (hne _ _ (by decide)) (one_mulVec _)
      (rotMatrix_mulVec_left _ _) hx (one_mul _))
    (fun n _ hc => mul_scalar_ne (hne _ _ (by decide))
      (rotGL_pow_mulVec_of_ne (hne _ _ (by decide)) (hne _ _ (by decide)) n)
      (rotMatrix_mulVec_left _ _) hc)

theorem psl_two_le_pRank_three {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 4 ≤ n) :
    2 ≤ Open.pRank 3 (⊤ : Subgroup (Open.StatedProj (Open.StatedSL n K))) :=
  two_le_pRank_three_of_rotGL ((Fin.castLE_injective hn).comp finSumFinEquiv.injective)
    fun _ => Subgroup.subset_closure (det_rotMatrix _ _)


section A5

open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.Quasithin.S152X

theorem a5_overgroup_false {Y : Type} [Group Y] [Finite Y] (e : Y ≃* alternatingGroup (Fin 5))
    (T J : Subgroup Y) (hT : IsSylowTwoOf T ⊤) (hNJ : Subgroup.normalizer (T : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer (T : Set Y))
    (hperf : ∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY : Nat.card Y = 60 := by rw [Nat.card_congr e.toEquiv]; exact card_A5G
  obtain ⟨T', rfl⟩ := exists_sylow_of_isSylowTwoOf_top hT
  have hTcard : Nat.card (T' : Subgroup Y) = 4 := by
    rw [Sylow.card_eq_multiplicity, hY]
    have h := factorization_sixty
    rw [card_A5G] at h
    rw [h]
    norm_num
  have hTindex : (T' : Subgroup Y).index = 15 := by
    have h := Subgroup.card_mul_index (T' : Subgroup Y)
    rw [hTcard, hY] at h
    omega
  have hodd : ¬ 2 ∣ (T' : Subgroup Y).index := by rw [hTindex]; norm_num
  have hker : IsPGroup 2 e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    exact IsPGroup.of_card (n := 0) (by rw [pow_zero]; exact Subgroup.card_bot)
  have hrel := relIndex_normalizer_of_surj e.toMonoidHom e.surjective hker T'.isPGroup' hodd
  have hle : (T' : Subgroup Y) ≤ Subgroup.normalizer ((T' : Subgroup Y) : Set Y) :=
    Subgroup.le_normalizer
  have h1 := Subgroup.relIndex_mul_index hle
  rw [hrel, hTindex] at h1
  have hNidx : (Subgroup.normalizer ((T' : Subgroup Y) : Set Y)).index = 5 := by omega
  have hNcard : Nat.card (Subgroup.normalizer ((T' : Subgroup Y) : Set Y)) = 12 := by
    have h := Subgroup.card_mul_index (Subgroup.normalizer ((T' : Subgroup Y) : Set Y))
    rw [hNidx, hY] at h
    omega
  have h12 : 12 ∣ Nat.card J := hNcard ▸ Subgroup.card_dvd_of_le hNJ
  have h60 : Nat.card J ∣ 60 := hY ▸ Subgroup.card_subgroup_dvd_card J
  obtain ⟨k, hk⟩ := h12
  rw [hk] at h60
  have hk5 : k ∣ 5 :=
    Nat.dvd_of_mul_dvd_mul_left (show 0 < 12 by norm_num) (by simpa using h60)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hk5 with rfl | rfl
  · apply hJ
    exact (Subgroup.eq_of_le_of_card_ge hNJ (by rw [hNcard, hk])).symm
  · have hJtop : J = ⊤ := Subgroup.eq_top_of_card_eq J (by rw [hk, hY])
    have hperfY : Group.IsPerfect Y := by
      have : Group.IsPerfect (alternatingGroup (Fin 5)) :=
        ⟨commutator_alternatingGroup_eq_top (by simp)⟩
      exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hc : ⁅(⊤ : Subgroup Y), ⊤⁆ = ⊤ := Group.isPerfect_def.mp hperfY
    have := hperf ⊤ (hJtop ▸ le_rfl) hc
    rw [Subgroup.card_top, hY] at this
    exact absurd this (by norm_num)

end A5

section Index

open CFSG.AGLEmbedding

theorem two_le_pRank_of_classicalIndexTwo {Y : Type} [Group Y] [Finite Y]
    (d : TauCeti.ValidLieTypeIndex) (hd : IsClassicalOrG2IndexTwo d.1)
    (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) : 2 ≤ Open.pRank 3 (⊤ : Subgroup Y) := by
  obtain ⟨d1, hv⟩ := d
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hdup := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).2
  simp only [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hdup
  cases d1 with
  | A r q =>
    simp only [IsClassicalOrG2IndexTwo] at hd
    obtain ⟨hp, hqe⟩ := primePower_card_two' hd
    have hr4 : 4 ≤ r := by
      by_contra hlt
      have h123 : r = 1 ∨ r = 2 ∨ r = 3 := by
        have := hrange.1
        omega
      rcases h123 with rfl | rfl | rfl
      · have := hrange.2 rfl
        omega
      · exact hdup (Or.inr (Or.inl ⟨rfl, hd⟩))
      · exact hdup (Or.inr (Or.inr ⟨rfl, hd⟩))
    have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    obtain ⟨-, K, _, _, -, ⟨e'⟩⟩ := h
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e']
    exact psl_two_le_pRank_three (by omega)
  | twistedA r q =>
    simp only [IsClassicalOrG2IndexTwo] at hd
    obtain ⟨hp, hqe⟩ := primePower_card_two' hd
    have hr3 : 3 ≤ r := by
      have h2 := hrange.1
      by_contra hlt
      have : r = 2 := by omega
      have := hrange.2 this
      omega
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    rw [hp, hqe] at h
    obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := h
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e']
    exact le_trans (by norm_num)
      (three_le_pRank_psu_two (K := K) (n := r + 1) (by rw [hK]; norm_num) (by omega))
  | B r q =>
    simp only [IsClassicalOrG2IndexTwo] at hd
    obtain ⟨hp, hqe⟩ := primePower_card_two' hd
    have hr3 : 3 ≤ r := by
      have h2 := hrange.1
      have h3 : r ≠ 2 := fun h => hrange.2 ⟨h, hd⟩
      omega
    exact two_le_pRank_three_typeB r hr3 q hp hqe hv e
  | D r q =>
    simp only [IsClassicalOrG2IndexTwo] at hd
    exact kFactOrthogonalTwoLieRank_proved Y ⟨.D r q, hv⟩ ⟨r, q, hd, Or.inl rfl⟩ ⟨e⟩
  | twistedD r q =>
    simp only [IsClassicalOrG2IndexTwo] at hd
    exact kFactOrthogonalTwoLieRank_proved Y ⟨.twistedD r q, hv⟩ ⟨r, q, hd, Or.inr (Or.inl rfl)⟩ ⟨e⟩
  | G2 q =>
    simp only [IsClassicalOrG2IndexTwo] at hd
    have := hrange
    omega
  | _ => exact hd.elim

end Index

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
