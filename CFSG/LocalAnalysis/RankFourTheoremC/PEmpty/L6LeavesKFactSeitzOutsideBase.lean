module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactSeitzOutsideDefs
public import CFSG.LieType.SeitzGeneration.HyperLeaf
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LargeExtraspecial.S45QSylow
public import CFSG.LieType.SeitzGeneration.Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KSeitz

open CFSG.Open Subgroup
open CFSG.LieType.SeitzGeneration (HyperGen Cat)
open CFSG.AGLEmbeddingD2 (KFactSeitzRankTwo IsD2SeitzException)

theorem zpowers_hyperplane {G : Type*} [Group G] {f : ℕ} (hf : f.Prime) {E : Subgroup G}
    (hE : IsElemAbelian f E) (hc : Nat.card E = f ^ 2) {a : G} (ha : a ∈ E) (ha1 : a ≠ 1) :
    Subgroup.zpowers a ≤ E ∧ (Subgroup.zpowers a).relIndex E = f := by
  haveI : Fact f.Prime := ⟨hf⟩
  have hle : Subgroup.zpowers a ≤ E := Subgroup.zpowers_le.mpr ha
  have ho : orderOf a = f := orderOf_eq_prime (hE.2 a ha) ha1
  refine ⟨hle, ?_⟩
  have h := Subgroup.relIndex_mul_card (H := Subgroup.zpowers a) (K := E)
  rw [inf_eq_left.mpr hle, Nat.card_zpowers, ho, hc] at h
  exact Nat.eq_of_mul_eq_mul_right hf.pos (by rw [h]; ring)

theorem mem_hset_of_commute {G : Type*} [Group G] {f : ℕ} (hf : f.Prime) {E : Subgroup G}
    (hE : IsElemAbelian f E) (hc : Nat.card E = f ^ 2) {a : G} (ha : a ∈ E) (ha1 : a ≠ 1)
    {k : G} (hk : a * k = k * a) : k ∈ hset f E := by
  obtain ⟨hle, hrel⟩ := zpowers_hyperplane hf hE hc ha ha1
  refine mem_hset hle hrel fun y hy => ?_
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (Commute.zpow_left (show Commute a k from hk) n).eq

theorem hyperGen_of_closure_hset {A : Type*} [Group A] {K E : Subgroup A} {f : ℕ}
    (hEK : E ≤ K) (h : Subgroup.closure (hset f (E.subgroupOf K)) = ⊤) : HyperGen f K E := by
  intro k hk
  have hk' : (⟨k, hk⟩ : ↥K) ∈ Subgroup.closure (hset f (E.subgroupOf K)) :=
    h ▸ Subgroup.mem_top _
  have hE : (E.subgroupOf K).map K.subtype = E := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hEK]
  have hle : Subgroup.closure (hset f (E.subgroupOf K)) ≤
      (Subgroup.closure {k : A | k ∈ K ∧ ∃ F : Subgroup A, F ≤ E ∧ F.relIndex E = f ∧
        ∀ y ∈ F, y * k = k * y}).comap K.subtype := by
    rw [Subgroup.closure_le]
    rintro k₀ ⟨F, hFE, hrel, hcomm⟩
    apply Subgroup.subset_closure
    refine ⟨k₀.2, F.map K.subtype, ?_, ?_, ?_⟩
    · rw [← hE]
      exact Subgroup.map_mono hFE
    · rw [← Subgroup.relIndex_map_map_of_injective F (E.subgroupOf K) K.subtype_injective, hE]
        at hrel
      exact hrel
    · rintro _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (hcomm y hy)
  exact hle hk'

theorem card_subgroupOf {A : Type*} [Group A] {K E : Subgroup A} (hEK : E ≤ K) :
    Nat.card (E.subgroupOf K) = Nat.card E :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv

theorem closure_hset_eq_top_of_seitz (hS : KFactSeitzRankTwo) {G : Type*} [Group G]
    (d : TauCeti.ValidLieTypeIndex) (e : G ≃* Cat d) (hZ : Subgroup.center G = ⊥) {f : ℕ}
    (hf : f.Prime) (hf2 : f ≠ 2) (hpd : f ≠ d.1.characteristic)
    (hex : ¬ IsD2SeitzException f d.1) {E : Subgroup G} (hE : IsElemAbelian f E)
    (hc : Nat.card E = f ^ 2) : Subgroup.closure (hset f E) = ⊤ := by
  let ψ : G →* MulAut (Cat d) :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conj : G →* MulAut G)
  have hfix : ∀ (a k : G), ψ a (e k) = e k ↔ a * k * a⁻¹ = k := by
    intro a k
    have h1 : ψ a (e k) = e (a * k * a⁻¹) := by
      simp [ψ, MulAut.congr_apply]
    rw [h1, e.apply_eq_iff_eq]
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxc : x ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro k
      have h1 : ψ x (e k) = e k := by rw [hx]; rfl
      have h2 := (hfix x k).mp h1
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    rw [hZ] at hxc
    exact Subgroup.mem_bot.mp hxc
  have hclos := hS d f hf hf2 hpd hex (E.map ψ) (hE.map ψ)
    (by rw [Subgroup.card_map_of_injective hψ, hc])
  have hgen : Subgroup.closure {k : G | ∃ a ∈ E, a ≠ 1 ∧ a * k * a⁻¹ = k} = ⊤ := by
    rw [eq_top_iff]
    intro k _
    have hk : e k ∈ Subgroup.closure
        {k : Cat d | ∃ ε ∈ E.map ψ, ε ≠ 1 ∧ ε k = k} := by
      rw [hclos]
      exact Subgroup.mem_top _
    have hle : Subgroup.closure
        {k : Cat d | ∃ ε ∈ E.map ψ, ε ≠ 1 ∧ ε k = k} ≤
        (Subgroup.closure {k : G | ∃ a ∈ E, a ≠ 1 ∧ a * k * a⁻¹ = k}).map e.toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro t ⟨_, ⟨a, haE, rfl⟩, hε1, hεt⟩
      refine ⟨e.symm t, Subgroup.subset_closure ⟨a, haE, ?_, ?_⟩, by simp⟩
      · rintro rfl
        exact hε1 (map_one ψ)
      · refine (hfix a (e.symm t)).mp ?_
        simpa using hεt
    obtain ⟨y, hy, hyk⟩ := hle hk
    exact (e.injective hyk) ▸ hy
  have hsub : {k : G | ∃ a ∈ E, a ≠ 1 ∧ a * k * a⁻¹ = k} ⊆ hset f E := by
    rintro k ⟨a, haE, ha1, hak⟩
    exact mem_hset_of_commute hf hE hc haE ha1 (mul_inv_eq_iff_eq_mul.mp hak)
  exact eq_top_iff.mpr (hgen ▸ Subgroup.closure_mono hsub)

theorem hyperGen_of_seitz (hS : KFactSeitzRankTwo) {A : Type*} [Group A] {K E : Subgroup A}
    (d : TauCeti.ValidLieTypeIndex) (e : ↥K ≃* Cat d) (hZ : Subgroup.center ↥K = ⊥) {f : ℕ}
    (hf : f.Prime) (hf2 : f ≠ 2) (hpd : f ≠ d.1.characteristic)
    (hex : ¬ IsD2SeitzException f d.1) (hEK : E ≤ K) (hE : IsElemAbelian f E)
    (hc : Nat.card E = f ^ 2) : HyperGen f K E :=
  hyperGen_of_closure_hset hEK (closure_hset_eq_top_of_seitz hS d e hZ hf hf2 hpd hex
    (hE.subgroupOf K) (by rw [card_subgroupOf hEK]; exact hc))

theorem exists_overgroup_of_holds {G : Type*} [Group G] (hBT : CFSG.LieType.BorelTits.Holds G 2)
    {E U : Subgroup G} (hU : IsPGroup 2 U) (hU0 : U ≠ ⊥)
    (hEU : E ≤ Subgroup.normalizer (U : Set G)) :
    ∃ (S : Sylow 2 G) (P : Subgroup G), P ≠ ⊤ ∧ E ≤ P ∧ (S : Subgroup G) ≤ P := by
  obtain ⟨S, P, hP, hN, -, -, hS⟩ := hBT U hU0 hU
  exact ⟨S, P, hP, hEU.trans hN, Subgroup.le_normalizer.trans hS⟩

theorem subgroupOf_le_normalizer {A : Type*} [Group A] {K E U : Subgroup A} (hUK : U ≤ K)
    (hEU : E ≤ Subgroup.normalizer (U : Set A)) :
    E.subgroupOf K ≤ Subgroup.normalizer ((U.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
  intro x hx
  rw [← Subgroup.subgroupOf_normalizer_eq hUK]
  exact hEU hx

theorem subgroupOf_ne_bot {A : Type*} [Group A] {K U : Subgroup A} (hUK : U ≤ K) (hU0 : U ≠ ⊥) :
    U.subgroupOf K ≠ ⊥ := by
  intro hbot
  apply hU0
  have hmap := Subgroup.subgroupOf_map_subtype U K
  rw [hbot, Subgroup.map_bot, inf_eq_left.mpr hUK] at hmap
  exact hmap.symm

theorem card_mem_of_overgroups {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    (φ : G ≃* G')
    (S₀ : Sylow 2 G') (L : Set ℕ)
    (hL : ∀ X : Subgroup G', (S₀ : Subgroup G') ≤ X → X = ⊤ ∨ Nat.card X ∈ L)
    (S : Sylow 2 G) {P : Subgroup G} (hP : P ≠ ⊤) (hSP : (S : Subgroup G) ≤ P) :
    Nat.card P ∈ L := by
  have hsurj : Function.Surjective φ.toMonoidHom := φ.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G' (Sylow.mapSurjective hsurj S) S₀
  set X : Subgroup G' := (P.map φ.toMonoidHom).map (MulAut.conj g).toMonoidHom with hX
  have hS₀X : (S₀ : Subgroup G') ≤ X := by
    have h1 : ((g • Sylow.mapSurjective hsurj S : Sylow 2 G') : Subgroup G') = S₀ := by
      rw [hg]
    rw [Sylow.coe_subgroup_smul, Sylow.coe_mapSurjective] at h1
    rw [← h1]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hx
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨φ z, ⟨z, hSP hz, rfl⟩, rfl⟩
  have hXtop : X ≠ ⊤ := by
    intro htop
    apply hP
    have h1 : (X.map (MulAut.conj g).symm.toMonoidHom) = ⊤ := by
      rw [htop]
      exact Subgroup.map_top_of_surjective _ (MulAut.conj g).symm.surjective
    rw [hX, Subgroup.map_map] at h1
    have h2 : (MulAut.conj g).symm.toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id G' := by ext x; simp
    rw [h2, Subgroup.map_id] at h1
    have h3 : (P.map φ.toMonoidHom).map φ.symm.toMonoidHom = ⊤ := by
      rw [h1]
      exact Subgroup.map_top_of_surjective _ φ.symm.surjective
    rw [Subgroup.map_map] at h3
    have h4 : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id G := by ext x; simp
    rwa [h4, Subgroup.map_id] at h3
  have hcard : Nat.card X = Nat.card P := by
    rw [hX, Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective φ.injective]
  rcases hL X hS₀X with h | h
  · exact absurd h hXtop
  · rwa [hcard] at h

theorem not_sq_dvd_two_pow_mul {f a q : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) (hq : q = 1 ∨ q.Prime) :
    ¬ f ^ 2 ∣ 2 ^ a * q := by
  intro h
  have hcop : Nat.Coprime (f ^ 2) (2 ^ a) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hf Nat.prime_two).mpr hf2)
  have hdq : f ^ 2 ∣ q := hcop.dvd_of_dvd_mul_left h
  rcases hq with rfl | hq
  · have := Nat.le_of_dvd Nat.one_pos hdq
    nlinarith [hf.two_le]
  · rcases (Nat.dvd_prime hq).mp hdq with h1 | h1
    · nlinarith [hf.two_le]
    · have hfq : f ∣ q := h1 ▸ dvd_pow_self f two_ne_zero
      have : f = q := (Nat.prime_dvd_prime_iff_eq hf hq).mp hfq
      subst this
      nlinarith [hf.two_le]

theorem false_of_card_three_sixty {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : Nat.card G = 360) (S : Sylow 2 G) {E P : Subgroup G} (hE : Nat.card E = 9)
    (hP : P ≠ ⊤) (hEP : E ≤ P) (hSP : (S : Subgroup G) ≤ P) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : Nat.card (S : Subgroup G) = 8 := by
    rw [Sylow.card_eq_multiplicity, hG, Nat.factorization_def _ Nat.prime_two]
    have : padicValNat 2 360 = 3 := by
      rw [show (360 : ℕ) = 2 ^ 3 * 45 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
        padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
    rw [this]
    norm_num
  have h72 : 72 ∣ Nat.card P := by
    have h8 : 8 ∣ Nat.card P := hS ▸ Subgroup.card_dvd_of_le hSP
    have h9 : 9 ∣ Nat.card P := hE ▸ Subgroup.card_dvd_of_le hEP
    exact (show Nat.Coprime 8 9 by norm_num).mul_dvd_of_dvd_of_dvd h8 h9
  obtain ⟨m, hm⟩ := h72
  have hidx := Subgroup.card_mul_index P
  rw [hm, hG] at hidx
  have hmi : m * P.index = 5 := by
    have h' : 72 * (m * P.index) = 360 := by rw [← mul_assoc]; exact hidx
    omega
  rcases (Nat.dvd_prime Nat.prime_five).mp (Dvd.intro_left m hmi) with h1 | h5
  · exact hP (Subgroup.index_eq_one.mp h1)
  · have := CFSG.LargeExtraspecial.S45Q.card_dvd_factorial_index hP
    rw [h5, hG] at this
    norm_num [Nat.factorial] at this

theorem not_sq_dvd_sixty {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) : ¬ f ^ 2 ∣ 60 := by
  intro h
  have hle : f ≤ 7 := by nlinarith [Nat.le_of_dvd (by norm_num) h]
  interval_cases f <;> first | omega | (exfalso; norm_num at hf) | (exfalso; norm_num at h)

theorem not_sq_dvd_168 {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) : ¬ f ^ 2 ∣ 168 := by
  intro h
  have hle : f ≤ 13 := by nlinarith [Nat.le_of_dvd (by norm_num) h]
  interval_cases f <;> first | omega | (exfalso; norm_num at hf) | (exfalso; norm_num at h)

theorem eq_three_of_sq_dvd_360 {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) (h : f ^ 2 ∣ 360) :
    f = 3 := by
  have hle : f ≤ 18 := by nlinarith [Nat.le_of_dvd (by norm_num) h]
  interval_cases f <;> first | omega | (exfalso; norm_num at hf) | (exfalso; norm_num at h)

theorem eq_three_of_sq_dvd_20160 {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) (h : f ^ 2 ∣ 20160) :
    f = 3 := by
  have hle : f ≤ 141 := by nlinarith [Nat.le_of_dvd (by norm_num) h]
  interval_cases f <;> first | omega | (exfalso; norm_num at hf) | (exfalso; norm_num at h)

theorem center_eq_bot_of_simple {K : Type*} [Group K] [Finite K] [IsSimpleGroup K] {f : ℕ}
    (hf : f.Prime) (hf2 : f ≠ 2) {E U : Subgroup K} (hc : Nat.card E = f ^ 2)
    (hU : IsPGroup 2 U) (hU0 : U ≠ ⊥) : Subgroup.center K = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · exact h
  · exfalso
    have hnormal : ∀ H : Subgroup K, H.Normal := fun H => ⟨fun n hn g => by
      have hg : g ∈ Subgroup.center K := h ▸ Subgroup.mem_top g
      have hgn : g * n = n * g := (Subgroup.mem_center_iff.mp hg n).symm
      rw [hgn, mul_inv_cancel_right]
      exact hn⟩
    have hUtop : U = ⊤ := by
      haveI := hnormal U
      exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal U).resolve_left hU0
    have hE0 : E ≠ ⊥ := by
      rintro rfl
      rw [Subgroup.card_bot] at hc
      nlinarith [hf.two_le]
    have hEtop : E = ⊤ := by
      haveI := hnormal E
      exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal E).resolve_left hE0
    obtain ⟨n, hn⟩ := hU.exists_card_eq
    have hEU : Nat.card E = Nat.card U := by rw [hEtop, hUtop]
    rw [hc, hn] at hEU
    have hn0 : n ≠ 0 := by
      rintro rfl
      nlinarith [hf.two_le]
    have h2 : 2 ∣ f ^ 2 := by
      rw [hEU]
      exact dvd_pow_self 2 hn0
    exact hf2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hf).mp
      (Nat.prime_two.dvd_of_dvd_pow h2)).symm

end KSeitz

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
