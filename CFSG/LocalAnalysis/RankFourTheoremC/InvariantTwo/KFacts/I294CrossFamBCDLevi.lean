module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamTransfer

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup

section Conjugacy

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

theorem exists_conj_mem_of_pow_eq_one {A : Subgroup G} (hA : ¬ p ∣ A.index) {y : G}
    (hy : y ^ p = 1) : ∃ g : G, g * y * g⁻¹ ∈ A := by
  have hzp : IsPGroup p (Subgroup.zpowers y) := by
    intro z
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 z.2
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, OneMemClass.coe_one, SubgroupClass.coe_pow]
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  obtain ⟨P, hP⟩ := hzp.exists_le_sylow
  have hyP : y ∈ (P : Subgroup G) := hP (Subgroup.mem_zpowers y)
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow p A))
  have hT' : IsPGroup p ((T : Subgroup A).map A.subtype) := T.isPGroup'.map A.subtype
  have hidx : ¬ p ∣ ((T : Subgroup A).map A.subtype).index := by
    rw [Subgroup.index_map_subtype]
    exact Nat.Prime.not_dvd_mul hp.out T.not_dvd_index hA
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (hT'.toSylow hidx) P
  have hS : (P : Subgroup G) =
      ((T : Subgroup A).map A.subtype).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  rw [hS] at hyP
  obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.1 hyP
  obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.1 ht
  refine ⟨g⁻¹, ?_⟩
  have : g⁻¹ * y * g⁻¹⁻¹ = (a : G) := by
    rw [← hty]
    simp [MulAut.conj_apply, mul_assoc]
  rw [this]
  exact a.2

theorem isMulCommutative_of_isPGroup_of_not_dvd_index' {A : Subgroup G} (hA : ¬ p ∣ A.index)
    (hAab : ∀ P : Subgroup A, IsPGroup p P → IsMulCommutative P) {P : Subgroup G}
    (hP : IsPGroup p P) : IsMulCommutative P := by
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow p A))
  have hT' : IsPGroup p ((T : Subgroup A).map A.subtype) := T.isPGroup'.map A.subtype
  have hidx : ¬ p ∣ ((T : Subgroup A).map A.subtype).index := by
    rw [Subgroup.index_map_subtype]
    exact Nat.Prime.not_dvd_mul hp.out T.not_dvd_index hA
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (hT'.toSylow hidx) S
  have hS : (S : Subgroup G) =
      ((T : Subgroup A).map A.subtype).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  haveI : IsMulCommutative (T : Subgroup A) := hAab _ T.isPGroup'
  have : IsMulCommutative (S : Subgroup G) := by
    rw [hS]
    infer_instance
  exact isMulCommutative_anti hPS

end Conjugacy

section Levi

variable {M G : Type*} [Group M] [Finite M] [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
  {ι : M →* G}

theorem isMulCommutative_of_isPGroup_of_levi (hι : Function.Injective ι)
    (hidx : ¬ p ∣ ι.range.index)
    (hM : ∀ P : Subgroup M, IsPGroup p P → IsMulCommutative P) {P : Subgroup G}
    (hP : IsPGroup p P) : IsMulCommutative P := by
  refine isMulCommutative_of_isPGroup_of_not_dvd_index' hidx (fun Q hQ => ?_) hP
  let e : M ≃* ι.range := MonoidHom.ofInjective hι
  have h1 : IsPGroup p (Q.map e.symm.toMonoidHom) := hQ.map _
  exact isMulCommutative_of_map_injective e.symm.toMonoidHom e.symm.injective (hM _ h1)

theorem le_pRank_centralizer_of_levi (hι : Function.Injective ι) (hidx : ¬ p ∣ ι.range.index)
    {c : ℕ} (hc : ∀ y₀ : M, y₀ ^ p = 1 →
      c ≤ CFSG.Open.pRank p (centralizer ({y₀} : Set M))) {y : G} (hy : y ^ p = 1) :
    c ≤ CFSG.Open.pRank p (centralizer ({y} : Set G)) := by
  have hp1 : 1 < p := hp.out.one_lt
  obtain ⟨g, y₁, hy₁⟩ := exists_conj_mem_of_pow_eq_one hidx hy
  have hy₁p : y₁ ^ p = 1 := by
    apply hι
    rw [map_pow, hy₁, map_one]
    have : (g * y * g⁻¹) ^ p = g * y ^ p * g⁻¹ := by
      simp [conj_pow]
    rw [this, hy]
    simp
  have h1 : CFSG.Open.pRank p (centralizer ({y₁} : Set M)) ≤
      CFSG.Open.pRank p (centralizer ({ι y₁} : Set G)) := by
    refine (CFSG.SectionRank.pRank_le_map hp1 ι hι _).trans
      (CFSG.SectionRank.pRank_mono hp1 ?_)
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [← map_mul, ← map_mul, hx]
  have h2 : CFSG.Open.pRank p (centralizer ({g * y * g⁻¹} : Set G)) ≤
      CFSG.Open.pRank p (centralizer ({y} : Set G)) :=
    pRank_centralizer_of_mulEquiv (MulAut.conj g) y
  rw [← hy₁] at h2
  exact (hc y₁ hy₁p).trans (h1.trans h2)

end Levi

section Quotient

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [hp : Fact p.Prime]

theorem isMulCommutative_sylow_quotient (N : Subgroup H) [N.Normal]
    (hH : ∀ P : Subgroup H, IsPGroup p P → IsMulCommutative P) (R : Sylow p (H ⧸ N)) :
    IsMulCommutative (R : Subgroup (H ⧸ N)) := by
  obtain ⟨S, rfl⟩ := Sylow.mapSurjective_surjective (f := QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective _) p R
  rw [Sylow.coe_mapSurjective]
  haveI := hH (S : Subgroup H) S.isPGroup'
  infer_instance

end Quotient

section CrossLevi

variable {H M : Type} [Group H] [Finite H] [Group M] [Finite M] {p d : ℕ} [hp : Fact p.Prime]

theorem crossAt_of_levi (hp5 : 5 ≤ p) (N : Subgroup H) [N.Normal] (hN : ¬ p ∣ Nat.card N)
    (ι : M →* H) (hι : Function.Injective ι) (hidx : ¬ p ∣ ι.range.index)
    (hsmall : d < p → ∀ P : Subgroup M, IsPGroup p P → IsMulCommutative P)
    (hrank : d ≤ CFSG.Open.pRank p (⊤ : Subgroup M))
    (hbig : p ≤ d → ∀ y₀ : M, y₀ ^ p = 1 →
      3 ≤ CFSG.Open.pRank p (centralizer ({y₀} : Set M))) :
    (CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ N)) = 2 →
      ∀ R : Sylow p (H ⧸ N), IsMulCommutative (R : Subgroup (H ⧸ N))) ∧
    (3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ N)) → ∀ y : H ⧸ N, y ^ p = 1 →
      3 ≤ CFSG.Open.pRank p (centralizer ({y} : Set (H ⧸ N)))) := by
  have hp1 : 1 < p := hp.out.one_lt
  have hHL : CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ N)) = CFSG.Open.pRank p (⊤ : Subgroup H) :=
    CFSG.SectionRank.pRank_quotient_eq N hN
  have hMH : CFSG.Open.pRank p (⊤ : Subgroup M) ≤ CFSG.Open.pRank p (⊤ : Subgroup H) :=
    CFSG.SectionRank.pRank_top_le_of_injective hp1 ι hι
  constructor
  · intro h2 R
    by_cases hd : d < p
    · exact isMulCommutative_sylow_quotient N
        (fun P hP => isMulCommutative_of_isPGroup_of_levi hι hidx (hsmall hd) hP) R
    · exfalso
      have := not_lt.1 hd
      omega
  · intro h3 y hy
    by_cases hd : d < p
    · exact three_le_pRank_centralizer_of_sylow_abelian
        (fun R => isMulCommutative_sylow_quotient N
          (fun P hP => isMulCommutative_of_isPGroup_of_levi hι hidx (hsmall hd) hP) R) h3 hy
    · obtain ⟨z, hzp, rfl⟩ := exists_pow_eq_one_lift N hN y hy
      have h3H : 3 ≤ CFSG.Open.pRank p (centralizer ({z} : Set H)) :=
        le_pRank_centralizer_of_levi hι hidx (hbig (not_lt.1 hd)) hzp
      obtain ⟨E, hEle, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp1
        (centralizer ({z} : Set H))
      have hFy : ∀ f ∈ E, f * z = z * f := fun f hf => by
        have := hEle hf
        rwa [Subgroup.mem_centralizer_singleton_iff] at this
      have := le_pRank_centralizer_quotient N hN hE hEcard hFy
      omega

end CrossLevi

section Transport

variable {L L' : Type*} [Group L] [Finite L] [Group L'] [Finite L'] {p : ℕ} [hp : Fact p.Prime]

theorem cross_transport (e' : L ≃* L')
    (h : (CFSG.Open.pRank p (⊤ : Subgroup L') = 2 →
        ∀ R : Sylow p L', IsMulCommutative (R : Subgroup L')) ∧
      (3 ≤ CFSG.Open.pRank p (⊤ : Subgroup L') → ∀ y : L', y ^ p = 1 →
        3 ≤ CFSG.Open.pRank p (centralizer ({y} : Set L')))) :
    (CFSG.Open.pRank p (⊤ : Subgroup L) = 2 →
        ∀ P : Sylow p L, IsMulCommutative (P : Subgroup L)) ∧
      (3 ≤ CFSG.Open.pRank p (⊤ : Subgroup L) → ∀ y : L, y ^ p = 1 →
        3 ≤ CFSG.Open.pRank p (centralizer ({y} : Set L))) := by
  have hp1 : 1 < p := hp.out.one_lt
  have hrk : CFSG.Open.pRank p (⊤ : Subgroup L) = CFSG.Open.pRank p (⊤ : Subgroup L') :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 e'
  refine ⟨fun h2 P => ?_, fun h3 y hy => ?_⟩
  · exact isMulCommutative_sylow_of_mulEquiv e' (fun R => h.1 (hrk ▸ h2) R) P
  · have hyp : (e' y) ^ p = 1 := by rw [← map_pow, hy, map_one]
    exact (h.2 (hrk ▸ h3) (e' y) hyp).trans (pRank_centralizer_of_mulEquiv e' y)

end Transport

end CFSG.LocalAnalysis.RankFourTheoremC
