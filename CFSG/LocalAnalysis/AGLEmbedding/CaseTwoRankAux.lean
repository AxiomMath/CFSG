module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.AGLEmbedding.CentralAlphaAux
public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedEscapeAux
public import CFSG.LocalAnalysis.AGLEmbedding.RankOneAutomizer
public import CFSG.LocalAnalysis.AGLEmbedding.ReducedOrbitsAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

section Elementary

variable {G : Type*} [Group G]

theorem isElemAbelian_of_le_of_isElemAbelian {p : ℕ} {E F : Subgroup G}
    (hE : IsElemAbelian p E) (hFE : F ≤ E) : IsElemAbelian p F :=
  CFSG.Open.IsElemAbelian.mono hE hFE

theorem card_le_of_isElemAbelian_of_isCyclic_sylow {K : Type*} [Group K] [Finite K] {p : ℕ}
    [Fact p.Prime] (T : Sylow p K) (hT : IsCyclic (T : Subgroup K)) {A : Subgroup K}
    (hA : IsElemAbelian p A) : Nat.card A ≤ p := by
  have hAp : IsPGroup p A := fun y => ⟨1, Subtype.ext (by simpa using hA.2 y y.2)⟩
  obtain ⟨T', hAT'⟩ := hAp.exists_le_sylow
  have : IsCyclic (T' : Subgroup K) :=
    isCyclic_of_surjective (Sylow.equiv T T') (MulEquiv.surjective _)
  have : IsCyclic A := Subgroup.isCyclic_of_le hAT'
  exact card_le_of_isCyclic_of_forall_pow_eq_one (Fact.out : p.Prime).pos fun a =>
    Subtype.ext (by simpa using hA.2 a a.2)

theorem card_mul_card_of_isCompl (hG : IsMulCommutative G) {I C : Subgroup G}
    (h : IsCompl I C) : Nat.card I * Nat.card C = Nat.card G := by
  have : I.Normal := ⟨fun n hn g => by
    rwa [(isMulCommutative_iff.mp hG) g n, mul_inv_cancel_right]⟩
  have h₁ := Subgroup.relIndex_sup_left C I
  rw [h.sup_eq_top, Subgroup.relIndex_top_right, Subgroup.relIndex,
    Subgroup.subgroupOf_eq_bot.mpr h.disjoint, Subgroup.index_bot] at h₁
  rw [← Subgroup.card_mul_index I, h₁]

end Elementary

section Aut

theorem pRank_mulAut_le_two_of_kOutRankLeOne {K : Type} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hZ : Subgroup.center K = ⊥)
    (hK : ∀ A : Subgroup K, IsElemAbelian p A → Nat.card A ≤ p) (hOut : KOutRankLeOne p K) :
    Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra! h3
  obtain ⟨E, -, hE, hEcard⟩ := pRank_attained p hp (⊤ : Subgroup (MulAut K))
  set Inn : Subgroup (MulAut K) := (MulAut.conj : K →* MulAut K).range with hInn
  have : IsElementaryAbelian p E :=
    { toIsMulCommutative := hE.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (by simpa using hE.2 g g.2) }
  obtain ⟨C, hC⟩ := IsElementaryAbelian.exists_isCompl p E (Inn.subgroupOf E)
  have hcard := card_mul_card_of_isCompl hE.1 hC
  have hI : Nat.card (Inn.subgroupOf E) ≤ p := by
    have hinj := mulAut_conj_injective hZ
    have hJ : IsElemAbelian p (E.comap (MulAut.conj : K →* MulAut K)) := by
      refine ⟨isMulCommutative_iff.mpr fun a b => Subtype.ext (hinj ?_), fun x hx => hinj ?_⟩
      · have : IsMulCommutative E := hE.1
        simpa only [Subgroup.coe_mul, map_mul] using
          setLike_mul_comm (show MulAut.conj (a : K) ∈ E from a.2)
            (show MulAut.conj (b : K) ∈ E from b.2)
      · rw [map_pow, map_one]
        exact hE.2 _ hx
    have hJcard : Nat.card (E.comap (MulAut.conj : K →* MulAut K)) =
        Nat.card (Inn.subgroupOf E) := by
      rw [← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq,
        ← Subgroup.card_map_of_injective E.subtype_injective, Subgroup.subgroupOf_map_subtype]
    exact hJcard ▸ hK _ hJ
  have hCp : Nat.card C ≤ p := by
    rw [← Subgroup.card_map_of_injective E.subtype_injective]
    refine hOut _ (isElemAbelian_of_le_of_isElemAbelian hE (Subgroup.map_subtype_le C)) ?_
    rw [eq_bot_iff]
    rintro _ ⟨⟨c, hcC, rfl⟩, hcI⟩
    have hc : c ∈ Inn.subgroupOf E ⊓ C := ⟨Subgroup.mem_subgroupOf.mpr hcI, hcC⟩
    rw [hC.inf_eq_bot, Subgroup.mem_bot] at hc
    rw [hc]
    exact Subgroup.one_mem _
  have hp3 : p ^ 3 ≤ p ^ Open.pRank p (⊤ : Subgroup (MulAut K)) :=
    Nat.pow_le_pow_right hp.pos h3
  rw [← hEcard, ← hcard] at hp3
  have hle := Nat.mul_le_mul hI hCp
  have hlt : p * p < p ^ 3 := by
    have := hp.two_le
    nlinarith
  omega

end Aut

section Conj

variable {X : Type*} [Group X] [Finite X]

theorem commute_of_mem_normalizer_zpowers_of_pow_eq_one {p : ℕ} (hp : p.Prime) {t v : X}
    (ht : orderOf t = p) (hv : v ∈ Subgroup.normalizer (Subgroup.zpowers t : Set X))
    (hvp : v ^ p = 1) : Commute v t := by
  have hle := card_le_card_inf_centralizer_pow hp
    (isElemAbelian_zpowers (ht ▸ pow_orderOf_eq_one t)) hv hvp
  rw [Nat.card_zpowers, ht] at hle
  have hdvd : Nat.card (Subgroup.zpowers t ⊓ Subgroup.centralizer ({v} : Set X) :
      Subgroup X) ∣ p := by
    have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers t ⊓
      Subgroup.centralizer ({v} : Set X) ≤ Subgroup.zpowers t)
    rwa [Nat.card_zpowers, ht] at this
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | hpc
  · rw [h1, one_pow] at hle
    exact absurd hle (by have := hp.one_lt; omega)
  · have heq : Subgroup.zpowers t ⊓ Subgroup.centralizer ({v} : Set X) = Subgroup.zpowers t :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hpc, Nat.card_zpowers, ht])
    have htC : t ∈ Subgroup.zpowers t ⊓ Subgroup.centralizer ({v} : Set X) := by
      rw [heq]
      exact Subgroup.mem_zpowers t
    exact (Subgroup.mem_centralizer_singleton_iff.mp htC.2).symm

theorem conj_mem_zpowers_of_isCyclic {T : Subgroup X} [IsCyclic T] {t t' g : X}
    (ht : orderOf t = orderOf t') (ht' : t' ∈ T) (hg : g * t * g⁻¹ ∈ T) :
    g * t * g⁻¹ ∈ Subgroup.zpowers t' :=
  mem_zpowers_of_orderOf_eq_of_isCyclic hg ht'
    ((SemiconjBy.orderOf_eq g (by simp [SemiconjBy, mul_assoc])).symm.trans ht)

theorem mem_normalizer_zpowers_of_mem_zpowers {a g : X}
    (ha : g * a * g⁻¹ ∈ Subgroup.zpowers a) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers a : Set X) := by
  apply mem_normalizer_of_conj_map_le
  rw [MonoidHom.map_zpowers]
  exact Subgroup.zpowers_le.mpr ha

theorem mem_normalizer_sup_zpowers {a b g : X}
    (ha : g * a * g⁻¹ ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b)
    (hb : g * b * g⁻¹ ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup X) : Set X) := by
  apply mem_normalizer_of_conj_map_le
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  exact sup_le (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr hb)

omit [Finite X] in
theorem le_centralizer_sup_zpowers {A : Subgroup X} {a b : X} (ha : ∀ v ∈ A, Commute v a)
    (hb : ∀ v ∈ A, Commute v b) :
    A ≤ Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup X) : Set X) := by
  rw [Subgroup.le_centralizer_iff]
  exact sup_le
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun v hv => (ha v hv).eq))
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun v hv => (hb v hv).eq))

theorem pRank_bot_eq_zero {p : ℕ} (hp : p.Prime) : Open.pRank p (⊥ : Subgroup X) = 0 := by
  obtain ⟨E, hE, -, hEcard⟩ := pRank_attained p hp (⊥ : Subgroup X)
  rw [le_bot_iff] at hE
  rw [hE, Subgroup.card_bot] at hEcard
  exact (Nat.pow_eq_one.mp hEcard.symm).resolve_left hp.one_lt.ne'

end Conj

end CFSG.AGLEmbedding
