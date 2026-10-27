module

public import CFSG.GH74.GLS.Basic
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJ

open CFSG Subgroup
open scoped commutatorElement

theorem zj_centralizes {G : Type*} [Group G] {Q A M : Subgroup G} [Q.Normal] [M.Normal]
    (hQ : CFSG.IsQuasisimple ↥Q) (hMQ : M ≤ Q) (hMne : M ≠ Q)
    (hcomm : ∀ q ∈ Q, ∀ a ∈ A, ⁅q, a⁆ ∈ M) :
    ∀ a ∈ A, ∀ q ∈ Q, a * q = q * a := by
  have hMcent : ∀ m ∈ M, ∀ q ∈ Q, m * q = q * m := by
    intro m hm q hq
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ (N := M.subgroupOf Q)
      inferInstance with htop | hle
    · exact absurd (le_antisymm hMQ (subgroupOf_eq_top.mp htop)) hMne
    · have hmem : (⟨m, hMQ hm⟩ : ↥Q) ∈ M.subgroupOf Q := mem_subgroupOf.mpr hm
      have hc := congrArg Subtype.val (Subgroup.mem_center_iff.mp (hle hmem) ⟨q, hq⟩)
      exact hc.symm
  have hQA : ⁅Q, A⁆ ≤ M := commutator_le.mpr hcomm
  have hdc : ⁅⁅Q, A⁆, Q⁆ = ⊥ := by
    rw [eq_bot_iff]
    refine commutator_le.mpr fun x hx y hy => ?_
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
    exact hMcent x (hQA hx) y hy
  have hQA_bot : ⁅Q, A⁆ = ⊥ := CFSG.LocalCores.perfect_double_commutator hQ.1 hdc
  intro a ha q hq
  have hmem : ⁅q, a⁆ ∈ ⁅Q, A⁆ := commutator_mem_commutator hq ha
  rw [hQA_bot, Subgroup.mem_bot, commutatorElement_eq_one_iff_commute] at hmem
  exact hmem.symm

theorem zj_isNilpotent {G : Type*} [Group G] [Finite G] {Q A : Subgroup G} [Q.Normal]
    (hcent : ∀ a ∈ A, ∀ q ∈ Q, a * q = q * a)
    (h2 : ∀ g : G, ∃ k : ℕ, g ^ (2 ^ k) ∈ Q) :
    Group.IsNilpotent ↥A := by
  let f : A →* G ⧸ Q := (QuotientGroup.mk' Q).comp A.subtype
  have hker : f.rangeRestrict.ker ≤ Subgroup.center ↥A := by
    rw [MonoidHom.ker_rangeRestrict]
    intro x hx
    have hx' : f x = 1 := MonoidHom.mem_ker.mp hx
    have hxQ : (x : G) ∈ Q := (QuotientGroup.eq_one_iff (x : G)).mp hx'
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact hcent y y.2 x hxQ
  have hP : IsPGroup 2 f.range := by
    intro h
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp h.2
    obtain ⟨k, hk⟩ := h2 (x : G)
    refine ⟨k, Subtype.ext ?_⟩
    have key : ((h : G ⧸ Q)) ^ (2 ^ k) = 1 := by
      rw [← hx]
      change ((x : G) : G ⧸ Q) ^ (2 ^ k) = 1
      rw [← QuotientGroup.mk_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hk
    simpa using key
  haveI : Group.IsNilpotent f.range := hP.isNilpotent
  exact Subgroup.isNilpotent_of_ker_le_center f.rangeRestrict hker

theorem zj_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hcore : CFSG.pPrimeCore p G = ⊥)
    {Q A M : Subgroup G} [Q.Normal] [M.Normal] [A.Normal]
    (hQ : CFSG.IsQuasisimple ↥Q) (hMQ : M ≤ Q) (hMne : M ≠ Q)
    (hcomm : ∀ q ∈ Q, ∀ a ∈ A, ⁅q, a⁆ ∈ M)
    (h2 : ∀ g : G, ∃ k : ℕ, g ^ (2 ^ k) ∈ Q) :
    IsPGroup p A :=
  CFSG.isPGroup_of_nilpotent_normal A inferInstance
    (zj_isNilpotent (zj_centralizes hQ hMQ hMne hcomm) h2) hcore

theorem zj_normal_le_pPrimeP {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K N : Subgroup X} [K.Normal] [N.Normal] (hK : CFSG.IsPComponent p K) (T : Sylow 2 X)
    (hKT : K ⊔ (T : Subgroup X) = ⊤) (hNK : ¬ K ≤ N) :
    N ≤ CFSG.GH74.GLS.pPrimePCore p X := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K₀, hK₀, -, hmap, hmin⟩ := hK
  set O := CFSG.pPrimeCore p X with hO
  haveI hKn : (K.map (QuotientGroup.mk' O)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective O)
  haveI hNn : (N.map (QuotientGroup.mk' O)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective O)
  haveI hMn : ((N ⊓ K).map (QuotientGroup.mk' O)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective O)
  have hQq : CFSG.IsQuasisimple ↥(K.map (QuotientGroup.mk' O)) := by
    rw [hmap]
    exact hK₀.1
  have hMQ : (N ⊓ K).map (QuotientGroup.mk' O) ≤ K.map (QuotientGroup.mk' O) :=
    Subgroup.map_mono inf_le_right
  have hMne : (N ⊓ K).map (QuotientGroup.mk' O) ≠ K.map (QuotientGroup.mk' O) := by
    intro heq
    have hlt : N ⊓ K < K := by
      refine lt_of_le_of_ne inf_le_right fun h => hNK ?_
      calc K = N ⊓ K := h.symm
        _ ≤ N := inf_le_left
    have hsub : (N ⊓ K).IsSubnormal := Subgroup.Normal.isSubnormal inferInstance
    exact hmin (N ⊓ K) hlt hsub (heq.trans hmap)
  have hcomm : ∀ q ∈ K.map (QuotientGroup.mk' O), ∀ a ∈ N.map (QuotientGroup.mk' O),
      ⁅q, a⁆ ∈ (N ⊓ K).map (QuotientGroup.mk' O) := by
    intro q hq a ha
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hq
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp ha
    refine Subgroup.mem_map.mpr ⟨⁅k, n⁆, ?_, ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        exact N.mul_mem (Subgroup.Normal.conj_mem inferInstance n hn k) (N.inv_mem hn)
      · have h : ⁅k, n⁆ = k * (n * k⁻¹ * n⁻¹) := by
          rw [commutatorElement_def]
          group
        rw [h]
        exact K.mul_mem hk (Subgroup.Normal.conj_mem inferInstance k⁻¹ (K.inv_mem hk) n)
    · simp [commutatorElement_def]
  have hQ2 : ∀ g : X ⧸ O, ∃ j : ℕ, g ^ (2 ^ j) ∈ K.map (QuotientGroup.mk' O) := by
    intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective O g
    have hx : x ∈ K ⊔ (T : Subgroup X) := by
      rw [hKT]
      exact Subgroup.mem_top x
    obtain ⟨k, hk, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    obtain ⟨j, hj⟩ := T.isPGroup' ⟨t, ht⟩
    have htj : t ^ (2 ^ j) = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    refine ⟨j, ?_⟩
    have hψk : QuotientGroup.mk' (K.map (QuotientGroup.mk' O)) (QuotientGroup.mk' O k) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_map_of_mem _ hk)
    have hψ : QuotientGroup.mk' (K.map (QuotientGroup.mk' O)) (QuotientGroup.mk' O (k * t)) =
        QuotientGroup.mk' (K.map (QuotientGroup.mk' O)) (QuotientGroup.mk' O t) := by
      rw [map_mul, map_mul, hψk, one_mul]
    have hpow : QuotientGroup.mk' (K.map (QuotientGroup.mk' O))
        ((QuotientGroup.mk' O (k * t)) ^ (2 ^ j)) = 1 := by
      rw [map_pow, hψ, ← map_pow, ← map_pow, htj, map_one, map_one]
    exact (QuotientGroup.eq_one_iff _).mp hpow
  have hcore : CFSG.pPrimeCore p (X ⧸ O) = ⊥ := CFSG.pPrimeCore_quotient_eq_bot hp
  have hpg : IsPGroup p (N.map (QuotientGroup.mk' O)) :=
    zj_isPGroup hcore hQq hMQ hMne hcomm hQ2
  have hle : N.map (QuotientGroup.mk' O) ≤ CFSG.pCore p (X ⧸ O) :=
    le_sSup ⟨inferInstance, hpg⟩
  intro n hn
  exact hle (Subgroup.mem_map_of_mem _ hn)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJ
