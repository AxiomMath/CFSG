module

public import CFSG.HardMathSupport.Foote.Bridges.CoprimeAut
public import CFSG.LocalAnalysis.AGLEmbedding.SPLMSidePPrime
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open SemidirectProduct CFSG.HardMathSupport.Foote.Bridges

theorem kFactCoprimeAutEvenCentralizer_of_pPrimeCompP
    (h : CFSG.AGLEmbedding.KFactPPrimeCompInvolutionP) :
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactCoprimeAutEvenCentralizer := by
  intro p hp hp2 K _ _ hS hnc hcat hpK φ hφp hφ1
  have hZ : Subgroup.center K = ⊥ := center_eq_bot_of_simple hS hnc
  have hPK : Group.IsPerfect K := isPerfect_of_simple hS hnc
  have hφfin : IsOfFinOrder φ := isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.pos, hφp⟩
  have : Finite (Subgroup.zpowers φ) := finite_zpowers.mpr hφfin
  have : Finite (K ⋊[zpowersAction K φ] ↥(Subgroup.zpowers φ)) :=
    finite_semidirect (zpowersAction K φ)
  set Λ : Subgroup (K ⋊[zpowersAction K φ] ↥(Subgroup.zpowers φ)) :=
    (SemidirectProduct.inl : K →* K ⋊[zpowersAction K φ] ↥(Subgroup.zpowers φ)).range with hΛdef
  let e : K ≃* Λ := MonoidHom.ofInjective SemidirectProduct.inl_injective
  have hΛn : Λ.Normal := by
    rw [hΛdef, SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  have hΛperf : Group.IsPerfect Λ := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hZΛ : Subgroup.center Λ = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨_, t, rfl⟩ hz
    have hk : t ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro k
      have hc := Subgroup.mem_center_iff.mp hz
        ⟨SemidirectProduct.inl k, by rw [hΛdef]; exact MonoidHom.mem_range.mpr ⟨k, rfl⟩⟩
      have h2 : (SemidirectProduct.inl k : K ⋊[zpowersAction K φ] ↥(Subgroup.zpowers φ)) *
          SemidirectProduct.inl t = SemidirectProduct.inl t * SemidirectProduct.inl k :=
        congrArg Subtype.val hc
      rw [← map_mul, ← map_mul] at h2
      exact SemidirectProduct.inl_injective h2
    rw [hZ] at hk
    have ht : t = 1 := Subgroup.mem_bot.mp hk
    subst ht
    rw [Subgroup.mem_bot]
    exact Subtype.ext (map_one _)
  have hΛidx : ¬ p ∣ (Subgroup.center Λ).index := by
    have hcard := Nat.card_congr e.toEquiv
    rw [hZΛ, Subgroup.index_bot, ← hcard]
    exact hpK
  let q : (Λ ⧸ Subgroup.center Λ) ≃* Λ :=
    (QuotientGroup.quotientMulEquivOfEq hZΛ).trans QuotientGroup.quotientBot
  let gq : K ≃* (Λ ⧸ Subgroup.center Λ) := e.trans q.symm
  have hSQ : IsSimpleGroup (Λ ⧸ Subgroup.center Λ) := gq.symm.isSimpleGroup
  have hncQ : ∃ a b : Λ ⧸ Subgroup.center Λ, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    refine ⟨gq a, gq b, fun heq => hab (gq.injective ?_)⟩
    rw [map_mul, map_mul]
    exact heq
  have hcatQ : CFSG.Open.IsCatalogGroup (Λ ⧸ Subgroup.center Λ) := by
    obtain ⟨i, ⟨ei⟩⟩ := hcat
    exact ⟨i, ⟨gq.symm.trans ei⟩⟩
  have hQ : CFSG.IsQuasisimple Λ := by
    unfold CFSG.IsQuasisimple
    exact ⟨hΛperf, hSQ, hncQ⟩
  have hΛcomp : CFSG.IsComponent Λ := ⟨hQ, hΛn.isSubnormal⟩
  let g : ↥(Subgroup.zpowers φ) := ⟨φ, Subgroup.mem_zpowers φ⟩
  have hgp : g ^ p = 1 := Subtype.ext (by simpa [g] using hφp)
  have hu_norm : (SemidirectProduct.inr g : K ⋊[zpowersAction K φ] ↥(Subgroup.zpowers φ)) ∈
      Subgroup.normalizer (Λ : Set (K ⋊[zpowersAction K φ] ↥(Subgroup.zpowers φ))) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hΛn]
    exact Subgroup.mem_top _
  have hup : (SemidirectProduct.inr g : K ⋊[zpowersAction K φ] ↥(Subgroup.zpowers φ)) ^ p = 1 := by
    rw [← map_pow SemidirectProduct.inr, hgp, map_one]
  have hTu : ∀ t ∈ (⊥ : Subgroup (K ⋊[zpowersAction K φ] ↥(Subgroup.zpowers φ))),
      t * SemidirectProduct.inr g = SemidirectProduct.inr g * t := by
    intro t ht
    rw [Subgroup.mem_bot] at ht
    subst ht
    simp
  have hT1le : (⊥ : Subgroup (K ⋊[zpowersAction K φ] ↥(Subgroup.zpowers φ))) ≤
      Subgroup.normalizer (Λ : Set (K ⋊[zpowersAction K φ] ↥(Subgroup.zpowers φ))) := bot_le
  have hTp : ∀ a ∈ (⊥ : Subgroup (K ⋊[zpowersAction K φ] ↥(Subgroup.zpowers φ))),
      a ^ p ∈ Subgroup.centralizer
        (Λ : Set (K ⋊[zpowersAction K φ] ↥(Subgroup.zpowers φ))) := by
    intro a ha
    rw [Subgroup.mem_bot] at ha
    subst ha
    rw [one_pow]
    exact Subgroup.one_mem _
  have hu_notcent : (SemidirectProduct.inr g : K ⋊[zpowersAction K φ] ↥(Subgroup.zpowers φ)) ∉
      Subgroup.centralizer (Λ : Set (K ⋊[zpowersAction K φ] ↥(Subgroup.zpowers φ))) := by
    intro hc
    apply hφ1
    ext t
    have h1 := Subgroup.mem_centralizer_iff.mp hc (SemidirectProduct.inl t)
      (SetLike.mem_coe.mpr (by rw [hΛdef]; exact MonoidHom.mem_range.mpr ⟨t, rfl⟩))
    have h3 : zpowersAction K φ g t = t := fixed_of_comm _ g t h1
    rw [MulAut.one_apply]
    exact h3
  obtain ⟨j, hjΛ, hj1, hj2, hju, -⟩ :=
    h (K ⋊[zpowersAction K φ] ↥(Subgroup.zpowers φ)) p hp hp2 Λ hΛcomp hcatQ hΛidx ⊥
      (SemidirectProduct.inr g) hT1le hTp hu_norm hup hTu hu_notcent
  obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hjΛ
  have ht1 : t ≠ 1 := fun ht => hj1 (by rw [ht, map_one])
  have hsq : t ^ 2 = 1 := by
    have h2 : (SemidirectProduct.inl (t ^ 2) : K ⋊[zpowersAction K φ] ↥(Subgroup.zpowers φ)) =
        SemidirectProduct.inl 1 := by
      rw [map_pow, map_one]
      exact hj2
    exact SemidirectProduct.inl_injective h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨t, orderOf_eq_prime hsq ht1, fixed_of_comm _ g t hju⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
