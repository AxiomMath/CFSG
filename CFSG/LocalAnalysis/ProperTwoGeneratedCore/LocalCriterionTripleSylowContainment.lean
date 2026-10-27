module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylowKernel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylowExtension
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointSylowBridge

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow

open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G] [Finite G]

theorem invariant_sylow_fixed_ambient
    (p : ℕ) (hp : p.Prime) (B K : Subgroup G) (hBK : B ≤ K)
    (J : Subgroup K) [J.Normal] (z : K) (hz : orderOf z = 2)
    (hJodd : Odd (Nat.card J)) (hJB : J ≤ B.subgroupOf K)
    (hcentral : QuotientGroup.mk' J z ∈ Subgroup.center (K ⧸ J))
    (P : Sylow p B)
    (hPnorm : (z : G) ∈ Subgroup.normalizer
      (((P : Subgroup B).map B.subtype : Subgroup G) : Set G)) :
    ∃ R : Sylow p (B ⊓ Subgroup.centralizer ({(z : G)} : Set G) : Subgroup G),
      (R : Subgroup (B ⊓ Subgroup.centralizer ({(z : G)} : Set G) : Subgroup G)).map
          (B ⊓ Subgroup.centralizer ({(z : G)} : Set G)).subtype =
        (P : Subgroup B).map B.subtype ⊓ Subgroup.centralizer ({(z : G)} : Set G) := by
  let : Fact p.Prime := ⟨hp⟩
  let BK := B.subgroupOf K
  obtain ⟨Q, hQimage⟩ := sylow_subgroupOf_restriction_ambient_image p hp B K hBK P
  have hQnorm : z ∈ Subgroup.normalizer
      (((Q : Subgroup BK).map BK.subtype : Subgroup K) : Set K) := by
    apply (normalizer_in_subgroup_iff_ambient_image K _ z).mpr
    rw [hQimage]
    exact hPnorm
  obtain ⟨R₀, hR₀image⟩ := odd_central_quotient_invariant_sylow_fixed
    p hp BK J z hz hJodd hJB hcentral Q hQnorm
  let C := B ⊓ Subgroup.centralizer ({(z : G)} : Set G)
  have hCK : C ≤ K := inf_le_left.trans hBK
  have hC₀ : BK ⊓ Subgroup.centralizer ({z} : Set K) = C.subgroupOf K := by
    ext a
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff, BK, C]
    exact ⟨fun h => ⟨h.1, congrArg Subtype.val h.2⟩,
      fun h => ⟨h.1, Subtype.ext h.2⟩⟩
  let e := MulEquiv.subgroupCongr hC₀
  have he : Function.Surjective e.toMonoidHom := by
    intro a
    obtain ⟨b, hb⟩ := e.surjective a
    exact ⟨b, hb⟩
  let R₁ : Sylow p (C.subgroupOf K) := R₀.mapSurjective (f := e.toMonoidHom) he
  obtain ⟨R, hRimage⟩ := sylow_subgroupOf_extension_ambient_image p hp C K hCK R₁
  refine ⟨R, ?_⟩
  rw [hRimage]
  have hR₁ : (R₁ : Subgroup (C.subgroupOf K)).map (C.subgroupOf K).subtype =
      (Q : Subgroup BK).map BK.subtype ⊓ Subgroup.centralizer ({z} : Set K) := by
    dsimp only [R₁]
    rw [Sylow.coe_mapSurjective, Subgroup.map_map]
    have hhom : (C.subgroupOf K).subtype.comp e.toMonoidHom =
        (BK ⊓ Subgroup.centralizer ({z} : Set K)).subtype := by
      ext a
      exact congrArg Subtype.val (MulEquiv.subgroupCongr_apply hC₀ a)
    rw [hhom]
    exact hR₀image
  rw [hR₁, Subgroup.map_inf _ _ K.subtype K.subtype_injective, hQimage,
    centralizer_in_subgroup_eq_ambient_restriction, Subgroup.subgroupOf_map_subtype]
  ext a
  exact ⟨fun ha => ⟨ha.1, ha.2.1⟩,
    fun ha => ⟨ha.1, ha.2, ((Subgroup.map_subtype_le _).trans hBK) ha.1⟩⟩

theorem invariant_subgroup_extends_ambient
    (p : ℕ) (hp : p.Prime) (B K X : Subgroup G) (hBK : B ≤ K)
    (hBnormal : (B.subgroupOf K).Normal)
    (J : Subgroup K) [J.Normal] (z : K) (hz : orderOf z = 2)
    (hJodd : Odd (Nat.card J)) (hJB : J ≤ B.subgroupOf K)
    (hcentral : QuotientGroup.mk' J z ∈ Subgroup.center (K ⧸ J))
    (hXB : X ≤ B) (hX : IsPGroup p X)
    (hXnorm : (z : G) ∈ Subgroup.normalizer (X : Set G)) :
    ∃ P : Sylow p B, X ≤ (P : Subgroup B).map B.subtype ∧
      (z : G) ∈ Subgroup.normalizer (((P : Subgroup B).map B.subtype : Subgroup G) : Set G) := by
  let _ := hBnormal
  have hXK : X ≤ K := hXB.trans hBK
  have hXKp : IsPGroup p (X.subgroupOf K) :=
    hX.of_injective (Subgroup.subgroupOfEquivOfLe hXK).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hXK).injective
  have hXKn : z ∈ Subgroup.normalizer (X.subgroupOf K : Set K) := by
    apply (normalizer_in_subgroup_iff_ambient_image K _ z).mpr
    rw [Subgroup.map_subgroupOf_eq_of_le hXK]
    exact hXnorm
  obtain ⟨Q, hXQ, hQnorm⟩ := invariant_subgroup_extends p hp
    (B.subgroupOf K) J (X.subgroupOf K) z hz hJodd hJB hcentral
    (Subgroup.subgroupOf_mono K hXB) hXKp hXKn
  obtain ⟨P, hPimage⟩ := sylow_subgroupOf_extension_ambient_image p hp B K hBK Q
  refine ⟨P, ?_, ?_⟩
  · rw [hPimage, ← Subgroup.map_subgroupOf_eq_of_le hXK]
    exact Subgroup.map_mono hXQ
  · rw [hPimage]
    exact (normalizer_in_subgroup_iff_ambient_image K _ z).mp hQnorm

theorem triple_invariant_sylow_fixed
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (P : Sylow p (triplePointStabilizer H z beta))
    (hPnorm : z ∈ Subgroup.normalizer
      (((P : Subgroup (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype : Subgroup G) : Set G)) :
    ∃ R : Sylow p (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G),
      (R : Subgroup (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G)).map
          (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({z} : Set G)).subtype =
        (P : Subgroup (triplePointStabilizer H z beta)).map
          (triplePointStabilizer H z beta).subtype ⊓ Subgroup.centralizer ({z} : Set G) := by
  refine Quotient.inductionOn' beta (fun x hbeta P hPnorm => ?_) hbeta P hPnorm
  let E := triplePointStabilizer H z (rightCosetMk H x)
  let K := E ⊔ Subgroup.zpowers z
  let J₀ := pairOddCore (CFSG.BenderSuzuki.PFchapter1section1.rightConjugate H x)
    (rightCosetMk (CFSG.BenderSuzuki.PFchapter1section1.rightConjugate H x) z)
  let J := (E ⊓ J₀).subgroupOf K
  let zK : K := ⟨z, (show Subgroup.zpowers z ≤ K from le_sup_right) (Subgroup.mem_zpowers z)⟩
  obtain ⟨hJnormal, _, hJodd, hJE, hcentral⟩ :=
    triple_opposite_kernel_odd_central_quotient h S hzS hzcenter x hbeta
  let _ := hJnormal
  have hzK : orderOf zK = 2 := (Subgroup.orderOf_coe zK).symm.trans h.distinguished_order
  have hfixed := invariant_sylow_fixed_ambient p hp E K le_sup_left J zK hzK hJodd
    (Subgroup.subgroupOf_mono K hJE) hcentral P hPnorm
  rw [triple_z_centralizer_eq_pair] at hfixed
  exact hfixed

theorem triple_invariant_subgroup_extends
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (X : Subgroup G) (hXB : X ≤ pairPointStabilizer H beta)
    (hX : IsPGroup p X) (hXnorm : z ∈ Subgroup.normalizer (X : Set G)) :
    X ≤ triplePointStabilizer H z beta ∧
      ∃ P : Sylow p (triplePointStabilizer H z beta),
        X ≤ (P : Subgroup (triplePointStabilizer H z beta)).map
          (triplePointStabilizer H z beta).subtype ∧
        z ∈ Subgroup.normalizer
          (((P : Subgroup (triplePointStabilizer H z beta)).map
            (triplePointStabilizer H z beta).subtype : Subgroup G) : Set G) ∧
        ∃ R : Sylow p (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G),
          (R : Subgroup (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G)).map
              (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({z} : Set G)).subtype =
            (P : Subgroup (triplePointStabilizer H z beta)).map
              (triplePointStabilizer H z beta).subtype ⊓ Subgroup.centralizer ({z} : Set G) := by
  have hXE := invariant_pair_subgroup_le_triple hXB hXnorm
  refine ⟨hXE, ?_⟩
  have hexists : ∃ P : Sylow p (triplePointStabilizer H z beta),
      X ≤ (P : Subgroup (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype ∧
      z ∈ Subgroup.normalizer
        (((P : Subgroup (triplePointStabilizer H z beta)).map
          (triplePointStabilizer H z beta).subtype : Subgroup G) : Set G) := by
    refine Quotient.inductionOn' beta (fun x hbeta hXE => ?_) hbeta hXE
    let E := triplePointStabilizer H z (rightCosetMk H x)
    let K := E ⊔ Subgroup.zpowers z
    let J₀ := pairOddCore (CFSG.BenderSuzuki.PFchapter1section1.rightConjugate H x)
      (rightCosetMk (CFSG.BenderSuzuki.PFchapter1section1.rightConjugate H x) z)
    let J := (E ⊓ J₀).subgroupOf K
    let zK : K := ⟨z, (show Subgroup.zpowers z ≤ K from le_sup_right) (Subgroup.mem_zpowers z)⟩
    obtain ⟨hJnormal, _, hJodd, hJE, hcentral⟩ :=
      triple_opposite_kernel_odd_central_quotient h S hzS hzcenter x hbeta
    let _ := hJnormal
    exact invariant_subgroup_extends_ambient p hp E K X le_sup_left
      (triple_stabilizer_normal_in_generated h (rightCosetMk H x)) J zK
      ((Subgroup.orderOf_coe zK).symm.trans h.distinguished_order) hJodd
      (Subgroup.subgroupOf_mono K hJE) hcentral hXE hX hXnorm
  obtain ⟨P, hXP, hPnorm⟩ := hexists
  exact ⟨P, hXP, hPnorm, triple_invariant_sylow_fixed h S hzS hzcenter beta hbeta p hp P hPnorm⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
