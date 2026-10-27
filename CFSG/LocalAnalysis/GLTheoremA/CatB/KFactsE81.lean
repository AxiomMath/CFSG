module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.KFactsAbs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.KFacts

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer equivalence)

section KLevel

variable {G : Type} [Group G] [Finite G]

theorem exists_normalizing_of_profile {K : Subgroup G} (hp : KProfile (PQuot 3 K)) {F : Subgroup G}
    (hFK : F ≤ K) (hF : IsElemAbelian 3 F) (hF4 : Nat.card F = 3 ^ 4) :
    ∃ n ∈ K, n ∈ Subgroup.normalizer (F : Set G) ∧ (∃ k : ℕ, n ^ 3 ^ k = 1) ∧
      n ∉ Subgroup.centralizer (F : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := piK K with hπ
  let F' : Subgroup ↥K := F.subgroupOf K
  have hF'e : IsElemAbelian 3 F' := isElemAbelian_subgroupOf hF
  have hF'c : Nat.card F' = 3 ^ 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFK).toEquiv).trans hF4
  obtain ⟨P, hFP⟩ := (isPGroup_of_isElemAbelian hF'e).exists_le_sylow
  set P' : Subgroup ↥K := (P : Subgroup ↥K) with hP'
  have hPb : (Sylow.mapSurjective (QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥K)) P :
      Subgroup (PQuot 3 K)) = P'.map π := Sylow.coe_mapSurjective _ P
  have hinj := piK_injective K P.isPGroup'
  have hPc : Nat.card P' = 3 ^ 5 := by
    rw [card_eq_of_injective_comp_subtype π hinj, ← hPb, Sylow.card_eq_multiplicity, hp.card3]
  obtain ⟨a, ha, b, hb, hab⟩ := hp.not_abelian (A := P'.map π)
    (by rw [← card_eq_of_injective_comp_subtype π hinj, hPc])
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  have hnc : a' * b' ≠ b' * a' := fun h => hab (by rw [← map_mul, ← map_mul, h])
  have hrel : (F'.subgroupOf P').index = 3 := by
    have h := Subgroup.relIndex_mul_card (H := F') (K := P')
    rw [inf_of_le_left hFP, hF'c, hPc] at h
    have h' : (F'.subgroupOf P').index * 3 ^ 4 = 3 * 3 ^ 4 := by
      rw [← Subgroup.relIndex]; omega
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'
  have hnormal : (F'.subgroupOf P').Normal :=
    Subgroup.normal_of_index_eq_minFac_card (by rw [hrel, hPc]; norm_num)
  have hPN : ∀ x : ↥P', (x : ↥K) ∈ Subgroup.normalizer (F' : Set ↥K) := fun x =>
    S8.L84.mem_normalizer_of_subgroupOf hFP (by
      rw [Subgroup.normalizer_eq_top_iff.2 hnormal]
      exact Subgroup.mem_top x)
  have hex : ∃ x : ↥P', (x : ↥K) ∉ Subgroup.centralizer (F' : Set ↥K) := by
    by_contra hcon
    push Not at hcon
    have hcomm : IsMulCommutative ↥P' := by
      let H : Subgroup ↥P' := F'.subgroupOf P'
      haveI : H.Normal := hnormal
      have hcard : Nat.card (↥P' ⧸ H) = 3 := (Subgroup.index_eq_card H).symm.trans hrel
      haveI : IsCyclic (↥P' ⧸ H) := isCyclic_of_prime_card hcard
      refine (QuotientGroup.mk' H).isMulCommutative_of_isCyclic_of_ker_le_center ?_
      rw [QuotientGroup.ker_mk']
      intro h hh
      rw [Subgroup.mem_center_iff]
      intro z
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hcon z) (h : ↥K) hh).symm
    exact hnc (congrArg Subtype.val (hcomm.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩))
  obtain ⟨x, hxc⟩ := hex
  refine ⟨((x : ↥K) : G), (x : ↥K).2, S8.L84.mem_normalizer_of_subgroupOf hFK (hPN x), ?_, ?_⟩
  · obtain ⟨k, hk⟩ := P.isPGroup' x
    exact ⟨k, by simpa using congrArg (fun y : ↥P' => ((y : ↥K) : G)) hk⟩
  · intro hcen
    apply hxc
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hcen (f : G) hf)

theorem relIndex_le_of_profile {K : Subgroup G} (hp : KProfile (PQuot 3 K))
    (hZ : Subgroup.center (PQuot 3 K) = ⊥) {F : Subgroup G} (hFK : F ≤ K) (hF : IsElemAbelian 3 F)
    (hF4 : Nat.card F = 3 ^ 4) {Q : Subgroup G} (hQ : IsPGroup 3 Q)
    (hQK : Q ≤ Subgroup.normalizer (K : Set G)) (hQF : Q ≤ Subgroup.normalizer (F : Set G)) :
    (Subgroup.centralizer (F : Set G)).relIndex Q ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y := PQuot 3 K
  set π := piK K with hπ
  let F' : Subgroup ↥K := F.subgroupOf K
  have hF'e : IsElemAbelian 3 F' := isElemAbelian_subgroupOf hF
  have hF'c : Nat.card F' = 3 ^ 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFK).toEquiv).trans hF4
  have hinjF := piK_injective K (isPGroup_of_isElemAbelian hF'e)
  let Fb : Subgroup Y := F'.map π
  have hFbc : Nat.card Fb = 3 ^ 4 := by
    rw [← card_eq_of_injective_comp_subtype π hinjF, hF'c]
  have hFbe : IsElemAbelian 3 Fb := S8.L84.isElemAbelian_map π hF'e
  let β : ↥Q →* MulAut Y :=
    (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K).comp (Subgroup.inclusion hQK)
  have hβ : ∀ q : ↥Q, β q ∈ (MulAut.conj : Y →* MulAut Y).range := by
    intro q
    obtain ⟨k, hk⟩ := hQ q
    exact mem_inner_of_pow hp.outer _ (k := k) (by rw [← map_pow, hk, map_one])
  have hcinj : Function.Injective (MulAut.conj : Y →* MulAut Y) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxc : x ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun φ : MulAut Y => φ g) (MonoidHom.mem_ker.1 hx)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc g * x = x * g * x⁻¹ * x := by rw [h1]
        _ = x * g := by group
    rw [hZ] at hxc
    exact hxc
  let θ : ↥Q →* Y :=
    (MonoidHom.ofInjective hcinj).symm.toMonoidHom.comp (β.codRestrict _ hβ)
  have hθ : ∀ q : ↥Q, MulAut.conj (θ q) = β q := fun q =>
    congrArg Subtype.val ((MonoidHom.ofInjective hcinj).apply_symm_apply (⟨β q, hβ q⟩ :
      (MulAut.conj : Y →* MulAut Y).range))
  have hKI : ∀ (q : ↥Q) (f : ↥K), θ q * π f * (θ q)⁻¹ =
      π ((K.normalizerMonoidHom ⟨(q : G), hQK q.2⟩ : MulAut ↥K) f) := by
    intro q f
    have h1 := congrArg (fun φ : MulAut Y => φ (π f)) (hθ q)
    simp only [MulAut.conj_apply] at h1
    rw [h1]
    exact CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk 3 K ⟨(q : G), hQK q.2⟩ f
  have hFbN : ∀ (q : ↥Q), ∀ y ∈ Fb, θ q * y * (θ q)⁻¹ ∈ Fb := by
    intro q y hy
    obtain ⟨f, hf, rfl⟩ := hy
    rw [hKI]
    refine ⟨_, ?_, rfl⟩
    show (((K.normalizerMonoidHom ⟨(q : G), hQK q.2⟩ : MulAut ↥K) f : ↥K) : G) ∈ F
    exact (Subgroup.mem_normalizer_iff.1 (hQF q.2) (f : G)).1 (Subgroup.mem_subgroupOf.1 hf)
  let D : Subgroup Y := θ.range
  have hDN : D ≤ Subgroup.normalizer (Fb : Set Y) := by
    rintro _ ⟨q, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hFbN q y hy, fun hy => ?_⟩
    have h1 := hFbN q⁻¹ _ hy
    simpa [map_inv, mul_assoc] using h1
  have hD3 : IsPGroup 3 D := hQ.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective
  have hsup3 : IsPGroup 3 ↥(Fb ⊔ D) :=
    IsPGroup.to_sup_of_normal_left' (isPGroup_of_isElemAbelian hFbe) hD3 hDN
  have hle : Nat.card ↥(Fb ⊔ D) ≤ 3 ^ 5 := by
    have h1 := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.card_le_of_isPGroup hsup3
    rwa [hp.card3] at h1
  have hprod := card_sup_mul_card_inf_of_le_normalizer hDN
  have hrel := Subgroup.relIndex_mul_card (H := Fb) (K := D)
  have hpos : 0 < Nat.card ↥(Fb ⊓ D) := Nat.card_pos
  have hrelD : Fb.relIndex D ≤ 3 := by
    have h1 : Nat.card ↥(Fb ⊔ D) * Nat.card ↥(Fb ⊓ D) =
        3 ^ 4 * Fb.relIndex D * Nat.card ↥(Fb ⊓ D) := by
      rw [hprod, hFbc, ← hrel]
      ring
    have h2 := Nat.eq_of_mul_eq_mul_right hpos h1
    rw [h2] at hle
    norm_num at hle
    omega
  let Z₁ : Subgroup ↥Q := Fb.comap θ
  have hZ₁ : Z₁ ≤ (Subgroup.centralizer (F : Set G)).subgroupOf Q := by
    intro q hq
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro f hf
    have hfK : f ∈ K := hFK hf
    have hfF' : (⟨f, hfK⟩ : ↥K) ∈ F' := Subgroup.mem_subgroupOf.2 hf
    have hmem : (K.normalizerMonoidHom ⟨(q : G), hQK q.2⟩ : MulAut ↥K) ⟨f, hfK⟩ ∈ F' :=
      Subgroup.mem_subgroupOf.2 ((Subgroup.mem_normalizer_iff.1 (hQF q.2) f).1 hf)
    have h1 : θ q * π ⟨f, hfK⟩ * (θ q)⁻¹ = π ⟨f, hfK⟩ := by
      have hcomm := isElemAbelian_commute hFbe (a := θ q) (b := π ⟨f, hfK⟩) hq
        ⟨_, hfF', rfl⟩
      rw [hcomm]
      group
    rw [hKI] at h1
    have h2 := hinjF (a₁ := ⟨_, hmem⟩) (a₂ := ⟨_, hfF'⟩) h1
    have h3 : (q : G) * f * (q : G)⁻¹ = f := congrArg (fun x : ↥F' => (((x : ↥K)) : G)) h2
    calc f * (q : G) = (q : G) * f * (q : G)⁻¹ * (q : G) := by rw [h3]
      _ = (q : G) * f := by group
  have hidx : Z₁.index = Fb.relIndex D := Subgroup.index_comap Fb θ
  calc (Subgroup.centralizer (F : Set G)).relIndex Q
      = ((Subgroup.centralizer (F : Set G)).subgroupOf Q).index := rfl
    _ ≤ Z₁.index := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.index_dvd_of_le hZ₁)
    _ = Fb.relIndex D := hidx
    _ ≤ 3 := hrelD

end KLevel

end CFSG.LocalAnalysis.GLTheoremA.CatB.KFacts
