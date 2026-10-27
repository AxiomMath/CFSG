module

public import CFSG.LocalAnalysis.AGLEmbedding.Escape
public import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

section Image

variable {X Y : Type*} [Group X] [Group Y]

theorem map_glbConj (f : X →* Y) (x : X) (S : Subgroup X) :
    (GLBConj x S).map f = GLBConj (f x) (S.map f) := by
  simp only [GLBConj, Subgroup.map_map]
  congr 1
  ext s
  simp

theorem map_inf_map_le_of_ker_le (f : X →* Y) {A B : Subgroup X} (hA : f.ker ≤ A) :
    A.map f ⊓ B.map f ≤ (A ⊓ B).map f := by
  rintro _ ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
  refine ⟨b, ⟨?_, hb⟩, hab⟩
  have hker : a⁻¹ * b ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
  simpa using A.mul_mem ha (hA hker)

end Image

namespace D1Escape

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem pRank_inf_conj_le_two (h : D1Escape p P M H R) {g : G} (hg : g ∉ M) :
    Open.pRank p ((H ⊓ M) ⊓ GLBConj g (H ⊓ M)) ≤ 2 :=
  (PreuniquenessRankFour.Helpers.pRank_mono p h.prime
    (inf_le_inf inf_le_right (Subgroup.map_mono inf_le_right))).trans
    (escaping_GLBConj_intersection_rank_le_two p h.prime P h.sylow_le h.weakCore_le
      (h.three_le_pRank.trans (PreuniquenessRankFour.Helpers.pRank_mono p h.prime h.le_P)) g hg)

theorem pRank_quotient_inf_conj_le_two (h : D1Escape p P M H R) (O : Subgroup H) [O.Normal]
    (hO : p.Coprime (Nat.card O)) (hOM : O ≤ (H ⊓ M).subgroupOf H) {x : H ⧸ O}
    (hx : x ∉ ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' O)) :
    Open.pRank p (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' O) ⊓
      GLBConj x (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' O))) ≤ 2 := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective O x
  have hk : (k : G) ∉ M := fun hkM => hx ⟨k, Subgroup.mem_subgroupOf.mpr ⟨k.2, hkM⟩, rfl⟩
  rw [← map_glbConj]
  refine (PreuniquenessRankFour.Helpers.pRank_mono p h.prime
    (map_inf_map_le_of_ker_le _ (by rwa [QuotientGroup.ker_mk']))).trans ?_
  rw [pRank_map_mk_eq_pRank_map_subtype h.prime O hO]
  refine (PreuniquenessRankFour.Helpers.pRank_mono p h.prime ?_).trans
    (h.pRank_inf_conj_le_two hk)
  refine (Subgroup.map_inf_le _ _ _).trans ?_
  rw [map_glbConj, Subgroup.map_subgroupOf_eq_of_le inf_le_left]
  rfl

end D1Escape

section Reduced

variable {X : Type*} [Group X] [Finite X]

theorem eq_bot_of_isSubnormal_of_coprime {p : ℕ} (hcore : primeComplementCore (G := X) p = ⊥)
    {S : Subgroup X} (hS : IsSubnormal S ⊤) (hcop : p.Coprime (Nat.card S)) : S = ⊥ := by
  have htop : (⊤ : Subgroup S) ≤ primeComplementCore p :=
    normal_coprime_le_primeComplementCore p ⊤ inferInstance (by rwa [Subgroup.card_top])
  rw [cfsg_subnormal_primeComplementCore_eq_bot p S hS hcore, top_le_iff] at htop
  rw [Subgroup.eq_bot_iff_forall]
  intro s hs
  have hmem : (⟨s, hs⟩ : S) ∈ (⊥ : Subgroup S) := htop ▸ Subgroup.mem_top _
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)

theorem isPGroup_center_of_isComponentOf {p : ℕ} (hp : p.Prime)
    (hcore : primeComplementCore (G := X) p = ⊥) {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    IsPGroup p (Subgroup.center K) :=
  normal_nilpotent_isPGroup_of_primeComplementCore_eq_bot p hp
    (cfsg_subnormal_primeComplementCore_eq_bot p K hK.2.1 hcore) _ inferInstance inferInstance

theorem prime_dvd_card_center_quotient_of_isComponentOf {p : ℕ} (hp : p.Prime)
    (hcore : primeComplementCore (G := X) p = ⊥) {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    p ∣ Nat.card (K ⧸ Subgroup.center K) := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hndvd
  have hpow : ∀ g : K, g ^ (Subgroup.center K).index = 1 := by
    intro g
    have hker : g ∈ (MonoidHom.transferCenterPow K).ker :=
      Abelianization.commutator_subset_ker _ (hK.2.2.1 ▸ Subgroup.mem_top g)
    rw [MonoidHom.mem_ker] at hker
    rw [← MonoidHom.transferCenterPow_apply, hker, Subgroup.coe_one]
  have hcop : p.Coprime (Nat.card K) := by
    rw [hp.coprime_iff_not_dvd]
    intro hdvd
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
    apply hndvd
    rw [← Subgroup.index_eq_card, ← hg]
    exact orderOf_dvd_of_pow_eq_one (hpow g)
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2.2.2
  have hK₁ : Nontrivial K := (QuotientGroup.mk'_surjective (Subgroup.center K)).nontrivial
  exact K.nontrivial_iff_ne_bot.mp hK₁ (eq_bot_of_isSubnormal_of_coprime hcore hK.2.1 hcop)

theorem not_le_of_normalizer_inf_le {p : ℕ} [Fact p.Prime] (R : Sylow p X) {N X₀ : Subgroup X}
    [N.Normal] (hN : Subgroup.normalizer (((R : Subgroup X) ⊓ N : Subgroup X) : Set X) ≤ X₀)
    (hX₀ : X₀ ≠ ⊤) : ¬ N ≤ X₀ := by
  intro hNX
  have hR : CFSG.ABGLocalTools.IsSylowOf p (R : Subgroup X) ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨le_top, R.isPGroup', by
      rw [Subgroup.relIndex_top_right]
      exact R.not_dvd_index⟩
  obtain ⟨S, hS⟩ := hR.inf_of_le_normalizer le_top (Subgroup.normalizer_eq_top N).ge
  have htop := Sylow.normalizer_sup_eq_top S
  rw [hS] at htop
  exact hX₀ (top_le_iff.mp (htop ▸ sup_le hN hNX))

theorem not_le_of_weakCore_le {p : ℕ} (hp : p.Prime) (R : Sylow p X) {N X₀ : Subgroup X}
    [N.Normal] (hW : GLBWeakCore p (R : Subgroup X) ≤ X₀) (hX₀ : X₀ ≠ ⊤)
    (hrank : 3 ≤ Open.pRank p ((R : Subgroup X) ⊓ N)) : ¬ N ≤ X₀ := by
  have : Fact p.Prime := ⟨hp⟩
  exact not_le_of_normalizer_inf_le R ((normalizer_le_weakCore p inf_le_left (by omega)
    (hrank.trans (PreuniquenessRankFour.Helpers.pRank_mono p hp le_sup_left))).trans hW) hX₀

theorem not_layer_le_of_weakCore_le {p : ℕ} (hp : p.Prime)
    (hcore : primeComplementCore (G := X) p = ⊥) (R : Sylow p X) {X₀ : Subgroup X}
    (hW : GLBWeakCore p (R : Subgroup X) ≤ X₀) (hX₀ : X₀ ≠ ⊤)
    (hrank : 3 ≤ Open.pRank p ((R : Subgroup X) ⊓ CFSG.generalizedFitting X)) :
    ¬ CFSG.layer X ≤ X₀ := by
  have : Fact p.Prime := ⟨hp⟩
  have : (CFSG.generalizedFitting X).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  have hpR : CFSG.pCore p X ≤ R :=
    sSup_le fun K ⟨hKn, hKp⟩ => @IsPGroup.le_sylow_of_normal _ _ _ K hKn hKp R
  have hF : fittingSubgroup X ≤ X₀ := by
    rw [CFSG.Fitting_eq_pcore X p hcore]
    exact hpR.trans ((subgroup_le_weakCore_of_rank p hp _ (hrank.trans
      (PreuniquenessRankFour.Helpers.pRank_mono p hp inf_le_left))).trans hW)
  exact fun hE => not_le_of_weakCore_le hp R hW hX₀ hrank (sup_le hF hE)

end Reduced

theorem exists_isElemAbelian_lift {Y : Type*} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (O : Subgroup Y) [O.Normal] (hO : p.Coprime (Nat.card O)) {T : Subgroup Y}
    (hT : IsPGroup p T) {E : Subgroup (Y ⧸ O)} (hE : IsElemAbelian p E)
    (hET : E ≤ T.map (QuotientGroup.mk' O)) :
    ∃ E₁ ≤ T, E₁.map (QuotientGroup.mk' O) = E ∧ IsElemAbelian p E₁ ∧
      Nat.card E₁ = Nat.card E := by
  have hinj : ∀ a ∈ T, ∀ b ∈ T, QuotientGroup.mk' O a = QuotientGroup.mk' O b → a = b := by
    intro a ha b hb hab
    have hmem : a⁻¹ * b ∈ T ⊓ O := ⟨T.mul_mem (T.inv_mem ha) hb, QuotientGroup.eq.mp hab⟩
    rwa [inf_eq_bot_of_isPGroup hp hT hO, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  have hmap : (E.comap (QuotientGroup.mk' O) ⊓ T).map (QuotientGroup.mk' O) = E :=
    map_comap_inf_eq _ hET
  refine ⟨E.comap (QuotientGroup.mk' O) ⊓ T, inf_le_right, hmap, ⟨?_, fun x hx => ?_⟩, ?_⟩
  · refine IsMulCommutative.of_comm fun x y => Subtype.ext
      (hinj _ (T.mul_mem x.2.2 y.2.2) _ (T.mul_mem y.2.2 x.2.2) ?_)
    simp only [Subgroup.coe_mul, map_mul]
    exact congrArg Subtype.val ((isMulCommutative_iff.mp hE.1) ⟨_, x.2.1⟩ ⟨_, y.2.1⟩)
  · refine hinj _ (T.pow_mem hx.2 p) _ T.one_mem ?_
    rw [map_pow, map_one]
    exact hE.2 _ hx.1
  · rw [← card_map_mk_of_isPGroup hp O hO (hT.to_le inf_le_right), hmap]

structure ReducedNongeneration (p : ℕ) (X : Type*) [Group X] [Finite X] (R : Sylow p X)
    (X₀ : Subgroup X) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  core_eq_bot : primeComplementCore (G := X) p = ⊥
  three_le_pRank : 3 ≤ Open.pRank p (R : Subgroup X)
  weakCore_le : GLBWeakCore p (R : Subgroup X) ≤ X₀
  hyperplane_le : ∀ E : Subgroup X, IsElemAbelian p E → Nat.card E = p ^ 3 → E ≤ R →
    ∀ F : Subgroup X, F ≤ E → F.relIndex E = p → Subgroup.centralizer (F : Set X) ≤ X₀
  ne_top : X₀ ≠ ⊤
  pRank_inf_conj_le : ∀ x : X, x ∉ X₀ → Open.pRank p (X₀ ⊓ GLBConj x X₀) ≤ 2

theorem D1Escape.reducedNongeneration {G : Type*} [Group G] [Finite G] {p : ℕ} {P : Sylow p G}
    {M H R : Subgroup G} (h : D1Escape p P M H R) :
    ∃ Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) ∧
      ReducedNongeneration p (H ⧸ primeComplementCore (G := H) p) Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨T, hT⟩ := h.isSylow
  have hTR : (T : Subgroup H) = R.subgroupOf H := by
    rw [← hT, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hO : p.Coprime (Nat.card (primeComplementCore (G := H) p)) :=
    primeComplementCore_coprime p
  have hOM : primeComplementCore (G := H) p ≤ (H ⊓ M).subgroupOf H := by
    rw [← glbPrimeCore_subgroupOf]
    exact glbPrimeCore_subgroupOf_le_inf h.primeCore_le
  have hRH : (R.subgroupOf H).map H.subtype = R := Subgroup.map_subgroupOf_eq_of_le h.le_H
  have hRp : IsPGroup p (R.subgroupOf H) := hTR ▸ T.isPGroup'
  refine ⟨T.mapSurjective (QuotientGroup.mk'_surjective _), by
    rw [Sylow.coe_mapSurjective, hTR], ⟨h.prime, h.ne_two, primeComplementCore_quotient_eq_bot p,
    ?_, ?_, ?_, ?_, fun x hx => h.pRank_quotient_inf_conj_le_two _ hO hOM hx⟩⟩
  · rw [Sylow.coe_mapSurjective, hTR, pRank_map_mk_eq_pRank_map_subtype h.prime _ hO, hRH]
    exact h.three_le_pRank
  · rw [Sylow.coe_mapSurjective, hTR]
    exact weakCore_map_le_map_inf_of_coprime h.prime P h.weakCore_le h.le_P h.le_H _ hO hOM
  ·
    intro E hE hEcard hER F hFE hFidx
    rw [Sylow.coe_mapSurjective, hTR] at hER
    obtain ⟨E₁, hE₁R, hE₁map, hE₁, hE₁card⟩ := exists_isElemAbelian_lift h.prime _ hO hRp hE hER
    have hE₁H : (E₁.map H.subtype).subgroupOf H = E₁ :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    have hle := hyperplane_centralizers_map_le_map_inf_of_coprime h.prime P h.weakCore_le
      (elementary_abelian_map p hE₁ H.subtype)
      (by rw [Subgroup.card_map_of_injective H.subtype_injective, hE₁card, hEcard])
      ((Subgroup.map_mono hE₁R).trans (hRH.le.trans h.le_P)) (Subgroup.map_subtype_le _) _ hO hOM
    rw [hE₁H, hE₁map] at hle
    exact iSup₂_le_iff.mp hle F ⟨hFE, hFidx⟩
  ·
    intro htop
    apply h.not_le
    have hcomap := Subgroup.comap_map_eq (QuotientGroup.mk' (primeComplementCore (G := H) p))
      ((H ⊓ M).subgroupOf H)
    rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk', sup_eq_left.mpr hOM] at hcomap
    intro g hg
    have hmem : (⟨g, hg⟩ : H) ∈ (H ⊓ M).subgroupOf H := hcomap ▸ Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp hmem).2

end CFSG.AGLEmbedding
