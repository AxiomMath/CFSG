module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeKill
import CFSG.LocalAnalysis.AGLEmbedding.CoverAbelianSylowAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open
open scoped commutatorElement

section Transport

variable {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] {p : ℕ}

theorem map_glbWeakCore_le (hp : p.Prime) (f : X →* Y) (hf : Function.Injective f)
    (P : Subgroup X) : (GLBWeakCore p P).map f ≤ GLBWeakCore p (P.map f) := by
  rw [Subgroup.map_le_iff_le_comap, PreuniquenessRankFour.Helpers.weakCore_le_iff]
  intro Q hQP hQ2 hQ3
  rw [← Subgroup.map_le_iff_le_comap]
  have hmap : (Q ⊔ (P ⊓ Subgroup.centralizer (Q : Set X))).map f ≤
      Q.map f ⊔ (P.map f ⊓ Subgroup.centralizer ((Q.map f : Subgroup Y) : Set Y)) := by
    rw [Subgroup.map_sup]
    refine sup_le_sup_left ((Subgroup.map_inf_le _ _ _).trans (inf_le_inf_left _ ?_)) _
    rw [Subgroup.coe_map]
    exact Subgroup.map_centralizer_le_centralizer_image _ f
  refine (Subgroup.le_normalizer_map f).trans
    (PreuniquenessRankFour.Helpers.normalizer_le_weakCore p (Subgroup.map_mono hQP) ?_ ?_)
  · rwa [PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp f hf]
  · refine le_trans ?_ (PreuniquenessRankFour.Helpers.pRank_mono p hp hmap)
    rwa [PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp f hf]

theorem glbWeakCore_eq_top_of_mulEquiv (hp : p.Prime) (f : X ≃* Y) {P : Subgroup X}
    {P' : Subgroup Y} (hP : P' = P.map f.toMonoidHom) (h : GLBWeakCore p P = ⊤) :
    GLBWeakCore p P' = ⊤ := by
  have h1 := map_glbWeakCore_le hp f.toMonoidHom f.injective P
  rw [h, Subgroup.map_top_of_surjective _ f.surjective, ← hP] at h1
  exact eq_top_iff.mpr h1

theorem klingenAlt_of_mulEquiv [Fact p.Prime] (f : X ≃* Y) {T : Sylow p X} {T' : Sylow p Y}
    (hT : (T' : Subgroup Y) = (T : Subgroup X).map f.toMonoidHom) (h : KlingenAlt p X T) :
    KlingenAlt p Y T' := by
  obtain ⟨E, D, L, hET, hEcard, hEexp, hZE, hDE, hDel, hDcard, hDC, hLC, ⟨e, hSL⟩, hgD, hgL⟩ :=
    h
  have hp : p.Prime := Fact.out
  have hinj : Function.Injective f.toMonoidHom := f.injective
  have hsurj : Function.Surjective f.toMonoidHom := f.surjective
  let φ : E ≃* E.map f.toMonoidHom := Subgroup.equivMapOfInjective E f.toMonoidHom hinj
  have hφ : ∀ u : E, ((φ u : E.map f.toMonoidHom) : Y) = f.toMonoidHom (u : X) := fun _ => rfl
  have hZmap : ∀ w : Subgroup.center (E.map f.toMonoidHom), ∃ z : Subgroup.center E,
      ((w : E.map f.toMonoidHom) : Y) = f.toMonoidHom ((z : E) : X) := by
    intro w
    refine ⟨(Subgroup.centerCongr φ).symm w, ?_⟩
    rw [← hφ]
    congr 2
    exact (congrArg Subtype.val ((Subgroup.centerCongr φ).apply_symm_apply w)).symm
  have hW := map_glbWeakCore_le hp f.toMonoidHom hinj (T : Subgroup X)
  rw [← hT] at hW
  refine ⟨E.map f.toMonoidHom, D.map f.toMonoidHom, L.map f.toMonoidHom,
    (Subgroup.map_mono hET).trans hT.ge, ?_, ?_, ?_, Subgroup.map_mono hDE,
    PreuniquenessRankFour.Helpers.elementary_abelian_map p hDel f.toMonoidHom, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hinj, hEcard]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hEexp x hx, map_one]
  · rw [← hZE]
    exact (Nat.card_congr (Subgroup.centerCongr φ).toEquiv).symm
  · rw [Subgroup.card_map_of_injective hinj, hDcard]
  · rintro _ ⟨d, hd, rfl⟩ hdT
    have hdT' : d ∈ Subgroup.centralizer ((T : Subgroup X) : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      apply hinj
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_iff.mp hdT (f.toMonoidHom t) (hT.ge ⟨t, ht, rfl⟩)
    obtain ⟨z, hz, hzd⟩ := hDC d hd hdT'
    refine ⟨Subgroup.centerCongr φ ⟨z, hz⟩, (Subgroup.centerCongr φ ⟨z, hz⟩).2, ?_⟩
    show (((Subgroup.centerCongr φ ⟨z, hz⟩ : Subgroup.center (E.map f.toMonoidHom)) :
        E.map f.toMonoidHom) : Y) = f.toMonoidHom d
    rw [← hzd]
    rfl
  · rintro _ ⟨l, hl, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨z, hz⟩ := hZmap ⟨w, hw⟩
    have hlz := Subgroup.mem_centralizer_iff.mp (hLC hl) ((z : E) : X) ⟨z, z.2, rfl⟩
    show ((w : E.map f.toMonoidHom) : Y) * f.toMonoidHom l =
      f.toMonoidHom l * ((w : E.map f.toMonoidHom) : Y)
    have hz' : ((w : E.map f.toMonoidHom) : Y) = f.toMonoidHom ((z : E) : X) := hz
    rw [hz', ← map_mul, ← map_mul, hlz]
  · refine ⟨_, statedSL_le_map_centerQuotientAction_of_mulEquiv φ e hSL ?_⟩
    intro g hgL hgN
    refine ⟨f.toMonoidHom g, Subgroup.mem_map_of_mem _ hgL,
      Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ hgN), ?_⟩
    intro u v huv
    rw [hφ, hφ, huv, map_mul, map_mul, map_inv]
  · rw [eq_top_iff]
    calc (⊤ : Subgroup Y) = (GLBWeakCore p (T : Subgroup X) ⊔
          Subgroup.normalizer (D : Set X)).map f.toMonoidHom := by
          rw [hgD, Subgroup.map_top_of_surjective _ hsurj]
      _ = (GLBWeakCore p (T : Subgroup X)).map f.toMonoidHom ⊔
          (Subgroup.normalizer (D : Set X)).map f.toMonoidHom := Subgroup.map_sup _ _ _
      _ ≤ _ := sup_le_sup hW (Subgroup.le_normalizer_map _)
  · rw [eq_top_iff]
    calc (⊤ : Subgroup Y) = (GLBWeakCore p (T : Subgroup X) ⊔ L).map f.toMonoidHom := by
          rw [hgL, Subgroup.map_top_of_surjective _ hsurj]
      _ = (GLBWeakCore p (T : Subgroup X)).map f.toMonoidHom ⊔ L.map f.toMonoidHom :=
          Subgroup.map_sup _ _ _
      _ ≤ _ := sup_le_sup_right hW _

end Transport

theorem commute_of_isCyclic_map_mk {K : Type*} [Group K] {T : Subgroup K}
    (h : IsCyclic (T.map (QuotientGroup.mk' (Subgroup.center K)))) {x y : K} (hx : x ∈ T)
    (hy : y ∈ T) : x * y = y * x := by
  have hf : ((QuotientGroup.mk' (Subgroup.center K)).subgroupMap T).ker ≤
      Subgroup.center T := by
    intro t ht
    rw [MonoidHom.mem_ker] at ht
    have htZ : (t : K) ∈ Subgroup.center K :=
      (QuotientGroup.eq_one_iff (t : K)).mp (congrArg Subtype.val ht)
    exact Subgroup.mem_center_iff.mpr fun s => Subtype.ext (Subgroup.mem_center_iff.mp htZ s)
  have := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center _ hf
  exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : T) ⟨y, hy⟩)

theorem pow_eq_one_of_card_eq_sq {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p ^ 2) (hc : ¬ IsCyclic G) (g : G) : g ^ p = 1 := by
  obtain ⟨m, hm, hgm⟩ := (Nat.dvd_prime_pow hp).mp (hG ▸ orderOf_dvd_natCard g)
  have hm1 : m ≤ 1 := by
    by_contra h
    exact hc (isCyclic_of_orderOf_eq_card g (by rw [hgm, hG, show m = 2 by omega]))
  rw [← orderOf_dvd_iff_pow_eq_one, hgm]
  exact (Nat.pow_dvd_pow p hm1).trans (by rw [pow_one])

theorem pRank_le_two_of_card_eq_pow_three {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {T : Subgroup G} (hT : Nat.card T = p ^ 3)
    (hnc : ∃ a ∈ T, ∃ b ∈ T, a * b ≠ b * a) : Open.pRank p T ≤ 2 := by
  refine SectionRank.pRank_le hp.one_lt fun E hET hE => ?_
  obtain ⟨j, hj, hEj⟩ := (Nat.dvd_prime_pow hp).mp (hT ▸ Subgroup.card_dvd_of_le hET)
  rw [hEj]
  refine Nat.pow_le_pow_right hp.pos ?_
  by_contra h2
  have hEq : E = T := Subgroup.eq_of_le_of_card_ge hET (by rw [hT, hEj, show j = 3 by omega])
  obtain ⟨a, ha, b, hb, hab⟩ := hnc
  have := hE.1
  rw [← hEq] at ha hb
  exact hab (congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : E) ⟨b, hb⟩))

section Order

variable {K : Type} [Group K] [Finite K] [Group.IsPerfect K] {p : ℕ} [Fact p.Prime]

theorem center_le_commutator_sylow (hZp : IsPGroup p (Subgroup.center K)) (T : Sylow p K) :
    Subgroup.center K ≤ ⁅(T : Subgroup K), (T : Subgroup K)⁆ := fun z hz => by
  obtain ⟨n, hn⟩ := hZp ⟨z, hz⟩
  exact center_le_commutator_of_isPerfect T hz ⟨n, congrArg Subtype.val hn⟩

theorem card_center_eq_of_commutator (hZ : Subgroup.center K ≠ ⊥)
    (hZp : IsPGroup p (Subgroup.center K)) (hZc : IsCyclic (Subgroup.center K)) (T : Sylow p K)
    (hc : ∀ x ∈ (T : Subgroup K), ∀ y ∈ (T : Subgroup K), ⁅x, y⁆ ∈ Subgroup.center K)
    (hcp : ∀ x ∈ (T : Subgroup K), ∀ y ∈ (T : Subgroup K), ⁅x, y⁆ ^ p = 1) :
    Nat.card (Subgroup.center K) = p := by
  have hp : p.Prime := Fact.out
  have hT' : ∀ z ∈ ⁅(T : Subgroup K), (T : Subgroup K)⁆, z ∈ Subgroup.center K ∧ z ^ p = 1 := by
    intro z hz
    rw [Subgroup.commutator_def] at hz
    induction hz using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      exact ⟨hc a ha b hb, hcp a ha b hb⟩
    | one => exact ⟨Subgroup.one_mem _, one_pow p⟩
    | mul x y _ _ hx hy =>
      refine ⟨Subgroup.mul_mem _ hx.1 hy.1, ?_⟩
      have hxy : Commute x y := Subgroup.mem_center_iff.mp hy.1 x
      rw [hxy.mul_pow, hx.2, hy.2, one_mul]
    | inv x _ hx => exact ⟨Subgroup.inv_mem _ hx.1, by rw [inv_pow, hx.2, inv_one]⟩
  have hZexp : ∀ z ∈ Subgroup.center K, z ^ p = 1 := fun z hz =>
    (hT' z (center_le_commutator_sylow hZp T hz)).2
  have hdvd : Nat.card (Subgroup.center K) ∣ p := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
      Subtype.ext (by simpa using hZexp _ g.2)
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact absurd (Subgroup.card_eq_one.mp h) hZ
  · exact h

theorem pRank_le_two_of_not_dvd_card (hZp : IsPGroup p (Subgroup.center K))
    (hZc : IsCyclic (Subgroup.center K)) (h3 : ¬ p ^ 3 ∣ Nat.card (K ⧸ Subgroup.center K))
    (T : Sylow p K) :
    Open.pRank p (T : Subgroup K) ≤ 2 ∧
      (Subgroup.center K = ⊥ ∨ Nat.card (T : Subgroup K) = p ^ 3) := by
  have hp : p.Prime := Fact.out
  have hTZ : Subgroup.comap (QuotientGroup.mk' (Subgroup.center K))
      ((T : Subgroup K).map (QuotientGroup.mk' (Subgroup.center K))) = T :=
    Subgroup.comap_map_eq_self (by
      rw [QuotientGroup.ker_mk']
      exact IsPGroup.le_sylow_of_normal hZp T)
  have hTcard : Nat.card (T : Subgroup K) = Nat.card (Subgroup.center K) *
      Nat.card ((T : Subgroup K).map (QuotientGroup.mk' (Subgroup.center K))) := by
    have h := QuotientGroup.card_preimage_mk (Subgroup.center K)
      (((T : Subgroup K).map (QuotientGroup.mk' (Subgroup.center K)) : Subgroup _) : Set _)
    conv_lhs => rw [← hTZ]
    exact h
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
    (T.isPGroup'.map (QuotientGroup.mk' (Subgroup.center K)))
  have hk2 : k ≤ 2 := by
    by_contra hk3
    exact h3 ((pow_dvd_pow p (by omega)).trans (hk ▸ Subgroup.card_subgroup_dvd_card _))
  by_cases hZ : Subgroup.center K = ⊥
  · refine ⟨SectionRank.pRank_le hp.one_lt fun E hET _ => ?_, Or.inl hZ⟩
    refine (Subgroup.card_le_of_le hET).trans ?_
    rw [hTcard, Subgroup.card_eq_one.mpr hZ, one_mul, hk]
    exact Nat.pow_le_pow_right hp.pos hk2
  have hZT' := center_le_commutator_sylow hZp T
  have hnc : ¬ ∀ x ∈ (T : Subgroup K), ∀ y ∈ (T : Subgroup K), x * y = y * x := by
    intro h
    apply hZ
    have hbot : ⁅(T : Subgroup K), (T : Subgroup K)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => h y hy x hx
    exact le_bot_iff.mp (hbot ▸ hZT')
  have hcyc : ¬ IsCyclic ((T : Subgroup K).map (QuotientGroup.mk' (Subgroup.center K))) :=
    fun h => hnc fun x hx y hy => commute_of_isCyclic_map_mk h hx hy
  have hk2' : k = 2 := by
    by_contra hne
    apply hcyc
    interval_cases k
    · exact isCyclic_of_orderOf_eq_card 1 (by rw [orderOf_one, hk, pow_zero])
    · exact isCyclic_of_prime_card (by rw [hk, pow_one])
    · exact absurd rfl hne
  rw [hk2'] at hk
  have hexp := pow_eq_one_of_card_eq_sq hp hk hcyc
  have hc : ∀ x ∈ (T : Subgroup K), ∀ y ∈ (T : Subgroup K), ⁅x, y⁆ ∈ Subgroup.center K := by
    intro x hx y hy
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    have := IsPGroup.isMulCommutative_of_card_eq_prime_sq hk
    exact congrArg Subtype.val (mul_comm'
      (⟨_, Subgroup.mem_map_of_mem _ hx⟩ :
        (T : Subgroup K).map (QuotientGroup.mk' (Subgroup.center K)))
      ⟨_, Subgroup.mem_map_of_mem _ hy⟩)
  have hpow : ∀ x ∈ (T : Subgroup K), x ^ p ∈ Subgroup.center K := by
    intro x hx
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow]
    exact congrArg Subtype.val (hexp ⟨_, Subgroup.mem_map_of_mem _ hx⟩)
  have hcp : ∀ x ∈ (T : Subgroup K), ∀ y ∈ (T : Subgroup K), ⁅x, y⁆ ^ p = 1 := by
    intro x hx y hy
    rw [Commute.commutatorElement_pow_left (Subgroup.mem_center_iff.mp (hc x hx y hy) x),
      commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hpow x hx) y).symm
  have hT3 : Nat.card (T : Subgroup K) = p ^ 3 := by
    rw [hTcard, card_center_eq_of_commutator hZ hZp hZc T hc hcp, hk]
    ring
  refine ⟨pRank_le_two_of_card_eq_pow_three hp hT3 ?_, Or.inr hT3⟩
  push Not at hnc
  exact hnc

end Order

end CFSG.AGLEmbedding
