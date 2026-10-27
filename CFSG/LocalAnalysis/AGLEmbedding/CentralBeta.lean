module

public import CFSG.LocalAnalysis.AGLEmbedding.ComponentCase
public import CFSG.LocalAnalysis.AGLEmbedding.KFacts
public import CFSG.LocalAnalysis.AGLEmbedding.RankLemmas
import CFSG.LocalAnalysis.SectionRank.TwoGenerators

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

section Cyclic

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
private theorem card_le_of_isCyclic_of_forall_pow (p : ℕ) (hp : 0 < p) {D : Subgroup X}
    (hD : IsCyclic D) (hDp : ∀ d ∈ D, d ^ p = 1) : Nat.card D ≤ p := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := D)
  rw [← hg]
  exact Nat.le_of_dvd hp (orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hDp g g.2)))

private theorem pRank_le_one_of_isCyclic {p : ℕ} (hp : p.Prime) {C : Subgroup X}
    (hC : IsCyclic C) : Open.pRank p C ≤ 1 := CFSG.SectionRank.pRank_le_one_of_isCyclic hp hC

private theorem mem_zpowers_of_isCyclic {p : ℕ} (hp : p.Prime) {T : Subgroup X}
    (hT : IsCyclic T) {a b : X} (haT : a ∈ T) (ha : orderOf a = p) (hbT : b ∈ T)
    (hb : b ^ p = 1) : b ∈ Subgroup.zpowers a := by
  by_contra hba
  let _ : CommGroup T := IsCyclic.commGroup
  have hab : Commute a b := congrArg Subtype.val (mul_comm (⟨a, haT⟩ : T) ⟨b, hbT⟩)
  have h2 := two_le_pRank_of_commute_of_not_mem_zpowers hp ha hb hba hab haT hbT
  have h1 := pRank_le_one_of_isCyclic hp hT
  omega

private theorem commute_of_mem_normalizer_zpowers {p : ℕ} (hp : p.Prime) {t v : X}
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

end Cyclic

namespace ReducedNongeneration

section Beta

variable {p : ℕ} {X : Type*} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

theorem normalizer_inf_le_of_isCyclic_of_center (h : ReducedNongeneration p X R X₀) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X} [K.Normal]
    (hzK : z ∉ K) (hcyc : IsCyclic ((R : Subgroup X) ⊓ K : Subgroup X)) {t : X}
    (htRK : t ∈ (R : Subgroup X) ⊓ K) (ht : orderOf t = p) :
    Subgroup.normalizer (((R : Subgroup X) ⊓ K : Subgroup X) : Set X) ≤ X₀ := by
  have hp := h.prime
  have htp : t ^ p = 1 := ht ▸ pow_orderOf_eq_one t
  have hconj : ∀ g : X, g * t * g⁻¹ ∈ (R : Subgroup X) ⊓ K →
      g * t * g⁻¹ ∈ Subgroup.zpowers t := fun g hg =>
    mem_zpowers_of_isCyclic hp hcyc htRK ht hg (by rw [conj_pow, htp, mul_one, mul_inv_cancel])
  have hnorm : ∀ g : X, g * t * g⁻¹ ∈ (R : Subgroup X) ⊓ K →
      g ∈ Subgroup.normalizer (Subgroup.zpowers t : Set X) := by
    intro g hg
    apply mem_normalizer_of_conj_map_le
    rw [MonoidHom.map_zpowers]
    exact Subgroup.zpowers_le.mpr (hconj g hg)
  have hRconj : ∀ v ∈ (R : Subgroup X), v * t * v⁻¹ ∈ (R : Subgroup X) ⊓ K := fun v hv =>
    ⟨(R : Subgroup X).mul_mem ((R : Subgroup X).mul_mem hv htRK.1) ((R : Subgroup X).inv_mem hv),
      ‹K.Normal›.conj_mem t htRK.2 v⟩
  have hzR := mem_sylow_of_mem_center hz hzp R
  have hQR : Subgroup.zpowers t ⊔ Subgroup.zpowers z ≤ R :=
    sup_le (Subgroup.zpowers_le.mpr htRK.1) (Subgroup.zpowers_le.mpr hzR)
  have hQ2 : 2 ≤ Open.pRank p (Subgroup.zpowers t ⊔ Subgroup.zpowers z) :=
    two_le_pRank_of_commute_of_not_mem_zpowers hp ht (hzp ▸ pow_orderOf_eq_one z)
      (fun hzt => hzK (Subgroup.zpowers_le.mpr htRK.2 hzt)) (Subgroup.mem_center_iff.mp hz t)
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  obtain ⟨A, hAR, hA, hAcard⟩ := pRank_attained p hp (R : Subgroup X)
  have hAC : A ≤ (R : Subgroup X) ⊓
      Subgroup.centralizer ((Subgroup.zpowers t ⊔ Subgroup.zpowers z : Subgroup X) : Set X) := by
    refine le_inf hAR ?_
    rw [Subgroup.le_centralizer_iff]
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
        (commute_of_mem_normalizer_zpowers hp ht (hnorm v (hRconj v (hAR hv)))
          (hA.2 v hv)).eq
    · exact Subgroup.mem_centralizer_iff.mpr fun v _ => Subgroup.mem_center_iff.mp hz v
  have hNQ : Subgroup.normalizer
      ((Subgroup.zpowers t ⊔ Subgroup.zpowers z : Subgroup X) : Set X) ≤ X₀ :=
    (normalizer_le_weakCore p hQR hQ2 (h.three_le_pRank.trans
      ((le_csSup (pRank_bddAbove p hp _) ⟨A, hAC, hA, hAcard⟩).trans
        (pRank_mono p hp le_sup_right)))).trans h.weakCore_le
  intro g hg
  apply hNQ
  apply mem_normalizer_of_conj_map_le
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine sup_le ((Subgroup.zpowers_le.mpr ?_).trans le_sup_left) (Subgroup.zpowers_le.mpr ?_)
  · exact hconj g ((Subgroup.mem_normalizer_iff.mp hg t).mp htRK)
  · rw [Subgroup.mem_center_iff.mp hz g, mul_inv_cancel_right]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)

theorem center_eq_bot_and_rankOne_of_not_mem (h : ReducedNongeneration p X R X₀) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hzK : z ∉ K) :
    Subgroup.center K = ⊥ ∧ (¬ IsCyclic ((R : Subgroup X) ⊓ K : Subgroup X) →
      (∀ U : Subgroup X, U ≤ (R : Subgroup X) ⊓ K → U ≠ ⊥ →
        K ⊓ Subgroup.normalizer (U : Set X) ≤ X₀) ∧ ¬ K ≤ X₀) := by
  rcases h.mem_or_rankOne_of_center hz hzp hK with ⟨hzZ, -⟩ | ⟨-, hrk⟩
  · exact absurd (Subgroup.map_subtype_le _ hzZ) hzK
  · exact hrk

theorem not_le_of_not_mem_of_center (h : ReducedNongeneration p X R X₀) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hKn : K.Normal) (hzK : z ∉ K) : ¬ K ≤ X₀ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  by_cases hcyc : IsCyclic ((R : Subgroup X) ⊓ K : Subgroup X)
  · obtain ⟨t, htRK, ht, -⟩ := exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot R hK
    exact not_le_of_normalizer_inf_le R
      (h.normalizer_inf_le_of_isCyclic_of_center hz hzp hzK hcyc htRK ht) h.ne_top
  · exact ((h.center_eq_bot_and_rankOne_of_not_mem hz hzp hK hzK).2 hcyc).2

theorem isCyclic_inf_centralizer_of_not_mem_of_center (h : ReducedNongeneration p X R X₀)
    {z : X} (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hKn : K.Normal) (hzK : z ∉ K) (hZ : Subgroup.center K = ⊥) :
    IsCyclic ((R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) := by
  have hp := h.prime
  by_contra hnc
  obtain ⟨F, hF, hFel, hFcard⟩ := exists_isElemAbelian_card_sq_of_two_le_pRank hp
    (two_le_pRank_of_isPGroup_not_isCyclic hp h.ne_two (R.isPGroup'.to_le inf_le_left) hnc)
  obtain ⟨t, ⟨htR, htK⟩, ht, -⟩ := exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot R hK
  have hFC : F ≤ Subgroup.centralizer (K : Set X) := hF.trans inf_le_right
  have htF : t ∉ F := by
    intro htF
    have hmem : (⟨t, htK⟩ : K) ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun k =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp (hFC htF) k k.2)
    rw [hZ, Subgroup.mem_bot] at hmem
    have ht1 : t = 1 := congrArg Subtype.val hmem
    rw [ht1, orderOf_one] at ht
    exact hp.one_lt.ne ht
  have hN := h.normalizer_le_of_mem_centralizer htR htF ht
    (Subgroup.le_centralizer_iff.mp hFC htK) (hF.trans inf_le_left)
    (le_csSup (pRank_bddAbove p hp F) ⟨F, le_rfl, hFel, hFcard⟩)
  exact h.not_le_of_not_mem_of_center hz hzp hK hKn hzK
    ((Subgroup.le_centralizer_iff.mp hFC).trans ((Subgroup.centralizer_le_normalizer _).trans hN))

theorem glbCore_ne_top_of_rankOne (h : ReducedNongeneration p X R X₀) {K : Subgroup X}
    (hN : ∀ U : Subgroup X, U ≤ (R : Subgroup X) ⊓ K → U ≠ ⊥ →
      K ⊓ Subgroup.normalizer (U : Set X) ≤ X₀)
    (hKX₀ : ¬ K ≤ X₀) {T : Subgroup K} (hT : T.map K.subtype = (R : Subgroup X) ⊓ K) :
    GLBCore p 1 T ≠ ⊤ := by
  have hp := h.prime
  intro htop
  have hle : GLBCore p 1 T ≤ X₀.comap K.subtype := by
    rw [fullCore_le_iff]
    intro Q hQT hQ1 k hk
    have hQne : Q ≠ ⊥ := by
      rintro rfl
      obtain ⟨E, hE, -, hEcard⟩ := pRank_attained p hp (⊥ : Subgroup K)
      rw [le_bot_iff] at hE
      rw [hE, Subgroup.card_bot] at hEcard
      have h1 := Nat.pow_le_pow_right hp.pos hQ1
      rw [pow_one, ← hEcard] at h1
      exact absurd h1 (by have := hp.one_lt; omega)
    have hU : Q.map K.subtype ≤ (R : Subgroup X) ⊓ K := hT ▸ Subgroup.map_mono hQT
    have hUne : Q.map K.subtype ≠ ⊥ := by
      rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective]
    exact hN _ hU hUne ⟨k.2, Subgroup.le_normalizer_map K.subtype ⟨k, hk, rfl⟩⟩
  exact hKX₀ fun x hx => hle (htop ▸ Subgroup.mem_top (⟨x, hx⟩ : K))

end Beta

section Main

variable {p : ℕ} {X : Type} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

theorem rankOneLieAutFacts_of_not_mem (h : ReducedNongeneration p X R X₀)
    (hR4 : 4 ≤ Open.pRank p (R : Subgroup X)) (hX : CatalogSimpleSections X) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hKn : K.Normal) (hzK : z ∉ K) (hKF : KFactBeta) :
    Subgroup.center K = ⊥ ∧
      IsCyclic ((R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) ∧
      RankOneLieAutFacts p K := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hZ, hrk⟩ := h.center_eq_bot_and_rankOne_of_not_mem hz hzp hK hzK
  have hcycC := h.isCyclic_inf_centralizer_of_not_mem_of_center hz hzp hK hKn hzK hZ
  refine ⟨hZ, hcycC, ?_⟩
  let e : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2.2.2
  have hsimple : IsSimpleGroup K := e.isSimpleGroup
  have hnonab : ∃ a b : K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.2.2
    refine ⟨e.symm a, e.symm b, fun hba => hab ?_⟩
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e hba
  have hcat : IsCatalogGroup K :=
    IsCatalogGroup.of_mulEquiv e (hX.isCatalogGroup_center_quotient hK)
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal R hKn.isSubnormal
  obtain ⟨t, htRK, ht, -⟩ := exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot R hK
  have hTne : (T : Subgroup K) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.map_bot] at hT
    have ht1 : t ∈ (⊥ : Subgroup X) := by
      rw [hT]
      exact htRK
    rw [Subgroup.mem_bot] at ht1
    rw [ht1, orderOf_one] at ht
    exact hp.one_lt.ne ht
  have hcond : IsCyclic (T : Subgroup K) ∨ GLBCore p 1 (T : Subgroup K) ≠ ⊤ := by
    by_cases hTc : IsCyclic (T : Subgroup K)
    · exact Or.inl hTc
    · refine Or.inr ?_
      have hnc : ¬ IsCyclic ((R : Subgroup X) ⊓ K : Subgroup X) := by
        intro hc
        rw [← hT] at hc
        exact hTc (isCyclic_of_surjective
          (Subgroup.equivMapOfInjective _ _ K.subtype_injective).symm (MulEquiv.surjective _))
      obtain ⟨hN, hKX₀⟩ := hrk hnc
      exact h.glbCore_ne_top_of_rankOne hN hKX₀ hT
  rcases hKF K hsimple hnonab hcat p hp h.ne_two T hTne hcond with hAut | hfacts
  · exfalso
    have hineq := pRank_le_pRank_inf_centralizer_add_pRank_map_conjNormal hp K (R : Subgroup X)
    have h1 := pRank_le_one_of_isCyclic hp hcycC
    have h2 := (pRank_mono p hp (le_top : (R : Subgroup X).map (MulAut.conjNormal (H := K)) ≤
      ⊤)).trans hAut
    have h3 := hineq.trans (Nat.add_le_add h1 h2)
    omega
  · exact hfacts

end Main

end ReducedNongeneration

theorem inf_centralizer_eq_center_map_of_isCyclic {p : ℕ} {X : Type*} [Group X] [Finite X]
    {R E K : Subgroup X} {z : X} (hER : E ≤ R) (hEp : ∀ e ∈ E, e ^ p = 1)
    (hZE : (Subgroup.center E).map E.subtype = Subgroup.zpowers z)
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p)
    (hcyc : IsCyclic (R ⊓ Subgroup.centralizer (K : Set X) : Subgroup X)) :
    E ⊓ Subgroup.centralizer (K : Set X) = (Subgroup.center E).map E.subtype := by
  have hzZ : z ∈ (Subgroup.center E).map E.subtype := by
    rw [hZE]
    exact Subgroup.mem_zpowers z
  have hle : Subgroup.zpowers z ≤ E ⊓ Subgroup.centralizer (K : Set X) :=
    Subgroup.zpowers_le.mpr ⟨Subgroup.map_subtype_le _ hzZ, Subgroup.center_le_centralizer _ hz⟩
  have : IsCyclic (E ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) :=
    Subgroup.isCyclic_of_le (inf_le_inf_right _ hER)
  rw [hZE]
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_zpowers, hzp]
  exact card_le_of_isCyclic_of_forall_pow p (hzp ▸ orderOf_pos z) this fun d hd => hEp d hd.1

end CFSG.AGLEmbedding
