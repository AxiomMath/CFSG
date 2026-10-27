module

public import CFSG.LocalAnalysis.AGLEmbedding.ReducedComponents
public import CFSG.LocalAnalysis.AGLEmbedding.ReducedOrbitsAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

namespace ReducedNongeneration

variable {p : ℕ} {X : Type*} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

theorem center_eq_bot_of_isCyclic (h : ReducedNongeneration p X R X₀) {L : Subgroup X}
    (hL : IsComponentOf L ⊤) (hcyc : IsCyclic ((R : Subgroup X) ⊓ L : Subgroup X)) :
    Subgroup.center L = ⊥ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal R
    (ComponentClassification.Components.mathlib_subnormal_of_chain hL.2.1
      Subgroup.IsSubnormal.top)
  rw [← hP] at hcyc
  have : IsCyclic (P : Subgroup L) :=
    isCyclic_of_surjective (Subgroup.equivMapOfInjective _ _ L.subtype_injective).symm
      (MulEquiv.surjective _)
  have hZ := isPGroup_center_of_isComponentOf hp h.core_eq_bot hL
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  obtain ⟨k, hk⟩ := hZ ⟨g, hg⟩
  exact eq_one_of_mem_center_of_pow_eq_one hL.2.2.1 P hg (by simpa using congrArg Subtype.val hk)

theorem false_of_forall_component_le (h : ReducedNongeneration p X R X₀)
    (hall : ∀ L : Subgroup X, IsComponentOf L ⊤ → L ≤ X₀)
    (hrank : 3 ≤ Open.pRank p ((R : Subgroup X) ⊓ CFSG.layer X)) : False :=
  not_layer_le_of_weakCore_le h.prime h.core_eq_bot R h.weakCore_le h.ne_top
    (hrank.trans (PreuniquenessRankFour.Helpers.pRank_mono p h.prime
      (inf_le_inf_left _ le_sup_right)))
    (sSup_le fun L hL => hall L ((CFSG.isComponent_iff_open L).mp hL))

theorem two_le_pRank_inf_sup_component (h : ReducedNongeneration p X R X₀) {L₂ L₃ : Subgroup X}
    (h₂ : IsComponentOf L₂ ⊤) (h₃ : IsComponentOf L₃ ⊤) (hne : L₂ ≠ L₃) :
    2 ≤ Open.pRank p ((R : Subgroup X) ⊓ (L₂ ⊔ L₃)) := by
  have hp := h.prime
  obtain ⟨t₂, ⟨ht₂R, ht₂L⟩, ht₂, ht₂Z⟩ :=
    exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot R h₂
  obtain ⟨t₃, ⟨ht₃R, ht₃L⟩, ht₃, -⟩ :=
    exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot R h₃
  have h₃₂ := le_centralizer_of_component_ne h₃ h₂ hne.symm
  exact two_le_pRank_of_commute_of_not_mem_zpowers hp ht₃ (ht₂ ▸ pow_orderOf_eq_one t₂)
    (fun ht => ht₂Z (Subgroup.zpowers_le.mpr (h₃₂ ht₃L) ht))
    (Subgroup.mem_centralizer_iff.mp (h₃₂ ht₃L) t₂ ht₂L).symm
    ⟨ht₃R, Subgroup.mem_sup_right ht₃L⟩ ⟨ht₂R, Subgroup.mem_sup_left ht₂L⟩

theorem exists_of_three_components (h : ReducedNongeneration p X R X₀) {L₁ L₂ L₃ : Subgroup X}
    (h₁ : IsComponentOf L₁ ⊤) (h₂ : IsComponentOf L₂ ⊤) (h₃ : IsComponentOf L₃ ⊤)
    (h₁₂ : L₁ ≠ L₂) (h₁₃ : L₁ ≠ L₃) (h₂₃ : L₂ ≠ L₃) :
    ∃ E ≤ (R : Subgroup X) ⊓ (L₂ ⊔ L₃), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      L₁ ≤ Subgroup.centralizer (E : Set X) ∧
      ∃ t ∈ (R : Subgroup X) ⊓ L₁, orderOf t = p ∧ t ∉ E := by
  obtain ⟨E, hE, hEel, hEcard⟩ := exists_isElemAbelian_card_sq_of_two_le_pRank h.prime
    (h.two_le_pRank_inf_sup_component h₂ h₃ h₂₃)
  obtain ⟨t, htRL, ht, htZ⟩ := exists_mem_sylow_inf_component h.prime h.ne_two h.core_eq_bot R h₁
  have hEC : E ≤ Subgroup.centralizer (L₁ : Set X) :=
    (hE.trans inf_le_right).trans (sup_le (le_centralizer_of_component_ne h₂ h₁ h₁₂.symm)
      (le_centralizer_of_component_ne h₃ h₁ h₁₃.symm))
  exact ⟨E, hE, hEel, hEcard, Subgroup.le_centralizer_iff.mp hEC, t, htRL, ht,
    fun htE => htZ (hEC htE)⟩

theorem le_of_three_components (h : ReducedNongeneration p X R X₀) {L₁ L₂ L₃ : Subgroup X}
    (h₁ : IsComponentOf L₁ ⊤) (h₂ : IsComponentOf L₂ ⊤) (h₃ : IsComponentOf L₃ ⊤)
    (h₁₂ : L₁ ≠ L₂) (h₁₃ : L₁ ≠ L₃) (h₂₃ : L₂ ≠ L₃) : L₁ ≤ X₀ := by
  have hp := h.prime
  obtain ⟨E, hE, hEel, hEcard, hLE, t, ⟨htR, htL⟩, ht, htE⟩ :=
    h.exists_of_three_components h₁ h₂ h₃ h₁₂ h₁₃ h₂₃
  have hN : Subgroup.normalizer (E : Set X) ≤ X₀ :=
    (normalizer_le_weakCore p (hE.trans inf_le_left)
      (le_csSup (pRank_bddAbove p hp E) ⟨E, le_rfl, hEel, hEcard⟩)
      (three_le_pRank_of_isElemAbelian_sq_of_mem_centralizer hp hEel hEcard ht htE (hLE htL)
        le_sup_left (Subgroup.mem_sup_right ⟨htR, hLE htL⟩))).trans h.weakCore_le
  exact (hLE.trans (Subgroup.centralizer_le_normalizer _)).trans hN

theorem false_of_three_components (h : ReducedNongeneration p X R X₀) {L₁ L₂ L₃ : Subgroup X}
    (h₁ : IsComponentOf L₁ ⊤) (h₂ : IsComponentOf L₂ ⊤) (h₃ : IsComponentOf L₃ ⊤)
    (h₁₂ : L₁ ≠ L₂) (h₁₃ : L₁ ≠ L₃) (h₂₃ : L₂ ≠ L₃) : False := by
  refine h.false_of_forall_component_le (fun L hL => ?_) ?_
  · by_cases hL₁ : L = L₁
    · rw [hL₁]
      exact h.le_of_three_components h₁ h₂ h₃ h₁₂ h₁₃ h₂₃
    by_cases hL₂ : L = L₂
    · rw [hL₂]
      exact h.le_of_three_components h₂ h₁ h₃ h₁₂.symm h₂₃ h₁₃
    exact h.le_of_three_components hL h₁ h₂ hL₁ hL₂ h₁₂
  · obtain ⟨E, hE, hEel, hEcard, hLE, t, ⟨htR, htL⟩, ht, htE⟩ :=
      h.exists_of_three_components h₁ h₂ h₃ h₁₂ h₁₃ h₂₃
    exact three_le_pRank_of_isElemAbelian_sq_of_mem_centralizer h.prime hEel hEcard ht htE
      (hLE htL) (hE.trans (inf_le_inf_left _
        (sup_le (le_layer_of_isComponentOf h₂) (le_layer_of_isComponentOf h₃))))
      ⟨htR, le_layer_of_isComponentOf h₁ htL⟩

theorem sylow_le_normalizer_component (h : ReducedNongeneration p X R X₀) {L : Subgroup X}
    (hL : IsComponentOf L ⊤) : (R : Subgroup X) ≤ Subgroup.normalizer (L : Set X) := by
  intro r hr
  by_contra hrN
  have hp := h.prime
  let f : X →* X := (MulAut.conj r).toMonoidHom
  have hL₁ : IsComponentOf (L.map f) ⊤ :=
    (ComponentClassification.LocalComponents.equiv_iff (MulAut.conj r) L).mpr hL
  have hL₂ : IsComponentOf ((L.map f).map f) ⊤ :=
    (ComponentClassification.LocalComponents.equiv_iff (MulAut.conj r) _).mpr hL₁
  have h₀₁ : L ≠ L.map f := fun heq => hrN (mem_normalizer_of_conj_map_le heq.ge)
  have h₁₂ : L.map f ≠ (L.map f).map f :=
    fun heq => h₀₁ (Subgroup.map_injective (MulAut.conj r).injective heq)
  refine h.false_of_three_components hL hL₁ hL₂ h₀₁ (fun heq => ?_) h₁₂
  have hcomp : (MulAut.conj (r ^ 2)).toMonoidHom = f.comp f := by
    ext x
    simp [f, pow_two, mul_assoc]
  have hr2 : r ^ 2 ∈ Subgroup.normalizer (L : Set X) := by
    refine mem_normalizer_of_conj_map_le (le_of_eq ?_)
    rw [hcomp, ← Subgroup.map_map, ← heq]
  obtain ⟨k, hk⟩ := R.isPGroup' ⟨r, hr⟩
  have hrk : r ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨m, hm⟩ : Odd (orderOf r) :=
    Odd.of_dvd_nat (hp.odd_of_ne_two h.ne_two).pow (orderOf_dvd_of_pow_eq_one hrk)
  have hreq : (r ^ 2) ^ (m + 1) = r := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf r + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  exact hrN (hreq ▸ Subgroup.pow_mem _ hr2 (m + 1))

theorem normalizer_le_of_mem_centralizer (h : ReducedNongeneration p X R X₀) {U : Subgroup X}
    {z : X} (hzR : z ∈ (R : Subgroup X)) (hzU : z ∉ U) (hzp : orderOf z = p)
    (hzC : z ∈ Subgroup.centralizer (U : Set X)) (hUR : U ≤ R) (hU : 2 ≤ Open.pRank p U) :
    Subgroup.normalizer (U : Set X) ≤ X₀ := by
  obtain ⟨E, hEU, hE, hEcard⟩ := exists_isElemAbelian_card_sq_of_two_le_pRank h.prime hU
  exact (normalizer_le_weakCore p hUR hU
    (three_le_pRank_of_isElemAbelian_sq_of_mem_centralizer h.prime hE hEcard hzp
      (fun hzE => hzU (hEU hzE)) (Subgroup.centralizer_le hEU hzC) (hEU.trans le_sup_left)
      (Subgroup.mem_sup_right ⟨hzR, hzC⟩))).trans h.weakCore_le

theorem normalizer_sup_zpowers_le (h : ReducedNongeneration p X R X₀) {K : Subgroup X}
    (hnc : ¬ IsCyclic ((R : Subgroup X) ⊓ K : Subgroup X)) {z : X} (hzR : z ∈ (R : Subgroup X))
    (hzK : z ∉ K) (hzp : orderOf z = p) (hzc : z ∈ Subgroup.centralizer (K : Set X)) {c : X}
    (hcRK : c ∈ (R : Subgroup X) ⊓ K) (hc : orderOf c = p) :
    Subgroup.normalizer
      ((Subgroup.zpowers c ⊔ Subgroup.zpowers z : Subgroup X) : Set X) ≤ X₀ := by
  have hp := h.prime
  have hTp : IsPGroup p ((R : Subgroup X) ⊓ K : Subgroup X) := R.isPGroup'.to_le inf_le_left
  have hQR : Subgroup.zpowers c ⊔ Subgroup.zpowers z ≤ R :=
    sup_le (Subgroup.zpowers_le.mpr hcRK.1) (Subgroup.zpowers_le.mpr hzR)
  have hQrank : 2 ≤ Open.pRank p (Subgroup.zpowers c ⊔ Subgroup.zpowers z) :=
    two_le_pRank_of_commute_of_not_mem_zpowers hp hc (hzp ▸ pow_orderOf_eq_one z)
      (fun hz => hzK (Subgroup.zpowers_le.mpr hcRK.2 hz))
      (Subgroup.mem_centralizer_iff.mp hzc c hcRK.2)
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  obtain ⟨E, hE, hEel, hEcard⟩ := exists_isElemAbelian_card_sq_of_two_le_pRank hp
    (two_le_pRank_inf_centralizer_zpowers hp h.ne_two hTp hnc hcRK hc)
  have hEK : E ≤ K := hE.trans (inf_le_left.trans inf_le_right)
  have hzE : z ∈ Subgroup.centralizer (E : Set X) := Subgroup.centralizer_le hEK hzc
  have hEQ : E ≤ Subgroup.centralizer
      ((Subgroup.zpowers c ⊔ Subgroup.zpowers z : Subgroup X) : Set X) := by
    rw [Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.le_centralizer_iff.mp (hE.trans inf_le_right))
      (Subgroup.zpowers_le.mpr hzE)
  exact (normalizer_le_weakCore p hQR hQrank
    (three_le_pRank_of_isElemAbelian_sq_of_mem_centralizer hp hEel hEcard hzp
      (fun hz => hzK (hEK hz)) hzE
      ((le_inf (hE.trans (inf_le_left.trans inf_le_left)) hEQ).trans le_sup_right)
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))))).trans
    h.weakCore_le

theorem inf_normalizer_le_of_pRank_le_one (h : ReducedNongeneration p X R X₀) {K : Subgroup X}
    (hnc : ¬ IsCyclic ((R : Subgroup X) ⊓ K : Subgroup X)) {z : X} (hzR : z ∈ (R : Subgroup X))
    (hzK : z ∉ K) (hzp : orderOf z = p) (hzc : z ∈ Subgroup.centralizer (K : Set X))
    {U : Subgroup X} (hU : U ≤ (R : Subgroup X) ⊓ K) (hU1 : U ≠ ⊥)
    (hrank : Open.pRank p U ≤ 1) : K ⊓ Subgroup.normalizer (U : Set X) ≤ X₀ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hcU, hc, hcC⟩ :=
    exists_mem_centralizer_orderOf_eq (R.isPGroup'.to_le (hU.trans inf_le_left)) hU1
  have hcp : c ^ p = 1 := hc ▸ pow_orderOf_eq_one c
  have hΩ : ∀ a ∈ U, a ^ p = 1 → a ∈ Subgroup.zpowers c := by
    intro a ha hap
    by_contra hac
    have := two_le_pRank_of_commute_of_not_mem_zpowers hp hc hap hac
      (Subgroup.mem_centralizer_iff.mp hcC a ha).symm hcU ha
    omega
  rintro k ⟨hkK, hkN⟩
  apply h.normalizer_sup_zpowers_le hnc hzR hzK hzp hzc (hU hcU) hc
  apply mem_normalizer_of_conj_map_le
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine sup_le ((Subgroup.zpowers_le.mpr ?_).trans le_sup_left) (Subgroup.zpowers_le.mpr ?_)
  · exact hΩ _ ((Subgroup.mem_normalizer_iff.mp hkN c).mp hcU)
      (by rw [conj_pow, hcp, mul_one, mul_inv_cancel])
  · rw [Subgroup.mem_centralizer_iff.mp hzc k hkK, mul_inv_cancel_right]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)

theorem normalizer_inf_le_of_rankOne (h : ReducedNongeneration p X R X₀) {K : Subgroup X}
    (hnc : ¬ IsCyclic ((R : Subgroup X) ⊓ K : Subgroup X)) {z : X} (hzR : z ∈ (R : Subgroup X))
    (hzK : z ∉ K) (hzp : orderOf z = p) (hzc : z ∈ Subgroup.centralizer (K : Set X)) :
    Subgroup.normalizer (((R : Subgroup X) ⊓ K : Subgroup X) : Set X) ≤ X₀ :=
  h.normalizer_le_of_mem_centralizer hzR (fun hz => hzK hz.2) hzp
    (Subgroup.centralizer_le inf_le_right hzc) inf_le_left
    (two_le_pRank_of_isPGroup_not_isCyclic h.prime h.ne_two (R.isPGroup'.to_le inf_le_left) hnc)

theorem not_le_of_rankOne (h : ReducedNongeneration p X R X₀) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hnc : ¬ IsCyclic ((R : Subgroup X) ⊓ K : Subgroup X)) {z : X}
    (hzR : z ∈ (R : Subgroup X)) (hzK : z ∉ K) (hzp : orderOf z = p)
    (hzc : z ∈ Subgroup.centralizer (K : Set X)) : ¬ K ≤ X₀ := by
  intro hKX₀
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hrank : 2 ≤ Open.pRank p ((R : Subgroup X) ⊓ K) :=
    two_le_pRank_of_isPGroup_not_isCyclic hp h.ne_two (R.isPGroup'.to_le inf_le_left) hnc
  by_cases hn : K.Normal
  · exact not_le_of_normalizer_inf_le R (h.normalizer_inf_le_of_rankOne hnc hzR hzK hzp hzc)
      h.ne_top hKX₀
  obtain ⟨x, hx⟩ : ∃ x : X, K.map (MulAut.conj x).toMonoidHom ≠ K := by
    by_contra! hall
    exact hn ⟨fun n hn g => hall g ▸ ⟨n, hn, rfl⟩⟩
  have hL := (ComponentClassification.LocalComponents.equiv_iff (MulAut.conj x) K).mpr hK
  obtain ⟨E, hE, hEel, hEcard⟩ := exists_isElemAbelian_card_sq_of_two_le_pRank hp hrank
  obtain ⟨t, ⟨htR, htL⟩, ht, htZ⟩ :=
    exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot R hL
  have hEK : E ≤ K := hE.trans inf_le_right
  refine h.false_of_forall_component_le (fun M hM => ?_) ?_
  · by_cases hMK : M = K
    · rw [hMK]
      exact hKX₀
    · exact h.le_of_ne_component hM hK hMK hrank
  · exact three_le_pRank_of_isElemAbelian_sq_of_mem_centralizer hp hEel hEcard ht
      (fun htE => htZ (le_centralizer_of_component_ne hK hL hx.symm (hEK htE)))
      (Subgroup.centralizer_le hEK (le_centralizer_of_component_ne hL hK hx htL))
      (hE.trans (inf_le_inf_left _ (le_layer_of_isComponentOf hK)))
      ⟨htR, le_layer_of_isComponentOf hL htL⟩

theorem rankOne_principle (h : ReducedNongeneration p X R X₀) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hnc : ¬ IsCyclic ((R : Subgroup X) ⊓ K : Subgroup X))
    {z : X} (hzR : z ∈ (R : Subgroup X)) (hzK : z ∉ K) (hzp : orderOf z = p)
    (hzc : z ∈ Subgroup.centralizer (K : Set X)) :
    (∀ U : Subgroup X, U ≤ (R : Subgroup X) ⊓ K → U ≠ ⊥ →
        K ⊓ Subgroup.normalizer (U : Set X) ≤ X₀) ∧
      ¬ K ≤ X₀ := by
  refine ⟨fun U hU hU1 => ?_, h.not_le_of_rankOne hK hnc hzR hzK hzp hzc⟩
  rcases le_or_gt 2 (Open.pRank p U) with h2 | h1
  · exact inf_le_right.trans (h.normalizer_le_of_mem_centralizer hzR (fun hz => hzK (hU hz).2)
      hzp (Subgroup.centralizer_le (hU.trans inf_le_right) hzc) (hU.trans inf_le_left) h2)
  · exact h.inf_normalizer_le_of_pRank_le_one hnc hzR hzK hzp hzc hU hU1 (by omega)

theorem center_eq_bot_of_rankOne (h : ReducedNongeneration p X R X₀) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hnc : ¬ IsCyclic ((R : Subgroup X) ⊓ K : Subgroup X))
    {z : X} (hzR : z ∈ (R : Subgroup X)) (hzK : z ∉ K) (hzp : orderOf z = p)
    (hzc : z ∈ Subgroup.centralizer (K : Set X)) : Subgroup.center K = ⊥ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hN, hK₀⟩ := h.rankOne_principle hK hnc hzR hzK hzp hzc
  by_contra hne
  obtain ⟨P, hP⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal R
    (ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
      Subgroup.IsSubnormal.top)
  have hZP : Subgroup.center K ≤ P :=
    (isPGroup_center_of_isComponentOf hp h.core_eq_bot hK).le_sylow_of_normal P
  refine hK₀ fun k hk => hN _ ((Subgroup.map_mono hZP).trans hP.le) ?_ ⟨hk, ?_⟩
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective]
  · apply mem_normalizer_of_conj_map_le
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨y, hy, ?_⟩
    have hky : k * (y : X) = y * k := congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨k, hk⟩)
    simp only [Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hky, mul_inv_cancel_right]

end ReducedNongeneration

end CFSG.AGLEmbedding
