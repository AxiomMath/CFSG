module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFCD
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFCE

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem centralizer_inf_le_normalizer_of_four [Finite X] {F : Subgroup X}
    (hF4 : Nat.card F = 4) (hFsq : ∀ x ∈ F, x * x = 1) {v₁ v₂ : X} (hv₁ : v₁ ∈ F) (hv₂ : v₂ ∈ F)
    (hv₁1 : v₁ ≠ 1) (hv₂1 : v₂ ≠ 1) (h12 : v₁ ≠ v₂) :
    centralizer ({v₁} : Set X) ⊓ centralizer ({v₂} : Set X) ≤ normalizer (F : Set X) := by
  have : IsKleinFour ↥F := isKleinFour_of_card hF4 fun g => Subtype.ext (hFsq g g.2)
  intro x hx
  obtain ⟨hx₁, hx₂⟩ := mem_inf.mp hx
  rw [mem_centralizer_singleton_iff] at hx₁ hx₂
  refine Subgroup.centralizer_le_normalizer (F : Set X) ?_
  rw [mem_centralizer_iff]
  intro y hy
  by_cases hy1 : y = 1
  · rw [hy1, mul_one, one_mul]
  by_cases hy₁ : y = v₁
  · rw [hy₁, hx₁]
  by_cases hy₂ : y = v₂
  · rw [hy₂, hx₂]
  have h := IsKleinFour.eq_mul_of_ne_all (G := ↥F) (x := ⟨v₁, hv₁⟩) (y := ⟨v₂, hv₂⟩)
    (z := ⟨y, hy⟩) (fun h => hv₁1 (congrArg Subtype.val h))
    (fun h => hv₂1 (congrArg Subtype.val h)) (fun h => h12 (congrArg Subtype.val h))
    (fun h => hy1 (congrArg Subtype.val h)) (fun h => hy₁ (congrArg Subtype.val h))
    (fun h => hy₂ (congrArg Subtype.val h))
  have hy' : y = v₁ * v₂ := congrArg Subtype.val h
  rw [hy']
  calc v₁ * v₂ * x = v₁ * (v₂ * x) := by group
    _ = v₁ * (x * v₂) := by rw [hx₂]
    _ = v₁ * x * v₂ := by group
    _ = x * v₁ * v₂ := by rw [hx₁]
    _ = x * (v₁ * v₂) := by group

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)} {E : Subgroup X} {D : Finset (Fin 9)}

theorem false_of_isPComponent_centralizer_of_mem_E (S : Sig36 X t J 9 e E D)
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M)
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M) (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9))
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} (hρ : IsPermAction θ ρ) {e₀ : X}
    (he₀E : e₀ ∈ E) (he₀1 : e₀ ≠ 1) {K₀ : Subgroup X} (hK₀C : K₀ ≤ centralizer ({e₀} : Set X))
    (hK₀pc : IsPComponent 2 (K₀.subgroupOf (centralizer ({e₀} : Set X))))
    (θK : ↥K₀ ⧸ pPrimeCore 2 ↥K₀ ≃* alternatingGroup (Fin 9)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  set Y := centralizer ({e₀} : Set X) with hYdef
  have hJH : J ≤ H := S.le_normalizer_completion h33 h35
  have hCt : centralizer ({t} : Set X) ≤ H :=
    S.centralizer_le_normalizer_completion h33 h35 hT13 hML hSch
  have he₀J : e₀ ∈ J := S.le he₀E
  have he₀H : e₀ ∈ H := hJH he₀J
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ he₀E
  have ht2 : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  have h4 := S.card_support_coreImage_E he₀E he₀1
  have hρe₀ : ρ ⟨e₀, hHN he₀H⟩ ≠ 1 := by
    intro h
    have h1 := card_support_rho_eq_of_sup (by norm_num) e hJM hsup hρ he₀J
    rw [h4] at h1
    have h2 : ρ ⟨e₀, le_normalizer (hJM he₀J)⟩ = 1 := h
    rw [h2, Perm.support_one, Finset.card_empty] at h1
    exact absurd h1 (by norm_num)
  have hte₀ : t ∈ Y :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp
      (S.pair.1.2.1 he₀J)).symm
  have hOC : (pPrimeCore 2 ↥Y).map Y.subtype ≤ H := S.oddCore_le_of_mem_E he₀E he₀1
  have hcover : ∀ Y' : Subgroup X, Y' ≤ K₀ → Y' ≤ H →
      Y' ⊔ (pPrimeCore 2 ↥K₀).map K₀.subtype = K₀ → False := fun Y' hY'K hY'H hY'sup =>
    S.false_of_cover_of_centralizer_of_isPComponent h33 h35 hT13 hML hSch hMH hMpc hHN hsup θ hρ
      (isPGroup_zpowers_of_mul_self he₀2) he₀H hρe₀ hK₀C hK₀pc θK hY'K hY'H hY'sup
  have hK₀H : ¬ K₀ ≤ H := fun h => hcover K₀ le_rfl h (sup_eq_left.mpr (map_subtype_le _))
  obtain ⟨L₀, hL₀J, hL₀pc, hinv, -, χ, -⟩ :=
    exists_fixed_component_of_acts S.pair.1.2.1 S.pair.1.2.2.1 e (le_normalizer he₀J) he₀2
      he₀J (by rw [mul_inv_cancel]; exact one_mem _) (by rw [h4])
  have hβ : Fintype.card ↥((coreImage e he₀J).supportᶜ : Finset (Fin 9)) = 5 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, h4]
  let eL₀ : ↥L₀ ⧸ pPrimeCore 2 ↥L₀ ≃* alternatingGroup (Fin 5) :=
    χ.trans (Fintype.equivFinOfCardEq hβ).altCongrHom
  have hL₀Ct : L₀ ≤ centralizer ({t} : Set X) := (hL₀J.trans inf_le_left).trans S.pair.1.2.1
  have hL₀Y : L₀ ≤ Y := hL₀J.trans inf_le_right
  obtain ⟨F, DF, hFJ, hF4, hFsq, hDF, hdisj, hFs, hFE⟩ :=
    exists_commuting_four_subgroup S.nine_le e S.le S.isPGroup S.card S.supp
  have hsuppD : (coreImage e he₀J).support ⊆ D := by
    intro ω hω
    by_contra hωD
    exact (Perm.mem_support.mp hω) (S.supp ⟨e₀, he₀J⟩ he₀E ω hωD)
  have hDFc : DF ⊆ (coreImage e he₀J).supportᶜ := by
    intro ω hω
    rw [Finset.mem_compl]
    intro h
    exact Finset.disjoint_left.mp hdisj (hsuppD h) hω
  have hFL₀ : F ≤ L₀ := by
    intro x hx
    have hxJ : x ∈ J := hFJ hx
    refine hinv x hxJ ?_ ⟨1, by rw [pow_one, sq]; exact hFsq x hx⟩ ?_
    · exact (mem_centralizer_iff.mp (hFE hx) e₀ he₀E).symm
    · intro ω hω
      refine hDFc ?_
      by_contra hωF
      exact (Perm.mem_support.mp hω) (hFs ⟨x, hxJ⟩ hx ω hωF)
  have hFk := klein_of_card_sq hF4 hFsq
  have hFH : normalizer (F : Set X) ≤ H := by
    have hFW := S.completion_eq_of_four h33 h35 hFJ hFk hDF hFs
    have h1 := normalizer_le_normalizer_signalizerCompletion_self F
    rwa [hFW] at h1
  have hF2 : IsPGroup 2 F := IsPGroup.of_card (n := 2) (by rw [hF4]; norm_num)
  obtain ⟨M₁, hM₁Y, hM₁pc, hL₀M₁, -, hswap⟩ := orbit_location_in_swap hte₀ S.pair.1.1
    (le_inf hL₀Y hL₀Ct) (by rw [inf_comm]; exact hL₀pc)
  obtain ⟨hM₁tY, hM₁tpc⟩ := isPComponent_conj hM₁Y hM₁pc hte₀
  by_cases hA : M₁ ≠ K₀ ∧ M₁.map (MulAut.conj t).toMonoidHom ≠ K₀
  ·
    apply hK₀H
    intro k hk
    refine mem_of_commutator_mem_oddCore hFH (hFJ.trans hJH) hOC hF2 (hFL₀.trans hL₀Y) ?_
    intro v hv
    exact forall_commutator_mem_oddCore_of_le_sup hM₁Y hM₁tY
      (fun k' hk' a ha => commutator_mem_oddCore_of_ne hK₀C hK₀pc hM₁Y hM₁pc (Ne.symm hA.1)
        hk' ha)
      (fun k' hk' a ha => commutator_mem_oddCore_of_ne hK₀C hK₀pc hM₁tY hM₁tpc (Ne.symm hA.2)
        hk' ha) k hk v (hL₀M₁ (hFL₀ hv))
  ·
    have hsupK : M₁ ⊔ M₁.map (MulAut.conj t).toMonoidHom =
        K₀ ⊔ K₀.map (MulAut.conj t).toMonoidHom := by
      by_cases h1 : M₁ = K₀
      · rw [h1]
      · have h2 : M₁.map (MulAut.conj t).toMonoidHom = K₀ := by
          by_contra h2
          exact hA ⟨h1, h2⟩
        have h3 : M₁ = K₀.map (MulAut.conj t).toMonoidHom := by
          rw [← h2, map_conj_map_conj_of_mul_self ht2]
        rw [h3, map_conj_map_conj_of_mul_self ht2, sup_comm]
    by_cases hfix : K₀.map (MulAut.conj t).toMonoidHom = K₀
    ·
      have hL₀K₀ : L₀ ≤ K₀ := by
        have h1 := hL₀M₁
        rwa [hsupK, hfix, sup_idem] at h1
      have htN : t ∈ normalizer (K₀ : Set X) := mem_normalizer_iff_map_conj_eq.mpr hfix
      have he₀t : e₀ * t = t * e₀ := (mem_centralizer_singleton_iff.mp hte₀).symm
      have he₀2' : IsPGroup 2 (zpowers e₀) := isPGroup_zpowers_of_mul_self he₀2
      obtain ⟨v₁, v₂, -, hv₁, hv₂, -, hv₁1, hv₂1, -, h12, -, -⟩ := exists_three_of_klein hFk
      have hv₁P := mem_fiveClosure_of_mul_self eL₀ hL₀Y hL₀Ct he₀2' ht2 he₀t (hFL₀ hv₁)
        (hFsq v₁ hv₁)
      have hv₂P := mem_fiveClosure_of_mul_self eL₀ hL₀Y hL₀Ct he₀2' ht2 he₀t (hFL₀ hv₂)
        (hFsq v₂ hv₂)
      have hv12 : v₁ * v₂ = v₂ * v₁ := by
        have h1 := hFsq (v₁ * v₂) (mul_mem hv₁ hv₂)
        have hi1 : v₁⁻¹ = v₁ := inv_eq_of_mul_eq_one_right (hFsq v₁ hv₁)
        have hi2 : v₂⁻¹ = v₂ := inv_eq_of_mul_eq_one_right (hFsq v₂ hv₂)
        have h4 : (v₁ * v₂)⁻¹ = v₁ * v₂ := inv_eq_of_mul_eq_one_right h1
        rw [mul_inv_rev, hi1, hi2] at h4
        exact h4.symm
      have hCv : ∀ y : X, y ∈ centralizer ({v₁} : Set X) → y ∈ centralizer ({v₂} : Set X) →
          y ∈ H := fun y hy₁ hy₂ =>
        hFH (centralizer_inf_le_normalizer_of_four hF4 hFsq hv₁ hv₂ hv₁1 hv₂1 h12
          (mem_inf.mpr ⟨hy₁, hy₂⟩))
      exact S.false_of_fiveClosure_cover h33 h35 hT13 hML hSch hMH hMpc hHN hsup θ hρ he₀2' he₀H
        hρe₀ hK₀C hK₀pc θK htN ht2 hCt (L := L₀) (w₀ := e₀)
        (fun w hwL _ _ => le_normalizer (hL₀K₀ hwL))
        hv₁P hv₂P (hFsq v₁ hv₁) (hFsq v₂ hv₂) hv12 hCv
    ·
      have hne : M₁.map (MulAut.conj t).toMonoidHom ≠ M₁ := by
        intro h
        apply hfix
        by_cases h1 : M₁ = K₀
        · rw [← h1]
          exact h
        · have h2 : M₁.map (MulAut.conj t).toMonoidHom = K₀ := by
            by_contra h2
            exact hA ⟨h1, h2⟩
          rw [← h2, h]
          exact h
      obtain ⟨φ⟩ := hswap hne
      have hZL : Open.fusionZStar ↥L₀ = pPrimeCore 2 ↥L₀ := fusionZStar_eq_of_alt (by norm_num) eL₀
      have hM₁θ : Nonempty (↥M₁ ⧸ pPrimeCore 2 ↥M₁ ≃* alternatingGroup (Fin 9)) := by
        by_cases h1 : M₁ = K₀
        · subst h1
          exact ⟨θK⟩
        · have h2 : M₁.map (MulAut.conj t).toMonoidHom = K₀ := by
            by_contra h2
            exact hA ⟨h1, h2⟩
          have h3 : M₁ = K₀.map (MulAut.conj t).toMonoidHom := by
            rw [← h2, map_conj_map_conj_of_mul_self ht2]
          rw [h3]
          exact ⟨(Sol78.coreQuotCongr (K₀.equivMapOfInjective (MulAut.conj t).toMonoidHom
            (MulAut.conj t).injective)).symm.trans θK⟩
      obtain ⟨θM₁⟩ := hM₁θ
      have hZM : Open.fusionZStar ↥M₁ = pPrimeCore 2 ↥M₁ := fusionZStar_eq_of_alt (by norm_num) θM₁
      have hcard := Nat.card_congr φ.toEquiv
      rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZL).toEquiv,
        Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZM).toEquiv, Nat.card_congr eL₀.toEquiv,
        Nat.card_congr θM₁.toEquiv, nat_card_alternatingGroup, nat_card_alternatingGroup,
        Nat.card_fin, Nat.card_fin] at hcard
      exact absurd hcard (by decide)

theorem false_of_isPComponent_centralizer_of_four (S : Sig36 X t J 9 e E D)
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M)
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M) (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9))
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} (hρ : IsPermAction θ ρ) {x : X}
    (hxM : x ∈ M) (hx2 : x * x = 1) (hx4 : (ρ ⟨x, le_normalizer hxM⟩).support.card = 4)
    {K : Subgroup X} (hKC : K ≤ centralizer ({x} : Set X))
    (hKpc : IsPComponent 2 (K.subgroupOf (centralizer ({x} : Set X))))
    (θK : ↥K ⧸ pPrimeCore 2 ↥K ≃* alternatingGroup (Fin 9)) : False := by
  obtain ⟨a₁, -, -, h₁, -, -, h₁₁, -⟩ := exists_three_of_klein S.klein
  have ha₁J : a₁ ∈ J := S.le h₁
  have ha₁M : a₁ ∈ M := hJM ha₁J
  have ha₁2 : a₁ * a₁ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 a₁ h₁
  have ha₁4 : (ρ ⟨a₁, le_normalizer ha₁M⟩).support.card = 4 := by
    have h1 := card_support_rho_eq_of_sup (by norm_num) e hJM hsup hρ ha₁J
    rw [S.card_support_coreImage_E h₁ h₁₁] at h1
    exact h1
  have hkerM : ∀ g ∈ M, g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g) :=
    fun g hg hgK => odd_orderOf_of_mem_oddCoreIn (mem_core_of_mem_coreActionKernel hρ (by norm_num)
      hg hgK)
  obtain ⟨c, -, hc⟩ := hρ.exists_conj_of_four (by norm_num) le_rfl hkerM (le_normalizer ha₁M)
    (le_normalizer hxM) ha₁M hxM ha₁2 hx2 ha₁4 hx4
  have hCmap : (centralizer ({x} : Set X)).map (MulAut.conj c⁻¹).toMonoidHom =
      centralizer ({a₁} : Set X) := by
    rw [map_conj_centralizer_singleton, ← hc]
    congr 2
    group
  have hK'C : K.map (MulAut.conj c⁻¹).toMonoidHom ≤ centralizer ({a₁} : Set X) := by
    rw [← hCmap]
    exact map_mono hKC
  have hK'pc : IsPComponent 2 ((K.map (MulAut.conj c⁻¹).toMonoidHom).subgroupOf
      (centralizer ({a₁} : Set X))) := by
    rw [← hCmap]
    exact isPComponent_map_conj hKC hKpc c⁻¹
  exact S.false_of_isPComponent_centralizer_of_mem_E h33 h35 hT13 hML hSch hMH hMpc hJM hHN hsup
    θ hρ h₁ h₁₁ hK'C hK'pc ((Sol78.coreQuotCongr (K.equivMapOfInjective
      (MulAut.conj c⁻¹).toMonoidHom (MulAut.conj c⁻¹).injective)).symm.trans θK)

end Sig36

end CFSG.ComponentClassification.SolMax
