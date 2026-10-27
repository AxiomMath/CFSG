module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigCoverGen
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36V
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36Z
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallA

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem sup_core_eq_of_cover [Finite X] {N K : Subgroup X} {r : ℕ}
    (θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin r)) (hKN : K ≤ N)
    (hcov : ∀ b : alternatingGroup (Fin r), ∃ x : ↥N, (x : X) ∈ K ∧
      θN (x : ↥N ⧸ pPrimeCore 2 ↥N) = b) :
    K ⊔ (pPrimeCore 2 ↥N).map N.subtype = N := by
  refine le_antisymm (sup_le hKN (map_subtype_le _)) ?_
  intro x hx
  obtain ⟨y, hyK, hy⟩ := hcov (θN ((⟨x, hx⟩ : ↥N) : ↥N ⧸ pPrimeCore 2 ↥N))
  have h1 : ((y : ↥N) : ↥N ⧸ pPrimeCore 2 ↥N) = ((⟨x, hx⟩ : ↥N) : ↥N ⧸ pPrimeCore 2 ↥N) :=
    θN.injective hy
  rw [QuotientGroup.eq] at h1
  have h2 : (x : X) = (y : X) * ((y⁻¹ * ⟨x, hx⟩ : ↥N) : X) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [h2]
  exact mul_mem (mem_sup_left hyK) (mem_sup_right ⟨_, h1, rfl⟩)

variable {M : Subgroup X} {r : ℕ} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)}

theorem IsPermAction.exists_lift_of_two_two (hρ : IsPermAction θ ρ) [Finite X] {a₁ a₂ : X}
    (ha₁ : a₁ ∈ normalizer (M : Set X)) (ha₁2 : IsPGroup 2 (zpowers a₁))
    (ha₂ : a₂ ∈ normalizer (M : Set X)) (ha₂2 : a₂ * a₂ = 1) (h12 : a₁ * a₂ = a₂ * a₁)
    {b : alternatingGroup (Fin r)} (hb₁ : (b : Perm (Fin r)) * ρ ⟨a₁, ha₁⟩ = ρ ⟨a₁, ha₁⟩ * b)
    (hb₂ : (b : Perm (Fin r)) * ρ ⟨a₂, ha₂⟩ = ρ ⟨a₂, ha₂⟩ * b) :
    ∃ x : ↥M, (x : X) ∈ centralizer ({a₁} : Set X) ∧ (x : X) ∈ centralizer ({a₂} : Set X) ∧
      θ (x : ↥M ⧸ pPrimeCore 2 ↥M) = b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x₁, hx₁C, hx₁θ⟩ := hρ.exists_lift_of_two ha₁ ha₁2 hb₁
  set O : Subgroup X := (pPrimeCore 2 ↥M).map M.subtype with hOdef
  set K : Subgroup X := O ⊓ centralizer ({a₁} : Set X) with hKdef
  have hKodd : Odd (Nat.card K) := by
    have h1 : Odd (Nat.card O) := by
      rw [hOdef, card_map_of_injective M.subtype_injective]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact h1.of_dvd_nat (card_dvd_of_le inf_le_left)
  have ha₂C : a₂ ∈ centralizer ({a₁} : Set X) := mem_centralizer_singleton_iff.mpr h12.symm
  have hK : ∀ k ∈ K, a₂ * k * a₂⁻¹ ∈ K := by
    intro k hk
    obtain ⟨hkO, hkC⟩ := mem_inf.mp hk
    exact mem_inf.mpr ⟨(mem_normalizer_iff.mp (le_normalizer_pPrimeCore ha₂) k).mp hkO,
      mul_mem (mul_mem ha₂C hkC) (inv_mem ha₂C)⟩
  have hx : (x₁ : X)⁻¹ * (a₂ * x₁ * a₂⁻¹) ∈ K := by
    set y : ↥M := x₁⁻¹ * M.normalizerMonoidHom ⟨a₂, ha₂⟩ x₁ with hydef
    have hy : (y : X) = (x₁ : X)⁻¹ * (a₂ * x₁ * a₂⁻¹) := by
      rw [hydef, Subgroup.coe_mul, normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inv]
    have hyθ : θ (y : ↥M ⧸ pPrimeCore 2 ↥M) = 1 := by
      apply Subtype.ext
      have h1 := hρ ⟨a₂, ha₂⟩ x₁
      rw [hydef, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv,
        Subgroup.coe_mul, Subgroup.coe_inv, h1, hx₁θ]
      rw [show ρ ⟨a₂, ha₂⟩ * (b : Perm (Fin r)) = (b : Perm (Fin r)) * ρ ⟨a₂, ha₂⟩ from hb₂.symm]
      simp
    have hyO : y ∈ pPrimeCore 2 ↥M := by
      rw [← QuotientGroup.eq_one_iff]
      exact θ.injective (by rw [hyθ, map_one])
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [← hy]
      exact ⟨y, hyO, rfl⟩
    · exact mul_mem (inv_mem hx₁C) (mul_mem (mul_mem ha₂C hx₁C) (inv_mem ha₂C))
  obtain ⟨k, hkK, hkc⟩ := exists_commute_of_mem_coset hKodd ha₂2 hK hx
  obtain ⟨hkO, hkC⟩ := mem_inf.mp hkK
  obtain ⟨k', hk'O, hk'⟩ := hkO
  refine ⟨x₁ * k', ?_, ?_, ?_⟩
  · rw [Subgroup.coe_mul]
    change (x₁ : X) * (M.subtype k') ∈ _
    rw [hk']
    exact mul_mem hx₁C hkC
  · rw [Subgroup.coe_mul]
    change (x₁ : X) * (M.subtype k') ∈ _
    rw [hk', mem_centralizer_singleton_iff]
    exact hkc.symm
  · rw [QuotientGroup.mk_mul, map_mul, hx₁θ, (QuotientGroup.eq_one_iff k').mpr hk'O, map_one,
      mul_one]

theorem exists_center_involution_commute [Finite X] {Q : Subgroup X} (hQ2 : IsPGroup 2 Q)
    (hQ1 : Q ≠ ⊥) {s : X} (hsQ : s ∈ normalizer (Q : Set X)) {k : ℕ} (hsk : s ^ 2 ^ k = 1) :
    ∃ z ∈ Q, orderOf z = 2 ∧ (∀ q ∈ Q, q * z = z * q) ∧ z * s = s * z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z : Subgroup X := Q ⊓ centralizer (Q : Set X) with hZdef
  have hsZ : s ∈ normalizer (Z : Set X) :=
    inf_mem_normalizer' hsQ (Sol78H.mem_normalizer_centralizer hsQ)
  have hZeven : Even (Nat.card Z) := by
    have : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQ1
    have hc := hQ2.center_nontrivial
    obtain ⟨⟨c, hc⟩, hc1⟩ := exists_ne (1 : center ↥Q)
    have hcZ : ((c : ↥Q) : X) ∈ Z := by
      refine mem_inf.mpr ⟨c.2, mem_centralizer_iff.mpr fun q hq => ?_⟩
      have h1 := mem_center_iff.mp hc ⟨q, hq⟩
      exact congrArg Subtype.val h1
    have hZ2 : IsPGroup 2 Z := hQ2.to_le inf_le_left
    have hZ1 : Z ≠ ⊥ := by
      intro h
      rw [h, mem_bot] at hcZ
      apply hc1
      exact Subtype.ext (Subtype.ext hcZ)
    obtain ⟨m, hm⟩ := hZ2.exists_card_eq
    have hm1 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hm
      exact hZ1 ((Subgroup.card_eq_one).mp hm)
    rw [hm]
    exact (Nat.even_pow.mpr ⟨even_two, hm1⟩)
  obtain ⟨u, huZ, hu2, hus⟩ := exists_involution_commute_of_even hsk hsZ hZeven
  obtain ⟨huQ, huC⟩ := mem_inf.mp huZ
  exact ⟨u, huQ, hu2, fun q hq => mem_centralizer_iff.mp huC q hq, hus⟩

namespace Sig36

variable [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}

theorem false_of_cover_of_centralizer [Finite X] (S : Sig36 X t J n e E D)
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ) {s : X}
    (hsH : s ∈ normalizer (Sol78.signalizerCompletion E E : Set X)) (hs1 : ρ ⟨s, hHN hsH⟩ ≠ 1)
    {N : Subgroup X} (θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin n)) {Y : Subgroup X}
    (hYN : Y ≤ N) (hYH : Y ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hYs : Y ≤ centralizer ({s} : Set X)) (hsupY : Y ⊔ (pPrimeCore 2 ↥N).map N.subtype = N)
    {T : Subgroup X} (hT2 : IsPGroup 2 T)
    (hTH : T ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) (hsT : s ∈ T)
    (hKT : FooteLit.IsTwoComponentIn (FooteLit.oddResidualIn N) (centralizer (T : Set X))) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn9 := S.nine_le
  have hTK : ¬ T ≤ UnbalancedLayer.coreActionKernel M := fun h =>
    hs1 (hρ.eq_one_of_mem_coreActionKernel (by omega) (h hsT))
  obtain ⟨θY, hθY⟩ := exists_coreQuot_of_sup hYN hsupY θN
  set Y' : Subgroup X := Y ⊓ UnbalancedLayer.coreActionKernel M with hY'def
  have hY'Y : Y' ≤ Y := inf_le_left
  set π : ↥Y →* alternatingGroup (Fin n) :=
    θY.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥Y)) with hπdef
  have hπs : Function.Surjective π :=
    θY.surjective.comp (QuotientGroup.mk'_surjective _)
  set I : Subgroup (alternatingGroup (Fin n)) := (Y'.subgroupOf Y).map π with hIdef
  have hInorm : I.Normal := by
    refine ⟨fun a ha b => ?_⟩
    obtain ⟨y', hy', rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hπs b
    refine ⟨y * y' * y⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    have hy'' : ((y' : ↥Y) : X) ∈ Y' := hy'
    obtain ⟨hy'Y, hy'K⟩ := mem_inf.mp hy''
    show ((y * y' * y⁻¹ : ↥Y) : X) ∈ Y'
    refine mem_inf.mpr ⟨?_, ?_⟩
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact mul_mem (mul_mem y.2 hy'Y) (inv_mem y.2)
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hρ.conj_mem_coreActionKernel (by omega) (hHN (hYH y.2)) hy'K
  have hsimple : IsSimpleGroup (alternatingGroup (Fin n)) := by
    have h1 := isSimpleGroup_fixAlt (τ := (1 : Perm (Fin n)))
      (by rw [Perm.support_one, Finset.card_empty]; omega)
    have h2 : fixAlt (1 : Perm (Fin n)) = ⊤ := by
      rw [eq_top_iff]
      intro k _
      rw [mem_fixAlt, Perm.support_one, Finset.compl_empty]
      exact Finset.subset_univ _
    rw [h2] at h1
    exact (Subgroup.topEquiv).symm.isSimpleGroup
  rcases hInorm.eq_bot_or_eq_top with hI | hI
  ·
    have hY'O : ∀ y : ↥Y, (y : X) ∈ UnbalancedLayer.coreActionKernel M →
        (y : X) ∈ coreNOf Y := by
      intro y hyK
      have h1 : π y = 1 := by
        have h2 : π y ∈ I := ⟨y, mem_subgroupOf.mpr (mem_inf.mpr ⟨y.2, hyK⟩), rfl⟩
        rwa [hI, mem_bot] at h2
      have h3 : (y : ↥Y ⧸ pPrimeCore 2 ↥Y) = 1 := θY.injective (by rw [map_one]; exact h1)
      exact ⟨y, (QuotientGroup.eq_one_iff y).mp h3, rfl⟩
    set A := (Y.subgroupOf (normalizer (M : Set X))).map ρ with hAdef
    have hYNM : Y ≤ normalizer (M : Set X) := hYH.trans hHN
    have hcardY := card_eq_of_alt (by omega) θY
    have hk₁ := card_eq_card_map_mul_card_inf_ker' ρ (Y.subgroupOf (normalizer (M : Set X)))
    have hYs' : Nat.card (Y.subgroupOf (normalizer (M : Set X))) = Nat.card Y :=
      Nat.card_congr (subgroupOfEquivOfLe hYNM).toEquiv
    have hinf : Nat.card (Y.subgroupOf (normalizer (M : Set X)) ⊓ ρ.ker : Subgroup _) ≤
        Nat.card (coreNOf Y) := by
      have h1 : Y.subgroupOf (normalizer (M : Set X)) ⊓ ρ.ker ≤
          (coreNOf Y).subgroupOf (normalizer (M : Set X)) := by
        rintro z ⟨hz, hzk⟩
        exact hY'O ⟨z, hz⟩ (hρ.mem_coreActionKernel z.2 hzk)
      rw [← Nat.card_congr (subgroupOfEquivOfLe ((map_subtype_le _).trans hYNM)).toEquiv]
      exact Subgroup.card_le_of_le h1
    have hOpos : 0 < Nat.card (coreNOf Y) := Nat.card_pos
    have hAcard : n.factorial / 2 ≤ Nat.card A := by
      have h1 : (n.factorial / 2) * Nat.card (coreNOf Y) ≤
          Nat.card A * Nat.card (coreNOf Y) := by
        calc (n.factorial / 2) * Nat.card (coreNOf Y) = Nat.card Y := hcardY.symm
          _ = Nat.card A * Nat.card (Y.subgroupOf (normalizer (M : Set X)) ⊓ ρ.ker :
              Subgroup _) := by rw [← hYs', hk₁]
          _ ≤ Nat.card A * Nat.card (coreNOf Y) := Nat.mul_le_mul_left _ hinf
      exact Nat.le_of_mul_le_mul_right h1 hOpos
    have hAidx : A.index ≤ 2 := by
      have h1 := A.index_mul_card
      rw [Nat.card_perm, Nat.card_fin] at h1
      have h2 : 2 * (n.factorial / 2) = n.factorial := by
        have : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
        omega
      have h3 : 0 < n.factorial / 2 := by
        have := Nat.factorial_pos n
        omega
      by_contra h4
      push Not at h4
      have h5 : 3 * (n.factorial / 2) ≤ A.index * Nat.card A :=
        Nat.mul_le_mul h4 hAcard
      omega
    have hAlt := Equiv.Perm.alternatingGroup_le_of_index_le_two hAidx
    apply hs1
    apply Equiv.ext
    intro v
    have h4 : 4 ≤ n - (1 : Perm (Fin n)).support.card := by
      rw [Perm.support_one, Finset.card_empty]
      omega
    have h5 : v ∉ (1 : Perm (Fin n)).support := by
      rw [Perm.support_one]
      exact Finset.notMem_empty v
    refine apply_eq_of_commute_fixAlt h4 (fun b _ => ?_) h5
    obtain ⟨y, hy, hyb⟩ := hAlt b.2
    rw [← hyb]
    have hys : (y : X) * s = s * y := mem_centralizer_singleton_iff.mp (hYs (mem_subgroupOf.mp hy))
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hys.symm
  ·
    have hcov : ∀ b : alternatingGroup (Fin n), ∃ x : ↥N, (x : X) ∈ Y' ∧
        θN (x : ↥N ⧸ pPrimeCore 2 ↥N) = b := by
      intro b
      have h1 : b ∈ I := by rw [hI]; exact mem_top b
      obtain ⟨x, hx, hxb⟩ := h1
      exact ⟨⟨x, hYN x.2⟩, mem_subgroupOf.mp hx, (hθY x).symm.trans hxb⟩
    exact S.false_of_cover_of_isTwoComponentIn h33 h35 hT13 hML hSch hMH hMpc hHN hsup θ θN
      (hY'Y.trans hYN) (hY'Y.trans hYH) inf_le_right
      (sup_core_eq_of_cover θN (hY'Y.trans hYN) hcov) hT2 (hTH.trans hHN) hTK hKT

theorem false_of_cover_of_centralizer_of_normal [Finite X] (S : Sig36 X t J n e E D)
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ) {s : X}
    (hs2 : IsPGroup 2 (zpowers s))
    (hsH : s ∈ normalizer (Sol78.signalizerCompletion E E : Set X)) (hs1 : ρ ⟨s, hHN hsH⟩ ≠ 1)
    {N : Subgroup X} (hNs : N ≤ centralizer ({s} : Set X))
    (hsN : centralizer ({s} : Set X) ≤ normalizer (N : Set X))
    (θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin n)) {Y : Subgroup X}
    (hYN : Y ≤ N) (hYH : Y ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hsupY : Y ⊔ (pPrimeCore 2 ↥N).map N.subtype = N) : False := by
  have hn9 := S.nine_le
  refine S.false_of_cover_of_centralizer h33 h35 hT13 hML hSch hMH hMpc hHN hsup θ hρ hsH hs1 θN
    hYN hYH (hYN.trans hNs) hsupY hs2 (zpowers_le.mpr hsH) (mem_zpowers s) ?_
  rw [UnbalancedLayer.centralizer_zpowers_eq]
  exact (isTwoComponentIn_oddResidualIn hNs hsN (by omega) θN).1

theorem false_of_cover_of_centralizer_of_isPComponent [Finite X]
    (S : Sig36 X t J n e E D)
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ) {s : X}
    (hs2 : IsPGroup 2 (zpowers s))
    (hsH : s ∈ normalizer (Sol78.signalizerCompletion E E : Set X)) (hs1 : ρ ⟨s, hHN hsH⟩ ≠ 1)
    {N : Subgroup X} (hNs : N ≤ centralizer ({s} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({s} : Set X))))
    (θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin n)) {Y : Subgroup X}
    (hYN : Y ≤ N) (hYH : Y ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hsupY : Y ⊔ (pPrimeCore 2 ↥N).map N.subtype = N) : False := by
  refine S.false_of_cover_of_centralizer h33 h35 hT13 hML hSch hMH hMpc hHN hsup θ hρ hsH hs1 θN
    hYN hYH (hYN.trans hNs) hsupY hs2 (zpowers_le.mpr hsH) (mem_zpowers s) ?_
  rw [FooteLit.oddResidualIn_eq_self_of_isPComponent hNs hNpc,
    UnbalancedLayer.centralizer_zpowers_eq]
  exact ⟨hNs, hNpc⟩

end Sig36

end CFSG.ComponentClassification.SolMax
