module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76F316Beta
public import CFSG.LocalAnalysis.ComponentClassification.Sol76False316Cover
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4Final
public import CFSG.RankThree.PartOne.SPOR.Final

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_pow_modO
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hq : QuasisimpleTwoPartInput) (hG : KStarKProper G) {N : Subgroup G}
    (hr : ∃ K₁ ∈ kStarComponents N, ∃ K₂ ∈ kStarComponents N, K₁ ≠ K₂)
    (hKH : solomonKStarOf (normalizer (solomonKStarOf N : Set G)) = solomonKStarOf N)
    (hCb : ∀ K ∈ kStarComponents N, ∀ s ∈ K, orderOf s = 2 →
      centralizer ({s} : Set G) ≤ normalizer (solomonKStarOf N : Set G))
    {K K' : Subgroup G} (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N) {t g : G}
    (htM : t ∈ normalizer (solomonKStarOf N : Set G))
    (htgM : g⁻¹ * t * g ∈ normalizer (solomonKStarOf N : Set G)) {k : ℕ}
    (htk : t ^ (2 ^ k) = 1) (ht1 : t ≠ 1)
    (htK : ∀ a ∈ K, t⁻¹ * a⁻¹ * t * a ∈ oddCoreIn (solomonKStarOf N))
    (htgK' : ∀ a ∈ K', (g⁻¹ * t * g)⁻¹ * a⁻¹ * (g⁻¹ * t * g) * a ∈ oddCoreIn (solomonKStarOf N)) :
    g ∈ normalizer (solomonKStarOf N : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := solomonKStarOf N with hD
  set M := normalizer (D : Set G) with hM
  have htQ : t ∈ coreActionKernel K := mem_coreActionKernel_of_commutator_mem_oddCoreIn hK htM htK
  have hL := twoLayerIn_centralizer_le_normalizer_of_pow_of_mem hq hG hCb hK htk ht1 htQ
  have hLg : twoLayerIn (centralizer ({g⁻¹ * t * g} : Set G)) ≤ conjugate M g := by
    have e1 := map_conj_centralizer_singleton g⁻¹ t
    rw [inv_inv] at e1
    rw [← e1, ← map_twoLayerIn]
    exact map_mono hL
  have hpow : (g⁻¹ * t * g) ^ (2 ^ k) = 1 := by
    have hconj : ∀ n : ℕ, (g⁻¹ * t * g) ^ n = g⁻¹ * t ^ n * g := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, ih, pow_succ]; group
    rw [hconj, htk]
    group
  have htg1 : g⁻¹ * t * g ≠ 1 := fun h => ht1 (by
    calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group)
  set t' := g⁻¹ * t * g with ht'
  have ht'Q : t' ∈ coreActionKernel K' :=
    mem_coreActionKernel_of_commutator_mem_oddCoreIn hK' htgM htgK'
  have hT2 : IsPGroup 2 (zpowers t') := isPGroup_zpowers_of_pow hpow
  have hTne : zpowers t' ≠ ⊥ := fun h => htg1 (zpowers_eq_bot.mp h)
  have hTQ : zpowers t' ≤ coreActionKernel K' := zpowers_le.mpr ht'Q
  have hCT : centralizer ((zpowers t' : Subgroup G) : Set G) = centralizer ({t'} : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  have h212 := lemma212Input G K' (zpowers t') hK'.2 hTne hT2 hTQ
  rw [hCT] at h212
  have hK'q : IsQuasisimple (↥K' ⧸ pPrimeCore 2 ↥K') :=
    isQuasisimple_quotient_of_isPComponent hK'.1.1 hK'.1.2
  have hcov := inf_centralizer_sup_oddCoreIn_eq hT2 hTQ
  rw [hCT] at hcov
  obtain ⟨hY2, hYL, hYsup, -⟩ := cover_facts hK'q inf_le_left hcov
  set Y := twoLayerIn (K' ⊓ centralizer ({t'} : Set G)) with hY
  have hYsup' : Y ⊔ oddCoreIn K' = K' := by
    rw [hYL]
    exact hYsup
  have hYK' : Y ≤ K' := by
    rw [hYL]
    exact hY2.1.trans inf_le_left
  have hYX : Y ≤ conjugate M g := (h212.trans (solomonKStarOf_le_twoLayerIn _)).trans hLg
  refine mem_normalizer_of_covers_modO hS hq hG hr hKH hCb hK' hYX fun a ha => ?_
  have hYO : Y ≤ normalizer (oddCoreIn K' : Set G) := hYK'.trans (le_normalizer_oddCoreIn K')
  have ha' : a ∈ oddCoreIn K' ⊔ Y := by
    rw [sup_comm, hYsup']
    exact ha
  obtain ⟨o, ho, y, hy, rfl⟩ := exists_mul_of_mem_sup_normalizer hYO ha'
  have h1 : y⁻¹ * o * y ∈ oddCoreIn K' := by
    have := (mem_normalizer_iff.mp (hYO (inv_mem hy)) o).mp ho
    rwa [inv_inv] at this
  have hK'D : K' ≤ D := le_iSup₂_of_le K' hK' le_rfl
  have hK'Dc : IsTwoComponentIn K' D := isTwoComponentIn_of_le hK'.1 hK'D (solomonKStarOf_le N)
  exact ⟨y, hy, y⁻¹ * o * y, oddCoreIn_le_of_isTwoComponentIn hK'Dc h1, by group⟩

theorem lemma313_modO
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hq : QuasisimpleTwoPartInput) (hG : KStarKProper G) {N : Subgroup G}
    (hr : ∃ K₁ ∈ kStarComponents N, ∃ K₂ ∈ kStarComponents N, K₁ ≠ K₂)
    (hKH : solomonKStarOf (normalizer (solomonKStarOf N : Set G)) = solomonKStarOf N)
    (hCb : ∀ K ∈ kStarComponents N, ∀ s ∈ K, orderOf s = 2 →
      centralizer ({s} : Set G) ≤ normalizer (solomonKStarOf N : Set G)) :
    (∀ K ∈ kStarComponents N, ∀ K' ∈ kStarComponents N, ∀ t g : G,
      t ∈ normalizer (solomonKStarOf N : Set G) →
      g⁻¹ * t * g ∈ normalizer (solomonKStarOf N : Set G) → (∃ k : ℕ, t ^ (2 ^ k) = 1) →
      t ∉ center G → (∀ a ∈ K, t⁻¹ * a⁻¹ * t * a ∈ oddCoreIn (solomonKStarOf N)) →
      (∀ a ∈ K', (g⁻¹ * t * g)⁻¹ * a⁻¹ * (g⁻¹ * t * g) * a ∈ oddCoreIn (solomonKStarOf N)) →
      g ∈ normalizer (solomonKStarOf N : Set G)) ∧
    ∀ K ∈ kStarComponents N, ∀ (g : G) (X : Subgroup G),
      X ≤ conjugate (normalizer (solomonKStarOf N : Set G)) g →
      (∀ a ∈ K, ∃ x ∈ X, ∃ o ∈ oddCoreIn (solomonKStarOf N), a = x * o) →
      g ∈ normalizer (solomonKStarOf N : Set G) := by
  refine ⟨fun K hK K' hK' t g htM htgM ht2 htZ htK htgK' => ?_,
    fun K hK g X hX hcov => mem_normalizer_of_covers_modO hS hq hG hr hKH hCb hK hX hcov⟩
  obtain ⟨k, hk⟩ := ht2
  have ht1 : t ≠ 1 := fun h => htZ (h ▸ one_mem _)
  exact mem_normalizer_of_pow_modO hS hq hG hr hKH hCb hK hK' htM htgM hk ht1 htK htgK'

theorem false_of_le_sup_oddCoreIn {N K₁ K₂ K' : Subgroup G} (hK₁ : K₁ ∈ kStarComponents N)
    (hK₂ : K₂ ∈ kStarComponents N) (hne : K₁ ≠ K₂) (h₁ : K₁ ≤ K') (h₂ : K₂ ≤ K')
    (hcov : K' ≤ K₂ ⊔ oddCoreIn K') : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := K' ⊓ N with hY
  have hK₁Y : IsTwoComponentIn K₁ Y := ⟨le_inf h₁ hK₁.1.1,
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf h₁ hK₁.1.1) inf_le_right hK₁.1.2⟩
  have hK₂Y : IsTwoComponentIn K₂ Y := ⟨le_inf h₂ hK₂.1.1,
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf h₂ hK₂.1.1) inf_le_right hK₂.1.2⟩
  have hOY : ∀ o ∈ oddCoreIn K', o ∈ N → o ∈ oddCoreIn Y := by
    intro o ho hoN
    have hn : Y ≤ normalizer (oddCoreIn K' : Set G) :=
      inf_le_left.trans (le_normalizer_oddCoreIn K')
    exact inf_le_oddCoreIn (coprime_card_oddCoreIn K') hn ⟨ho, (map_subtype_le _) ho, hoN⟩
  have hle : K₁ ≤ oddCoreIn Y ⊔ K₂ := by
    intro k hk
    have hK₂O : K₂ ≤ normalizer (oddCoreIn K' : Set G) := h₂.trans (le_normalizer_oddCoreIn K')
    have hk' : k ∈ oddCoreIn K' ⊔ K₂ := by
      rw [sup_comm]
      exact hcov (h₁ hk)
    obtain ⟨o, ho, k₂, hk₂, rfl⟩ := exists_mul_of_mem_sup_normalizer hK₂O hk'
    have hoN : o ∈ N := by
      have e : o = o * k₂ * k₂⁻¹ := by group
      rw [e]
      exact mul_mem (hK₁.1.1 hk) (inv_mem (hK₂.1.1 hk₂))
    exact mul_mem (mem_sup_left (hOY o ho hoN)) (mem_sup_right hk₂)
  exact hne (Sol76.eq_of_le_oddCoreIn_sup hK₁Y hK₂Y hle
    (exists_orderOf_eq_two_of_mem_solomonKStar hK₁.2))

theorem exists_two_mem_of_cover {N M : Subgroup G} (hN : IsSolomonChoice N)
    (hcov : ∀ K ∈ kStarComponents N, ∃ K' ∈ kStarComponents M, K ≤ K' ∧ K' ≤ K ⊔ oddCoreIn K') :
    ∃ K₁ ∈ kStarComponents M, ∃ K₂ ∈ kStarComponents M, K₁ ≠ K₂ := by
  obtain ⟨K₁, h₁, K₂, h₂, hne⟩ := exists_two_mem_kStarComponents hN
  obtain ⟨K'₁, hK'₁, hle₁, -⟩ := hcov K₁ h₁
  obtain ⟨K'₂, hK'₂, hle₂, hcov₂⟩ := hcov K₂ h₂
  refine ⟨K'₁, hK'₁, K'₂, hK'₂, fun h => ?_⟩
  rw [← h] at hle₂ hcov₂
  exact false_of_le_sup_oddCoreIn h₁ h₂ hne hle₁ hle₂ hcov₂

theorem normalizer_ne_top_of_cover {N M : Subgroup G} (hN : IsSolomonChoice N)
    (hcov : ∀ K ∈ kStarComponents N, ∃ K' ∈ kStarComponents M, K ≤ K' ∧ K' ≤ K ⊔ oddCoreIn K') :
    normalizer (solomonKStarOf M : Set G) ≠ ⊤ := by
  intro htop
  apply hN.2.1
  have hDn : (solomonKStarOf M).Normal := normalizer_eq_top_iff.mp htop
  refine iSup₂_le fun K hK => ?_
  obtain ⟨K', hK', hKK', -⟩ := hcov K hK
  have hK'D : K' ≤ solomonKStarOf M := le_iSup₂_of_le K' hK' le_rfl
  have hK'Dc : IsTwoComponentIn K' (solomonKStarOf M) :=
    isTwoComponentIn_of_le hK'.1 hK'D (solomonKStarOf_le M)
  exact hKK'.trans (le_solomonKStarOf_top hK'Dc hDn hK'.2)

end CFSG.ComponentClassification.Sol76T13

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.Open
open scoped commutatorElement

theorem false_of_semisimple_family
    {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ} (hr : 2 ≤ r)
    (Abar : Fin r → Subgroup (↥D ⧸ aschbacherThm5OddCore ↥D))
    (hdistinct : Function.Injective Abar)
    (hsemisimple : ∀ i, aschbacherThm5IsSemisimple (Abar i))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ Abar i, ∀ y ∈ Abar j, x * y = y * x)
    (hgen : ⨆ i, Abar i = ⊤)
    (hperm : ∀ h ∈ Subgroup.normalizer (D : Set G), ∀ i, ∃ j,
      (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj h).toMonoidHom =
        aschbacherThm5Preimage D (Abar j))
    (hi : ∀ (i j : Fin r) (t g : G), (∃ k : ℕ, t ^ (2 ^ k) = 1) → t ∉ Subgroup.center G →
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar i)) t →
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar j))
        (g⁻¹ * t * g) →
      g ∈ Subgroup.normalizer (D : Set G))
    (hii : ∀ (i : Fin r) (g : G) (X : Subgroup G),
      X ≤ (Subgroup.normalizer (D : Set G)).map (MulAut.conj g⁻¹).toMonoidHom →
      (∀ a ∈ aschbacherThm5Preimage D (Abar i), ∃ x ∈ X, ∃ o ∈ aschbacherThm5Core D,
        a = x * o) →
      g ∈ Subgroup.normalizer (D : Set G))
    (hH : Subgroup.normalizer (D : Set G) ≠ ⊤)
    (hrank : ∀ i, 2 ≤ CFSG.pRank 2 (aschbacherThm5Preimage D (Abar i))) : False := by
  rcases Open.aschbacher_component_type_theorem_five G D r (by omega) Abar hdistinct hsemisimple
    hcomm hgen hperm hi hii hH with h | ⟨-, hrank'⟩
  · omega
  · have h3 := (hrank' ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp)).2.1
    have h4 : 2 ≤ Open.pRank 2 (aschbacherThm5Preimage D (Abar ⟨0, by omega⟩)) := by
      have h := hrank ⟨0, by omega⟩
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
      rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h
    omega

theorem false_of_lemma313_at
    {G : Type} [Group G] [Finite G] {M₀ : Subgroup G}
    (hr : ∃ K₁ ∈ kStarComponents M₀, ∃ K₂ ∈ kStarComponents M₀, K₁ ≠ K₂)
    (htop : normalizer (solomonKStarOf M₀ : Set G) ≠ ⊤)
    (hCb : ∀ K ∈ kStarComponents M₀, ∀ s ∈ K, orderOf s = 2 →
      centralizer ({s} : Set G) ≤ normalizer (solomonKStarOf M₀ : Set G))
    (h1 : ∀ K ∈ kStarComponents M₀, ∀ K' ∈ kStarComponents M₀, ∀ t g : G,
      t ∈ normalizer (solomonKStarOf M₀ : Set G) →
      g⁻¹ * t * g ∈ normalizer (solomonKStarOf M₀ : Set G) → (∃ k : ℕ, t ^ (2 ^ k) = 1) →
      t ∉ center G → (∀ a ∈ K, t⁻¹ * a⁻¹ * t * a ∈ oddCoreIn (solomonKStarOf M₀)) →
      (∀ a ∈ K', (g⁻¹ * t * g)⁻¹ * a⁻¹ * (g⁻¹ * t * g) * a ∈ oddCoreIn (solomonKStarOf M₀)) →
      g ∈ normalizer (solomonKStarOf M₀ : Set G))
    (h2 : ∀ K ∈ kStarComponents M₀, ∀ (g : G) (X : Subgroup G),
      X ≤ conjugate (normalizer (solomonKStarOf M₀ : Set G)) g →
      (∀ a ∈ K, ∃ x ∈ X, ∃ o ∈ oddCoreIn (solomonKStarOf M₀), a = x * o) →
      g ∈ normalizer (solomonKStarOf M₀ : Set G)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin ↥(kStarComponents M₀)
  set K : Fin r → Subgroup G := fun i => ((e.symm i : ↥(kStarComponents M₀)) : Subgroup G)
    with hKdef
  have hKiff : ∀ J, J ∈ kStarComponents M₀ ↔ ∃ i, K i = J := by
    intro J
    refine ⟨fun hJ => ⟨e ⟨J, hJ⟩, by simp [hKdef]⟩, ?_⟩
    rintro ⟨i, rfl⟩
    exact (e.symm i).2
  have hKinj : Function.Injective K := fun i j h => e.symm.injective (Subtype.ext h)
  have hr2 : 2 ≤ r := by
    obtain ⟨K₁, h₁, K₂, h₂, hne⟩ := hr
    by_contra hlt
    apply hne
    have i₁ := (e ⟨K₁, h₁⟩).isLt
    have i₂ := (e ⟨K₂, h₂⟩).isLt
    have heq : e ⟨K₁, h₁⟩ = e ⟨K₂, h₂⟩ := Fin.ext (by omega)
    exact congrArg Subtype.val (e.injective heq)
  have hcommN : ∀ i j, i ≠ j → ⁅K i, K j⁆ ≤ oddCoreIn M₀ := fun i j hij =>
    FooteLit.commutator_le_oddCoreIn_of_ne ((hKiff (K i)).mpr ⟨i, rfl⟩).1
      ((hKiff (K j)).mpr ⟨j, rfl⟩).1 fun h => hij (hKinj h)
  set D := solomonKStarOf M₀ with hD
  set H := normalizer (D : Set G) with hH
  have hKmem : ∀ i, K i ∈ kStarComponents M₀ := fun i => (hKiff (K i)).mpr ⟨i, rfl⟩
  have hDgen : ⨆ i, K i = D := by
    apply le_antisymm
    · exact iSup_le fun i => le_iSup₂_of_le (K i) (hKmem i) le_rfl
    · refine iSup₂_le fun J hJ => ?_
      obtain ⟨i, rfl⟩ := (hKiff J).mp hJ
      exact le_iSup K i
  have hKD : ∀ i, K i ≤ D := fun i => hDgen ▸ le_iSup K i
  have hDN : D ≤ M₀ := iSup₂_le fun J hJ => hJ.1.1
  have hKtwo : ∀ i, IsTwoComponentIn (K i) D := fun i =>
    isTwoComponentIn_of_le (hKmem i).1 (hKD i) hDN
  have hcommD : ∀ i j, i ≠ j → ⁅K i, K j⁆ ≤ oddCoreIn D := by
    intro i j hij
    refine le_trans (le_inf (hcommN i j hij) ?_) (oddCoreIn_inf_le hDN)
    exact commutator_le.mpr fun x hx y hy =>
      D.mul_mem (D.mul_mem (D.mul_mem (hKD i hx) (hKD j hy)) (D.inv_mem (hKD i hx)))
        (D.inv_mem (hKD j hy))
  have hHtop : H ≠ ⊤ := htop
  set Abar : Fin r → Subgroup (↥D ⧸ aschbacherThm5OddCore ↥D) :=
    fun i => ((K i).subgroupOf D).map (QuotientGroup.mk' _) with hAbar
  have hpre : ∀ i, aschbacherThm5Preimage D (Abar i) = K i ⊔ oddCoreIn D := fun i =>
    aschbacherThm5Preimage_map_subgroupOf (hKD i)
  have hcore : aschbacherThm5Core D = oddCoreIn D := aschbacherThm5Core_eq_oddCoreIn D
  have hq : ∀ i, CFSG.IsQuasisimple ↥(Abar i) := fun i =>
    isQuasisimple_image (hKtwo i) _ (aschbacherThm5OddCore_eq_pPrimeCore' _)
  have hcomm : ∀ i j, i ≠ j → ∀ x ∈ Abar i, ∀ y ∈ Abar j, x * y = y * x := by
    rintro i j hij _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, aschbacherThm5OddCore_eq_pPrimeCore']
    have hmem : ((a * b)⁻¹ * (b * a) : D) ∈ ((oddCoreIn D).subgroupOf D) := by
      rw [mem_subgroupOf]
      have h3 : (((a * b)⁻¹ * (b * a) : D) : G) = ⁅(b : G)⁻¹, (a : G)⁻¹⁆ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, inv_inv, mul_inv_rev]
        group
      rw [h3]
      exact hcommD j i (Ne.symm hij) (commutator_mem_commutator (inv_mem hb) (inv_mem ha))
    rw [mem_subgroupOf] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    rwa [Subtype.ext hyx] at hy
  have hdistinct : Function.Injective Abar := by
    intro i j hij
    by_contra hne
    obtain ⟨-, -, a, b, hab⟩ := hq i
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    have hbj : (b : ↥D ⧸ aschbacherThm5OddCore ↥D) ∈ Abar j := by rw [← hij]; exact b.2
    exact Subtype.ext (hcomm i j hne a a.2 b hbj)
  have hsemisimple : ∀ i, aschbacherThm5IsSemisimple (Abar i) := fun i =>
    ⟨1, fun _ => Abar i, one_pos, fun _ => ⟨le_rfl, (hq i).1.commutator_eq_top, (hq i).2.1⟩,
      fun l m hlm => absurd (Subsingleton.elim l m) hlm, iSup_const⟩
  have hgen : ⨆ i, Abar i = ⊤ := iSup_map_subgroupOf_eq_top hKD hDgen _
  have hperm : ∀ h ∈ normalizer (D : Set G), ∀ i, ∃ j,
      (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj h).toMonoidHom =
        aschbacherThm5Preimage D (Abar j) := by
    intro h hh i
    simp only [hpre]
    exact exists_map_conj_eq hKtwo hDgen hh i
  have hinv : ∀ i, ∃ b ∈ K i, orderOf b = 2 := fun i =>
    exists_orderOf_eq_two_of_pRank ((by norm_num : 1 ≤ 2).trans
      (two_le_pRank_of_mem_solomonKStar (hKmem i).2))
  have hcov : ∀ i (s : G), (∃ k : ℕ, s ^ (2 ^ k) = 1) →
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar i)) s →
      s ∈ H := by
    rintro i s ⟨k, hk⟩ hs
    rw [hcore, hpre] at hs
    obtain ⟨b, hbK, hb⟩ := hinv i
    exact mem_of_centralizes_quotient (hKD i) le_normalizer hbK hb (hCb _ (hKmem i) b hbK hb) hk hs
  have hi : ∀ (i j : Fin r) (t g : G), (∃ k : ℕ, t ^ (2 ^ k) = 1) → t ∉ center G →
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar i)) t →
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar j))
        (g⁻¹ * t * g) →
      g ∈ normalizer (D : Set G) := by
    intro i j t g ht htZ hti htj
    have htH := hcov i t ht hti
    have htg : ∃ k : ℕ, (g⁻¹ * t * g) ^ (2 ^ k) = 1 := by
      obtain ⟨k, hk⟩ := ht
      refine ⟨k, ?_⟩
      rw [show g⁻¹ * t * g = g⁻¹ * t * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hk]
      group
    have htgH := hcov j _ htg htj
    rw [hcore, hpre] at hti htj
    exact h1 (K i) (hKmem i) (K j) (hKmem j) t g htH htgH ht htZ
      (fun a ha => hti a (mem_sup_left ha)) (fun a ha => htj a (mem_sup_left ha))
  have hii : ∀ (i : Fin r) (g : G) (X : Subgroup G),
      X ≤ (normalizer (D : Set G)).map (MulAut.conj g⁻¹).toMonoidHom →
      (∀ a ∈ aschbacherThm5Preimage D (Abar i), ∃ x ∈ X, ∃ o ∈ aschbacherThm5Core D,
        a = x * o) →
      g ∈ normalizer (D : Set G) := by
    intro i g X hX hXa
    rw [hcore, hpre] at hXa
    exact h2 (K i) (hKmem i) g X hX (fun a ha => hXa a (mem_sup_left ha))
  have hrank : ∀ i, 2 ≤ CFSG.pRank 2 (aschbacherThm5Preimage D (Abar i)) := by
    intro i
    rw [hpre]
    rw [show CFSG.pRank 2 ↥(K i ⊔ oddCoreIn D) = CFSG.Open.pRank 2 (K i ⊔ oddCoreIn D) from
      (by rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
        ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup])]
    exact (two_le_pRank_of_mem_solomonKStar (hKmem i).2).trans
      (SectionRank.pRank_mono (p := 2) (by norm_num)
        (le_sup_left : K i ≤ K i ⊔ oddCoreIn D))
  exact false_of_semisimple_family (by omega) Abar hdistinct hsemisimple hcomm hgen hperm hi hii
    hHtop hrank

theorem false316CoverFor_simple_of_schreier
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog) :
    False316CoverFor Sol76T13.simpleAmbient := by
  intro G _ _ hG N hN M hM hcov _ hCbM
  have hq : Sol76T13.QuasisimpleTwoPartInput :=
    Sol76T13.quasisimpleTwoPartInput_of_centralFour Sol76T13.Hq4.quasisimpleCentralFourInput_holds
  have hGK : Sol76T13.KStarKProper G := Sol76T13.kStarKProper_of_simpleAmbient hG
  have hr := Sol76T13.exists_two_mem_of_cover hN hcov
  have htop := Sol76T13.normalizer_ne_top_of_cover hN hcov
  have hKH : solomonKStarOf (normalizer (solomonKStarOf M : Set G)) = solomonKStarOf M :=
    congrArg solomonKStarOf hM.symm
  have hCb : ∀ K ∈ kStarComponents M, ∀ s ∈ K, orderOf s = 2 →
      centralizer ({s} : Set G) ≤ normalizer (solomonKStarOf M : Set G) := fun K hK s hs hs2 =>
    (hCbM K hK s hs hs2).trans hM.le
  obtain ⟨h1, h2⟩ := Sol76T13.lemma313_modO hS hq hGK hr hKH hCb
  exact false_of_lemma313_at hr htop hCb h1 h2

theorem false316CoverFor_simple
    : False316CoverFor Sol76T13.simpleAmbient :=
  false316CoverFor_simple_of_schreier CFSG.RankThree.PartOne.SPOR.schreierFor_catalog

end CFSG.ComponentClassification.Sol76
