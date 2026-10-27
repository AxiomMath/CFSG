module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSzEight
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSL25
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4CoverCore
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAschbacherCore
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma49Tools
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitRankOneTools

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup
open scoped MatrixGroups commutatorElement

@[expose] def FooteAschbacherDichotomy (X : Type) [Group X] : Prop :=
  IsCoverOverTwo X (alternatingGroup (Fin 9)) ∨
    ∃ L : Subgroup X, L.Normal ∧
      (Open.fusionIsBenderGroup L ∨ IsCoverOverTwo L (Open.Sz 1) ∨
        Nonempty (L ≃* SL(2, ZMod 5)) ∨ IsCentralSquareSL25 L) ∧
      CFSG.pRank 2 (centralizer (L : Set X)) = 1 ∧
      ∀ x : X, orderOf x = 2 → x ∈ L ⊔ centralizer (L : Set X)

theorem IsCoverOverTwo.of_mulEquiv {Y Y' X : Type*} [Group Y] [Group Y'] [Group X]
    (e : Y' ≃* Y) (h : IsCoverOverTwo Y X) : IsCoverOverTwo Y' X := by
  obtain ⟨π, hπs, hKZ, hKC, hK2⟩ := h
  have hker : (π.comp e.toMonoidHom).ker = π.ker.map e.symm.toMonoidHom := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, mem_map_equiv, MulEquiv.symm_symm]
    rfl
  refine ⟨π.comp e.toMonoidHom, hπs.comp e.surjective, ?_, ?_, ?_⟩
  · intro y hy
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hy
    have h1 : e y ∈ center Y := hKZ hy
    rw [mem_center_iff] at h1 ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul, h1 (e g)]
  · intro y hy
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hy
    have h1 : e y ∈ commutator Y := hKC hy
    have h2 : commutator Y = (commutator Y').map e.toMonoidHom := by
      rw [_root_.commutator_def, _root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr e.surjective]
    rw [h2] at h1
    obtain ⟨z, hz, hze⟩ := mem_map.mp h1
    rw [← e.injective hze]
    exact hz
  · rw [hker, card_map_of_injective e.symm.injective, hK2]

theorem center_eq_bot_of_isSimpleGroup' {S : Type*} [Group S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) : center S = ⊥ := by
  obtain ⟨a, b, hab⟩ := hna
  rcases (center S).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    apply hab
    exact mem_center_iff.mp (h ▸ mem_top b) a

theorem alternatingGroup_nine_simple_nonabelian :
    IsSimpleGroup (alternatingGroup (Fin 9)) ∧
      ∃ a b : alternatingGroup (Fin 9), a * b ≠ b * a := by
  refine ⟨alternatingGroup.isSimpleGroup (by simp), ?_⟩
  have h1 : (Equiv.swap (0 : Fin 9) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 9) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide
  have h2 : (Equiv.swap (1 : Fin 9) 2 * Equiv.swap 2 3) ∈ alternatingGroup (Fin 9) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide
  refine ⟨⟨_, h1⟩, ⟨_, h2⟩, fun h => ?_⟩
  have h3 := congrArg Subtype.val h
  simp only [Subgroup.coe_mul] at h3
  exact absurd h3 (by decide)

theorem exists_mul_ne_of_fusionIsBenderGroup {X : Type*} [Group X] [Finite X]
    (hX : Open.fusionIsBenderGroup X) : ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨q, k, -, hB⟩ := (AschbacherToolkit.BenderExt.benderData_of_isBenderGroup hX).borel
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 2 X))
  obtain ⟨hSE, -⟩ := hB T
  by_contra hcon
  push Not at hcon
  apply hSE.1
  rw [eq_top_iff]
  intro x _
  rw [mem_normalizer_iff]
  intro y
  rw [hcon x y, mul_inv_cancel_right]

section Abstract

variable {B : Type} [Group B] [Finite B]

theorem orderOf_mk_pPrimeCore {x : B} (hx : orderOf x = 2) :
    orderOf (QuotientGroup.mk' (pPrimeCore 2 B) x) = 2 := by
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  apply orderOf_eq_prime
  · rw [← map_pow, hx2, map_one]
  · intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    have h1 := Subgroup.orderOf_dvd_natCard _ h
    rw [hx] at h1
    exact (Nat.not_even_iff_odd.mpr (odd_card_pPrimeCore_two B)) (even_iff_two_dvd.mpr h1)

theorem exists_isPComponent_mem {K' : Subgroup (B ⧸ pPrimeCore 2 B)} (hK' : IsComponent K')
    {t : B} (ht : t ^ 2 = 1) (htK' : QuotientGroup.mk' (pPrimeCore 2 B) t ∈ K') :
    ∃ K : Subgroup B, IsPComponent 2 K ∧ K.map (QuotientGroup.mk' (pPrimeCore 2 B)) = K' ∧
      t ∈ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK, hKmap⟩ := LocalAnalysis.ComponentInitial.exists_isPComponent_of_isComponent 2 hK'
  refine ⟨K, hK, hKmap, mem_of_mk_mem_map (UnbalancedLayer.pPrimeCore_le_normalizer hK)
    (k := 1) (by rw [pow_one]; exact ht) (hKmap ▸ htK')⟩

theorem pRank_eq_pRank_map {K : Subgroup B} (hK : IsPComponent 2 K) :
    CFSG.pRank 2 ↥K = CFSG.pRank 2 ↥(K.map (QuotientGroup.mk' (pPrimeCore 2 B))) := by
  obtain ⟨e⟩ := nonempty_quotientEquivMap hK
  rw [← pRank_quotient_pPrimeCore, UnbalancedLayer.pRank_eq_of_mulEquiv one_lt_two e]

theorem eq_of_isPComponent_of_map_eq {t : B} (ht2 : t ^ 2 = 1)
    {L' : Subgroup (B ⧸ pPrimeCore 2 B)} (hL'n : L'.Normal) (hLq : CFSG.IsQuasisimple ↥L')
    (hrank : CFSG.pRank 2 ↥(centralizer (L' : Set (B ⧸ pPrimeCore 2 B))) = 1)
    (hCinv : ∀ u ∈ centralizer (L' : Set (B ⧸ pPrimeCore 2 B)), orderOf u = 2 →
      u = QuotientGroup.mk' (pPrimeCore 2 B) t)
    (hcl : ∀ X : Subgroup B, IsPComponent 2 X → t ∈ X → CFSG.pRank 2 ↥X ≤ 1 → False)
    {K : Subgroup B} (hK : IsPComponent 2 K)
    (hKmap : K.map (QuotientGroup.mk' (pPrimeCore 2 B)) = L')
    {X : Subgroup B} (hX : IsPComponent 2 X) : X = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX' := hX
  obtain ⟨X', hX'c, -, hXmap, -⟩ := hX'
  rcases CFSG.LocalCores.component_subnormal_subgroup hX'c hL'n.isSubnormal with hle | hc
  · have h1 := eq_of_isComponent_le hX'c hLq hle
    exact UnbalancedLayer.pComponent_eq_of_map_eq hX hK (by rw [hXmap, hKmap, h1])
  · exfalso
    have hX'C : X' ≤ centralizer (L' : Set (B ⧸ pPrimeCore 2 B)) := by
      intro x hx
      rw [mem_centralizer_iff]
      intro l hl
      have h1 : ⁅x, l⁆ ∈ ⁅X', L'⁆ := commutator_mem_commutator hx hl
      rw [hc, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 2
      (even_iff_two_dvd.mp (CatFactsSp4.even_card_of_isPComponent hX))
    have hx2 : orderOf (x : B) = 2 := (Subgroup.orderOf_coe x).trans hx
    have hxX' : QuotientGroup.mk' (pPrimeCore 2 B) (x : B) ∈ X' :=
      hXmap ▸ mem_map_of_mem _ x.2
    have hxt := hCinv _ (hX'C hxX') (orderOf_mk_pPrimeCore hx2)
    have htX : t ∈ X := mem_of_mk_mem_map (UnbalancedLayer.pPrimeCore_le_normalizer hX) (k := 1)
      (by rw [pow_one]; exact ht2) (hXmap ▸ hxt ▸ hxX')
    apply hcl X hX htX
    rw [pRank_eq_pRank_map hX, hXmap]
    calc CFSG.pRank 2 ↥X' ≤ CFSG.pRank 2 ↥(centralizer (L' : Set (B ⧸ pPrimeCore 2 B))) :=
          pRank_le_pRank_of_injective one_lt_two (Subgroup.inclusion hX'C)
            (Subgroup.inclusion_injective hX'C)
      _ = 1 := hrank

theorem mem_sup_zpowers_of_orderOf_eq_two {t : B} (htZ : t ∈ center B)
    {L' : Subgroup (B ⧸ pPrimeCore 2 B)} (hL'n : L'.Normal)
    (hinv : ∀ x : B ⧸ pPrimeCore 2 B, orderOf x = 2 →
      x ∈ L' ⊔ centralizer (L' : Set (B ⧸ pPrimeCore 2 B)))
    (hCinv : ∀ u ∈ centralizer (L' : Set (B ⧸ pPrimeCore 2 B)), orderOf u = 2 →
      u = QuotientGroup.mk' (pPrimeCore 2 B) t)
    (hsq : ∀ l ∈ L', l ^ 2 ∈ centralizer (L' : Set (B ⧸ pPrimeCore 2 B)) → l ^ 2 = 1)
    {K : Subgroup B} (hK : IsPComponent 2 K)
    (hKmap : K.map (QuotientGroup.mk' (pPrimeCore 2 B)) = L')
    {x : B} (hx : orderOf x = 2) : x ∈ K ⊔ zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 B) with hπ
  set C := centralizer (L' : Set (B ⧸ pPrimeCore 2 B)) with hC
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have h1 := hinv (π x) (orderOf_mk_pPrimeCore hx)
  have hCN : C ≤ normalizer (L' : Set (B ⧸ pPrimeCore 2 B)) := by
    rw [normalizer_eq_top]
    exact le_top
  have h2 : π x ∈ ((C ⊔ L' : Subgroup _) : Set (B ⧸ pPrimeCore 2 B)) := by
    rw [sup_comm]
    exact h1
  rw [coe_mul_of_left_le_normalizer_right C L' hCN] at h2
  obtain ⟨c, hc, l, hl, hcl⟩ := Set.mem_mul.mp h2
  have hlc : l * c = c * l := mem_centralizer_iff.mp hc l hl
  have hsq' : c ^ 2 * l ^ 2 = 1 := by
    have : (c * l) ^ 2 = 1 := by rw [hcl, ← map_pow, hx2, map_one]
    rw [← this, sq, sq, sq]
    calc c * c * (l * l) = c * (c * l) * l := by group
      _ = c * (l * c) * l := by rw [hlc]
      _ = c * l * (c * l) := by group
  have hl2C : l ^ 2 ∈ C := by
    rw [eq_inv_of_mul_eq_one_right hsq']
    exact inv_mem (pow_mem hc 2)
  have hl2 : l ^ 2 = 1 := hsq l hl hl2C
  have hc2 : c ^ 2 = 1 := by rw [hl2, mul_one] at hsq'; exact hsq'
  have hcmem : c ∈ zpowers (π t) := by
    by_cases hc1 : c = 1
    · rw [hc1]
      exact one_mem _
    · rw [hCinv c hc (orderOf_eq_prime hc2 hc1)]
      exact mem_zpowers _
  have hmap : (K ⊔ zpowers t).map π = L' ⊔ zpowers (π t) := by
    rw [Subgroup.map_sup, hKmap, MonoidHom.map_zpowers]
  have hxmem : π x ∈ (K ⊔ zpowers t).map π := by
    rw [hmap, ← hcl]
    exact mul_mem (mem_sup_right hcmem) (mem_sup_left hl)
  exact mem_of_mk_mem_map (pPrimeCore_le_normalizer_sup hK htZ) (k := 1)
    (by rw [pow_one]; exact hx2) hxmem

theorem foote_lemma_4_9_abstract {t : B} (ht : orderOf t = 2) (htZ : t ∈ center B)
    (hdich : FooteAschbacherDichotomy (B ⧸ pPrimeCore 2 B))
    (hcl : ∀ X : Subgroup B, IsPComponent 2 X → t ∈ X → CFSG.pRank 2 ↥X ≤ 1 → False)
    (hA9 : ∀ X : Subgroup B, IsPComponent 2 X → t ∈ X →
      IsCoverOverTwo (X ⧸ pPrimeCore 2 X) (alternatingGroup (Fin 9)) → False) :
    ∃ K : Subgroup B, IsPComponent 2 K ∧ (∀ X : Subgroup B, IsPComponent 2 X → X = K) ∧
      ((Open.fusionIsBenderGroup (K ⧸ pPrimeCore 2 K) ∧ t ∉ K) ∨
        (IsCoverOverTwo (K ⧸ pPrimeCore 2 K) (Open.Sz 1) ∧ t ∈ K)) ∧
      ∀ x : B, orderOf x = 2 → x ∈ K ⊔ zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 B) with hπ
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have ht' : orderOf (π t) = 2 := orderOf_mk_pPrimeCore ht
  have htZ' : ∀ y : B ⧸ pPrimeCore 2 B, y * π t = π t * y := by
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ y
    rw [← map_mul, ← map_mul, mem_center_iff.mp htZ y]
  have hcl' : ∀ K' : Subgroup (B ⧸ pPrimeCore 2 B), IsComponent K' → π t ∈ K' →
      CFSG.pRank 2 ↥K' ≤ 1 → False := by
    intro K' hK' htK' hr
    obtain ⟨K, hK, hKmap, htK⟩ := exists_isPComponent_mem hK' ht2 htK'
    exact hcl K hK htK (by rw [pRank_eq_pRank_map hK, hKmap]; exact hr)
  rcases hdich with h9 | ⟨L', hL'n, htype, hrank, hinv⟩
  ·
    exfalso
    obtain ⟨hA9s, hna9⟩ := alternatingGroup_nine_simple_nonabelian
    have h9' := h9
    obtain ⟨π₉, hπ₉s, hK₉Z, hK₉C, -⟩ := h9'
    obtain ⟨hq, -⟩ := isQuasisimple_of_isCoverOverTwo hna9 hπ₉s hK₉Z hK₉C
    have hc : IsComponent (⊤ : Subgroup (B ⧸ pPrimeCore 2 B)) :=
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.topEquiv).symm hq,
        Subgroup.IsSubnormal.top⟩
    obtain ⟨K, hK, hKmap, htK⟩ := exists_isPComponent_mem hc ht2 (mem_top _)
    obtain ⟨e⟩ := nonempty_quotientEquivMap hK
    have e' : K ⧸ pPrimeCore 2 K ≃* B ⧸ pPrimeCore 2 B :=
      (e.trans (MulEquiv.subgroupCongr hKmap)).trans Subgroup.topEquiv
    exact hA9 K hK htK (IsCoverOverTwo.of_mulEquiv e' h9)
  have htC : π t ∈ centralizer (L' : Set (B ⧸ pPrimeCore 2 B)) :=
    mem_centralizer_iff.mpr fun y _ => htZ' y
  have hCinv : ∀ u ∈ centralizer (L' : Set (B ⧸ pPrimeCore 2 B)), orderOf u = 2 → u = π t :=
    fun u hu hu2 => eq_of_commute_of_pRank_eq_one hrank htC hu ht' hu2 (htZ' u).symm
  rcases htype with hBen | hSz | ⟨⟨e⟩⟩ | ⟨L₁, L₂, hsup, hcomm, hcard, ⟨e₁⟩, ⟨e₂⟩⟩
  ·
    have : Finite ↥L' := inferInstance
    have hsimp := QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hBen
    have hna := exists_mul_ne_of_fusionIsBenderGroup hBen
    have hLq : CFSG.IsQuasisimple ↥L' := isQuasisimple_of_isSimpleGroup' hna
    have hZ : center ↥L' = ⊥ := center_eq_bot_of_isSimpleGroup' hna
    obtain ⟨K, hK, hKmap⟩ :=
      LocalAnalysis.ComponentInitial.exists_isPComponent_of_isComponent 2 ⟨hLq, hL'n.isSubnormal⟩
    have hLC : ∀ l ∈ L', l ∈ centralizer (L' : Set (B ⧸ pPrimeCore 2 B)) → l = 1 := by
      intro l hl hlC
      have h1 : (⟨l, hl⟩ : ↥L') ∈ center ↥L' := by
        rw [mem_center_iff]
        intro g
        exact Subtype.ext (mem_centralizer_iff.mp hlC g g.2)
      rw [hZ, mem_bot] at h1
      exact congrArg Subtype.val h1
    obtain ⟨eK⟩ := nonempty_quotientEquivMap hK
    have e' : K ⧸ pPrimeCore 2 K ≃* ↥L' := eK.trans (MulEquiv.subgroupCongr hKmap)
    refine ⟨K, hK, fun X hX => eq_of_isPComponent_of_map_eq ht2 hL'n hLq hrank hCinv hcl hK
      hKmap hX, Or.inl ⟨QuasithinUnique.RankOneRecog.fusionIsBenderGroup_of_mulEquiv e'.symm hBen,
      fun htK => ?_⟩, fun x hx => mem_sup_zpowers_of_orderOf_eq_two htZ hL'n hinv hCinv
      (fun l hl hl2 => hLC _ (pow_mem hl 2) hl2) hK hKmap hx⟩
    have htL : π t ∈ L' := hKmap ▸ mem_map_of_mem π htK
    have h1 := hLC _ htL htC
    rw [h1, orderOf_one] at ht'
    omega
  ·
    have : Finite ↥L' := inferInstance
    obtain ⟨π₈, hπ₈s, hK₈Z, hK₈C, hK₈2⟩ := hSz
    have : Finite (Open.Sz 1) := Finite.of_surjective π₈ hπ₈s
    obtain ⟨hsimp, hna⟩ := sz_one_simple_nonabelian
    obtain ⟨hLq, hker⟩ := isQuasisimple_of_isCoverOverTwo (hX := hsimp) hna hπ₈s hK₈Z hK₈C
    have hZ2 : Nat.card (center ↥L') = 2 := hker ▸ hK₈2
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥L')) 2 (by rw [hZ2])
    have hz2 : orderOf ((z : ↥L') : B ⧸ pPrimeCore 2 B) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
    have hzC : ((z : ↥L') : B ⧸ pPrimeCore 2 B) ∈ centralizer (L' : Set (B ⧸ pPrimeCore 2 B)) := by
      rw [mem_centralizer_iff]
      intro l hl
      exact congrArg Subtype.val (mem_center_iff.mp z.2 ⟨l, hl⟩)
    have hzt := hCinv _ hzC hz2
    have htL : π t ∈ L' := hzt ▸ (z : ↥L').2
    obtain ⟨K, hK, hKmap, htK⟩ := exists_isPComponent_mem ⟨hLq, hL'n.isSubnormal⟩ ht2 htL
    obtain ⟨eK⟩ := nonempty_quotientEquivMap hK
    have e' : K ⧸ pPrimeCore 2 K ≃* ↥L' := eK.trans (MulEquiv.subgroupCongr hKmap)
    have hcov : IsCoverOverTwo ↥L' (Open.Sz 1) := ⟨π₈, hπ₈s, hK₈Z, hK₈C, hK₈2⟩
    refine ⟨K, hK, fun X hX => eq_of_isPComponent_of_map_eq ht2 hL'n hLq hrank hCinv hcl hK
      hKmap hX, Or.inr ⟨IsCoverOverTwo.of_mulEquiv e' hcov, htK⟩, fun x hx =>
      mem_sup_zpowers_of_orderOf_eq_two htZ hL'n hinv hCinv (fun l hl hl2 => ?_) hK hKmap hx⟩
    have h1 : (⟨l, hl⟩ : ↥L') ^ 2 ∈ center ↥L' := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.mp hl2 g g.2)
    have h2 := sq_eq_one_of_sq_mem_center_sz hcov h1
    exact congrArg Subtype.val h2
  ·
    exfalso
    set z₀ : B ⧸ pPrimeCore 2 B := ((e.symm sl25NegOne : L') : B ⧸ pPrimeCore 2 B) with hz₀
    have hz₀C : z₀ ∈ centralizer (L' : Set (B ⧸ pPrimeCore 2 B)) := by
      rw [mem_centralizer_iff]
      intro l hl
      have h1 : (⟨l, hl⟩ : L') * e.symm sl25NegOne = e.symm sl25NegOne * ⟨l, hl⟩ := by
        apply e.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, sl25NegOne_mul_comm]
      exact congrArg Subtype.val h1
    have hz₀2 : orderOf z₀ = 2 := by
      rw [hz₀, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_sl25NegOne]
    have hz₀t : z₀ = π t := hCinv z₀ hz₀C hz₀2
    have hLq : CFSG.IsQuasisimple ↥L' :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm isQuasisimple_sl25
    exact hcl' L' ⟨hLq, hL'n.isSubnormal⟩ (hz₀t ▸ (e.symm sl25NegOne).2)
      (pRank_le_one_of_mulEquiv_sl25 e)
  ·
    exfalso
    set z₀ : B ⧸ pPrimeCore 2 B := ((e₁.symm sl25NegOne : L₁) : B ⧸ pPrimeCore 2 B) with hz₀
    have hz₀L₁ : z₀ ∈ L₁ := (e₁.symm sl25NegOne).2
    have hz₀C₁ : ∀ l ∈ L₁, l * z₀ = z₀ * l := by
      intro l hl
      have h1 : (⟨l, hl⟩ : L₁) * e₁.symm sl25NegOne = e₁.symm sl25NegOne * ⟨l, hl⟩ := by
        apply e₁.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, sl25NegOne_mul_comm]
      exact congrArg Subtype.val h1
    have hle : L₁ ⊔ L₂ ≤ centralizer ({z₀} : Set (B ⧸ pPrimeCore 2 B)) := by
      refine sup_le (fun l hl => mem_centralizer_singleton_iff.mpr (hz₀C₁ l hl)) ?_
      intro l hl
      exact mem_centralizer_singleton_iff.mpr (hcomm z₀ hz₀L₁ l hl).symm
    have hz₀C : z₀ ∈ centralizer (L' : Set (B ⧸ pPrimeCore 2 B)) := by
      rw [mem_centralizer_iff]
      intro l hl
      rw [← hsup] at hl
      exact mem_centralizer_singleton_iff.mp (hle hl)
    have hz₀2 : orderOf z₀ = 2 := by
      rw [hz₀, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_sl25NegOne]
    have hz₀t : z₀ = π t := hCinv z₀ hz₀C hz₀2
    have hL₁L' : L₁ ≤ L' := hsup ▸ le_sup_left
    have hN : L' ≤ normalizer (L₁ : Set (B ⧸ pPrimeCore 2 B)) := by
      rw [← hsup]
      refine sup_le le_normalizer fun l hl => ?_
      rw [mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have h1 : l * x * l⁻¹ = x := by rw [← hcomm x hx l hl]; group
        rw [h1]
        exact hx
      · intro hx
        have h1 : l * x * l⁻¹ * l = l * (l * x * l⁻¹) := hcomm _ hx l hl
        have h2 : x = l * x * l⁻¹ := by
          have h3 : l * x = l * (l * x * l⁻¹) := by rw [← h1]; group
          exact (mul_left_cancel h3)
        rw [h2]
        exact hx
    have hL₁n : (L₁.subgroupOf L').Normal :=
      (normal_subgroupOf_iff_le_normalizer hL₁L').mpr hN
    have hL₁c : IsComponent L₁ :=
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e₁.symm isQuasisimple_sl25,
        Subgroup.IsSubnormal.trans hL₁L' hL₁n.isSubnormal hL'n.isSubnormal⟩
    exact hcl' L₁ hL₁c (hz₀t ▸ hz₀L₁) (pRank_le_one_of_mulEquiv_sl25 e₁)

end Abstract

end CFSG.ComponentClassification.FooteLit
