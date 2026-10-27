module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5MComp
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Reduced3
import CFSG.LocalAnalysis.RankFourTheoremC.PPointAutRank
import CFSG.LocalAnalysis.RankFourTheoremC.PPointFusion
import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantConjugacy
import CFSG.RankThree.PartOne.D4RC.Burnside

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding
  CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

structure Case2Hyp (Y : Type) [Group Y] [Finite Y] (x : Y) : Prop where
  core_eq_bot : primeComplementCore (G := Y) 3 = ⊥
  catalog : CatalogSimpleSections Y
  abelian : ∀ Q : Sylow 3 Y, IsMulCommutative (Q : Subgroup Y)
  ne_one : x ≠ 1
  pow_eq_one : x ^ 3 = 1
  weakClosed : ∀ Q : Sylow 3 Y, x ∈ (Q : Subgroup Y) → ∀ g : Y,
    (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup Y) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x

namespace Case2Hyp

variable {Y : Type} [Group Y] [Finite Y] {x : Y} {K : Subgroup Y}

theorem center_eq_bot (h : Case2Hyp Y x) (hK : IsComponentOf K ⊤) : center K = ⊥ :=
  GL83Generic5MComp.center_eq_bot_of_isComponentOf_of_abelian h.core_eq_bot h.abelian hK

theorem exists_order_three (h : Case2Hyp Y x) (hK : IsComponentOf K ⊤) :
    ∃ t ∈ K, orderOf t = 3 ∧ t ∉ centralizer (K : Set Y) := by
  obtain ⟨R⟩ := (Sylow.nonempty : Nonempty (Sylow 3 Y))
  obtain ⟨t, htRK, hto, htC⟩ :=
    exists_mem_sylow_inf_component Nat.prime_three (by norm_num) h.core_eq_bot R hK
  exact ⟨t, htRK.2, hto, htC⟩

theorem mem_normalizer_of_pow_three (h : Case2Hyp Y x) (hK : IsComponentOf K ⊤) {y : Y}
    (hy : y ^ 3 = 1) : y ∈ normalizer (K : Set Y) := by
  classical
  by_contra hyK
  obtain ⟨t, htK, hto, htC⟩ := h.exists_order_three hK
  have ht3 : t ^ 3 = 1 := hto ▸ pow_orderOf_eq_one t
  set f : ℕ → Subgroup Y := fun i => K.map (MulAut.conj (y ^ i)).toMonoidHom with hf
  have hfK : ∀ i, IsComponentOf (f i) ⊤ := fun i =>
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj (y ^ i)) K).mpr hK
  have key : ∀ i j : ℕ, i < j → j < 3 → f i ≠ f j := by
    intro i j hij hj hfij
    apply hyK
    refine mem_normalizer_of_pow_mem Nat.prime_three hy (m := j - i) ?_ ?_
    · exact (Nat.coprime_of_lt_prime (by omega) (by omega) Nat.prime_three).symm
    · rw [mem_normalizer_iff_map_conj_eq]
      have h1 : f j = (f (j - i)).map (MulAut.conj (y ^ i)).toMonoidHom := by
        simp only [hf]
        rw [← CFSG.RankThreeEvenClassification.Helpers.subgroup_map_conj_mul, ← pow_add,
          Nat.add_sub_cancel' hij.le]
      rw [h1] at hfij
      exact (map_injective (MulAut.conj (y ^ i)).injective hfij).symm
  have hKK : ∀ i j : Fin 3, i ≠ j → f i.val ≤ centralizer (f j.val : Set Y) := by
    intro i j hij
    have hne : f i.val ≠ f j.val := by
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h' | h'
      · exact key _ _ h' j.2
      · exact (key _ _ h' i.2).symm
    exact commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ (hfK _) (hfK _) hne)
  set tt : ℕ → Y := fun i => y ^ i * t * (y ^ i)⁻¹ with htt
  have htt_succ : ∀ n, y * tt n * y⁻¹ = tt (n + 1) := by
    intro n
    simp only [htt, pow_succ']
    group
  have htt_mod : ∀ n, tt (n % 3) = tt n := by
    intro n
    simp only [htt]
    rw [← pow_eq_pow_mod n hy]
  have htp : ∀ i : Fin 3, tt i.val ^ 3 = 1 := by
    intro i
    simp only [htt]
    rw [conj_pow, ht3]
    simp
  have htKi : ∀ i : Fin 3, tt i.val ∈ f i.val := fun i => ⟨t, htK, rfl⟩
  have htCi : ∀ i : Fin 3, tt i.val ∉ centralizer (f i.val : Set Y) := by
    intro i hi
    apply htC
    rw [mem_centralizer_iff]
    intro k hk
    have h1 := mem_centralizer_iff.mp hi (y ^ i.val * k * (y ^ i.val)⁻¹) ⟨k, hk, rfl⟩
    have h2 : y ^ i.val * (k * t) * (y ^ i.val)⁻¹ = y ^ i.val * (t * k) * (y ^ i.val)⁻¹ := by
      calc y ^ i.val * (k * t) * (y ^ i.val)⁻¹
          = (y ^ i.val * k * (y ^ i.val)⁻¹) * tt i.val := by simp only [htt]; group
        _ = tt i.val * (y ^ i.val * k * (y ^ i.val)⁻¹) := h1
        _ = y ^ i.val * (t * k) * (y ^ i.val)⁻¹ := by simp only [htt]; group
    exact mul_left_cancel (mul_right_cancel h2)
  obtain ⟨hE, -⟩ := isElemAbelian_iSup_zpowers (Y := Y) Nat.prime_three
    (fun i : Fin 3 => f i.val) (fun i : Fin 3 => tt i.val) htp htKi htCi hKK Finset.univ
  set B : Subgroup Y := ⨆ i ∈ (Finset.univ : Finset (Fin 3)), zpowers (tt i.val) with hB
  have hval : ∀ i : Fin 3, ((i + 1 : Fin 3) : ℕ) = (i.val + 1) % 3 := by
    intro i
    fin_cases i <;> rfl
  have hyB : y ∈ normalizer (B : Set Y) := by
    refine mem_normalizer_of_map_conj_le ?_
    simp only [hB, Subgroup.map_iSup]
    refine iSup₂_le fun i _ => ?_
    rw [MonoidHom.map_zpowers]
    have hs : (MulAut.conj y).toMonoidHom (tt i.val) = tt ((i + 1 : Fin 3) : ℕ) := by
      rw [hval, htt_mod]
      exact htt_succ i.val
    rw [hs]
    exact le_iSup₂ (f := fun (j : Fin 3) (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
      zpowers (tt j.val)) (i + 1) (Finset.mem_univ _)
  have hBp : IsPGroup 3 B := elementary_isPGroup 3 B hE
  have hyp : IsPGroup 3 (zpowers y) := elementary_isPGroup 3 _ (isElemAbelian_zpowers hy)
  have hsup : IsPGroup 3 (zpowers y ⊔ B : Subgroup Y) :=
    hyp.to_sup_of_normal_right' hBp (zpowers_le.mpr hyB)
  obtain ⟨Q, hQ⟩ := hsup.exists_le_sylow
  have := h.abelian Q
  have hyQ : y ∈ (Q : Subgroup Y) := hQ (mem_sup_left (mem_zpowers y))
  have ht0 : tt 0 = t := by simp [htt]
  have htQ : t ∈ (Q : Subgroup Y) := by
    refine hQ (mem_sup_right ?_)
    rw [← ht0]
    exact le_iSup₂ (f := fun (j : Fin 3) (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
      zpowers (tt j.val)) (0 : Fin 3) (Finset.mem_univ _) (mem_zpowers _)
  have hcomm : y * t = t * y := setLike_mul_comm hyQ htQ
  have ht1 : tt 1 = t := by
    have : tt 1 = y * t * y⁻¹ := by simp [htt]
    rw [this, hcomm]
    group
  have ht1f : t ∈ f 1 := ht1 ▸ htKi 1
  have hf0 : f 0 = K := by
    have h1 : (MulAut.conj (y ^ 0)).toMonoidHom = MonoidHom.id Y := by
      ext g
      simp
    simp only [hf, h1, Subgroup.map_id]
  apply htC
  have := hKK 1 0 (by decide) ht1f
  simpa only [Fin.val_zero, hf0] using this

theorem mem_normalizer_of_mem (h : Case2Hyp Y x) (hK : IsComponentOf K ⊤) (hxK : x ∈ K) {s : Y}
    (hs : s * x * s⁻¹ = x) : s ∈ normalizer (K : Set Y) := by
  by_contra hsK
  have hK' : IsComponentOf (K.map (MulAut.conj s).toMonoidHom) ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj s) K).mpr hK
  have hne : K.map (MulAut.conj s).toMonoidHom ≠ K := fun h' =>
    hsK (mem_normalizer_iff_map_conj_eq.mpr h')
  have hC : K.map (MulAut.conj s).toMonoidHom ≤ centralizer (K : Set Y) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hK' hK hne)
  exact h.ne_one (GL83Generic5MComp.eq_one_of_mem_of_mem_centralizer (h.center_eq_bot hK) hxK
    (hC ⟨x, hxK, hs⟩))

theorem exists_decomp (h : Case2Hyp Y x) (hInn : KFactInnerAction) (hK : IsComponentOf K ⊤)
    (hxN : x ∈ normalizer (K : Set Y)) (hxC : x ∉ centralizer (K : Set Y)) :
    ∃ Q : Sylow 3 Y, x ∈ (Q : Subgroup Y) ∧
      ∃ P : Sylow 3 K, (P : Subgroup K) = (Q : Subgroup Y).subgroupOf K ∧
        (P : Subgroup K) ≠ ⊥ ∧
        ∃ r ∈ (Q : Subgroup Y) ⊓ K, r⁻¹ * x ∈ centralizer (K : Set Y) ∧ orderOf r = 3 := by
  have hZ := h.center_eq_bot hK
  obtain ⟨hsimple, hnonab⟩ := isSimpleGroup_of_isComponentOf_of_center_eq_bot hK hZ
  have hxp : IsPGroup 3 (zpowers x) :=
    elementary_isPGroup 3 _ (isElemAbelian_zpowers h.pow_eq_one)
  obtain ⟨Q, hQ, P, hP⟩ :=
    GL83Generic5MComp.exists_sylow_le_subgroupOf hxp (zpowers_le.mpr hxN)
  have hxQ : x ∈ (Q : Subgroup Y) := hQ (mem_zpowers x)
  have hP1 : (P : Subgroup K) ≠ ⊥ := by
    obtain ⟨t, htQK, hto, -⟩ :=
      exists_mem_sylow_inf_component Nat.prime_three (by norm_num) h.core_eq_bot Q hK
    intro hbot
    have ht : (⟨t, (mem_inf.mp htQK).2⟩ : K) ∈ (P : Subgroup K) := by
      rw [hP, mem_subgroupOf]
      exact (mem_inf.mp htQK).1
    rw [hbot, mem_bot] at ht
    rw [show t = 1 from congrArg Subtype.val ht, orderOf_one] at hto
    exact absurd hto (by norm_num)
  obtain ⟨r, hrQK, hc⟩ := GL83Generic5MComp.exists_inv_mul_mem_centralizer hInn (by norm_num)
    hsimple hnonab (h.catalog.simple_subgroup K hsimple hnonab) (h.abelian Q) hP hP1 hxQ hxN
    h.pow_eq_one
  refine ⟨Q, hxQ, P, hP, hP1, r, hrQK, hc, ?_⟩
  have hrc : Commute r (r⁻¹ * x) := mem_centralizer_iff.mp hc r hrQK.2
  have hrp : r ^ 3 = 1 := by
    have h1 : r ^ 3 * (r⁻¹ * x) ^ 3 = 1 := by
      rw [← hrc.mul_pow, mul_inv_cancel_left, h.pow_eq_one]
    exact GL83Generic5MComp.eq_one_of_mem_of_mem_centralizer hZ (pow_mem hrQK.2 3)
      ((eq_inv_of_mul_eq_one_left h1) ▸ inv_mem (pow_mem hc 3))
  refine orderOf_eq_prime hrp fun hr1 => hxC ?_
  rwa [hr1, inv_one, one_mul] at hc

theorem isCyclic_of_decomp (h : Case2Hyp Y x) (hWC : KFactWeakClosure) (hK : IsComponentOf K ⊤)
    {Q : Sylow 3 Y} (hxQ : x ∈ (Q : Subgroup Y)) {P : Sylow 3 K}
    (hP : (P : Subgroup K) = (Q : Subgroup Y).subgroupOf K) {r : Y}
    (hrQK : r ∈ (Q : Subgroup Y) ⊓ K) (hc : r⁻¹ * x ∈ centralizer (K : Set Y))
    (hro : orderOf r = 3) : IsCyclic (P : Subgroup K) := by
  by_contra hnc
  have hZ := h.center_eq_bot hK
  obtain ⟨hsimple, hnonab⟩ := isSimpleGroup_of_isComponentOf_of_center_eq_bot hK hZ
  have hmem := GL83Generic5MComp.mem_sylow_iff hP
  have := h.abelian Q
  have : IsSimpleGroup K := hsimple
  set r' : K := ⟨r, hrQK.2⟩ with hr'
  obtain ⟨g, hg1, hg2⟩ := hWC 3 Nat.prime_three (by norm_num) K ⊤ inferInstance
    Subgroup.topEquiv.isSimpleGroup
    (by
      obtain ⟨a, b, hab⟩ := hnonab
      exact ⟨⟨a, mem_top a⟩, ⟨b, mem_top b⟩, fun hba => hab (congrArg Subtype.val hba)⟩)
    (IsCatalogGroup.of_mulEquiv Subgroup.topEquiv (h.catalog.simple_subgroup K hsimple hnonab))
    (by rw [coe_top, centralizer_univ, hZ])
    (by
      rw [card_top, ← hro, ← Subgroup.orderOf_mk r hrQK.2]
      exact orderOf_dvd_natCard r')
    P (top_sup_eq _)
    (IsMulCommutative.of_comm fun a b => Subtype.ext (Subtype.ext
      (setLike_mul_comm ((hmem a).mp a.2) ((hmem b).mp b.2))))
    (by
      rw [inf_top_eq]
      exact two_le_pRank_of_not_isCyclic Nat.prime_three (by norm_num) P.isPGroup' hnc)
    (zpowers r') (zpowers_le.mpr ((hmem r').mpr hrQK.1))
    (by rw [Nat.card_zpowers, hr', Subgroup.orderOf_mk, hro])
  have hgr : (g : Y) * r * (g : Y)⁻¹ ∈ (Q : Subgroup Y) :=
    (hmem _).mp (hg1 (mem_map_of_mem _ (mem_zpowers r')))
  obtain ⟨m, hm, -⟩ := GL83Generic5MComp.exists_conj_eq_zpow hZ (h.weakClosed Q hxQ) hxQ
    hrQK.1 hrQK.2 hc g.2 hgr
  refine hg2 (eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (MulAut.conj g).injective]))
  rw [MonoidHom.map_zpowers, zpowers_le]
  have hgm : (MulAut.conj g).toMonoidHom r' = r' ^ m := Subtype.ext (by simpa using hm)
  rw [hgm]
  exact zpow_mem (mem_zpowers _) m

theorem mem_of_decomp (h : Case2Hyp Y x) (hK : IsComponentOf K ⊤)
    {Q : Sylow 3 Y} (hxQ : x ∈ (Q : Subgroup Y)) {P : Sylow 3 K}
    (hP : (P : Subgroup K) = (Q : Subgroup Y).subgroupOf K) (hP1 : (P : Subgroup K) ≠ ⊥)
    (hPc : IsCyclic (P : Subgroup K)) {r : Y} (hrQK : r ∈ (Q : Subgroup Y) ⊓ K)
    (hc : r⁻¹ * x ∈ centralizer (K : Set Y)) (hro : orderOf r = 3) : x ∈ K := by
  have hZ := h.center_eq_bot hK
  have hmem := GL83Generic5MComp.mem_sylow_iff hP
  set r' : K := ⟨r, hrQK.2⟩ with hr'
  have hr'P : r' ∈ (P : Subgroup K) := (hmem r').mpr hrQK.1
  obtain ⟨g, hgN, a, haP, hap, hga⟩ :=
    CFSG.RankThree.PartOne.D4RC.rcb_exists_normalizer_elt_perfect
      hK.2.2.1 P.isPGroup' P.not_dvd_index hPc hP1
  have ha1 : a ≠ 1 := fun ha => hga (by rw [ha, mul_one, mul_inv_cancel])
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, r' ^ j = a := by
    have hr'p : (⟨r', hr'P⟩ : (P : Subgroup K)) ^ 3 = 1 :=
      Subtype.ext (Subtype.ext (by simp [hr', ← hro, pow_orderOf_eq_one]))
    have hr'1 : (⟨r', hr'P⟩ : (P : Subgroup K)) ≠ 1 := fun h1 => by
      have h2 : r = 1 := congrArg Subtype.val (congrArg Subtype.val h1)
      rw [h2, orderOf_one] at hro
      exact absurd hro (by norm_num)
    have heq : zpowers (⟨a, haP⟩ : (P : Subgroup K)) = zpowers ⟨r', hr'P⟩ := by
      rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
        orderOf_eq_prime (Subtype.ext hap) (fun h1 => ha1 (congrArg Subtype.val h1)),
        orderOf_eq_prime hr'p hr'1]
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (heq ▸ mem_zpowers (⟨a, haP⟩ : (P : Subgroup K)))
    exact ⟨j, congrArg Subtype.val hj⟩
  have hgr : (g : Y) * r * (g : Y)⁻¹ ∈ (Q : Subgroup Y) :=
    (hmem _).mp ((mem_normalizer_iff.mp hgN r').mp hr'P)
  obtain ⟨m, hm, hcm⟩ := GL83Generic5MComp.exists_conj_eq_zpow hZ (h.weakClosed Q hxQ) hxQ
    hrQK.1 hrQK.2 hc g.2 hgr
  have hrm : r ^ (m - 1) ≠ 1 := by
    intro hr1
    apply hga
    have hfix : g * r' * g⁻¹ = r' := Subtype.ext (by
      rw [zpow_sub_one, mul_inv_eq_one] at hr1
      simpa [hr1] using hm)
    rw [← conj_zpow, hfix]
  set c := r⁻¹ * x with hcdef
  have hcp : c ^ 3 = 1 := by
    have := h.abelian Q
    have hrx : Commute r⁻¹ x := setLike_mul_comm (inv_mem (mem_inf.mp hrQK).1) hxQ
    have hrp : r ^ 3 = 1 := hro ▸ pow_orderOf_eq_one r
    rw [hcdef, hrx.mul_pow, inv_pow, hrp, inv_one, one_mul, h.pow_eq_one]
  have hc1 : c = 1 := by
    have hcm1 : c ^ (m - 1) = 1 := by rw [zpow_sub_one, hcm, mul_inv_cancel]
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hcp) with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      refine hrm (orderOf_dvd_iff_zpow_eq_one.mp ?_)
      rw [hro, ← h1]
      exact orderOf_dvd_iff_zpow_eq_one.mpr hcm1
  have hxr : x = r := by
    rw [hcdef, inv_mul_eq_one] at hc1
    exact hc1.symm
  exact hxr ▸ hrQK.2

theorem mem_and_pRank_le_one (h : Case2Hyp Y x) (hInn : KFactInnerAction)
    (hWC : KFactWeakClosure) (hK : IsComponentOf K ⊤) (hxN : x ∈ normalizer (K : Set Y))
    (hxC : x ∉ centralizer (K : Set Y)) :
    x ∈ K ∧ CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 1 := by
  obtain ⟨Q, hxQ, P, hP, hP1, r, hrQK, hc, hro⟩ := h.exists_decomp hInn hK hxN hxC
  have hPc := h.isCyclic_of_decomp hWC hK hxQ hP hrQK hc hro
  refine ⟨h.mem_of_decomp hK hxQ hP hP1 hPc hrQK hc hro, ?_⟩
  rw [← CFSG.PreuniquenessRankFour.Helpers.pRank_sylow_eq_globalRank 3 Nat.prime_three P]
  exact pRank_le_one_of_isCyclic Nat.prime_three hPc

end Case2Hyp

end CFSG.LocalAnalysis.RankFourTheoremC
