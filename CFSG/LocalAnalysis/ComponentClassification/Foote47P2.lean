module

public import CFSG.LocalAnalysis.ComponentClassification.Foote47TwoGroup
public import CFSG.LocalAnalysis.ComponentClassification.Foote47Gen43
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm46Tools

public section

namespace CFSG.ComponentClassification.Foote47

open CFSG Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] def NoEight (X : Subgroup G) : Prop :=
  ∀ F : Subgroup G, F ≤ X → (∀ x ∈ F, x ^ 2 = 1) → Nat.card F ≠ 8

theorem three_le_pRank_of_card_eight {X F : Subgroup G} (hFX : F ≤ X) (hF2 : ∀ x ∈ F, x ^ 2 = 1)
    (hF8 : Nat.card F = 8) : 3 ≤ CFSG.pRank 2 ↥X := by
  have hF : CFSG.Open.IsElemAbelian 2 (F.subgroupOf X) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a ha => Subtype.ext ?_⟩
    · exact commute_of_sq_eq_one hF2 a.2 b.2
    · rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hF2 _ ha
  have hFcard : Nat.card (F.subgroupOf X) = 2 ^ 3 := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hFX).symm.toEquiv, hF8]
    norm_num
  have h3 := SectionRank.le_pRank one_lt_two (le_top : F.subgroupOf X ≤ ⊤) hF hFcard
  rw [← SectionRank.pRank_eq_open_pRank_top] at h3
  exact h3

theorem noEight_iff (X : Subgroup G) : NoEight X ↔ CFSG.pRank 2 ↥X < 3 := by
  constructor
  · intro h
    by_contra h3
    obtain ⟨F, hFX, hF2, hF8⟩ := exists_card_eight_of_le_pRank (not_lt.mp h3)
    exact h F hFX hF2 hF8
  · intro h F hFX hF2 hF8
    exact absurd (three_le_pRank_of_card_eight hFX hF2 hF8) (not_le.mpr h)

theorem NoEight.of_isSylowOf {Q X : Subgroup G} (hQ : IsSylowOf 2 Q X) (hno : NoEight Q) :
    NoEight X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro F hFX hF2 hF8
  have hFp : IsPGroup 2 F := IsPGroup.of_card (n := 3) (by rw [hF8]; norm_num)
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf hQ hFX hFp
  exact hno _ (conjugate_le_of_forall hk) (sq_eq_one_of_mem_conjugate hF2 k)
    (by rw [card_conjugate_eq_card, hF8])

structure Viol (L M : Subgroup G) (t : G) : Prop where
  hM : IsFooteM L M
  ht : orderOf t = 2
  htC : t ∈ coreActionKernel M
  hno : NoEight (coreActionKernel M ⊓ centralizer ({t} : Set G))

omit [Finite G] in
theorem coreActionKernel_conjugate (J : Subgroup G) (g : G) :
    coreActionKernel (conjugate J g) = conjugate (coreActionKernel J) g := by
  ext x
  constructor
  · intro hx
    rw [mem_conjugate_iff]
    have h0 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ ∈ coreActionKernel (conjugate J g) := by
      rw [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group]
      exact hx
    have h1 : g * x * g⁻¹ ∈ coreActionKernel (conjugate (conjugate J g) g⁻¹) :=
      mem_coreActionKernel_conjugate h0
    rwa [conjugate_conjugate_inv] at h1
  · intro hx
    exact mem_coreActionKernel_conjugate (mem_conjugate_iff.mp hx)

theorem exists_card_eight_le_of_isSylowOf (h : FooteSec4 G L) {M T : Subgroup G}
    (hM : IsFooteM L M) (hT : IsSylowOf 2 T (coreActionKernel M)) :
    ∃ E : Subgroup G, E ≤ T ∧ (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hE2, hE8, hEC⟩ := hM.exists_card_eight h
  have hEp : IsPGroup 2 E := IsPGroup.of_card (n := 3) (by rw [hE8]; norm_num)
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf hT hEC hEp
  exact ⟨_, conjugate_le_of_forall hk, sq_eq_one_of_mem_conjugate hE2 k,
    by rw [card_conjugate_eq_card, hE8]⟩

structure ZData (L M T : Subgroup G) (z : G) : Prop where
  hz : orderOf z = 2
  hzC : z ∈ coreActionKernel M
  hKM : footeF L z ≤ M
  hKsup : footeF L z ⊔ oddCoreIn M = M
  hKmax : FootePointedMaximal z (footeF L z)
  hKF : footeF L z ∈ footeFamilyOf L
  hTKle : T ≤ coreActionKernel (footeF L z)
  hTK : IsSylowOf 2 T (coreActionKernel (footeF L z))
  hTKz : IsSylowOf 2 T (coreActionKernel (footeF L z) ⊓ centralizer ({z} : Set G))

theorem zData_of (h : FooteSec4 G L) {M T : Subgroup G} {z : G} (hM : IsFooteM L M)
    (hT : IsSylowOf 2 T (coreActionKernel M)) (hz : orderOf z = 2) (hzT : z ∈ T)
    (hzc : ∀ x ∈ T, x * z = z * x) : ZData L M T z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzC : z ∈ coreActionKernel M := hT.le hzT
  obtain ⟨E, hET, hE2, hE8⟩ := exists_card_eight_le_of_isSylowOf h hM hT
  have hTz : T ≤ centralizer ({z} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hzc x hx)
  have hEC : E ≤ coreActionKernel M ⊓ centralizer ({z} : Set G) :=
    le_inf (hET.trans hT.le) (hET.trans hTz)
  obtain ⟨hKM, hKsup⟩ := footeF_le_of_card_eight h hM hz hzC hE2 hE8 hEC
  obtain ⟨-, -, hKmax, hKF⟩ := foote_lemma_4_5_i h hM hz hzC
  obtain ⟨h45i, h45ii, -⟩ := foote_lemma_4_5_iv h hM hz hzC hE2 hE8 hEC
  have hCzK : centralizer ({z} : Set G) ≤ normalizer (footeF L z : Set G) :=
    le_normalizer_of_mem_footeFamilyOf h.huniq hKmax.1 hKF
  have hTKle : T ≤ coreActionKernel (footeF L z) := fun x hx =>
    mem_coreActionKernel_of_le hKM (hCzK (hTz hx)) (hT.le hx)
  refine ⟨hz, hzC, hKM, hKsup, hKmax, hKF, hTKle, ?_, ?_⟩
  · exact h45i T (hT.of_le (le_inf hT.le hTKle) inf_le_left)
  · exact h45ii T (hT.of_le (le_inf (le_inf hT.le hTKle) hTz) (inf_le_left.trans inf_le_left))

namespace ZData

variable {M T : Subgroup G} {z : G}

theorem centralizer_le_normalizer (h : FooteSec4 G L) (d : ZData L M T z) :
    centralizer ({z} : Set G) ≤ normalizer (footeF L z : Set G) :=
  le_normalizer_of_mem_footeFamilyOf h.huniq d.hKmax.1 d.hKF

theorem mem_coreActionKernel_footeF (h : FooteSec4 G L) (d : ZData L M T z) {x : G}
    (hx : x ∈ coreActionKernel M) (hxz : x ∈ centralizer ({z} : Set G)) :
    x ∈ coreActionKernel (footeF L z) :=
  mem_coreActionKernel_of_le d.hKM (d.centralizer_le_normalizer h hxz) hx

theorem mem_coreActionKernel (d : ZData L M T z) {x : G}
    (hx : x ∈ coreActionKernel (footeF L z)) (hxN : x ∈ normalizer (M : Set G)) :
    x ∈ coreActionKernel M :=
  mem_coreActionKernel_of_sup d.hKM d.hKsup hxN hx

end ZData

theorem isSylowOf_inf_centralizer_footeF (h : FooteSec4 G L) {M T Q₀ : Subgroup G} {t z : G}
    (hv : Viol L M t) (hT : IsSylowOf 2 T (coreActionKernel M)) (htT : t ∈ T)
    (hd : TwoData T t z Q₀)
    (hmax : ∀ M' Q' : Subgroup G, Viol L M' t → IsPGroup 2 Q' →
      Q' ≤ coreActionKernel M' ⊓ centralizer ({t} : Set G) →
      Nat.card Q' ≤ Nat.card ↥(T ⊓ centralizer ({t} : Set G))) :
    IsSylowOf 2 (T ⊓ centralizer ({t} : Set G))
      (centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) ⊓ coreActionKernel (footeF L z)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have dz := zData_of h hv.hM hT hd.hz hd.hzT hd.hzc
  set K := footeF L z with hK
  set Q := T ⊓ centralizer ({t} : Set G) with hQ
  set X := centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) ⊓ coreActionKernel K with hX
  have hTp : IsPGroup 2 T := hT.isPGroup
  have hQp : IsPGroup 2 Q := hTp.to_le inf_le_left
  have hTz : T ≤ centralizer ({z} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hd.hzc x hx)
  have hQX : Q ≤ X := fun x hx =>
    mem_inf.mpr ⟨mem_inf.mpr ⟨hTz (mem_inf.mp hx).1, (mem_inf.mp hx).2⟩,
      dz.hTKle (mem_inf.mp hx).1⟩
  have hz2 : z ^ 2 = 1 := by rw [← hd.hz]; exact pow_orderOf_eq_one z
  have ht2 : t ^ 2 = 1 := by rw [← hv.ht]; exact pow_orderOf_eq_one t
  have htt : t * t = 1 := by rw [← sq]; exact ht2
  have hz1 : z ≠ 1 := fun h1 => by have := hd.hz; rw [h1, orderOf_one] at this; omega
  have ht1 : t ≠ 1 := fun h1 => by have := hv.ht; rw [h1, orderOf_one] at this; omega
  have hzt : z * t = t * z := (hd.hzc t htT).symm
  have hzQ : z ∈ Q := mem_inf.mpr ⟨hd.hzT, mem_centralizer_singleton_iff.mpr hzt⟩
  have htQ : t ∈ Q := mem_inf.mpr ⟨htT, mem_centralizer_singleton_iff.mpr rfl⟩
  obtain ⟨Qs, hQs, hQQs⟩ := exists_isSylowOf_ge_of_le hQX hQp
  have hQsp : IsPGroup 2 Qs := hQs.isPGroup
  suffices hQeq : Qs = Q by rw [← hQeq]; exact hQs
  by_cases hA : NoEight Qs
  ·
    have hQsKz : Qs ≤ coreActionKernel K ⊓ centralizer ({z} : Set G) := fun x hx =>
      mem_inf.mpr ⟨(mem_inf.mp (hQs.le hx)).2, (mem_inf.mp (mem_inf.mp (hQs.le hx)).1).1⟩
    obtain ⟨k, hkX, hk⟩ := exists_conj_le_of_isSylowOf dz.hTKz hQsKz hQsp
    have hkK : k ∈ coreActionKernel K := (mem_inf.mp hkX).1
    have hkz : k ∈ centralizer ({z} : Set G) := (mem_inf.mp hkX).2
    set c := k⁻¹ with hc
    set M' := conjugate M c with hM'
    set T' := conjugate T c with hT'
    have hmemT' : ∀ x, x ∈ T' ↔ k⁻¹ * x * k ∈ T := fun x => by
      rw [hT', mem_conjugate_iff, hc, inv_inv]
    have hQsT' : Qs ≤ T' := fun x hx => (hmemT' x).mpr (hk x hx)
    have hM'F : IsFooteM L M' := isFooteM_conjugate h hv.hM c
    have hT'C : IsSylowOf 2 T' (coreActionKernel M') := by
      rw [hM', coreActionKernel_conjugate]
      have h1 := isSylowOf_map_conj hT c⁻¹
      unfold conjugate
      exact h1
    have htT' : t ∈ T' := hQsT' (hQQs htQ)
    have hkzc : k * z = z * k := mem_centralizer_singleton_iff.mp hkz
    have hT'z : T' ≤ centralizer ({z} : Set G) := by
      intro x hx
      have h1 := hTz ((hmemT' x).mp hx)
      rw [mem_centralizer_singleton_iff] at h1 ⊢
      have h2 : x = k * (k⁻¹ * x * k) * k⁻¹ := by group
      rw [h2]
      calc k * (k⁻¹ * x * k) * k⁻¹ * z = k * (k⁻¹ * x * k) * (k⁻¹ * z) := by group
        _ = k * (k⁻¹ * x * k) * (z * k⁻¹) := by
            rw [show k⁻¹ * z = z * k⁻¹ by
              calc k⁻¹ * z = k⁻¹ * (z * k) * k⁻¹ := by group
                _ = k⁻¹ * (k * z) * k⁻¹ := by rw [hkzc]
                _ = z * k⁻¹ := by group]
        _ = k * ((k⁻¹ * x * k) * z) * k⁻¹ := by group
        _ = k * (z * (k⁻¹ * x * k)) * k⁻¹ := by rw [h1]
        _ = (k * z) * (k⁻¹ * x * k) * k⁻¹ := by group
        _ = (z * k) * (k⁻¹ * x * k) * k⁻¹ := by rw [hkzc]
        _ = z * (k * (k⁻¹ * x * k) * k⁻¹) := by group
    have hT'K : T' ≤ coreActionKernel K := by
      intro x hx
      have h1 := dz.hTKle ((hmemT' x).mp hx)
      have h2 : x = k * (k⁻¹ * x * k) * k⁻¹ := by group
      rw [h2]
      exact mul_mem (mul_mem hkK h1) (inv_mem hkK)
    have hT'Q : T' ⊓ centralizer ({t} : Set G) = Qs :=
      hQs.eq_of_le (le_inf hQsT' fun x hx => (mem_inf.mp (mem_inf.mp (hQs.le hx)).1).2)
        (fun x hx => mem_inf.mpr ⟨mem_inf.mpr ⟨hT'z (mem_inf.mp hx).1, (mem_inf.mp hx).2⟩,
          hT'K (mem_inf.mp hx).1⟩) (hT'C.isPGroup.to_le inf_le_left)
    obtain ⟨E, hET, hE2, hE8⟩ := exists_card_eight_le_of_isSylowOf h hM'F hT'C
    obtain ⟨z', Q₀', hd'⟩ := exists_twoData hT'C.isPGroup hET hE2 hE8 htT' hv.ht
      (by rw [hT'Q]; exact hA)
    have hzT' : z ∈ T' := (hmemT' z).mpr (by
      rw [show k⁻¹ * z * k = z by rw [mul_assoc, ← hkzc, inv_mul_cancel_left]]; exact hd.hzT)
    have hzz' : z = z' := hd'.hzZ z hzT' hd.hz fun y hy =>
      (mem_centralizer_singleton_iff.mp (hT'z hy)).symm
    have hN : normalizer ((Qs : Subgroup G) : Set G) ≤ centralizer ({z} : Set G) := by
      rw [← hT'Q, hzz']
      exact hd'.normalizer_le_centralizer htt
    have hKM' : K ≤ M' := by
      have h1 : conjugate K c = K := conjugate_eq_of_mem_normalizer (inv_mem hkK.1)
      rw [← h1]
      exact map_mono dz.hKM
    have hQsM' : Qs ≤ coreActionKernel M' ⊓ centralizer ({t} : Set G) := fun x hx =>
      mem_inf.mpr ⟨hT'C.le (hQsT' hx), (mem_inf.mp (mem_inf.mp (hQs.le hx)).1).2⟩
    obtain ⟨Q'', hQ'', hQsQ''⟩ := exists_isSylowOf_ge_of_le hQsM' hQsp
    have hQ''eq : Q'' = Qs := by
      by_contra hne
      have hlt : Qs < Q'' := lt_of_le_of_ne hQsQ'' (Ne.symm hne)
      obtain ⟨x, hxQ'', hxQs, hxN⟩ := exists_mem_normalizer_of_lt hQ''.isPGroup hlt
      have hxz := hN hxN
      have hxM' : x ∈ coreActionKernel M' := (mem_inf.mp (hQ''.le hxQ'')).1
      have hxt : x ∈ centralizer ({t} : Set G) := (mem_inf.mp (hQ''.le hxQ'')).2
      have hxK : x ∈ coreActionKernel K :=
        mem_coreActionKernel_of_le hKM' (dz.centralizer_le_normalizer h hxz) hxM'
      have hY : Q'' ⊓ normalizer ((Qs : Subgroup G) : Set G) = Qs :=
        hQs.eq_of_le (le_inf hQsQ'' le_normalizer)
          (fun y hy => by
            have hyz := hN (mem_inf.mp hy).2
            have hyM' : y ∈ coreActionKernel M' := (mem_inf.mp (hQ''.le (mem_inf.mp hy).1)).1
            exact mem_inf.mpr ⟨mem_inf.mpr ⟨hyz, (mem_inf.mp (hQ''.le (mem_inf.mp hy).1)).2⟩,
              mem_coreActionKernel_of_le hKM' (dz.centralizer_le_normalizer h hyz) hyM'⟩)
          (hQ''.isPGroup.to_le inf_le_left)
      exact hxQs (hY ▸ mem_inf.mpr ⟨hxQ'', hxN⟩)
    have hv' : Viol L M' t :=
      ⟨hM'F, hv.ht, hT'C.le htT', NoEight.of_isSylowOf (hQ''eq ▸ hQ'') hA⟩
    have hcard := hmax M' Qs hv' hQsp hQsM'
    exact (Subgroup.eq_of_le_of_card_ge hQQs hcard).symm
  ·
    exfalso
    simp only [NoEight, not_forall, not_not] at hA
    obtain ⟨F, hFQs, hF2, hF8⟩ := hA
    have hZ := isKleinFour_sup_zpowers hz2 ht2 hz1 ht1 (hd.t_ne_z) hzt
    set Z := zpowers z ⊔ zpowers t with hZdef
    have hZQs : Z ≤ Qs := sup_le (zpowers_le.mpr (hQQs hzQ)) (zpowers_le.mpr (hQQs htQ))
    have hFZ : ∀ f ∈ F, ∀ w ∈ Z, f * w = w * f := by
      intro f hf w hw
      have hfz : f ∈ centralizer ({z} : Set G) :=
        (mem_inf.mp (mem_inf.mp (hQs.le (hFQs hf))).1).1
      have hft : f ∈ centralizer ({t} : Set G) :=
        (mem_inf.mp (mem_inf.mp (hQs.le (hFQs hf))).1).2
      have hZf : Z ≤ centralizer ({f} : Set G) := sup_le
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp hfz).symm))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp hft).symm))
      exact (mem_centralizer_singleton_iff.mp (hZf hw)).symm
    obtain ⟨A, hA2, hA8, hZA, hAZF⟩ := exists_card_eight_le_sup hF2 hF8 hZ hFZ
    have hAQs : A ≤ Qs := hAZF.trans (sup_le hZQs hFQs)
    have hAK : A ≤ coreActionKernel K := fun x hx => (mem_inf.mp (hQs.le (hAQs hx))).2
    have hM'F : IsFooteM L (footeME L A) := ⟨z, K, A, dz.hKmax, dz.hKF, hA2, hA8, hAK, rfl⟩
    obtain ⟨-, S, -, -, -, -, hS, -, hAS, -⟩ :=
      foote_lemma_4_5_sylow h dz.hKmax dz.hKF hA2 hA8 hAK
    have hZM' : footeME L Z = footeME L A :=
      (foote_lemma_4_5_ii h hM'F hA2 hA8 (hAS.trans hS.le)).2 Z hZ hZA
    have hZC : Z ≤ coreActionKernel M := sup_le (zpowers_le.mpr dz.hzC) (zpowers_le.mpr hv.htC)
    have hMle : M ≤ footeME L A := hZM' ▸ le_footeME_of_isKleinFour h hv.hM hZ hZC
    have hAp : IsPGroup 2 A := IsPGroup.of_card (n := 3) (by rw [hA8]; norm_num)
    obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf dz.hTK hAK hAp
    have hAkT : conjugate A k ≤ T := conjugate_le_of_forall hk
    have hMk : footeME L (conjugate A k) = M :=
      (foote_lemma_4_5_ii h hv.hM (sq_eq_one_of_mem_conjugate hA2 k)
        (by rw [card_conjugate_eq_card, hA8]) (hAkT.trans hT.le)).1
    rw [footeME_conjugate h.huniq] at hMk
    have hcard : Nat.card (footeME L A) ≤ Nat.card M := by
      rw [← hMk, card_conjugate_eq_card]
    have hMeq : M = footeME L A := Subgroup.eq_of_le_of_card_ge hMle hcard
    have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
      commute_of_sq_eq_one hA2 ha hb
    have hAN : A ≤ normalizer (M : Set G) := by
      intro a ha
      have haZ : a ∈ normalizer (Z : Set G) := by
        rw [mem_normalizer_iff]
        intro w
        have hc : ∀ b ∈ A, ∀ w ∈ Z, b * w * b⁻¹ = w := fun b hb w hw => by
          rw [hAcomm b hb w (hZA hw), mul_inv_cancel_right]
        constructor
        · intro hw
          rw [hc a ha w hw]
          exact hw
        · intro hw
          have h1 := hc a⁻¹ (inv_mem ha) _ hw
          rw [show a⁻¹ * (a * w * a⁻¹) * a⁻¹⁻¹ = w by group] at h1
          rw [h1]
          exact hw
      apply FooteLit.mem_normalizer_of_conjugate_eq
      rw [hMeq, ← hZM', ← footeME_conjugate h.huniq, conjugate_eq_of_mem_normalizer haZ]
    have hAC : A ≤ coreActionKernel M ⊓ centralizer ({t} : Set G) := fun a ha =>
      mem_inf.mpr ⟨dz.mem_coreActionKernel (hAK ha) (hAN ha),
        mem_centralizer_singleton_iff.mpr (hAcomm a ha t (hZA (mem_sup_right (mem_zpowers t))))⟩
    exact hv.hno A hAC hA2 hA8

end CFSG.ComponentClassification.Foote47
