module

public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizerBasic
public import CFSG.LieType.Chevalley.ChevalleyLargeRootCentralizerFaithful
public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex

public noncomputable section

namespace CFSG.LieType.Chevalley.E6SecondGraphFull

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K]

theorem diagramMap_E6_inv :
    (diagramMap TwistTag.E6 K)⁻¹ = diagramMap TwistTag.E6 K :=
  (eq_inv_of_mul_eq_one_left diagramMap_E6_mul_self).symm

theorem diagramMap_inv_conj_mem
    {y : ModGL TwistTag.E6.tag K}
    (hy : y ∈ adjointGroup TwistTag.E6.tag K) :
    (diagramMap TwistTag.E6 K)⁻¹ * y * diagramMap TwistTag.E6 K ∈
      adjointGroup TwistTag.E6.tag K := by
  have h := (diagramConjAut TwistTag.E6 K ⟨y, hy⟩).2
  rw [coe_diagramConjAut] at h
  rwa [show (diagramMap TwistTag.E6 K)⁻¹ * y * diagramMap TwistTag.E6 K =
    diagramMap TwistTag.E6 K * y * (diagramMap TwistTag.E6 K)⁻¹ by rw [diagramMap_E6_inv]]

theorem conj_inv_mem_adjointGroup
    (hK : ringChar K = 2) {y : ModGL TwistTag.E6.tag K}
    (hy : y ∈ adjointGroup TwistTag.E6.tag K) :
    (pinnedX TwistTag.E6.tag K e6HighestRoot 1 * diagramMap TwistTag.E6 K)⁻¹ * y *
      (pinnedX TwistTag.E6.tag K e6HighestRoot 1 * diagramMap TwistTag.E6 K) ∈
        adjointGroup TwistTag.E6.tag K := by
  obtain ⟨htC, -, -, -⟩ :=
    even_E6_highest_root_graph_fixed_centralizer_intersection K hK one_ne_zero
  have e : (pinnedX TwistTag.E6.tag K e6HighestRoot 1 * diagramMap TwistTag.E6 K)⁻¹ * y *
      (pinnedX TwistTag.E6.tag K e6HighestRoot 1 * diagramMap TwistTag.E6 K) =
        (diagramMap TwistTag.E6 K)⁻¹ * ((pinnedX TwistTag.E6.tag K e6HighestRoot 1)⁻¹ * y *
          pinnedX TwistTag.E6.tag K e6HighestRoot 1) * diagramMap TwistTag.E6 K := by group
  rw [e]
  exact diagramMap_inv_conj_mem (mul_mem (mul_mem (inv_mem htC) hy) htC)

theorem units_map_entrywiseHom_pinnedX_one
    (φ : K →+* K) :
    Units.map (entrywiseHom φ) (pinnedX TwistTag.E6.tag K e6HighestRoot 1) =
      pinnedX TwistTag.E6.tag K e6HighestRoot 1 :=
  Units.ext ((entrywise_pinnedX _ _ _).trans (by rw [map_one]))

theorem units_map_entrywiseHom_secondGraphRep
    (φ : K →+* K) :
    Units.map (entrywiseHom φ)
        (pinnedX TwistTag.E6.tag K e6HighestRoot 1 * diagramMap TwistTag.E6 K) =
      pinnedX TwistTag.E6.tag K e6HighestRoot 1 * diagramMap TwistTag.E6 K := by
  rw [map_mul, units_map_entrywiseHom_pinnedX_one, units_map_entrywiseHom_diagramMap]

section Ordinary

variable {f : ℕ} {k : Type} [Field k]

theorem eq_of_commute_adjointGroup
    (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    {g : ModGL TwistTag.E6.tag k} (hg : g ∈ adjointGroup TwistTag.E6.tag k)
    (a : Fin TwistTag.E6.tag.rank → kˣ)
    (hz : ∀ w ∈ adjointGroup TwistTag.E6.tag k,
      (pinnedX TwistTag.E6.tag k e6HighestRoot 1 * diagramMap TwistTag.E6 k *
          (g * rootDiagUnit TwistTag.E6.tag a))⁻¹ *
        (g * rootDiagUnit TwistTag.E6.tag a *
          (pinnedX TwistTag.E6.tag k e6HighestRoot 1 * diagramMap TwistTag.E6 k)) * w =
      w * ((pinnedX TwistTag.E6.tag k e6HighestRoot 1 * diagramMap TwistTag.E6 k *
          (g * rootDiagUnit TwistTag.E6.tag a))⁻¹ *
        (g * rootDiagUnit TwistTag.E6.tag a *
          (pinnedX TwistTag.E6.tag k e6HighestRoot 1 * diagramMap TwistTag.E6 k)))) :
    g * rootDiagUnit TwistTag.E6.tag a *
        (pinnedX TwistTag.E6.tag k e6HighestRoot 1 * diagramMap TwistTag.E6 k) =
      pinnedX TwistTag.E6.tag k e6HighestRoot 1 * diagramMap TwistTag.E6 k *
        (g * rootDiagUnit TwistTag.E6.tag a) := by
  classical
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hk2 : ringChar k = 2 := E6SecondGraphFixed.ringChar_eq_two_of_card hf hk
  set T := pinnedX TwistTag.E6.tag k e6HighestRoot 1 * diagramMap TwistTag.E6 k with hT
  set x := g * rootDiagUnit TwistTag.E6.tag a with hx
  suffices h1 : (T * x)⁻¹ * (x * T) = 1 from (inv_mul_eq_one.1 h1).symm
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  ·
    have hunit : ∀ u : kˣ, u = 1 := by
      have : Fintype k := Fintype.ofFinite k
      have hcard : Fintype.card kˣ = 1 := by
        rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hk, show f = 1 by omega, pow_one]
      have : Subsingleton kˣ := Fintype.card_le_one_iff_subsingleton.mp hcard.le
      exact fun u => Subsingleton.elim u 1
    have hxg : x = g := by
      rw [hx, show a = 1 from funext fun i => hunit (a i), rootDiagUnit_one, mul_one]
    have hzC : (T * x)⁻¹ * (x * T) ∈ adjointGroup TwistTag.E6.tag k := by
      rw [hxg, show (T * g)⁻¹ * (g * T) = g⁻¹ * (T⁻¹ * g * T) by group]
      exact mul_mem (inv_mem hg) (conj_inv_mem_adjointGroup hk2 hg)
    have hzZ : (⟨_, hzC⟩ : adjointGroup TwistTag.E6.tag k) ∈
        Subgroup.center (adjointGroup TwistTag.E6.tag k) :=
      Subgroup.mem_center_iff.2 fun w => Subtype.ext (hz w w.2).symm
    rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hzZ
    exact congrArg Subtype.val hzZ
  ·
    have h4 : 4 ≤ Nat.card k := by
      rw [hk]
      calc 4 = 2 ^ 2 := rfl
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    set L := AlgebraicClosure k
    set ι : k →+* L := algebraMap k L
    obtain ⟨hιinj, -, hfaith, -⟩ :=
      Chevalley_large_finite_root_centralizer_faithfulness_of_four_le TwistTag.E6.tag k h4 L ι
    have hL2 : ringChar L = 2 := by
      have : CharP k 2 := ringChar.of_eq hk2
      have : CharP L 2 := charP_of_injective_algebraMap ι.injective 2
      exact ringChar.eq L 2
    have hxL : baseChangeGL ι x ∈ adjointGroup TwistTag.E6.tag L := by
      rw [hx, map_mul, baseChangeGL_rootDiagUnit]
      exact mul_mem (baseChangeGL_mem_adjointGroup ι hg)
        (exceptional_Lang_adjoint_diagonal_lift _ L _).1
    have hTL : baseChangeGL ι T =
        pinnedX TwistTag.E6.tag L e6HighestRoot 1 * diagramMap TwistTag.E6 L := by
      rw [hT, baseChangeGL_secondGraphRep]
    have hzL : baseChangeGL ι ((T * x)⁻¹ * (x * T)) ∈ adjointGroup TwistTag.E6.tag L := by
      rw [show (T * x)⁻¹ * (x * T) = x⁻¹ * (T⁻¹ * x * T) by group, map_mul, map_mul, map_mul,
        map_inv, map_inv, hTL]
      exact mul_mem (inv_mem hxL) (conj_inv_mem_adjointGroup hL2 hxL)
    have hcomm : ∀ h ∈ (adjointGroup TwistTag.E6.tag k).map (baseChangeGL ι),
        baseChangeGL ι ((T * x)⁻¹ * (x * T)) * h = h * baseChangeGL ι ((T * x)⁻¹ * (x * T)) := by
      rintro _ ⟨h0, hh0, rfl⟩
      rw [← map_mul, ← map_mul, hz h0 hh0]
    exact hιinj ((hfaith _ hzL hcomm).trans (map_one _).symm)

theorem exists_conj_mul_of_mem_centralizer_adjointGroup
    (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (htC : pinnedX TwistTag.E6.tag k e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag k)
    (β : MulAut (adjointGroup TwistTag.E6.tag k))
    (hβ : MulAut.conj ⟨_, htC⟩ * diagramConjAut TwistTag.E6 k * β =
      β * (MulAut.conj ⟨_, htC⟩ * diagramConjAut TwistTag.E6 k)) :
    ∃ x ∈ twistedFixedGroup TwistTag.E6 k (RingHom.id k),
      pinnedX TwistTag.E6.tag k e6HighestRoot 1 * x =
        x * pinnedX TwistTag.E6.tag k e6HighestRoot 1 ∧
      ∃ (φ : k ≃+* k) (Q : ModGL TwistTag.E6.tag k), (Q = 1 ∨ Q = diagramMap TwistTag.E6 k) ∧
        ∀ h : adjointGroup TwistTag.E6.tag k, (β h : ModGL TwistTag.E6.tag k) =
          x * (Q * Units.map (entrywiseHom φ.toRingHom) (h : ModGL TwistTag.E6.tag k) * Q⁻¹) *
            x⁻¹ := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hk2 : ringChar k = 2 := E6SecondGraphFixed.ringChar_eq_two_of_card hf hk
  obtain ⟨-, hPt, -, -⟩ :=
    even_E6_highest_root_graph_fixed_centralizer_intersection k hk2 one_ne_zero
  set P := diagramMap TwistTag.E6 k with hP
  set T := pinnedX TwistTag.E6.tag k e6HighestRoot 1 * P with hT
  have hPt' : P * pinnedX TwistTag.E6.tag k e6HighestRoot 1 =
      pinnedX TwistTag.E6.tag k e6HighestRoot 1 * P := mul_inv_eq_iff_eq_mul.1 hPt
  obtain ⟨-, hNF2, hNF3⟩ :=
    ordinary_E_exact_automorphism_normal_form TwistTag.E6.tag (Or.inl rfl) k
  obtain ⟨g, a, φ, ε, hβf⟩ := hNF3 β
  have hε : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by
    have h := ε.isLt
    change (ε : ℕ) < 2 at h
    omega
  set Q : ModGL TwistTag.E6.tag k := exactQ TwistTag.E6.tag k ε with hQdef
  have hQ : Q = P ^ (ε : ℕ) := rfl
  have hQ1 : Q = 1 ∨ Q = P := by
    rcases hε with h | h
    · left
      rw [hQ, h, pow_zero]
    · right
      rw [hQ, h, pow_one]
  set x : ModGL TwistTag.E6.tag k := (g : ModGL TwistTag.E6.tag k) * rootDiagUnit TwistTag.E6.tag a
    with hx
  obtain ⟨F, -, hF⟩ := hNF2 1 φ ε
  have hF' : ∀ h : adjointGroup TwistTag.E6.tag k, (F h : ModGL TwistTag.E6.tag k) =
      Q * Units.map (entrywiseHom φ.toRingHom) (h : ModGL TwistTag.E6.tag k) * Q⁻¹ := fun h => by
    rw [hF h, rootDiagUnit_one, one_mul, inv_one, mul_one]
  have hβx : ∀ h : adjointGroup TwistTag.E6.tag k, (β h : ModGL TwistTag.E6.tag k) =
      x * F h * x⁻¹ := fun h => by
    rw [hβf h, hF' h, hx, mul_inv_rev]
    simp only [mul_assoc]
  have hξ : ∀ h : adjointGroup TwistTag.E6.tag k,
      ((MulAut.conj (⟨_, htC⟩ : adjointGroup TwistTag.E6.tag k) * diagramConjAut TwistTag.E6 k) h :
        ModGL TwistTag.E6.tag k) = T * h * T⁻¹ := fun h => by
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_diagramConjAut, ← hP, hT, mul_inv_rev]
    simp only [mul_assoc]
  have hQT : Q * T = T * Q := by
    have h1 : Commute Q (pinnedX TwistTag.E6.tag k e6HighestRoot 1) := by
      rw [hQ]
      exact (show Commute P (pinnedX TwistTag.E6.tag k e6HighestRoot 1) from hPt').pow_left _
    have h2 : Commute Q P := by
      rw [hQ]
      exact (Commute.refl P).pow_left _
    exact (h1.mul_right h2).eq
  have hφT : Units.map (entrywiseHom φ.toRingHom) T = T :=
    units_map_entrywiseHom_secondGraphRep φ.toRingHom
  have hFξ : ∀ h : adjointGroup TwistTag.E6.tag k,
      (F ((MulAut.conj (⟨_, htC⟩ : adjointGroup TwistTag.E6.tag k) *
        diagramConjAut TwistTag.E6 k) h) : ModGL TwistTag.E6.tag k) = T * F h * T⁻¹ := fun h => by
    rw [hF', hξ, map_mul, map_mul, map_inv, hφT, hF']
    calc Q * (T * Units.map (entrywiseHom φ.toRingHom) (h : ModGL TwistTag.E6.tag k) * T⁻¹) * Q⁻¹
        = (Q * T) * Units.map (entrywiseHom φ.toRingHom) (h : ModGL TwistTag.E6.tag k) *
            (Q * T)⁻¹ := by group
      _ = (T * Q) * Units.map (entrywiseHom φ.toRingHom) (h : ModGL TwistTag.E6.tag k) *
            (T * Q)⁻¹ := by rw [hQT]
      _ = _ := by group
  have hzC := conj_commute_of_commute hβx hξ hFξ hβ
  have hxT : x * T = T * x := eq_of_commute_adjointGroup hf hk g.2 a fun w hw => hzC ⟨w, hw⟩
  have hζk : pinnedX TwistTag.E6.tag k e6HighestRoot 1 * (P * x * P⁻¹) *
      (pinnedX TwistTag.E6.tag k e6HighestRoot 1)⁻¹ = x := by
    calc _ = T * x * T⁻¹ := by rw [hT]; group
      _ = x := by rw [← hxT, mul_inv_cancel_right]
  set L := AlgebraicClosure k
  set ι : k →+* L := algebraMap k L
  obtain ⟨Fr, hFr⟩ := exists_frobenius_of_ringChar k L hk2
  have hxL : baseChangeGL ι x ∈ adjointGroup TwistTag.E6.tag L := by
    rw [hx, map_mul, baseChangeGL_rootDiagUnit]
    exact mul_mem (baseChangeGL_mem_adjointGroup ι g.2)
      (exceptional_Lang_adjoint_diagonal_lift _ L _).1
  have hζ : pinnedX TwistTag.E6.tag L e6HighestRoot 1 *
      (diagramMap TwistTag.E6 L * baseChangeGL ι x * (diagramMap TwistTag.E6 L)⁻¹) *
        (pinnedX TwistTag.E6.tag L e6HighestRoot 1)⁻¹ = baseChangeGL ι x := by
    have h := congrArg (baseChangeGL ι) hζk
    rwa [map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, baseChangeGL_pinnedX_one,
      hP, baseChangeGL_diagramMap] at h
  obtain ⟨⟨y, hy, hyx⟩, -⟩ := mem_map_of_conj_fixed hk2 Fr hFr hxL
    (units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr x) hζ
  have hyx' : y = x := baseChangeGL_injective ι hyx
  rw [hyx'] at hy
  have hPx : P * x = x * P := (mem_twistedFixedGroup_id_iff.1 hy).2
  have htx : x * pinnedX TwistTag.E6.tag k e6HighestRoot 1 * P =
      pinnedX TwistTag.E6.tag k e6HighestRoot 1 * x * P := by
    calc x * pinnedX TwistTag.E6.tag k e6HighestRoot 1 * P = x * T := by rw [hT, mul_assoc]
      _ = T * x := hxT
      _ = pinnedX TwistTag.E6.tag k e6HighestRoot 1 * (P * x) := by rw [hT, mul_assoc]
      _ = pinnedX TwistTag.E6.tag k e6HighestRoot 1 * x * P := by rw [hPx, ← mul_assoc]
  exact ⟨x, hy, (mul_right_cancel htx).symm, φ, Q, hQ1, fun h => by rw [hβx, hF']⟩

end Ordinary

theorem secondGraphFullCentralizer_adjointGroup
    {f : ℕ} (hf : 1 ≤ f) (k : Type) [Field k]
    (hk : Nat.card k = 2 ^ f) :
    SecondGraphFullCentralizer (adjointGroup TwistTag.E6.tag k)
      ((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (RingHom.id k)))
      (diagramMap TwistTag.E6 k) (pinnedX TwistTag.E6.tag k e6HighestRoot 1)
      (embeddedFieldAut (RingHom.id k)) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hk2 : ringChar k = 2 := E6SecondGraphFixed.ringChar_eq_two_of_card hf hk
  set Γ := twistedFixedGroup TwistTag.E6 k (RingHom.id k) with hΓ
  set J := Γ.map (baseChangeGL (RingHom.id k)) with hJdef
  have hJ : J = Γ := map_baseChangeGL_id k Γ
  have hJC : J ≤ adjointGroup TwistTag.E6.tag k := by
    rw [hJ]
    exact twistedFixedGroup_le_adjointGroup _ _ _
  have htΓ : pinnedX TwistTag.E6.tag k e6HighestRoot 1 ∈ Γ :=
    E6SecondGraphFixed.pinnedX_e6HighestRoot_mem_twistedFixedGroup hk2
  have htJ : pinnedX TwistTag.E6.tag k e6HighestRoot 1 ∈ J := ⟨_, htΓ, baseChangeGL_id k _⟩
  have hη : ∀ g : adjointGroup TwistTag.E6.tag k, (diagramConjAut TwistTag.E6 k g :
      ModGL TwistTag.E6.tag k) = diagramMap TwistTag.E6 k * g * (diagramMap TwistTag.E6 k)⁻¹ :=
    coe_diagramConjAut TwistTag.E6 k
  have hηΓ : ∀ g : adjointGroup TwistTag.E6.tag k, (g : ModGL TwistTag.E6.tag k) ∈ Γ →
      diagramConjAut TwistTag.E6 k g = g := fun g hg => Subtype.ext (by
    rw [hη, (mem_twistedFixedGroup_id_iff.1 hg).2, mul_inv_cancel_right])
  have hηJ : ∀ g : adjointGroup TwistTag.E6.tag k, (g : ModGL TwistTag.E6.tag k) ∈ J →
      diagramConjAut TwistTag.E6 k g = g := fun g hg => hηΓ g (hJ ▸ hg)
  have hJΓ : ∀ g : J, (g : ModGL TwistTag.E6.tag k) ∈ Γ := fun g => hJ ▸ g.2
  have hact : ∀ (φ : k ≃+* k) (g : J), ((embeddedFieldAut (RingHom.id k) φ g : J) :
      ModGL TwistTag.E6.tag k) =
        Units.map (entrywiseHom φ.toRingHom) (g : ModGL TwistTag.E6.tag k) :=
    fun φ g => by
      rw [coe_embeddedFieldAut (RingHom.id k) φ ⟨g, hJΓ g⟩ g (baseChangeGL_id k _).symm,
        baseChangeGL_id]
  have hQΓ : ∀ (φ : k ≃+* k) (Q : ModGL TwistTag.E6.tag k), (Q = 1 ∨ Q = diagramMap TwistTag.E6 k) →
      ∀ g ∈ Γ, Q * Units.map (entrywiseHom φ.toRingHom) g * Q⁻¹ =
        Units.map (entrywiseHom φ.toRingHom) g := by
    rintro φ Q hQ g hg
    rcases hQ with hQ | hQ
    · rw [hQ, one_mul, inv_one, mul_one]
    · have hm : diagramMap TwistTag.E6 k * Units.map (entrywiseHom φ.toRingHom) g =
          Units.map (entrywiseHom φ.toRingHom) g * diagramMap TwistTag.E6 k :=
        (mem_twistedFixedGroup_id_iff.1 (baseChangeGL_mem_twistedFixedGroup φ.toRingHom hg)).2
      rw [hQ, hm, mul_inv_cancel_right]
  have hdec' : ∀ β ∈ Subgroup.centralizer {MulAut.conj (⟨_, hJC htJ⟩ :
      adjointGroup TwistTag.E6.tag k) * diagramConjAut TwistTag.E6 k}, ∃ x : J,
        x * ⟨_, htJ⟩ = ⟨_, htJ⟩ * x ∧
        ∃ (φ : k ≃+* k) (Q : ModGL TwistTag.E6.tag k), (Q = 1 ∨ Q = diagramMap TwistTag.E6 k) ∧
          (∀ h : adjointGroup TwistTag.E6.tag k, (β h : ModGL TwistTag.E6.tag k) =
            x * (Q * Units.map (entrywiseHom φ.toRingHom) (h : ModGL TwistTag.E6.tag k) * Q⁻¹) *
              (x : ModGL TwistTag.E6.tag k)⁻¹) ∧
          ∀ g : J, (β ⟨g, hJC g.2⟩ : ModGL TwistTag.E6.tag k) =
            ((MulAut.conj x * embeddedFieldAut (RingHom.id k) φ) g : J) := by
    intro β hβ
    have hβ' := Subgroup.mem_centralizer_singleton_iff.1 hβ
    obtain ⟨x, hxΓ, htx, φ, Q, hQ, hβx⟩ :=
      exists_conj_mul_of_mem_centralizer_adjointGroup hf hk (hJC htJ) β hβ'.symm
    have hxJ : x ∈ J := hJ ▸ hxΓ
    refine ⟨⟨x, hxJ⟩, Subtype.ext htx.symm, φ, Q, hQ, hβx, fun g => ?_⟩
    rw [hβx, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hact]
    exact congrArg (fun w => x * w * x⁻¹) (hQΓ φ Q hQ g (hJΓ g))
  refine secondGraphFullCentralizer_of htJ hJC (diagramConjAut TwistTag.E6 k) hη hηJ _ rfl
    (fun β hβ => ?_) (fun β hβ hfix => ?_) (fun φ => ?_)
    (fun x x' φ φ' h => eq_of_conj_mul_embeddedFieldAut_eq hf hk (RingHom.id k) h)
    (fun φ => embeddedFieldAut_pinnedX hk2 (RingHom.id k) φ htJ)
  · obtain ⟨x, hxt, φ, -, -, -, hx⟩ := hdec' β hβ
    exact ⟨x, hxt, φ, hx⟩
  ·
    obtain ⟨x, -, φ, Q, hQ, hβx, hx⟩ := hdec' β hβ
    have hid : MulAut.conj x * embeddedFieldAut (RingHom.id k) φ =
        MulAut.conj 1 * embeddedFieldAut (RingHom.id k) (RingEquiv.refl k) := by
      rw [map_one, embeddedFieldAut_refl, one_mul]
      refine MulEquiv.ext fun g => Subtype.ext ?_
      rw [← hx g, hfix ⟨g, hJC g.2⟩ g.2]
      rfl
    obtain ⟨rfl, rfl⟩ := eq_of_conj_mul_embeddedFieldAut_eq hf hk (RingHom.id k) hid
    have hβQ : ∀ h : adjointGroup TwistTag.E6.tag k, (β h : ModGL TwistTag.E6.tag k) =
        Q * h * Q⁻¹ := fun h => by
      rw [hβx, Subgroup.coe_one, one_mul, inv_one, mul_one]
      congr 2
      exact Units.ext (entrywise_id _)
    rcases hQ with hQ | hQ
    · have hβ1 : β = 1 := MulEquiv.ext fun h => Subtype.ext (by
        rw [hβQ, hQ, one_mul, inv_one, mul_one]
        rfl)
      rw [hβ1]
      exact one_mem _
    · have hβη : β = diagramConjAut TwistTag.E6 k :=
        MulEquiv.ext fun h => Subtype.ext (by rw [hβQ, hη, hQ])
      rw [hβη]
      exact Subgroup.mem_zpowers _
  ·
    have hψ : ∀ h : adjointGroup TwistTag.E6.tag k,
        (exactNormalAut TwistTag.E6.tag k 1 φ 0 h : ModGL TwistTag.E6.tag k) =
          Units.map (entrywiseHom φ.toRingHom) (h : ModGL TwistTag.E6.tag k) := fun h => by
      rw [coe_exactNormalAut_zero, rootDiagUnit_one, one_mul, inv_one, mul_one]
    have hφt := units_map_entrywiseHom_pinnedX_one (K := k) φ.toRingHom
    have hφP := units_map_entrywiseHom_diagramMap (t := TwistTag.E6) (K := k) φ.toRingHom
    refine ⟨exactNormalAut TwistTag.E6.tag k 1 φ 0, Subgroup.mem_centralizer_singleton_iff.2
      (MulEquiv.ext fun h => Subtype.ext ?_), fun g => by rw [hψ, hact]⟩
    change (exactNormalAut TwistTag.E6.tag k 1 φ 0 (MulAut.conj (⟨_, hJC htJ⟩ :
        adjointGroup TwistTag.E6.tag k) (diagramConjAut TwistTag.E6 k h)) :
          ModGL TwistTag.E6.tag k) =
      (MulAut.conj (⟨_, hJC htJ⟩ : adjointGroup TwistTag.E6.tag k)
        (diagramConjAut TwistTag.E6 k (exactNormalAut TwistTag.E6.tag k 1 φ 0 h)) :
          ModGL TwistTag.E6.tag k)
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, hη, hψ, map_mul, map_inv,
      hφt, hφP]

end CFSG.LieType.Chevalley.E6SecondGraphFull
