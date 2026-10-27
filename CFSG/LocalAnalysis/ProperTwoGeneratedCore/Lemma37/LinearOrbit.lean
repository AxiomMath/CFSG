module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseOne
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.LinearSetup

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {z : G}

omit [Finite G] in
theorem isCentralInvolution_conj (hz : IsCentralInvolution (S : Subgroup G) z) {n : G}
    (hn : n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)) :
    IsCentralInvolution (S : Subgroup G) (n⁻¹ * z * n) := by
  refine ⟨(Subgroup.mem_normalizer_iff''.mp hn z).mp hz.1,
    (orderOf_inv_mul_mul_eq z n).trans hz.2.1, fun s hs => ?_⟩
  have h := hz.2.2 _ ((Subgroup.mem_normalizer_iff.mp hn s).mp hs)
  calc s * (n⁻¹ * z * n) = n⁻¹ * (n * s * n⁻¹ * z) * n := by group
    _ = n⁻¹ * (z * (n * s * n⁻¹)) * n := by rw [h]
    _ = n⁻¹ * z * n * s := by group

omit [Finite G] in
theorem isCentralInvolution_mul {a b : G} (ha : IsCentralInvolution (S : Subgroup G) a)
    (hb : IsCentralInvolution (S : Subgroup G) b) (hab : a ≠ b) :
    IsCentralInvolution (S : Subgroup G) (a * b) := by
  refine ⟨(S : Subgroup G).mul_mem ha.1 hb.1,
    orderOf_mul_eq_two_of_commute ha.2.1 hb.2.1 (ha.2.2 b hb.1).symm hab, fun s hs => ?_⟩
  rw [← mul_assoc, ha.2.2 s hs, mul_assoc, hb.2.2 s hs, mul_assoc]

@[expose] def centralInJ (hz : IsCentralInvolution (S : Subgroup G) z)
    (J : Subgroup (EscapingQuotient z)) : Set G :=
  {w | IsCentralInvolution (S : Subgroup G) w ∧
    ∀ h : w ∈ (S : Subgroup G), sylowBar hz ⟨w, h⟩ ∈ J}

@[expose] def centralInBarJ (hz : IsCentralInvolution (S : Subgroup G) z)
    (J : Subgroup (EscapingQuotient z)) : Set G :=
  {w | IsCentralInvolution (S : Subgroup G) w ∧ w ≠ z ∧
    ∀ h : w ∈ (S : Subgroup G), escapingBar z * sylowBar hz ⟨w, h⟩ ∈ J}

@[expose] noncomputable def centralJSubgroup (hz : IsCentralInvolution (S : Subgroup G) z)
    (J : Subgroup (EscapingQuotient z)) : Subgroup G :=
  (Subgroup.center (S : Subgroup G) ⊓ J.comap (sylowBar hz)).map (S : Subgroup G).subtype

section CaseOne

variable {H : Subgroup G} (hset : CoreSetting G S H) (hz : IsCentralInvolution (S : Subgroup G) z)
  (hesc : ¬ Subgroup.centralizer ({z} : Set G) ≤ H) {J : Subgroup (EscapingQuotient z)}
  (hJ : CFSG.IsComponent J) (hzJ : escapingBar z ∉ J) {D : Subgroup (EscapingQuotient z)} {q : ℕ}
  (hlin : LinearSylowData J ((sylowBar hz).range ⊓ J) D q)

include hlin in
theorem centralInJ_eq_diff :
    centralInJ hz J = (centralJSubgroup hz J : Set G) \ {1} := by
  ext w
  simp only [centralInJ, Set.mem_ofPred_eq, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hw, hwJ⟩
    refine ⟨⟨⟨w, hw.1⟩, ⟨Subgroup.mem_center_iff.mpr fun s => Subtype.ext (hw.2.2 s s.2),
      hwJ hw.1⟩, rfl⟩, fun h => ?_⟩
    have h2 := hw.2.1
    rw [h, orderOf_one] at h2
    exact absurd h2 (by decide)
  · rintro ⟨⟨w', ⟨hcen, hw'J⟩, rfl⟩, hw1⟩
    have hR : sylowBar hz w' ∈ (sylowBar hz).range ⊓ J := ⟨⟨w', rfl⟩, hw'J⟩
    have hww := mul_self_eq_one_of_sylowBar hz (hlin.sq _ hR)
    refine ⟨⟨w'.2, orderOf_eq_prime (by rw [pow_two]; exact hww) hw1, fun s hs => ?_⟩,
      fun _ => hw'J⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hcen ⟨s, hs⟩)

include hset hesc hJ hzJ in
theorem centralInBarJ_eq_image :
    centralInBarJ hz J = (fun w => z * w) '' centralInJ hz J := by
  have hq := caseOne_quotientData hset hz hesc
  have hzz : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two hz.2.1
  ext x
  simp only [centralInBarJ, centralInJ, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨hx, hxz, hxJ⟩
    refine ⟨z * x, ⟨isCentralInvolution_mul hz hx (Ne.symm hxz), fun h => ?_⟩, ?_⟩
    · have h2 : sylowBar hz ⟨z * x, h⟩ = escapingBar z * sylowBar hz ⟨x, hx.1⟩ := by
        rw [← sylowBar_self hz, ← map_mul]
        rfl
      rw [h2]
      exact hxJ hx.1
    · rw [← mul_assoc, hzz, one_mul]
  · rintro ⟨w, ⟨hw, hwJ⟩, rfl⟩
    have hwz : w ≠ z := by
      rintro rfl
      exact hzJ (hwJ hz.1)
    have hw1 : w ≠ 1 := by
      rintro rfl
      have h2 := hw.2.1
      rw [orderOf_one] at h2
      exact absurd h2 (by decide)
    refine ⟨isCentralInvolution_mul hz hw (Ne.symm hwz), fun h => hw1 ?_, fun h => ?_⟩
    · calc w = z * (z * w) := by rw [← mul_assoc, hzz, one_mul]
        _ = z * z := by rw [h]
        _ = 1 := hzz
    · have h2 : sylowBar hz ⟨z * w, h⟩ = escapingBar z * sylowBar hz ⟨w, hw.1⟩ := by
        rw [← sylowBar_self hz, ← map_mul]
        rfl
      rw [h2, ← mul_assoc, escapingBar_mul_self hz.2.1, one_mul]
      exact hwJ hw.1

include hset hesc hJ hzJ

theorem central_trichotomy {w : G} (hw : IsCentralInvolution (S : Subgroup G) w) :
    w = z ∨ w ∈ centralInJ hz J ∨ w ∈ centralInBarJ hz J := by
  have hq := caseOne_quotientData hset hz hesc
  have h2 : orderOf (sylowBar hz ⟨w, hw.1⟩) = 2 := by
    rw [orderOf_injective _ (sylowBar_injective hz), Subgroup.orderOf_mk, hw.2.1]
  rcases hq.involution_mem_component_or hJ hzJ h2 with h | h
  · exact Or.inr (Or.inl ⟨hw, fun _ => h⟩)
  · by_cases hwz : w = z
    · exact Or.inl hwz
    · exact Or.inr (Or.inr ⟨hw, hwz, fun _ => h⟩)

theorem isConj_of_mem_centralInJ {w w' : G} (hw : w ∈ centralInJ hz J)
    (hw' : w' ∈ centralInJ hz J) : IsConj w w' := by
  have hq := caseOne_quotientData hset hz hesc
  exact (hq.caseOneConfig hJ hzJ).isConj_of_mk_mem (a := ⟨w, hz.le_centralizer hw.1.1⟩)
    (b := ⟨w', hz.le_centralizer hw'.1.1⟩) (by rw [Subgroup.orderOf_mk, hw.1.2.1])
    (by rw [Subgroup.orderOf_mk, hw'.1.2.1]) (hw.2 hw.1.1) (hw'.2 hw'.1.1)

theorem isConj_of_mem_centralInBarJ {w w' : G} (hw : w ∈ centralInBarJ hz J)
    (hw' : w' ∈ centralInBarJ hz J) : IsConj w w' := by
  have hq := caseOne_quotientData hset hz hesc
  exact (hq.caseOneConfig hJ hzJ).isConj_of_bar_mul_mk_mem hz.2.1
    (a := ⟨w, hz.le_centralizer hw.1.1⟩) (b := ⟨w', hz.le_centralizer hw'.1.1⟩)
    (by rw [Subgroup.orderOf_mk, hw.1.2.1]) (by rw [Subgroup.orderOf_mk, hw'.1.2.1])
    (hw.2.2 hw.1.1) (hw'.2.2 hw'.1.1) hw.2.1 hw'.2.1

include hlin in
theorem even_ncard_centralInJ_add_one : Even ((centralInJ hz J).ncard + 1) := by
  obtain ⟨r, hr, -, hrJ, -⟩ := coreSetting_component_fused_class hset hz hesc hJ hzJ
  have h1 : (1 : G) ∈ (centralJSubgroup hz J : Set G) := (centralJSubgroup hz J).one_mem
  have hdiff := Set.ncard_sdiff_singleton_of_mem h1
  rw [← centralInJ_eq_diff hz hlin] at hdiff
  have hrW : (r : G) ∈ centralJSubgroup hz J := by
    have h := (centralInJ_eq_diff hz hlin ▸
      (show (r : G) ∈ centralInJ hz J from ⟨hr, fun _ => hrJ⟩) : (r : G) ∈ _)
    exact h.1
  have hdvd : 2 ∣ Nat.card (centralJSubgroup hz J) := by
    have h := Subgroup.orderOf_dvd_natCard (centralJSubgroup hz J) hrW
    rwa [hr.2.1] at h
  have hpos : 0 < (centralJSubgroup hz J : Set G).ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨1, h1⟩
  rw [hdiff, Nat.sub_add_cancel hpos, ← Nat.card_coe_set_eq]
  exact even_iff_two_dvd.mpr hdvd

include hlin in
theorem caseOne_exists_normalizer_conj_eq {w : G} (hw : IsCentralInvolution (S : Subgroup G) w) :
    ∃ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), n⁻¹ * z * n = w := by
  set N := Subgroup.normalizer ((S : Subgroup G) : Set G)
  set O : Set G := {w | ∃ n ∈ N, n⁻¹ * z * n = w} with hOdef
  set V₁ := centralInJ hz J
  set V₂ := centralInBarJ hz J
  have hOodd : Odd O.ncard := by
    rw [← Nat.card_coe_set_eq]
    exact sylow_normalizer_class_card_odd S hz.1 hz.2.2
  have hOV : ∀ x ∈ O, IsCentralInvolution (S : Subgroup G) x := by
    rintro _ ⟨n, hn, rfl⟩
    exact isCentralInvolution_conj hz hn
  have hVO : ∀ x, IsCentralInvolution (S : Subgroup G) x → IsConj z x → x ∈ O := by
    intro x hx h
    obtain ⟨n, hn, -, hnx⟩ := coreSetting_centralInvolution_fusion hset hz hx h
    exact ⟨n, hn, hnx⟩
  have hzO : z ∈ O := ⟨1, N.one_mem, by group⟩
  have hconjO : ∀ x ∈ O, IsConj z x := by
    rintro _ ⟨n, -, rfl⟩
    exact isConj_iff.mpr ⟨n⁻¹, by rw [inv_inv]⟩
  have hV₁ : (∃ x ∈ V₁, x ∈ O) → V₁ ⊆ O := by
    rintro ⟨x, hx, hxO⟩ y hy
    exact hVO y hy.1 ((hconjO x hxO).trans (isConj_of_mem_centralInJ hset hz hesc hJ hzJ hx hy))
  have hV₂ : (∃ x ∈ V₂, x ∈ O) → V₂ ⊆ O := by
    rintro ⟨x, hx, hxO⟩ y hy
    exact hVO y hy.1
      ((hconjO x hxO).trans (isConj_of_mem_centralInBarJ hset hz hesc hJ hzJ hx hy))
  have hzV₁ : z ∉ V₁ := fun h => hzJ (by have := h.2 hz.1; rwa [sylowBar_self] at this)
  have hzV₂ : z ∉ V₂ := fun h => h.2.1 rfl
  have hV₁V₂ : ∀ x ∈ V₁, x ∉ V₂ := by
    intro x hx hx'
    apply hzJ
    have h := J.mul_mem (hx'.2.2 hx.1.1) (J.inv_mem (hx.2 hx.1.1))
    rwa [mul_inv_cancel_right] at h
  obtain ⟨r, -, -, -, a, -, haS, haz, n, hn, -, hna⟩ :=
    coreSetting_component_fused_class hset hz hesc hJ hzJ
  have haO : a ∈ O := ⟨n, hn, hna⟩
  have hcardV : V₂.ncard = V₁.ncard := by
    change (centralInBarJ hz J).ncard = (centralInJ hz J).ncard
    rw [centralInBarJ_eq_image hset hz hesc hJ hzJ]
    exact Set.ncard_image_of_injective _ (mul_right_injective z)
  have heven := even_ncard_centralInJ_add_one hset hz hesc hJ hzJ hlin
  by_contra hwO
  have hwO' : w ∉ O := fun h => hwO h
  have hwz : w ≠ z := fun h => hwO' (h ▸ hzO)
  have hOeq : ∀ V : Set G, (∀ x ∈ O, x = z ∨ x ∈ V) → V ⊆ O → O = insert z V := by
    intro V h1 h2
    ext x
    refine ⟨fun hx => h1 x hx, ?_⟩
    rintro (rfl | hx)
    · exact hzO
    · exact h2 hx
  rcases (central_trichotomy hset hz hesc hJ hzJ hw).resolve_left hwz with hw₁ | hw₂
  ·
    have hV₁O : ∀ x ∈ V₁, x ∉ O := fun x hx hxO => hwO' (hV₁ ⟨x, hx, hxO⟩ hw₁)
    have hOsplit : ∀ x ∈ O, x = z ∨ x ∈ V₂ := by
      intro x hx
      rcases central_trichotomy hset hz hesc hJ hzJ (hOV x hx) with h | h | h
      · exact Or.inl h
      · exact absurd hx (hV₁O x h)
      · exact Or.inr h
    have haV₂ : a ∈ V₂ := (hOsplit a haO).resolve_left haz
    have hO := hOeq V₂ hOsplit (hV₂ ⟨a, haV₂, haO⟩)
    rw [hO, Set.ncard_insert_of_notMem hzV₂, hcardV] at hOodd
    exact (Nat.not_even_iff_odd.mpr hOodd) heven
  ·
    have hV₂O : ∀ x ∈ V₂, x ∉ O := fun x hx hxO => hwO' (hV₂ ⟨x, hx, hxO⟩ hw₂)
    have hOsplit : ∀ x ∈ O, x = z ∨ x ∈ V₁ := by
      intro x hx
      rcases central_trichotomy hset hz hesc hJ hzJ (hOV x hx) with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd hx (hV₂O x h)
    have haV₁ : a ∈ V₁ := (hOsplit a haO).resolve_left haz
    have hO := hOeq V₁ hOsplit (hV₁ ⟨a, haV₁, haO⟩)
    rw [hO, Set.ncard_insert_of_notMem hzV₁] at hOodd
    exact (Nat.not_even_iff_odd.mpr hOodd) heven

end CaseOne

end CFSG.ProperTwoGeneratedCore.Lemma37
