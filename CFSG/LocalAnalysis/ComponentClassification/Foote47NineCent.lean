module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFooteGen

public noncomputable section

namespace CFSG.ComponentClassification.Foote47.Nine

open CFSG GorensteinWalter Subgroup CFSG.ComponentClassification.AutL2Facts

variable {F : Type} [Field F] [Finite F]

theorem card_centralizer_four_le
    (hodd : IsOddPrimePower (Nat.card F))
    {U : Subgroup (PGammaL2 F)} (hU4 : Nat.card U = 4) (hU2 : ∀ u ∈ U, u * u = 1)
    (hUr : ∀ u ∈ U, u.right = 1) :
    Nat.card (centralizer (U : Set (PGammaL2 F))) ≤ 4 * Nat.card (F ≃+* F) := by
  have hUle : U ≤ (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).range := fun u hu =>
    ⟨u.left, SemidirectProduct.ext (SemidirectProduct.left_inl _)
      ((SemidirectProduct.right_inl _).trans (hUr u hu).symm)⟩
  have hV4 : Nat.card (linearPart U) = 4 := by
    rw [← card_map_of_injective (f := (SemidirectProduct.inl : PGL2 F →* PGammaL2 F))
      SemidirectProduct.inl_injective, map_comap_eq_self hUle, hU4]
  have hVK : IsKleinFour (linearPart U) := isKleinFour_of_card_four_sq hV4 fun g =>
    Subtype.ext (SemidirectProduct.inl_injective (by
      rw [Subgroup.coe_pow, map_pow, Subgroup.coe_one, map_one, pow_two]
      exact hU2 _ g.2))
  have : Finite (linearPart U) := Nat.finite_of_card_ne_zero (by rw [hV4]; norm_num)
  have hle : linearPart (centralizer (U : Set (PGammaL2 F))) ≤ linearPart U := by
    intro g hg
    rw [← pgl2_kleinFour_centralizer_eq_self F hodd _ hVK, mem_centralizer_iff]
    intro h hh
    apply SemidirectProduct.inl_injective (φ := pgl2FieldAut F)
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.mp hg _ hh
  rw [card_eq_linearPart_mul]
  exact Nat.mul_le_mul (hV4 ▸ card_le_of_le hle) (card_le_card_group _)

theorem eq_mul_of_four {G : Type*} [Group G] {U : Subgroup G} (hU4 : Nat.card U = 4)
    (hU2 : ∀ u ∈ U, u * u = 1) {a b c : G} (ha : a ∈ U) (hb : b ∈ U) (hc : c ∈ U)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hc1 : c ≠ 1) (hca : c ≠ a) (hcb : c ≠ b) :
    c = a * b := by
  have : IsKleinFour U := isKleinFour_of_card_four_sq hU4 fun g =>
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]; exact hU2 _ g.2)
  have h := IsKleinFour.eq_mul_of_ne_all (G := U) (x := ⟨a, ha⟩) (y := ⟨b, hb⟩) (z := ⟨c, hc⟩)
    (fun h => ha1 (congrArg Subtype.val h)) (fun h => hb1 (congrArg Subtype.val h))
    (fun h => hab (congrArg Subtype.val h)) (fun h => hc1 (congrArg Subtype.val h))
    (fun h => hca (congrArg Subtype.val h)) (fun h => hcb (congrArg Subtype.val h))
  exact congrArg Subtype.val h

theorem exists_normalizing_sq_mem {G : Type*} [Group G] {T E : Subgroup G} [Finite T]
    (hT2 : IsPGroup 2 T) (hET : E ≤ T) (hne : E ≠ T) :
    ∃ x ∈ T, x ∉ E ∧ x * x ∈ E ∧ ∀ e ∈ E, x * e * x⁻¹ ∈ E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hT2.isNilpotent
  have hlt : E.subgroupOf T < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne (le_antisymm hET fun g hg => ?_)
    have : (⟨g, hg⟩ : T) ∈ E.subgroupOf T := h ▸ mem_top _
    exact this
  obtain ⟨y, hyN, hyE⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hyn : ∀ e ∈ E, (y : G) * e * (y : G)⁻¹ ∈ E := fun e he =>
    (mem_normalizer_iff.mp hyN ⟨e, hET he⟩).mp he
  have hpow : ∀ k : ℕ, ∀ e ∈ E, (y : G) ^ k * e * ((y : G) ^ k)⁻¹ ∈ E := by
    intro k
    induction k with
    | zero => intro e he; simpa using he
    | succ k ih =>
      intro e he
      have h := hyn _ (ih e he)
      convert h using 1
      rw [pow_succ']
      group
  obtain ⟨n, hn⟩ := hT2 y
  have hn' : (y : G) ^ 2 ^ n = 1 := by rw [← Subgroup.coe_pow, hn, Subgroup.coe_one]
  have hex : ∃ j, (y : G) ^ 2 ^ (j + 1) ∈ E :=
    ⟨n, by rw [pow_succ, pow_mul, hn', one_pow]; exact E.one_mem⟩
  classical
  obtain ⟨m, hm⟩ : ∃ m, m = Nat.find hex := ⟨_, rfl⟩
  have hmE : (y : G) ^ 2 ^ (m + 1) ∈ E := hm ▸ Nat.find_spec hex
  refine ⟨(y : G) ^ 2 ^ m, T.pow_mem y.2 _, fun h => ?_, ?_, hpow _⟩
  · rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero, pow_one] at h
      exact hyE h
    · have hmin := Nat.find_min hex (m := m - 1) (by omega)
      rw [show m - 1 + 1 = m by omega] at hmin
      exact hmin h
  · rw [← pow_add, ← two_mul, ← pow_succ']
    exact hmE

theorem exists_e8_pair
    (hodd : IsOddPrimePower (Nat.card F)) (hAut : Nat.card (F ≃+* F) = 2)
    [Finite (PGammaL2 F)] {T : Subgroup (PGammaL2 F)} (hT2 : IsPGroup 2 T)
    {E : Subgroup (PGammaL2 F)} (hET : E ≤ T) (hE2 : ∀ x ∈ E, x * x = 1) (hE8 : Nat.card E = 8)
    (hnab : ∃ x ∈ T, ∃ y ∈ T, x * y ≠ y * x) :
    ∃ E' : Subgroup (PGammaL2 F), E' ≤ T ∧ (∀ x ∈ E', x * x = 1) ∧ Nat.card E' = 8 ∧
      ∃ t ∈ E, t ∈ E' ∧ t.right = 1 ∧ t ≠ 1 ∧ ∃ t₀ ∈ E, t₀.right = 1 ∧
        ∃ u ∈ E', u.right = 1 ∧ t₀ * u ≠ u * t₀ := by
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    commute_of_forall_sq E hE2 ha hb
  have hinvE : ∀ a ∈ E, a⁻¹ = a := fun a ha => inv_eq_of_mul_eq_one_right (hE2 a ha)
  have hσ2 : ∀ σ : F ≃+* F, σ * σ = 1 := fun σ => by
    rw [← pow_two, ← hAut]
    exact pow_card_eq_one'
  have hne : E ≠ T := by
    rintro rfl
    obtain ⟨a, ha, b, hb, hab⟩ := hnab
    exact hab (hcomm a ha b hb)
  obtain ⟨x, hxT, hxE, hx2, hxN⟩ := exists_normalizing_sq_mem hT2 hET hne
  obtain ⟨U, hUdef⟩ : ∃ U : Subgroup (PGammaL2 F), U = (linearPart E).map SemidirectProduct.inl :=
    ⟨_, rfl⟩
  have hUE : U ≤ E := by
    rw [hUdef]
    rintro _ ⟨A, hA, rfl⟩
    exact hA
  have hUr : ∀ u ∈ U, u.right = 1 := by
    rw [hUdef]
    rintro _ ⟨A, -, rfl⟩
    exact SemidirectProduct.right_inl A
  have hmemU : ∀ e ∈ E, e.right = 1 → e ∈ U := fun e he hr => by
    have h : SemidirectProduct.inl e.left = e := SemidirectProduct.ext
      (SemidirectProduct.left_inl _) ((SemidirectProduct.right_inl _).trans hr.symm)
    rw [hUdef]
    exact ⟨e.left, by change SemidirectProduct.inl e.left ∈ E; rw [h]; exact he, h⟩
  have hU4 : Nat.card U = 4 := by
    rw [hUdef, card_map_of_injective SemidirectProduct.inl_injective,
      card_linearPart_of_card_eight hodd hE2 hE8]
  have hU2 : ∀ u ∈ U, u * u = 1 := fun u hu => hE2 u (hUE hu)
  have hCU : ∀ g : PGammaL2 F, (∀ u ∈ U, u * g = g * u) → g ∈ E := by
    intro g hg
    have hEC : E ≤ centralizer (U : Set (PGammaL2 F)) := fun e he =>
      mem_centralizer_iff.mpr fun u hu => hcomm u (hUE hu) e he
    have hle := card_centralizer_four_le hodd hU4 hU2 hUr
    rw [hAut] at hle
    have heq := eq_of_le_of_card_ge hEC (by rw [hE8]; exact hle)
    rw [heq]
    exact mem_centralizer_iff.mpr hg
  obtain ⟨t₀, ht₀U, hxt₀⟩ : ∃ t₀ ∈ U, x * t₀ * x⁻¹ ≠ t₀ := by
    by_contra h
    push Not at h
    apply hxE
    apply hCU
    intro u hu
    calc u * x = x * u * x⁻¹ * x := by rw [h u hu]
      _ = x * u := by group
  have ht₀E := hUE ht₀U
  obtain ⟨s, hsdef⟩ : ∃ s, s = x * t₀ * x⁻¹ := ⟨_, rfl⟩
  have hsE : s ∈ E := by rw [hsdef]; exact hxN t₀ ht₀E
  have hsU : s ∈ U := hmemU s hsE (by rw [hsdef, right_conj]; exact hUr t₀ ht₀U)
  have hxs : x * s * x⁻¹ = t₀ := by
    calc x * s * x⁻¹ = (x * x) * t₀ * (x * x)⁻¹ := by rw [hsdef]; group
      _ = t₀ := by rw [hcomm _ hx2 t₀ ht₀E]; group
  have hst : s ≠ t₀ := by rw [hsdef]; exact hxt₀
  have ht₀1 : t₀ ≠ 1 := by
    intro h
    apply hxt₀
    rw [h]
    group
  have hs1 : s ≠ 1 := by
    intro h
    apply ht₀1
    calc t₀ = x⁻¹ * s * x := by rw [hsdef]; group
      _ = 1 := by rw [h]; group
  obtain ⟨t, htdef⟩ : ∃ t, t = t₀ * s := ⟨_, rfl⟩
  have htU : t ∈ U := by rw [htdef]; exact U.mul_mem ht₀U hsU
  have hxt : x * t * x⁻¹ = t := by
    calc x * t * x⁻¹ = (x * t₀ * x⁻¹) * (x * s * x⁻¹) := by rw [htdef]; group
      _ = s * t₀ := by rw [← hsdef, hxs]
      _ = t := by rw [htdef]; exact hcomm s hsE t₀ ht₀E
  have ht1 : t ≠ 1 := by
    intro h
    apply hst
    calc s = t₀⁻¹ * t := by rw [htdef]; group
      _ = t₀ := by rw [h, mul_one, hinvE t₀ ht₀E]
  have hfix : ∀ u ∈ U, x * u * x⁻¹ = u → u = 1 ∨ u = t := by
    intro u hu hxu
    by_contra h
    push Not at h
    obtain ⟨hu1, hut⟩ := h
    have hut₀ : u ≠ t₀ := by
      intro h
      rw [h] at hxu
      exact hxt₀ hxu
    have hus : u ≠ s := by
      intro h
      rw [h, hxs] at hxu
      exact hst hxu.symm
    exact hut (htdef ▸ eq_mul_of_four hU4 hU2 ht₀U hsU hu ht₀1 hs1 hst.symm hu1 hut₀ hus)
  have hx2U : x * x ∈ U := hmemU _ hx2 (by rw [SemidirectProduct.mul_right]; exact hσ2 _)
  obtain ⟨y, hyT, hyE, hy2, hyN⟩ : ∃ y ∈ T, y ∉ E ∧ y * y = 1 ∧
      ∀ e ∈ E, y * e * y⁻¹ = x * e * x⁻¹ := by
    rcases hfix _ hx2U (by group) with h | h
    · exact ⟨x, hxT, hxE, h, fun e _ => rfl⟩
    · refine ⟨x * t₀, T.mul_mem hxT (hET ht₀E), fun h' => hxE ?_, ?_, fun e he => ?_⟩
      · have := E.mul_mem h' (E.inv_mem ht₀E)
        rwa [mul_inv_cancel_right] at this
      · calc x * t₀ * (x * t₀) = (x * t₀ * x⁻¹) * (x * x) * t₀ := by group
          _ = s * (t₀ * s) * t₀ := by rw [← hsdef, h, htdef]
          _ = (s * t₀) * (s * t₀) := by group
          _ = 1 := hE2 _ (E.mul_mem hsE ht₀E)
      · calc x * t₀ * e * (x * t₀)⁻¹ = x * (t₀ * e) * t₀⁻¹ * x⁻¹ := by group
          _ = x * (e * t₀) * t₀⁻¹ * x⁻¹ := by rw [hcomm t₀ ht₀E e he]
          _ = x * e * x⁻¹ := by group
  have hyt : y * t * y⁻¹ = t := by rw [hyN t (hUE htU), hxt]
  have hyt₀ : y * t₀ * y⁻¹ = s := by rw [hyN t₀ ht₀E, hsdef]
  have hyfix : ∀ u ∈ U, y * u * y⁻¹ = u → u = 1 ∨ u = t := fun u hu h =>
    hfix u hu (by rw [← hyN u (hUE hu)]; exact h)
  obtain ⟨x₀, hx₀E, hx₀r⟩ := exists_right_ne_one_of_card_eight hodd E hE2 hE8.ge
  obtain ⟨y₀, hy₀E, hy₀r, hyy₀⟩ : ∃ y₀ ∈ E, y₀.right ≠ 1 ∧ y * y₀ * y⁻¹ = y₀ := by
    obtain ⟨w, hwdef⟩ : ∃ w, w = y * x₀ * y⁻¹ := ⟨_, rfl⟩
    have hwE : w ∈ E := by rw [hwdef, hyN x₀ hx₀E]; exact hxN x₀ hx₀E
    have huU : x₀⁻¹ * w ∈ U := hmemU _ (E.mul_mem (E.inv_mem hx₀E) hwE) (by
      rw [SemidirectProduct.mul_right, SemidirectProduct.inv_right, hwdef, right_conj,
        inv_mul_cancel])
    have hyw : y * w * y⁻¹ = x₀ := by
      rw [hwdef]
      calc y * (y * x₀ * y⁻¹) * y⁻¹ = (y * y) * x₀ * (y * y)⁻¹ := by group
        _ = x₀ := by rw [hy2]; group
    have hyu : y * (x₀⁻¹ * w) * y⁻¹ = x₀⁻¹ * w := by
      calc y * (x₀⁻¹ * w) * y⁻¹ = (y * x₀ * y⁻¹)⁻¹ * (y * w * y⁻¹) := by group
        _ = w⁻¹ * x₀ := by rw [← hwdef, hyw]
        _ = w * x₀ := by rw [hinvE w hwE]
        _ = x₀ * w := hcomm w hwE x₀ hx₀E
        _ = x₀⁻¹ * w := by rw [hinvE x₀ hx₀E]
    rcases hyfix _ huU hyu with h | h
    · refine ⟨x₀, hx₀E, hx₀r, ?_⟩
      rw [← hwdef]
      calc w = x₀ * (x₀⁻¹ * w) := by group
        _ = x₀ := by rw [h, mul_one]
    · refine ⟨x₀ * t₀, E.mul_mem hx₀E ht₀E, ?_, ?_⟩
      · rw [SemidirectProduct.mul_right, hUr t₀ ht₀U, mul_one]
        exact hx₀r
      · calc y * (x₀ * t₀) * y⁻¹ = (y * x₀ * y⁻¹) * (y * t₀ * y⁻¹) := by group
          _ = w * s := by rw [← hwdef, hyt₀]
          _ = x₀ * (x₀⁻¹ * w) * s := by group
          _ = x₀ * (t₀ * s) * s := by rw [h, htdef]
          _ = x₀ * t₀ * (s * s) := by group
          _ = x₀ * t₀ := by rw [hE2 s hsE, mul_one]
  have hyy₀' : y * y₀ = y₀ * y := by
    calc y * y₀ = y * y₀ * y⁻¹ * y := by group
      _ = y₀ * y := by rw [hyy₀]
  have hyt' : y * t = t * y := by
    calc y * t = y * t * y⁻¹ * y := by group
      _ = t * y := by rw [hyt]
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup (PGammaL2 F),
      C = E ⊓ centralizer ({y} : Set (PGammaL2 F)) := ⟨_, rfl⟩
  have hCE : C ≤ E := by rw [hCdef]; exact inf_le_left
  have hCy : ∀ c ∈ C, y * c = c * y := fun c hc => by
    rw [hCdef] at hc
    exact (mem_centralizer_singleton_iff.mp (mem_inf.mp hc).2).symm
  have hmemC : ∀ c ∈ E, y * c = c * y → c ∈ C := fun c hc h => by
    rw [hCdef]
    exact mem_inf.mpr ⟨hc, mem_centralizer_singleton_iff.mpr h.symm⟩
  have htC : t ∈ C := hmemC t (hUE htU) hyt'
  have hy₀C : y₀ ∈ C := hmemC y₀ hy₀E hyy₀'
  have hyya : ∀ a, y * a ∈ C → y * a * y = a := fun a ha => by
    calc y * a * y = y * (y * a) := (hCy _ ha).symm
      _ = (y * y) * a := by group
      _ = a := by rw [hy2, one_mul]
  let E' : Subgroup (PGammaL2 F) :=
    { carrier := {g | g ∈ C ∨ y * g ∈ C}
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (C.mul_mem ha hb)
        · refine Or.inr ?_
          have h : y * (a * b) = a * (y * b) := by rw [← mul_assoc, hCy a ha, mul_assoc]
          rw [h]
          exact C.mul_mem ha hb
        · refine Or.inr ?_
          rw [← mul_assoc]
          exact C.mul_mem ha hb
        · refine Or.inl ?_
          have h : (y * a) * (y * b) = a * b := by rw [← mul_assoc, hyya a ha]
          rw [← h]
          exact C.mul_mem ha hb
      one_mem' := Or.inl C.one_mem
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (C.inv_mem ha)
        · refine Or.inr ?_
          have h : y * a⁻¹ = (y * a)⁻¹ := by
            calc y * a⁻¹ = y * (y * a * y)⁻¹ := by rw [hyya a ha]
              _ = (y * a)⁻¹ := by group
          rw [h]
          exact C.inv_mem ha }
  have hCE' : C ≤ E' := fun c hc => Or.inl hc
  have hyE' : y ∈ E' := Or.inr (by rw [hy2]; exact C.one_mem)
  have hE'T : E' ≤ T := by
    rintro g (hg | hg)
    · exact hET (hCE hg)
    · have h : g = y⁻¹ * (y * g) := by group
      rw [h]
      exact T.mul_mem (T.inv_mem hyT) (hET (hCE hg))
  have hE'2 : ∀ g ∈ E', g * g = 1 := by
    rintro g (hg | hg)
    · exact hE2 g (hCE hg)
    · obtain ⟨c, hcdef⟩ : ∃ c, c = y * g := ⟨_, rfl⟩
      rw [← hcdef] at hg
      have hgc : g = y * c := by rw [hcdef, ← mul_assoc, hy2, one_mul]
      rw [hgc]
      calc y * c * (y * c) = y * (c * y) * c := by group
        _ = y * (y * c) * c := by rw [hCy c hg]
        _ = (y * y) * (c * c) := by group
        _ = 1 := by rw [hy2, hE2 c (hCE hg), one_mul]
  have ht2 : orderOf t = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hE2 t (hUE htU)) ht1
  have hy₀1 : y₀ ≠ 1 := fun h => hy₀r (by rw [h]; rfl)
  have hy₀2 : orderOf y₀ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hE2 y₀ hy₀E) hy₀1
  have hty₀ : t ≠ y₀ := fun h => hy₀r (by rw [← h]; exact hUr t htU)
  obtain ⟨V, hVle, -, hV4⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup.exists_elementary_four_of_commute
      ht2 hy₀2 (hcomm t (hUE htU) y₀ hy₀E) hty₀
  have hVC : V ≤ C := hVle.trans ((closure_le C).mpr (by
    rintro _ (rfl | rfl)
    · exact htC
    · exact hy₀C))
  have hE'8 : Nat.card E' = 8 := by
    have hle8 := pGammaL2_card_le_eight_of_sq hodd E' hE'2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_two_of_forall_sq E' hE'2)
    have hlt : 4 < Nat.card E' := by
      by_contra h
      push Not at h
      have heq := eq_of_le_of_card_ge (hVC.trans hCE') (by rw [hV4]; exact h)
      exact hyE (hCE (hVC (heq ▸ hyE')))
    rw [hk] at hle8 hlt ⊢
    have hk4 : k < 4 := by
      by_contra h
      push Not at h
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h
      norm_num at this
      omega
    interval_cases k
    · norm_num at hlt
    · norm_num at hlt
    · norm_num at hlt
    · norm_num
  have hmove : ∀ c ∈ C, t₀ * (y * c) ≠ (y * c) * t₀ := fun c hc h => by
    apply hst
    have h1 : (y * c) * t₀ * (y * c)⁻¹ = s := by
      calc (y * c) * t₀ * (y * c)⁻¹ = y * (c * t₀) * c⁻¹ * y⁻¹ := by group
        _ = y * (t₀ * c) * c⁻¹ * y⁻¹ := by rw [hcomm c (hCE hc) t₀ ht₀E]
        _ = y * t₀ * y⁻¹ := by group
        _ = s := hyt₀
    rw [← h1, ← h, mul_inv_cancel_right]
  obtain ⟨u, huE', hur, hut₀⟩ : ∃ u ∈ E', u.right = 1 ∧ t₀ * u ≠ u * t₀ := by
    by_cases hyr : y.right = 1
    · refine ⟨y, hyE', hyr, ?_⟩
      have := hmove 1 C.one_mem
      rwa [mul_one] at this
    · refine ⟨y * y₀, Or.inr ?_, ?_, hmove y₀ hy₀C⟩
      · rw [← mul_assoc, hy2, one_mul]
        exact hy₀C
      · obtain ⟨σ, -, hσ⟩ := (Nat.card_eq_two_iff' (1 : F ≃+* F)).mp hAut
        rw [SemidirectProduct.mul_right, hσ _ hyr, hσ _ hy₀r]
        exact hσ2 σ
  exact ⟨E', hE'T, hE'2, hE'8, t, hUE htU, hCE' htC, hUr t htU, ht1, t₀, ht₀E, hUr t₀ ht₀U,
    u, huE', hur, hut₀⟩

end CFSG.ComponentClassification.Foote47.Nine
