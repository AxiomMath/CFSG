module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76L26Alpha27
public import CFSG.LocalAnalysis.ComponentClassification.Asc76L26Four
public import CFSG.LocalAnalysis.ComponentClassification.Asc76L26Reduce
public import CFSG.LocalAnalysis.ComponentClassification.Asc76L26Bender

public section

namespace CFSG.ComponentClassification.Asc76.L26

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G] {S : Subgroup G} {𝒯 : Set (Subgroup G)}

omit [Finite G] in
theorem commute_of_memberSet27 (h : Hyp27 S 𝒯) {x y : G} (hx : x ∈ memberSet 𝒯)
    (hy : y ∈ memberSet 𝒯) : x * y = y * x := by
  obtain ⟨-, T₁, hT₁, hxT⟩ := hx
  obtain ⟨-, T₂, hT₂, hyT⟩ := hy
  by_cases hT : T₁ = T₂
  · subst hT
    have := (h.cyclic T₁ hT₁).1
    exact congrArg Subtype.val (mul_comm' (⟨x, hxT⟩ : T₁) ⟨y, hyT⟩)
  · exact commute_of_commutator_eq_bot (h.comm T₁ hT₁ T₂ hT₂ hT) hxT hyT

omit [Finite G] in
theorem isMulCommutative_closure27 (h : Hyp27 S 𝒯) :
    IsMulCommutative (closure (memberSet 𝒯)) :=
  isMulCommutative_closure fun _ hx _ hy _ => commute_of_memberSet27 h hx hy

omit [Finite G] in
theorem closure_le27 (h : Hyp27 S 𝒯) : closure (memberSet 𝒯) ≤ S :=
  (closure_le _).mpr (memberSet_subset h.toHypCore)

omit [Finite G] in
theorem le_closure27 {T : Subgroup G} (hT : T ∈ 𝒯) : T ≤ closure (memberSet 𝒯) := by
  intro x hx
  by_cases hx1 : x = 1
  · rw [hx1]; exact one_mem _
  · exact subset_closure (mem_memberSet hT hx hx1)

omit [Finite G] in
theorem closure_le_centralizer27 (h : Hyp27 S 𝒯) {x : G} (hx : x ∈ closure (memberSet 𝒯)) :
    closure (memberSet 𝒯) ≤ centralizer ({x} : Set G) := by
  have := isMulCommutative_closure27 h
  intro y hy
  rw [mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : closure (memberSet 𝒯)) ⟨x, hx⟩)

omit [Finite G] in
theorem rightConjugate_centralizer_singleton (x g : G) :
    rightConjugate (centralizer ({x} : Set G)) g = centralizer ({g⁻¹ * x * g} : Set G) := by
  ext y
  rw [mem_rightConjugate_iff, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro hy
    calc y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [hy]
      _ = g⁻¹ * x * g * y := by group
  · intro hy
    calc g * y * g⁻¹ * x = g * (y * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * y) * g⁻¹ := by rw [hy]
      _ = x * (g * y * g⁻¹) := by group

theorem card_le_pred_of_ne_top {Y : Subgroup G} (hY : Y ≠ ⊤) : Nat.card Y ≤ Nat.card G - 1 := by
  have h1 : Nat.card Y < Nat.card G := by
    by_contra hle
    exact hY (Subgroup.eq_top_of_le_card Y (by omega))
  omega

omit [Finite G] in
theorem rightConjugate_closure_le (hcl : fusionStronglyClosed (memberSet 𝒯) S) {g : G}
    (hg : rightConjugate (closure (memberSet 𝒯)) g ≤ S) :
    rightConjugate (closure (memberSet 𝒯)) g ≤ closure (memberSet 𝒯) := by
  have hmap : rightConjugate (closure (memberSet 𝒯)) g =
      closure ((MulAut.conj g⁻¹) '' memberSet 𝒯) := by
    rw [rightConjugate, MonoidHom.map_closure]
    rfl
  rw [hmap, closure_le]
  rintro _ ⟨γ, hγ, rfl⟩
  have hS : g⁻¹ * γ * g ∈ S := by
    have := hg (show (MulAut.conj g⁻¹) γ ∈ rightConjugate (closure (memberSet 𝒯)) g from
      hmap ▸ subset_closure ⟨γ, hγ, rfl⟩)
    simpa [MulAut.conj_apply] using this
  have := hcl γ hγ g hS
  simpa [MulAut.conj_apply] using subset_closure this

theorem exists_sylow_position27 (h : Hyp27 S 𝒯) {x : G} (hxA : x ∈ closure (memberSet 𝒯)) :
    ∃ h₀ ∈ fusionGen (memberSet 𝒯), h₀⁻¹ * x * h₀ ∈ closure (memberSet 𝒯) ∧
      IsSylowOf 2 (S ⊓ centralizer ({h₀⁻¹ * x * h₀} : Set G))
        (centralizer ({h₀⁻¹ * x * h₀} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, hV4, hVe, hVΓ⟩ := h.four
  set Γ := memberSet 𝒯 with hΓdef
  set A := closure Γ with hAdef
  have hΓS : Γ ⊆ S := memberSet_subset h.toHypCore
  have hA2 : IsPGroup 2 A := h.sylow.isPGroup.to_le (closure_le27 h)
  obtain ⟨v, hvV, hv1⟩ := (Subgroup.bot_or_exists_ne_one V).resolve_left (fun h' => by
    rw [h', Subgroup.card_bot] at hV4; omega)
  have hvΓ : v ∈ Γ := hVΓ v hvV hv1
  have hvA : v ∈ A := subset_closure hvΓ
  obtain ⟨Q, hQ, hAQ⟩ := AschbacherTheorem3.exists_isSylowOf_le hA2
    (closure_le_centralizer27 h hxA)
  have hSH : S ≤ fusionGen Γ := le_fusionGen h.closed hΓS ⟨v, hvΓ⟩
  have hQH : Q ≤ fusionGen Γ := by
    obtain ⟨c, -, hc⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf h.sylow
      hQ.isPGroup le_top
    have hle := rightConjugate_mono (hc.trans hSH) c⁻¹
    rw [rightConjugate_inv] at hle
    have hvc : v ∈ rightConjugate (fusionGen Γ) c⁻¹ := hle (hAQ hvA)
    rw [mem_rightConjugate_fusionGen_iff h.sylow h.closed hΓS hvΓ] at hvc
    intro q hq
    have hq' := hle hq
    rw [mem_rightConjugate_iff] at hq'
    have hq'' := (fusionGen Γ).mul_mem ((fusionGen Γ).mul_mem ((fusionGen Γ).inv_mem hvc) hq')
      hvc
    simpa [mul_assoc] using hq''
  obtain ⟨h₀, hh₀, hQS⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf
    (h.sylow.of_le hSH le_top) hQ.isPGroup hQH
  have hAA : rightConjugate A h₀ ≤ A :=
    rightConjugate_closure_le h.closed ((rightConjugate_mono hAQ h₀).trans hQS)
  have hx'A : h₀⁻¹ * x * h₀ ∈ A :=
    hAA (by rw [mem_rightConjugate_iff]; simpa [mul_assoc] using hxA)
  refine ⟨h₀, hh₀, hx'A, ?_⟩
  have hYeq := rightConjugate_centralizer_singleton x h₀
  have hQ'Y : rightConjugate Q h₀ ≤ centralizer ({h₀⁻¹ * x * h₀} : Set G) := by
    rw [← hYeq]
    exact rightConjugate_mono hQ.le h₀
  have hQ'syl : IsSylowOf 2 (rightConjugate Q h₀) (centralizer ({h₀⁻¹ * x * h₀} : Set G)) := by
    rw [← hYeq]
    apply isSylowOf_of_card (rightConjugate_mono hQ.le h₀)
    rw [rightConjugate_card, hQ.card_eq, rightConjugate_card]
  have := hQ'syl.eq_of_le (le_inf hQS hQ'Y) inf_le_right (h.sylow.isPGroup.to_le inf_le_left)
  rw [this]
  exact hQ'syl

theorem centralizer_le27 (IH : Statement27 (Nat.card G - 1)) (h : Hyp27 S 𝒯) {x : G}
    (hxA : x ∈ closure (memberSet 𝒯)) (hxZ : x ∉ center G) :
    centralizer ({x} : Set G) ≤ fusionGen (memberSet 𝒯) := by
  obtain ⟨V, hV4, hVe, hVΓ⟩ := h.four
  have hVA : V ≤ closure (memberSet 𝒯) := fun v hv => by
    by_cases hv1 : v = 1
    · rw [hv1]; exact one_mem _
    · exact subset_closure (hVΓ v hv hv1)
  obtain ⟨h₀, hh₀, hx'A, hsyl⟩ := exists_sylow_position27 h hxA
  set x' := h₀⁻¹ * x * h₀ with hx'def
  set Y := centralizer ({x'} : Set G) with hYdef
  have hAY : closure (memberSet 𝒯) ≤ Y := closure_le_centralizer27 h hx'A
  have hle : ∀ T ∈ 𝒯, T ≤ S ⊓ Y := fun T hT =>
    le_inf (h.le T hT) ((le_closure27 hT).trans hAY)
  have hcl : ∀ γ ∈ memberSet 𝒯, ∀ y ∈ Y, y⁻¹ * γ * y ∈ S ⊓ Y → y⁻¹ * γ * y ∈ memberSet 𝒯 :=
    fun γ hγ y _ hy => h.closed γ hγ y (mem_inf.mp hy).1
  have hYne : Y ≠ ⊤ := by
    intro htop
    apply hxZ
    have hx'Z : x' ∈ center G := by
      rw [mem_center_iff]
      intro g
      have hg : g ∈ Y := by rw [htop]; exact mem_top g
      exact mem_centralizer_singleton_iff.mp hg
    have : x = h₀ * x' * h₀⁻¹ := by rw [hx'def]; group
    rw [this]
    exact (inferInstance : (center G).Normal).conj_mem x' hx'Z h₀
  have hYle := le_fusionGen_of_sub27 IH (card_le_pred_of_ne_top hYne) inf_le_right hsyl hle hcl
    h.comm h.cyclic (hVA.trans hAY) hV4 hVe hVΓ
  intro c hc
  have hcY : h₀⁻¹ * c * h₀ ∈ Y := by
    have hY' : Y = rightConjugate (centralizer ({x} : Set G)) h₀ :=
      (rightConjugate_centralizer_singleton x h₀).symm
    rw [hY', mem_rightConjugate_iff]
    simpa [mul_assoc] using hc
  have hc' : c = h₀ * (h₀⁻¹ * c * h₀) * h₀⁻¹ := by group
  rw [hc']
  exact (fusionGen _).mul_mem ((fusionGen _).mul_mem hh₀ (hYle hcY)) ((fusionGen _).inv_mem hh₀)

theorem conj_mem27 (h : Hyp27 S 𝒯) {T : Subgroup G} (hT : T ∈ 𝒯) {g : G}
    (hg : rightConjugate T g ≤ S) : rightConjugate T g ∈ 𝒯 := by
  obtain ⟨hTc, hT4⟩ := h.cyclic T hT
  obtain ⟨t, htT, ht4, htgen⟩ := exists_gen_of_cyclic_four hTc hT4
  have ht1 : t ≠ 1 := fun h' => by rw [h', orderOf_one] at ht4; omega
  have htg : g⁻¹ * t * g ∈ rightConjugate T g := by
    rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using htT
  obtain ⟨-, T', hT', htT'⟩ := h.closed t (mem_memberSet hT htT ht1) g (hg htg)
  obtain ⟨hT'c, hT'4⟩ := h.cyclic T' hT'
  have hord : orderOf (g⁻¹ * t * g) = 4 := by
    rw [show g⁻¹ * t * g = MulAut.conj g⁻¹ t by simp, MulEquiv.orderOf_eq]
    exact ht4
  have h1 : zpowers (g⁻¹ * t * g) = rightConjugate T g := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr htg) ?_
    rw [Nat.card_zpowers, hord, rightConjugate_card, hT4]
  have h2 : zpowers (g⁻¹ * t * g) = T' := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr htT') ?_
    rw [Nat.card_zpowers, hord, hT'4]
  rw [← h1, h2]
  exact hT'

theorem oddCore_eq_bot27 (IH : Statement27 (Nat.card G - 1)) (h : Hyp27 S 𝒯)
    (hH : fusionGen (memberSet 𝒯) ≠ ⊤) : CFSG.Assembly.oddCore G = ⊥ := by
  by_contra hO
  obtain ⟨V, hV4, hVe, hVΓ⟩ := h.four
  apply hH
  refine fusionGen_eq_top_of_quot27 IH h (N := CFSG.Assembly.oddCore G) (fun T hT => ?_)
    (oddCore_le_fusionGen hV4 hVe hVΓ) ?_
  · rw [inf_comm]
    exact inf_eq_bot_of_odd_of_isPGroup (odd_card_oddCore G)
      (h.sylow.isPGroup.to_le (h.le T hT))
  · have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Assembly.oddCore G)
    have h2 : 1 < Nat.card (CFSG.Assembly.oddCore G) := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      exact hO
    have h3 : 0 < Nat.card (G ⧸ CFSG.Assembly.oddCore G) := Nat.card_pos
    have h4 : Nat.card (G ⧸ CFSG.Assembly.oddCore G) < Nat.card G := by
      rw [h1]
      exact lt_mul_of_one_lt_right h3 h2
    omega

theorem not_central_involution27 (IH : Statement27 (Nat.card G - 1)) (h : Hyp27 S 𝒯)
    (hH : fusionGen (memberSet 𝒯) ≠ ⊤) : ∀ c ∈ center G, orderOf c ≠ 2 := by
  intro u hu hu2
  obtain ⟨V, hV4, hVe, hVΓ⟩ := h.four
  have hΓS : memberSet 𝒯 ⊆ S := memberSet_subset h.toHypCore
  have huΓ : u ∉ memberSet 𝒯 := fun huΓ =>
    hH (fusionGen_eq_top_of_mem_center h.sylow h.closed hΓS huΓ hu)
  have hNn : (zpowers u).Normal := normal_of_le_center (zpowers_le.mpr hu)
  obtain ⟨v, hvV, hv1⟩ := (Subgroup.bot_or_exists_ne_one V).resolve_left (fun h' => by
    rw [h', Subgroup.card_bot] at hV4; omega)
  have hvΓ := hVΓ v hvV hv1
  apply hH
  refine fusionGen_eq_top_of_quot27 IH h (N := zpowers u) (fun T hT => ?_) ?_ ?_
  · rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyT, hyu⟩ := mem_inf.mp hy
    rw [mem_bot]
    by_contra hy1
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hyu
    have hu' : u ∈ T := by
      obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
      · exfalso
        apply hy1
        rw [hk, zpow_mul, zpow_two, show u * u = 1 by rw [← sq, ← hu2]; exact pow_orderOf_eq_one u,
          one_zpow]
      · have : u ^ n = u := by
          rw [hk, zpow_add, zpow_mul, zpow_two,
            show u * u = 1 by rw [← sq, ← hu2]; exact pow_orderOf_eq_one u, one_zpow, one_mul,
            zpow_one]
        rw [this] at hyT
        exact hyT
    exact huΓ (mem_memberSet hT hu' (by rintro rfl; rw [orderOf_one] at hu2; omega))
  · rw [zpowers_le]
    exact centralizer_le_fusionGen hvΓ (mem_centralizer_singleton_iff.mpr
      (mem_center_iff.mp hu v).symm)
  · have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (zpowers u)
    rw [Nat.card_zpowers, hu2] at h1
    have h3 : 0 < Nat.card (G ⧸ zpowers u) := Nat.card_pos
    omega

omit [Finite G] in
theorem isPGroup_zpowers_of_mul_self {y : G} (hy : y * y = 1) : IsPGroup 2 (zpowers y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h1 : y = 1
  · rw [h1, zpowers_one_eq_bot]
    exact IsPGroup.of_bot
  · apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [sq]; exact hy) h1

theorem false_of_beta27 (IH : Statement27 (Nat.card G - 1)) (h : Hyp27 S 𝒯)
    (hZ : ∀ c ∈ center G, orderOf c ≠ 2) {x : G} (hxA : x ∈ closure (memberSet 𝒯))
    (hx1 : x ≠ 1) (hx2 : x * x = 1) {k : G} (hk : k ∉ fusionGen (memberSet 𝒯))
    (hxk : k * x * k⁻¹ ∈ fusionGen (memberSet 𝒯)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Γ := memberSet 𝒯 with hΓdef
  set A := closure Γ with hAdef
  set H := fusionGen Γ with hHdef
  have hΓS : Γ ⊆ S := memberSet_subset h.toHypCore
  have hAS : A ≤ S := closure_le27 h
  have hAc := isMulCommutative_closure27 h
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨b, hb⟩)
  obtain ⟨V, hV4, hVe, hVΓ⟩ := h.four
  have hVA : V ≤ A := fun v hv => by
    by_cases hv1 : v = 1
    · rw [hv1]; exact one_mem _
    · exact subset_closure (hVΓ v hv hv1)
  obtain ⟨v₀, hv₀V, hv₀1⟩ := (Subgroup.bot_or_exists_ne_one V).resolve_left (fun h' => by
    rw [h', Subgroup.card_bot] at hV4; omega)
  have hv₀Γ : v₀ ∈ Γ := hVΓ v₀ hv₀V hv₀1
  have hSH : S ≤ H := le_fusionGen h.closed hΓS ⟨v₀, hv₀Γ⟩
  have hΓH : ∀ y ∈ Γ, ∀ g, y ∈ rightConjugate H g ↔ g ∈ H := fun y hy g =>
    mem_rightConjugate_fusionGen_iff h.sylow h.closed hΓS hy g
  have hcentA : ∀ y ∈ A, y ≠ 1 → y * y = 1 → centralizer ({y} : Set G) ≤ H :=
    fun y hyA hy1 hy2 => centralizer_le27 IH h hyA
      (fun hyZ => hZ y hyZ (orderOf_eq_prime (by rw [sq]; exact hy2) hy1))
  obtain ⟨h₀, hh₀, hx₁A, hsyl₁⟩ := exists_sylow_position27 h hxA
  set x₁ := h₀⁻¹ * x * h₀ with hx₁def
  have hx₁1 : x₁ ≠ 1 := fun h' => hx1 (by
    have : x = h₀ * x₁ * h₀⁻¹ := by rw [hx₁def]; group
    rw [this, h']; group)
  have hx₁2 : x₁ * x₁ = 1 := by
    calc x₁ * x₁ = h₀⁻¹ * (x * x) * h₀ := by rw [hx₁def]; group
      _ = 1 := by rw [hx2]; group
  have hCx₁ := hcentA x₁ hx₁A hx₁1 hx₁2
  have hk₁ : k * h₀ ∉ H := fun h' => hk (by
    have := H.mul_mem h' (H.inv_mem hh₀)
    rwa [mul_inv_cancel_right] at this)
  have hk₁x : (k * h₀) * x₁ * (k * h₀)⁻¹ ∈ H := by
    have : (k * h₀) * x₁ * (k * h₀)⁻¹ = k * x * k⁻¹ := by rw [hx₁def]; group
    rw [this]
    exact hxk
  have hd₀2 : ((k * h₀) * x₁ * (k * h₀)⁻¹) * ((k * h₀) * x₁ * (k * h₀)⁻¹) = 1 := by
    calc ((k * h₀) * x₁ * (k * h₀)⁻¹) * ((k * h₀) * x₁ * (k * h₀)⁻¹) =
        (k * h₀) * (x₁ * x₁) * (k * h₀)⁻¹ := by group
      _ = 1 := by rw [hx₁2]; group
  obtain ⟨h₁, hh₁, hdS'⟩ := exists_conj_mem_of_le h.sylow hSH hk₁x
    (isPGroup_zpowers_of_mul_self hd₀2)
  set g₀ := (k * h₀)⁻¹ * h₁ with hg₀def
  have hg₀ : g₀ ∉ H := fun h' => hk₁ (by
    have := H.mul_mem hh₁ (H.inv_mem h')
    rw [hg₀def] at this
    simpa using this)
  set d := g₀⁻¹ * x₁ * g₀ with hddef
  have hdS : d ∈ S := by
    have : d = h₁⁻¹ * ((k * h₀) * x₁ * (k * h₀)⁻¹) * h₁ := by rw [hddef, hg₀def]; group
    rw [this]
    exact hdS'
  have hCd : centralizer ({d} : Set G) = rightConjugate (centralizer ({x₁} : Set G)) g₀ :=
    (rightConjugate_centralizer_singleton x₁ g₀).symm
  have hP₀ : IsSylowOf 2 (rightConjugate (S ⊓ centralizer ({x₁} : Set G)) g₀)
      (centralizer ({d} : Set G)) := by
    rw [hCd]
    apply isSylowOf_of_card (rightConjugate_mono hsyl₁.le g₀)
    rw [rightConjugate_card, hsyl₁.card_eq, rightConjugate_card]
  obtain ⟨c, hc, hcle⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hP₀
    (h.sylow.isPGroup.to_le inf_le_left) (inf_le_right : S ⊓ centralizer ({d} : Set G) ≤ _)
  set g := g₀ * c⁻¹ with hgdef
  have hcd : c * d = d * c := mem_centralizer_singleton_iff.mp hc
  have hdg : g⁻¹ * x₁ * g = d := by
    calc g⁻¹ * x₁ * g = c * d * c⁻¹ := by rw [hgdef, hddef]; group
      _ = d := by rw [hcd]; group
  have hCS : S ⊓ centralizer ({d} : Set G) ≤ rightConjugate S g := by
    have := rightConjugate_mono hcle c⁻¹
    rw [rightConjugate_inv, rightConjugate_mul] at this
    exact this.trans (rightConjugate_mono inf_le_left g)
  have hCdH : centralizer ({d} : Set G) ≤ rightConjugate H g := by
    rw [← hdg, ← rightConjugate_centralizer_singleton]
    exact rightConjugate_mono hCx₁ g
  have hg : g ∉ H := by
    intro hgH
    apply hg₀
    have hcH : c ∈ rightConjugate H g := hCdH hc
    rw [mem_rightConjugate_iff] at hcH
    have h2 : g₀ = (g * c * g⁻¹) * g := by rw [hgdef]; group
    rw [h2]
    exact H.mul_mem hcH hgH
  have hCΓ : ∀ y ∈ Γ, y * d ≠ d * y := fun y hy hyd =>
    hg ((hΓH y hy g).mp (hCdH (mem_centralizer_singleton_iff.mpr hyd)))
  have hd2 : d * d = 1 := by
    calc d * d = g₀⁻¹ * (x₁ * x₁) * g₀ := by rw [hddef]; group
      _ = 1 := by rw [hx₁2]; group
  have hVd : ∀ v ∈ V, d⁻¹ * v * d ∈ A := by
    intro v hv
    by_cases hv1 : v = 1
    · rw [hv1, mul_one, inv_mul_cancel]; exact one_mem _
    · exact subset_closure (h.closed v (hVΓ v hv hv1) d
        (S.mul_mem (S.mul_mem (S.inv_mem hdS) (hAS (hVA hv))) hdS))
  let φ : V →* G := MonoidHom.mk' (fun v => (v : G) * (d⁻¹ * v * d)) (by
    intro a b
    simp only [Subgroup.coe_mul]
    have hab := hAcomm _ (hVA b.2) _ (hVd a a.2)
    calc (a : G) * b * (d⁻¹ * (a * b) * d) = a * (b * (d⁻¹ * a * d)) * (d⁻¹ * b * d) := by
          group
      _ = a * ((d⁻¹ * a * d) * b) * (d⁻¹ * b * d) := by rw [hab]
      _ = a * (d⁻¹ * a * d) * (b * (d⁻¹ * b * d)) := by group)
  have hφ : ∀ v : V, φ v = (v : G) * (d⁻¹ * v * d) := fun _ => rfl
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro v hv
    rw [MonoidHom.mem_ker, hφ] at hv
    rw [mem_bot]
    by_contra hv1
    have hv1' : (v : G) ≠ 1 := fun h' => hv1 (Subtype.ext h')
    have hvv : (v : G) * v = 1 := by rw [← sq]; exact hVe.2 v v.2
    have hvd : d⁻¹ * v * d = v := by
      rw [eq_inv_of_mul_eq_one_right hv, inv_eq_of_mul_eq_one_right hvv]
    apply hCΓ v (hVΓ v v.2 hv1')
    calc (v : G) * d = d * (d⁻¹ * v * d) := by group
      _ = d * v := by rw [hvd]
  set W := φ.range with hWdef
  have hW4 : Nat.card W = 4 := by
    rw [← hV4]
    exact (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm
  have hWA : W ≤ A := by
    rintro _ ⟨v, rfl⟩
    rw [hφ]
    exact A.mul_mem (hVA v.2) (hVd v v.2)
  have hW2 : ∀ w ∈ W, w * w = 1 := by
    rintro _ ⟨v, rfl⟩
    rw [hφ]
    have hvv : (v : G) * v = 1 := by rw [← sq]; exact hVe.2 v v.2
    have hc' := hAcomm _ (hVA v.2) _ (hVd v v.2)
    calc (v : G) * (d⁻¹ * v * d) * (v * (d⁻¹ * v * d)) =
        v * ((d⁻¹ * v * d) * v) * (d⁻¹ * v * d) := by group
      _ = v * (v * (d⁻¹ * v * d)) * (d⁻¹ * v * d) := by rw [← hc']
      _ = (v * v) * (d⁻¹ * (v * v) * d) := by group
      _ = 1 := by rw [hvv]; group
  have hWe : IsElemAbelian 2 W :=
    ⟨⟨⟨fun a b => Subtype.ext (hAcomm _ (hWA a.2) _ (hWA b.2))⟩⟩,
      fun w hw => by rw [sq]; exact hW2 w hw⟩
  have hWd : W ≤ centralizer ({d} : Set G) := by
    rintro _ ⟨v, rfl⟩
    rw [hφ, mem_centralizer_singleton_iff]
    have hc' := hAcomm _ (hVA v.2) _ (hVd v v.2)
    rw [hdinv] at hc' ⊢
    calc (v : G) * (d * v * d) * d = v * d * v * (d * d) := by group
      _ = (d * d) * (v * d * v) := by rw [hd2, one_mul, mul_one]
      _ = d * ((d * v * d) * v) := by group
      _ = d * (v * (d * v * d)) := by rw [← hc']
  have hWS : W ≤ rightConjugate S g := (le_inf (hWA.trans hAS) hWd).trans hCS
  have hWC : ∀ w ∈ W, w ≠ 1 → centralizer ({w} : Set G) ≤ H := fun w hw hw1 =>
    hcentA w (hWA hw) hw1 (hW2 w hw)
  obtain ⟨-, T₁, hT₁, hv₀T₁⟩ := hv₀Γ
  obtain ⟨hT₁c, hT₁4⟩ := h.cyclic T₁ hT₁
  obtain ⟨t₁, ht₁T, ht₁4, -⟩ := exists_gen_of_cyclic_four hT₁c hT₁4
  have hQ2 : IsPGroup 2 (rightConjugate T₁ g) :=
    (h.sylow.isPGroup.to_le (h.le T₁ hT₁)).map _
  have hrQ : g⁻¹ * t₁ * g ∈ rightConjugate T₁ g := by
    rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using ht₁T
  have hr2 : (g⁻¹ * t₁ * g) ^ 2 ≠ 1 := by
    have hord : orderOf (g⁻¹ * t₁ * g) = 4 := by
      rw [show g⁻¹ * t₁ * g = MulAut.conj g⁻¹ t₁ by simp, MulEquiv.orderOf_eq]
      exact ht₁4
    exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hord]; norm_num)
  have hcommQ : ∀ w ∈ W, w ∉ normalizer ((rightConjugate T₁ g : Subgroup G) : Set G) →
      ∀ a ∈ rightConjugate T₁ g, ∀ b ∈ rightConjugate (rightConjugate T₁ g) w,
        a * b = b * a := by
    intro w hw hwN a ha b hb
    have hw' : g * w * g⁻¹ ∈ S := by
      have := hWS hw
      rwa [mem_rightConjugate_iff] at this
    have hQw : rightConjugate (rightConjugate T₁ g) w =
        rightConjugate (rightConjugate T₁ (g * w * g⁻¹)) g := by
      rw [rightConjugate_mul, rightConjugate_mul]
      congr 1
      group
    have hT₁S : rightConjugate T₁ (g * w * g⁻¹) ≤ S := by
      intro y hy
      rw [mem_rightConjugate_iff] at hy
      have := S.mul_mem (S.mul_mem (S.inv_mem hw') (h.le T₁ hT₁ hy)) hw'
      simpa [mul_assoc] using this
    have hT₁' : rightConjugate T₁ (g * w * g⁻¹) ∈ 𝒯 := conj_mem27 h hT₁ hT₁S
    have hne : rightConjugate T₁ (g * w * g⁻¹) ≠ T₁ := by
      intro heq
      apply hwN
      rw [← rightConjugate_eq_self_iff, hQw, heq]
    have hcomm1 := h.comm _ hT₁' T₁ hT₁ hne
    rw [hQw, mem_rightConjugate_iff] at hb
    rw [mem_rightConjugate_iff] at ha
    have hc1 := commute_of_commutator_eq_bot hcomm1 hb ha
    have h2 : g * (b * a) * g⁻¹ = g * (a * b) * g⁻¹ := by
      calc g * (b * a) * g⁻¹ = (g * b * g⁻¹) * (g * a * g⁻¹) := by group
        _ = (g * a * g⁻¹) * (g * b * g⁻¹) := hc1
        _ = g * (a * b) * g⁻¹ := by group
    exact (mul_left_cancel (mul_right_cancel h2)).symm
  obtain ⟨z, hzQ, hz1, hzH⟩ :=
    exists_ne_one_mem_of_centralizers_le hQ2 hrQ hr2 hW4 hWe hcommQ hWC
  rw [mem_rightConjugate_iff] at hzQ
  have hy1 : g * z * g⁻¹ ≠ 1 := fun h' => hz1 (by
    have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
    rw [this, h']; group)
  have hyΓ : g * z * g⁻¹ ∈ Γ := mem_memberSet hT₁ hzQ hy1
  apply hg
  have h3 := (hΓH _ hyΓ g⁻¹).mp (by rw [mem_rightConjugate_iff]; simpa [mul_assoc] using hzH)
  exact (H.inv_mem_iff).mp h3

omit [Finite G] in
theorem fusionIsBenderGroup_congr {X X' : Type*} [Group X] [Group X'] (e : X ≃* X')
    (h : fusionIsBenderGroup X) : fusionIsBenderGroup X' := by
  rcases h with ⟨f, hf, ⟨e'⟩⟩ | ⟨f, hf, ⟨e'⟩⟩ | ⟨a, ha, ⟨e'⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩)
  · exact Or.inr (Or.inr ⟨a, ha, ⟨e.symm.trans e'⟩⟩)

theorem false_of_bender27' (h : Hyp27 S 𝒯) {K : Subgroup G} [K.Normal]
    (hK : fusionIsBenderGroup K) {a : G} (haΓ : a ∈ memberSet 𝒯) (haK : a ∈ K)
    (ha2 : orderOf a = 2) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := K ⊔ S with hYdef
  have hKY : K ≤ Y := le_sup_left
  have hSY : S ≤ Y := le_sup_right
  have hKYn : (K.subgroupOf Y).Normal := Subgroup.Normal.subgroupOf inferInstance Y
  have hKYB : fusionIsBenderGroup (K.subgroupOf Y) :=
    fusionIsBenderGroup_congr (subgroupOfEquivOfLe hKY).symm hK
  obtain ⟨P, hP⟩ := (h.sylow.of_le hSY le_top).exists_sylow_eq_subgroupOf
  have hKP : K.subgroupOf Y ⊔ (P : Subgroup Y) = ⊤ := by
    rw [hP, ← subgroupOf_sup hKY hSY, subgroupOf_self]
  have hle : ∀ T ∈ subFamily Y 𝒯, T ≤ (P : Subgroup Y) := by
    rintro _ ⟨T, hT, rfl⟩
    rw [hP]
    exact fun x hx => mem_subgroupOf.mpr (h.le T hT (mem_subgroupOf.mp hx))
  have hcyc : ∀ T ∈ subFamily Y 𝒯, IsCyclic T ∧ Nat.card T = 4 := by
    rintro _ ⟨T, hT, rfl⟩
    have hTY : T ≤ Y := (h.le T hT).trans hSY
    obtain ⟨hTc, hT4⟩ := h.cyclic T hT
    have e := subgroupOfEquivOfLe hTY
    exact ⟨isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective,
      (Nat.card_congr e.toEquiv).trans hT4⟩
  have hcomm : ∀ T₁ ∈ subFamily Y 𝒯, ∀ T₂ ∈ subFamily Y 𝒯, T₁ ≠ T₂ → ⁅T₁, T₂⁆ = ⊥ := by
    rintro _ ⟨T₁, hT₁, rfl⟩ _ ⟨T₂, hT₂, rfl⟩ hne
    exact commutator_subgroupOf_eq_bot (h.comm T₁ hT₁ T₂ hT₂ fun h' => hne (by rw [h']))
  have hcl : fusionStronglyClosed (memberSet (subFamily Y 𝒯)) (P : Subgroup Y) := by
    intro x hx y hy
    rw [mem_memberSet_subFamily] at hx ⊢
    rw [hP, mem_subgroupOf] at hy
    simpa using h.closed _ hx y (by simpa using hy)
  have haY : (⟨a, hKY haK⟩ : Y) ∈ memberSet (subFamily Y 𝒯) := by
    rw [mem_memberSet_subFamily]
    exact haΓ
  exact false_of_bender27 hKYB P hKP hle hcyc hcomm hcl haY haK
    (by rw [Subgroup.orderOf_mk]; exact ha2)

theorem fusionGen_eq_top27 (IH : Statement27 (Nat.card G - 1)) (h : Hyp27 S 𝒯) :
    fusionGen (memberSet 𝒯) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hH
  have hO := oddCore_eq_bot27 IH h hH
  have hZ := not_central_involution27 IH h hH
  have hΓS : memberSet 𝒯 ⊆ S := memberSet_subset h.toHypCore
  obtain ⟨V, hV4, hVe, hVΓ⟩ := h.four
  obtain ⟨a, haV, ha1⟩ := (Subgroup.bot_or_exists_ne_one V).resolve_left (fun h' => by
    rw [h', Subgroup.card_bot] at hV4; omega)
  have haΓ := hVΓ a haV ha1
  have haa : a * a = 1 := by rw [← sq]; exact hVe.2 a haV
  have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact haa) ha1
  have huniq := mem_rightConjugate_fusionGen_iff h.sylow h.closed hΓS haΓ
  by_cases h1 : AschbacherStrongEmbedding.ProductUniqueContainment (fusionGen (memberSet 𝒯)) a
  · obtain ⟨hKn, hKB, -, -, haK⟩ := exists_normal_bender (G := G) hO hZ hH ha2 huniq h1
    exact false_of_bender27' h hKB haΓ haK ha2
  · simp only [AschbacherStrongEmbedding.ProductUniqueContainment, not_forall] at h1
    obtain ⟨t, ht, hat, hta, g, hg⟩ := h1
    set H := fusionGen (memberSet 𝒯) with hHdef
    have haH : a ∈ H := mem_fusionGen_of_mem haΓ
    have htH : t ∈ H :=
      centralizer_le_fusionGen haΓ (mem_centralizer_singleton_iff.mpr hat.eq.symm)
    have hatH : a * t ∈ H := H.mul_mem haH htH
    have hgH : g ∉ H := fun hgH =>
      hg ⟨fun _ => hgH, fun _ => H.mul_mem (H.mul_mem (H.inv_mem hgH) hatH) hgH⟩
    have hgat : g⁻¹ * (a * t) * g ∈ H := by
      by_contra hn
      exact hg ⟨fun h' => absurd h' hn, fun h' => absurd h' hgH⟩
    obtain ⟨k, hk⟩ := ht
    have htk : t = k⁻¹ * a * k := by rw [← hk]; rfl
    have htt : t * t = 1 := by
      rw [htk]
      calc k⁻¹ * a * k * (k⁻¹ * a * k) = k⁻¹ * (a * a) * k := by group
        _ = 1 := by rw [haa]; group
    have ht1 : t ≠ 1 := fun h' => ha1 (by
      rw [htk] at h'
      have : a = k * (k⁻¹ * a * k) * k⁻¹ := by group
      rw [this, h']; group)
    have hP₀ : IsPGroup 2 (AschbacherStrongEmbedding.commutingPairSubgroup a t haa htt hat) :=
      IsPGroup.of_card (AschbacherStrongEmbedding.commutingPairSubgroup_card ha1 ht1
        (Ne.symm hta))
    obtain ⟨c, -, hc⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf h.sylow hP₀
      le_top
    have hmemP : ∀ y ∈ AschbacherStrongEmbedding.commutingPairSubgroup a t haa htt hat,
        c⁻¹ * y * c ∈ S := fun y hy => hc (by
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using hy)
    have ha' : c⁻¹ * a * c ∈ memberSet 𝒯 :=
      h.closed a haΓ c (hmemP a (AschbacherStrongEmbedding.mem_commutingPairSubgroup.mpr
        (Or.inr (Or.inl rfl))))
    have ht' : c⁻¹ * t * c ∈ memberSet 𝒯 := by
      have hS := hmemP t (AschbacherStrongEmbedding.mem_commutingPairSubgroup.mpr
        (Or.inr (Or.inr (Or.inl rfl))))
      have e : c⁻¹ * t * c = (k * c)⁻¹ * a * (k * c) := by rw [htk]; group
      rw [e] at hS ⊢
      exact h.closed a haΓ (k * c) hS
    have hx'A : c⁻¹ * (a * t) * c ∈ closure (memberSet 𝒯) := by
      have e : c⁻¹ * (a * t) * c = (c⁻¹ * a * c) * (c⁻¹ * t * c) := by group
      rw [e]
      exact mul_mem (subset_closure ha') (subset_closure ht')
    have hat1 : a * t ≠ 1 := fun h' => hta (by
      rw [eq_inv_of_mul_eq_one_right h', inv_eq_of_mul_eq_one_right haa])
    have hx'1 : c⁻¹ * (a * t) * c ≠ 1 := fun h' => hat1 (by
      have : a * t = c * (c⁻¹ * (a * t) * c) * c⁻¹ := by group
      rw [this, h']; group)
    have hx'2 : c⁻¹ * (a * t) * c * (c⁻¹ * (a * t) * c) = 1 := by
      have hatat : a * t * (a * t) = 1 := by
        calc a * t * (a * t) = a * (t * a) * t := by group
          _ = a * (a * t) * t := by rw [hat.eq]
          _ = (a * a) * (t * t) := by group
          _ = 1 := by rw [haa, htt, one_mul]
      calc c⁻¹ * (a * t) * c * (c⁻¹ * (a * t) * c) = c⁻¹ * (a * t * (a * t)) * c := by group
        _ = 1 := by rw [hatat]; group
    by_cases hcH : c ∈ H
    · refine false_of_beta27 IH h hZ hx'A hx'1 hx'2 (k := g⁻¹ * c) (fun h' => hgH ?_) ?_
      · have := H.mul_mem h' (H.inv_mem hcH)
        rw [mul_inv_cancel_right] at this
        exact H.inv_mem_iff.mp this
      · have e : g⁻¹ * c * (c⁻¹ * (a * t) * c) * (g⁻¹ * c)⁻¹ = g⁻¹ * (a * t) * g := by group
        rw [e]
        exact hgat
    · refine false_of_beta27 IH h hZ hx'A hx'1 hx'2 (k := c) hcH ?_
      have e : c * (c⁻¹ * (a * t) * c) * c⁻¹ = a * t := by group
      rw [e]
      exact hatH

omit [Finite G] in
theorem statement27_all : ∀ n, Statement27 n := by
  intro n
  induction n with
  | zero =>
    intro X _ _ hX
    have := Nat.card_pos (α := X)
    omega
  | succ n ih =>
    intro X _ _ hX S' 𝒯' h
    by_cases hle : Nat.card X ≤ n
    · exact ih X hle S' 𝒯' h
    have IH : Statement27 (Nat.card X - 1) := fun Y _ _ hY => ih Y (by omega)
    exact fusionGen_eq_top27 IH h

theorem asc76Lemma27 : Asc76Lemma27 := asc76Lemma27_of statement27_all

end CFSG.ComponentClassification.Asc76.L26
