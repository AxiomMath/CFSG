module

public import CFSG.LocalAnalysis.ComponentClassification.Foote47P3Gen
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma414Bender

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_conj_le_centralizer_of_odd_isPGroup {O F W : Subgroup G} (hO : Odd (Nat.card O))
    (hFO : F ≤ normalizer (O : Set G)) (hFp : IsPGroup 2 F) (hWp : IsPGroup 2 W)
    (hWO : W ≤ normalizer (O : Set G)) (hWF : ∀ f ∈ F, ∀ w ∈ W, f⁻¹ * (w * f * w⁻¹) ∈ O) :
    ∃ k ∈ F ⊔ O, conjugate F k ≤ centralizer (W : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := F ⊔ O with hD
  have hOD : O ≤ D := le_sup_right
  have hDmul : ∀ d ∈ D, ∃ f ∈ F, ∃ o ∈ O, f * o = d := by
    intro d hd
    have h1 : d ∈ ((F : Set G) * O) := by
      rw [← coe_mul_of_left_le_normalizer_right F O hFO]
      exact hd
    obtain ⟨f, hf, o, ho, hfo⟩ := Set.mem_mul.mp h1
    exact ⟨f, hf, o, ho, hfo⟩
  set X := D ⊓ centralizer (W : Set G) with hX
  have hXD : X ≤ D := inf_le_left
  have hcover : ∀ d ∈ D, ∃ x ∈ X, ∃ o ∈ O, d = x * o := by
    intro d hd
    obtain ⟨f, hf, o₀, ho₀, rfl⟩ := hDmul d hd
    have hd' : ∀ w ∈ W, (f * o₀)⁻¹ * (w * (f * o₀) * w⁻¹) ∈ O := by
      intro w hw
      have h1 : f⁻¹ * (w * f * w⁻¹) ∈ O := hWF f hf w hw
      have h2 : w * o₀ * w⁻¹ ∈ O := (mem_normalizer_iff.mp (hWO hw) o₀).mp ho₀
      have h3 : (f * o₀)⁻¹ * (w * (f * o₀) * w⁻¹) =
          o₀⁻¹ * (f⁻¹ * (w * f * w⁻¹)) * (w * o₀ * w⁻¹) := by group
      rw [h3]
      exact mul_mem (mul_mem (inv_mem ho₀) h1) h2
    obtain ⟨o, ho, hdo⟩ := Foote47.exists_mem_centralizer_of_isPGroup hWp hWO hO hd'
    exact ⟨f * o₀ * o, mem_inf.mpr ⟨mul_mem hd (hOD ho), hdo⟩, o⁻¹, inv_mem ho, by group⟩
  have hDN : D ≤ normalizer (O : Set G) := sup_le hFO le_normalizer
  have : (O.subgroupOf D).Normal := (normal_subgroupOf_iff_le_normalizer hOD).mpr hDN
  have hodd : ¬ 2 ∣ X.relIndex D := by
    rw [relIndex_eq_relIndex_inf_of_mul hXD hOD hcover]
    intro h2
    exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr
      (h2.trans (Subgroup.relIndex_dvd_card _ _)))
  obtain ⟨Q, hQ⟩ := exists_isSylowOf 2 X
  have hQD : IsSylowOf 2 Q D := by
    have hQ' := isSylowOf_iff.mp hQ
    refine isSylowOf_iff.mpr ⟨hQ'.1.trans hXD, hQ'.2.1, fun h2 => ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex Q X D hQ'.1 hXD] at h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
    exacts [hQ'.2.2 h, hodd h]
  obtain ⟨k, hkD, hk⟩ := exists_conj_le_of_isSylowOf hQD le_sup_left hFp
  exact ⟨k, hkD, (conjugate_le_of_forall hk).trans (hQ.le.trans inf_le_right)⟩

theorem sup_eq_of_isSylowOf_of_sq_mem {V U O : Subgroup G} (hU : IsSylowOf 2 U V) (hOV : O ≤ V)
    (hVO : V ≤ normalizer (O : Set G)) (hsq : ∀ v ∈ V, v ^ 2 ∈ O) : U ⊔ O = V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUOV : U ⊔ O ≤ V := sup_le hU.le hOV
  have : (O.subgroupOf V).Normal := (normal_subgroupOf_iff_le_normalizer hOV).mpr hVO
  have hpow : IsPGroup 2 (↥V ⧸ O.subgroupOf V) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H v =>
      refine ⟨1, ?_⟩
      rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      show ((v ^ 2 : ↥V) : G) ∈ O
      rw [SubgroupClass.coe_pow]
      exact hsq v v.2
  obtain ⟨j, hj⟩ := hpow.exists_card_eq
  have hO2 : O.relIndex V = 2 ^ j := hj
  have h1 : (U ⊔ O).relIndex V ∣ 2 ^ j := hO2 ▸ relIndex_dvd_of_le_left V le_sup_right
  have h2 : ¬ 2 ∣ (U ⊔ O).relIndex V := fun h =>
    (isSylowOf_iff.mp hU).2.2 (h.trans (relIndex_dvd_of_le_left V le_sup_left))
  obtain ⟨i, -, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hi0 : i = 0 := by
    by_contra hne
    exact h2 (hi' ▸ dvd_pow_self 2 hne)
  rw [hi0, pow_zero] at hi'
  exact le_antisymm hUOV (relIndex_eq_one.mp hi')

theorem exists_card_eight_le_inf_centralizer_of_isKleinFour
    (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) {M : Subgroup G} (hM : IsFooteM L M) {W₀ : Subgroup G}
    (hW₀ : IsKleinFour W₀) (hW₀MC : W₀ ≤ M ⊔ coreActionKernel M) :
    ∃ F : Subgroup G, F ≤ coreActionKernel M ⊓ centralizer (W₀ : Set G) ∧
      (∀ x ∈ F, x ^ 2 = 1) ∧ Nat.card F = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := coreActionKernel M with hCdef
  set O := oddCoreIn M with hOdef
  have hOM : O ≤ M := map_subtype_le _
  have hOC : O ≤ C := GSThmB.oddCoreIn_le_coreActionKernel M
  have hCN : C ≤ normalizer (M : Set G) := fun c hc => (mem_coreActionKernel.mp hc).1
  have hMN : M ≤ normalizer (M : Set G) := le_normalizer
  have hNO : ∀ g ∈ normalizer (M : Set G), g ∈ normalizer (O : Set G) := fun g hg =>
    mem_normalizer_oddCoreIn hg
  have hW₀N : W₀ ≤ normalizer (M : Set G) := hW₀MC.trans (sup_le hMN hCN)
  have hW₀2 : ∀ w ∈ W₀, w ^ 2 = 1 := fun w hw => sq_eq_one_of_isKleinFour hW₀ hw
  have hW₀p : IsPGroup 2 W₀ := IsPGroup.of_card (n := 2) (by rw [hW₀.card_four]; norm_num)
  set V := (W₀ ⊔ M) ⊓ C with hVdef
  have hWM : ∀ x ∈ W₀ ⊔ M, ∃ w ∈ W₀, ∃ m ∈ M, x = w * m := by
    intro x hx
    have h1 : x ∈ ((W₀ : Set G) * M) := by
      rw [← coe_mul_of_left_le_normalizer_right W₀ M hW₀N]
      exact hx
    obtain ⟨w, hw, m, hm, rfl⟩ := Set.mem_mul.mp h1
    exact ⟨w, hw, m, hm, rfl⟩
  have hsqV : ∀ v ∈ V, v ^ 2 ∈ O := by
    intro v hv
    obtain ⟨w, hw, m, hm, rfl⟩ := hWM v (mem_inf.mp hv).1
    have hvM : (w * m) ^ 2 ∈ M := by
      have h1 : (w * m) ^ 2 = (w * m * w⁻¹) * (w * w) * m := by rw [sq]; group
      rw [h1, ← sq, hW₀2 w hw, mul_one]
      exact mul_mem ((mem_normalizer_iff.mp (hW₀N hw) m).mp hm) hm
    exact hM.inf_coreActionKernel_le h (mem_inf.mpr ⟨hvM, pow_mem (mem_inf.mp hv).2 2⟩)
  have hOV : O ≤ V := le_inf (hOM.trans le_sup_right) hOC
  have hVO : V ≤ normalizer (O : Set G) := fun v hv => hNO v (hCN (mem_inf.mp hv).2)
  obtain ⟨U, hU⟩ := exists_isSylowOf 2 V
  have hUO : U ⊔ O = V := sup_eq_of_isSylowOf_of_sq_mem hU hOV hVO hsqV
  have hUC : U ≤ C := hU.le.trans inf_le_right
  have hUp : IsPGroup 2 U := hU.isPGroup
  have hU2 : ∀ u ∈ U, u ^ 2 = 1 := by
    intro u hu
    have h1 := hsqV u (hU.le hu)
    exact eq_one_of_mem_of_odd hUp (odd_card_oddCoreIn M) (pow_mem hu 2) h1
  obtain ⟨F₀, hF₀C, hF₀U, hF₀2, hF₀8⟩ : ∃ F₀ : Subgroup G, F₀ ≤ C ∧
      (∀ f ∈ F₀, ∀ u ∈ U, f * u = u * f) ∧ (∀ x ∈ F₀, x ^ 2 = 1) ∧ Nat.card F₀ = 8 := by
    have hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb => commute_of_sq_eq_one hU2 ha hb
    obtain ⟨k, hk⟩ := hUp.exists_card_eq
    rcases k with _ | _ | _ | k
    ·
      obtain ⟨E, hE2, hE8, hEC⟩ := hM.exists_card_eight h
      refine ⟨E, hEC, fun f _ u hu => ?_, hE2, hE8⟩
      rw [pow_zero] at hk
      have hu1 : u = 1 := by
        have := (Subgroup.card_eq_one).mp hk
        rw [this] at hu
        exact (mem_bot).mp hu
      rw [hu1, one_mul, mul_one]
    ·
      rw [pow_one] at hk
      obtain ⟨⟨u₀, hu₀⟩, hu₀1, hall⟩ := (Nat.card_eq_two_iff' (1 : ↥U)).mp hk
      have hu₀1' : u₀ ≠ 1 := fun h1 => hu₀1 (Subtype.ext h1)
      have hu₀2 : orderOf u₀ = 2 := orderOf_eq_prime (hU2 u₀ hu₀) hu₀1'
      obtain ⟨F, hF, hF2, hF8⟩ := exists_card_eight_of_le_pRank
        (h47 G L h M hM u₀ hu₀2 (hUC hu₀))
      refine ⟨F, hF.trans inf_le_left, fun f hf u hu => ?_, hF2, hF8⟩
      by_cases hu1 : u = 1
      · rw [hu1, one_mul, mul_one]
      · have : (⟨u, hu⟩ : ↥U) = ⟨u₀, hu₀⟩ := hall ⟨u, hu⟩ (fun h1 => hu1 (congrArg Subtype.val h1))
        have hu' : u = u₀ := congrArg Subtype.val this
        rw [hu']
        exact mem_centralizer_singleton_iff.mp (hF hf).2
    ·
      have hUK : IsKleinFour U := isKleinFour_of_card_eq_four (by rw [hk]; norm_num) hU2
      obtain ⟨A, hA2, hA8, hUA, hAC⟩ := foote_cor_4_8_i h h47 hST hM hUK hUC
      exact ⟨A, hAC, fun f hf u hu => commute_of_sq_eq_one hA2 hf (hUA hu), hA2, hA8⟩
    ·
      have h8 : 8 ≤ Nat.card U := by
        rw [hk, pow_succ, pow_succ, pow_succ]
        have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        omega
      obtain ⟨F, hFU, hF2, hF8⟩ := exists_card_eight_le_of_sq_eq_one hU2 h8
      exact ⟨F, hFU.trans hUC, fun f hf u hu => hUc f (hFU hf) u hu, hF2, hF8⟩
  have hF₀p : IsPGroup 2 F₀ := IsPGroup.of_card (n := 3) (by rw [hF₀8]; norm_num)
  have hF₀O : F₀ ≤ normalizer (O : Set G) := fun f hf => hNO f (hCN (hF₀C hf))
  have hW₀O : W₀ ≤ normalizer (O : Set G) := fun w hw => hNO w (hW₀N hw)
  have hUOn : U ≤ normalizer (O : Set G) := fun u hu => hNO u (hCN (hUC hu))
  have hwF : ∀ f ∈ F₀, ∀ w ∈ W₀, f⁻¹ * (w * f * w⁻¹) ∈ O := by
    intro f hf w hw
    have hfO := hF₀O hf
    obtain ⟨m, hm, c, hc, rfl⟩ : ∃ m ∈ M, ∃ c ∈ C, m * c = w := by
      have h1 : w ∈ ((M : Set G) * C) := by
        rw [← coe_mul_of_left_le_normalizer_right M C
          (hMN.trans (normalizer_le_normalizer_coreActionKernel M))]
        exact hW₀MC hw
      obtain ⟨m, hm, c, hc, hmc⟩ := Set.mem_mul.mp h1
      exact ⟨m, hm, c, hc, hmc⟩
    have hcV : c ∈ V := by
      refine mem_inf.mpr ⟨?_, hc⟩
      have h1 : c = m⁻¹ * (m * c) := by group
      rw [h1]
      exact mul_mem (mem_sup_right (inv_mem hm)) (mem_sup_left hw)
    obtain ⟨u, hu, o, ho, rfl⟩ : ∃ u ∈ U, ∃ o ∈ O, u * o = c := by
      have h1 : c ∈ ((U : Set G) * O) := by
        rw [← coe_mul_of_left_le_normalizer_right U O hUOn, hUO]
        exact hcV
      obtain ⟨u, hu, o, ho, huo⟩ := Set.mem_mul.mp h1
      exact ⟨u, hu, o, ho, huo⟩
    have hfu : f * u = u * f := hF₀U f hf u hu
    set o' := f⁻¹ * o * f * o⁻¹ with ho'def
    have ho' : o' ∈ O := mul_mem (by
      have := (mem_normalizer_iff.mp (inv_mem hfO) o).mp ho
      simpa using this) (inv_mem ho)
    set o'' := u * o' * u⁻¹ with ho''def
    have ho'' : o'' ∈ O := (mem_normalizer_iff.mp (hUOn hu) o').mp ho'
    have h1 : m * (u * o) * f * (m * (u * o))⁻¹ = (m * f * m⁻¹) * (m * o'' * m⁻¹) := by
      have h2 : u * (o * f * o⁻¹) * u⁻¹ = f * o'' := by
        rw [ho''def, ho'def]
        calc u * (o * f * o⁻¹) * u⁻¹ = u * f * (f⁻¹ * o * f * o⁻¹) * u⁻¹ := by group
          _ = f * u * (f⁻¹ * o * f * o⁻¹) * u⁻¹ := by rw [hfu]
          _ = f * (u * (f⁻¹ * o * f * o⁻¹) * u⁻¹) := by group
      calc m * (u * o) * f * (m * (u * o))⁻¹ = m * (u * (o * f * o⁻¹) * u⁻¹) * m⁻¹ := by group
        _ = m * (f * o'') * m⁻¹ := by rw [h2]
        _ = (m * f * m⁻¹) * (m * o'' * m⁻¹) := by group
    rw [h1, show f⁻¹ * (m * f * m⁻¹ * (m * o'' * m⁻¹)) =
      (f⁻¹ * (m * f * m⁻¹)) * (m * o'' * m⁻¹) by group]
    exact mul_mem (inv_mul_conj_mem_oddCoreIn (hF₀C hf) hm)
      ((mem_normalizer_iff.mp (hNO m (hMN hm)) o'').mp ho'')
  obtain ⟨k, hk, hkF⟩ := exists_conj_le_centralizer_of_odd_isPGroup (odd_card_oddCoreIn M) hF₀O
    hF₀p hW₀p hW₀O hwF
  have hkC : k ∈ C := (sup_le hF₀C hOC) hk
  refine ⟨conjugate F₀ k, le_inf (fun x hx => ?_) hkF, sq_eq_one_of_mem_conjugate hF₀2 k,
    by rw [card_conjugate_eq_card, hF₀8]⟩
  rw [mem_conjugate_iff] at hx
  have h1 : k⁻¹ * (k * x * k⁻¹) * k = x := by group
  rw [← h1]
  exact mul_mem (mul_mem (inv_mem hkC) (hF₀C hx)) hkC

theorem exists_isKleinFour_le_inf_sup
    (h : FooteSec4 G L) (hFI : FooteFourgroupInner)
    {M : Subgroup G} (hM : IsFooteM L M) {E : Subgroup G} (hEN : E ≤ normalizer (M : Set G))
    (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hE8 : Nat.card E = 8)
    (hEC : ∀ x ∈ E, x ∈ coreActionKernel M → x = 1) :
    ∃ E₀ : Subgroup G, IsKleinFour E₀ ∧ E₀ ≤ E ∧ E₀ ≤ M ⊔ coreActionKernel M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨ε⟩⟩ := hM.quotient h
  set N := normalizer (M : Set G) with hN
  have key : ∀ W : Subgroup G, IsKleinFour W → W ≤ E →
      ∃ w ∈ W, w ≠ 1 ∧ w ∈ M ⊔ coreActionKernel M := by
    intro W hW hWE
    have hWN : W ≤ N := hWE.trans hEN
    set W' := (W.subgroupOf N).map (footeAct ε) with hW'
    have hinj : Function.Injective ((footeAct ε).comp (W.subgroupOf N).subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      apply Subtype.ext
      apply Subtype.ext
      exact hEC _ (hWE x.2) (mem_coreActionKernel_of_footeAct_eq_one ε hx)
    have hW'4 : Nat.card W' = 4 := by
      have hr : ((footeAct ε).comp (W.subgroupOf N).subtype).range = W' := by
        rw [MonoidHom.range_comp, range_subtype]
      rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, ← hW.card_four]
      exact Nat.card_congr (subgroupOfEquivOfLe hWN).toEquiv
    have hW'2 : ∀ φ ∈ W', φ * φ = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      have hx2 : x * x = 1 := Subtype.ext (by
        rw [Subgroup.coe_mul, OneMemClass.coe_one, ← sq]
        exact sq_eq_one_of_isKleinFour hW hx)
      rw [← map_mul, hx2, map_one]
    obtain ⟨φ, ⟨x, hx, rfl⟩, hφ1, hφI⟩ := hFI _ h.footeFamilyType W' hW'2 hW'4
    refine ⟨x, hx, fun h1 => hφ1 ?_, mem_sup_of_footeAct_mem_range ε hφI⟩
    have : x = 1 := Subtype.ext h1
    rw [this, map_one]
  set E₀ := E ⊓ (M ⊔ coreActionKernel M) with hE₀
  have hE₀2 : ∀ x ∈ E₀, x ^ 2 = 1 := fun x hx => hE2 x (mem_inf.mp hx).1
  have hE₀p : IsPGroup 2 E₀ := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hE₀2 x x.2)⟩
  by_cases h4 : 4 ≤ Nat.card E₀
  · obtain ⟨W, hW, hWE₀⟩ := exists_isKleinFour_le hE₀2 h4
    exact ⟨W, hW, hWE₀.trans inf_le_left, hWE₀.trans inf_le_right⟩
  exfalso
  push Not at h4
  obtain ⟨W, hW, hWE, hWE₀⟩ : ∃ W : Subgroup G, IsKleinFour W ∧ W ≤ E ∧
      ∀ x ∈ W, x ∈ E₀ → x = 1 := by
    by_cases hbot : E₀ = ⊥
    · obtain ⟨W, hW, hWE⟩ := exists_isKleinFour_le hE2 (by omega)
      exact ⟨W, hW, hWE, fun x _ hx => by rw [hbot] at hx; exact (mem_bot).mp hx⟩
    · obtain ⟨v, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
      have hv1' : (v : G) ≠ 1 := fun h1 => hv1 (Subtype.ext h1)
      obtain ⟨W, hW, hWE, hvW⟩ := Foote47.exists_isKleinFour_not_mem hE2 hE8
        (mem_inf.mp v.2).1 hv1'
      refine ⟨W, hW, hWE, fun x hxW hxE₀ => ?_⟩
      by_contra hx1
      obtain ⟨k, hk⟩ := hE₀p.exists_card_eq
      have hk1 : k = 1 := by
        rcases k with _ | _ | k
        · exact absurd (Subgroup.card_eq_one.mp hk) hbot
        · rfl
        · exfalso
          rw [hk, pow_succ, pow_succ] at h4
          have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
          omega
      rw [hk1, pow_one] at hk
      obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥E₀)).mp hk
      have e1 := hy v hv1
      have e2 := hy ⟨x, hxE₀⟩ (fun h1 => hx1 (congrArg Subtype.val h1))
      have : x = v := congrArg Subtype.val (e2.trans e1.symm)
      exact hvW (this ▸ hxW)
  obtain ⟨w, hwW, hw1, hwMC⟩ := key W hW hWE
  exact hw1 (hWE₀ w hwW (mem_inf.mpr ⟨hWE hwW, hwMC⟩))


end CFSG.ComponentClassification.FooteLit
