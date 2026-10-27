module

public import CFSG.LocalAnalysis.SteinbergBVSp6NonnormalLayer
public import CFSG.LocalAnalysis.EvenBN.GMSK.Statement
public import CFSG.LocalAnalysis.EvenBN.GMSK.SL2Facts
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.LocalCores CFSG.LocalAnalysis.SteinbergBV
open scoped commutatorElement

open OneOrTwoLayer in
theorem nonnormal_involution_component_layer {H : Type} [Group H] [Finite H]
    (hcore : CFSG.pPrimeCore 2 H = ⊥) {J : Subgroup H} [IsSimpleGroup J]
    (hJna : ∃ x y : J, x * y ≠ y * x)
    (hJ4 : ∃ E : Subgroup H, E ≤ J ∧ CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 4)
    {a : H} (ha : orderOf a = 2) (hJa : J ≤ centralizer ({a} : Set H))
    (hJn : centralizer ({a} : Set H) ≤ normalizer (J : Set H))
    (hsyl : ¬ 2 ∣ (zpowers a).relIndex (centralizer (J : Set H))) (hJnn : ¬ J.Normal) :
    OneOrTwoLayerConclusion J a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haB : a ∈ centralizer (J : Set H) := mem_centralizer_iff.2 fun j hj =>
    mem_centralizer_singleton_iff.1 (hJa hj)
  have hB4 := not_four_dvd_card ha haB hsyl
  have hJ4' : 4 ∣ Nat.card J := by
    obtain ⟨E, hEJ, -, hE4⟩ := hJ4
    rw [← hE4]
    exact card_dvd_of_le hEJ
  have hJ1 : ∃ j : J, j ≠ 1 := exists_ne 1
  set L₀ := J.subgroupOf (centralizer ({a} : Set H)) with hL₀def
  have hL₀ : CFSG.IsComponent L₀ :=
    ⟨isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hJa).symm (isQuasisimple_of_simple hJna),
      ((normal_subgroupOf_iff_le_normalizer hJa).2 hJn).isSubnormal⟩
  have hL₀map : L₀.map (centralizer ({a} : Set H)).subtype = J := by
    rw [hL₀def, subgroupOf_map_subtype, inf_eq_left.2 hJa]
  set B := centralizer (J : Set H) with hBdef
  have hza : IsPGroup 2 (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  have hP2 : IsPGroup 2 ((zpowers a).subgroupOf B) :=
    hza.comap_of_injective _ B.subtype_injective
  have hsyl' : ¬ 2 ∣ ((zpowers a).subgroupOf B).index := by
    rwa [Subgroup.relIndex] at hsyl
  set S₀ := hP2.toSylow hsyl' with hS₀def
  have hmemS₀ : ∀ x : B, x ∈ S₀ → (x : H) = 1 ∨ (x : H) = a := fun x hx => by
    rw [hS₀def, IsPGroup.mem_toSylow] at hx
    exact eq_one_or_eq_of_mem_zpowers ha hx
  have hO2 : CFSG.pCore 2 H = ⊥ := by
    have hcomm := CFSG.LocalAnalysis.ComponentInitial.involution_component_centralizes_two_core
      ha L₀ hL₀
    rw [hL₀map, commutator_comm] at hcomm
    have hQB : CFSG.pCore 2 H ≤ B := commutator_eq_bot_iff_le_centralizer.1 hcomm
    have hN2 : IsPGroup 2 ((CFSG.pCore 2 H).subgroupOf B) :=
      CFSG.pCore_isPGroup.comap_of_injective _ B.subtype_injective
    have hle := hN2.le_sylow_of_normal S₀
    have hQa : ∀ q ∈ CFSG.pCore 2 H, q = 1 ∨ q = a := fun q hq =>
      hmemS₀ ⟨q, hQB hq⟩ (hle hq)
    by_contra hne
    obtain ⟨⟨q, hq⟩, hq1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    have hqa : q = a := (hQa q hq).resolve_left fun h => hq1 (Subtype.ext h)
    rw [hqa] at hq
    apply hJnn
    have htop : centralizer ({a} : Set H) = ⊤ := by
      refine eq_top_iff.2 fun g _ => mem_centralizer_singleton_iff.2 ?_
      have hm : g * a * g⁻¹ ∈ CFSG.pCore 2 H :=
        (inferInstance : (CFSG.pCore 2 H).Normal).conj_mem a hq g
      rcases hQa _ hm with h | h
      · exfalso
        have h1 : a = 1 := by
          calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
            _ = 1 := by rw [h]; group
        rw [h1, orderOf_one] at ha
        exact absurd ha (by norm_num)
      · calc g * a = g * a * g⁻¹ * g := by group
          _ = a * g := by rw [h]
    exact normalizer_eq_top_iff.1 (top_le_iff.1 (htop ▸ hJn))
  have hF : CFSG.fittingSubgroup H = ⊥ := by
    rw [fittingSubgroup_eq_iSup_pCore, eq_bot_iff]
    refine iSup_le fun p => ?_
    have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    by_cases hp2 : (p : ℕ) = 2
    · rw [hp2, hO2]
    · rw [← hcore]
      have : Fact (p : ℕ).Prime := ⟨hp⟩
      refine le_sSup ⟨inferInstance, ?_⟩
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := (p : ℕ)) (G := H))
      rw [hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have hJE : J ≤ CFSG.layer H :=
    CFSG.SeitzReduction.isComponent_centralizer_le_layer hcore
      (by rw [← ha]; exact pow_orderOf_eq_one a) hJa hL₀
  have hZ : ∀ K : Subgroup H, CFSG.IsComponent K → center K = ⊥ := fun K hK =>
    center_eq_bot_of_fitting_eq_bot hF hK
  have hZE := center_layer_eq_bot hF
  set D := normalClosure (J : Set H) with hDdef
  have hJD : J ≤ D := le_normalClosure
  have hDE : D ≤ CFSG.layer H := by
    have := layer_characteristic (G := H)
    exact normalClosure_le_normal hJE
  have hDeq := eq_iSup_components_of_normal hZE hDE
  have hDZ : D ⊓ centralizer (D : Set H) = ⊥ := by
    have h := map_center_le_fitting D
    rw [hF, le_bot_iff] at h
    refine eq_bot_iff.2 fun x hx => ?_
    have hx' : x ∈ (center D).map D.subtype := (mem_map_center_iff D).2 ⟨hx.1, hx.2⟩
    rwa [h] at hx'
  have hA : ∀ L : Subgroup H, CFSG.IsComponent L → L ≤ D → J ⊓ centralizer (L : Set H) = ⊥ :=
    fun L hL hLD => inf_centralizer_eq_bot hZ hJ4' hJE hB4 hL hLD
  have hcomp_ne : ∀ K : Subgroup H, CFSG.IsComponent K → K ≠ ⊥ := fun K hK =>
    (Subgroup.nontrivial_iff_ne_bot K).1 (isQuasisimple_nontrivial hK.1)
  obtain ⟨K₀, hK₀, hK₀D⟩ : ∃ K₀ : Subgroup H, CFSG.IsComponent K₀ ∧ K₀ ≤ D := by
    by_contra hno
    push Not at hno
    have hDbot : D = ⊥ := hDeq.trans (iSup₂_eq_bot.2 fun K hK => absurd hK.2 (hno K hK.1))
    obtain ⟨j, hj1⟩ := hJ1
    have hj := hJD j.2
    rw [hDbot, mem_bot] at hj
    exact hj1 (Subtype.ext hj)
  set c : H →* H := (MulAut.conj a⁻¹).toMonoidHom with hc
  have hc_apply : ∀ x, c x = a⁻¹ * x * a := fun x => by
    rw [hc]
    simp
  set K₁ := K₀.map c with hK₁def
  have hK₁ : CFSG.IsComponent K₁ := isComponent_map_mulEquiv _ hK₀
  have hK₁D : K₁ ≤ D := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hc_apply]
    have := (normalClosure_normal (s := (J : Set H))).conj_mem x (hK₀D hx) a⁻¹
    rwa [inv_inv] at this
  have hpair : ∀ L : Subgroup H, CFSG.IsComponent L → L ≤ D → L = K₀ ∨ L = K₁ :=
    fun L hL hLD => components_le_pair hJna hJE ha hJa hJn hA hDZ hDeq hK₀ hK₀D hL hLD
  have hDK : D = K₀ ⊔ K₁ := by
    apply le_antisymm
    · calc D = ⨆ (K : Subgroup H) (_ : CFSG.IsComponent K ∧ K ≤ D), K := hDeq
        _ ≤ K₀ ⊔ K₁ := iSup₂_le fun K hK => by
          rcases hpair K hK.1 hK.2 with h | h
          · rw [h]
            exact le_sup_left
          · rw [h]
            exact le_sup_right
    · exact sup_le hK₀D hK₁D
  have hsimple₀ := isSimpleGroup_of_isComponent hK₀ (hZ K₀ hK₀)
  have hsimple₁ := isSimpleGroup_of_isComponent hK₁ (hZ K₁ hK₁)
  have hJDne : J ≠ D := fun h => hJnn (h ▸ normalClosure_normal)
  have halt : OneOrTwoLayerAlternatives J D a ∧ ∃ d ∈ D, a⁻¹ * d * a ≠ d := by
    by_cases h01 : K₁ = K₀
    · have hD0 : D = K₀ := by rw [hDK, h01, sup_idem]
      have hDs : IsSimpleGroup D := by
        rw [hD0]
        exact hsimple₀.1
      have hnt : ∃ d ∈ D, a⁻¹ * d * a ≠ d := by
        by_contra hall
        push Not at hall
        have hDa : D ≤ centralizer ({a} : Set H) := fun d hd => by
          rw [mem_centralizer_singleton_iff]
          calc d * a = a * (a⁻¹ * d * a) := by group
            _ = a * d := by rw [hall d hd]
        have hn : (J.subgroupOf D).Normal :=
          (normal_subgroupOf_iff_le_normalizer hJD).2 (hDa.trans hJn)
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (J.subgroupOf D) with h | h
        · obtain ⟨j, hj1⟩ := hJ1
          have hj : (⟨j, hJD j.2⟩ : D) ∈ J.subgroupOf D := j.2
          rw [h, mem_bot] at hj
          have hj' : (j : H) = 1 := congrArg Subtype.val hj
          exact hj1 (Subtype.ext hj')
        · apply hJDne
          refine le_antisymm hJD fun x hx => ?_
          have : (⟨x, hx⟩ : D) ∈ J.subgroupOf D := h ▸ mem_top _
          exact this
      refine ⟨Or.inl ⟨⟨hDs, ?_, lt_of_le_of_ne hJD hJDne, hnt⟩, ?_⟩, hnt⟩
      · obtain ⟨x, y, hxy⟩ := hsimple₀.2
        refine ⟨⟨x, hD0 ▸ x.2⟩, ⟨y, hD0 ▸ y.2⟩, fun h => ?_⟩
        have h' : (x : H) * y = y * x := congrArg Subtype.val h
        exact hxy (Subtype.ext h')
      · rintro ⟨D₁, D₂, hD₁, hD₂, hne, -, -, -, -, hsup, -⟩
        have h1 := hpair D₁ hD₁ (hsup ▸ le_sup_left)
        have h2 := hpair D₂ hD₂ (hsup ▸ le_sup_right)
        rw [h01] at h1 h2
        exact hne ((h1.elim id id).trans (h2.elim id id).symm)
    · obtain ⟨hJeq, ψ, hψ1, hψ2⟩ := two_factor_data hZ ha hJa hJn hK₀ (Ne.symm h01) hDK hJD
      have hcomm : ⁅K₀, K₁⁆ = ⊥ :=
        (distinct_components_commute hK₀ hK₁).resolve_left (Ne.symm h01)
      have hinf : K₀ ⊓ K₁ = ⊥ := by
        refine eq_bot_iff.2 fun x hx => ?_
        have hz : (⟨x, hx.1⟩ : K₀) ∈ center K₀ := mem_center_iff.2 fun g => Subtype.ext
          (mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hcomm g.2) x hx.2).symm
        rw [hZ K₀ hK₀, mem_bot] at hz
        exact mem_bot.2 (congrArg Subtype.val hz)
      have hnt : ∃ d ∈ D, a⁻¹ * d * a ≠ d := by
        by_contra hall
        push Not at hall
        apply h01
        refine le_antisymm ?_ ?_
        · rintro _ ⟨x, hx, rfl⟩
          rw [hc_apply, hall x (hK₀D hx)]
          exact hx
        · intro x hx
          refine ⟨x, hx, ?_⟩
          rw [hc_apply, hall x (hK₀D hx)]
      refine ⟨Or.inr ⟨⟨K₀, K₁, hK₀, hK₁, Ne.symm h01, hsimple₀.1, hsimple₀.2, hsimple₁.1,
        hsimple₁.2, hDK.symm, hinf, hcomm, rfl, hJeq, ψ, hψ1, hψ2⟩, ?_⟩, hnt⟩
      rintro ⟨hDs, -⟩
      have hn : (K₀.subgroupOf D).Normal :=
        (normal_subgroupOf_iff_le_normalizer hK₀D).2 (hDE.trans (layer_le_normalizer hK₀))
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K₀.subgroupOf D) with h | h
      · apply hcomp_ne K₀ hK₀
        refine eq_bot_iff.2 fun x hx => ?_
        have : (⟨x, hK₀D hx⟩ : D) ∈ K₀.subgroupOf D := hx
        rw [h, mem_bot] at this
        exact mem_bot.2 (congrArg Subtype.val this)
      · apply hcomp_ne K₁ hK₁
        refine eq_bot_iff.2 fun x hx => ?_
        have hxK₀ : x ∈ K₀ := by
          have : (⟨x, hK₁D hx⟩ : D) ∈ K₀.subgroupOf D := h ▸ mem_top _
          exact this
        have : x ∈ K₀ ⊓ K₁ := ⟨hxK₀, hx⟩
        rwa [hinf] at this
  obtain ⟨halt, hnt⟩ := halt
  have hCD : centralizer (D : Set H) = ⊥ := by
    set CD := centralizer (D : Set H) with hCDdef
    have hCDB : CD ≤ B := centralizer_le hJD
    have haCD : a ∉ CD := fun h => by
      obtain ⟨d, hd, hda⟩ := hnt
      apply hda
      have := mem_centralizer_iff.1 h d hd
      calc a⁻¹ * d * a = a⁻¹ * (d * a) := by group
        _ = a⁻¹ * (a * d) := by rw [this]
        _ = d := by group
    have hodd : ¬ 2 ∣ Nat.card CD := by
      intro h2
      obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := CD) 2 h2
      have hbB : (b : H) ∈ B := hCDB b.2
      have hbo : orderOf (⟨(b : H), hbB⟩ : B) = 2 := by
        rw [← Subgroup.orderOf_coe, show ((⟨(b : H), hbB⟩ : B) : H) = b from rfl,
          Subgroup.orderOf_coe, hb]
      have hb2 : IsPGroup 2 (zpowers (⟨b, hbB⟩ : B)) := IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, hbo, pow_one])
      obtain ⟨S, hS⟩ := hb2.exists_le_sylow
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq B S₀ S
      have hbS : (⟨b, hbB⟩ : B) ∈ (S : Subgroup B) := hS (mem_zpowers _)
      rw [← hg, Sylow.coe_subgroup_smul, mem_smul_pointwise_iff_exists] at hbS
      obtain ⟨s, hs, hsb⟩ := hbS
      rw [MulAut.smul_def, MulAut.conj_apply] at hsb
      have hsb' : (g : H) * s * (g : H)⁻¹ = b := congrArg Subtype.val hsb
      rcases hmemS₀ s hs with h | h
      · rw [h, mul_one, mul_inv_cancel] at hsb'
        have hb1 : b = 1 := Subtype.ext hsb'.symm
        rw [hb1, orderOf_one] at hb
        exact absurd hb (by norm_num)
      · apply haCD
        have hmem : (g : H)⁻¹ * b * (g : H)⁻¹⁻¹ ∈ CD :=
          (inferInstance : CD.Normal).conj_mem _ b.2 _
        rw [← hsb', h, inv_inv] at hmem
        have e : (g : H)⁻¹ * ((g : H) * a * (g : H)⁻¹) * (g : H) = a := by group
        rwa [e] at hmem
    rw [eq_bot_iff, ← hcore]
    refine le_sSup ⟨inferInstance, ?_⟩
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd
  have hDE' : D = CFSG.layer H := by
    refine le_antisymm hDE (sSup_le fun K hK => ?_)
    rcases component_normal_subgroup hK (normalClosure_normal (s := (J : Set H))) with h | h
    · exact h
    · exfalso
      apply hcomp_ne K hK
      have hKC : K ≤ centralizer (D : Set H) := commutator_eq_bot_iff_le_centralizer.1 h
      rwa [hCD, le_bot_iff] at hKC
  refine ⟨hO2, hF, hJE, hDE', hCD, halt, fun h hh => ?_⟩
  have hhC : h ∈ centralizer (D : Set H) := mem_centralizer_iff.2 fun d hd => by
    calc d * h = h * (h⁻¹ * d * h) := by group
      _ = h * d := by rw [hh d hd]
  rw [hCD] at hhC
  exact mem_bot.1 hhC

theorem nonnormalInvolutionComponentLayerStmt : NonnormalInvolutionComponentLayerStmt :=
  fun _ _ _ _ hcore _ _ hJna hJ4 _ ha hJa hJn hsyl hJnn =>
    nonnormal_involution_component_layer hcore hJna hJ4 ha hJa hJn hsyl hJnn

section Data

variable {G : Type} [Group G] {A : Subgroup G} {n : ℕ}

theorem pPrimeCore_eq_bot_of_oddCore_eq_bot {X : Type*} [Group X]
    (hO : CFSG.Open.standardComponentOddCore X = ⊥) : CFSG.pPrimeCore 2 X = ⊥ := by
  rw [eq_bot_iff]
  refine sSup_le fun N hN => ?_
  rw [← hO]
  exact le_sSup ⟨hN.1, Nat.coprime_two_left.mp hN.2⟩

namespace StdLinearData

variable (h : StdLinearData G A n)
include h

theorem isSimpleGroup : IsSimpleGroup A := by
  obtain ⟨hn, -, -, k, _, _, hk, ⟨φ⟩⟩ := h
  have := sl2_isSimpleGroup (two_eq_zero_of_card (by omega) hk)
    (hk ▸ (Nat.pow_le_pow_right (by norm_num) hn : 2 ^ 2 ≤ 2 ^ n))
  exact φ.isSimpleGroup

theorem exists_mul_ne : ∃ x y : A, x * y ≠ y * x := by
  obtain ⟨-, -, -, k, _, _, -, ⟨φ⟩⟩ := h
  obtain ⟨x, y, hxy⟩ := sl2_exists_mul_ne (K := k)
  exact ⟨φ.symm x, φ.symm y, fun e => hxy (by simpa using congrArg φ e)⟩

theorem exists_four : ∃ E : Subgroup G, E ≤ A ∧ CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hn, -, -, k, _, _, hk, ⟨φ⟩⟩ := h
  obtain ⟨E, hE, hE4⟩ := exists_elementaryAbelian_four (two_eq_zero_of_card (by omega) hk)
    (hk ▸ pow_dvd_pow 2 hn : 2 ^ 2 ∣ Fintype.card k)
  set f : Multiplicative k →* G := A.subtype.comp (φ.symm.toMonoidHom.comp (sl2Upper k))
  have hf : Function.Injective f :=
    A.subtype_injective.comp (φ.symm.injective.comp sl2Upper_injective)
  refine ⟨E.map f, ?_, CFSG.IsElementaryAbelian.map f, by rw [card_map_of_injective hf, hE4]⟩
  rintro _ ⟨x, -, rfl⟩
  exact (φ.symm (sl2Upper k x)).2

theorem isStandard : CFSG.Assembly.ComponentType.IsStandardSubgroup A := h.2.1

theorem not_normal : ¬ A.Normal := h.2.2.1

end StdLinearData

end Data

section RankOne

variable {G : Type*} [Group G] [Finite G] {C : Subgroup G}

theorem card_le_two_of_sylow (hC : ∀ S : Sylow 2 C, Nat.card S = 2) {P : Subgroup G}
    (hPC : P ≤ C) (hP : IsPGroup 2 P) : Nat.card P ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 (P.subgroupOf C) := hP.of_equiv (subgroupOfEquivOfLe hPC).symm
  obtain ⟨S, hS⟩ := hP'.exists_le_sylow
  calc Nat.card P = Nat.card (P.subgroupOf C) :=
        Nat.card_congr (subgroupOfEquivOfLe hPC).toEquiv.symm
    _ ≤ Nat.card S := card_le_of_le hS
    _ = 2 := hC S

theorem exists_involution_of_sylow (hC : ∀ S : Sylow 2 C, Nat.card S = 2) :
    ∃ t ∈ C, orderOf t = 2 ∧ ¬ 2 ∣ (zpowers t).relIndex C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 C))
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 (by rw [hC S])
  set u : C := (s : C) with hu
  have hzu : zpowers u = (S : Subgroup C) := by
    refine eq_of_le_of_card_ge (zpowers_le.2 s.2) ?_
    rw [Nat.card_zpowers, show orderOf u = 2 by rw [hu, Subgroup.orderOf_coe, hs]]
    exact (hC S).le
  refine ⟨u, u.2, by rw [Subgroup.orderOf_coe, hu, Subgroup.orderOf_coe, hs], ?_⟩
  have hsub : (zpowers (u : G)).subgroupOf C = (S : Subgroup C) := by
    rw [← hzu, show zpowers (u : G) = (zpowers u).map C.subtype from
      (MonoidHom.map_zpowers C.subtype u).symm, Subgroup.subgroupOf,
      comap_map_eq_self_of_injective C.subtype_injective]
  rw [Subgroup.relIndex, hsub]
  exact Sylow.not_dvd_index S

end RankOne

theorem oneOrTwoLayer_of_stdLinearData {G : Type} [Group G] [Finite G]
    (hO : CFSG.Open.standardComponentOddCore G = ⊥) {n : ℕ} {A : Subgroup G}
    (hA : StdLinearData G A n) {t : G} (ht : orderOf t = 2) (htA : t ∈ centralizer (A : Set G))
    (hsyl : ¬ 2 ∣ (zpowers t).relIndex (centralizer (A : Set G))) :
    OneOrTwoLayerConclusion A t := by
  have := hA.isSimpleGroup
  obtain ⟨hCt, hAt, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hA.isStandard
      htA ht
  exact nonnormal_involution_component_layer (pPrimeCore_eq_bot_of_oddCore_eq_bot hO)
    hA.exists_mul_ne hA.exists_four ht hAt hCt hsyl hA.not_normal

end CFSG.LocalAnalysis.EvenBN.GMSK
