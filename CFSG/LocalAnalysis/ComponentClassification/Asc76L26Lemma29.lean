module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GroupTheory.ThompsonAxB
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.AS76bInputs

public section

namespace CFSG.ComponentClassification.Asc76.L26

open Subgroup CFSG.ComponentClassification.AS76b
open scoped Pointwise

variable {G : Type*} [Group G]

theorem inf_eq_bot_of_odd_of_isPGroup [Finite G] {X Y : Subgroup G} (hX : Odd (Nat.card X))
    (hY : IsPGroup 2 Y) : X ⊓ Y = ⊥ := by
  rw [← disjoint_iff]
  apply Subgroup.disjoint_of_coprime_natCard
  obtain ⟨k, hk⟩ := hY.exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hX)

theorem mem_normalizer_of_commute {U : Subgroup G} {c : G} (hc : ∀ u ∈ U, u * c = c * u) :
    c ∈ normalizer (U : Set G) := by
  rw [mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    have : c * u * c⁻¹ = u := by rw [← hc u hu]; group
    rw [this]; exact hu
  · intro hu
    have h := hc _ hu
    have : u = c * u * c⁻¹ := by
      calc u = c⁻¹ * ((c * u * c⁻¹) * c) := by group
        _ = c⁻¹ * (c * (c * u * c⁻¹)) := by rw [h]
        _ = c * u * c⁻¹ := by group
    rw [this]; exact hu

theorem commutatorElement_mem_inf {X Y : Subgroup G} {x y : G} (hx : x ∈ X) (hy : y ∈ Y)
    (hxY : x ∈ normalizer (Y : Set G)) (hyX : y ∈ normalizer (X : Set G)) :
    x * y * x⁻¹ * y⁻¹ ∈ X ⊓ Y := by
  refine mem_inf.mpr ⟨?_, ?_⟩
  · have h2 : y * x⁻¹ * y⁻¹ ∈ X := (mem_normalizer_iff.mp hyX x⁻¹).mp (X.inv_mem hx)
    have : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
    rw [this]
    exact X.mul_mem hx h2
  · exact Y.mul_mem ((mem_normalizer_iff.mp hxY y).mp hy) (Y.inv_mem hy)

theorem commute_of_inf_eq_bot {X Y : Subgroup G} (hXY : X ⊓ Y = ⊥) {x y : G} (hx : x ∈ X)
    (hy : y ∈ Y) (hxY : x ∈ normalizer (Y : Set G)) (hyX : y ∈ normalizer (X : Set G)) :
    x * y = y * x := by
  have hc := commutatorElement_mem_inf hx hy hxY hyX
  rw [hXY, mem_bot] at hc
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [hc, one_mul]

theorem pPrimeCore_two_le_oddCore : CFSG.pPrimeCore 2 G ≤ CFSG.Assembly.oddCore G :=
  sSup_le fun _ hK => le_sSup ⟨hK.1, Nat.coprime_two_left.mp hK.2⟩

theorem eq_bot_of_oddCore_eq_bot [Finite G] (hO : CFSG.Assembly.oddCore G = ⊥)
    {U X : Subgroup G} (hU : IsPGroup 2 U) (hUP : U ≤ CFSG.pCore 2 G) (hX : Odd (Nat.card X))
    (hXN : X ≤ normalizer (U : Set G)) (hNX : normalizer (U : Set G) ≤ normalizer (X : Set G)) :
    X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.pCore 2 G with hPdef
  have hP : IsPGroup 2 P := CFSG.pCore_isPGroup (p := 2) (G := G)
  have hUX : U ≤ normalizer (X : Set G) := le_normalizer.trans hNX
  have hXU : X ⊓ U = ⊥ := inf_eq_bot_of_odd_of_isPGroup hX hU
  have hXP : X ⊓ P = ⊥ := inf_eq_bot_of_odd_of_isPGroup hX hP
  have hNP : normalizer (P : Set G) = ⊤ := normalizer_eq_top P
  have hcommU : ∀ x ∈ X, ∀ u ∈ U, x * u = u * x := fun x hx u hu =>
    commute_of_inf_eq_bot hXU hx hu (hXN hx) (hUX hu)
  have hcent : ∀ x ∈ X, ∀ c ∈ P, (∀ u ∈ U, u * c = c * u) → x * c = c * x := by
    intro x hx c hc hcU
    exact commute_of_inf_eq_bot hXP hx hc (by rw [hNP]; exact mem_top x)
      (hNX (mem_normalizer_of_commute hcU))
  have hXcP : ∀ x ∈ X, ∀ c ∈ P, x * c = c * x := by
    let α : X →* MulAut P := (MulAut.conjNormal (H := P)).comp X.subtype
    let β : U →* MulAut P := (MulAut.conjNormal (H := P)).comp U.subtype
    have hA : ¬ 2 ∣ Nat.card X := fun h => (Nat.not_even_iff_odd.mpr hX) (even_iff_two_dvd.mpr h)
    have key := CFSG.GroupTheory.thompson_A_times_B (p := 2) hP hA hU α β (fun a b => by
        change MulAut.conjNormal (a : G) * MulAut.conjNormal (b : G) =
          MulAut.conjNormal (b : G) * MulAut.conjNormal (a : G)
        rw [← map_mul, ← map_mul, hcommU a a.2 b b.2])
      (fun a r hr => by
        apply Subtype.ext
        change (a : G) * r * (a : G)⁻¹ = r
        have h := hcent a a.2 r r.2 (fun u hu => by
          have h1 := congrArg Subtype.val (hr ⟨u, hu⟩)
          change u * r * u⁻¹ = r at h1
          calc u * r = u * r * u⁻¹ * u := by group
            _ = r * u := by rw [h1])
        calc (a : G) * r * (a : G)⁻¹ = (r : G) * a * (a : G)⁻¹ := by rw [h]
          _ = r := by group)
    intro x hx c hc
    have h := congrArg (fun φ : MulAut P => ((φ ⟨c, hc⟩ : P) : G)) (key ⟨x, hx⟩)
    change x * c * x⁻¹ = c at h
    calc x * c = x * c * x⁻¹ * x := by group
      _ = c * x := by rw [h]
  set E := CFSG.layer G with hEdef
  have hEn : E.Normal := by
    have : E.Characteristic := CFSG.LocalCores.layer_characteristic
    infer_instance
  have hUE : U ≤ centralizer (E : Set G) := by
    rw [← commutator_eq_bot_iff_le_centralizer]
    have hUF : U ≤ CFSG.fittingSubgroup G := hUP.trans (CFSG.pCore_le_fitting G 2)
    exact le_bot_iff.mp (CFSG.LocalCores.fitting_layer_commute (G := G) ▸
      commutator_mono hUF le_rfl)
  have hEN : E ≤ normalizer (X : Set G) := fun e he =>
    hNX (mem_normalizer_of_commute fun u hu => (mem_centralizer_iff.mp (hUE hu) e he).symm)
  set D := E ⊓ X with hDdef
  have hDsub : D.IsSubnormal := by
    refine Subgroup.IsSubnormal.step D E inf_le_left hEn.isSubnormal ⟨fun d hd e => ?_⟩
    rw [mem_subgroupOf] at hd ⊢
    obtain ⟨hdE, hdX⟩ := mem_inf.mp hd
    refine mem_inf.mpr ⟨E.mul_mem (E.mul_mem e.2 hdE) (E.inv_mem e.2), ?_⟩
    exact (mem_normalizer_iff.mp (hEN e.2) d).mp hdX
  have hDodd : Odd (Nat.card D) :=
    Odd.of_dvd_nat hX (Subgroup.card_dvd_of_le inf_le_right)
  have hDsol : Group.IsSolvable D := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hDodd
  have hED : ⁅E, D⁆ = ⊥ := (CFSG.LocalCores.component_solvable_centralizer hDsol hDsub).2
  have hEXD : ⁅E, X⁆ ≤ D := by
    rw [commutator_le]
    intro e he x hx
    rw [commutatorElement_def]
    exact commutatorElement_mem_inf he hx (hEN he) (by rw [normalizer_eq_top E]; exact mem_top x)
  have hEX : ⁅E, X⁆ = ⊥ := by
    have h1 : ⁅⁅E, X⁆, E⁆ = ⊥ := le_bot_iff.mp <| by
      calc ⁅⁅E, X⁆, E⁆ ≤ ⁅D, E⁆ := commutator_mono hEXD le_rfl
        _ = ⁅E, D⁆ := commutator_comm _ _
        _ = ⊥ := hED
    have h2 : ⁅⁅X, E⁆, E⁆ = ⊥ := by rw [commutator_comm X E]; exact h1
    have h3 := commutator_commutator_eq_bot_of_rotate h1 h2
    rwa [CFSG.LocalCores.layer_perfect] at h3
  have hF : CFSG.fittingSubgroup G = P :=
    CFSG.Fitting_eq_pcore G 2 (le_bot_iff.mp (hO ▸ pPrimeCore_two_le_oddCore))
  have hXC : X ≤ centralizer (CFSG.generalizedFitting G : Set G) := by
    rw [le_centralizer_iff]
    refine sup_le ?_ ?_
    · rw [hF]
      intro c hc
      exact mem_centralizer_iff.mpr fun x hx => hXcP x hx c hc
    · exact commutator_eq_bot_iff_le_centralizer.mp hEX
  have hXF : X ≤ CFSG.generalizedFitting G := hXC.trans (CFSG.centralizer_generalizedFitting_le G)
  set Z := CFSG.generalizedFitting G ⊓ centralizer (CFSG.generalizedFitting G : Set G)
  have hZn : Z.Normal := by
    have : (CFSG.generalizedFitting G).Normal :=
      (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
    infer_instance
  have hZab : IsMulCommutative Z := ⟨⟨fun a b => Subtype.ext
    (mem_centralizer_iff.mp (mem_inf.mp b.2).2 a (mem_inf.mp a.2).1)⟩⟩
  have hZF : Z ≤ CFSG.fittingSubgroup G := le_sSup ⟨hZn, inferInstance⟩
  have hXP' : X ≤ P := hF ▸ (le_inf hXF hXC).trans hZF
  rw [eq_bot_iff, ← hXP]
  exact le_inf le_rfl hXP'

theorem oddCore_eq_pPrimeCore_two (X : Type*) [Group X] :
    CFSG.Assembly.oddCore X = CFSG.pPrimeCore 2 X := by
  unfold CFSG.Assembly.oddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp [Nat.coprime_two_left]

theorem odd_card_oddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.Assembly.oddCore X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [oddCore_eq_pPrimeCore_two]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

theorem le_oddCore {X : Type*} [Group X] {N : Subgroup X} (hN : N.Normal)
    (hodd : Odd (Nat.card N)) : N ≤ CFSG.Assembly.oddCore X :=
  le_sSup ⟨hN, hodd⟩

theorem card_comap_mk'_eq {X : Type*} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (V : Subgroup (X ⧸ N)) :
    Nat.card (V.comap (QuotientGroup.mk' N)) = Nat.card N * Nat.card V := by
  have h1 := Subgroup.card_mul_index (V.comap (QuotientGroup.mk' N))
  rw [Subgroup.index_comap_of_surjective V (QuotientGroup.mk'_surjective N)] at h1
  have h2 := Subgroup.card_mul_index V
  have h3 := Subgroup.card_mul_index N
  have hV0 : V.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hV0)
  rw [h1, ← h3, Subgroup.index_eq_card, ← h2]
  ring

theorem oddCore_quotient_oddCore_eq_bot [Finite G] :
    CFSG.Assembly.oddCore (G ⧸ CFSG.Assembly.oddCore G) = ⊥ := by
  set O := CFSG.Assembly.oddCore G
  set K := (CFSG.Assembly.oddCore (G ⧸ O)).comap (QuotientGroup.mk' O) with hK
  have hKn : K.Normal := Subgroup.Normal.comap inferInstance _
  have hKodd : Odd (Nat.card K) := by
    rw [hK, card_comap_mk'_eq]
    exact (odd_card_oddCore G).mul (odd_card_oddCore _)
  have hKO : K ≤ O := le_oddCore hKn hKodd
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [mem_bot, QuotientGroup.eq_one_iff]
  exact hKO hx

theorem IsSylowOf.exists_conj_mem [Finite G] {p : ℕ} [Fact p.Prime] {P P' K : Subgroup G}
    (h : CFSG.ABGLocalTools.IsSylowOf p P K) (h' : CFSG.ABGLocalTools.IsSylowOf p P' K) :
    ∃ k ∈ K, ∀ x : G, x ∈ P' ↔ k⁻¹ * x * k ∈ P := by
  obtain ⟨Q, rfl⟩ := h
  obtain ⟨Q', rfl⟩ := h'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q Q'
  have key : ∀ y : K, y ∈ (Q' : Subgroup K) ↔ g⁻¹ * y * g ∈ (Q : Subgroup K) := by
    intro y
    rw [← hg]
    change y ∈ MulAut.conj g • (Q : Subgroup K) ↔ _
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
  refine ⟨g, g.2, fun x => ?_⟩
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g⁻¹ * y * g, (key y).mp hy, by simp⟩
  · rintro ⟨z, hz, hzx⟩
    have hzx' : (z : G) = (g : G)⁻¹ * x * g := hzx
    have hx : x = (g : G) * z * (g : G)⁻¹ := by rw [hzx']; group
    have hxK : x ∈ K := by
      rw [hx]
      exact K.mul_mem (K.mul_mem g.2 z.2) (K.inv_mem g.2)
    refine ⟨⟨x, hxK⟩, (key _).mpr ?_, rfl⟩
    have : g⁻¹ * ⟨x, hxK⟩ * g = z := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hzx'.symm)
    rw [this]
    exact hz

theorem normalizer_map_le_map_normalizer [Finite G] {O U : Subgroup G} [O.Normal]
    (hO : Odd (Nat.card O)) (hU : IsPGroup 2 U) :
    normalizer ((U.map (QuotientGroup.mk' O) : Subgroup (G ⧸ O)) : Set (G ⧸ O)) ≤
      (normalizer (U : Set G)).map (QuotientGroup.mk' O) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro gbar hg
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective O gbar
  set K := U ⊔ O with hKdef
  set V : Subgroup G := U.map (MulAut.conj g).toMonoidHom with hVdef
  have hUK : CFSG.ABGLocalTools.IsSylowOf 2 U K := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_sup_left, hU, fun hdvd => ?_⟩
    rw [hKdef, sup_comm, CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal O U] at hdvd
    have h1 : U.relIndex O ∣ Nat.card O := Subgroup.index_dvd_card (U.subgroupOf O)
    exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr (hdvd.trans h1))
  have hVK : V ≤ K := by
    rintro _ ⟨u, hu, rfl⟩
    have hmem : QuotientGroup.mk' O (g * u * g⁻¹) ∈ U.map (QuotientGroup.mk' O) := by
      have := (mem_normalizer_iff.mp hg (QuotientGroup.mk' O u)).mp ⟨u, hu, rfl⟩
      simpa only [map_mul, map_inv] using this
    obtain ⟨u', hu', hu'eq⟩ := hmem
    have hOmem : u'⁻¹ * (g * u * g⁻¹) ∈ O := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      change (QuotientGroup.mk' O u')⁻¹ * QuotientGroup.mk' O (g * u * g⁻¹) = 1
      rw [hu'eq, inv_mul_cancel]
    have : (MulAut.conj g).toMonoidHom u = u' * (u'⁻¹ * (g * u * g⁻¹)) := by
      simp [MulAut.conj_apply]
    rw [this]
    exact K.mul_mem (mem_sup_left hu') (mem_sup_right hOmem)
  have hVsyl : CFSG.ABGLocalTools.IsSylowOf 2 V K := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hVK ?_
    rw [hVdef, card_map_of_injective (MulAut.conj g).injective]
    exact hUK.card_eq
  obtain ⟨k, hkK, hk⟩ := IsSylowOf.exists_conj_mem hUK hVsyl
  have hn : k⁻¹ * g ∈ normalizer (U : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    have hyV : y ∈ U ↔ g * y * g⁻¹ ∈ V := by
      constructor
      · intro hy
        exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
      · rintro ⟨y', hy', hyy'⟩
        have h1 : g * y' * g⁻¹ = g * y * g⁻¹ := hyy'
        have : y' = y := by simpa using h1
        rwa [← this]
    rw [hyV, hk]
    have : k⁻¹ * (g * y * g⁻¹) * k = k⁻¹ * g * y * (k⁻¹ * g)⁻¹ := by group
    rw [this]
  have hkmem : k ∈ (U : Set G) * (O : Set G) := by
    rw [← Subgroup.mul_normal]
    exact hkK
  obtain ⟨u, hu, o, ho, hkuo⟩ := hkmem
  refine ⟨u * (k⁻¹ * g), mul_mem (le_normalizer hu) hn, ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have : (u * (k⁻¹ * g))⁻¹ * g = g⁻¹ * (u * o * u⁻¹) * g := by
    rw [← hkuo]
    group
  rw [this]
  exact (inferInstance : O.Normal).conj_mem _ ((inferInstance : O.Normal).conj_mem o ho u) g⁻¹
    |> fun h => by simpa [mul_assoc] using h

theorem lemma29 [Finite G] {U : Subgroup G} (hU : IsPGroup 2 U)
    (hUO : U ≤ (CFSG.pCore 2 (G ⧸ CFSG.Assembly.oddCore G)).comap
      (QuotientGroup.mk' (CFSG.Assembly.oddCore G))) :
    oddCoreIn (normalizer (U : Set G)) ≤ CFSG.Assembly.oddCore G := by
  set O := CFSG.Assembly.oddCore G with hOdef
  set N := normalizer (U : Set G) with hNdef
  set X := oddCoreIn N with hXdef
  have hXN : X ≤ N := map_subtype_le _
  have hXodd : Odd (Nat.card X) := by
    rw [hXdef, oddCoreIn, card_map_of_injective N.subtype_injective]
    exact odd_card_oddCore N
  have hNX : N ≤ normalizer (X : Set G) := by
    rw [← normal_subgroupOf_iff_le_normalizer hXN]
    have : X.subgroupOf N = CFSG.Assembly.oddCore N :=
      comap_map_eq_self_of_injective N.subtype_injective _
    rw [this]
    infer_instance
  set Ubar := U.map (QuotientGroup.mk' O)
  set Xbar := X.map (QuotientGroup.mk' O)
  have hXbar : Odd (Nat.card Xbar) := Odd.of_dvd_nat hXodd (Subgroup.card_map_dvd X _)
  have hUbar : IsPGroup 2 Ubar := hU.map _
  have hUbarP : Ubar ≤ CFSG.pCore 2 (G ⧸ O) := map_le_iff_le_comap.mpr hUO
  have hXbarN : Xbar ≤ normalizer (Ubar : Set (G ⧸ O)) :=
    (map_mono hXN).trans (le_normalizer_map _)
  have hNbarX : normalizer (Ubar : Set (G ⧸ O)) ≤ normalizer (Xbar : Set (G ⧸ O)) :=
    (normalizer_map_le_map_normalizer (odd_card_oddCore G) hU).trans
      ((map_mono hNX).trans (le_normalizer_map _))
  have hbot := eq_bot_of_oddCore_eq_bot oddCore_quotient_oddCore_eq_bot hUbar hUbarP hXbar
    hXbarN hNbarX
  intro x hx
  have hxbar : QuotientGroup.mk' O x ∈ Xbar := ⟨x, hx, rfl⟩
  rw [hbot, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hxbar
  exact hxbar

theorem oddCore_map_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) : (CFSG.Assembly.oddCore X).map e.toMonoidHom = CFSG.Assembly.oddCore Y := by
  apply le_antisymm
  · exact le_oddCore ((inferInstance : (CFSG.Assembly.oddCore X).Normal).map _ e.surjective)
      (by rw [card_map_of_injective e.injective]; exact odd_card_oddCore X)
  · have hle : (CFSG.Assembly.oddCore Y).map e.symm.toMonoidHom ≤ CFSG.Assembly.oddCore X :=
      le_oddCore ((inferInstance : (CFSG.Assembly.oddCore Y).Normal).map _ e.symm.surjective)
        (by rw [card_map_of_injective e.symm.injective]; exact odd_card_oddCore Y)
    intro y hy
    exact ⟨e.symm y, hle ⟨y, hy, rfl⟩, by simp⟩

theorem map_subtype_oddCoreIn [Finite G] (Y : Subgroup G) (K : Subgroup Y) :
    (oddCoreIn K).map Y.subtype = oddCoreIn (K.map Y.subtype) := by
  set e : K ≃* K.map Y.subtype := K.equivMapOfInjective Y.subtype Y.subtype_injective
  rw [oddCoreIn, oddCoreIn, Subgroup.map_map, ← oddCore_map_mulEquiv e, Subgroup.map_map]
  congr 1

theorem lemma29_subgroup [Finite G] {Y U : Subgroup G} (hUY : U ≤ Y) (hU : IsPGroup 2 U)
    (hUO : U.subgroupOf Y ≤ (CFSG.pCore 2 (Y ⧸ CFSG.Assembly.oddCore Y)).comap
      (QuotientGroup.mk' (CFSG.Assembly.oddCore Y))) :
    oddCoreIn (Y ⊓ normalizer (U : Set G)) ≤ oddCoreIn Y := by
  have h := lemma29 (G := Y) (hU.comap_subtype) hUO
  have hN : (normalizer ((U.subgroupOf Y : Subgroup Y) : Set Y)).map Y.subtype =
      Y ⊓ normalizer (U : Set G) := by
    rw [← subgroupOf_normalizer_eq hUY, subgroupOf_map_subtype, inf_comm]
  rw [← hN, ← map_subtype_oddCoreIn]
  exact map_mono h

end CFSG.ComponentClassification.Asc76.L26
