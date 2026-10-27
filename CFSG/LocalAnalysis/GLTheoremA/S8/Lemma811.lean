module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Close
public import CFSG.LocalAnalysis.GLTheoremA.Lemma48
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement Pointwise

namespace S8

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem co2_odd_core (hc : S8Ctx G 3) (hrk : GLATwoLocalRank 3 G = 4) {x : G} (hx : orderOf x = 3)
    {L : Subgroup G} (hL : GLAPComponent 3 (cx x) L) (hZ : Nat.card (Subgroup.center (PQuot 3 L)) = 1)
    {E : Subgroup G} (hEL : E ≤ L) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 4) :
    Odd (Nat.card (GLAPPrimeCoreOf 3 (cx x))) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hEx : E ≤ cx x := hEL.trans hL.1
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hxL : x ∉ E := by
    intro hxE
    have hxL : x ∈ L := hEL hxE
    have hcen : (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : PQuot 3 L) ∈ Subgroup.center (PQuot 3 L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hL.1 g'.2))
    have hbot : Subgroup.center (PQuot 3 L) = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ
    rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcen
    have hO : x ∈ GLAPPrimeCoreOf 3 L := ⟨⟨x, hxL⟩, hcen, rfl⟩
    have hcop := CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hp3 L
    have h3 : 3 ∣ Nat.card (GLAPPrimeCoreOf 3 L) := by
      have := orderOf_dvd_natCard (⟨x, hO⟩ : ↥(GLAPPrimeCoreOf 3 L))
      rwa [Subgroup.orderOf_mk, hx] at this
    exact absurd (Nat.Coprime.eq_one_of_dvd hcop h3) (by norm_num)
  have hxcx : x ∈ cx x := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hE5 : IsElemAbelian 3 (E ⊔ Subgroup.zpowers x) :=
    isElemAbelian_sup_zpowers hE (fun e he => Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_singleton_iff.1 (hEx he) : e * x = x * e)) hx3
  have hlt : E < E ⊔ Subgroup.zpowers x :=
    lt_of_le_of_ne le_sup_left (fun h => hxL (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))
  have hcardlt : Nat.card E < Nat.card (E ⊔ Subgroup.zpowers x : Subgroup G) :=
    Subgroup.card_lt_of_lt hlt
  obtain ⟨B, hB⟩ := exists_glaIsBmax (by norm_num : 1 < 3) (by rw [hrk]; norm_num)
  have hBc : Nat.card B = 3 ^ 4 := by rw [hB.2.1, hrk]
  exact odd_core_of_big_rank hp3 hB (sup_le hEx (Subgroup.zpowers_le.2 hxcx)) hE5
    (by rw [hBc, ← hEc]; exact hcardlt)

theorem mem_core_iff {L : Subgroup G} (x : ↥L) :
    x ∈ GLAPPrimeCore p ↥L ↔ (x : G) ∈ GLAPPrimeCoreOf p L :=
  (Subgroup.mem_map_iff_mem (f := L.subtype) L.subtype_injective).symm

theorem mk_mem_center_of_forall {L : Subgroup G} {l : G} (hl : l ∈ L)
    (hcen : ∀ y ∈ L, ⁅y, l⁆ ∈ GLAPPrimeCoreOf p L) :
    (QuotientGroup.mk ⟨l, hl⟩ : PQuot p L) ∈ Subgroup.center (PQuot p L) := by
  rw [Subgroup.mem_center_iff]
  intro w
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_core_iff]
  have h1 := hcen ((y : G)⁻¹) (L.inv_mem y.2)
  have hlp : l⁻¹ ∈ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) :=
    normalizer_le_normalizer_glaPPrimeCoreOf p L (Subgroup.le_normalizer (L.inv_mem hl))
  have h2 := (Subgroup.mem_normalizer_iff.1 hlp _).1 h1
  have h3 : (((y * ⟨l, hl⟩)⁻¹ * (⟨l, hl⟩ * y) : ↥L) : G) =
      l⁻¹ * ⁅(y : G)⁻¹, l⁆ * (l⁻¹)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, mul_inv_rev, inv_inv]
    group
  rw [h3]
  exact h2

theorem card_map_mk_of_coprime {Z : Type*} [Group Z] [Finite Z] (hp : p.Prime) {K : Subgroup Z}
    (hK : IsPGroup p K) (N : Subgroup Z) [N.Normal] (hN : ¬ p ∣ Nat.card N) :
    Nat.card (K.map (QuotientGroup.mk' N)) = Nat.card K := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hK.exists_card_eq
  have hdisj : Disjoint K N := Subgroup.disjoint_of_coprime_natCard (by
    rw [hk]; exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hN))
  have hinj : Function.Injective ((QuotientGroup.mk' N).subgroupMap K) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : (QuotientGroup.mk' N) (x : Z) = 1 := congrArg Subtype.val hx
    have h2 : (x : Z) ∈ N := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    have h3 : (x : Z) ∈ K ⊓ N := ⟨x.2, h2⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at h3
    exact Subgroup.mem_bot.2 (Subtype.ext h3)
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, MonoidHom.subgroupMap_surjective _ K⟩)).symm

theorem exists_elemAbelian_lift_prod (hp : p.Prime) {L E A : Subgroup G}
    (hEL : E ≤ L) (hE : IsElemAbelian p E) (hA : IsElemAbelian p A)
    (hAcm : ∀ a ∈ A, CentMod p L a) (hZ : Subgroup.center (PQuot p L) = ⊥) :
    ∃ S : Subgroup G, S ≤ E ⊔ A ⊔ GLAPPrimeCoreOf p L ∧ IsElemAbelian p S ∧
      Nat.card S = Nat.card E * Nat.card A := by
  haveI : Fact p.Prime := ⟨hp⟩
  set O := GLAPPrimeCoreOf p L with hO
  have hOp : ¬ p ∣ Nat.card O := not_dvd_card_glaPPrimeCoreOf hp L
  have hNO : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (O : Set G) :=
    normalizer_le_normalizer_glaPPrimeCoreOf p L
  have hEN : E ≤ Subgroup.normalizer (O : Set G) := fun e he => hNO (Subgroup.le_normalizer (hEL he))
  have hAN : A ≤ Subgroup.normalizer (O : Set G) := fun a ha => hNO (hAcm a ha).1
  set M := Subgroup.normalizer (O : Set G) with hM
  haveI hNn : (O.subgroupOf M).Normal := Subgroup.normal_in_normalizer
  have hOM : Nat.card (O.subgroupOf M) = Nat.card O :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv
  have hN : ¬ p ∣ Nat.card (O.subgroupOf M) := by rw [hOM]; exact hOp
  set Eh : Subgroup ↥M := E.subgroupOf M with hEh
  set Ah : Subgroup ↥M := A.subgroupOf M with hAh
  set mk : ↥M →* ↥M ⧸ O.subgroupOf M := QuotientGroup.mk' (O.subgroupOf M) with hmk
  have hEhel : IsElemAbelian p Eh := hE.subgroupOf M
  have hAhel : IsElemAbelian p Ah := hA.subgroupOf M
  have hEbar : IsElemAbelian p (Eh.map mk) := hEhel.map mk
  have hAbar : IsElemAbelian p (Ah.map mk) := hAhel.map mk
  have hcomm : ∀ a ∈ Eh.map mk, ∀ b ∈ Ah.map mk, a * b = b * a := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, hmk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have he' : (e : G) ∈ E := Subgroup.mem_subgroupOf.1 he
    have ha' : (a : G) ∈ A := Subgroup.mem_subgroupOf.1 ha
    have h1 := (centMod_iff.1 (centMod_inv (hAcm a ha'))).2 (e : G)⁻¹ (L.inv_mem (hEL he'))
    have h2 := Subgroup.inv_mem _ h1
    rw [Subgroup.mem_subgroupOf]
    have h3 : (((e * a)⁻¹ * (a * e) : ↥M) : G) = ⁅(a : G)⁻¹, (e : G)⁻¹⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, mul_inv_rev, inv_inv]
      group
    rw [h3]
    have h4 : ⁅(a : G)⁻¹, (e : G)⁻¹⁆ = (⁅(e : G)⁻¹, (a : G)⁻¹⁆)⁻¹ := by
      rw [commutatorElement_inv]
    rw [h4]
    exact h2
  set Eb : Subgroup (↥M ⧸ O.subgroupOf M) := Eh.map mk ⊔ Ah.map mk with hEb
  have hEbel : IsElemAbelian p Eb := IsElemAbelian.sup_of_commute hEbar hAbar hcomm
  have hcardE : Nat.card (Eh.map mk) = Nat.card E := by
    rw [hmk, card_map_mk_of_coprime hp hEhel.isPGroup _ hN]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv
  have hcardA : Nat.card (Ah.map mk) = Nat.card A := by
    rw [hmk, card_map_mk_of_coprime hp hAhel.isPGroup _ hN]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
  have hOE : Disjoint E O := by
    obtain ⟨k, hk⟩ := hE.isPGroup.exists_card_eq
    exact Subgroup.disjoint_of_coprime_natCard (by
      rw [hk]; exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hOp))
  have hinf : Eh.map mk ⊓ Ah.map mk = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨e, he, rfl⟩, ⟨a, ha, hae⟩⟩
    have he' : (e : G) ∈ E := Subgroup.mem_subgroupOf.1 he
    have ha' : (a : G) ∈ A := Subgroup.mem_subgroupOf.1 ha
    have hae' : (QuotientGroup.mk a : ↥M ⧸ O.subgroupOf M) = QuotientGroup.mk e := hae
    have hao : (a : G)⁻¹ * (e : G) ∈ O := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hae')
    have he_eq : (e : G) = (a : G) * ((a : G)⁻¹ * (e : G)) := by group
    have hcen : ∀ y ∈ L, ⁅y, (e : G)⁆ ∈ O := by
      intro y hy
      have h1 := (centMod_iff.1 (hAcm a ha')).2 y hy
      have hyN : y ∈ Subgroup.normalizer (O : Set G) := hNO (Subgroup.le_normalizer hy)
      have h2 : ⁅y, (a : G)⁻¹ * (e : G)⁆ ∈ O := by
        have h3 := (Subgroup.mem_normalizer_iff.1 hyN _).1 hao
        have h4 := O.mul_mem h3 (O.inv_mem hao)
        simpa [commutatorElement_def, mul_assoc] using h4
      rw [he_eq, commutatorElement_mul_right]
      exact O.mul_mem h1 ((Subgroup.mem_normalizer_iff.1 (hAN ha') _).1 h2)
    have hmem := mk_mem_center_of_forall (p := p) (hEL he') hcen
    rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff, mem_core_iff] at hmem
    have h5 : (e : G) ∈ E ⊓ O := ⟨he', hmem⟩
    rw [hOE.eq_bot, Subgroup.mem_bot] at h5
    have h6 : e = 1 := Subtype.ext h5
    rw [Subgroup.mem_bot, h6, map_one]
  have hnorm : Ah.map mk ≤ Subgroup.normalizer ((Eh.map mk : Subgroup (↥M ⧸ O.subgroupOf M)) : Set _) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact hcomm h hh b hb
  have hcardEb : Nat.card Eb = Nat.card E * Nat.card A := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer hnorm
    rw [hinf, Subgroup.card_bot, mul_one, hcardE, hcardA] at h1
    exact h1
  obtain ⟨S₀, hS₀el, hS₀map, hS₀card⟩ := exists_elemAbelian_lift (O.subgroupOf M) hN hEbel
  refine ⟨S₀.map M.subtype, ?_, hS₀el.map M.subtype, ?_⟩
  · have h1 : S₀ ≤ Eh ⊔ Ah ⊔ O.subgroupOf M := by
      have h2 : S₀ ≤ Subgroup.comap mk Eb := by
        rw [hmk, ← hS₀map]
        exact Subgroup.le_comap_map _ _
      have h3 : Eb = (Eh ⊔ Ah).map mk := by rw [hEb, Subgroup.map_sup]
      rw [h3, Subgroup.comap_map_eq, hmk, QuotientGroup.ker_mk'] at h2
      exact h2
    calc S₀.map M.subtype ≤ (Eh ⊔ Ah ⊔ O.subgroupOf M).map M.subtype := Subgroup.map_mono h1
      _ = E ⊔ A ⊔ O := by
        rw [Subgroup.map_sup, Subgroup.map_sup, hEh, hAh, Subgroup.subgroupOf_map_subtype,
          Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hEN,
          inf_eq_left.2 hAN, inf_eq_left.2 Subgroup.le_normalizer]
  · rw [Subgroup.card_map_of_injective M.subtype_injective, hS₀card, hcardEb]

theorem card_mul_le_pow_of_lift (hp : p.Prime) (hp2 : p ≠ 2) {L E V A : Subgroup G}
    (hEL : E ≤ L) (hE : IsElemAbelian p E) (hVL : V ≤ L) (hV2 : IsPGroup 2 V)
    (hVO : ¬ V ≤ GLAPPrimeCoreOf p L) (hEV : E ≤ Subgroup.normalizer (V : Set G))
    (hA : IsElemAbelian p A) (hAcm : ∀ a ∈ A, CentMod p L a)
    (hZ : Subgroup.center (PQuot p L) = ⊥) :
    Nat.card E * Nat.card A ≤ p ^ GLATwoLocalRank p G := by
  obtain ⟨S, hSle, hSel, hScard⟩ := exists_elemAbelian_lift_prod hp hEL hE hA hAcm hZ
  set O := GLAPPrimeCoreOf p L with hO
  have hOp : ¬ p ∣ Nat.card O := not_dvd_card_glaPPrimeCoreOf hp L
  have hNO : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (O : Set G) :=
    normalizer_le_normalizer_glaPPrimeCoreOf p L
  have hEN : E ≤ Subgroup.normalizer (O : Set G) := fun e he => hNO (Subgroup.le_normalizer (hEL he))
  have hVN : V ≤ Subgroup.normalizer (O : Set G) := fun v hv => hNO (Subgroup.le_normalizer (hVL hv))
  have hAN : A ≤ Subgroup.normalizer (O : Set G) := fun a ha => hNO (hAcm a ha).1
  set W : Subgroup G := V ⊔ O with hW
  have hEW : E ≤ Subgroup.normalizer (W : Set G) := le_normalizer_sup hEV hEN
  have hOW : O ≤ Subgroup.normalizer (W : Set G) := le_sup_right.trans Subgroup.le_normalizer
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := by
    have key : ∀ a ∈ A, ∀ y ∈ W, a * y * a⁻¹ ∈ W := by
      intro a ha y hy
      have hy' : y ∈ ((V : Set G) * (O : Set G)) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right V O hVN]
        exact hy
      obtain ⟨v, hv, o, ho, rfl⟩ := Set.mem_mul.1 hy'
      have h1 : ⁅a, v⁆ ∈ O := by
        have := (centMod_iff.1 (hAcm a ha)).2 v (hVL hv)
        have h2 := Subgroup.inv_mem _ this
        rwa [commutatorElement_inv] at h2
      have h3 : a * o * a⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 (hAN ha) o).1 ho
      have h4 : a * (v * o) * a⁻¹ = ⁅a, v⁆ * v * (a * o * a⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [h4]
      exact W.mul_mem (W.mul_mem (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hv))
        (Subgroup.mem_sup_right h3)
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => key a ha y hy, fun hy => ?_⟩
    have h5 := key a⁻¹ (A.inv_mem ha) _ hy
    have e : a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = y := by group
    rwa [e] at h5
  have hSW : S ≤ Subgroup.normalizer (W : Set G) := hSle.trans (sup_le (sup_le hEW hAW) hOW)
  have hVp : ¬ p ∣ Nat.card V := by
    obtain ⟨k, hk⟩ := hV2.exists_card_eq
    rw [hk]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  have hWcop : Nat.Coprime p (Nat.card W) := by
    rw [hW, sup_comm]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2
      (not_dvd_card_sup_of_le_normalizer hp hVN hOp hVp)
  have hVne : V ≠ ⊥ := by
    rintro rfl
    exact hVO bot_le
  have h2W : 2 ∣ Nat.card W := by
    obtain ⟨k, hk⟩ := hV2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hVne (Subgroup.eq_bot_of_card_eq _ (by simpa using hk))
    exact (dvd_pow_self 2 hk0).trans (hk ▸ Subgroup.card_dvd_of_le (le_sup_left : V ≤ W))
  obtain ⟨T, -, hT2, hTne, hST, -⟩ := S3.exists_invariant_sylow hp Nat.prime_two
    hSel.isPGroup hSW hWcop h2W
  have h6 := card_le_pow_glaTwoLocalRank hp hSel hTne hT2 hST
  rwa [hScard] at h6

theorem co2_rank_one (hc : S8Ctx G 3) (hrk : GLATwoLocalRank 3 G = 4) {x : G} {L : Subgroup G}
    (hL : GLAPComponent 3 (cx x) L) (hZ : Nat.card (Subgroup.center (PQuot 3 L)) = 1)
    {E V : Subgroup G} (hEL : E ≤ L) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 3) (hVL : V ≤ L)
    (hV2 : IsPGroup 2 V) (hVO : ¬ V ≤ GLAPPrimeCoreOf 3 L) (hEV : E ≤ Subgroup.normalizer (V : Set G)) :
    ∀ A : Subgroup G, IsElemAbelian 3 A → A ≤ cx x → (∀ a ∈ A, CentMod 3 L a) → Nat.card A ≤ 3 := by
  intro A hA _ hAcm
  have hZ' : Subgroup.center (PQuot 3 L) = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ
  have h := card_mul_le_pow_of_lift Nat.prime_three (by norm_num) hEL hE hVL hV2 hVO hEV hA hAcm hZ'
  rw [hrk, hEc] at h
  omega

theorem lemma811 (hc : S8Ctx G 3) (hin : Inputs8910 G 3) (h301 : I301AAt G 3) (h1016 : I1016Co2At G)
    (hrk : GLATwoLocalRank 3 G = 4) {x : G} (hx : orderOf x = 3) {L : Subgroup G}
    (hL : GLAPComponent 3 (cx x) L) :
    ¬ catalogIs (PSimple 3 L) fun i => i = .sporadic .Co2 := by
  intro hco2
  have hx1 : x ≠ 1 := by
    intro h
    rw [h] at hx
    simp at hx
  have hKC : CFSG.Open.IsKGroup ↥(cx x) := isKGroup_cx hc.ctx hx1
  obtain ⟨hZ, ⟨E4, hE4L, hE4, hE4c⟩, ⟨E3, V, hE3L, hE3, hE3c, hVL, hV2, hVO, hEV⟩⟩ :=
    h1016 (cx x) L hKC hL hco2
  have hrow : RowL .co2 3 L := ⟨rfl, hco2, hZ⟩
  have hodd := co2_odd_core hc hrk hx hL hZ hE4L hE4 hE4c
  have hrk1 := co2_rank_one hc hrk hL hZ hE3L hE3 hE3c hVL hV2 hVO hEV
  obtain ⟨c⟩ := h301 x L .co2 hx1 hx hL hKC hrow hodd hrk1 (by rw [hrk]; exact le_refl _)
  exact cfg_three hc hin hx hL hrow hodd c

end S8

end CFSG.LocalAnalysis.GLTheoremA
