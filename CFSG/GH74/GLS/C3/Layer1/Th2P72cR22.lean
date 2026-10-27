module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR21
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR13
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR16
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR6

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.C3.Layer1.PumpRigid
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isSimple_of_u2 {X : Type} [Group X]
    (hu : Nonempty (X ≃* alternatingGroup (Fin 7)) ∨ HasL2Model X Odd) : IsSimpleGroup X := by
  rcases hu with ⟨⟨eA⟩⟩ | hL2
  · exact (eA.isSimpleGroup_congr).2 (alternatingGroup.isSimpleGroup (by simp))
  · obtain ⟨F, _, _, hF, -, ⟨eF⟩⟩ := IVK.exists_l2Field_of_hasL2Model_pred (fun q hq => hq) hL2
    exact IVK.Proofs2.isSimpleGroup_of_l2 hF eF

theorem le_pPrimeCore_of_normalized {L : Type*} [Group L] [Finite L]
    (hs : IsSimpleGroup (L ⧸ pPrimeCore 2 L)) (hperf : Group.IsPerfect L) (Λ Y : Subgroup L)
    (hY : Odd (Nat.card Y)) (hcov : ∀ k : L, ∃ l ∈ Λ, ∃ o ∈ pPrimeCore 2 L, k = l * o)
    (hnorm : ∀ l ∈ Λ, ∀ y ∈ Y, l * y * l⁻¹ ∈ Y) : Y ≤ pPrimeCore 2 L := by
  classical
  set π : L →* L ⧸ pPrimeCore 2 L := QuotientGroup.mk' (pPrimeCore 2 L) with hπ
  have hnormal : (Y.map π).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hn
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨l, hl, o, ho, rfl⟩ := hcov k
    refine ⟨l * y * l⁻¹, hnorm l hl y hy, ?_⟩
    have ho1 : π o = 1 := (QuotientGroup.eq_one_iff o).2 ho
    have : (QuotientGroup.mk (l * o) : L ⧸ pPrimeCore 2 L) = π l := by
      show π (l * o) = π l
      rw [map_mul, ho1, mul_one]
    rw [this]
    simp [map_mul]
  have hodd : Odd (Nat.card (Y.map π)) :=
    Odd.of_dvd_nat hY (Subgroup.card_dvd_of_surjective (f := π.subgroupMap Y) (π.subgroupMap_surjective Y))
  rcases hs.eq_bot_or_eq_top_of_normal (Y.map π) with h | h
  · intro y hy
    have : π y ∈ Y.map π := ⟨y, hy, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff y).1 this
  · exfalso
    rw [h, Subgroup.card_top] at hodd
    have hnt : Nontrivial (L ⧸ pPrimeCore 2 L) := hs.toNontrivial
    have hP : Group.IsPerfect (L ⧸ pPrimeCore 2 L) :=
      Group.IsPerfect.ofSurjective (f := π) (QuotientGroup.mk'_surjective _)
    have hsolv : Group.IsSolvable (L ⧸ pPrimeCore 2 L) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    exact Group.IsPerfect.not_isSolvable (L ⧸ pPrimeCore 2 L) hsolv

theorem le_cSec_of_mem_cSec {u t : G} {L : Subgroup G}
    (hL : IsPCompIn 2 (centralizer ({u} : Set G)) L) (ht2 : orderOf t = 2)
    (hLN : ∀ g ∈ centralizer ({u} : Set G), g ∈ normalizer (L : Set G))
    (hsimple : IsSimpleGroup (kBar L))
    (htL : t ∈ centralizerSection L (pPrimeCoreOf 2 L)) :
    pPrimeCoreOf 2 (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G) ≤
      centralizerSection L (pPrimeCoreOf 2 L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Λ, hΛ⟩ := exists_isLam ht2 hL htL
  rintro a ⟨haO, haC⟩
  have haN : a ∈ normalizer (L : Set G) := hLN a haC
  set O : Subgroup G := pPrimeCoreOf 2 L with hO
  have haNO : a ∈ normalizer (O : Set G) := TwoThin.mem_normalizer_pPrimeCoreOf haN
  have hY₁ : L ⊓ pPrimeCoreOf 2 (centralizer ({t} : Set G)) ≤ O := by
    set Y₁ : Subgroup G := L ⊓ pPrimeCoreOf 2 (centralizer ({t} : Set G)) with hY₁def
    have hperf : Group.IsPerfect ↥L :=
      Subgroup.isPerfect_iff.mpr (C3.Layer1.Bk.perfect_of_isPCompIn hL)
    have hYodd : Odd (Nat.card ↥(Y₁.subgroupOf L)) := by
      have h1 : Nat.card ↥(Y₁.subgroupOf L) = Nat.card ↥Y₁ :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Y₁ ≤ L)).toEquiv
      rw [h1]
      exact Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd (centralizer ({t} : Set G)))
        (Subgroup.card_dvd_of_le inf_le_right)
    have hcov : ∀ k : ↥L, ∃ l ∈ Λ.subgroupOf L, ∃ o ∈ pPrimeCore 2 ↥L, k = l * o := by
      intro k
      obtain ⟨l, hl, o, ho, hk⟩ := hΛ.cover k.1 k.2
      have hlL : l ∈ L := (hΛ.le hl).1
      have hoL : o ∈ L := TwoThin.pPrimeCoreOf_le L ho
      obtain ⟨hoJ', hoc⟩ := C3.Layer1.Back.Setup91.mem_pPrimeCoreOf_iff.1 ho
      refine ⟨⟨l, hlL⟩, Subgroup.mem_subgroupOf.2 hl, ⟨o, hoL⟩, hoc, Subtype.ext hk⟩
    have hnorm : ∀ l ∈ Λ.subgroupOf L, ∀ y ∈ Y₁.subgroupOf L, l * y * l⁻¹ ∈ Y₁.subgroupOf L := by
      intro l hl y hy
      have hlΛ : (l : G) ∈ Λ := Subgroup.mem_subgroupOf.1 hl
      have hyY : (y : G) ∈ Y₁ := Subgroup.mem_subgroupOf.1 hy
      have hlC : (l : G) ∈ centralizer ({t} : Set G) := (hΛ.le hlΛ).2
      rw [Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      refine ⟨L.mul_mem (L.mul_mem l.2 y.2) (L.inv_mem l.2), ?_⟩
      have hnC : (l : G) ∈ normalizer (pPrimeCoreOf 2 (centralizer ({t} : Set G)) : Set G) :=
        TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hlC)
      exact (Subgroup.mem_normalizer_iff.1 hnC (y : G)).1 hyY.2
    have hle := le_pPrimeCore_of_normalized hsimple hperf _ _ hYodd hcov hnorm
    intro g hg
    have hgL : g ∈ L := hg.1
    have : (⟨g, hgL⟩ : ↥L) ∈ pPrimeCore 2 ↥L := hle (Subgroup.mem_subgroupOf.2 hg)
    exact C3.Layer1.Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨hgL, this⟩
  have hcomm : ∀ l ∈ Λ, ⁅l, a⁆ ∈ O := by
    intro l hl
    have hlL : l ∈ L := (hΛ.le hl).1
    have hlC : l ∈ centralizer ({t} : Set G) := (hΛ.le hl).2
    refine hY₁ ⟨?_, ?_⟩
    · have h1 : a * l⁻¹ * a⁻¹ ∈ L := by
        have := (Subgroup.mem_normalizer_iff.1 haN l⁻¹).1 (L.inv_mem hlL)
        simpa using this
      have : ⁅l, a⁆ = l * (a * l⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
      rw [this]
      exact L.mul_mem hlL h1
    · have hnC : l ∈ normalizer (pPrimeCoreOf 2 (centralizer ({t} : Set G)) : Set G) :=
        TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hlC)
      have h1 : l * a * l⁻¹ ∈ pPrimeCoreOf 2 (centralizer ({t} : Set G)) :=
        (Subgroup.mem_normalizer_iff.1 hnC a).1 haO
      have : ⁅l, a⁆ = (l * a * l⁻¹) * a⁻¹ := by simp only [commutatorElement_def]
      rw [this]
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ haO)
  refine ⟨haN, haNO, fun k hk => ?_⟩
  obtain ⟨l, hl, o, ho, rfl⟩ := hΛ.cover k hk
  have hlL : l ∈ L := (hΛ.le hl).1
  have hlNO : l ∈ normalizer (O : Set G) := TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hlL)
  have h1 : ⁅o, a⁆ ∈ O := by
    have h2 : a * o⁻¹ * a⁻¹ ∈ O := by
      have := (Subgroup.mem_normalizer_iff.1 haNO o⁻¹).1 (O.inv_mem ho)
      simpa using this
    have : ⁅o, a⁆ = o * (a * o⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact O.mul_mem ho h2
  have h3 : ⁅l * o, a⁆ = l * ⁅o, a⁆ * l⁻¹ * ⁅l, a⁆ := by simp only [commutatorElement_def]; group
  rw [h3]
  exact O.mul_mem ((Subgroup.mem_normalizer_iff.1 hlNO ⁅o, a⁆).1 h1) (hcomm l hl)

theorem row2_exists_a {t z : G} {A J : Subgroup G}
    (hJc : IsPCompIn 2 (centralizer ({t} : Set G)) J) (hnqs : ¬ CFSG.IsQuasisimple ↥J)
    (hsimple : IsSimpleGroup (kBar J)) (hAel : CFSG.IsElementaryAbelian 2 ↥A)
    (hA3 : pRank 2 ↥A = 3) (hAN : A ≤ normalizer (J : Set G)) (hzA : z ∈ A)
    (hz2 : orderOf z = 2) (hzJ : z ∈ J) :
    ∃ (V : Subgroup G) (a : G), V ≤ A ∧ pRank 2 ↥V = 2 ∧ a ∈ pPrimeCoreOf 2 J ∧
      Odd (orderOf a) ∧ (∀ v ∈ V, v * a = a * v) ∧ z * a * z⁻¹ = a⁻¹ ∧ a ≠ 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect ↥J :=
    Subgroup.isPerfect_iff.mpr (C3.Layer1.Bk.perfect_of_isPCompIn hJc)
  have hOodd : Odd (Nat.card ↥(pPrimeCoreOf 2 J)) := TwoThin.card_pPrimeCoreOf_odd J
  have hzO : z ∉ pPrimeCoreOf 2 J := by
    intro hzO
    have : Odd (orderOf z) := Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard _ hzO)
    rw [hz2] at this
    exact absurd this (by decide)
  obtain ⟨p, hp, hp2, w, hw, hzw⟩ := exists_prime_noncentral hperf hsimple hnqs hzJ hzO
  have : Fact p.Prime := ⟨hp⟩
  have hPodd : ¬ 2 ∣ Nat.card ↥(Pp J p) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (Pp_isPGroup J p)
    rw [hn]
    intro h2
    have h2' : 2 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2').symm
  have hAN' : A ≤ normalizer (Pp J p : Set G) := fun g hg => mem_normalizer_Pp (hAN hg)
  obtain ⟨V, a, hVA, hV2, haP, hVa, hza, ha1⟩ :=
    exists_inverted_element hAel hA3 hPodd hAN' hzA ⟨w, hw, hzw⟩
  have haO : a ∈ pPrimeCoreOf 2 J := Pp_le_O J p haP
  exact ⟨V, a, hVA, hV2, haO, Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard _ haO), hVa, hza,
    ha1⟩

theorem row2_exists_vL (hG : C3Hyp G) (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2)
    {B A V : Subgroup G} {t z a : G} {J : Subgroup G}
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hVA : V ≤ A) (hAB : A ≤ B) (hV2 : pRank 2 ↥V = 2)
    (h7B2 : ∀ W : Subgroup G, IsE 2 B W → ⁅AG W, B⁆ = ⊥)
    (htB : t ∈ B) (ht2 : orderOf t = 2) (hJc : IsPCompIn 2 (centralizer ({t} : Set G)) J)
    (hzA : z ∈ A) (haJ : a ∈ pPrimeCoreOf 2 J) (haodd : Odd (orderOf a))
    (haV : ∀ v ∈ V, v * a = a * v) (hza : z * a * z⁻¹ = a⁻¹) (ha1 : a ≠ 1) :
    ∃ (v : G) (L : Subgroup G), v ∈ V ∧ v ≠ 1 ∧ orderOf v = 2 ∧
      IsPCompIn 2 (centralizer ({v} : Set G)) L ∧ IsUnbalancingTriple v t L ∧
      z ∈ normalizer (L : Set G) ∧ z * v = v * z ∧ v ≠ z ∧
      z ∉ centralizerSection L (pPrimeCoreOf 2 L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  have hVel : CFSG.IsElementaryAbelian 2 ↥V := isElementaryAbelian_le hBel (hVA.trans hAB)
  have hE2 : IsE 2 B V := ⟨hVA.trans hAB, hVel, le_of_eq hV2.symm⟩
  have hAGV := h7B2 V hE2
  have hzB : z ∈ B := hAB hzA
  have hex : ∃ v ∈ V, v ≠ 1 ∧
      ¬ Subgroup.zpowers a ≤ pPrimeCoreOf 2 (centralizer ({v} : Set G)) := by
    by_contra hno
    push Not at hno
    have haAG : a ∈ AG V := by
      simp only [AG, Subgroup.mem_iInf]
      intro b hb
      exact hno b hb.1 hb.2 (Subgroup.mem_zpowers a)
    have h1 : ⁅a, z⁆ ∈ ⁅AG V, B⁆ := Subgroup.commutator_mem_commutator haAG hzB
    rw [hAGV, Subgroup.mem_bot] at h1
    have hcomm : a * z = z * a := commutatorElement_eq_one_iff_mul_comm.1 h1
    have h2 : a * a = 1 := by
      have e1 : z * a * z⁻¹ = a := by rw [← hcomm]; group
      rw [e1] at hza
      calc a * a = a * a⁻¹ := by rw [← hza]
        _ = 1 := mul_inv_cancel a
    have h3 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h2)
    have h4 : orderOf a = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.coprime_two_right.2 haodd) h3
    exact ha1 (orderOf_eq_one_iff.1 h4)
  obtain ⟨v, hvV, hv1, hvnot⟩ := hex
  have hvB : v ∈ B := hAB (hVA hvV)
  have hv2 : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hBsq v hvB) hv1
  have hut : v * t = t * v := hBc v hvB t htB
  have hZt : Subgroup.zpowers a ≤ pPrimeCoreOf 2 (centralizer ({t} : Set G)) :=
    Subgroup.zpowers_le.2 (pPrimeCoreOf_le_of_isPCompIn hJc haJ)
  have hZu : Subgroup.zpowers a ≤ centralizer ({v} : Set G) :=
    Subgroup.zpowers_le.2 (mem_centralizer_singleton_iff.2 (haV v hvV).symm)
  obtain ⟨L, hL, htN, hZN, htnot, hZnot'⟩ := exists_pComponent_of_Z ht2 hut hZt hZu hvnot
  have htu : t ∈ centralizer ({v} : Set G) := mem_centralizer_singleton_iff.2 hut.symm
  have hunb : IsUnbalancingTriple v t L :=
    ⟨⟨hv2, hL⟩, ht2, htu, htN, fun hle => hZnot' (fun z hz => hle ⟨hZt hz, hZu hz⟩)⟩
  have hu := kBar_u2_of_unbal hG hL34 h102 hunb
  have hLN := centralizer_le_normalizer_of_u2 hG.pRank_eq_four.le hv2 hL hu
  have hzv : z * v = v * z := hBc z hzB v hvB
  have hzC : z ∈ centralizer ({v} : Set G) := mem_centralizer_singleton_iff.2 hzv
  have hzN := hLN z hzC
  have haC : a ∈ centralizer ({v} : Set G) := hZu (Subgroup.mem_zpowers a)
  have haN := hLN a haC
  have hvcS : v ∈ centralizerSection L (pPrimeCoreOf 2 L) := by
    have hvN : v ∈ normalizer (L : Set G) := hLN v (mem_centralizer_singleton_iff.2 rfl)
    refine ⟨hvN, TwoThin.mem_normalizer_pPrimeCoreOf hvN, fun k hk => ?_⟩
    have hkv : k * v = v * k := mem_centralizer_singleton_iff.1 (hL.1 hk)
    rw [commutatorElement_eq_one_iff_mul_comm.2 hkv]
    exact (pPrimeCoreOf 2 L).one_mem
  have hzL : z ∉ centralizerSection L (pPrimeCoreOf 2 L) := by
    intro hzL
    apply hZnot'
    have hbz : barAct L ⟨z, hzN⟩ = 1 := (barAct_eq_one_iff _).2 hzL
    have hconj : (⟨z, hzN⟩ : ↥(normalizer (L : Set G))) * ⟨a, haN⟩ * ⟨z, hzN⟩⁻¹ = ⟨a, haN⟩⁻¹ :=
      Subtype.ext (by simpa using hza)
    have hα : barAct L ⟨a, haN⟩ = (barAct L ⟨a, haN⟩)⁻¹ := by
      have := congrArg (barAct L) hconj
      rw [map_mul, map_mul, map_inv, map_inv, hbz] at this
      simpa using this
    have hα2 : barAct L ⟨a, haN⟩ ^ 2 = 1 := by
      rw [sq]
      calc barAct L ⟨a, haN⟩ * barAct L ⟨a, haN⟩
          = barAct L ⟨a, haN⟩ * (barAct L ⟨a, haN⟩)⁻¹ := by rw [← hα]
        _ = 1 := mul_inv_cancel _
    have hord : orderOf (barAct L ⟨a, haN⟩) ∣ 2 := orderOf_dvd_of_pow_eq_one hα2
    have hord' : orderOf (barAct L ⟨a, haN⟩) ∣ orderOf a := by
      have := orderOf_map_dvd (barAct L) (⟨a, haN⟩ : ↥(normalizer (L : Set G)))
      rwa [Subgroup.orderOf_mk] at this
    have h1 : orderOf (barAct L ⟨a, haN⟩) = 1 :=
      Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left hord' (Nat.coprime_two_right.2 haodd)) hord
    have h2 : barAct L ⟨a, haN⟩ = 1 := orderOf_eq_one_iff.1 h1
    exact Subgroup.zpowers_le.2 ((barAct_eq_one_iff _).1 h2)
  exact ⟨v, L, hvV, hv1, hv2, hL, hunb, hzN, hzv, fun hvz => hzL (hvz ▸ hvcS), hzL⟩

theorem row2_not_mem_E (hG : C3Hyp G) (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2)
    {x y : G} {K T S : Subgroup G} (hstd : Th2Std x y K T S) {B : Subgroup G}
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hxB : x ∈ B) {t v z : G} {L : Subgroup G}
    (htE : t ∈ B ⊓ (T ⊓ CxK x K)) (hvE : v ∈ B ⊓ (T ⊓ CxK x K)) (hv2 : orderOf v = 2)
    (ht2 : orderOf t = 2) (hz2 : orderOf z = 2) (hzK : z ∈ K) (hzB : z ∈ B)
    (hL : IsPCompIn 2 (centralizer ({v} : Set G)) L) (hunb : IsUnbalancingTriple v t L)
    (hzL : z ∉ centralizerSection L (pPrimeCoreOf 2 L)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  have hvB : v ∈ B := hvE.1
  have htB : t ∈ B := htE.1
  obtain ⟨M, hlt⟩ := HY.exists_pumpup_at hG hstd hvE.2.2 hv2
  obtain ⟨⟨eMK⟩, hMcen, hM2, hMN⟩ := hstd.pumpup_facts hG hL34 h102 hv2 hlt
  have hMc : IsPCompIn 2 (centralizer ({v} : Set G)) M := hlt.2.1.2.2
  have hxM : x ∈ normalizer (M : Set G) :=
    hMN x (mem_centralizer_singleton_iff.2 (hBc x hxB v hvB))
  have hzv : z * v = v * z := hBc z hzB v hvB
  have hz2' : ∃ n : ℕ, z ^ (2 ^ n) = 1 := ⟨1, by
    have := pow_orderOf_eq_one z
    rwa [hz2] at this⟩
  have hzM : z ∈ M := mem_pumpup_of_two_elt hlt hxM eMK hzK hzv hz2'
  have hML : M = L := by
    by_contra hne
    exact hzL (Stage1.Thm2.Recip.le_cSec_of_ne hMc hL hne hzM)
  obtain ⟨Θ, hΘ⟩ := exists_theta hlt hxM eMK
  have htv : t * v = v * t := hBc t htB v hvB
  have htN : t ∈ normalizer (M : Set G) := hMN t (mem_centralizer_singleton_iff.2 htv)
  have htcK : t ∈ centralizerSection K (pPrimeCoreOf 2 K) := htE.2.2.2
  have htK : t ∈ normalizer (K : Set G) := htcK.1
  have hbarK : barAct K ⟨t, htK⟩ = 1 := (barAct_eq_one_iff _).2 htcK
  have htM : t ∈ centralizerSection M (pPrimeCoreOf 2 M) := by
    rw [← barAct_eq_one_iff ⟨t, htN⟩]
    ext c
    have h1 := hΘ t htN htK htv c
    rw [hbarK] at h1
    simp only [MulAut.one_apply] at h1 ⊢
    exact Θ.injective h1
  rw [hML] at htM
  have hu := kBar_u2_of_unbal hG hL34 h102 hunb
  have hLN := centralizer_le_normalizer_of_u2 hG.pRank_eq_four.le hv2 hL hu
  have hsimple : IsSimpleGroup (kBar L) := isSimple_of_u2 hu
  exact hunb.2.2.2.2 (le_cSec_of_mem_cSec hL ht2 hLN hsimple htM)

theorem row2_triple (hG : C3Hyp G) (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2)
    {x y : G} {K T S : Subgroup G} (hstd : Th2Std x y K T S) {B : Subgroup G} {t : G}
    {J : Subgroup G} {ρ : Th2Row} (hpick : Th2Pick ρ x y K T S B t J)
    (hsimple : IsSimpleGroup (kBar J)) (hE2 : 2 ≤ pRank 2 ↥(B ⊓ (T ⊓ CxK x K)))
    (h7B2 : ∀ W : Subgroup G, IsE 2 B W → ⁅AG W, B⁆ = ⊥)
    {z : G} (hzK : z ∈ T ⊓ K) (hz2 : orderOf z = 2) (hzB : z ∈ B) :
    ∃ (v : G) (L : Subgroup G),
      v ∈ Subgroup.zpowers z ⊔ (B ⊓ (T ⊓ CxK x K)) ∧ v ∉ B ⊓ (T ⊓ CxK x K) ∧ v ≠ z ∧
      orderOf v = 2 ∧ IsPCompIn 2 (centralizer ({v} : Set G)) L ∧ IsUnbalancingTriple v t L ∧
      z ∈ normalizer (L : Set G) ∧ z ∉ centralizerSection L (pPrimeCoreOf 2 L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcen, hP⟩ := hstd.centerless_and_shape hG hL34 h102
  have hcd := hstd.commDisj hcen
  set E : Subgroup G := B ⊓ (T ⊓ CxK x K) with hE
  have hEQ : E ≤ T ⊓ CxK x K := inf_le_right
  have hEB : E ≤ B := inf_le_left
  have hEel : CFSG.IsElementaryAbelian 2 ↥E := isElementaryAbelian_le hpick.elem hEB
  have hE2' : pRank 2 ↥E = 2 :=
    le_antisymm (hstd.pRank_le_two_of_le_Q hG hL34 h102 hEQ) hE2
  have hzel := Th2.isElementaryAbelian_zpowers_of_orderOf_two hz2
  have hzP : Subgroup.zpowers z ≤ T ⊓ K := Subgroup.zpowers_le.2 hzK
  set A : Subgroup G := Subgroup.zpowers z ⊔ E with hA
  have hAel : CFSG.IsElementaryAbelian 2 ↥A := hcd.isElementaryAbelian_sup' hzel hEel hzP hEQ
  have hA3 : pRank 2 ↥A = 3 := by
    rw [hA, hcd.pRank_sup hzel hEel hzP hEQ, Th2.pRank_zpowers_of_orderOf_two hz2, hE2']
  have hAB : A ≤ B := sup_le (Subgroup.zpowers_le.2 hzB) hEB
  have hAN : A ≤ normalizer (J : Set G) := hAB.trans hpick.normalizes
  have hzA : z ∈ A := Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hpick.elem
  have htB : t ∈ B := hpick.t_mem.1
  have hxJ : x ∈ normalizer (J : Set G) := hpick.normalizes hpick.x_mem
  obtain ⟨eJK⟩ := hpick.bar
  have hzJ : z ∈ J := by
    refine mem_pumpup_of_two_elt hpick.pump hxJ eJK hzK.2 (hBc z hzB t htB) ⟨1, ?_⟩
    have := pow_orderOf_eq_one z
    rwa [hz2] at this
  have hJc : IsPCompIn 2 (centralizer ({t} : Set G)) J := hpick.pump.2.1.2.2
  obtain ⟨V, a, hVA, hV2, haJ, haodd, haV, hza, ha1⟩ :=
    row2_exists_a hJc hpick.nonqs hsimple hAel hA3 hAN hzA hz2 hzJ
  obtain ⟨v, L, hvV, hv1, hv2, hL, hunb, hzN, hzv, hvz, hzL⟩ :=
    row2_exists_vL hG hL34 h102 hpick.elem hVA hAB hV2 h7B2 htB hpick.t_two hJc hzA haJ haodd haV
      hza ha1
  refine ⟨v, L, hVA hvV, fun hvE => ?_, hvz, hv2, hL, hunb, hzN, hzL⟩
  exact row2_not_mem_E hG hL34 h102 hstd hpick.elem hpick.x_mem hpick.t_mem hvE hv2 hpick.t_two hz2
    hzK.2 hzB hL hunb hzL

end CFSG.GH74.GLS.Th2.Obs
