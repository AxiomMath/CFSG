module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511Defs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.OraclesGen
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511C
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511D2
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PG
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PM
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecLiftSylowSelf
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.AGL81I811Reduction
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.LThreeTwoPowCore
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.CtxRankBound

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open KFactsSmall
open CFSG.LocalAnalysis.AGL81TheoremCD.Section15
open scoped commutatorElement

namespace false_of_A8_L5_aux

theorem eq_bot_of_perfect_central_odd {P : Type} [Group P] [Finite P]
    (hP : _root_.commutator P = ⊤) (Z : Subgroup P) (hZ : Z ≤ Subgroup.center P)
    (hodd : Odd (Nat.card Z)) (hcard : Nat.card P = 168 * Nat.card Z) : Z = ⊥ := by
  by_contra hne
  have hZ1 : Nat.card Z ≠ 1 := fun h => hne (Subgroup.eq_bot_of_card_eq Z h)
  obtain ⟨p, hp, hpZ⟩ := Nat.exists_prime_and_dvd hZ1
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hpZ)
  haveI : Z.Normal := Subgroup.normal_of_le_center hZ
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) p hpZ
  have hz'ord : orderOf (z : P) = p := by rw [Subgroup.orderOf_coe]; exact hz
  have hzp : IsPGroup p (Subgroup.zpowers (z : P)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hz'ord, pow_one]
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  have hzQ : (z : P) ∈ (Q : Subgroup P) := hQ (Subgroup.mem_zpowers _)
  set H : Subgroup P := (Q : Subgroup P) with hH
  let f : ↥H →* P ⧸ Z := (QuotientGroup.mk' Z).comp H.subtype
  have hker : f.ker ≤ Subgroup.center ↥H := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro g
    have hy' : (y : P) ∈ Z := (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hy)
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hZ hy') g)
  have hHp : IsPGroup p H := Q.isPGroup'
  have hrange_p : IsPGroup p f.range := hHp.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hP168 : Nat.card (P ⧸ Z) = 168 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    have hpos : 0 < Nat.card Z := Nat.card_pos
    rw [hcard] at h
    nlinarith
  have hrdvd : Nat.card f.range ∣ 168 := hP168 ▸ Subgroup.card_subgroup_dvd_card f.range
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hrange_p
  have hcyc : IsCyclic f.range := by
    have h21 : p ^ a ∣ 21 := by
      rw [ha] at hrdvd
      have hcop : Nat.Coprime (p ^ a) 8 := by
        apply Nat.Coprime.pow_left
        have : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
        simpa using Nat.Coprime.pow_right 3 this
      have : (168 : ℕ) = 8 * 21 := by norm_num
      rw [this] at hrdvd
      exact hcop.dvd_of_dvd_mul_left hrdvd
    rcases Nat.lt_or_ge a 2 with ha2 | ha2
    · interval_cases a
      · have h1 : Nat.card f.range = 1 := by rw [ha]; simp
        haveI : Subsingleton f.range := (Nat.card_eq_one_iff_unique.1 h1).1
        infer_instance
      · exact isCyclic_of_prime_card (p := p) (by rw [ha]; simp)
    · exfalso
      have h1 : p ^ 2 ∣ 21 := (pow_dvd_pow p ha2).trans h21
      have h2 : p ^ 2 ≤ 21 := Nat.le_of_dvd (by norm_num) h1
      have h3 : p ≤ 4 := by nlinarith [hp.two_le]
      have h4 : p = 3 := by
        have := hp.two_le
        rcases (show p = 3 ∨ p = 4 by omega) with h | h
        · exact h
        · exact absurd (h ▸ hp : Nat.Prime 4) (by norm_num)
      rw [h4] at h1
      norm_num at h1
  haveI : IsMulCommutative ↥H :=
    f.rangeRestrict.isMulCommutative_of_isCyclic_of_ker_le_center (by rwa [MonoidHom.ker_rangeRestrict])
  have hidx : ¬ p ∣ H.index := Sylow.not_dvd_index Q
  let ϕ : ↥H →* Abelianization ↥H := Abelianization.of
  have key : ∀ (k : ℕ) (g₀ : P), g₀⁻¹ * (z : P) ^ k * g₀ ∈ H →
      g₀⁻¹ * (z : P) ^ k * g₀ = (z : P) ^ k := by
    intro k g₀ _
    have hc : (z : P) ^ k ∈ Subgroup.center P := Subgroup.pow_mem _ (hZ z.2) k
    have h := Subgroup.mem_center_iff.1 hc g₀⁻¹
    rw [h, mul_assoc, inv_mul_cancel, mul_one]
  have h1 := MonoidHom.transfer_eq_pow ϕ (z : P) key
  have h2 : MonoidHom.transfer ϕ (z : P) = 1 := by
    have h := Abelianization.commutator_subset_ker (MonoidHom.transfer ϕ)
    rw [hP] at h
    exact MonoidHom.mem_ker.1 (h (Subgroup.mem_top _))
  rw [h2] at h1
  have h3 := MonoidHom.mem_ker.2 h1.symm
  rw [Abelianization.ker_of, _root_.commutator_eq_bot] at h3
  have h4 := congrArg Subtype.val (Subgroup.mem_bot.1 h3)
  have h5 : orderOf (z : P) ∣ H.index := orderOf_dvd_of_pow_eq_one h4
  rw [hz'ord] at h5
  exact hidx h5

theorem pCore_two_quotient_eq_bot {G : Type} [Group G] [Finite G] :
    CFSG.pCore 2 (G ⧸ CFSG.pCore 2 G) = ⊥ := by
  have key : ∀ (K : Subgroup G) [K.Normal], K = CFSG.primeSetCore {2} G →
      CFSG.pCore 2 (G ⧸ K) = ⊥ := by
    intro K _ hK
    subst hK
    rw [← CFSG.primeSetCore_singleton_eq_pCore Nat.prime_two]
    exact CFSG.primeSetCore_quotient_primeSetCore_eq_bot _
  exact key _ (CFSG.primeSetCore_singleton_eq_pCore Nat.prime_two).symm

theorem quotient_pCore_equiv {D S : Type} [Group D] [Finite D] [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hS168 : Nat.card S = 168)
    (θ : D →* S) (hθ : Function.Surjective θ) (hperf : _root_.commutator D = ⊤)
    (Kc : Subgroup D) (h0 : ∀ x ∈ Kc, θ x = 1)
    (h1 : ∀ x ∈ Kc, ∀ l : D, ⁅x, l⁆ ∈ CFSG.pCore 2 D)
    (h2 : ∀ w, θ w = 1 → ∃ k : ℕ, w ^ (2 ^ k) ∈ Kc) :
    Nonempty ((D ⧸ CFSG.pCore 2 D) ≃* S) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.pCore 2 D with hQ
  haveI : Q.Normal := CFSG.pCore_normal
  have hQker : Q ≤ θ.ker := by
    have hn : (Q.map θ).Normal := Subgroup.Normal.map inferInstance θ hθ
    rcases hS.eq_bot_or_eq_top_of_normal (Q.map θ) with h | h
    · intro x hx
      refine MonoidHom.mem_ker.2 ?_
      have : θ x ∈ Q.map θ := ⟨x, hx, rfl⟩
      rw [h] at this
      simpa using this
    · exfalso
      have hp : IsPGroup 2 (Q.map θ) := (CFSG.pCore_isPGroup (p := 2) (G := D)).map θ
      rw [h] at hp
      have hp' : IsPGroup 2 S := hp.of_surjective (Subgroup.topEquiv : (⊤ : Subgroup S) ≃* S).toMonoidHom (Subgroup.topEquiv : (⊤ : Subgroup S) ≃* S).surjective
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hp'
      have h3 : 3 ∣ 2 ^ n := by rw [← hn, hS168]; norm_num
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
  let θb : (D ⧸ Q) →* S := QuotientGroup.lift Q θ hQker
  have hθb : Function.Surjective θb := by
    intro s
    obtain ⟨d, hd⟩ := hθ s
    exact ⟨QuotientGroup.mk d, by rw [QuotientGroup.lift_mk]; exact hd⟩
  have hperfΔ : _root_.commutator (D ⧸ Q) = ⊤ := by
    unfold _root_.commutator at hperf ⊢
    have h := Subgroup.map_commutator (⊤ : Subgroup D) (⊤ : Subgroup D) (QuotientGroup.mk' Q)
    rw [hperf, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Q)] at h
    exact h.symm
  have hO2 : CFSG.pCore 2 (D ⧸ Q) = ⊥ := pCore_two_quotient_eq_bot
  let Kb : Subgroup (D ⧸ Q) := Kc.map (QuotientGroup.mk' Q)
  have hKbc : Kb ≤ Subgroup.center (D ⧸ Q) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective g
    have h3 : ⁅(QuotientGroup.mk' Q) x, (QuotientGroup.mk' Q) l⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).2 (h1 x hx l)
    exact (commutatorElement_eq_one_iff_mul_comm.1 h3).symm
  let Wb : Subgroup (D ⧸ Q) := θb.ker
  have hWn : Wb.Normal := MonoidHom.normal_ker θb
  let Kw : Subgroup ↥Wb := Kb.subgroupOf Wb
  have hKwc : Kw ≤ Subgroup.center ↥Wb := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hKbc hy) g)
  haveI : Kw.Normal := Subgroup.normal_of_le_center hKwc
  have hKbW : ∀ w : ↥Wb, ∃ k : ℕ, w ^ (2 ^ k) ∈ Kw := by
    intro w
    obtain ⟨d, hd⟩ := QuotientGroup.mk_surjective (w : D ⧸ Q)
    have hθd : θ d = 1 := by
      have := MonoidHom.mem_ker.1 w.2
      rw [← hd] at this
      simpa [θb] using this
    obtain ⟨k, hk⟩ := h2 d hθd
    refine ⟨k, ?_⟩
    show ((w ^ (2 ^ k) : ↥Wb) : D ⧸ Q) ∈ Kb
    rw [Subgroup.coe_pow, ← hd]
    exact ⟨d ^ (2 ^ k), hk, by simp⟩
  have h2grp : IsPGroup 2 (↥Wb ⧸ Kw) := by
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hKbW w
    exact ⟨k, by rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).2 hk⟩
  haveI : Group.IsNilpotent (↥Wb ⧸ Kw) := h2grp.isNilpotent
  haveI hnil : Group.IsNilpotent ↥Wb :=
    _root_.isNilpotent_of_ker_le_center (QuotientGroup.mk' Kw) (by rw [QuotientGroup.ker_mk']; exact hKwc)
  have hWodd : ¬ 2 ∣ Nat.card Wb := by
    intro h2d
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Wb) 2 h2d
    have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx]; simp)
    obtain ⟨P, hP⟩ := hxp.exists_le_sylow
    have hle := Sylow.map_le_pCore hWn hnil 2 P
    have hxP : x ∈ (P : Subgroup ↥Wb) := hP (Subgroup.mem_zpowers x)
    have hxmem : (x : D ⧸ Q) ∈ CFSG.pCore 2 (D ⧸ Q) := hle ⟨x, hxP, rfl⟩
    rw [hO2, Subgroup.mem_bot] at hxmem
    have : x = 1 := Subtype.ext hxmem
    rw [this, orderOf_one] at hx
    omega
  have hWK : Wb ≤ Kb := by
    have hdvd : Nat.card (↥Wb ⧸ Kw) ∣ Nat.card Wb := Subgroup.card_quotient_dvd_card Kw
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 h2grp
    have ha0 : a = 0 := by
      by_contra hne
      apply hWodd
      rw [ha] at hdvd
      exact (dvd_pow_self 2 hne).trans hdvd
    have hidx : Kw.index = 1 := by rw [Subgroup.index_eq_card, ha, ha0, pow_zero]
    have hKwtop : Kw = ⊤ := Subgroup.index_eq_one.1 hidx
    intro w hw
    have : (⟨w, hw⟩ : ↥Wb) ∈ Kw := by rw [hKwtop]; exact Subgroup.mem_top _
    exact this
  have hWc : Wb ≤ Subgroup.center (D ⧸ Q) := hWK.trans hKbc
  have hcardΔ : Nat.card (D ⧸ Q) = 168 * Nat.card Wb := by
    have h := Subgroup.card_ker_mul_card_range θb
    rw [MonoidHom.range_eq_top.2 hθb, Subgroup.card_top, hS168] at h
    rw [← h]
    ring
  have hbot : Wb = ⊥ :=
    eq_bot_of_perfect_central_odd hperfΔ Wb hWc (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hWodd))
      hcardΔ
  exact ⟨MulEquiv.ofBijective θb ⟨(MonoidHom.ker_eq_bot_iff θb).1 hbot, hθb⟩⟩

theorem hasLThreeCore_of_quotient_equiv {Y : Type} [Group Y] {D : Subgroup Y} [Finite ↥D]
    {S : Type} [Group S] (e : (↥D ⧸ CFSG.pCore 2 ↥D) ≃* S) (hS : IsLThreeTwo S) :
    HasLThreeCore D := by
  obtain ⟨hsimp, hcard⟩ := small1522_simple_center_aux3 hS
  haveI : IsSimpleGroup S := hsimp
  haveI : IsSimpleGroup (↥D ⧸ CFSG.pCore 2 ↥D) := e.isSimpleGroup
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card (↥D ⧸ CFSG.pCore 2 ↥D) := by
    rw [Nat.card_congr e.toEquiv, hcard]; norm_num
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥D ⧸ CFSG.pCore 2 ↥D) 2 h2
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy
    omega
  have htop : pElementSubgroup 2 (⊤ : Subgroup (↥D ⧸ CFSG.pCore 2 ↥D)) = ⊤ := by
    haveI := R1511C.pElementSubgroup_top_normal (Y := ↥D ⧸ CFSG.pCore 2 ↥D) 2
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (pElementSubgroup 2 (⊤ : Subgroup (↥D ⧸ CFSG.pCore 2 ↥D))) with h | h
    · exfalso
      apply hy1
      have : y ∈ pElementSubgroup 2 (⊤ : Subgroup (↥D ⧸ CFSG.pCore 2 ↥D)) :=
        Subgroup.subset_closure ⟨Subgroup.mem_top y, 1, by rw [hy]; simp⟩
      rw [h] at this
      simpa using this
    · exact h
  let iso : ↥(pElementSubgroup 2 (⊤ : Subgroup (↥D ⧸ CFSG.pCore 2 ↥D))) ≃* S :=
    ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).trans e
  exact R1511C.isLThreeOdd_of_equiv iso ⟨1, odd_one, isLThreeTwo_iff_isLThreeOfExp_one.1 hS⟩

theorem exists_component_image_le {P : Type} [Group P] [Finite P] (A : Subgroup P) [A.Normal]
    (hS : IsSimpleGroup ↥(pElementSubgroup 2 (⊤ : Subgroup (↥A ⧸ CFSG.pCore 2 ↥A))))
    (h3 : 3 ∣ Nat.card ↥(pElementSubgroup 2 (⊤ : Subgroup (↥A ⧸ CFSG.pCore 2 ↥A)))) :
    ∃ K₁ : Subgroup (P ⧸ CFSG.pPrimeCore 3 P), CFSG.IsComponent K₁ ∧
      K₁ ≤ A.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 P)) ∧
      Nonempty (↥(pElementSubgroup 2 (⊤ : Subgroup (↥A ⧸ CFSG.pCore 2 ↥A))) ≃* ↥K₁) := by
  classical
  haveI := hS
  have hAsub : A.IsSubnormal := Subgroup.Normal.isSubnormal inferInstance
  have hπs : Function.Surjective (QuotientGroup.mk' (CFSG.pPrimeCore 3 P)) :=
    QuotientGroup.mk'_surjective _
  have hgker : ((QuotientGroup.mk' (CFSG.pPrimeCore 3 P)).comp A.subtype).ker =
      CFSG.pPrimeCore 3 ↥A := by
    rw [← R1511C.subgroupOf_pPrimeCore_eq hAsub]
    ext a
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_subtype]
  have hle : CFSG.pCore 2 ↥A ≤ ((QuotientGroup.mk' (CFSG.pPrimeCore 3 P)).comp A.subtype).ker :=
    hgker ▸ R1511C.pCore_two_le_pPrimeCore_three ↥A
  let gh : (↥A ⧸ CFSG.pCore 2 ↥A) →* P ⧸ CFSG.pPrimeCore 3 P :=
    QuotientGroup.lift (CFSG.pCore 2 ↥A) _ hle
  have hghker : gh.ker ≤ (CFSG.pPrimeCore 3 ↥A).map (QuotientGroup.mk' (CFSG.pCore 2 ↥A)) := by
    intro y hy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
    refine ⟨a, ?_, rfl⟩
    rw [← hgker]
    exact hy
  have hnd : ¬ 3 ∣ Nat.card gh.ker := fun hd =>
    R1511C.not_dvd_card_pPrimeCore ↥A
      (hd.trans ((Subgroup.card_dvd_of_le hghker).trans (Subgroup.card_map_dvd _ _)))
  let Kt : Subgroup (↥A ⧸ CFSG.pCore 2 ↥A) := pElementSubgroup 2 ⊤
  let f : ↥Kt →* P ⧸ CFSG.pPrimeCore 3 P := gh.comp Kt.subtype
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
    · exact h
    · exfalso
      have hKle : Kt ≤ gh.ker := fun x hx => by
        have h1 : f ⟨x, hx⟩ = 1 := by
          rw [← MonoidHom.mem_ker, h]
          exact Subgroup.mem_top _
        exact h1
      exact hnd (h3.trans (Subgroup.card_dvd_of_le hKle))
  have hnc := R1511C.exists_noncomm_of_simple_of_dvd h3 R1511C.closure_two_elements_eq_top
  let e : ↥Kt ≃* ↥f.range := MonoidHom.ofInjective hfinj
  haveI : Kt.Normal := R1511C.pElementSubgroup_top_normal 2
  have hcomp : (QuotientGroup.mk' (CFSG.pPrimeCore 3 P)).comp A.subtype =
      gh.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥A)) := MonoidHom.ext fun a => rfl
  have hrange : f.range = ((Kt.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥A))).map A.subtype).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 P)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_map, hcomp,
      ← Subgroup.map_map,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  refine ⟨f.range, ⟨?_, ?_⟩, ?_, ⟨e⟩⟩
  · exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).1
      (R1511C.isQuasisimple_of_simple_noncomm hnc)
  · have hK1 : (Kt.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥A))).IsSubnormal :=
      Subgroup.Normal.isSubnormal inferInstance
    rw [hrange]
    exact (hK1.trans' hAsub).map hπs
  · rw [hrange]
    exact Subgroup.map_mono (Subgroup.map_subtype_le _)

theorem exists_isPComponent_map_eq_le {Y : Type} [Group Y] [Finite Y] {A : Subgroup Y} [A.Normal]
    {K : Subgroup (Y ⧸ CFSG.pPrimeCore 3 Y)} (hK : CFSG.IsComponent K)
    (hKA : K ≤ A.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 Y))) :
    ∃ L : Subgroup Y, L ≤ A ∧ CFSG.IsPComponent 3 L ∧
      L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 Y)) = K := by
  classical
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 Y)
  have hAsub : A.IsSubnormal := Subgroup.Normal.isSubnormal inferInstance
  have hJ0 : (A ⊓ K.comap π).IsSubnormal := hAsub.inf (hK.2.comap π)
  have hmap0 : (A ⊓ K.comap π).map π = K := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.2
    · intro hy
      obtain ⟨x, hxA, rfl⟩ := hKA hy
      exact ⟨x, ⟨hxA, hy⟩, rfl⟩
  have hex : ∃ n : ℕ, ∃ J : Subgroup Y, J ≤ A ∧ J.IsSubnormal ∧ J.map π = K ∧ Nat.card J = n :=
    ⟨_, A ⊓ K.comap π, inf_le_left, hJ0, hmap0, rfl⟩
  obtain ⟨J, hJA, hJsub, hJmap, hJcard⟩ : ∃ J : Subgroup Y, J ≤ A ∧ J.IsSubnormal ∧
      J.map π = K ∧ Nat.card J = Nat.find hex := Nat.find_spec hex
  refine ⟨J, hJA, ⟨K, hK, hJsub, hJmap, fun J' hlt hsub hmap => ?_⟩, hJmap⟩
  have hle : Nat.find hex ≤ Nat.card J' :=
    Nat.find_min' hex ⟨J', hlt.le.trans hJA, hsub, hmap, rfl⟩
  have hlt' : Nat.card J' < Nat.card J := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hlt.le) fun heq => ?_
    exact hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le heq.ge)
  omega

theorem exists_isPComponent_le_of_hasLThreeCore (hK3 : K3DvdL3) {P : Type} [Group P] [Finite P]
    {A : Subgroup P} [A.Normal] (h : HasLThreeCore A) :
    ∃ L : Subgroup P, L ≤ A ∧ CFSG.IsPComponent 3 L ∧
      IsLThreeTwoPow (↥L ⧸ CFSG.pPrimeCore 3 ↥L) := by
  have h2 : IsLThreeTwoPow ↥(pElementSubgroup 2 (⊤ : Subgroup (↥A ⧸ CFSG.pCore 2 ↥A))) :=
    R1511C.isLThreeTwoPow_of_isLThreeOdd h
  obtain ⟨K₁, hK₁, hK₁A, ⟨e⟩⟩ := exists_component_image_le A
    (R1511C.isSimpleGroup_of_isLThreeTwoPow h2) (hK3 _ h2)
  obtain ⟨L, hLA, hL, hLmap⟩ := exists_isPComponent_map_eq_le hK₁ hK₁A
  obtain ⟨e1⟩ := isPComponent_quot_equiv hL
  exact ⟨L, hLA, hL, R1511C.isLThreeTwoPow_of_equiv
    (e1.trans ((MulEquiv.subgroupCongr hLmap).trans e.symm)) h2⟩

theorem exists_threeComponent_of_section' (hK3 : K3DvdL3) {P : Type} [Group P] [Finite P]
    (I : Subgroup P) [I.Normal] {B : Type} [Group B] [Finite B]
    (ψ : ↥I →* B) (hψ : Function.Surjective ψ) (hB : IsLThreeTwo (B ⧸ CFSG.pCore 2 B))
    (hc : ∀ x : ↥I, ψ x = 1 → ∀ l : ↥I, ⁅(x : P), (l : P)⁆ ∈ CFSG.pCore 2 P) :
    ∃ L : Subgroup P, L ≤ I ∧ CFSG.IsPComponent 3 L ∧
      IsLThreeTwoPow (↥L ⧸ CFSG.pPrimeCore 3 ↥L) ∧
      IsLThreeTwoPow (↥L ⧸ CFSG.pCore 2 ↥L) := by
  classical
  haveI : (CFSG.pCore 2 B).Normal := CFSG.pCore_normal
  obtain ⟨hSsimp, hS168⟩ := small1522_simple_center_aux3 hB
  haveI := hSsimp
  let θ : ↥I →* (B ⧸ CFSG.pCore 2 B) := (QuotientGroup.mk' (CFSG.pCore 2 B)).comp ψ
  have hθ : Function.Surjective θ := (QuotientGroup.mk'_surjective _).comp hψ
  have hSperf : _root_.commutator (B ⧸ CFSG.pCore 2 B) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (_root_.commutator (B ⧸ CFSG.pCore 2 B)) with h | h
    · exfalso
      haveI : IsMulCommutative (B ⧸ CFSG.pCore 2 B) := (_root_.commutator_eq_bot_iff _).1 h
      have := Group.is_simple_iff_prime_card.mp hSsimp
      rw [hS168] at this
      exact absurd this (by norm_num)
    · exact h
  let 𝒟 : Set (Subgroup ↥I) := {D | (D.map I.subtype).Normal ∧ D.map θ = ⊤}
  have h𝒟top : (⊤ : Subgroup ↥I) ∈ 𝒟 := by
    refine ⟨?_, Subgroup.map_top_of_surjective θ hθ⟩
    have : (⊤ : Subgroup ↥I).map I.subtype = I := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [this]
    infer_instance
  obtain ⟨D, hD𝒟, hDmin⟩ := Set.exists_min_image 𝒟 (fun D : Subgroup ↥I => Nat.card D)
    (Set.toFinite 𝒟) ⟨⊤, h𝒟top⟩
  obtain ⟨hDn, hDθ⟩ := hD𝒟
  haveI hDn' : (D.map I.subtype).Normal := hDn
  have hDperf : ⁅D, D⁆ = D := by
    have hmem : ⁅D, D⁆ ∈ 𝒟 := by
      refine ⟨?_, ?_⟩
      · rw [Subgroup.map_commutator]
        infer_instance
      · rw [Subgroup.map_commutator, hDθ]
        exact hSperf
    have hle : ⁅D, D⁆ ≤ D := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact D.mul_mem (D.mul_mem (D.mul_mem ha hb) (D.inv_mem ha)) (D.inv_mem hb)
    exact Subgroup.eq_of_le_of_card_ge hle (hDmin _ hmem)
  have hDcomm : _root_.commutator ↥D = ⊤ := by
    have h1 : (⊤ : Subgroup ↥D).map D.subtype = D := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    apply Subgroup.map_injective D.subtype_injective
    unfold _root_.commutator
    rw [Subgroup.map_commutator, h1, hDperf]
  let θD : ↥D →* (B ⧸ CFSG.pCore 2 B) := θ.comp D.subtype
  have hθD : Function.Surjective θD := by
    intro s
    have : s ∈ D.map θ := by
      rw [hDθ]
      exact Subgroup.mem_top s
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨⟨x, hx⟩, rfl⟩
  let Kc : Subgroup ↥D := (ψ.comp D.subtype).ker
  have h0 : ∀ x ∈ Kc, θD x = 1 := by
    intro x hx
    have hx' : ψ (D.subtype x) = 1 := MonoidHom.mem_ker.1 hx
    show (QuotientGroup.mk' (CFSG.pCore 2 B)) (ψ (D.subtype x)) = 1
    rw [hx']
    simp
  have h1 : ∀ x ∈ Kc, ∀ l : ↥D, ⁅x, l⁆ ∈ CFSG.pCore 2 ↥D := by
    intro x hx l
    let R : Subgroup ↥D := (CFSG.pCore 2 P).comap (I.subtype.comp D.subtype)
    haveI : R.Normal := Subgroup.Normal.comap CFSG.pCore_normal _
    have hR : IsPGroup 2 R :=
      (CFSG.pCore_isPGroup (p := 2) (G := P)).comap_of_injective _
        (I.subtype_injective.comp D.subtype_injective)
    have hRle : R ≤ CFSG.pCore 2 ↥D := le_sSup ⟨inferInstance, hR⟩
    apply hRle
    show (I.subtype.comp D.subtype) ⁅x, l⁆ ∈ CFSG.pCore 2 P
    rw [map_commutatorElement]
    exact hc (D.subtype x) (MonoidHom.mem_ker.1 hx) (D.subtype l)
  have h2 : ∀ w, θD w = 1 → ∃ k : ℕ, w ^ (2 ^ k) ∈ Kc := by
    intro w hw
    have hw' : ψ (D.subtype w) ∈ CFSG.pCore 2 B := (QuotientGroup.eq_one_iff _).1 hw
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := B)) ⟨_, hw'⟩
    refine ⟨k, MonoidHom.mem_ker.2 ?_⟩
    have := congrArg Subtype.val hk
    simpa [map_pow] using this
  obtain ⟨e⟩ := quotient_pCore_equiv hSsimp hS168 θD hθD hDcomm Kc h0 h1 h2
  have hLD : HasLThreeCore D := hasLThreeCore_of_quotient_equiv e hB
  have hLD' : HasLThreeCore (D.map I.subtype) :=
    R1511C.hasLThreeCore_of_equiv (D.equivMapOfInjective I.subtype I.subtype_injective).symm hLD
  have hApow : IsLThreeTwoPow (↥(D.map I.subtype) ⧸
      CFSG.pCore 2 ↥(D.map I.subtype)) :=
    exists_sylow_of_K89Sp_aux1
      (D.equivMapOfInjective I.subtype I.subtype_injective).symm
      (R1511C.isLThreeTwoPow_of_equiv e
        (R1511C.isLThreeTwoPow_of_isLThreeOdd
          ⟨1, odd_one, isLThreeTwo_iff_isLThreeOfExp_one.1 hB⟩))
  have hcoreA : CFSG.pPrimeCore 3 ↥(D.map I.subtype) =
      CFSG.pCore 2 ↥(D.map I.subtype) :=
    pPrimeCore_three_eq_pCore_two hApow
  obtain ⟨L, hLle, hLcomp, hLq⟩ :=
    exists_isPComponent_le_of_hasLThreeCore hK3 (A := D.map I.subtype) hLD'
  have hLsub : L.IsSubnormal := by
    obtain ⟨-, -, hLsub, -, -⟩ := hLcomp
    exact hLsub
  have h2L : IsPGroup 2 (CFSG.pPrimeCore 3 ↥L) := by
    have hcoreSub := R1511C.subgroupOf_pPrimeCore_eq
      (P := D.map I.subtype) (L := L.subgroupOf (D.map I.subtype)) hLsub.subgroupOf
    have h2 : IsPGroup 2
        (CFSG.pPrimeCore 3 ↥(L.subgroupOf (D.map I.subtype))) := by
      rw [← hcoreSub, hcoreA]
      exact (CFSG.pCore_isPGroup (p := 2) (G := D.map I.subtype)).comap_subtype
    let eL : ↥(L.subgroupOf (D.map I.subtype)) ≃* ↥L :=
      Subgroup.subgroupOfEquivOfLe hLle
    rw [← CFSG.pPrimeCore_map_iso 3 eL]
    exact h2.map eL.toMonoidHom
  exact ⟨L, hLle.trans (Subgroup.map_subtype_le D), hLcomp, hLq,
    isLThreeTwoPow_pCore_of_pPrimeCore h2L hLq⟩

section XLevel

variable {X : Type} [Group X] [Finite X]

theorem comm_mem_pCore_of_lift {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hX : GNSetting X T) (hLs : IsComponentOf Ls ⊤) (hL : LiftOf T L Ls) {x l : X} (hx : x ∈ L)
    (hxC : x ∈ gnC T) (hl : l ∈ L) : ⁅x, l⁆ ∈ CFSG.pCore 2 X := by
  obtain ⟨z, hz, hzx⟩ := (liftOf_central_ext hX hLs hL).1
    (Subgroup.mem_map.2 ⟨x, ⟨hx, hxC⟩, rfl⟩)
  have h1 := Subgroup.mem_center_iff.1 hz ⟨QuotientGroup.mk' (CFSG.pCore 2 X) l, ⟨l, hl, rfl⟩⟩
  have h2 := congrArg Subtype.val h1
  have hzx' : (z : X ⧸ CFSG.pCore 2 X) = QuotientGroup.mk' (CFSG.pCore 2 X) x := hzx
  have h3 : QuotientGroup.mk' (CFSG.pCore 2 X) l * QuotientGroup.mk' (CFSG.pCore 2 X) x =
      QuotientGroup.mk' (CFSG.pCore 2 X) x * QuotientGroup.mk' (CFSG.pCore 2 X) l := by
    simpa [hzx'] using h2
  have h4 : ⁅QuotientGroup.mk' (CFSG.pCore 2 X) x, QuotientGroup.mk' (CFSG.pCore 2 X) l⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 h3.symm
  rw [← map_commutatorElement] at h4
  exact (QuotientGroup.eq_one_iff _).1 h4

theorem exists_threeComponent_of_gnA' (hK3 : K3DvdL3) {T Ti : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hX : GNSetting X T) (hLs : IsComponentOf Ls ⊤)
    (hL : LiftOf T L Ls) (hLn : L.Normal)
    (hsl : gnA T Ti Ls ≤ (Subgroup.normalizer (Ti : Set X) ⊓ L).map (toStar T))
    (hmod : IsL3TwoModO2 (gnA T Ti Ls)) :
    ∃ L' : Subgroup X, L' ≤ Subgroup.normalizer (Ti : Set X) ⊓ L ∧
      CFSG.IsPComponent 3 (L'.subgroupOf (Subgroup.normalizer (Ti : Set X))) ∧
      IsLThreeTwoPow (↥L' ⧸ CFSG.pPrimeCore 3 ↥L') ∧
      IsLThreeTwoPow (↥L' ⧸ CFSG.pCore 2 ↥L') := by
  set N : Subgroup X := Subgroup.normalizer (Ti : Set X) with hN
  set I : Subgroup ↥N := (N ⊓ L).subgroupOf N with hI
  haveI hIn : I.Normal := R1511C.normal_inf_subgroupOf N L hLn
  have hmem : ∀ x : ↥I, toStar T (x : ↥N).1 ∈ gnA T Ti Ls := by
    intro x
    have hx : ((x : ↥N) : X) ∈ N ⊓ L := x.2
    refine ⟨⟨_, hx.1, rfl⟩, ?_⟩
    rw [← hL.2]
    exact ⟨_, hx.2, rfl⟩
  let ψ : ↥I →* ↥(gnA T Ti Ls) :=
    { toFun := fun x => ⟨toStar T (x : ↥N).1, hmem x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨n, hn, rfl⟩ := hsl hy
    exact ⟨⟨⟨n, hn.1⟩, hn⟩, rfl⟩
  have hc : ∀ x : ↥I, ψ x = 1 → ∀ l : ↥I, ⁅(x : ↥N), (l : ↥N)⁆ ∈ CFSG.pCore 2 ↥N := by
    intro x hx l
    have hxC : ((x : ↥N) : X) ∈ gnC T := by
      have := congrArg Subtype.val hx
      exact (QuotientGroup.eq_one_iff _).1 this
    have hxL : ((x : ↥N) : X) ∈ L := (show ((x : ↥N) : X) ∈ N ⊓ L from x.2).2
    have hlL : ((l : ↥N) : X) ∈ L := (show ((l : ↥N) : X) ∈ N ⊓ L from l.2).2
    have hcomm := comm_mem_pCore_of_lift hX hLs hL hxL hxC hlL
    let R : Subgroup ↥N := (CFSG.pCore 2 X).comap N.subtype
    haveI : R.Normal := Subgroup.Normal.comap CFSG.pCore_normal _
    have hR : IsPGroup 2 R :=
      (CFSG.pCore_isPGroup (p := 2) (G := X)).comap_of_injective _ N.subtype_injective
    have hRle : R ≤ CFSG.pCore 2 ↥N := le_sSup ⟨inferInstance, hR⟩
    apply hRle
    show N.subtype ⁅(x : ↥N), (l : ↥N)⁆ ∈ CFSG.pCore 2 X
    rw [map_commutatorElement]
    exact hcomm
  obtain ⟨L₀, hL₀I, hL₀, hL₀q, hL₀q2⟩ := exists_threeComponent_of_section' hK3 I ψ hψ hmod hc
  refine ⟨L₀.map N.subtype, ?_, ?_, ?_, ?_⟩
  · have := Subgroup.map_mono (f := N.subtype) hL₀I
    rw [hI, Subgroup.subgroupOf_map_subtype] at this
    exact this.trans inf_le_left
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
    exact hL₀
  · exact isLThreeTwoPow_quotient_aux2 (L₀.equivMapOfInjective N.subtype N.subtype_injective).symm
      hL₀q
  · exact exists_sylow_of_K89Sp_aux1
      (L₀.equivMapOfInjective N.subtype N.subtype_injective).symm hL₀q2

end XLevel

section GLevel

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_map_conj_eq {M : Subgroup G} {g : G}
    (h : M.map (MulAut.conj g).toMonoidHom = M) : g ∈ Subgroup.normalizer (M : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : (MulAut.conj g) x ∈ M.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
    rw [h] at this
    simpa [MulAut.conj_apply] using this
  · intro hx
    rw [← h] at hx
    obtain ⟨m, hm, hmx⟩ := hx
    have : m = x := by simpa [MulAut.conj_apply] using hmx
    rw [← this]
    exact hm

theorem mem_of_map_conj_le {M A : Subgroup G} (hM : rankThreeIsMaxTwoLocal M)
    (hA : A ∈ uniqueSet M) {h : G} (hAh : A.map (MulAut.conj h).toMonoidHom ≤ M) : h ∈ M := by
  have h1 : A ≤ M.map (MulAut.conj h⁻¹).toMonoidHom := by
    intro y hy
    refine ⟨h * y * h⁻¹, hAh ⟨y, hy, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  have h2 := hA.2 h⁻¹ h1
  have h3 := mem_normalizer_of_map_conj_eq h2
  rw [CFSG.RankThreeCoreUniqueness.Helpers.maxTwoLocal_self_normalizing M hM] at h3
  simpa using M.inv_mem h3

private theorem isTwoLocal_normalizer_map_subtype {M T : Subgroup G} {Ti : Subgroup ↥M}
    (hne : Ti ≠ ⊥) (hTiT : Ti.map M.subtype ≤ T) (hT2 : IsPGroup 2 T) :
    IsTwoLocal (Subgroup.normalizer ((Ti.map M.subtype : Subgroup G) : Set G)) := by
  have hne' : Ti.map M.subtype ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have hxG : (x : G) ∈ Ti.map M.subtype := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at hxG
    rw [Subgroup.mem_bot]
    exact Subtype.ext hxG
  exact ⟨Ti.map M.subtype, hne', hT2.to_le hTiT, rfl⟩

theorem false_of_threeComponent_O89_gen {M T : Subgroup G} (hO89 : O89At G M)
    {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂)
    {Ti : Subgroup ↥M} (hne : Ti ≠ ⊥) (hle : Ti ≤ T.subgroupOf M)
    (hchar : (Ti.subgroupOf (T.subgroupOf M)).Characteristic) {L : Subgroup ↥M} (hLn : L.Normal)
    (hrk : CFSG.Open.pRank 3 (Subgroup.normalizer (Ti : Set ↥M) ⊓ L) ≤ 1)
    (hU : ∀ A : Subgroup ↥M, A ≤ L → Nat.card A = 3 → A.map M.subtype ∈ uniqueSet M)
    {L' : Subgroup ↥M} (hL'I : L' ≤ Subgroup.normalizer (Ti : Set ↥M) ⊓ L)
    (hcomp : CFSG.IsPComponent 3 (L'.subgroupOf (Subgroup.normalizer (Ti : Set ↥M))))
    (hLq : IsLThreeTwoPow (↥L' ⧸ CFSG.pCore 2 ↥L'))
    (hH3 : CFSG.Open.pRank 3
      (Subgroup.normalizer ((Ti.map M.subtype : Subgroup G) : Set G)) ≤ 3) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTM : T ≤ M := ctx.sylow.le
  have hTp : IsPGroup 2 T := ctx.sylow.isPGroup
  obtain ⟨hTi'T, hTi'char⟩ := map_subtype_characteristic hTM hle hchar
  obtain ⟨H, hHdef⟩ : ∃ H : Subgroup G,
      Subgroup.normalizer ((Ti.map M.subtype : Subgroup G) : Set G) = H := ⟨_, rfl⟩
  have hND : Subgroup.normalizer (T : Set G) ≤ H := by
    rw [← hHdef]
    exact normalizer_le_normalizer_of_characteristic hTi'T hTi'char
  have hTH : T ≤ H := Subgroup.le_normalizer.trans hND
  have hH2 : IsTwoLocal H := hHdef ▸ isTwoLocal_normalizer_map_subtype hne hTi'T hTp
  have hInf : H ⊓ M = (Subgroup.normalizer (Ti : Set ↥M)).map M.subtype := by
    rw [← hHdef]
    exact false_of_threeComponent_aux2 Ti
  set N := Subgroup.normalizer (Ti : Set ↥M) with hN
  have hL'N : L' ≤ N := hL'I.trans inf_le_left
  have hL'L : L' ≤ L := hL'I.trans inf_le_right
  have hLle : L'.map M.subtype ≤ H ⊓ M := by
    rw [hInf]
    exact Subgroup.map_mono hL'N
  have hcomp' : CFSG.IsPComponent 3 ((L'.map M.subtype).subgroupOf (H ⊓ M)) := by
    rw [hInf]
    exact isPComponent_map_equivMap_aux1 M.subtype M.subtype_injective _ L' hcomp
  have hLq' : IsLThreeTwoPow (↥(L'.map M.subtype) ⧸ CFSG.pCore 2 ↥(L'.map M.subtype)) :=
    exists_sylow_of_K89Sp_aux1 (L'.equivMapOfInjective M.subtype M.subtype_injective).symm hLq
  have h3 : 3 ∣ Nat.card L' := (K3DvdL3_holds _ hLq).trans (Subgroup.card_quotient_dvd_card _)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L') 3 h3
  have hxord : orderOf (x : ↥M) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hx
  set AX : Subgroup ↥M := Subgroup.zpowers (x : ↥M) with hAX
  have hAX3 : Nat.card AX = 3 := by rw [Nat.card_zpowers, hxord]
  have hAXL' : AX ≤ L' := Subgroup.zpowers_le.2 x.2
  have hAXelem : IsElemAbelian 3 AX := by
    refine ⟨inferInstance, ?_⟩
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hx3 : (x : ↥M) ^ 3 = 1 := by rw [← hxord]; exact pow_orderOf_eq_one _
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  set A : Subgroup G := AX.map M.subtype with hA
  have hA3 : Nat.card A = 3 := by
    rw [hA, Subgroup.card_map_of_injective M.subtype_injective]
    exact hAX3
  have hAU : A ∈ uniqueSet M := hU AX (hAXL'.trans hL'L) hAX3
  have hAL'' : A ≤ L'.map M.subtype := Subgroup.map_mono hAXL'
  have hrkL' : CFSG.Open.pRank 3 (L'.map M.subtype) = 1 := by
    have hup : CFSG.Open.pRank 3 (L'.map M.subtype) ≤ 1 := by
      rw [← CFSG.RankThreeEvenClassification.Helpers.pRank_eq_of_subgroup_equiv 3
        Nat.prime_three _ _ (L'.equivMapOfInjective M.subtype M.subtype_injective)]
      exact (CFSG.SectionRank.pRank_mono (by norm_num) hL'I).trans hrk
    have hAelem : IsElemAbelian 3 A := CFSG.SectionRank.isElemAbelian_map hAXelem M.subtype
    have hlow : 1 ≤ CFSG.Open.pRank 3 (L'.map M.subtype) :=
      CFSG.SectionRank.le_pRank (by norm_num) hAL'' hAelem (k := 1) (by rw [hA3]; simp)
    omega
  have hweak : ∀ h ∈ H, A.map (MulAut.conj h).toMonoidHom ≤
      Subgroup.normalizer (A : Set G) ⊓ (H ⊓ M) → A.map (MulAut.conj h).toMonoidHom = A := by
    intro h hh hAh
    have hAhM : A.map (MulAut.conj h).toMonoidHom ≤ M := fun y hy => ((hAh hy).2).2
    have hhM : h ∈ M := mem_of_map_conj_le ctx.maxLocal hAU hAhM
    set B : Subgroup G := (N ⊓ L).map M.subtype with hB
    have hBrk : CFSG.Open.pRank 3 B ≤ 1 := by
      rw [hB, ← CFSG.RankThreeEvenClassification.Helpers.pRank_eq_of_subgroup_equiv 3
        Nat.prime_three _ _ ((N ⊓ L).equivMapOfInjective M.subtype M.subtype_injective)]
      exact hrk
    have hcyc : ∀ X : Subgroup G, X ≤ B → IsPGroup 3 X → IsCyclic X := by
      intro X hXB hXp
      by_contra hnc
      have h2 := CFSG.LocalAnalysis.RankThreeTheoremC.two_le_pRank_of_not_isCyclic
        Nat.prime_three (by norm_num) hXp hnc
      have h3' := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hXB
      omega
    have hAB : A ≤ B := hAL''.trans (Subgroup.map_mono hL'I)
    have hA'B : A.map (MulAut.conj h).toMonoidHom ≤ B := by
      intro y hy
      have hyN : y ∈ N.map M.subtype := by
        rw [← hInf]
        exact (hAh hy).2
      have hyL : y ∈ L.map M.subtype := by
        obtain ⟨a, ha, rfl⟩ := hy
        obtain ⟨ax, hax, rfl⟩ := ha
        have := hLn.conj_mem ax (hL'L (hAXL' hax)) ⟨h, hhM⟩
        exact ⟨_, this, by simp [MulAut.conj_apply]⟩
      rw [hB, Subgroup.map_inf _ _ _ M.subtype_injective]
      exact ⟨hyN, hyL⟩
    have hA'3 : Nat.card (A.map (MulAut.conj h).toMonoidHom) = 3 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj h).injective]
      exact hA3
    exact CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.eq_of_card_three_of_le_normalizer hcyc hAB
      hA'B hA3 hA'3 (fun y hy => (hAh hy).1)
  have hH3' : CFSG.Open.pRank 3 H ≤ 3 := hHdef ▸ hH3
  obtain ⟨S, hS, hSM, hSN⟩ :=
    hO89 H hH2 hH3' (L'.map M.subtype) hLle hcomp' hrkL' hLq' A hAL'' hA3 hAU hweak
  have hfin := normalizer_inf_le_of_sylow ctx.sylow hTH hS hSM hSN
  exact ctx.notLe fun y hy => hfin (Subgroup.mem_inf.mpr ⟨hy, hND hy⟩)

end GLevel

end false_of_A8_L5_aux

theorem false_of_A8_L5_gen (k1525d : K1525d) {G : Type} [Group G]
    [Finite G] {M T : Subgroup G} (hO89 : O89At G M) {T₁ T₂ : Subgroup ↥M}
    (ctx : S15CtxGen G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    (hLn : L.Normal) (hbig : Nonempty (↥Ls ≃* alternatingGroup (Fin 8)) ∨ IsL5Two ↥Ls)
    (hQ : ∀ Ti : Subgroup ↥M, (Ti = T₁ ∨ Ti = T₂) →
      CFSG.Open.pRank 3 (Subgroup.normalizer (Ti : Set ↥M) ⊓ L) ≤ 1)
    (hU : ∀ A : Subgroup ↥M, A ≤ L → Nat.card A = 3 → A.map M.subtype ∈ uniqueSet M) : False := by
  have hg : GNGood (T.subgroupOf M) T₁ T₂ := ctx.good
  have hbig' : Big1525 ↥Ls := by
    rcases hbig with hA8 | hL5
    · exact Or.inr (Or.inl hA8)
    · exact Or.inr (Or.inr (Or.inl (isL5Two_iff_isLinTwo_five.1 hL5)))
  have hLs2 : 2 ≤ CFSG.Open.pRank 3 Ls := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact exists_E9_of_order_three_aux_big hbig'
  have hL2 : 2 ≤ CFSG.Open.pRank 3 L := by
    have h1 : 2 ≤ CFSG.Open.pRank 3 (L.map (toStar (T.subgroupOf M))) := by
      rw [hL.2]
      exact hLs2
    exact two_le_pRank_of_map (toStar (T.subgroupOf M)) Nat.prime_three (by norm_num) L h1
  have hM3 : 2 ≤ CFSG.Open.pRank 3 M := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hL2.trans (CFSG.SectionRank.pRank_mono (by norm_num) le_top)
  obtain ⟨hT₁'T, hT₁'char⟩ := map_subtype_characteristic ctx.sylow.le
    (ctx.pair.le_center.trans (omegaOneCenterOf_le_subgroup _)) ctx.pair.char₁
  obtain ⟨hT₂'T, hT₂'char⟩ := map_subtype_characteristic ctx.sylow.le
    ctx.pair.le₂ ctx.pair.char₂
  have hT₁'ne : T₁.map M.subtype ≠ ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (H := T₁) (f := M.subtype)
      M.subtype_injective).not.mpr ctx.pair.ne_bot₁
  have hT₂'ne : T₂.map M.subtype ≠ ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (H := T₂) (f := M.subtype)
      M.subtype_injective).not.mpr ctx.pair.ne_bot₂
  have hH3₁ : CFSG.Open.pRank 3
      (Subgroup.normalizer ((T₁.map M.subtype : Subgroup G) : Set G)) ≤ 3 :=
    S15CtxGen.pRank_three_normalizer_le_three ctx hM3 hT₁'ne hT₁'T hT₁'char
  have hH3₂ : CFSG.Open.pRank 3
      (Subgroup.normalizer ((T₂.map M.subtype : Subgroup G) : Set G)) ≤ 3 :=
    S15CtxGen.pRank_three_normalizer_le_three ctx hM3 hT₂'ne hT₂'T hT₂'char
  have hsl₁ : gnA (T.subgroupOf M) T₁ Ls ≤
      (Subgroup.normalizer (T₁ : Set ↥M) ⊓ L).map (toStar (T.subgroupOf M)) :=
    gnA_le_map_normalizer_one hg hL
  have hsl₂ : gnA (T.subgroupOf M) T₂ Ls ≤
      (Subgroup.normalizer (T₂ : Set ↥M) ⊓ L).map (toStar (T.subgroupOf M)) :=
    gnA_le_map_normalizer_two_of_A8_L5 ctx.gn hg hL hLn hbig
  have hrank : ∀ Ti : Subgroup ↥M, (Ti = T₁ ∨ Ti = T₂) →
      gnA (T.subgroupOf M) Ti Ls ≤
        (Subgroup.normalizer (Ti : Set ↥M) ⊓ L).map (toStar (T.subgroupOf M)) →
      CFSG.Open.pRank 3 (gnA (T.subgroupOf M) Ti Ls) ≤ 1 := by
    intro Ti hTi hsl
    have h1 : CFSG.Open.pRank 3 (gnA (T.subgroupOf M) Ti Ls) ≤
        CFSG.Open.pRank 3 ((Subgroup.normalizer (Ti : Set ↥M) ⊓ L).map
          (toStar (T.subgroupOf M))) := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hsl
    by_contra hcon
    have h2 : 2 ≤ CFSG.Open.pRank 3 ((Subgroup.normalizer (Ti : Set ↥M) ⊓ L).map
        (toStar (T.subgroupOf M))) := by omega
    have h3 := two_le_pRank_of_map (toStar (T.subgroupOf M)) Nat.prime_three (by norm_num) _ h2
    have h4 := hQ Ti hTi
    omega
  have hLsN : Ls.Normal := by
    rw [← hL.2]
    exact Subgroup.Normal.map hLn _ (QuotientGroup.mk'_surjective _)
  have hnorm : gnImg (T.subgroupOf M) (T.subgroupOf M) ≤ Subgroup.normalizer (Ls : Set _) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hLsN]
    exact le_top
  rcases k1525d ↥M (T.subgroupOf M) T₁ T₂ ctx.gn.sylow ctx.gnParabolic Ls hLs.1 hnorm hbig
      (hrank T₁ (Or.inl rfl) hsl₁) (hrank T₂ (Or.inr rfl) hsl₂) with hmod | hmod
  · obtain ⟨L', hL'I, hcomp, -, hLq⟩ :=
      false_of_A8_L5_aux.exists_threeComponent_of_gnA' K3DvdL3_holds ctx.gn hLs.1 hL hLn hsl₁ hmod
    exact false_of_A8_L5_aux.false_of_threeComponent_O89_gen hO89 ctx ctx.pair.ne_bot₁
      (ctx.pair.le_center.trans (omegaOneCenterOf_le_subgroup _)) ctx.pair.char₁ hLn
      (hQ T₁ (Or.inl rfl)) hU hL'I hcomp hLq hH3₁
  · obtain ⟨L', hL'I, hcomp, -, hLq⟩ :=
      false_of_A8_L5_aux.exists_threeComponent_of_gnA' K3DvdL3_holds ctx.gn hLs.1 hL hLn hsl₂ hmod
    exact false_of_A8_L5_aux.false_of_threeComponent_O89_gen hO89 ctx ctx.pair.ne_bot₂ ctx.pair.le₂
      ctx.pair.char₂ hLn (hQ T₂ (Or.inr rfl)) hU hL'I hcomp hLq hH3₂

end CFSG.LocalAnalysis.RankThreeUC.S15
