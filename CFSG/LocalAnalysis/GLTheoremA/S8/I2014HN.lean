module

public import CFSG.LocalAnalysis.GLTheoremA.S8.I2014Core
public import CFSG.LocalAnalysis.GLTheoremA.S8.I1423HN
public import CFSG.Sporadic.HNSchreier.FullAut
public import CFSG.Sporadic.HNSchreier.Intrinsic
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.Parity
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt73
public import Certificates.Certificate431002

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.HNRows

open Equiv Equiv.Perm CFSG.Sporadic.HNSchreier CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA
open scoped Pointwise commutatorElement


@[expose] def HNData (Y : Type) [Group Y] (s₁ s₃ : Y) (L : Subgroup Y)
    (ψ : alternatingGroup (Fin 9) →* Y) : Prop :=
  Function.Injective ψ ∧ ψ.range = L ∧
    (∀ d : Y, orderOf d = 3 → IsConj s₁ d ∨ IsConj s₃ d) ∧
    Nat.card (Subgroup.centralizer ({s₃} : Set Y)) = 29160 ∧
    Subgroup.centralizer ({s₁} : Set Y) = Subgroup.zpowers s₁ ⊔ L ∧
    Subgroup.zpowers s₁ ⊓ L = ⊥ ∧ (∀ l ∈ L, l * s₁ = s₁ * l) ∧
    ⁅Subgroup.centralizer ({s₁} : Set Y), Subgroup.centralizer ({s₁} : Set Y)⁆ = L ∧
    orderOf s₁ = 3

theorem HNData.of_iso {Y Q : Type} [Group Y] [Group Q] (e : Y ≃* Q) {s₁ s₃ : Q} {L : Subgroup Q}
    {ψ : alternatingGroup (Fin 9) →* Q} (h : HNData Q s₁ s₃ L ψ) :
    HNData Y (e.symm s₁) (e.symm s₃) (L.map e.symm.toMonoidHom) (e.symm.toMonoidHom.comp ψ) := by
  obtain ⟨hψ, hψr, hcls, hc3, hC1, hinf, hLs, hcom, hs1⟩ := h
  have hC : ∀ q : Q, Subgroup.centralizer ({e.symm q} : Set Y) =
      (Subgroup.centralizer ({q} : Set Q)).map e.symm.toMonoidHom := fun q =>
    CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.centralizer_map_equiv e.symm q
  refine ⟨e.symm.injective.comp hψ, by rw [MonoidHom.range_comp, hψr], fun d hd => ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · have hd' : orderOf (e d) = 3 := by rw [MulEquiv.orderOf_eq]; exact hd
    rcases hcls (e d) hd' with h | h
    · left
      obtain ⟨c, hc⟩ := isConj_iff.1 h
      exact isConj_iff.2 ⟨e.symm c, by rw [← map_mul, ← map_inv, ← map_mul, hc,
        MulEquiv.symm_apply_apply]⟩
    · right
      obtain ⟨c, hc⟩ := isConj_iff.1 h
      exact isConj_iff.2 ⟨e.symm c, by rw [← map_mul, ← map_inv, ← map_mul, hc,
        MulEquiv.symm_apply_apply]⟩
  · rw [hC, Subgroup.card_map_of_injective e.symm.injective, hc3]
  · rw [hC, hC1, Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  · have : (Subgroup.zpowers (e.symm s₁) : Subgroup Y) = (Subgroup.zpowers s₁).map e.symm.toMonoidHom := by
      rw [MonoidHom.map_zpowers]; rfl
    rw [this, ← Subgroup.map_inf _ _ _ e.symm.injective, hinf, Subgroup.map_bot]
  · rintro _ ⟨l, hl, rfl⟩
    show e.symm l * e.symm s₁ = e.symm s₁ * e.symm l
    rw [← map_mul, ← map_mul, hLs l hl]
  · rw [hC, ← Subgroup.map_commutator, hcom]
  · rw [MulEquiv.orderOf_eq]; exact hs1

theorem i2014_of_data {Y : Type} [Group Y] [Finite Y] (hc : A9.A9Fact) {s₁ s₃ : Y}
    {L : Subgroup Y} {ψ : alternatingGroup (Fin 9) →* Y} (hD : HNData Y s₁ s₃ L ψ)
    {I R : Subgroup Y} (hIL : I ≤ L) (eI : I ≃* alternatingGroup (Fin 8)) (hR : IsPGroup 2 R)
    (hIR : I ≤ Subgroup.normalizer (R : Set Y)) (hsR : s₁ ∈ Subgroup.normalizer (R : Set Y)) :
    I ≤ Subgroup.centralizer (R : Set Y) :=
  i2014_core hc hD.1 hD.2.1 hD.2.2.1 hD.2.2.2.1 hD.2.2.2.2.1 hD.2.2.2.2.2.1 hD.2.2.2.2.2.2.1
    hD.2.2.2.2.2.2.2.1 hD.2.2.2.2.2.2.2.2 hIL eI hR hIR hsR

theorem exists_inner_of_pow_three {Y : Type} [Group Y] [Finite Y] (hZ : Subgroup.center Y = ⊥)
    (hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y) ∣ 2)
    (α : MulAut Y) (hα : α ^ 3 = 1) : ∃ k : Y, α = MulAut.conj k ∧ k ^ 3 = 1 := by
  have hinn : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner Y := by
    set ψ : CFSG.ComponentClassification.OuterAutomorphisms.Outer Y := QuotientGroup.mk α
    have h1 : orderOf ψ ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one])
    have h2 : orderOf ψ ∣ 2 := (orderOf_dvd_natCard ψ).trans hOut
    have h3 : orderOf ψ = 1 := by
      have := Nat.dvd_gcd h1 h2
      simpa using this
    rw [orderOf_eq_one_iff] at h3
    exact (QuotientGroup.eq_one_iff α).mp h3
  obtain ⟨k, rfl⟩ := hinn
  refine ⟨k, rfl, ?_⟩
  have h : MulAut.conj (k ^ 3) = 1 := by rw [map_pow]; exact hα
  have hc : k ^ 3 ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut Y => φ g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * k ^ 3 = k ^ 3 * g * (k ^ 3)⁻¹ * k ^ 3 := by rw [this]
      _ = k ^ 3 * g := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc

theorem fixSubgroup_conj {Y : Type} [Group Y] (k : Y) :
    CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj k) =
      Subgroup.centralizer ({k} : Set Y) := by
  ext x
  rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup, MulAut.conj_apply,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * k = k * x * k⁻¹ * k := by rw [h]
      _ = k * x := by group
  · intro h
    rw [← h]
    group


theorem simple_of_equiv {Y Q : Type} [Group Y] [Group Q] (e : Y ≃* Q) (h : IsSimpleGroup Q) :
    IsSimpleGroup Y := (MulEquiv.isSimpleGroup_congr e).2 h

theorem card_outer_of_equiv {Y Q : Type} [Group Y] [Group Q] (e : Y ≃* Q) :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y) =
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Q) :=
  CFSG.SignalizerFunctorTheorem.CatalogBridge.card_outer_eq_of_mulEquiv e


theorem bar_core {Y : Type} [Group Y] [Finite Y] (hc : A9.A9Fact) {s₁ s₃ : Y}
    {L : Subgroup Y} {ψ : alternatingGroup (Fin 9) →* Y} (hD : HNData Y s₁ s₃ L ψ) {k : Y}
    (hko : orderOf k = 3) {Jb Ib Sb : Subgroup Y}
    (hJb : GLAPComponent 3 (Subgroup.centralizer ({k} : Set Y)) Jb)
    (eJb : PQuot 3 Jb ≃* alternatingGroup (Fin 9)) (eIb : PQuot 3 Ib ≃* alternatingGroup (Fin 8))
    (hIbJb : Ib ≤ Jb) (hSb : IsPGroup 2 Sb) (hIbN : Ib ≤ Subgroup.normalizer (Sb : Set Y))
    (hkN : k ∈ Subgroup.normalizer (Sb : Set Y)) :
    Ib ≤ Subgroup.centralizer (Sb : Set Y) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hcJb : 181440 ∣ Nat.card Jb := by
    rw [← card_of_equiv_alt9 eJb]
    have := Subgroup.index_dvd_card (GLAPPrimeCore 3 ↥Jb)
    simpa [Subgroup.index] using this
  rcases hD.2.2.1 k hko with h3A | h3B
  · obtain ⟨g, hg⟩ := isConj_iff.1 h3A
    set c : Y →* Y := (MulAut.conj g⁻¹).toMonoidHom with hcdef
    have hcinj : Function.Injective c := (MulAut.conj g⁻¹).injective
    have hcomk : ⁅Subgroup.centralizer ({k} : Set Y), Subgroup.centralizer ({k} : Set Y)⁆ =
        L.map (MulAut.conj g).toMonoidHom := by
      rw [← hg, centralizer_conj, ← Subgroup.map_commutator, hD.2.2.2.2.2.2.2.1]
    have hJbL : Jb ≤ L.map (MulAut.conj g).toMonoidHom := by
      rw [← glaPComponent_perfect hJb, ← hcomk]
      exact Subgroup.commutator_mono hJb.1 hJb.1
    have hmapc : ∀ A : Subgroup Y, (A.map (MulAut.conj g).toMonoidHom).map c = A := by
      intro A
      rw [Subgroup.map_map]
      have : c.comp (MulAut.conj g).toMonoidHom = MonoidHom.id _ := by
        ext x
        simp only [hcdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          MonoidHom.id_apply]
        group
      rw [this, Subgroup.map_id]
    have hIbL : Ib.map c ≤ L := by
      rw [← hmapc L]
      exact Subgroup.map_mono (hIbJb.trans hJbL)
    have hcL : Nat.card L = 181440 := by
      rw [← hD.2.1, ← Nat.card_congr (MonoidHom.ofInjective hD.1).toEquiv]
      exact card_of_equiv_alt9 (MulEquiv.refl _)
    have hcLg : Nat.card (L.map (MulAut.conj g).toMonoidHom) = 181440 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcL]
    have hIdvd : Nat.card Ib ∣ 181440 := hcLg ▸ Subgroup.card_dvd_of_le (hIbJb.trans hJbL)
    have hIcard : Nat.card Ib = Nat.card (GLAPPrimeCore 3 ↥Ib) * 20160 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore 3 ↥Ib)]
      rw [show Nat.card (↥Ib ⧸ GLAPPrimeCore 3 ↥Ib) = 20160 from card_of_equiv_alt8 eIb, mul_comm]
    have hcore : GLAPPrimeCore 3 ↥Ib = ⊥ := by
      have hdvd9 : Nat.card (GLAPPrimeCore 3 ↥Ib) ∣ 3 ^ 2 := by
        have h1 : Nat.card (GLAPPrimeCore 3 ↥Ib) * 20160 ∣ 9 * 20160 := by
          rw [← hIcard]; exact hIdvd
        exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h1
      have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥Ib)) :=
        CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥Ib)
      have h1 : Nat.card (GLAPPrimeCore 3 ↥Ib) = 1 := by
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp3).1 hdvd9
        rcases j with _ | j
        · simpa using hj
        · exfalso
          rw [hj] at hcop
          have := Nat.Coprime.coprime_dvd_right (dvd_pow_self 3 (Nat.succ_ne_zero j)) hcop
          norm_num at this
      exact Subgroup.card_eq_one.1 h1
    have eIb' : Ib ≃* alternatingGroup (Fin 8) :=
      ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot).symm.trans eIb
    have eI'' : ↥(Ib.map c) ≃* alternatingGroup (Fin 8) :=
      (Ib.equivMapOfInjective c hcinj).symm.trans eIb'
    have hck : c k = s₁ := by
      rw [← hg]
      simp only [hcdef, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hsN : s₁ ∈ Subgroup.normalizer ((Sb.map c : Subgroup Y) : Set Y) :=
      hck ▸ Subgroup.le_normalizer_map c ⟨k, hkN, rfl⟩
    have key := i2014_of_data hc hD hIbL eI'' (hSb.map c)
      ((Subgroup.map_mono hIbN).trans (Subgroup.le_normalizer_map c)) hsN
    intro i hi
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have := (Subgroup.mem_centralizer_iff.1 (key ⟨i, hi, rfl⟩)) (c t) ⟨t, ht, rfl⟩
    apply hcinj
    rw [map_mul, map_mul]
    exact this
  · obtain ⟨g, hg⟩ := isConj_iff.1 h3B
    have hCk : Nat.card (Subgroup.centralizer ({k} : Set Y)) = 29160 := by
      rw [← hg, centralizer_conj, Subgroup.card_map_of_injective (MulAut.conj g).injective,
        hD.2.2.2.1]
    have := (hcJb.trans (Subgroup.card_dvd_of_le hJb.1))
    rw [hCk] at this
    norm_num at this


@[expose] noncomputable def psiJ : alternatingGroup (Fin 9) →* JH :=
  iotaA.comp (alt3.subtype.comp alt9Equiv.toMonoidHom)

set_option maxRecDepth 20000 in
theorem hnData_JH : HNData JH (sJ 0) (sJ 2) L1J psiJ := by
  have hinj : Function.Injective psiJ :=
    iotaA_injective.comp (alt3.subtype_injective.comp alt9Equiv.injective)
  have hrange : psiJ.range = L1J := by
    ext x
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨(alt9Equiv σ : alt3), (alt9Equiv σ).2, rfl⟩
    · rintro ⟨τ, hτ, rfl⟩
      refine ⟨alt9Equiv.symm ⟨τ, hτ⟩, ?_⟩
      show iotaA ((alt9Equiv (alt9Equiv.symm ⟨τ, hτ⟩) : alt3) : alternatingGroup (Fin 12)) = iotaA τ
      rw [MulEquiv.apply_symm_apply]
  obtain ⟨h1, h2, h3⟩ := CJ_s1_structure
  exact ⟨hinj, hrange, fun d hd => (order_three_classes d).1 hd, card_CJ_s3, h1, h2, h3,
    commutator_CJ_s1, orderOf_sJ (by norm_num)⟩


variable {G : Type} [Group G] [Finite G]

theorem subgroupOf_le_normalizer {H A B : Subgroup G} (hA : A ≤ Subgroup.normalizer (B : Set G)) :
    A.subgroupOf H ≤ Subgroup.normalizer ((B.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.1 (hA ha) x

theorem card_pQuot_of_comp_top {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (h3 : 3 ∣ Nat.card Y) {J : Subgroup Y} (hJ : GLAPComponent 3 ⊤ J) :
    J = ⊥ ∨ Nat.card (PQuot 3 J) = Nat.card Y := by
  by_cases hJt : J = ⊤
  · right
    subst hJt
    haveI : IsSimpleGroup (⊤ : Subgroup Y) := Subgroup.topEquiv.symm.isSimpleGroup_congr.1 inferInstance
    rw [Nat.card_congr (pQuotEquivSelf (⊤ : Subgroup Y)
      (by rw [Subgroup.card_top]; exact h3)).toEquiv, Subgroup.card_top]
  · left
    obtain ⟨M, hJM, -, hMne, hMn, -⟩ := isSubnormal_exists_normal hJ.2.1 hJt
    have hMnorm : M.Normal := by
      have h1 := (Subgroup.normal_subgroupOf_iff_le_normalizer (le_top : M ≤ ⊤)).1 hMn
      exact Subgroup.normalizer_eq_top_iff.1 (eq_top_iff.2 h1)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with h | h
    · exact eq_bot_iff.2 (h ▸ hJM)
    · exact absurd h hMne


set_option maxRecDepth 20000 in
theorem facts_of_equiv_JH {Y : Type} [Group Y] [Finite Y] (e : Y ≃* JH) :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y) = 2 ∧
      Nat.card Y = 273030912000000 ∧ IsSimpleGroup Y := by
  exact ⟨(@card_outer_of_equiv Y JH _ inferInstance e).trans card_outer,
    (Nat.card_congr e.toEquiv).trans card_JH, @simple_of_equiv Y JH _ inferInstance e jh_simple⟩

set_option maxRecDepth 20000 in
theorem i2014_bar (hc : A9.A9Fact) {X K J I S : Subgroup G} {d : G}
    (hK : GLAPComponent 3 X K) (hcat : catalogIs (PSimple 3 K) (S8.sporIs .HN))
    (hdN : d ∈ Subgroup.normalizer (K : Set G)) (hd3 : d ^ 3 = 1)
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({d} : Set G)) J) (hJt : IsAltPType 3 J 9)
    (hIJ : I ≤ J) (hIt : IsAltPType 3 I 8) (hSK : S ≤ K) (hS : IsPGroup 2 S)
    (hIS : I ≤ Subgroup.normalizer (S : Set G)) (hdS : d ∈ Subgroup.normalizer (S : Set G)) :
    imageMod 3 K I ≤ Subgroup.centralizer ((imageMod 3 K S : Subgroup (PQuot 3 K)) : Set (PQuot 3 K)) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  obtain ⟨hZ, ⟨ψ⟩⟩ := nonempty_pquot_equiv_HN hK hcat
  let e : PQuot 3 K ≃* JH := ψ.trans hnEquivJ
  obtain ⟨hOut2, hcY, hYs⟩ := facts_of_equiv_JH e
  have hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (PQuot 3 K)) ∣ 2 := by
    rw [hOut2]
  set α := CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨d, hdN⟩ with hαdef
  have hα : α ^ 3 = 1 := by
    have : (⟨d, hdN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 := Subtype.ext hd3
    rw [hαdef, ← map_pow, this, map_one]
  obtain ⟨k, hαk, hk3⟩ := exists_inner_of_pow_three hZ hOut α hα
  have hdp : IsPGroup 3 (Subgroup.zpowers d) := isPGroup_zpowers_of_pow_eq_one hd3
  have hJb := glaPComponent_map_pQuotHom hp3 hdN hdp hJ
  rw [← hαdef, hαk, fixSubgroup_conj] at hJb
  set Jb : Subgroup (PQuot 3 K) := (J.subgroupOf K).map (pQuotHom 3 K) with hJbdef
  set Ib : Subgroup (PQuot 3 K) := imageMod 3 K I with hIbdef
  set Sb : Subgroup (PQuot 3 K) := imageMod 3 K S with hSbdef
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hIK : I ≤ K := hIJ.trans hJK
  obtain ⟨eJ⟩ := hJt
  obtain ⟨eI⟩ := hIt
  obtain ⟨eJ'⟩ := nonempty_pQuot_equiv_imageMod hp3 hJK
  obtain ⟨eI'⟩ := nonempty_pQuot_equiv_imageMod hp3 hIK
  have eJb : PQuot 3 Jb ≃* alternatingGroup (Fin 9) := eJ'.symm.trans eJ
  have eIb : PQuot 3 Ib ≃* alternatingGroup (Fin 8) := eI'.symm.trans eI
  have hcJb : 181440 ∣ Nat.card Jb := by
    rw [← card_of_equiv_alt9 eJb]
    have := Subgroup.index_dvd_card (GLAPPrimeCore 3 ↥Jb)
    simpa [Subgroup.index] using this
  have hk1 : k ≠ 1 := by
    intro h1
    rw [h1, Subgroup.centralizer_singleton_one] at hJb
    rcases card_pQuot_of_comp_top (by rw [hcY]; norm_num) hJb with h | h
    · have : Nat.card Jb = 1 := by rw [h, Subgroup.card_bot]
      rw [this] at hcJb
      norm_num at hcJb
    · rw [card_of_equiv_alt9 eJb, hcY] at h
      norm_num at h
  have hko : orderOf k = 3 := orderOf_eq_prime hk3 hk1
  have hD := @HNData.of_iso (PQuot 3 K) JH _ inferInstance e _ _ _ _ hnData_JH
  have hSb : IsPGroup 2 Sb :=
    (hS.comap_of_injective K.subtype K.subtype_injective).map _
  have hIbN : Ib ≤ Subgroup.normalizer (Sb : Set (PQuot 3 K)) :=
    (Subgroup.map_mono (subgroupOf_le_normalizer hIS)).trans (Subgroup.le_normalizer_map _)
  have hkN : k ∈ Subgroup.normalizer (Sb : Set (PQuot 3 K)) := by
    refine mem_normalizer_of_conj_le fun x hx => ?_
    obtain ⟨s', hs', rfl⟩ := hx
    have h1 : k * QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) s' * k⁻¹ =
        α (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) s') := by rw [hαk]; rfl
    rw [h1, hαdef, QuotientGroup.mk'_apply, CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk]
    refine ⟨K.normalizerMonoidHom ⟨d, hdN⟩ s', ?_, rfl⟩
    show ((K.normalizerMonoidHom ⟨d, hdN⟩ s' : ↥K) : G) ∈ S
    rw [chev_coe_normalizerMonoidHom]
    exact (Subgroup.mem_normalizer_iff.1 hdS s').1 hs'
  have hIbJb : Ib ≤ Jb := Subgroup.map_mono (fun x hx => hIJ hx)
  exact bar_core hc hD hko hJb eJb eIb hIbJb hSb hIbN hkN

theorem i2014UsedAt_holds (G : Type) [Group G] [Finite G] :
    S8.L83.I2014UsedAt G := by
  intro X K J I S d hK hcat hdN hd3 hJ hJt hIJ hIt hSK hS hIS hdS
  have hbar := i2014_bar Certificates.certificate431002 hK hcat hdN hd3 hJ hJt hIJ hIt hSK hS hIS hdS
  have hIK : I ≤ K := hIJ.trans (hJ.1.trans inf_le_left)
  rw [Subgroup.commutator_le]
  intro s hs i hi
  have hsK : s ∈ K := hSK hs
  have hiK : i ∈ K := hIK hi
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)
  have hcomm := (Subgroup.mem_centralizer_iff.1 (hbar ⟨⟨i, hiK⟩, hi, rfl⟩)) (π ⟨s, hsK⟩)
    ⟨⟨s, hsK⟩, hs, rfl⟩
  have hπ : π ⁅(⟨s, hsK⟩ : ↥K), ⟨i, hiK⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hπ
  exact ⟨_, hπ, rfl⟩

theorem catalogIs_sporIs_of_isSporType {G : Type} [Group G] {K : Subgroup G}
    (h : IsSporType 3 K .HN) : catalogIs (PSimple 3 K) (S8.sporIs .HN) := by
  obtain ⟨i, hi, he⟩ := h
  cases i with
  | sporadic s =>
    have hs : s = .HN := hi
    subst hs
    exact ⟨_, rfl, he⟩
  | _ => exact absurd hi (by simp [isSporIdx])

theorem i2014At_holds (G : Type) [Group G] [Finite G] :
    I2014At G := by
  intro X K J I R y _ hK hsp hyN hy3 _ hJ hJt hIJ hIt hRK hR hIR hyR
  exact i2014_bar Certificates.certificate431002 hK (catalogIs_sporIs_of_isSporType hsp) hyN hy3 hJ hJt hIJ hIt hRK hR hIR hyR

end CFSG.LocalAnalysis.GLTheoremA.S8.HNRows
