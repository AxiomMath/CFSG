module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveRankTools
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveFaithful

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding

section Cores

variable {Y : Type*} [Group Y]

theorem map_pCore_le_pCore_of_normal {p : ℕ} (C : Subgroup Y) [C.Normal] :
    (CFSG.pCore p ↥C).map C.subtype ≤ CFSG.pCore p Y := by
  have hn : ((CFSG.pCore p ↥C).map C.subtype).Normal := ⟨fun n hn g => by
    obtain ⟨x, hx, rfl⟩ := hn
    refine ⟨MulAut.conjNormal g x, ?_, ?_⟩
    · have := CFSG.pCore_map_iso p (MulAut.conjNormal g : ↥C ≃* ↥C)
      rw [← this]
      exact ⟨x, hx, rfl⟩
    · rfl⟩
  exact le_sSup ⟨hn, IsPGroup.map CFSG.pCore_isPGroup C.subtype⟩

theorem map_pPrimeCore_two_le_of_normal [Finite Y] (C : Subgroup Y) [C.Normal] :
    (CFSG.pPrimeCore 2 ↥C).map C.subtype ≤ CFSG.pPrimeCore 2 Y := by
  have hK : ((CFSG.pPrimeCore 2 ↥C).map C.subtype).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have hc := (CFSG.pPrimeCore_characteristic (p := 2) (G := ↥C)).fixed
      (MulAut.conjNormal g)
    have : ((MulAut.conjNormal g) y : ↥C) ∈ CFSG.pPrimeCore 2 ↥C := by
      have h2 : y ∈ (CFSG.pPrimeCore 2 ↥C).comap (MulAut.conjNormal g).toMonoidHom := by
        rw [hc]
        exact hy
      exact h2
    exact ⟨_, this, by simp [MulAut.conjNormal_apply]⟩
  refine le_sSup ⟨hK, ?_⟩
  rw [Subgroup.card_map_of_injective C.subtype_injective]
  exact CFSG.pPrimeCore_coprime_card

end Cores

section Centralizer

variable {Y : Type*} [Group Y] [Finite Y]

theorem centralizer_pPrimeCore_two_le (hO2 : CFSG.pCore 2 Y = ⊥)
    (hE : ∀ L : Subgroup Y, ¬ IsComponentOf L ⊤) :
    Subgroup.centralizer (CFSG.pPrimeCore 2 Y : Set Y) ≤ CFSG.pPrimeCore 2 Y := by
  have : (CFSG.pPrimeCore 2 Y).Normal := CFSG.pPrimeCore_normal
  set T := Subgroup.centralizer (CFSG.pPrimeCore 2 Y : Set Y) with hT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 T) := inferInstance
  set P' : Subgroup Y := (P : Subgroup T).map T.subtype with hP'
  have hP'2 : IsPGroup 2 P' := P.isPGroup'.map _
  have hP'T : P' ≤ T := Subgroup.map_subtype_le _
  have hP'O : P' ≤ CFSG.pCore 2 Y := by
    refine le_pCore_of_le_centralizer_components hP'2 (fun L hL => (hE L hL).elim)
      fun l hl => ?_
    by_cases hl2 : l = 2
    · subst hl2
      rw [hO2]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hy
      rw [hy, one_mul, mul_one]
    · exact hP'T.trans (Subgroup.centralizer_le (pCore_le_pPrimeCore_two hl hl2))
  rw [hO2, le_bot_iff] at hP'O
  have hP1 : (P : Subgroup T) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ T.subtype_injective).mp hP'O
  have hTodd : Nat.Coprime 2 (Nat.card T) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two, ← Subgroup.index_bot, ← hP1]
    exact P.not_dvd_index
  exact le_sSup ⟨inferInstance, hTodd⟩

theorem mem_centralizer_of_pow_two_of_pPrimeCore {C : Subgroup Y} [C.Normal]
    (hO2 : CFSG.pCore 2 ↥C = ⊥) (hE : ∀ L : Subgroup ↥C, ¬ IsComponentOf L ⊤) {s : Y} {k : ℕ}
    (hs : s ^ 2 ^ k = 1)
    (hsO : ∀ x ∈ (CFSG.pPrimeCore 2 ↥C).map C.subtype, s * x * s⁻¹ = x) :
    s ∈ Subgroup.centralizer (C : Set Y) := by
  have hcen := centralizer_pPrimeCore_two_le hO2 hE
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  set c' : ↥C := ⟨s * c * s⁻¹, (inferInstance : C.Normal).conj_mem c hc s⟩ with hc'
  set c₀ : ↥C := ⟨c, hc⟩ with hc₀
  set o : ↥C := c₀⁻¹ * c' with ho
  have hoO : o ∈ CFSG.pPrimeCore 2 ↥C := by
    refine hcen (Subgroup.mem_centralizer_iff.mpr fun x hx => ?_)
    have hxs : s * (x : Y) * s⁻¹ = x := hsO _ ⟨x, hx, rfl⟩
    have hcx : c₀ * x * c₀⁻¹ ∈ CFSG.pPrimeCore 2 ↥C :=
      (CFSG.pPrimeCore_normal (p := 2) (G := ↥C)).conj_mem x hx c₀
    have h1 : s * ((c₀ * x * c₀⁻¹ : ↥C) : Y) * s⁻¹ = ((c₀ * x * c₀⁻¹ : ↥C) : Y) :=
      hsO _ ⟨_, hcx, rfl⟩
    have key : (s * c * s⁻¹) * (x : Y) * (s * c * s⁻¹)⁻¹ = c * x * c⁻¹ := by
      have h1' : s * (c * (x : Y) * c⁻¹) * s⁻¹ = c * x * c⁻¹ := by
        simpa only [hc₀, Subgroup.coe_mul, Subgroup.coe_inv] using h1
      calc (s * c * s⁻¹) * (x : Y) * (s * c * s⁻¹)⁻¹
          = (s * c * s⁻¹) * (s * (x : Y) * s⁻¹) * (s * c * s⁻¹)⁻¹ := by rw [hxs]
        _ = s * (c * (x : Y) * c⁻¹) * s⁻¹ := by group
        _ = c * x * c⁻¹ := h1'
    apply Subtype.ext
    simp only [ho, hc', hc₀, Subgroup.coe_mul, Subgroup.coe_inv]
    calc (x : Y) * (c⁻¹ * (s * c * s⁻¹)) = c⁻¹ * (c * x * c⁻¹) * (s * c * s⁻¹) := by group
      _ = c⁻¹ * ((s * c * s⁻¹) * (x : Y) * (s * c * s⁻¹)⁻¹) * (s * c * s⁻¹) := by rw [key]
      _ = c⁻¹ * (s * c * s⁻¹) * x := by group
  have hos : s * (o : Y) * s⁻¹ = o := hsO _ ⟨o, hoO, rfl⟩
  have hpow : ∀ n : ℕ, s ^ n * c * (s ^ n)⁻¹ = c * (o : Y) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hco : s * c * s⁻¹ = c * (o : Y) := by
        simp only [ho, hc', hc₀, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      have hsn : s * (o : Y) ^ n * s⁻¹ = (o : Y) ^ n := by
        rw [← conj_pow, hos]
      calc s ^ (n + 1) * c * (s ^ (n + 1))⁻¹ = s * (s ^ n * c * (s ^ n)⁻¹) * s⁻¹ := by group
        _ = (s * c * s⁻¹) * (s * (o : Y) ^ n * s⁻¹) := by rw [ih]; group
        _ = c * (o : Y) ^ (n + 1) := by rw [hco, hsn, pow_succ', mul_assoc]
  have ho1 : (o : Y) ^ 2 ^ k = 1 := by
    have := hpow (2 ^ k)
    rw [hs, one_mul, inv_one, mul_one] at this
    exact (mul_eq_left.mp this.symm)
  have hodd := CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥C)
  have hord1 : orderOf o ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using ho1))
  have hord2 : orderOf o ∣ Nat.card (CFSG.pPrimeCore 2 ↥C) := by
    rw [← Subgroup.orderOf_mk o hoO]
    exact orderOf_dvd_natCard _
  have ho1' : o = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (hodd.pow_left k) hord1 hord2)
  have : s * c * s⁻¹ = c := by
    have h := congrArg Subtype.val ho1'
    simp only [ho, hc', hc₀, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h
    calc s * c * s⁻¹ = c * (c⁻¹ * (s * c * s⁻¹)) := by group
      _ = c := by rw [h, mul_one]
  calc c * s = (s * c * s⁻¹) * s := by rw [this]
    _ = s * c := by group

end Centralizer

section Elementary

variable {Y : Type*} [Group Y] [Finite Y]

theorem not_isCyclic_of_card_sq_of_pow_eq_one {W : Type*} [Group W] {p : ℕ} (hp : p.Prime)
    (hc : Nat.card W = p ^ 2) (h : ∀ g : W, g ^ p = 1) : ¬ IsCyclic W := by
  intro hcyc
  have h1 : Monoid.exponent W ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one h
  rw [IsCyclic.exponent_eq_card, hc] at h1
  have h2 : p * p ≤ p * 1 := by
    simpa only [sq, mul_one] using Nat.le_of_dvd hp.pos h1
  exact absurd (Nat.le_of_mul_le_mul_left h2 hp.pos) (by have := hp.two_le; omega)

theorem exists_isElemAbelian_three_of_centerQuotient {V : Type*} [Group V] [Finite V]
    {Lb : Subgroup Y} (φ : ↥Lb ⧸ Subgroup.center ↥Lb ≃* V) {E : Subgroup V}
    (hE3 : IsPGroup 3 E) (hEnc : ¬ IsCyclic E) :
    ∃ E₀ : Subgroup Y, E₀ ≤ Lb ∧ IsElemAbelian 3 E₀ ∧ Nat.card E₀ = 3 ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S⟩ : Nonempty (Sylow 3 ↥Lb) := inferInstance
  set f : ↥Lb →* V := φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥Lb)) with hf
  have hfs : Function.Surjective f := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  set S' : Sylow 3 V := S.mapSurjective hfs with hS'
  obtain ⟨T, hET⟩ := hE3.exists_le_sylow
  have hTnc : ¬ IsCyclic (T : Subgroup V) := fun h => hEnc (Subgroup.isCyclic_of_le hET)
  have hS'nc : ¬ IsCyclic (S' : Subgroup V) := fun h => hTnc
    (isCyclic_of_surjective (Sylow.equiv S' T).toMonoidHom (Sylow.equiv S' T).surjective)
  have hSnc : ¬ IsCyclic (S : Subgroup ↥Lb) := fun h => hS'nc (by
    rw [hS', Sylow.coe_mapSurjective]
    exact isCyclic_of_surjective (f.subgroupMap S) (f.subgroupMap_surjective S))
  set S₀ : Subgroup Y := (S : Subgroup ↥Lb).map Lb.subtype with hS₀
  have hS₀nc : ¬ IsCyclic S₀ := fun h => hSnc (by
    have e := (Subgroup.equivMapOfInjective (S : Subgroup ↥Lb) Lb.subtype Lb.subtype_injective)
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective)
  have h2 := two_le_pRank_of_isPGroup_not_isCyclic Nat.prime_three (by decide)
    (S.isPGroup'.map Lb.subtype) hS₀nc
  obtain ⟨E₀, hE₀S, hE₀, hE₀c⟩ := exists_isElemAbelian_card_sq_of_two_le_pRank Nat.prime_three h2
  exact ⟨E₀, hE₀S.trans (Subgroup.map_subtype_le _), hE₀, hE₀c⟩

omit [Finite Y] in
theorem isPGroup_not_isCyclic_of_isElemAbelian {p : ℕ} (hp : p.Prime) {E : Subgroup Y}
    (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) : IsPGroup p E ∧ ¬ IsCyclic E :=
  ⟨fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩,
    not_isCyclic_of_card_sq_of_pow_eq_one hp hEc fun g => Subtype.ext (by simpa using hE.2 g g.2)⟩

theorem exists_isElemAbelian_card_pow_of_le_pRank {p k : ℕ} (hp : p.Prime) {B : Subgroup Y}
    (hk : k ≤ Open.pRank p B) : ∃ E ≤ B, IsElemAbelian p E ∧ Nat.card E = p ^ k := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, hAB, hA, hAcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp B
  obtain ⟨C, hC⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) p (n := k)
    (hAcard ▸ pow_dvd_pow p hk)
  have : IsMulCommutative A := hA.1
  have hC' : IsElemAbelian p C :=
    ⟨inferInstance, fun x _ => Subtype.ext (hA.2 x x.property)⟩
  refine ⟨C.map A.subtype, (Subgroup.map_subtype_le C).trans hAB,
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hC' A.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective A.subtype_injective, hC]

omit [Finite Y] in
theorem not_le_centralizer_self_of_isComponentOf {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    ¬ L ≤ Subgroup.centralizer (L : Set Y) := by
  intro hLC
  obtain ⟨a, b, hab⟩ :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hL.2.2
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hLC a.2) b b.2).symm

end Elementary

section Inner

variable {Y : Type*} [Group Y] [Finite Y]

omit [Finite Y] in
open CFSG.ComponentClassification.OuterAutomorphisms in
theorem le_sup_centralizer_of_isPGroup_of_not_dvd_outer {p : ℕ} (hp : p.Prime)
    {L E : Subgroup Y} (hE : IsPGroup p E) (hEN : E ≤ Subgroup.normalizer (L : Set Y))
    (hout : ¬ p ∣ Nat.card (Outer L)) : E ≤ L ⊔ Subgroup.centralizer (L : Set Y) := by
  intro e he
  obtain ⟨k, hk⟩ := hE ⟨e, he⟩
  have hek : e ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  set a : MulAut L := L.normalizerMonoidHom ⟨e, hEN he⟩ with ha
  have hak : a ^ p ^ k = 1 := by
    rw [ha, ← map_pow]
    have : (⟨e, hEN he⟩ : Subgroup.normalizer (L : Set Y)) ^ p ^ k = 1 :=
      Subtype.ext (by simpa using hek)
    rw [this, map_one]
  have hcop : (p ^ k).Coprime (Nat.card (Outer L)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hout)
  have hψ : QuotientGroup.mk' (inner L) a = 1 :=
    (pow_eq_one_iff_of_coprime hcop).mp
      ⟨by rw [← map_pow, hak, map_one], pow_card_eq_one'⟩
  obtain ⟨l, hl⟩ := (QuotientGroup.eq_one_iff _).mp hψ
  have hcent : (l : Y)⁻¹ * e ∈ Subgroup.centralizer (L : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hl ⟨x, hx⟩)
    change (l : Y) * x * (l : Y)⁻¹ = e * x * e⁻¹ at h1
    calc x * ((l : Y)⁻¹ * e) = (l : Y)⁻¹ * ((l : Y) * x * (l : Y)⁻¹) * e := by group
      _ = (l : Y)⁻¹ * (e * x * e⁻¹) * e := by rw [h1]
      _ = (l : Y)⁻¹ * e * x := by group
  have : e = (l : Y) * ((l : Y)⁻¹ * e) := by group
  rw [this]
  exact Subgroup.mul_mem_sup l.2 hcent

end Inner

section Rank

variable {Y : Type*} [Group Y] [Finite Y]

theorem succ_pRank_le_of_commute {q : ℕ} [Fact q.Prime] {A B C : Subgroup Y} (hAB : A ≤ B)
    (hAC : A ≤ C) {z : Y} (hzB : z ∈ B) (hz : z ^ q = 1) (hzC : z ∉ C)
    (hzA : z ∈ Subgroup.centralizer (A : Set Y)) :
    Open.pRank q A + 1 ≤ Open.pRank q B := by
  have hq : q.Prime := Fact.out
  have hz1 : z ≠ 1 := fun h1 => hzC (h1 ▸ C.one_mem)
  have hord : orderOf z = q :=
    orderOf_eq_prime hz hz1
  have hdisj : Subgroup.zpowers z ⊓ A = ⊥ := by
    have hcard : Nat.card (Subgroup.zpowers z) = q := by rw [Nat.card_zpowers, hord]
    have : Fact (Nat.card (Subgroup.zpowers z)).Prime := ⟨hcard ▸ hq⟩
    rcases ((Subgroup.zpowers z ⊓ A).subgroupOf (Subgroup.zpowers z)).eq_bot_or_eq_top_of_prime_card
      with h0 | h0
    · rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx.1⟩ : Subgroup.zpowers z) ∈
          (Subgroup.zpowers z ⊓ A).subgroupOf (Subgroup.zpowers z) := Subgroup.mem_subgroupOf.mpr hx
      rw [h0, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    · exfalso
      have : (⟨z, Subgroup.mem_zpowers z⟩ : Subgroup.zpowers z) ∈
          (Subgroup.zpowers z ⊓ A).subgroupOf (Subgroup.zpowers z) := h0 ▸ Subgroup.mem_top _
      exact hzC (hAC (Subgroup.mem_subgroupOf.mp this).2)
  exact (pRank_succ_le_sup_zpowers A hz hz1 hzA hdisj).trans
    (CFSG.PreuniquenessRankFour.Helpers.pRank_mono q hq (sup_le hAB (Subgroup.zpowers_le.mpr hzB)))

end Rank

section TwoComponents

variable {Y : Type*} [Group Y]

theorem map_conj_eq_of_two_components {A B : Subgroup Y} (hA : IsComponentOf A ⊤)
    (hB : IsComponentOf B ⊤) (hAB : A ≠ B)
    (hall : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L = A ∨ L = B) {e : Y} {q : ℕ}
    (hq : Odd q) (he : e ^ q = 1) : A.map (MulAut.conj e).toMonoidHom = A := by
  set T : Subgroup Y → Subgroup Y := fun L => L.map (MulAut.conj e).toMonoidHom with hT
  have hTc : ∀ L, IsComponentOf L ⊤ → IsComponentOf (T L) ⊤ := fun L hL =>
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj e) L).mpr hL
  have hTinj : ∀ L L', T L = T L' → L = L' := fun L L' h =>
    Subgroup.map_injective (MulAut.conj e).injective h
  have hone : (MulAut.conj (1 : Y)).toMonoidHom = MonoidHom.id Y := by
    ext x
    simp
  have hiter : ∀ n : ℕ, T^[n] A = A.map (MulAut.conj (e ^ n)).toMonoidHom := by
    intro n
    induction n with
    | zero => rw [Function.iterate_zero_apply, pow_zero, hone, Subgroup.map_id]
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [hT, Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, pow_succ', mul_assoc]
  by_contra hne
  have hTA : T A = B := (hall _ (hTc A hA)).resolve_left hne
  have hTB : T B = A := by
    rcases hall _ (hTc B hB) with h | h
    · exact h
    · exact absurd (hTinj _ _ (hTA.trans h.symm)) hAB
  have h2 : ∀ k : ℕ, T^[2 * k] A = A ∧ T^[2 * k + 1] A = B := by
    intro k
    induction k with
    | zero => exact ⟨rfl, hTA⟩
    | succ k ih =>
      have e1 : T^[2 * (k + 1)] A = T (T (T^[2 * k] A)) := by
        rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Function.iterate_succ_apply',
          Function.iterate_succ_apply']
      have e2 : T^[2 * (k + 1) + 1] A = T (T^[2 * (k + 1)] A) := Function.iterate_succ_apply' _ _ _
      rw [ih.1, hTA, hTB] at e1
      exact ⟨e1, by rw [e2, e1, hTA]⟩
  obtain ⟨k, rfl⟩ := hq
  have h3 := (h2 k).2
  rw [hiter, he, hone, Subgroup.map_id] at h3
  exact hAB h3

end TwoComponents

section Layer

variable {Y : Type*} [Group Y] [Finite Y]

theorem centralizer_layer_le_centralizer (hO2 : CFSG.pCore 2 Y = ⊥) {S : Subgroup Y}
    (hS : IsPGroup 2 S) (hSO : CFSG.pPrimeCore 2 Y ≤ Subgroup.centralizer (S : Set Y)) :
    Subgroup.centralizer (CFSG.ComponentClassification.Layer.subgroup Y : Set Y) ≤
      Subgroup.centralizer (S : Set Y) := by
  set Lay := CFSG.ComponentClassification.Layer.subgroup Y with hLay
  have : Lay.Normal := CFSG.ComponentClassification.Layer.normal Y
  set C := Subgroup.centralizer (Lay : Set Y) with hC
  have hCO2 : CFSG.pCore 2 ↥C = ⊥ := by
    have h1 := map_pCore_le_pCore_of_normal (p := 2) C
    rw [hO2, le_bot_iff] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp h1
  have hCsub : IsSubnormal C ⊤ := IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤)
  have hCE : ∀ L : Subgroup ↥C, ¬ IsComponentOf L ⊤ := by
    intro L hL
    have hLc :=
      CFSG.ComponentClassification.LocalComponents.of_subnormal_subgroup C hCsub L hL
    have h1 : L.map C.subtype ≤ Lay := CFSG.ComponentClassification.Layer.component_le hLc
    have h2 : L.map C.subtype ≤
        Subgroup.centralizer ((L.map C.subtype : Subgroup Y) : Set Y) :=
      fun x hx => Subgroup.centralizer_le h1 (Subgroup.map_subtype_le L hx)
    exact not_le_centralizer_self_of_isComponentOf hLc h2
  rw [Subgroup.le_centralizer_iff]
  intro s hs
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  have hsk : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine mem_centralizer_of_pow_two_of_pPrimeCore hCO2 hCE hsk fun x hx => ?_
  have hxS := hSO (map_pPrimeCore_two_le_of_normal C hx)
  have hsx := Subgroup.mem_centralizer_iff.mp hxS s hs
  calc s * x * s⁻¹ = x * s * s⁻¹ := by rw [hsx]
    _ = x := by group

omit [Finite Y] in
open CFSG.ComponentClassification.OuterAutomorphisms in
theorem card_le_mul_of_two_components {X : Type*} [Group X] [Finite X] {L₀ L₁ : Subgroup Y}
    (hL₀ : IsComponentOf L₀ ⊤) (hL₁ : IsComponentOf L₁ ⊤) (h01 : L₀ ≠ L₁)
    (hall : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L = L₀ ∨ L = L₁)
    (hC : ∀ x ∈ Subgroup.centralizer
      (CFSG.ComponentClassification.Layer.subgroup Y : Set Y), (orderOf x).Coprime 5)
    (hout : ¬ 5 ∣ Nat.card (Outer ↥L₀)) {U : Subgroup X}
    (φ : ↥L₀ ⧸ Subgroup.center ↥L₀ ≃* ↥U) (hX : Open.pRank 5 (⊤ : Subgroup X) ≤ 2)
    {E : Subgroup Y} (hE : IsElemAbelian 5 E) :
    Nat.card E ≤ Nat.card ↥(E ⊓ Subgroup.centralizer (L₀ : Set Y)) * 5 ^ 2 ∧
      E ⊓ Subgroup.centralizer (L₀ : Set Y) ⊓ Subgroup.centralizer (L₁ : Set Y) = ⊥ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hEp : IsPGroup 5 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  have hall' : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L = L₁ ∨ L = L₀ :=
    fun L hL => (hall L hL).symm
  have hN₀ : E ≤ Subgroup.normalizer (L₀ : Set Y) := fun e he => by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact map_conj_eq_of_two_components hL₀ hL₁ h01 hall (q := 5) (by decide) (hE.2 e he)
  have hEsup : E ≤ L₀ ⊔ Subgroup.centralizer (L₀ : Set Y) :=
    le_sup_centralizer_of_isPGroup_of_not_dvd_outer Nat.prime_five hEp hN₀ hout
  obtain ⟨ρ, hρ⟩ := exists_hom_centerQuotient L₀ E.subtype (fun e => hEsup e.2)
  set ψ : ↥E →* X := U.subtype.comp (φ.toMonoidHom.comp ρ) with hψ
  have hψker : ψ.ker = (Subgroup.centralizer (L₀ : Set Y)).subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro he1
      have h0 : ((φ (ρ e) : ↥U) : X) = 1 := he1
      have h1 : φ (ρ e) = 1 := Subtype.ext h0
      exact (hρ e).mp ((MulEquiv.map_eq_one_iff φ).mp h1)
    · intro heC
      have h1 : ρ e = 1 := (hρ e).mpr heC
      have h2 : φ (ρ e) = 1 := by
        rw [h1]
        exact φ.map_one
      exact (congrArg Subtype.val h2 : _)
  have hrange : Nat.card ψ.range ≤ 5 ^ 2 := by
    have hrp : IsPGroup 5 ψ.range := by
      rw [MonoidHom.range_eq_map]
      exact (hEp.of_equiv Subgroup.topEquiv.symm).map ψ
    have hrel : IsElemAbelian 5 ψ.range := by
      refine ⟨isMulCommutative_iff.mpr fun a b => ?_, ?_⟩
      · obtain ⟨_, ⟨x, rfl⟩⟩ := a
        obtain ⟨_, ⟨y, rfl⟩⟩ := b
        have := hE.1
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [← map_mul, ← map_mul, mul_comm' x y]
      · rintro _ ⟨x, rfl⟩
        rw [← map_pow]
        have : x ^ 5 = 1 := Subtype.ext (by simpa using hE.2 x x.2)
        rw [this, map_one]
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hrp
    have hjle : j ≤ Open.pRank 5 (⊤ : Subgroup X) :=
      (CFSG.AGLEmbeddingD2.le_pRank_of_isElemAbelian Nat.prime_five hrel hj).trans
        (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 5 Nat.prime_five le_top)
    rw [hj]
    exact Nat.pow_le_pow_right (by norm_num) (hjle.trans hX)
  set E₁ := E ⊓ Subgroup.centralizer (L₀ : Set Y) with hE₁
  have hLay : CFSG.ComponentClassification.Layer.subgroup Y ≤ L₀ ⊔ L₁ := sSup_le fun L hL =>
    (hall L hL).elim (fun h => h ▸ le_sup_left) (fun h => h ▸ le_sup_right)
  have hE₁₁ : E₁ ⊓ Subgroup.centralizer (L₁ : Set Y) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨hxE, hxC₀⟩, hxC₁⟩
    have hxC : x ∈ Subgroup.centralizer
        (CFSG.ComponentClassification.Layer.subgroup Y : Set Y) := by
      refine Subgroup.centralizer_le hLay ?_
      rw [← Subgroup.zpowers_le, ← Subgroup.le_centralizer_iff]
      refine sup_le ?_ ?_
      · rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
        exact hxC₀
      · rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
        exact hxC₁
    have h1 : orderOf x ∣ 5 := orderOf_dvd_of_pow_eq_one (hE.2 x hxE)
    have h2 : orderOf x = 1 :=
      Nat.eq_one_of_dvd_coprimes (hC x hxC) dvd_rfl h1
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h2)
  have h1 := Subgroup.card_mul_index ψ.ker
  rw [Subgroup.index_ker] at h1
  have h2 : Nat.card ψ.ker = Nat.card E₁ := by
    rw [hψker, ← Subgroup.card_map_of_injective E.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  refine ⟨?_, hE₁₁⟩
  rw [← h1, h2]
  exact Nat.mul_le_mul_left _ hrange

omit [Finite Y] in
open CFSG.ComponentClassification.OuterAutomorphisms in
theorem card_le_of_two_components {X : Type*} [Group X] [Finite X] {L₀ L₁ : Subgroup Y}
    (hL₀ : IsComponentOf L₀ ⊤) (hL₁ : IsComponentOf L₁ ⊤) (h01 : L₀ ≠ L₁)
    (hall : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L = L₀ ∨ L = L₁)
    (hC : ∀ x ∈ Subgroup.centralizer
      (CFSG.ComponentClassification.Layer.subgroup Y : Set Y), (orderOf x).Coprime 5)
    (hout : ¬ 5 ∣ Nat.card (Outer ↥L₀)) {U : Subgroup X}
    (φ : ↥L₀ ⧸ Subgroup.center ↥L₀ ≃* ↥U) (hX : Open.pRank 5 (⊤ : Subgroup X) ≤ 2)
    (h₁ : ∀ V : Subgroup Y, V ≤ Subgroup.normalizer (L₁ : Set Y) → IsElemAbelian 5 V →
      (V ⊓ Subgroup.centralizer (L₁ : Set Y)).relIndex V ≤ 5)
    {E : Subgroup Y} (hE : IsElemAbelian 5 E) : Nat.card E ≤ 5 ^ 3 := by
  have hN₁ : E ≤ Subgroup.normalizer (L₁ : Set Y) := fun e he => by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact map_conj_eq_of_two_components hL₁ hL₀ h01.symm (fun L hL => (hall L hL).symm)
      (q := 5) (by decide) (hE.2 e he)
  obtain ⟨hle, hE₁₁⟩ := card_le_mul_of_two_components hL₀ hL₁ h01 hall hC hout φ hX hE
  set E₁ := E ⊓ Subgroup.centralizer (L₀ : Set Y) with hE₁
  have hidx₁ := h₁ E₁ (inf_le_left.trans hN₁)
    (CFSG.AGLEmbeddingD2.isElemAbelian_of_le hE inf_le_left)
  have hcardE₁ : Nat.card E₁ ≤ 5 := by
    have h1 := Subgroup.card_mul_index
      ((E₁ ⊓ Subgroup.centralizer (L₁ : Set Y)).subgroupOf E₁)
    have h2 : Nat.card ((E₁ ⊓ Subgroup.centralizer (L₁ : Set Y)).subgroupOf E₁) = 1 := by
      rw [hE₁₁, Subgroup.bot_subgroupOf, Subgroup.card_bot]
    rw [h2, one_mul] at h1
    rw [← h1]
    exact hidx₁
  calc Nat.card E ≤ Nat.card ↥E₁ * 5 ^ 2 := hle
    _ ≤ 5 * 5 ^ 2 := Nat.mul_le_mul_right _ hcardE₁
    _ = 5 ^ 3 := by norm_num

end Layer

end CFSG.AGLEmbeddingD2
