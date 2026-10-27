module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L56Frame

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3 (SylowFrame)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_le_normalizer {T V : Subgroup G} (hT2 : IsPGroup 2 T) (hV2 : IsPGroup 2 V)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) {v₀ : G} (hv₀ : v₀ ∈ V)
    (hv₀N : v₀ ∉ Subgroup.normalizer (T : Set G)) :
    ∃ v ∈ V, rightConjugate T v ≤ Subgroup.normalizer (T : Set G) ∧ rightConjugate T v ≠ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 (V ⊔ T : Subgroup G) := hV2.to_sup_of_normal_left' hT2 hTV
  have : Group.IsNilpotent ↥(V ⊔ T : Subgroup G) := hR2.isNilpotent
  set R : Subgroup G := V ⊔ T with hR
  set H : Subgroup ↥R := (Subgroup.normalizer (T : Set G)).subgroupOf R with hH
  have hv₀R : v₀ ∈ R := Subgroup.mem_sup_left hv₀
  have hHtop : H < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hv₀N ?_
    have : (⟨v₀, hv₀R⟩ : ↥R) ∈ H := by rw [h]; trivial
    exact this
  have hlt : H < Subgroup.normalizer (H : Set ↥R) :=
    Group.normalizerCondition_of_isNilpotent H hHtop
  obtain ⟨n, hnN, hnH⟩ := (IsConcreteLE.lt_iff_le_and_exists.1 hlt).2
  have hnN' : ∀ h : ↥R, h ∈ H ↔ n * h * n⁻¹ ∈ H := Subgroup.mem_normalizer_iff.1 hnN
  have hnG : (n : G) ∈ T ⊔ V := by
    rw [sup_comm]
    exact n.2
  obtain ⟨t, ht, v, hv, htv⟩ := exists_mul_of_mem_sup hTV hnG
  refine ⟨v, hv, ?_, ?_⟩
  · intro s hs
    rw [mem_rightConjugate_iff] at hs
    have hyT : t * (v * s * v⁻¹) * t⁻¹ ∈ T := T.mul_mem (T.mul_mem ht hs) (T.inv_mem ht)
    have hyR : t * (v * s * v⁻¹) * t⁻¹ ∈ R := Subgroup.mem_sup_right hyT
    have hyH : (⟨t * (v * s * v⁻¹) * t⁻¹, hyR⟩ : ↥R) ∈ H := Subgroup.le_normalizer hyT
    have h1 : n⁻¹ * (⟨t * (v * s * v⁻¹) * t⁻¹, hyR⟩ : ↥R) * n ∈ H := by
      rw [hnN']
      simpa [mul_assoc] using hyH
    have hmem : (n : G)⁻¹ * (t * (v * s * v⁻¹) * t⁻¹) * n ∈ Subgroup.normalizer (T : Set G) := h1
    have e : (n : G)⁻¹ * (t * (v * s * v⁻¹) * t⁻¹) * n = s := by
      rw [← htv]
      group
    rwa [e] at hmem
  · intro hvT
    have hvN : v ∈ Subgroup.normalizer (T : Set G) := (rightConjugate_eq_self_iff T v).1 hvT
    apply hnH
    have : (n : G) ∈ Subgroup.normalizer (T : Set G) := by
      rw [← htv]
      exact (Subgroup.normalizer (T : Set G)).mul_mem (Subgroup.le_normalizer ht) hvN
    exact this

namespace CE

variable {M J : Subgroup G} (c : CE G M J)
include c

theorem inf_rightConjugate_eq_bot (hA : FooteTheoremA) {z₀ : G} (hz : ZData J z₀) {g : G}
    {T : Subgroup G} (hg : g ∉ M) (hT : ABGLocalTools.IsSylowOf 2 T (eSub J g))
    (hTJ : T ⊓ J = ⊥) {v : G}
    (hvV : v ∈ blockU J) (hvN : rightConjugate T v ≤ Subgroup.normalizer (T : Set G))
    (hne : rightConjugate T v ≠ T) : T ⊓ rightConjugate T v = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hbot
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hI2 : IsPGroup 2 ↥(T ⊓ rightConjugate T v) := hT2.to_le inf_le_left
  obtain ⟨u, huI, hu1, hu2⟩ := exists_involution_of_isPGroup hI2 hbot
  obtain ⟨huT, huTv⟩ := Subgroup.mem_inf.1 huI
  rw [mem_rightConjugate_iff] at huTv
  have hTN : T ≤ Subgroup.normalizer (J : Set G) := hT.le.trans inf_le_right
  have hcomm : ⁅v, u⁆ ∈ T ⊓ J := by
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact T.mul_mem huTv (T.inv_mem huT)
    · have h2 : u * v⁻¹ * u⁻¹ ∈ blockU J :=
        conj_mem_blockU (hTN huT) ((blockU J).inv_mem hvV)
      have : ⁅v, u⁆ = v * (u * v⁻¹ * u⁻¹) := by rw [commutatorElement_def]; group
      rw [this]
      exact blockU_le J ((blockU J).mul_mem hvV h2)
  rw [hTJ, Subgroup.mem_bot] at hcomm
  have hvu : v * u = u * v := commutatorElement_eq_one_iff_mul_comm.1 hcomm
  have hvN' := c.centralizer_blockU_le_normalizer hA hz hg (hT.le huT) hu1 hu2 hvV hvu
  have hTv : rightConjugate T v ≤ eSub J g := by
    intro y hy
    rw [mem_rightConjugate_iff] at hy
    obtain ⟨hyJg, hyNJ⟩ := Subgroup.mem_inf.1 (hT.le hy)
    have e : v⁻¹ * (v * y * v⁻¹) * v⁻¹⁻¹ = y := by group
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hvN')
        (v * y * v⁻¹)).1 hyJg
      rwa [e] at this
    · have hvNJ : v ∈ Subgroup.normalizer (J : Set G) :=
        Subgroup.le_normalizer (blockU_le J hvV)
      have h1 := (Subgroup.normalizer (J : Set G)).mul_mem
        ((Subgroup.normalizer (J : Set G)).mul_mem ((Subgroup.normalizer (J : Set G)).inv_mem hvNJ)
          hyNJ) hvNJ
      have e' : v⁻¹ * (v * y * v⁻¹) * v = y := by group
      rwa [e'] at h1
  have hTT : IsPGroup 2 (T ⊔ rightConjugate T v : Subgroup G) :=
    hT2.to_sup_of_normal_left' (hT2.map _) hvN
  have hle : T ⊔ rightConjugate T v ≤ eSub J g := sup_le hT.le hTv
  have heq := hT.eq_of_le le_sup_left hle hTT
  have hsub : rightConjugate T v ≤ T := le_sup_right.trans heq.le
  have hcard : Nat.card T ≤ Nat.card ↥(rightConjugate T v) := by
    rw [rightConjugate_card]
  exact hne (Subgroup.eq_of_le_of_card_ge hsub hcard)

theorem partC (hA : FooteTheoremA) {z₀ : G} (hz : ZData J z₀) {g : G} {T S : Subgroup G}
    (hgood : Good56 M J g) (hT : ABGLocalTools.IsSylowOf 2 T (eSub J g))
    (hmax : ∀ h, Good56 M J h →
      (Nat.card ↥(eSub J h)).factorization 2 ≤ (Nat.card ↥(eSub J g)).factorization 2)
    (hS : SylowFrame J T S) (hncent : ¬ ∀ t ∈ T, ∀ v ∈ blockU J, t * v = v * t) :
    (∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t) ∧ (∀ t ∈ T, t * t = 1) ∧
      S ⊓ Subgroup.normalizer (T : Set G) ⊓ J ≤ blockU J ∧
      Nat.card ↥(S ⊓ Subgroup.normalizer (T : Set G) ⊓ J) = Nat.card T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ := c.block
  have hg : g ∉ M := hgood.1
  have hTE : T ≤ eSub J g := hT.le
  have hTN : T ≤ Subgroup.normalizer (J : Set G) := hTE.trans inf_le_right
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hTJ : T ⊓ J = ⊥ := hS.inf_eq_bot
  have hTV : T ≤ Subgroup.normalizer (blockU J : Set G) := fun t ht =>
    mem_normalizer_blockU (hTN ht)
  obtain ⟨v₀, hv₀V, hv₀N⟩ : ∃ v ∈ blockU J, v ∉ Subgroup.normalizer (T : Set G) := by
    by_contra hcon
    push Not at hcon
    apply hncent
    intro t ht v hv
    have hvN := hcon v hv
    have hcomm : ⁅t, v⁆ ∈ T ⊓ J := by
      refine ⟨?_, ?_⟩
      · have h1 : v * t⁻¹ * v⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hvN t⁻¹).1 (T.inv_mem ht)
        have : ⁅t, v⁆ = t * (v * t⁻¹ * v⁻¹) := by rw [commutatorElement_def]; group
        rw [this]
        exact T.mul_mem ht h1
      · have h1 : t * v * t⁻¹ ∈ blockU J := conj_mem_blockU (hTN ht) hv
        rw [commutatorElement_def]
        exact blockU_le J ((blockU J).mul_mem h1 ((blockU J).inv_mem hv))
    rw [hTJ, Subgroup.mem_bot] at hcomm
    exact commutatorElement_eq_one_iff_mul_comm.1 hcomm
  obtain ⟨v, hvV, hvN, hvne⟩ :=
    exists_conj_le_normalizer hT2 hJ.isPGroup_blockU hTV hv₀V hv₀N
  have hTTv := c.inf_rightConjugate_eq_bot hA hz hg hT hTJ hvV hvN hvne
  have hvv : v * v = 1 := hJ.blockU_sq_eq_one v hvV
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  have hTN' : T ≤ Subgroup.normalizer ((rightConjugate T v : Subgroup G) : Set G) := by
    intro t ht
    have ht1 : v * t * v⁻¹ ∈ Subgroup.normalizer (T : Set G) := by
      have h0 : v⁻¹ * t * v ∈ rightConjugate T v := by
        rw [mem_rightConjugate_iff]
        have e : v * (v⁻¹ * t * v) * v⁻¹ = t := by group
        rw [e]
        exact ht
      have h := hvN h0
      have e : v⁻¹ * t * v = v * t * v⁻¹ := by rw [hvinv]
      rwa [e] at h
    rw [Subgroup.mem_normalizer_iff]
    intro s
    rw [mem_rightConjugate_iff, mem_rightConjugate_iff]
    have e : v * (t * s * t⁻¹) * v⁻¹ = (v * t * v⁻¹) * (v * s * v⁻¹) * (v * t * v⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.mem_normalizer_iff.1 ht1 (v * s * v⁻¹)
  have hcomm : ∀ t ∈ T, ∀ s ∈ rightConjugate T v, t * s = s * t := by
    intro t ht s hs
    have hsN : s ∈ Subgroup.normalizer (T : Set G) := hvN hs
    have hc : t * s * t⁻¹ * s⁻¹ ∈ T ⊓ rightConjugate T v := by
      refine ⟨?_, ?_⟩
      · have h1 : s * t⁻¹ * s⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hsN t⁻¹).1 (T.inv_mem ht)
        have : t * s * t⁻¹ * s⁻¹ = t * (s * t⁻¹ * s⁻¹) := by group
        rw [this]
        exact T.mul_mem ht h1
      · have h1 : t * s * t⁻¹ ∈ rightConjugate T v :=
          (Subgroup.mem_normalizer_iff.1 (hTN' ht) s).1 hs
        exact (rightConjugate T v).mul_mem h1 ((rightConjugate T v).inv_mem hs)
    rw [hTTv, Subgroup.mem_bot] at hc
    calc t * s = (t * s * t⁻¹ * s⁻¹) * (s * t) := by group
      _ = s * t := by rw [hc, one_mul]
  have hsTv : ∀ t ∈ T, v⁻¹ * t * v ∈ rightConjugate T v := by
    intro t ht
    rw [mem_rightConjugate_iff]
    have e : v * (v⁻¹ * t * v) * v⁻¹ = t := by group
    rw [e]
    exact ht
  have hdV : ∀ t ∈ T, t⁻¹ * (v⁻¹ * t * v) ∈ blockU J := by
    intro t ht
    have h1 : t⁻¹ * v⁻¹ * t ∈ blockU J := by
      have h := conj_mem_blockU (hTN (T.inv_mem ht)) ((blockU J).inv_mem hvV)
      simpa using h
    have e : t⁻¹ * (v⁻¹ * t * v) = (t⁻¹ * v⁻¹ * t) * v := by group
    rw [e]
    exact (blockU J).mul_mem h1 hvV
  have hTc : ∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t := by
    intro t ht t' ht'
    have hVc := hJ.blockU_comm _ (hdV t ht) _ (hdV t' ht')
    have c1 := hcomm t'⁻¹ (T.inv_mem ht') _ (hsTv t ht)
    have c2 := hcomm t⁻¹ (T.inv_mem ht) _ (hsTv t' ht')
    set s := v⁻¹ * t * v with hs
    set s' := v⁻¹ * t' * v with hs'
    have hsm : s ∈ rightConjugate T v := hsTv t ht
    have hs'm : s' ∈ rightConjugate T v := hsTv t' ht'
    have star : t⁻¹ * t'⁻¹ * (s * s') = t'⁻¹ * t⁻¹ * (s' * s) := by
      calc t⁻¹ * t'⁻¹ * (s * s') = t⁻¹ * (t'⁻¹ * s) * s' := by group
        _ = t⁻¹ * (s * t'⁻¹) * s' := by rw [c1]
        _ = t⁻¹ * s * (t'⁻¹ * s') := by group
        _ = t'⁻¹ * s' * (t⁻¹ * s) := hVc
        _ = t'⁻¹ * (s' * t⁻¹) * s := by group
        _ = t'⁻¹ * (t⁻¹ * s') * s := by rw [← c2]
        _ = t'⁻¹ * t⁻¹ * (s' * s) := by group
    have hz : t * t' * t⁻¹ * t'⁻¹ = s' * s * s'⁻¹ * s⁻¹ := by
      calc t * t' * t⁻¹ * t'⁻¹ = (t * t') * (t⁻¹ * t'⁻¹ * (s * s')) * (s * s')⁻¹ := by group
        _ = (t * t') * (t'⁻¹ * t⁻¹ * (s' * s)) * (s * s')⁻¹ := by rw [star]
        _ = s' * s * s'⁻¹ * s⁻¹ := by group
    have hzmem : t * t' * t⁻¹ * t'⁻¹ ∈ T ⊓ rightConjugate T v := by
      refine ⟨T.mul_mem (T.mul_mem (T.mul_mem ht ht') (T.inv_mem ht)) (T.inv_mem ht'), ?_⟩
      rw [hz]
      exact (rightConjugate T v).mul_mem ((rightConjugate T v).mul_mem
        ((rightConjugate T v).mul_mem hs'm hsm) ((rightConjugate T v).inv_mem hs'm))
        ((rightConjugate T v).inv_mem hsm)
    rw [hTTv, Subgroup.mem_bot] at hzmem
    calc t * t' = (t * t' * t⁻¹ * t'⁻¹) * (t' * t) := by group
      _ = t' * t := by rw [hzmem, one_mul]
  have hTs : ∀ t ∈ T, t * t = 1 := by
    intro t ht
    have hVs := hJ.blockU_sq_eq_one _ (hdV t ht)
    have c1 := hcomm t⁻¹ (T.inv_mem ht) _ (hsTv t ht)
    set s := v⁻¹ * t * v with hs
    have hss : s * s = v⁻¹ * (t * t) * v := by rw [hs]; group
    have h1 : t⁻¹ * t⁻¹ * (s * s) = 1 := by
      calc t⁻¹ * t⁻¹ * (s * s) = t⁻¹ * (t⁻¹ * s) * s := by group
        _ = t⁻¹ * (s * t⁻¹) * s := by rw [c1]
        _ = t⁻¹ * s * (t⁻¹ * s) := by group
        _ = 1 := hVs
    rw [hss] at h1
    have h2 : v⁻¹ * (t * t) * v = t * t := by
      calc v⁻¹ * (t * t) * v = (t * t) * (t⁻¹ * t⁻¹ * (v⁻¹ * (t * t) * v)) := by group
        _ = t * t := by rw [h1, mul_one]
    have hmem : t * t ∈ T ⊓ rightConjugate T v := by
      refine ⟨T.mul_mem ht ht, (mem_rightConjugate_iff T v _).2 ?_⟩
      have e : v * (t * t) * v⁻¹ = t * t := by
        calc v * (t * t) * v⁻¹ = v * (v⁻¹ * (t * t) * v) * v⁻¹ := by rw [h2]
          _ = t * t := by group
      rw [e]
      exact T.mul_mem ht ht
    rw [hTTv, Subgroup.mem_bot] at hmem
    exact hmem
  have hVS : blockU J ≤ S :=
    QBlock.le_of_isPGroup_normal' hS.sylow ((blockU_le J).trans le_sup_left)
      (sup_le (le_normalizer_blockU J) hTV) hJ.isPGroup_blockU
  have hdQ : ∀ t ∈ T, t⁻¹ * (v⁻¹ * t * v) ∈ S ⊓ Subgroup.normalizer (T : Set G) ⊓ J := by
    intro t ht
    refine ⟨⟨?_, ?_⟩, blockU_le J (hdV t ht)⟩
    · exact S.mul_mem (S.inv_mem (hS.le ht))
        (S.mul_mem (S.mul_mem (S.inv_mem (hVS hvV)) (hS.le ht)) (hVS hvV))
    · exact (Subgroup.normalizer (T : Set G)).mul_mem
        (Subgroup.le_normalizer (T.inv_mem ht)) (hvN (hsTv t ht))
  have hinj : ∀ t ∈ T, ∀ t' ∈ T, t⁻¹ * (v⁻¹ * t * v) = t'⁻¹ * (v⁻¹ * t' * v) → t = t' := by
    intro t ht t' ht' h
    have hmem : t' * t⁻¹ ∈ T ⊓ rightConjugate T v := by
      refine ⟨T.mul_mem ht' (T.inv_mem ht), ?_⟩
      have e : t' * t⁻¹ = (v⁻¹ * t' * v) * (v⁻¹ * t * v)⁻¹ := by
        calc t' * t⁻¹ = t' * (t⁻¹ * (v⁻¹ * t * v)) * (v⁻¹ * t * v)⁻¹ := by group
          _ = t' * (t'⁻¹ * (v⁻¹ * t' * v)) * (v⁻¹ * t * v)⁻¹ := by rw [h]
          _ = (v⁻¹ * t' * v) * (v⁻¹ * t * v)⁻¹ := by group
      rw [e]
      exact (rightConjugate T v).mul_mem (hsTv t' ht')
        ((rightConjugate T v).inv_mem (hsTv t ht))
    rw [hTTv, Subgroup.mem_bot] at hmem
    exact (mul_inv_eq_one.1 hmem).symm
  let f : ↥T → ↥(S ⊓ Subgroup.normalizer (T : Set G) ⊓ J) := fun t =>
    ⟨t⁻¹ * (v⁻¹ * t * v), hdQ t t.2⟩
  have hf : Function.Injective f := fun a b h =>
    Subtype.ext (hinj a a.2 b b.2 (congrArg Subtype.val h))
  have hQT := c.card_inf_le hA hz hgood hT hmax hS
  have hTQ : Nat.card T ≤ Nat.card ↥(S ⊓ Subgroup.normalizer (T : Set G) ⊓ J) :=
    Nat.card_le_card_of_injective f hf
  have hbij : Function.Bijective f := hf.bijective_of_nat_card_le hQT
  refine ⟨hTc, hTs, ?_, le_antisymm hQT hTQ⟩
  intro q hq
  obtain ⟨t, ht⟩ := hbij.2 ⟨q, hq⟩
  have : q = t⁻¹ * (v⁻¹ * t * v) := congrArg Subtype.val ht.symm
  rw [this]
  exact hdV t t.2

end CE

end CFSG.CGT.PushingUpLit.LIT.Foote
