module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43One
public import CFSG.RankThree.Native.Fi22FiveCentralizers
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanFi22GuestThree

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.HardMathSupport.Solomon.LocalBalance

theorem fi22_centre_eq_bot {K : Type} [Group K]
    (θ : K ≃* CFSG.Blueprint.NativeSporadic.Fi22) : Subgroup.center K = ⊥ := by
  have hF : IsSimpleGroup CFSG.Blueprint.NativeSporadic.Fi22 :=
    CFSG.Sporadic.Fi22.isSimpleGroup_Fi22
  have hs : IsSimpleGroup K :=
    @MulEquiv.isSimpleGroup K _ CFSG.Blueprint.NativeSporadic.Fi22 _ hF θ
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · exact h
  · exfalso
    have hc : IsMulCommutative K := Subgroup.center_eq_top_iff.1 h
    have hp := Group.is_simple_iff_prime_card.1 hs
    have hcard : Nat.card K = 64561751654400 :=
      (Nat.card_congr θ.toEquiv).trans CFSG.Sporadic.Fi22.card_Fi22
    rw [hcard] at hp
    have h2 := hp.eq_one_or_self_of_dvd 2 (by norm_num)
    norm_num at h2

theorem fi22_orderOf_ne_25 {K : Type} [Group K]
    (θ : K ≃* CFSG.Blueprint.NativeSporadic.Fi22) (x : K) : orderOf x ≠ 25 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro hx
  set ψ : K ≃* CFSG.Monster.B.Fischer.fi22P :=
    θ.trans CFSG.Monster.B.Fischer.fi22PermEquiv with hψ
  have hzord : orderOf (ψ x) = 25 := by
    rw [← hx]
    exact orderOf_injective ψ.toMonoidHom ψ.injective x
  have hPz : IsPGroup 5 (Subgroup.zpowers (ψ x)) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hzord]; norm_num)
  obtain ⟨Q, hQ⟩ := hPz.exists_le_sylow
  obtain ⟨S, hS⟩ := CFSG.RankThree.Native.fi22FiveQ_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq CFSG.Monster.B.Fischer.fi22P Q S
  have hzQ : ψ x ∈ Q := hQ (Subgroup.mem_zpowers (ψ x))
  have hconj : MulAut.conj g (ψ x) ∈ (S : Subgroup CFSG.Monster.B.Fischer.fi22P) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hzQ
  have hmemS : MulAut.conj g (ψ x) ∈ CFSG.RankThree.Native.fi22FiveQ.subgroupOf
      CFSG.Monster.B.Fischer.fi22P := by
    rw [← hS]
    exact hconj
  have hw : ((MulAut.conj g (ψ x) : CFSG.Monster.B.Fischer.fi22P) : Equiv.Perm (Fin 3510)) ∈
      CFSG.RankThree.Native.fi22FiveQ :=
    Subgroup.mem_subgroupOf.1 hmemS
  have h5 : ((MulAut.conj g (ψ x) : CFSG.Monster.B.Fischer.fi22P) : Equiv.Perm (Fin 3510)) ^ 5 =
      1 :=
    elemPow_eq_one_of_isElementaryAbelian _ hw
  have hw5 : (MulAut.conj g (ψ x)) ^ 5 = 1 := Subtype.ext (by simpa using h5)
  have hz5 : (ψ x) ^ 5 = 1 := by
    have h := hw5
    rw [MulAut.conj_apply, conj_pow, mul_inv_eq_one] at h
    have h2 : g * (ψ x) ^ 5 = g * 1 := by
      rw [mul_one]
      exact h
    exact mul_left_cancel h2
  have hdvd := orderOf_dvd_of_pow_eq_one hz5
  rw [hzord] at hdvd
  norm_num at hdvd

theorem fi22_card_outer {K : Type} [Group K]
    (θ : K ≃* CFSG.Blueprint.NativeSporadic.Fi22) :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer K) = 2 := by
  have h1 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer K) =
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        CFSG.Blueprint.NativeSporadic.Fi22) :=
    CFSG.RankThree.PartOne.card_outer_eq_of_mulEquiv θ
  rw [h1]
  exact CFSG.RankThree.PartOne.card_outer_fi22_carrier

theorem fi22_inner_of_isPGroup {K : Type} [Group K]
    (θ : K ≃* CFSG.Blueprint.NativeSporadic.Fi22) (φ : MulAut K)
    (hφ : IsPGroup 5 (Subgroup.zpowers φ)) : ∃ k : K, φ = MulAut.conj k := by
  have hout := fi22_card_outer θ
  obtain ⟨n, hn⟩ := hφ ⟨φ, Subgroup.mem_zpowers φ⟩
  have hφn : φ ^ 5 ^ n = 1 := by
    have h := congrArg Subtype.val hn
    simpa using h
  have hq : (QuotientGroup.mk φ : CFSG.ComponentClassification.OuterAutomorphisms.Outer K) ^
      5 ^ n = 1 := by
    rw [← QuotientGroup.mk_pow, hφn]
    rfl
  have hd1 : orderOf (QuotientGroup.mk φ :
      CFSG.ComponentClassification.OuterAutomorphisms.Outer K) ∣ 5 ^ n :=
    orderOf_dvd_of_pow_eq_one hq
  have hd2 : orderOf (QuotientGroup.mk φ :
      CFSG.ComponentClassification.OuterAutomorphisms.Outer K) ∣ 2 := by
    have := orderOf_dvd_natCard
      (QuotientGroup.mk φ : CFSG.ComponentClassification.OuterAutomorphisms.Outer K)
    rwa [hout] at this
  have hg : Nat.gcd (5 ^ n) 2 = 1 := Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 5 2)
  have h1 : orderOf (QuotientGroup.mk φ :
      CFSG.ComponentClassification.OuterAutomorphisms.Outer K) = 1 := by
    have := Nat.dvd_gcd hd1 hd2
    rw [hg] at this
    exact Nat.dvd_one.1 this
  have hmk := orderOf_eq_one_iff.1 h1
  have hmem : φ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner K :=
    (QuotientGroup.eq_one_iff φ).1 hmk
  have hmem' : φ ∈ (MulAut.conj : K →* MulAut K).range := hmem
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.1 hmem'
  exact ⟨k, hk.symm⟩

theorem fi22Facts_holds :
    Fi22Facts := by
  unfold Fi22Facts
  intro K _ _ hK
  obtain ⟨e⟩ := hK
  obtain ⟨β⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  have β' : CFSG.Blueprint.NativeSporadic.Fi22 ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group := β
  let θ : K ≃* CFSG.Blueprint.NativeSporadic.Fi22 := e.trans β'.symm
  refine ⟨fi22_centre_eq_bot θ, ?_, fi22_orderOf_ne_25 θ, fi22_inner_of_isPGroup θ⟩
  have hcard : Nat.card K = 64561751654400 :=
    (Nat.card_congr θ.toEquiv).trans CFSG.Sporadic.Fi22.card_Fi22
  rw [hcard]
  exact CFSG.AGLEmbeddingD2.factorization_five_fi22

end CFSG.HardMathSupport.Solomon.Proving
