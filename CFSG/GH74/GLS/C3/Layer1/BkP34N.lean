module

public import CFSG.GH74.GLS.C3.Layer1.P34RealDone
public import CFSG.GH74.GLS.C3.Layer1.P34RealTop

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1 CFSG.GH74.GLS.C3.Layer1.P34Real
open scoped commutatorElement

structure Prop34HypN (X : Type) [Group X] (x : X) (K : Subgroup X) : Prop where
  simple : IsSimpleGroup X
  nonab : ∃ a b : X, a * b ≠ b * a
  central : IsCentralInvolution x
  comp : IsPCompIn 2 (centralizer ({x} : Set X)) K
  normal : ∀ c ∈ centralizer ({x} : Set X), ∀ k ∈ K, c * k * c⁻¹ ∈ K
  shape : HasL2Model (kBar K) Odd ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7))
  sylowQ : ∃ Q : Subgroup X, IsSylowOf 2 Q (CMK (centralizer ({x} : Set X)) K) ∧
    (IsCyclic ↥Q ∨ P34.IsMaximalClassTwoGroup ↥Q)

theorem isMaximalClassTwoGroup_of_four {G : Type} [Group G] [Finite G] {Q : Subgroup G}
    (hel : CFSG.IsElementaryAbelian 2 ↥Q) (h4 : Nat.card ↥Q = 4) :
    P34.IsMaximalClassTwoGroup ↥Q := by
  have hp : IsPGroup 2 ↥Q := IsPGroup.of_card (n := 2) (by rw [h4]; norm_num)
  have hab : IsMulCommutative ↥Q := hel.toIsMulCommutative
  have hnil : Group.IsNilpotent ↥Q := inferInstance
  have hnt : Nontrivial ↥Q := by
    have : 1 < Nat.card ↥Q := by rw [h4]; norm_num
    exact Finite.one_lt_card_iff_nontrivial.1 this
  refine ⟨hp, hnil, ?_⟩
  have hle : Group.nilpotencyClass ↥Q ≤ 1 := (Group.IsNilpotent.nilpotencyClass_le_one_iff).2 hab
  have hne : Group.nilpotencyClass ↥Q ≠ 0 := by
    intro h0
    have := (Group.nilpotencyClass_zero_iff_subsingleton).1 h0
    exact (not_subsingleton ↥Q) this
  have : Group.nilpotencyClass ↥Q = 1 := le_antisymm hle (Nat.one_le_iff_ne_zero.2 hne)
  rw [this, h4]
  norm_num

variable {G : Type} [Group G] [Finite G]

theorem exists_real34N {x : G} {K : Subgroup G} (hyp : Prop34HypN G x K) {f : G}
    (hfC : f ∈ centralizer ({x} : Set G)) (hf2 : orderOf f = 2) (hind : P34.InducesFAutL2A7 f K)
    (hfixAll : ∀ α : MulAut (kBar K), orderOf α = 2 → P34.IsFAutL2A7 (kBar K) α →
      (Nat.card ↥(fixedSubgroup (kBar K) α)).factorization 2 = (Nat.card (kBar K)).factorization 2) :
    ∃ (T : Subgroup G) (H : Real34 x K T f), ¬ 2 ∣ T.index ∧
      (IsCyclic ↥H.Q ∨ P34.IsMaximalClassTwoGroup ↥H.Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKC : K ≤ centralizer ({x} : Set G) := hyp.comp.1
  have hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K := hyp.normal
  have hcen : Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K)) := by
    rcases hyp.shape with h | ⟨⟨e7⟩⟩
    · obtain ⟨F, _, _, _, ⟨e⟩⟩ := exists_l2_model_of_hasL2Model h
      exact IVK.conj_injective_of_L2 e
    · exact conj_injective_of_A7 e7
  obtain ⟨hfN', hF⟩ := hind
  have hFa : P34.IsFAutL2A7 (kBar K) (act hKN f) := by
    rw [act_of_mem hKN hfC]
    exact hF
  have hff : f * f = 1 := by
    have := pow_orderOf_eq_one f
    rwa [hf2, sq] at this
  have hα2 : orderOf (act hKN f) = 2 := by
    refine orderOf_eq_prime ?_ hFa.1
    rw [sq, ← act_mul hKN hfC hfC, hff, act_one]
  have hfix := hfixAll (act hKN f) hα2 hFa
  rw [act_of_mem hKN hfC] at hfix
  obtain ⟨P, hPK, hPS, hPc⟩ := exists_sylow_centralizing hKN hfC hf2 hfix
  have hP2 : IsPGroup 2 ↥P := hPS.isPGroup
  have hf2g : IsPGroup 2 ↥(zpowers f) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hf2, pow_one])
  obtain ⟨hx2, S, hxS, hxc⟩ := hyp.central
  have hx2g : IsPGroup 2 ↥(zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx2, pow_one])
  have hPf : IsPGroup 2 ↥(P ⊔ zpowers f) := by
    refine hP2.to_sup_of_normal_left' hf2g (P34.W_le_normalizer_of fun w hw a ha => ?_)
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hw
    have : f ^ j * a * (f ^ j)⁻¹ = a := by
      have hc : Commute (f ^ j) a := (Commute.zpow_left (show Commute f a from hPc a ha) j)
      rw [hc.eq]
      group
    rw [this]
    exact ha
  have hPfC : P ⊔ zpowers f ≤ centralizer ({x} : Set G) :=
    sup_le (hPK.trans hKC) ((zpowers_le).2 hfC)
  have hK2 : IsPGroup 2 ↥((P ⊔ zpowers f) ⊔ zpowers x) := by
    refine hPf.to_sup_of_normal_left' hx2g (P34.W_le_normalizer_of fun w hw a ha => ?_)
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hw
    have hax : Commute x a := (mem_centralizer_singleton_iff.1 (hPfC ha)).symm
    have hc : Commute (x ^ j) a := hax.zpow_left j
    have : x ^ j * a * (x ^ j)⁻¹ = a := by
      rw [hc.eq]
      group
    rw [this]
    exact ha
  have hxC : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 rfl
  obtain ⟨T, hKT, hTC, hT2, hTidx⟩ := P34.exists_sylow_ge
    (sup_le hPfC ((zpowers_le).2 hxC)) hK2
  have hsylowT : IsSylowOf 2 T (centralizer ({x} : Set G)) :=
    isSylowOf_iff.2 ⟨hTC, hT2, hTidx⟩
  have hPT : P ≤ T := le_sup_left.trans (le_sup_left.trans hKT)
  have hfT : f ∈ T := hKT (Subgroup.mem_sup_left (Subgroup.mem_sup_right (mem_zpowers f)))
  have hxT : x ∈ T := hKT (Subgroup.mem_sup_right (mem_zpowers x))
  have hTK : T ⊓ K = P := hPS.eq_of_le (le_inf hPT hPK) inf_le_right hT2.to_inf_left
  have hsylowP : IsSylowOf 2 (T ⊓ K) K := by rw [hTK]; exact hPS
  let H : Real34 x K T f :=
    { KC := hKC
      KN := hKN
      cen := hcen
      sylowT := hsylowT
      sylowP := hsylowP
      x_mem := hxT
      f_mem := hfT
      f_order := hf2
      f_cent := fun p hp => by rw [hTK] at hp; exact hPc p hp
      f_fa := hFa }
  refine ⟨T, H, ?_, ?_⟩
  ·
    have hSC : (S : Subgroup G) ≤ centralizer ({x} : Set G) := fun s hs =>
      mem_centralizer_singleton_iff.2 (hxc s hs)
    have hSsyl : IsSylowOf 2 (S : Subgroup G) (centralizer ({x} : Set G)) := by
      refine isSylowOf_iff.2 ⟨hSC, S.isPGroup', fun hdvd => S.not_dvd_index ?_⟩
      exact hdvd.trans (Subgroup.relIndex_dvd_index_of_le hSC)
    have hcard : Nat.card ↥T = Nat.card ↥(S : Subgroup G) := by
      rw [hsylowT.card_eq, hSsyl.card_eq]
    have h1 := Subgroup.index_mul_card T
    have h2 := Subgroup.index_mul_card (S : Subgroup G)
    have hidx : T.index = (S : Subgroup G).index := by
      have hpos : 0 < Nat.card ↥T := Nat.card_pos
      apply Nat.eq_of_mul_eq_mul_right hpos
      rw [h1, hcard, h2]
    rw [hidx]
    exact S.not_dvd_index
  ·
    obtain ⟨Q₀, hQ₀, hQ₀shape⟩ := hyp.sylowQ
    have hCN : centralizer ({x} : Set G) ≤ normalizer ((CMK (centralizer ({x} : Set G)) K : Subgroup G) : Set G) := by
      intro g hg
      refine P34.mem_normalizer_of_conj_le (fun a ha => ?_)
      have := CMK_conj hKN (Subgroup.inv_mem _ hg) ha
      simpa using this
    have hQsyl : IsSylowOf 2 H.Q (CMK (centralizer ({x} : Set G)) K) :=
      hsylowT.inf_of_le_normalizer inf_le_left hCN
    obtain ⟨e⟩ := exists_equiv_of_isSylowOf hQ₀ hQsyl
    rcases hQ₀shape with hc | hm
    · exact Or.inl (isCyclic_of_surjective e.toMonoidHom e.surjective)
    · exact Or.inr (isMaximalClassTwoGroup_of_equiv e hm)

theorem prop34N_false
    {x : G} {K : Subgroup G} (hyp : Prop34HypN G x K) {f : G}
    (hfC : f ∈ centralizer ({x} : Set G)) (hf2 : orderOf f = 2) (hind : P34.InducesFAutL2A7 f K) :
    False := by
  have hAL : B_prop34_autlevel := b_prop34_autlevel_proved
  have hAL' : AutLevelP (kBar K) := hAL (kBar K) hyp.shape
  obtain ⟨T, H, hTidx, hQ⟩ := exists_real34N hyp hfC hf2 hind hAL'.1
  have hfC' : f ∈ centralizer ({x} : Set G) := hfC
  have hα : act H.KN f ∈ H.B := (H.mem_B).2 ⟨f, H.f_mem, rfl⟩
  have hα2 : orderOf (act H.KN f) = 2 := H.act_f_order
  obtain ⟨zb, hA⟩ := hAL'.2 H.B H.B_isPGroup H.sylow_Pbar (act H.KN f) hα hα2 H.f_fa
    (fun q hq => H.act_f_comm_Pbar hq)
  obtain ⟨P, Q, z, h, hcfg⟩ := H.cfg hA hyp.simple hyp.nonab hTidx hyp.central.1 hQ
  exact P34.prop34_core_all hcfg

end CFSG.GH74.GLS.C3.Layer1.Bk
