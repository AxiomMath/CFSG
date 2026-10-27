module

public import CFSG.GH74.GLS.C3.Layer1.P34RealCfg
public import CFSG.GH74.GLS.C3.Layer1.Thm1Normal
public import CFSG.GH74.GLS.C3.Layer1.Thm1Layer

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34Real

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_equiv_of_isSylowOf {N A B : Subgroup G} (hA : IsSylowOf 2 A N)
    (hB : IsSylowOf 2 B N) : Nonempty (↥A ≃* ↥B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₁, hS₁⟩ := hA.exists_sylow_eq_subgroupOf
  obtain ⟨S₂, hS₂⟩ := hB.exists_sylow_eq_subgroupOf
  let e : ↥(S₁ : Subgroup ↥N) ≃* ↥(S₂ : Subgroup ↥N) := Sylow.equiv S₁ S₂
  let eA : ↥(A.subgroupOf N) ≃* ↥A := Subgroup.subgroupOfEquivOfLe hA.le
  let eB : ↥(B.subgroupOf N) ≃* ↥B := Subgroup.subgroupOfEquivOfLe hB.le
  exact ⟨eA.symm.trans ((MulEquiv.subgroupCongr hS₁.symm).trans
    (e.trans ((MulEquiv.subgroupCongr hS₂).trans eB)))⟩

theorem factorization_two_mul_odd {a b : ℕ} (ha : a ≠ 0) (hb : Odd b) :
    (a * b).factorization 2 = a.factorization 2 := by
  have hb0 : b ≠ 0 := hb.pos.ne'
  have hb2 : b.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by rw [← even_iff_two_dvd, Nat.not_even_iff_odd]; exact hb)
  rw [Nat.factorization_mul ha hb0, Finsupp.add_apply, hb2, add_zero]

theorem exists_sylow_centralizing {C K : Subgroup G} (hKN : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    {f : G} (hfC : f ∈ C) (hf2 : orderOf f = 2)
    (hfix : (Nat.card ↥(fixedSubgroup (kBar K) (Back.actHom hKN ⟨f, hfC⟩))).factorization 2 =
      (Nat.card (kBar K)).factorization 2) :
    ∃ P : Subgroup G, P ≤ K ∧ IsSylowOf 2 P K ∧ ∀ p ∈ P, f * p = p * f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 ↥(K ⊓ centralizer ({f} : Set G))))
  set Cf : Subgroup G := K ⊓ centralizer ({f} : Set G) with hCf
  refine ⟨(S : Subgroup ↥Cf).map Cf.subtype, (Subgroup.map_subtype_le _).trans inf_le_left, ?_, ?_⟩
  ·
    have hle : (S : Subgroup ↥Cf).map Cf.subtype ≤ K :=
      (Subgroup.map_subtype_le _).trans inf_le_left
    refine isSylowOf_of_card hle ?_
    rw [Subgroup.card_map_of_injective Cf.subtype_injective, Sylow.card_eq_multiplicity]
    have hsurj := centMap_surjective hKN hfC hf2
    have hker := centMap_ker_odd hKN hfC
    have h1 : Nat.card ↥Cf = Nat.card ↥(fixedSubgroup (kBar K) (Back.actHom hKN ⟨f, hfC⟩)) *
        Nat.card (centMap hKN hfC).ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (centMap hKN hfC).ker]
      congr 1
      exact Nat.card_congr
        (QuotientGroup.quotientKerEquivOfSurjective (centMap hKN hfC) hsurj).toEquiv
    have h2 : Nat.card ↥K = Nat.card (kBar K) * Nat.card (pPrimeCore 2 ↥K) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K)
    have hodd2 : Odd (Nat.card (pPrimeCore 2 ↥K)) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
    have hne1 : Nat.card ↥(fixedSubgroup (kBar K) (Back.actHom hKN ⟨f, hfC⟩)) ≠ 0 := Nat.card_pos.ne'
    have hne2 : Nat.card (kBar K) ≠ 0 := Nat.card_pos.ne'
    rw [h1, factorization_two_mul_odd hne1 hker, hfix, h2, factorization_two_mul_odd hne2 hodd2]
  · intro p hp
    obtain ⟨c, hc, rfl⟩ := hp
    exact (mem_centralizer_singleton_iff.1 c.2.2).symm

theorem exists_real34 {x : G} {K : Subgroup G} (hyp : P34.Prop34Hyp G x K) {f : G}
    (hfC : f ∈ centralizer ({x} : Set G)) (hf2 : orderOf f = 2) (hind : P34.InducesFAutL2A7 f K)
    (hfixAll : ∀ α : MulAut (kBar K), orderOf α = 2 → P34.IsFAutL2A7 (kBar K) α →
      (Nat.card ↥(fixedSubgroup (kBar K) α)).factorization 2 = (Nat.card (kBar K)).factorization 2) :
    ∃ (T : Subgroup G) (H : Real34 x K T f), ¬ 2 ∣ T.index ∧
      (IsCyclic ↥H.Q ∨ P34.IsMaximalClassTwoGroup ↥H.Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKC : K ≤ centralizer ({x} : Set G) := hyp.comp.1
  have hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K := by
    intro c hc k hk
    have hK' : IsPCompIn 2 (centralizer ({x} : Set G)) (K.map (MulAut.conj c).toMonoidHom) := by
      have := Stage1.Thm2.Recip.isPCompIn_map_conj hyp.comp c
      rwa [map_conj_eq_self_of_mem hc] at this
    have heq := hyp.unique _ hK'
    have hmem : c * k * c⁻¹ ∈ K.map (MulAut.conj c).toMonoidHom :=
      ⟨k, hk, by simp [MulAut.conj_apply]⟩
    rwa [heq] at hmem
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

theorem b_prop34_realize_of_autlevel (hAL : B_prop34_autlevel) : P34.B_prop34_realize := by
  intro X _ _ x K hyp f hfC hf2 hind
  have hAL' : AutLevelP (kBar K) := hAL (kBar K) hyp.shape
  obtain ⟨T, H, hTidx, hQ⟩ := exists_real34 hyp hfC hf2 hind hAL'.1
  have hfC' : f ∈ centralizer ({x} : Set X) := hfC
  have hα : act H.KN f ∈ H.B := (H.mem_B).2 ⟨f, H.f_mem, rfl⟩
  have hα2 : orderOf (act H.KN f) = 2 := H.act_f_order
  obtain ⟨zb, hA⟩ := hAL'.2 H.B H.B_isPGroup H.sylow_Pbar (act H.KN f) hα hα2 H.f_fa
    (fun q hq => H.act_f_comm_Pbar hq)
  obtain ⟨P, Q, z, h, hcfg⟩ := H.cfg hA hyp.simple hyp.nonab hTidx hyp.central.1 hQ
  exact ⟨T, P, Q, z, h, hcfg⟩

end CFSG.GH74.GLS.C3.Layer1.P34Real
