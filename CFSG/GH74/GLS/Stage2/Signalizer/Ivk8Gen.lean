module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Abs
import CFSG.GH74.AS16.Standard

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

namespace Gen

theorem quasisimple_quot {G : Type*} [Group G] {J : Subgroup G} (hq : IsQuasisimple ↥J) :
    IsSimpleGroup (↥J ⧸ center ↥J) ∧ ¬ Group.IsSolvable (↥J ⧸ center ↥J) := by
  obtain ⟨-, hs, a, b, hab⟩ := hq
  refine ⟨hs, fun hsol => hab ?_⟩
  have := hs
  exact (IsSimpleGroup.comm_iff_isSolvable.mpr hsol) a b

theorem mem_pPrimeCore_two_of_commuting_conjugates {A : Type*} [Group A] [Finite A] {c : A}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcp : c ^ p = 1)
    (hcomm : ∀ a b : A, (a * c * a⁻¹) * (b * c * b⁻¹) = (b * c * b⁻¹) * (a * c * a⁻¹)) :
    c ∈ pPrimeCore 2 A := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hX : ∀ x ∈ Group.conjugatesOfSet ({c} : Set A), ∃ a : A, x = a * c * a⁻¹ := by
    intro x hx
    rw [Group.mem_conjugatesOfSet_iff] at hx
    obtain ⟨b, hb, hbx⟩ := hx
    rw [Set.mem_singleton_iff] at hb
    subst hb
    obtain ⟨a, ha⟩ := isConj_iff.mp hbx
    exact ⟨a, ha.symm⟩
  have hXp : ∀ x ∈ Group.conjugatesOfSet ({c} : Set A), x ^ p = 1 := by
    intro x hx
    obtain ⟨a, rfl⟩ := hX x hx
    rw [conj_pow, hcp]
    simp
  have hpair : (Group.conjugatesOfSet ({c} : Set A)).Pairwise Commute := by
    intro x hx y hy _
    obtain ⟨a, rfl⟩ := hX x hx
    obtain ⟨b, rfl⟩ := hX y hy
    exact hcomm a b
  have := Subgroup.isMulCommutative_closure hpair
  have hNcomm : ∀ g₁ ∈ Subgroup.closure (Group.conjugatesOfSet ({c} : Set A)),
      ∀ g₂ ∈ Subgroup.closure (Group.conjugatesOfSet ({c} : Set A)), g₁ * g₂ = g₂ * g₁ := by
    intro g₁ h₁ g₂ h₂
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm
      (⟨g₁, h₁⟩ : Subgroup.closure (Group.conjugatesOfSet ({c} : Set A))) ⟨g₂, h₂⟩)
  have hNp : ∀ g ∈ Subgroup.closure (Group.conjugatesOfSet ({c} : Set A)), g ^ p = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hXp x hx
    | one => simp
    | mul x y hx hy hx1 hy1 =>
      rw [(Commute.mul_pow (hNcomm x hx y hy) p), hx1, hy1, one_mul]
    | inv x hx hx1 => rw [inv_pow, hx1, inv_one]
  have hNP : IsPGroup p (Subgroup.normalClosure ({c} : Set A)) := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa using hNp g.1 g.2
  obtain ⟨n, hn⟩ := hNP.exists_card_eq
  have hcop : Nat.Coprime 2 (Nat.card (Subgroup.normalClosure ({c} : Set A))) := by
    rw [hn]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have hle : Subgroup.normalClosure ({c} : Set A) ≤ pPrimeCore 2 A :=
    le_sSup ⟨inferInstance, hcop⟩
  exact hle (Subgroup.subset_normalClosure (Set.mem_singleton c))

theorem commute_conj_of_central_in_component {A : Type*} [Group A] [Finite A] {K : Subgroup A}
    (hK : IsComponent K) {c : A} (hcK : c ∈ K) (hcz : ∀ k ∈ K, k * c = c * k) (a b : A) :
    (a * c * a⁻¹) * (b * c * b⁻¹) = (b * c * b⁻¹) * (a * c * a⁻¹) := by
  have h1 : IsComponent (K.map (MulAut.conj a).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj a) hK
  have h2 : IsComponent (K.map (MulAut.conj b).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj b) hK
  have ha : a * c * a⁻¹ ∈ K.map (MulAut.conj a).toMonoidHom :=
    ⟨c, hcK, by simp [MulAut.conj_apply]⟩
  have hb : b * c * b⁻¹ ∈ K.map (MulAut.conj b).toMonoidHom :=
    ⟨c, hcK, by simp [MulAut.conj_apply]⟩
  rcases CFSG.LocalCores.distinct_components_commute h1 h2 with h | h
  · have hb' : b * c * b⁻¹ ∈ K.map (MulAut.conj a).toMonoidHom := h ▸ hb
    obtain ⟨j, hj, hjb⟩ := hb'
    have hjb' : a * j * a⁻¹ = b * c * b⁻¹ := by simpa [MulAut.conj_apply] using hjb
    rw [← hjb']
    have := hcz j hj
    calc a * c * a⁻¹ * (a * j * a⁻¹) = a * (c * j) * a⁻¹ := by group
      _ = a * (j * c) * a⁻¹ := by rw [this]
      _ = a * j * a⁻¹ * (a * c * a⁻¹) := by group
  · have hmem : ⁅a * c * a⁻¹, b * c * b⁻¹⁆ ∈ ⁅K.map (MulAut.conj a).toMonoidHom,
        K.map (MulAut.conj b).toMonoidHom⁆ := Subgroup.commutator_mem_commutator ha hb
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem

theorem normal_of_unique_comp {A : Type*} [Group A] {J : Subgroup A} (hJ : IsComponent J)
    (h2 : ∀ K : Subgroup A, IsComponent K → K = J) : J.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have h := h2 _ (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hJ)
  have : g * n * g⁻¹ ∈ J.map (MulAut.conj g).toMonoidHom :=
    ⟨n, hn, by simp [MulAut.conj_apply]⟩
  rwa [h] at this

theorem exists_involution_center_of_normal {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    {N : Subgroup P} [N.Normal] (hN : N ≠ ⊥) :
    ∃ w : P, w ∈ N ∧ w ∈ center P ∧ orderOf w = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hP.isNilpotent
  have hW : N ⊓ center P ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hN
  have hWp : IsPGroup 2 ↥(N ⊓ center P) := hP.to_subgroup _
  have hcard : Nat.card ↥(N ⊓ center P) ≠ 1 := fun h => hW (Subgroup.card_eq_one.mp h)
  have hdvd : 2 ∣ Nat.card ↥(N ⊓ center P) := (hWp.card_eq_or_dvd).resolve_left hcard
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥(N ⊓ center P)) 2 hdvd
  refine ⟨(w : P), (Subgroup.mem_inf.mp w.2).1, (Subgroup.mem_inf.mp w.2).2, ?_⟩
  rw [Subgroup.orderOf_coe, hw]

end Gen

section Frame

variable {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb J : Subgroup A}

theorem AFrame.kindFactor_of_centralizes (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J) {u : A}
    (hu : orderOf u = 2) (hJu : ∀ j ∈ J, j * u = u * j) :
    KindFactorAll Kind.ly (↥J ⧸ center ↥J) := by
  obtain ⟨hs, hns⟩ := Gen.quasisimple_quot hJ.1
  have := hs
  refine hfr.invsec u hu _ hns ?_
  have hle : J ≤ centralizer ({u} : Set A) := by
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (hJu j hj).symm
  exact ⟨J.subgroupOf (centralizer ({u} : Set A)),
    (QuotientGroup.mk' (center ↥J)).comp (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom,
    (QuotientGroup.mk'_surjective _).comp (Subgroup.subgroupOfEquivOfLe hle).surjective⟩

theorem AFrame.center_eq_bot (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J)
    (hY : ¬ KindFactorAll Kind.ly (↥J ⧸ center ↥J)) : center ↥J = ⊥ := by
  by_contra hne
  have hcard : Nat.card (center ↥J) ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hcard
  have := Fact.mk hp
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥J)) p hpd
  have hxc : ∀ y : ↥J, y * (x : ↥J) = (x : ↥J) * y := fun y =>
    Subgroup.mem_center_iff.mp x.2 y
  have hord : orderOf ((x : ↥J) : A) = p := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  by_cases hp2 : p = 2
  · subst hp2
    refine hY (hfr.kindFactor_of_centralizes hJ hord fun j hj => ?_)
    exact congrArg Subtype.val (hxc ⟨j, hj⟩)
  · have hxJ : ((x : ↥J) : A) ∈ J := (x : ↥J).2
    have hmem := Gen.mem_pPrimeCore_two_of_commuting_conjugates (A := A)
      (c := ((x : ↥J) : A)) hp hp2 ?_ ?_
    · rw [hfr.core, Subgroup.mem_bot] at hmem
      rw [hmem, orderOf_one] at hord
      exact hp.one_lt.ne hord
    · have := pow_orderOf_eq_one ((x : ↥J) : A)
      rwa [hord] at this
    · refine Gen.commute_conj_of_central_in_component (K := J) hJ hxJ ?_
      intro k hk
      exact congrArg (fun y : ↥J => (y : A)) (hxc ⟨k, hk⟩)

theorem AFrame.comp_eq (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J)
    (hY : ¬ KindFactorAll Kind.ly (↥J ⧸ center ↥J)) :
    ∀ K : Subgroup A, IsComponent K → K = J := by
  intro K hK
  by_contra hne
  rcases CFSG.LocalCores.distinct_components_commute hJ hK with h | h
  · exact hne h.symm
  · obtain ⟨t, htK, ht2⟩ := AS16.exists_involution_of_isQuasisimple hK.1
    refine hY (hfr.kindFactor_of_centralizes hJ ht2 fun j hj => ?_)
    have hmem : ⁅j, t⁆ ∈ ⁅J, K⁆ := Subgroup.commutator_mem_commutator hj htK
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem

theorem AFrame.zb_mem_of_unique_comp (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J)
    (h2 : ∀ K : Subgroup A, IsComponent K → K = J) : zb ∈ J := by
  have hJn : J.Normal := Gen.normal_of_unique_comp hJ h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, htJ, ht2⟩ := AS16.exists_involution_of_isQuasisimple hJ.1
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 2 (Sb ⊓ J) J :=
    hfr.sylow.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top])
  have hdvd : 2 ∣ Nat.card ↥J := by
    have := orderOf_dvd_natCard (⟨t, htJ⟩ : ↥J)
    rwa [Subgroup.orderOf_mk, ht2] at this
  have hpos : 0 < (Nat.card ↥J).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' hdvd
  have hne : Sb ⊓ J ≠ ⊥ := by
    intro h
    have hc := hsyl.card_eq
    rw [h, Subgroup.card_bot] at hc
    have : 1 < 2 ^ (Nat.card ↥J).factorization 2 := Nat.one_lt_two_pow hpos.ne'
    omega
  have hNne : J.subgroupOf Sb ≠ ⊥ := by
    intro h
    exact hne (by rw [inf_comm]; exact disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h))
  obtain ⟨w, hwN, hwc, hw2⟩ := Gen.exists_involution_center_of_normal hfr.sylow.isPGroup hNne
  have hwcomm : ∀ s ∈ Sb, s * ((w : ↥Sb) : A) = ((w : ↥Sb) : A) * s := fun s hs =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hwc ⟨s, hs⟩)
  have hwz : ((w : ↥Sb) : A) = zb :=
    hfr.zcen _ w.2 hwcomm (by rw [Subgroup.orderOf_coe]; exact hw2)
  rw [← hwz]
  exact Subgroup.mem_subgroupOf.mp hwN

theorem AFrame.reduce (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J)
    (hY : ¬ KindFactorAll Kind.ly (↥J ⧸ center ↥J)) :
    center ↥J = ⊥ ∧ (∀ K : Subgroup A, IsComponent K → K = J) ∧ zb ∈ J :=
  ⟨hfr.center_eq_bot hJ hY, hfr.comp_eq hJ hY,
    hfr.zb_mem_of_unique_comp hJ (hfr.comp_eq hJ hY)⟩

theorem AFrame.embed_aut (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J) (h1 : center ↥J = ⊥)
    (h2 : ∀ K : Subgroup A, IsComponent K → K = J) :
    ∃ φ : ↥Sb →* MulAut ↥J, Function.Injective φ ∧
      ∀ (s : ↥Sb) (x : ↥J), ((φ s x : ↥J) : A) = (s : A) * (x : A) * (s : A)⁻¹ := by
  have hJn : J.Normal := Gen.normal_of_unique_comp hJ h2
  have hnorm : Sb ≤ normalizer (J : Set A) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  refine ⟨J.normalizerMonoidHom.comp (Subgroup.inclusion hnorm), ?_, fun s x => rfl⟩
  have hzJ : zb ∈ J := hfr.zb_mem_of_unique_comp hJ h2
  set φ : ↥Sb →* MulAut ↥J := J.normalizerMonoidHom.comp (Subgroup.inclusion hnorm) with hφ
  rw [injective_iff_map_eq_one]
  intro s hs
  by_contra hne
  have hker : φ.ker ≠ ⊥ := fun h => hne (by
    have : s ∈ φ.ker := hs
    rw [h] at this
    exact Subgroup.mem_bot.mp this)
  obtain ⟨w, hwk, hwc, hw2⟩ := Gen.exists_involution_center_of_normal hfr.sylow.isPGroup hker
  have hwcomm : ∀ s ∈ Sb, s * ((w : ↥Sb) : A) = ((w : ↥Sb) : A) * s := fun s hs =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hwc ⟨s, hs⟩)
  have hwz : ((w : ↥Sb) : A) = zb :=
    hfr.zcen _ w.2 hwcomm (by rw [Subgroup.orderOf_coe]; exact hw2)
  have hzc : (⟨zb, hzJ⟩ : ↥J) ∈ center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h := MonoidHom.mem_ker.mp hwk
    have hy : ((φ w y : ↥J) : A) = (y : A) := by rw [h]; rfl
    have hy' : ((w : ↥Sb) : A) * (y : A) * ((w : ↥Sb) : A)⁻¹ = (y : A) := hy
    rw [hwz] at hy'
    apply Subtype.ext
    have : zb * (y : A) = (y : A) * zb := by
      calc zb * (y : A) = (zb * (y : A) * zb⁻¹) * zb := by group
        _ = (y : A) * zb := by rw [hy']
    exact this.symm
  rw [h1, Subgroup.mem_bot] at hzc
  have hz1 : zb = 1 := congrArg Subtype.val hzc
  have := hfr.zb_ord
  rw [hz1, orderOf_one] at this
  exact absurd this (by norm_num)

end Frame

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
