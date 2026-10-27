module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims135b
public import CFSG.GH74.GLS.AssemblyComponents
public import CFSG.RankThree.PartTwo.Sec4.T444.Coprime
public import CFSG.LocalAnalysis.GL83PartI.I713.Extension
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.KFactI713OutMain

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims135c

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section Components

variable {X : Type} [Group X] [Finite X]

theorem component_le_centralizer_pCore {J : Subgroup X} (hJ : IsComponentOf J ⊤) :
    J ≤ Subgroup.centralizer (CFSG.pCore 3 X : Set X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (CFSG.pCore 3 X).Normal := CFSG.pCore_normal
  haveI : Group.IsNilpotent (CFSG.pCore 3 X) := (CFSG.pCore_isPGroup (p := 3)).isNilpotent
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.1
    (CFSG.ComponentClassification.LocalComponents.commutes_with_solvable_subnormal J _ hJ
      (isSubnormal_of_normal inferInstance))

theorem mem_pCore_of_mem_center (hcore : GLAPPrimeCore 3 X = ⊥) {J : Subgroup X}
    (hJ : IsComponentOf J ⊤) {z : J} (hz : z ∈ Subgroup.center J) :
    (z : X) ∈ CFSG.pCore 3 X := by
  refine mem_pCore_of_centralizes Nat.prime_three hcore (component_le_centralizer_pCore hJ z.2) ?_
  intro K hK
  by_cases hKJ : K = J
  · subst hKJ
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨k, hk⟩)
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne J K hJ hK (Ne.symm hKJ)) z.2

theorem isPGroup_center (hcore : GLAPPrimeCore 3 X = ⊥) {J : Subgroup X}
    (hJ : IsComponentOf J ⊤) : IsPGroup 3 (Subgroup.center J) := by
  intro z
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 3) (G := X)
    ⟨((z : J) : X), mem_pCore_of_mem_center hcore hJ z.2⟩
  refine ⟨k, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  simpa using congrArg Subtype.val hk

theorem commute_of_isPGroup
    (hab : ∀ S : Sylow 3 X, ∀ a ∈ (S : Subgroup X), ∀ b ∈ (S : Subgroup X), a * b = b * a)
    {U : Subgroup X} (hU : IsPGroup 3 U) {a b : X} (ha : a ∈ U) (hb : b ∈ U) : a * b = b * a := by
  obtain ⟨S, hS⟩ := hU.exists_le_sylow
  exact hab S a (hS ha) b (hS hb)

theorem center_eq_bot (hcore : GLAPPrimeCore 3 X = ⊥)
    (hab : ∀ S : Sylow 3 X, ∀ a ∈ (S : Subgroup X), ∀ b ∈ (S : Subgroup X), a * b = b * a)
    {J : Subgroup X} (hJ : IsComponentOf J ⊤) : Subgroup.center J = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsPerfect J := ⟨hJ.2.2.1⟩
  obtain ⟨T⟩ : Nonempty (Sylow 3 J) := inferInstance
  have hT : ⁅(T : Subgroup J), (T : Subgroup J)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    apply Subtype.ext
    exact commute_of_isPGroup hab (T.isPGroup'.map J.subtype) ⟨b, hb, rfl⟩ ⟨a, ha, rfl⟩
  have h := (CFSG.ShultStronglyClosedTI.MiscAlgebra.central_sylow_transfer_derived T _ le_rfl
    (isPGroup_center hcore hJ)).1
  rw [hT] at h
  exact le_bot_iff.1 h

theorem three_dvd_card (hcore : GLAPPrimeCore 3 X = ⊥) {J : Subgroup X}
    (hJ : IsComponentOf J ⊤) : 3 ∣ Nat.card J := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra h
  have hle := CFSG.GH74.GLS.le_pPrimeCore_of_subnormal 3
    (CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hJ.2.1
      Subgroup.IsSubnormal.top)
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h)
  have hbot : J = ⊥ := le_bot_iff.1 (hle.trans (le_of_eq hcore))
  haveI := CFSG.ComponentClassification.Quasisimple.nontrivial hJ.2.2
  exact (Subgroup.nontrivial_iff_ne_bot J).1 inferInstance hbot

theorem eq_one_of_commute {J : Subgroup X} (hZ : Subgroup.center J = ⊥) {x : X} (hx : x ∈ J)
    (hc : ∀ j ∈ J, j * x = x * j) : x = 1 := by
  have h : (⟨x, hx⟩ : J) ∈ Subgroup.center J :=
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (hc g g.2)
  rw [hZ, Subgroup.mem_bot] at h
  exact congrArg Subtype.val h

theorem inf_eq_bot_of_le_center {J Q U : Subgroup X} (hZ : Subgroup.center J = ⊥)
    (hQZ : Q ≤ Subgroup.center X) (hUJ : U ≤ J) : Q ⊓ U = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxQ, hxU⟩
  rw [Subgroup.mem_bot]
  exact eq_one_of_commute hZ (hUJ hxU) fun j _ => Subgroup.mem_center_iff.1 (hQZ hxQ) j

theorem normal_of_le_center {Q : Subgroup X} (hQZ : Q ≤ Subgroup.center X) : Q.Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_center_iff.1 (hQZ hn) g, mul_inv_cancel_right]
    exact hn⟩

theorem card_map_eq_of_inf_eq_bot {Q U : Subgroup X} [Q.Normal] (h : Q ⊓ U = ⊥) :
    Nat.card (U.map (QuotientGroup.mk' Q)) = Nat.card U := by
  have h' := Subgroup.relIndex_mul_card (QuotientGroup.mk' Q).ker U
  rw [Subgroup.relIndex_ker, QuotientGroup.ker_mk', h, Subgroup.card_bot, mul_one] at h'
  exact h'

structure LayerConfig (X : Type) [Group X] [Finite X] (Q : Subgroup X) : Prop where
  core : GLAPPrimeCore 3 X = ⊥
  ab : ∀ S : Sylow 3 X, ∀ a ∈ (S : Subgroup X), ∀ b ∈ (S : Subgroup X), a * b = b * a
  card27 : ∀ S : Sylow 3 X, Nat.card (S : Subgroup X) = 27
  central : Q ≤ Subgroup.center X
  card9 : Nat.card Q = 9

variable {Q : Subgroup X}

theorem LayerConfig.exists_sylow (h : LayerConfig X Q) {U : Subgroup X} (hU : IsPGroup 3 U) :
    haveI := normal_of_le_center h.central
    ∃ S : Sylow 3 X, U ≤ S ∧ Q ≤ S ∧
      Nat.card ((S : Subgroup X).map (QuotientGroup.mk' Q)) = 3 := by
  haveI := normal_of_le_center h.central
  have hQp : IsPGroup 3 Q := IsPGroup.of_card (n := 2) (by rw [h.card9]; norm_num)
  obtain ⟨S, hS⟩ := (hU.to_sup_of_normal_right hQp).exists_le_sylow
  refine ⟨S, le_sup_left.trans hS, le_sup_right.trans hS, ?_⟩
  have h' := Subgroup.relIndex_mul_card (QuotientGroup.mk' Q).ker (S : Subgroup X)
  rw [Subgroup.relIndex_ker, QuotientGroup.ker_mk', inf_eq_left.2 (le_sup_right.trans hS),
    h.card9, h.card27 S] at h'
  omega

theorem LayerConfig.card_sylow (h : LayerConfig X Q) {J : Subgroup X} (hJ : IsComponentOf J ⊤)
    (T : Sylow 3 J) : Nat.card (T : Subgroup J) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := normal_of_le_center h.central
  have hZ := center_eq_bot h.core h.ab hJ
  set T' := (T : Subgroup J).map J.subtype with hT'
  have hT'card : Nat.card T' = Nat.card (T : Subgroup J) :=
    Subgroup.card_map_of_injective J.subtype_injective
  obtain ⟨S, hT'S, -, hS3⟩ := h.exists_sylow (T.isPGroup'.map J.subtype)
  have hle : Nat.card (T'.map (QuotientGroup.mk' Q)) ≤ 3 :=
    hS3 ▸ Subgroup.card_le_of_le (Subgroup.map_mono hT'S)
  rw [card_map_eq_of_inf_eq_bot (inf_eq_bot_of_le_center hZ h.central
    (Subgroup.map_subtype_le _)), hT'card] at hle
  have h3 := three_dvd_card h.core hJ
  rw [T.card_eq_multiplicity] at hle ⊢
  have hv : 1 ≤ (Nat.card J).factorization 3 :=
    (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three Nat.card_pos.ne').1 h3
  have hv2 : (Nat.card J).factorization 3 ≤ 1 := by
    by_contra hc
    have : 3 ^ 2 ≤ 3 ^ (Nat.card J).factorization 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [show (Nat.card J).factorization 3 = 1 by omega, pow_one]

theorem LayerConfig.factorization_eq_one (h : LayerConfig X Q) {J : Subgroup X}
    (hJ : IsComponentOf J ⊤) : (Nat.card J).factorization 3 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T⟩ : Nonempty (Sylow 3 J) := inferInstance
  have h1 := h.card_sylow hJ T
  rw [T.card_eq_multiplicity] at h1
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) (h1.trans (pow_one 3).symm)

theorem LayerConfig.component_eq (h : LayerConfig X Q) {J₁ J₂ : Subgroup X}
    (h₁ : IsComponentOf J₁ ⊤) (h₂ : IsComponentOf J₂ ⊤) : J₁ = J₂ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := normal_of_le_center h.central
  by_contra hne
  have hZ₁ := center_eq_bot h.core h.ab h₁
  have hZ₂ := center_eq_bot h.core h.ab h₂
  have hc : J₂ ≤ Subgroup.centralizer (J₁ : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne J₂ J₁ h₂ h₁ (Ne.symm hne))
  obtain ⟨T₁⟩ : Nonempty (Sylow 3 J₁) := inferInstance
  obtain ⟨T₂⟩ : Nonempty (Sylow 3 J₂) := inferInstance
  set T₁' := (T₁ : Subgroup J₁).map J₁.subtype with hT₁'
  set T₂' := (T₂ : Subgroup J₂).map J₂.subtype with hT₂'
  have hT₁J : T₁' ≤ J₁ := Subgroup.map_subtype_le _
  have hT₂J : T₂' ≤ J₂ := Subgroup.map_subtype_le _
  have hT₁c : Nat.card T₁' = 3 :=
    (Subgroup.card_map_of_injective J₁.subtype_injective).trans (h.card_sylow h₁ T₁)
  have hT₂c : Nat.card T₂' = 3 :=
    (Subgroup.card_map_of_injective J₂.subtype_injective).trans (h.card_sylow h₂ T₂)
  have hN : T₁' ≤ Subgroup.normalizer (T₂' : Set X) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_iff.1 (hc (hT₂J hb)) a (hT₁J ha) |>.symm
  have hU : IsPGroup 3 ↥(T₁' ⊔ T₂') :=
    (T₁.isPGroup'.map J₁.subtype).to_sup_of_normal_right' (T₂.isPGroup'.map J₂.subtype) hN
  obtain ⟨S, hUS, -, hS3⟩ := h.exists_sylow hU
  have e₁ : T₁'.map (QuotientGroup.mk' Q) = (S : Subgroup X).map (QuotientGroup.mk' Q) := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono (le_sup_left.trans hUS)) ?_
    rw [hS3, card_map_eq_of_inf_eq_bot (inf_eq_bot_of_le_center hZ₁ h.central hT₁J), hT₁c]
  have h₂le : T₂' ≤ T₁' ⊔ Q := by
    have h1 := Subgroup.map_mono (f := QuotientGroup.mk' Q)
      (le_sup_right.trans hUS : T₂' ≤ (S : Subgroup X))
    rw [← e₁] at h1
    have h2 := Subgroup.comap_mono (f := QuotientGroup.mk' Q) h1
    rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2
    exact le_sup_left.trans h2
  have hT₂ne : T₂' ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hT₂c
    omega
  obtain ⟨t₂, ht₂1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hT₂ne
  obtain ⟨t₁, ht₁, q, hq, hqt⟩ := Subgroup.mem_sup_of_normal_right.1 (h₂le t₂.2)
  have ht₁1 : t₁ = 1 := by
    refine eq_one_of_commute hZ₁ (hT₁J ht₁) fun j hj => ?_
    have e : t₁ = (t₂ : X) * q⁻¹ := by rw [← hqt]; group
    have hj2 : j * (t₂ : X) = t₂ * j := (Subgroup.mem_centralizer_iff.1 (hc (hT₂J t₂.2)) j hj)
    rw [e]
    calc j * ((t₂ : X) * q⁻¹) = (j * t₂) * q⁻¹ := by group
      _ = (t₂ * j) * q⁻¹ := by rw [hj2]
      _ = t₂ * (q⁻¹ * j) := by
          rw [mul_assoc, Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ (h.central hq)) j]
      _ = (t₂ : X) * q⁻¹ * j := by group
  rw [ht₁1, one_mul] at hqt
  have hbot := inf_eq_bot_of_le_center hZ₂ h.central hT₂J
  have : (t₂ : X) ∈ Q ⊓ T₂' := ⟨hqt ▸ hq, t₂.2⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact ht₂1 (Subtype.ext this)

end Components

section GoodLayer

variable {X : Type} [Group X] [Finite X]

structure GoodLayer (X : Type) [Group X] [Finite X] (J : Subgroup X) : Prop where
  comp : ∀ K : Subgroup X, IsComponentOf K ⊤ → K = J
  char : ∀ σ : MulAut X, J.map (σ : X →* X) = J
  cent : J ≤ Subgroup.centralizer (CFSG.pCore 3 X : Set X)
  inn : ∀ σ : MulAut J, ∀ k : ℕ, σ ^ (3 ^ k) = 1 → σ ∈ inner J
  card : ∀ H : Subgroup (MulAut J), IsPGroup 3 H → Nat.card H ≤ 3

theorem mem_inner_of_pow_eq_one {J : Type*} [Group J] [Finite J]
    (hout : ¬ 3 ∣ Nat.card (Outer J)) {σ : MulAut J} {k : ℕ} (hσ : σ ^ (3 ^ k) = 1) :
    σ ∈ inner J := by
  have h1 : orderOf (σ : Outer J) ∣ 3 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hσ, QuotientGroup.mk_one])
  have h2 : orderOf (σ : Outer J) ∣ Nat.card (Outer J) := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (3 ^ k) (Nat.card (Outer J)) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hout)
  have h3 : orderOf (σ : Outer J) = 1 := Nat.dvd_one.1 (hcop ▸ Nat.dvd_gcd h1 h2)
  rwa [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3

theorem card_le_three {J : Type*} [Group J] [Finite J] (hZ : Subgroup.center J = ⊥)
    (h3 : (Nat.card J).factorization 3 = 1) (hout : ¬ 3 ∣ Nat.card (Outer J))
    {H : Subgroup (MulAut J)} (hH : IsPGroup 3 H) : Nat.card H ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : H ≤ inner J := fun σ hσ => by
    obtain ⟨k, hk⟩ := hH ⟨σ, hσ⟩
    exact mem_inner_of_pow_eq_one hout (k := k) (by simpa using congrArg Subtype.val hk)
  have hH' : IsPGroup 3 (H.subgroupOf (inner J)) :=
    hH.comap_of_injective (inner J).subtype (inner J).subtype_injective
  obtain ⟨S, hS⟩ := hH'.exists_le_sylow
  have hcardS : Nat.card (S : Subgroup (inner J)) = 3 := by
    rw [S.card_eq_multiplicity, ← Nat.card_congr (GL83.I713.innerEquiv J hZ).toEquiv, h3,
      pow_one]
  calc Nat.card H = Nat.card (H.subgroupOf (inner J)) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).symm
    _ ≤ Nat.card (S : Subgroup (inner J)) := Subgroup.card_le_of_le hS
    _ = 3 := hcardS

theorem LayerConfig.exists_goodLayer {Q : Subgroup X} (h : LayerConfig X Q)
    (hout : ∀ J : Subgroup X, IsComponentOf J ⊤ → Subgroup.center J = ⊥ →
      (Nat.card J).factorization 3 = 1 → ¬ 3 ∣ Nat.card (Outer J)) :
    ∃ J : Subgroup X, GoodLayer X J := by
  by_cases hex : ∃ J : Subgroup X, IsComponentOf J ⊤
  · obtain ⟨J, hJ⟩ := hex
    have hZ := center_eq_bot h.core h.ab hJ
    have h3 := h.factorization_eq_one hJ
    have ho := hout J hJ hZ h3
    refine ⟨J, ⟨fun K hK => h.component_eq hK hJ, fun σ => ?_, component_le_centralizer_pCore hJ,
      fun σ k hσ => mem_inner_of_pow_eq_one ho hσ, fun H hH => card_le_three hZ h3 ho hH⟩⟩
    exact h.component_eq ((CFSG.ComponentClassification.LocalComponents.equiv_iff σ J).2 hJ) hJ
  · simp only [not_exists] at hex
    have hsub : Subsingleton (MulAut (⊥ : Subgroup X)) :=
      ⟨fun a b => MulEquiv.ext fun x => Subsingleton.elim _ _⟩
    refine ⟨⊥, ⟨fun K hK => (hex K hK).elim, fun σ => Subgroup.map_bot _, bot_le, ?_, ?_⟩⟩
    · intro σ k _
      rw [Subsingleton.elim σ 1]
      exact Subgroup.one_mem _
    · intro H _
      have h1 := Subgroup.card_le_card_group H
      have h2 := Finite.card_le_one_iff_subsingleton.2 hsub
      omega

theorem GoodLayer.normal {J : Subgroup X} (hJ : GoodLayer X J) : J.Normal :=
  ⟨fun n hn g => by
    rw [← hJ.char (MulAut.conj g)]
    exact ⟨n, hn, rfl⟩⟩

theorem GoodLayer.sylow_le (hcore : GLAPPrimeCore 3 X = ⊥) {J : Subgroup X} (hJ : GoodLayer X J)
    (P : Sylow 3 X) (hPab : ∀ a ∈ (P : Subgroup X), ∀ b ∈ (P : Subgroup X), a * b = b * a) :
    (P : Subgroup X) ≤ J ⊔ CFSG.pCore 3 X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (CFSG.pCore 3 X).Normal := CFSG.pCore_normal
  haveI := hJ.normal
  intro x hx
  have hOP : CFSG.pCore 3 X ≤ P := (CFSG.pCore_isPGroup (p := 3)).le_sylow_of_normal P
  have hxO : x ∈ Subgroup.centralizer (CFSG.pCore 3 X : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    exact hPab o (hOP ho) x hx
  have hxN : x ∈ Subgroup.normalizer (J : Set X) := by
    rw [Subgroup.normalizer_eq_top J]
    exact Subgroup.mem_top x
  set σ := J.normalizerMonoidHom ⟨x, hxN⟩ with hσdef
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
  have hxk : x ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hσ : σ ^ (3 ^ k) = 1 := by
    rw [hσdef, ← map_pow]
    have : (⟨x, hxN⟩ : Subgroup.normalizer (J : Set X)) ^ (3 ^ k) = 1 :=
      Subtype.ext (by simpa using hxk)
    rw [this, map_one]
  obtain ⟨y, hy⟩ := hJ.inn σ k hσ
  have hconj : ∀ j ∈ J, x * j * x⁻¹ = (y : X) * j * (y : X)⁻¹ := by
    intro j hj
    have h1 : ((MulAut.conj y ⟨j, hj⟩ : J) : X) = ((σ ⟨j, hj⟩ : J) : X) := by rw [hy]
    rw [MulAut.conj_apply] at h1
    exact h1.symm
  have hc : (y : X)⁻¹ * x ∈ CFSG.pCore 3 X := by
    refine mem_pCore_of_centralizes Nat.prime_three hcore
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hJ.cent y.2)) hxO) ?_
    intro K hK
    rw [hJ.comp K hK, Subgroup.mem_centralizer_iff]
    intro j hj
    have := hconj j hj
    calc j * ((y : X)⁻¹ * x) = (y : X)⁻¹ * ((y : X) * j * (y : X)⁻¹) * x := by group
      _ = (y : X)⁻¹ * (x * j * x⁻¹) * x := by rw [this]
      _ = (y : X)⁻¹ * x * j := by group
  have e : x = (y : X) * ((y : X)⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left y.2) (Subgroup.mem_sup_right hc)

theorem GoodLayer.top_le (hcore : GLAPPrimeCore 3 X = ⊥) {J : Subgroup X} (hJ : GoodLayer X J)
    (P : Sylow 3 X) (hPab : ∀ a ∈ (P : Subgroup X), ∀ b ∈ (P : Subgroup X), a * b = b * a) :
    (⊤ : Subgroup X) ≤ Subgroup.normalizer (P : Set X) ⊔ J := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (CFSG.pCore 3 X).Normal := CFSG.pCore_normal
  haveI := hJ.normal
  have h := Sylow.normalizer_sup_eq_top' P (hJ.sylow_le hcore P hPab)
  rw [← h]
  refine sup_le le_sup_left (sup_le le_sup_right ?_)
  exact ((CFSG.pCore_isPGroup (p := 3)).le_sylow_of_normal P).trans
    (Subgroup.le_normalizer.trans le_sup_left)

end GoodLayer

section Action

theorem map_core {Y : Type} [Group Y] (σ : MulAut Y) :
    (GLAPPrimeCore 3 Y).map (σ : Y →* Y) = GLAPPrimeCore 3 Y :=
  Subgroup.characteristic_iff_map_eq.1 CFSG.pPrimeCore_characteristic σ

@[expose] noncomputable def quotAut (Y : Type) [Group Y] :
    MulAut Y →* MulAut (Y ⧸ GLAPPrimeCore 3 Y) where
  toFun σ := QuotientGroup.congr _ _ σ (map_core σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

@[expose] noncomputable def restrictAut {X : Type} [Group X] (J : Subgroup X)
    (hJ : ∀ σ : MulAut X, J.map (σ : X →* X) = J) : MulAut X →* MulAut J where
  toFun σ := (σ.subgroupMap J).trans (MulEquiv.subgroupCongr (hJ σ))
  map_one' := by ext; rfl
  map_mul' σ τ := by ext; rfl

@[expose] def fixSub {B Y : Type} [Group B] [Group Y] (β : B →* MulAut Y) (E : Subgroup B) :
    Subgroup Y where
  carrier := {y | ∀ e ∈ E, β e y = y}
  mul_mem' := fun {a b} ha hb e he => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha e he, hb e he]
  one_mem' := fun e _ => map_one _
  inv_mem' := fun {a} ha e he => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha e he]

theorem mem_fixSub {B Y : Type} [Group B] [Group Y] {β : B →* MulAut Y} {E : Subgroup B} {y : Y} :
    y ∈ fixSub β E ↔ ∀ e ∈ E, β e y = y :=
  Iff.rfl

theorem exists_fixed_mem_coset {B Y : Type} [Group B] [Group Y] [Finite Y] (β : B →* MulAut Y)
    {E : Subgroup B} (hE : IsPGroup 3 E) {N : Subgroup Y} (hN : ¬ 3 ∣ Nat.card N)
    (hβN : ∀ e ∈ E, ∀ n ∈ N, β e n ∈ N) {l : Y} (hl : ∀ e ∈ E, l⁻¹ * β e l ∈ N) :
    ∃ n ∈ N, l * n ∈ fixSub β E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let α := {y : Y // l⁻¹ * y ∈ N}
  letI : MulAction E α :=
    { smul := fun e y => ⟨β e y, by
        have h1 := hl e e.2
        have h2 := hβN e e.2 _ y.2
        rw [map_mul, map_inv] at h2
        have e' : l⁻¹ * β (e : B) y = (l⁻¹ * β e l) * ((β e l)⁻¹ * β e y) := by group
        rw [e']
        exact N.mul_mem h1 h2⟩
      one_smul := fun y => Subtype.ext (show β ((1 : E) : B) y = y by
        rw [OneMemClass.coe_one, map_one]; rfl)
      mul_smul := fun a b y => Subtype.ext (show β ((a * b : E) : B) y = β a (β b y) by
        rw [Subgroup.coe_mul, map_mul]; rfl) }
  have hcard : Nat.card α = Nat.card N := Nat.card_congr
    { toFun := fun y => ⟨l⁻¹ * y, y.2⟩
      invFun := fun n => ⟨l * n, by simpa using n.2⟩
      left_inv := fun y => Subtype.ext (by simp)
      right_inv := fun n => Subtype.ext (by simp) }
  obtain ⟨y, hy⟩ := hE.nonempty_fixed_point_of_prime_not_dvd_card α (by rwa [hcard])
  refine ⟨l⁻¹ * y, y.2, ?_⟩
  rw [mul_inv_cancel_left, mem_fixSub]
  intro e he
  exact congrArg Subtype.val (hy ⟨e, he⟩)

end Action

section LayerStep

variable {Y : Type} [Group Y] [Finite Y]

theorem GoodLayer.exists_sub {B : Type} [Group B] [Finite B] (hB : IsPGroup 3 B)
    (hB27 : Nat.card B = 27) (β : B →* MulAut Y) {J : Subgroup (Y ⧸ GLAPPrimeCore 3 Y)}
    (hJ : GoodLayer _ J) :
    ∃ E : Subgroup B, Nat.card E = 9 ∧
      J.comap (QuotientGroup.mk' (GLAPPrimeCore 3 Y)) ≤ GLAPPrimeCore 3 Y ⊔ fixSub β E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := GLAPPrimeCore 3 Y with hNdef
  set ψ : B →* MulAut J := (restrictAut J hJ.char).comp ((quotAut Y).comp β) with hψ
  have hrange : Nat.card ψ.range ≤ 3 :=
    hJ.card _ (hB.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective)
  have hmul : Nat.card ψ.ker * Nat.card ψ.range = 27 := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index, hB27]
  have h9 : 3 ^ 2 ∣ Nat.card ψ.ker := by
    have hdvd : Nat.card ψ.ker ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hB27]
      exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    rw [hj']
    refine Nat.pow_dvd_pow 3 ?_
    by_contra hlt
    have hj1 : 3 ^ j ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hj'] at hmul
    have h := Nat.mul_le_mul hj1 hrange
    rw [hmul] at h
    norm_num at h
  obtain ⟨E', hE'⟩ := Sylow.exists_subgroup_card_pow_prime 3 h9
  set E := E'.map ψ.ker.subtype with hE
  have hEcard : Nat.card E = 9 := by
    rw [hE, Subgroup.card_map_of_injective ψ.ker.subtype_injective, hE']
    norm_num
  refine ⟨E, hEcard, ?_⟩
  have hEker : E ≤ ψ.ker := Subgroup.map_subtype_le _
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hEcard]; norm_num)
  have hNc : ¬ 3 ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card
  have hβN : ∀ e ∈ E, ∀ n ∈ N, β e n ∈ N := by
    intro e _ n hn
    have hm : N.map (β e : Y →* Y) = N := map_core (β e)
    rw [← hm]
    exact ⟨n, hn, rfl⟩
  intro l hl
  have hfix : ∀ e ∈ E, l⁻¹ * β e l ∈ N := by
    intro e he
    have h1 : ψ e = 1 := MonoidHom.mem_ker.1 (hEker he)
    have h2 : ((ψ e ⟨QuotientGroup.mk' N l, hl⟩ : J) : Y ⧸ N) =
        (((1 : MulAut J) ⟨QuotientGroup.mk' N l, hl⟩ : J) : Y ⧸ N) := by rw [h1]
    change ((β e l : Y) : Y ⧸ N) = ((l : Y) : Y ⧸ N) at h2
    rw [QuotientGroup.eq] at h2
    simpa using N.inv_mem h2
  obtain ⟨n, hn, hln⟩ := exists_fixed_mem_coset β hEp hNc hβN hfix
  have e' : l = (l * n) * n⁻¹ := by group
  rw [e']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hln) (Subgroup.mem_sup_left (N.inv_mem hn))

omit [Finite Y] in
theorem isSimpleGroup_of_center_eq_bot {X : Type} [Group X] {J : Subgroup X}
    (hJ : IsComponentOf J ⊤) (hZ : Subgroup.center J = ⊥) : IsSimpleGroup J := by
  haveI := hJ.2.2.2
  exact ((QuotientGroup.quotientBot (G := J)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ.symm)).isSimpleGroup

omit [Finite Y] in
theorem nonabelian_of_component {X : Type} [Group X] {J : Subgroup X} (hJ : IsComponentOf J ⊤)
    (hZ : Subgroup.center J = ⊥) : ∃ a b : J, a * b ≠ b * a :=
  CFSG.KCore.nonabelian_of_mulEquiv ((QuotientGroup.quotientBot (G := J)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ.symm))
    (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian J hJ.2.2)

theorem isCatalogGroup_of_le_quotient (hK : CFSG.KCore.KGroupNonab @CFSG.Open.IsCatalogGroup Y)
    (J : Subgroup (Y ⧸ GLAPPrimeCore 3 Y)) [IsSimpleGroup J] (hnonab : ∃ a b : J, a * b ≠ b * a) :
    CFSG.Open.IsCatalogGroup J := by
  let π := QuotientGroup.mk' (GLAPPrimeCore 3 Y)
  let L := J.comap π
  let φ : L →* J := (π.comp L.subtype).codRestrict J (fun l => l.2)
  have hφ : Function.Surjective φ := by
    rintro ⟨j, hj⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ j
    exact ⟨⟨y, hj⟩, rfl⟩
  exact CFSG.KCore.KGroupNonab.catalogue_of_surjective
    (fun e ⟨i, ⟨ψ⟩⟩ => ⟨i, ⟨e.trans ψ⟩⟩) hK L hnonab φ hφ

theorem core_inf_eq_bot {U : Subgroup Y} (hU : IsPGroup 3 U) : GLAPPrimeCore 3 Y ⊓ U = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hU.exists_card_eq
  refine Subgroup.inf_eq_bot_of_coprime ?_
  rw [hk]
  exact Nat.Coprime.pow_right k (CFSG.pPrimeCore_coprime_card (p := 3) (G := Y)).symm

theorem layerConfig_of {Q : Subgroup Y} (hQZ : Q ≤ Subgroup.center Y) (hQ9 : Nat.card Q = 9)
    (P : Sylow 3 Y) (hPab : ∀ a ∈ (P : Subgroup Y), ∀ b ∈ (P : Subgroup Y), a * b = b * a)
    (hP27 : Nat.card (P : Subgroup Y) = 27) :
    LayerConfig (Y ⧸ GLAPPrimeCore 3 Y) (Q.map (QuotientGroup.mk' (GLAPPrimeCore 3 Y))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := GLAPPrimeCore 3 Y with hN
  set π := QuotientGroup.mk' N with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  set P' := P.mapSurjective hπ with hP'
  have hP'c : Nat.card (P' : Subgroup (Y ⧸ N)) = 27 := by
    rw [hP', Sylow.coe_mapSurjective, card_map_eq_of_inf_eq_bot (core_inf_eq_bot P.isPGroup'),
      hP27]
  have hP'ab : ∀ u ∈ (P' : Subgroup (Y ⧸ N)), ∀ v ∈ (P' : Subgroup (Y ⧸ N)), u * v = v * u := by
    rw [hP', Sylow.coe_mapSurjective]
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    rw [← map_mul, ← map_mul, hPab u hu v hv]
  refine ⟨CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCore_quotient_eq_bot Nat.prime_three, ?_, ?_, ?_,
    ?_⟩
  · intro S a ha b hb
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (Y ⧸ N) P' S
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at ha hb
    have ha' : g⁻¹ * a * g ∈ (P' : Subgroup (Y ⧸ N)) := by
      simpa [MulAut.smul_def, MulAut.conj_apply] using ha
    have hb' : g⁻¹ * b * g ∈ (P' : Subgroup (Y ⧸ N)) := by
      simpa [MulAut.smul_def, MulAut.conj_apply] using hb
    have h2 : g⁻¹ * (a * b) * g = g⁻¹ * (b * a) * g := by
      calc g⁻¹ * (a * b) * g = g⁻¹ * a * g * (g⁻¹ * b * g) := by group
        _ = g⁻¹ * b * g * (g⁻¹ * a * g) := hP'ab _ ha' _ hb'
        _ = g⁻¹ * (b * a) * g := by group
    simpa using h2
  · intro S
    rw [S.card_eq_multiplicity, ← P'.card_eq_multiplicity, hP'c]
  · rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := hπ g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 (hQZ hq) y]
  · have hQp : IsPGroup 3 Q := IsPGroup.of_card (n := 2) (by rw [hQ9]; norm_num)
    rw [card_map_eq_of_inf_eq_bot (core_inf_eq_bot hQp), hQ9]

theorem layer_step (hK : CFSG.KCore.KGroupNonab @CFSG.Open.IsCatalogGroup Y)
    (hI : ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
      CFSG.Open.IsCatalogGroup K → (Nat.card K).factorization 3 = 1 → ¬ 3 ∣ Nat.card (Outer K))
    {Q : Subgroup Y} (hQZ : Q ≤ Subgroup.center Y) (hQ9 : Nat.card Q = 9) (P : Sylow 3 Y)
    (hPab : ∀ a ∈ (P : Subgroup Y), ∀ b ∈ (P : Subgroup Y), a * b = b * a)
    (hP27 : Nat.card (P : Subgroup Y) = 27) {B : Type} [Group B] [Finite B] (hB : IsPGroup 3 B)
    (hB27 : Nat.card B = 27) (β : B →* MulAut Y) :
    ∃ E : Subgroup B, Nat.card E = 9 ∧
      (⊤ : Subgroup Y) ≤ GLAPPrimeCore 3 Y ⊔ Subgroup.normalizer (P : Set Y) ⊔ fixSub β E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := GLAPPrimeCore 3 Y with hN
  set π := QuotientGroup.mk' N with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hcfg := layerConfig_of hQZ hQ9 P hPab hP27
  obtain ⟨J, hJ⟩ := hcfg.exists_goodLayer fun J hJ hZ h3 => by
    haveI := isSimpleGroup_of_center_eq_bot hJ hZ
    exact hI J inferInstance (nonabelian_of_component hJ hZ)
      (isCatalogGroup_of_le_quotient hK J (nonabelian_of_component hJ hZ)) h3
  obtain ⟨E, hE9, hLE⟩ := hJ.exists_sub hB hB27 β
  refine ⟨E, hE9, ?_⟩
  set P' := P.mapSurjective hπ with hP'
  have htop := hJ.top_le hcfg.core P' (hcfg.ab P')
  have hNc : ¬ 3 ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card
  have hnorm := CFSG.RankThree.PartTwo.Sec4.map_normalizer_eq_of_not_dvd Nat.prime_three N hNc
    P.isPGroup'
  have h1 := Subgroup.comap_mono (f := π) htop
  rw [Subgroup.comap_top, ← Subgroup.comap_sup_eq_of_le_range π
    (by rw [MonoidHom.range_eq_top.2 hπ]; exact le_top)
    (by rw [MonoidHom.range_eq_top.2 hπ]; exact le_top)] at h1
  have h2 : (Subgroup.normalizer (P' : Set (Y ⧸ N))).comap π =
      Subgroup.normalizer (P : Set Y) ⊔ N := by
    have e2 : Subgroup.normalizer (P' : Set (Y ⧸ N)) =
        (Subgroup.normalizer ((P : Subgroup Y) : Set Y)).map π := by
      rw [hnorm]
      rfl
    rw [e2, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    rfl
  rw [h2] at h1
  refine h1.trans (sup_le (sup_le (le_sup_right.trans le_sup_left)
    (le_sup_left.trans le_sup_left)) (hLE.trans (sup_le (le_sup_left.trans le_sup_left)
      le_sup_right)))

end LayerStep

@[expose] def I_7_13_3 : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → CFSG.Open.IsCatalogGroup K → (Nat.card K).factorization p = 1 →
      ¬ p ∣ Nat.card (Outer K)

theorem exists_sylow_map_eq {G : Type} [Group G] {C P : Subgroup G} (hP : IsSylowIn 3 C P) :
    ∃ S : Sylow 3 C, (S : Subgroup C).map C.subtype = P := by
  have hPC : IsPGroup 3 (P.subgroupOf C) :=
    hP.2.1.comap_of_injective C.subtype C.subtype_injective
  obtain ⟨S, hS⟩ := hPC.exists_le_sylow
  refine ⟨S, hP.2.2 _ (Subgroup.map_subtype_le _) (S.isPGroup'.map _) ?_⟩
  intro x hx
  exact ⟨⟨x, hP.1 hx⟩, hS (Subgroup.mem_subgroupOf.2 hx), rfl⟩

theorem centralizerLayerInput_of_I_7_13_3 (hI : I_7_13_3) : Claims135b.CentralizerLayerInput := by
  intro G _ _ hK Q P₁ B₀ hQe hQc hCtop hsyl hab h27 hB₀N hB₀e hB₀c
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer (Q : Set G) with hC
  have hKC : CFSG.KCore.KGroupNonab @CFSG.Open.IsCatalogGroup C :=
    CFSG.KCore.KProperNonab.kGroupNonab (fun e ⟨i, ⟨ψ⟩⟩ => ⟨i, ⟨e.trans ψ⟩⟩) hK C hCtop
  have hQC : Q ≤ C := fun q hq => Subgroup.mem_centralizer_iff.2 fun r hr =>
    congrArg Subtype.val (hQe.1.is_comm.comm ⟨r, hr⟩ ⟨q, hq⟩)
  have hQZ : Q.subgroupOf C ≤ Subgroup.center C := fun q hq =>
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_centralizer_iff.1 g.2 q hq).symm
  have hQ9 : Nat.card (Q.subgroupOf C) = 9 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv).trans hQc
  obtain ⟨S, hS⟩ := exists_sylow_map_eq hsyl
  have hSP : ∀ a ∈ (S : Subgroup C), (a : G) ∈ P₁ := fun a ha => by
    rw [← hS]
    exact ⟨a, ha, rfl⟩
  have hSab : ∀ a ∈ (S : Subgroup C), ∀ b ∈ (S : Subgroup C), a * b = b * a := fun a ha b hb =>
    Subtype.ext (hab a (hSP a ha) b (hSP b hb))
  have hS27 : Nat.card (S : Subgroup C) = 27 := by
    rw [← Subgroup.card_map_of_injective C.subtype_injective, hS, h27]
  have hB₀C : B₀ ≤ Subgroup.normalizer (C : Set G) :=
    hB₀N.trans (Lemma135.le_normalizer_centralizer_of_le le_rfl)
  let β : B₀ →* MulAut C := C.normalizerMonoidHom.comp (Subgroup.inclusion hB₀C)
  have hB₀p : IsPGroup 3 B₀ := IsPGroup.of_card (n := 3) (by rw [hB₀c]; norm_num)
  obtain ⟨E, hE9, hle⟩ := layer_step hKC (hI 3 Nat.prime_three (by norm_num)) hQZ hQ9 S hSab
    hS27 hB₀p hB₀c β
  set T : Subgroup G := GLAPPrimeCoreOf 3 C ⊔ Subgroup.normalizer (P₁ : Set G) ⊔
    ⨆ (E : Subgroup G) (_ : E ≤ B₀ ∧ Nat.card ↥E = 9), Subgroup.centralizer (E : Set G) with hT
  have h₁ : (GLAPPrimeCore 3 C).map C.subtype ≤ T := le_sup_left.trans le_sup_left
  have h₂ : (Subgroup.normalizer ((S : Subgroup C) : Set C)).map C.subtype ≤ T := by
    refine le_trans ?_ (le_sup_right.trans le_sup_left)
    rw [← hS]
    exact Subgroup.le_normalizer_map _
  have h₃ : (fixSub β E).map C.subtype ≤ T := by
    refine le_trans ?_ le_sup_right
    refine le_trans ?_ (le_iSup₂_of_le (f := fun E (_ : E ≤ B₀ ∧ Nat.card ↥E = 9) =>
      Subgroup.centralizer (E : Set G)) (E.map B₀.subtype)
      ⟨Subgroup.map_subtype_le _, by rw [Subgroup.card_map_of_injective B₀.subtype_injective, hE9]⟩
      le_rfl)
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨e, he, rfl⟩
    have h1 : ((β e y : C) : G) = y := congrArg Subtype.val ((mem_fixSub.1 hy) e he)
    change (e : G) * y * (e : G)⁻¹ = y at h1
    change (e : G) * y = y * e
    calc (e : G) * y = (e : G) * y * (e : G)⁻¹ * e := by group
      _ = y * e := by rw [h1]
  intro c hc
  have hmem := Subgroup.mem_map_of_mem C.subtype (hle (Subgroup.mem_top ⟨c, hc⟩))
  rw [Subgroup.map_sup, Subgroup.map_sup] at hmem
  exact (sup_le (sup_le h₁ h₂) h₃) hmem

section Certified

set_option linter.unusedSectionVars false

theorem i_7_13_3_holds : I_7_13_3 := by
  intro p hp hp2 K _ _ hs hnab hcat h1
  haveI : IsSimpleGroup K := hs
  haveI : Fact p.Prime := ⟨hp⟩
  exact CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.not_dvd_card_outer_of_sylow_card_eq_prime
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.reducedOuterSylow_holds hp hp2 hnab hcat
    (fun S => by rw [Sylow.card_eq_multiplicity, h1, pow_one])

theorem centralizerLayerInput_holds : Claims135b.CentralizerLayerInput :=
  centralizerLayerInput_of_I_7_13_3 i_7_13_3_holds

end Certified

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims135c
