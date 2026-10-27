module

public import CFSG.GH74.GLS.C3.Layer1.EvenMax
public import CFSG.GH74.GLS.TwoThin.Bridge
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.GH74.GLS.C3.Layer1.Th2CaseI
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31s

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.ComponentClassification
open scoped commutatorElement

namespace CFSG.GH74.GLS.EvenSel

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q N : Subgroup G}

theorem isQuasisimple_K (hs : EvenSel x K T Q) : IsQuasisimple ↥K :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hs.K_le_C)
    hs.terminal.2.1.2.1

theorem isPCompIn_of_le_normalizer
    (hs : EvenSel x K T Q) {X : Subgroup G} (hKX : K ≤ X) (hXN : X ≤ normalizer (K : Set G)) :
    IsPCompIn 2 X K := by
  refine ⟨hKX, ?_⟩
  have hq : IsQuasisimple ↥(K.subgroupOf X) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKX).symm
      hs.isQuasisimple_K
  have hKs := hs.K_simple
  have hKs' : IsSimpleGroup ↥(K.subgroupOf X) :=
    (Subgroup.subgroupOfEquivOfLe hKX).isSimpleGroup
  have hZ : center ↥(K.subgroupOf X) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥(K.subgroupOf X)) with hb | ht
    · exact hb
    · exfalso
      obtain ⟨-, -, a', b', hab'⟩ := hq
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a'
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b'
      apply hab'
      have : a ∈ center ↥(K.subgroupOf X) := by rw [ht]; exact Subgroup.mem_top _
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (Subgroup.mem_center_iff.1 this b)]
  have h2 : 2 ∣ Nat.card ↥(K.subgroupOf X) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv]
    exact hs.two_dvd_K
  exact isPComponent_two_of_normal'
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXN) hq hZ h2

end CFSG.GH74.GLS.EvenSel

namespace CFSG.GH74.GLS.EvenCore

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q N : Subgroup G}

theorem centralizer_le_normalizer_of_mem (hgam : gammaK 2 Q 1 ≤ normalizer (K : Set G)) {u : G}
    (hu : u ∈ Q) (hu2 : orderOf u = 2) :
    centralizer ({u} : Set G) ≤ normalizer (K : Set G) :=
  (C3.Layer1.U1a.centralizer_le_gammaK hu hu2).trans hgam

theorem exists_conj_mem_Q {y : G} (hQ : IsSylowOf 2 Q (centralizer (K : Set G)))
    (hy : y ∈ centralizer (K : Set G)) (hy2 : orderOf y = 2) :
    ∃ c ∈ centralizer (K : Set G), c⁻¹ * y * c ∈ Q := by
  have hp : IsPGroup 2 ↥(zpowers y) := by
    have : Nat.card ↥(zpowers y) = 2 := by rw [Nat.card_zpowers, hy2]
    exact IsPGroup.of_card (n := 1) (by rw [this]; simp)
  obtain ⟨k, hk, hkQ⟩ := C3.Layer1.Thm1.exists_conj_le_of_isSylowOf hQ
    (X := zpowers y) (by rw [zpowers_le]; exact hy) hp
  exact ⟨k, hk, hkQ y (mem_zpowers y)⟩

theorem centralizer_le_of_mem_centralizer (hQ : IsSylowOf 2 Q (centralizer (K : Set G)))
    (hgam : gammaK 2 Q 1 ≤ normalizer (K : Set G)) (hMN : normalizer (K : Set G) ≤ N)
    {y : G} (hy : y ∈ centralizer (K : Set G)) (hy2 : orderOf y = 2) :
    centralizer ({y} : Set G) ≤ N := by
  obtain ⟨c, hc, hcQ⟩ := exists_conj_mem_Q hQ hy hy2
  have hcN : c ∈ N := hMN (centralizer_le_normalizer _ hc)
  have hord : orderOf (c⁻¹ * y * c) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj c⁻¹) y
    simpa [MulAut.conj_apply] using this.trans hy2
  intro g hg
  have hg' : c⁻¹ * g * c ∈ centralizer ({c⁻¹ * y * c} : Set G) := by
    rw [mem_centralizer_singleton_iff] at hg ⊢
    calc c⁻¹ * g * c * (c⁻¹ * y * c) = c⁻¹ * (g * y) * c := by group
      _ = c⁻¹ * (y * g) * c := by rw [hg]
      _ = c⁻¹ * y * c * (c⁻¹ * g * c) := by group
  have h1 : c⁻¹ * g * c ∈ N := hMN (centralizer_le_normalizer_of_mem hgam hcQ hord hg')
  have := N.mul_mem (N.mul_mem hcN h1) (N.inv_mem hcN)
  simpa [mul_assoc] using this

omit [Finite G] in
theorem le_pPrimeCoreOf_two {A X : Subgroup G} (hAX : A ≤ X) (hnorm : X ≤ normalizer (A : Set G))
    (hcop : Nat.Coprime 2 (Nat.card A)) : A ≤ pPrimeCoreOf 2 X := by
  have hnormal : (A.subgroupOf X).Normal := by
    refine ⟨fun a ha h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hnorm h.2) a).mp ha
  have hcop' : Nat.Coprime 2 (Nat.card (A.subgroupOf X)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv]
  have hle : A.subgroupOf X ≤ pPrimeCore 2 X := le_sSup ⟨hnormal, hcop'⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hAX]
  exact Subgroup.map_mono hle

theorem coprime_card_pPrimeCoreOf_two (X : Subgroup G) :
    Nat.Coprime 2 (Nat.card (pPrimeCoreOf 2 X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [pPrimeCoreOf, Subgroup.card_map_of_injective X.subtype_injective]
  exact pPrimeCore_coprime_card

theorem pPrimeCoreOf_eq_bot {Q N : Subgroup G} (hrk : 2 ≤ pRank 2 ↥Q) (hQN : Q ≤ N)
    (hC : ∀ b ∈ Q, orderOf b = 2 → centralizer ({b} : Set G) ≤ N)
    (hE : ∀ b : G, orderOf b = 2 → pPrimeCore 2 ↥(centralizer ({b} : Set G)) = ⊥) :
    pPrimeCoreOf 2 N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEQ, hE2, hEcard⟩ := Th2.CaseI.exists_elemAbelian_four hrk
  rw [eq_bot_iff]
  refine CFSG.Asc75.le_of_forall_inf_centralizer_le' hE2 hEcard ?_ ?_ ?_
  · have h := coprime_card_pPrimeCoreOf_two N
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 h
  · intro e he
    exact C3.Layer1.Back.Setup91.mem_normalizer_pPrimeCoreOf_self (hQN (hEQ he))
  · intro b hb hb1
    have hb2 : orderOf b = 2 :=
      orderOf_eq_prime (CFSG.elemPow_eq_one_of_isElementaryAbelian b hb) hb1
    have hCN : centralizer ({b} : Set G) ≤ N := hC b (hEQ hb) hb2
    have hcore : pPrimeCoreOf 2 (centralizer ({b} : Set G)) = ⊥ := by
      unfold pPrimeCoreOf
      rw [hE b hb2]
      exact Subgroup.map_bot _
    refine (le_pPrimeCoreOf_two (A := pPrimeCoreOf 2 N ⊓ centralizer ({b} : Set G))
      (X := centralizer ({b} : Set G)) inf_le_right ?_ ?_).trans hcore.le
    · intro c hc
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have h1 := Subgroup.mem_normalizer_iff.mp
        (C3.Layer1.Back.Setup91.mem_normalizer_pPrimeCoreOf_self (hCN hc)) h
      have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hc) h
      simp only [Subgroup.mem_inf]
      exact and_congr h1 h2
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        (coprime_card_pPrimeCoreOf_two N)

omit [Finite G] in
theorem centralizer_singleton_mk_eq (b : G) (hb : b ∈ N) :
    centralizer ({(⟨b, hb⟩ : ↥N)} : Set ↥N) = (centralizer ({b} : Set G)).subgroupOf N := by
  ext a
  rw [mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem isTwoComponent_in_N {b : G} (hb : b ∈ N) (hCN : centralizer ({b} : Set G) ≤ N)
    (hK : IsPCompIn 2 (centralizer ({b} : Set G)) K) :
    K.subgroupOf N ≤ centralizer ({(⟨b, hb⟩ : ↥N)} : Set ↥N) ∧
      TwoComponents.IsTwoComponent
        ((K.subgroupOf N).subgroupOf (centralizer ({(⟨b, hb⟩ : ↥N)} : Set ↥N))) := by
  obtain ⟨hKC, hKT⟩ := TwoThin.isPCompIn_two_iff.mp hK
  rw [centralizer_singleton_mk_eq b hb]
  refine ⟨?_, ?_⟩
  · intro a ha
    exact hKC ha
  · exact TwoThin.isTwoComponent_subgroupOf_subgroupOf hKC hCN hKT

theorem one_le_pRank_of_involution {H : Subgroup G} {y : G} (hy : y ∈ H) (hy2 : orderOf y = 2) :
    1 ≤ pRank 2 ↥H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let g : ↥H := ⟨y, hy⟩
  have hg : orderOf g = 2 := by rw [Subgroup.orderOf_mk]; exact hy2
  exact CFSG.LieType.SteinbergBR.le_pRank_of_card one_lt_two (zpowers g)
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 (zpowers g)).2
      (CFSG.ProperTwoGeneratedCore.involution_zpowers_elementary g hg))
    (k := 1) (by rw [Nat.card_zpowers, hg, pow_one])

theorem fitting_eq_bot (hcoreN : pPrimeCore 2 ↥N = ⊥)
    (hQC : IsSylowOf 2 Q (centralizer (K : Set G))) (hCKN : centralizer (K : Set G) ≤ N)
    (hgam : gammaK 2 Q 1 ≤ normalizer (K : Set G)) (hNM : ¬ N ≤ normalizer (K : Set G))
    (hKN : K ≤ N) (hKlayer : K.subgroupOf N ≤ CFSG.layer ↥N) : fittingSubgroup ↥N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  set F := fittingSubgroup ↥N with hF
  have hFn : F.Normal := inferInstance
  have hFp : IsPGroup 2 ↥F := isPGroup_of_nilpotent_normal F hFn inferInstance hcoreN
  set F' := F.map N.subtype with hF'
  have hF'p : IsPGroup 2 ↥F' :=
    hFp.of_equiv (F.equivMapOfInjective N.subtype N.subtype_injective)
  have hF'ne : F' ≠ ⊥ := by
    intro h
    exact hne ((Subgroup.map_eq_bot_iff_of_injective F N.subtype_injective).mp h)
  have hcomm : ⁅F, CFSG.layer ↥N⁆ = ⊥ := CFSG.LocalCores.fitting_layer_commute
  have hF'C : F' ≤ centralizer (K : Set G) := by
    rintro _ ⟨f, hf, rfl⟩
    rw [mem_centralizer_iff]
    intro k hk
    have hk' : (⟨k, hKN hk⟩ : ↥N) ∈ CFSG.layer ↥N := hKlayer hk
    have hc : ⁅f, (⟨k, hKN hk⟩ : ↥N)⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator hf hk'
      rw [hcomm, Subgroup.mem_bot] at this
      exact this
    have := commutatorElement_eq_one_iff_mul_comm.1 hc
    exact (congrArg Subtype.val this).symm
  have hF'N : ∀ n ∈ N, ∀ y ∈ F', n * y * n⁻¹ ∈ F' := by
    rintro n hn _ ⟨f, hf, rfl⟩
    refine ⟨⟨n, hn⟩ * f * ⟨n, hn⟩⁻¹, hFn.conj_mem f hf ⟨n, hn⟩, ?_⟩
    simp
  obtain ⟨c, hc, hcQ⟩ := C3.Layer1.Thm1.exists_conj_le_of_isSylowOf hQC (X := F') hF'C hF'p
  have hcN : c ∈ N := hCKN hc
  have hF'Q : F' ≤ Q := by
    intro y hy
    have h1 := hcQ (c * y * c⁻¹) (hF'N c hcN y hy)
    simpa [mul_assoc] using h1
  obtain ⟨b, hbF', hb2⟩ := Th2.exists_involution_mem hF'p hF'ne
  have hr : 1 ≤ pRank 2 ↥F' := one_le_pRank_of_involution hbF' hb2
  have hNF : N ≤ normalizer (F' : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact fun hy => hF'N n hn y hy
    · intro hy
      have := hF'N n⁻¹ (N.inv_mem hn) _ hy
      simpa [mul_assoc] using this
  have hle : normalizer (F' : Set G) ≤ normalizer (K : Set G) := by
    refine le_trans ?_ hgam
    exact le_iSup_of_le F' (le_iSup_of_le hF'Q (le_iSup_of_le hr le_rfl))
  exact hNM (hNF.trans hle)

theorem exists_involution_of_isComponent {H : Type} [Group H] [Finite H] {L : Subgroup H}
    (hL : CFSG.IsComponent L) : ∃ b ∈ L, orderOf b = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hno
  push Not at hno
  have hodd : Odd (Nat.card ↥L) := by
    rcases Nat.even_or_odd (Nat.card ↥L) with he | ho
    · exfalso
      obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 2 (even_iff_two_dvd.1 he)
      exact hno t t.2 (by rw [Subgroup.orderOf_coe]; exact ht)
    · exact ho
  have hsolv : Group.IsSolvable ↥L := CFSG.Milestones.odd_order_solvable hodd
  have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
  have : Group.IsPerfect ↥L := hL.1.1
  exact Group.IsPerfect.not_isSolvable ↥L hsolv

omit [Finite G] in
theorem map_subtype_map_conj {n : G} (hn : n ∈ N) (A : Subgroup ↥N) :
    (A.map (MulAut.conj (⟨n, hn⟩ : ↥N)).toMonoidHom).map N.subtype =
      (A.map N.subtype).map (MulAut.conj n).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem le_normalizer_of_component_eq {Lh : Subgroup ↥N} (hLc : CFSG.IsComponent Lh)
    (hstd : IsStandardSubgroup K) (heq : K = Lh.map N.subtype) : N ≤ normalizer (K : Set G) := by
  intro n hn
  set σ : ↥N ≃* ↥N := MulAut.conj (⟨n, hn⟩ : ↥N) with hσ
  have hLc' : CFSG.IsComponent (Lh.map σ.toMonoidHom) := CFSG.LocalCores.isComponent_map_mulEquiv σ hLc
  have hmap : (Lh.map σ.toMonoidHom).map N.subtype = K.map (MulAut.conj n).toMonoidHom := by
    rw [heq]
    exact map_subtype_map_conj hn Lh
  rcases CFSG.LocalCores.distinct_components_commute hLc hLc' with h | h
  · have key : K.map (MulAut.conj n).toMonoidHom = K := by
      rw [← hmap, ← h, ← heq]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr key
  · exfalso
    apply hstd.2.2.2.2 n⁻¹
    have h1 : ⁅Lh.map N.subtype, (Lh.map σ.toMonoidHom).map N.subtype⁆ = ⊥ := by
      rw [← Subgroup.map_commutator, h, Subgroup.map_bot]
    rw [hmap, ← heq] at h1
    simpa [CFSG.conjugate] using h1

omit [Finite G] in
theorem not_le_centralizer_of_lt {L : Subgroup G} (hKL : K < L) (hLq : CFSG.IsQuasisimple ↥L)
    (hKq : CFSG.IsQuasisimple ↥K) {b : G}
    (hb : centralizer ({b} : Set G) ≤ normalizer (K : Set G)) : ¬ L ≤ centralizer ({b} : Set G) := by
  intro hLb
  have hLN : L ≤ normalizer (K : Set G) := hLb.trans hb
  have hnormal : (K.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKL.le).mpr hLN
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq hnormal with h | h
  · exact not_le_of_gt hKL (Subgroup.subgroupOf_eq_top.mp h)
  · have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hKq.1
    have hKcomm : ⁅K, K⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro k1 hk1
      rw [mem_centralizer_iff]
      intro k2 hk2
      have h1 : (⟨k1, hKL.le hk1⟩ : ↥L) ∈ K.subgroupOf L := hk1
      have h2 := Subgroup.mem_center_iff.mp (h h1) ⟨k2, hKL.le hk2⟩
      exact congrArg Subtype.val h2
    have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hKq
    have hbot : K = ⊥ := by rw [← hKperf]; exact hKcomm
    exact (Subgroup.nontrivial_iff_ne_bot K).1 this hbot

theorem all_components_eq
    (hQC : IsSylowOf 2 Q (centralizer (K : Set G))) (hCKN : centralizer (K : Set G) ≤ N)
    (hKN : K ≤ N) (hKq : CFSG.IsQuasisimple ↥K)
    {Lh : Subgroup ↥N} (hLc : CFSG.IsComponent Lh) (hKL : K.subgroupOf N ≤ Lh)
    (hno : ∀ b ∈ Q, orderOf b = 2 → ¬ Lh.map N.subtype ≤ centralizer ({b} : Set G))
    {M : Subgroup ↥N} (hM : CFSG.IsComponent M) : M = Lh := by
  by_contra hne
  have hcomm : ⁅M, Lh⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute hM hLc).resolve_left hne
  obtain ⟨b', hb'M, hb'2⟩ := exists_involution_of_isComponent hM
  have hKhq : CFSG.IsQuasisimple ↥(K.subgroupOf N) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKN).symm hKq
  have hKhperf : ⁅K.subgroupOf N, K.subgroupOf N⁆ = K.subgroupOf N :=
    Subgroup.isPerfect_iff.mp hKhq.1
  have hKhne : K.subgroupOf N ≠ ⊥ := by
    have : Nontrivial ↥(K.subgroupOf N) := CFSG.LocalCores.isQuasisimple_nontrivial hKhq
    exact (Subgroup.nontrivial_iff_ne_bot _).1 this
  have hb2 : orderOf (b' : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hb'2
  have hbC : (b' : G) ∈ centralizer (K : Set G) := by
    rw [mem_centralizer_iff]
    intro k hk
    have hk' : (⟨k, hKN hk⟩ : ↥N) ∈ Lh := hKL hk
    have hc : ⁅b', (⟨k, hKN hk⟩ : ↥N)⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator hb'M hk'
      rw [hcomm, Subgroup.mem_bot] at this
      exact this
    have := commutatorElement_eq_one_iff_mul_comm.1 hc
    exact congrArg Subtype.val this.symm
  obtain ⟨c, hc, hcQ⟩ := exists_conj_mem_Q hQC hbC hb2
  have hcN : c ∈ N := hCKN hc
  set σ : ↥N ≃* ↥N := MulAut.conj (⟨c⁻¹, N.inv_mem hcN⟩ : ↥N) with hσ
  have hσapply : ∀ x : ↥N, ((σ x : ↥N) : G) = c⁻¹ * (x : G) * c := by
    intro x
    simp [hσ, MulAut.conj_apply]
  have hσK : (K.subgroupOf N).map σ.toMonoidHom = K.subgroupOf N := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzc : (z : G) ∈ K := hz
      have hzcomm : (z : G) * c = c * (z : G) := (mem_centralizer_iff.mp hc) _ hzc
      have : ((σ z : ↥N) : G) = (z : G) := by
        rw [hσapply]
        calc c⁻¹ * (z : G) * c = c⁻¹ * ((z : G) * c) := by group
          _ = c⁻¹ * (c * (z : G)) := by rw [hzcomm]
          _ = (z : G) := by group
      have h2 : σ z = z := Subtype.ext this
      rw [MulEquiv.coe_toMonoidHom, h2]
      exact hz
    · intro hy
      refine ⟨y, hy, ?_⟩
      have hyc : (y : G) ∈ K := hy
      have hycomm : (y : G) * c = c * (y : G) := (mem_centralizer_iff.mp hc) _ hyc
      have : ((σ y : ↥N) : G) = (y : G) := by
        rw [hσapply]
        calc c⁻¹ * (y : G) * c = c⁻¹ * ((y : G) * c) := by group
          _ = c⁻¹ * (c * (y : G)) := by rw [hycomm]
          _ = (y : G) := by group
      exact Subtype.ext this
  have hLσc : CFSG.IsComponent (Lh.map σ.toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv σ hLc
  have hLσ : Lh.map σ.toMonoidHom = Lh := by
    by_contra hne'
    have hcomm2 : ⁅Lh, Lh.map σ.toMonoidHom⁆ = ⊥ :=
      (CFSG.LocalCores.distinct_components_commute hLc hLσc).resolve_left (Ne.symm hne')
    have hKσ : K.subgroupOf N ≤ Lh.map σ.toMonoidHom := by
      rw [← hσK]
      exact Subgroup.map_mono hKL
    have hle : ⁅K.subgroupOf N, K.subgroupOf N⁆ ≤ ⁅Lh, Lh.map σ.toMonoidHom⁆ :=
      Subgroup.commutator_mono hKL hKσ
    rw [hcomm2, le_bot_iff, hKhperf] at hle
    exact hKhne hle
  have hMσc : CFSG.IsComponent (M.map σ.toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv σ hM
  have hMσne : M.map σ.toMonoidHom ≠ Lh := by
    intro h
    apply hne
    rw [← hLσ] at h
    exact Subgroup.map_injective σ.injective h
  have hcomm3 : ⁅M.map σ.toMonoidHom, Lh⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hMσc hLc).resolve_left hMσne
  have hord : orderOf (c⁻¹ * (b' : G) * c) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj c⁻¹) (b' : G)
    simpa [MulAut.conj_apply] using this.trans hb2
  refine hno _ hcQ hord ?_
  rintro _ ⟨l, hl, rfl⟩
  rw [mem_centralizer_singleton_iff]
  have hmem : σ b' ∈ M.map σ.toMonoidHom := ⟨b', hb'M, rfl⟩
  have hc1 : ⁅σ b', l⁆ = 1 := by
    have := Subgroup.commutator_mem_commutator hmem hl
    rw [hcomm3, Subgroup.mem_bot] at this
    exact this
  have h2 := commutatorElement_eq_one_iff_mul_comm.1 hc1
  have h3 := congrArg Subtype.val h2
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hσapply] at h3
  exact h3.symm

theorem exists_simpleSocle
    (hcoreN : pPrimeCore 2 ↥N = ⊥)
    (hQC : IsSylowOf 2 Q (centralizer (K : Set G))) (hCKN : centralizer (K : Set G) ≤ N)
    (hgam : gammaK 2 Q 1 ≤ normalizer (K : Set G)) (hNM : ¬ N ≤ normalizer (K : Set G))
    (hKN : K ≤ N) (hKq : CFSG.IsQuasisimple ↥K) (hstd : IsStandardSubgroup K)
    (hQ2 : ∀ b ∈ Q, orderOf b = 2 → centralizer ({b} : Set G) ≤ normalizer (K : Set G))
    {Lh : Subgroup ↥N} (hLc : CFSG.IsComponent Lh) (hKL : K.subgroupOf N ≤ Lh) :
    K < Lh.map N.subtype ∧ IsSimpleSocle (Lh.map N.subtype) N := by
  have hKLg : K ≤ Lh.map N.subtype := fun k hk => ⟨⟨k, hKN hk⟩, hKL hk, rfl⟩
  have hKlayer : K.subgroupOf N ≤ CFSG.layer ↥N :=
    hKL.trans (CFSG.LocalCores.component_le_layer hLc)
  have hF : fittingSubgroup ↥N = ⊥ := fitting_eq_bot hcoreN hQC hCKN hgam hNM hKN hKlayer
  have hKne : K ≠ Lh.map N.subtype := fun h => hNM (le_normalizer_of_component_eq hLc hstd h)
  have hKlt : K < Lh.map N.subtype := lt_of_le_of_ne hKLg hKne
  have hLgq : CFSG.IsQuasisimple ↥(Lh.map N.subtype) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Lh.equivMapOfInjective N.subtype N.subtype_injective) hLc.1
  have hno : ∀ b ∈ Q, orderOf b = 2 → ¬ Lh.map N.subtype ≤ centralizer ({b} : Set G) :=
    fun b hb hb2 => not_le_centralizer_of_lt hKlt hLgq hKq (hQ2 b hb hb2)
  have hall : ∀ M : Subgroup ↥N, CFSG.IsComponent M → M = Lh := fun M hM =>
    all_components_eq hQC hCKN hKN hKq hLc hKL hno hM
  have hlayer : CFSG.layer ↥N = Lh := by
    simp only [CFSG.layer.eq_sSup]
    have hset : {M : Subgroup ↥N | CFSG.IsComponent M} = {Lh} := by
      ext M
      exact ⟨fun hM => hall M hM, fun h => by rw [Set.mem_singleton_iff] at h; rw [h]; exact hLc⟩
    rw [hset, sSup_singleton]
  have hLn : Lh.Normal := by
    rw [← hlayer]
    have := CFSG.LocalCores.layer_characteristic (G := ↥N)
    infer_instance
  have hZ : center ↥Lh = ⊥ := by
    have := hLn
    have hnormal : ((center ↥Lh).map Lh.subtype).Normal := inferInstance
    have : Group.IsNilpotent ↥((center ↥Lh).map Lh.subtype) :=
      Group.nilpotent_of_mulEquiv ((center ↥Lh).equivMapOfInjective Lh.subtype Lh.subtype_injective)
    have hle : (center ↥Lh).map Lh.subtype ≤ fittingSubgroup ↥N := le_sSup ⟨hnormal, inferInstance⟩
    rw [hF, le_bot_iff] at hle
    exact (Subgroup.map_eq_bot_iff_of_injective _ Lh.subtype_injective).mp hle
  have hLsimple : IsSimpleGroup ↥Lh := by
    have hs : IsSimpleGroup (↥Lh ⧸ center ↥Lh) := hLc.1.2.1
    let e : ↥Lh ≃* (↥Lh ⧸ center ↥Lh) :=
      (QuotientGroup.quotientBot (G := ↥Lh)).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hZ.symm)
    exact e.isSimpleGroup
  have hFstar : CFSG.Open.genFittingFStar ↥N = Lh := by
    have h1 : CFSG.Open.genFittingFitting ↥N = ⊥ := by
      have : CFSG.Open.genFittingFitting ↥N = fittingSubgroup ↥N := rfl
      rw [this, hF]
    have h2 : CFSG.Open.genFittingLayer ↥N = Lh := by
      simp only [CFSG.Open.genFittingLayer.eq_sSup]
      apply le_antisymm
      · refine sSup_le fun M hM => ?_
        exact (hall M ((CFSG.isComponent_iff_open M).mpr hM)).le
      · exact le_sSup ((CFSG.isComponent_iff_open Lh).mp hLc)
    simp only [CFSG.Open.genFittingFStar.eq_sup]
    rw [h1, h2, bot_sup_eq]
  have hCent : ∀ n : ↥N, (∀ l ∈ Lh, n * l = l * n) → n = 1 := by
    intro n hn
    have hmem : n ∈ centralizer (CFSG.Open.genFittingFStar ↥N : Set ↥N) := by
      rw [hFstar, mem_centralizer_iff]
      intro l hl
      exact (hn l hl).symm
    have hnL : n ∈ Lh := by
      have := CFSG.Adapters.generalized_fitting_self_centralizing ↥N hmem
      rwa [hFstar] at this
    have hnz : (⟨n, hnL⟩ : ↥Lh) ∈ center ↥Lh := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hn g g.2).symm
    rw [hZ, Subgroup.mem_bot] at hnz
    exact congrArg Subtype.val hnz
  refine ⟨hKlt, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.map_subtype_le Lh
  · rintro n hn _ ⟨l, hl, rfl⟩
    refine ⟨⟨n, hn⟩ * l * ⟨n, hn⟩⁻¹, hLn.conj_mem l hl ⟨n, hn⟩, ?_⟩
    simp
  · have := hLsimple
    exact (Lh.equivMapOfInjective N.subtype N.subtype_injective).symm.isSimpleGroup
  · intro n hn hnc
    have h := hCent ⟨n, hn⟩ (fun l hl => Subtype.ext (hnc _ ⟨l, hl, rfl⟩))
    exact congrArg Subtype.val h

end CFSG.GH74.GLS.EvenCore

