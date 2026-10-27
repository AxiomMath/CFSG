module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddExc

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.GH74.GLS.Stage2.OddAut CFSG.GH74.GLS.Stage2.Bender.Thm1

section L28Abstract

variable {G : Type} [Group G] [Finite G]

theorem card_sylow_three_of_card_504 (hcard : Nat.card G = 504) (T : Sylow 3 G) :
    Nat.card (T : Subgroup G) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Sylow.card_eq_multiplicity, hcard]
  have h : (504 : ℕ) = 3 ^ 2 * 56 := by norm_num
  rw [Nat.factorization_def _ Nat.prime_three, h, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  norm_num

theorem isPGroup_three_of_card_nine {H : Subgroup G} (h : Nat.card H = 9) : IsPGroup 3 H :=
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  IsPGroup.of_card (n := 2) (by rw [h]; norm_num)

theorem exists_sylow_three_centralizer (hcard : Nat.card G = 504)
    (hK : ∀ y : G, orderOf y = 3 → Nat.card (Subgroup.centralizer ({y} : Set G)) = 9)
    {U : Subgroup G} (hU0 : U ≠ ⊥) (hU : IsPGroup 3 U) :
    ∃ T : Sylow 3 G, U ≤ (T : Subgroup G) ∧
      Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer ((T : Subgroup G) : Set G) ∧
      ∀ x : G, (∀ t ∈ (T : Subgroup G), x * t = t * x) → x ∈ (T : Subgroup G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hxU, hx1⟩ : ∃ x ∈ U, x ≠ 1 := (Subgroup.bot_or_exists_ne_one U).resolve_left hU0
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hU) ⟨x, hxU⟩
  have hk' : orderOf x = 3 ^ k := by
    rw [← Subgroup.orderOf_coe (⟨x, hxU⟩ : U)] at hk
    exact hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hk'
    exact hx1 hk'
  obtain ⟨y, hyU, hyord⟩ : ∃ y ∈ U, orderOf y = 3 := by
    refine ⟨x ^ (orderOf x / 3), U.pow_mem hxU _, ?_⟩
    exact orderOf_pow_orderOf_div (orderOf_pos x).ne' (by rw [hk']; exact dvd_pow_self 3 hk0)
  set C : Subgroup G := Subgroup.centralizer ({y} : Set G) with hC
  have hCcard : Nat.card C = 9 := hK y hyord
  obtain ⟨T, hCT⟩ := (isPGroup_three_of_card_nine hCcard).exists_le_sylow
  have hTcard := card_sylow_three_of_card_504 hcard T
  have hCeqT : C = (T : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hCT (by rw [hTcard, hCcard])
  have hCmem : ∀ x : G, x ∈ C ↔ x * y = y * x := fun x => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
  obtain ⟨T'', hUT''⟩ := hU.exists_le_sylow
  have hT''card := card_sylow_three_of_card_504 hcard T''
  have hcomm'' := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
    (G := (T'' : Subgroup G)) (by rw [hT''card]; norm_num)).is_comm.comm
  have hT''C : (T'' : Subgroup G) ≤ C := by
    intro t ht
    rw [hCmem]
    have := hcomm'' ⟨t, ht⟩ ⟨y, hUT'' hyU⟩
    exact congrArg Subtype.val this
  have hT''eq : C = (T'' : Subgroup G) :=
    (Subgroup.eq_of_le_of_card_ge hT''C (by rw [hCcard, hT''card])).symm
  have hUT : U ≤ (T : Subgroup G) := by
    rw [← hCeqT, hT''eq]
    exact hUT''
  have hyT : y ∈ (T : Subgroup G) := hUT hyU
  have hCT' : ∀ x : G, (∀ t ∈ (T : Subgroup G), x * t = t * x) → x ∈ (T : Subgroup G) := by
    intro x hx
    rw [← hCeqT, hCmem]
    exact hx y hyT
  have hUdvd : Nat.card U ∣ 9 := hTcard ▸ Subgroup.card_dvd_of_le hUT
  have hU1 : Nat.card U ≠ 1 := by
    intro h1
    exact hU0 (Subgroup.eq_bot_of_card_eq U h1)
  have hUcases : Nat.card U = 3 ∨ Nat.card U = 9 := by
    have : Nat.card U ∈ Nat.divisors 9 := Nat.mem_divisors.2 ⟨hUdvd, by norm_num⟩
    have hd : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [hd] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  refine ⟨T, hUT, ?_, hCT'⟩
  rcases hUcases with h3 | h9
  ·
    have hUz : Subgroup.zpowers y = U := by
      refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hyU) ?_
      rw [Nat.card_zpowers, hyord, h3]
    have key : ∀ g ∈ Subgroup.normalizer (U : Set G), ∀ c : G, c * y = y * c →
        (g * c * g⁻¹) * y = y * (g * c * g⁻¹) := by
      intro g hg c hc
      have h1 : g⁻¹ * y * g ∈ Subgroup.zpowers y := by
        rw [hUz]
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) y).mp hyU
        simpa using this
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h1
      have hy' : g * y ^ m * g⁻¹ = y := by rw [hm]; group
      have hcm : c * y ^ m = y ^ m * c := Commute.zpow_right hc m
      calc (g * c * g⁻¹) * y = (g * c * g⁻¹) * (g * y ^ m * g⁻¹) := by rw [hy']
        _ = g * (c * y ^ m) * g⁻¹ := by group
        _ = g * (y ^ m * c) * g⁻¹ := by rw [hcm]
        _ = (g * y ^ m * g⁻¹) * (g * c * g⁻¹) := by group
        _ = y * (g * c * g⁻¹) := by rw [hy']
    have hmemC : ∀ g ∈ Subgroup.normalizer (U : Set G), ∀ h : G, h ∈ C → g * h * g⁻¹ ∈ C := by
      intro g hg h hh
      rw [hCmem] at hh ⊢
      exact key g hg h hh
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    show h ∈ (T : Subgroup G) ↔ g * h * g⁻¹ ∈ (T : Subgroup G)
    rw [← hCeqT]
    constructor
    · exact hmemC g hg h
    · intro h2
      have := hmemC g⁻¹ (inv_mem hg) _ h2
      simpa [mul_assoc] using this
  · have hUeq : U = (T : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge hUT (by rw [hTcard, h9])
    rw [hUeq]

theorem le_sylow_of_le_normalizer {T : Sylow 3 G} {Z : Subgroup G} (hZ : IsPGroup 3 Z)
    (hZN : Z ≤ Subgroup.normalizer ((T : Subgroup G) : Set G)) : Z ≤ (T : Subgroup G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsup : IsPGroup 3 ↥((T : Subgroup G) ⊔ Z) := T.isPGroup'.to_sup_of_normal_left' hZ hZN
  have := T.is_maximal' hsup le_sup_left
  exact le_sup_right.trans this.le

theorem pCoreOf_normalizer_sylow_three (T : Sylow 3 G) :
    pCoreOf 3 (Subgroup.normalizer ((T : Subgroup G) : Set G)) = (T : Subgroup G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine le_antisymm ?_ (le_pCoreOf_of_le_normalizer 3 Subgroup.le_normalizer le_rfl T.isPGroup')
  exact le_sylow_of_le_normalizer (pCoreOf_isPGroup 3 _) (pCoreOf_le 3 _)

theorem holds_three_of_centralizers (hs : IsSimpleGroup G) (hcard : Nat.card G = 504)
    (hK : ∀ y : G, orderOf y = 3 → Nat.card (Subgroup.centralizer ({y} : Set G)) = 9) :
    Holds G 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro U hU0 hU
  obtain ⟨T, hUT, hNU, -⟩ := exists_sylow_three_centralizer hcard hK hU0 hU
  have hTcard := card_sylow_three_of_card_504 hcard T
  have hTcore := pCoreOf_normalizer_sylow_three T
  refine ⟨T, Subgroup.normalizer ((T : Subgroup G) : Set G), ?_, hNU, ?_, ?_, le_rfl⟩
  · intro htop
    haveI : (T : Subgroup G).Normal := Subgroup.normalizer_eq_top_iff.1 htop
    rcases hs.eq_bot_or_eq_top_of_normal (T : Subgroup G) with h | h
    · have : Nat.card (T : Subgroup G) = 1 := by rw [h]; exact Subgroup.card_bot
      omega
    · have : Nat.card (T : Subgroup G) = Nat.card G := by rw [h]; exact Subgroup.card_top
      omega
  · rw [hTcore]
    exact le_sylow_of_le_normalizer (pCoreOf_isPGroup 3 _) ((pCoreOf_le 3 _).trans hNU)
  · rw [hTcore]
    exact hUT

theorem radRigidInner_three_of_centralizers (hcard : Nat.card G = 504)
    (hK : ∀ y : G, orderOf y = 3 → Nat.card (Subgroup.centralizer ({y} : Set G)) = 9) :
    RadRigidInner 3 G := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro R hR x hx hxo
  obtain ⟨h0, hp, hc, hnt⟩ := hR
  obtain ⟨T, hRT, hNR, hCT⟩ := exists_sylow_three_centralizer hcard hK h0 hp
  have hTcard := card_sylow_three_of_card_504 hcard T
  have hcomm := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
    (G := (T : Subgroup G)) (by rw [hTcard]; norm_num)).is_comm.comm
  have hTN : (T : Subgroup G) ≤ Subgroup.normalizer (R : Set G) := by
    intro t ht
    refine Subgroup.centralizer_le_normalizer (R : Set G) (Subgroup.mem_centralizer_iff.2 fun r hr => ?_)
    have := hcomm ⟨r, hRT hr⟩ ⟨t, ht⟩
    exact congrArg Subtype.val this
  have hTR : (T : Subgroup G) ≤ R := by
    have : (T : Subgroup G) ≤ pCoreOf 3 (Subgroup.normalizer (R : Set G)) :=
      le_pCoreOf_of_le_normalizer 3 hTN hNR T.isPGroup'
    rwa [hc] at this
  have hxT : x ∈ (T : Subgroup G) := hCT x fun t ht => hx t (hTR ht)
  exact eq_one_of_mem_pGroup_of_coprime T.isPGroup' hxT hxo

instance innerAut_normal : ((MulAut.conj : G →* MulAut G).range).Normal where
  conj_mem := by
    rintro _ ⟨g, rfl⟩ α
    refine ⟨α g, ?_⟩
    ext x
    simp [MulAut.conj_apply]

theorem inner_of_coprime_three (hcen : Subgroup.center G = ⊥)
    (hAut : Nat.card (MulAut G) = 3 * Nat.card G) [Finite (MulAut G)] (α : MulAut G)
    (hα : Nat.Coprime (orderOf α) 3) : α ∈ (MulAut.conj : G →* MulAut G).range := by
  set I : Subgroup (MulAut G) := (MulAut.conj : G →* MulAut G).range with hI
  have hinj := mulAut_conj_injective_of_center_bot hcen
  have hIcard : Nat.card I = Nat.card G :=
    (Nat.card_congr (Equiv.ofInjective _ hinj)).symm
  have hidx : I.index = 3 := by
    have h := I.index_mul_card
    rw [hIcard, hAut] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hQ : Nat.card (MulAut G ⧸ I) = 3 := by rw [← Subgroup.index_eq_card, hidx]
  have h1 : orderOf (QuotientGroup.mk' I α) ∣ 3 := by
    rw [← hQ]
    exact orderOf_dvd_natCard _
  have h2 : orderOf (QuotientGroup.mk' I α) ∣ orderOf α := orderOf_map_dvd _ α
  have h3 : orderOf (QuotientGroup.mk' I α) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hα) h1
  have h4 : QuotientGroup.mk' I α = 1 := orderOf_eq_one_iff.1 h3
  exact (QuotientGroup.eq_one_iff α).1 h4

theorem radRigid_three_of_centralizers (hs : IsSimpleGroup G) (hna : ∃ a b : G, a * b ≠ b * a)
    (hcard : Nat.card G = 504)
    (hK : ∀ y : G, orderOf y = 3 → Nat.card (Subgroup.centralizer ({y} : Set G)) = 9)
    (hAut : Nat.card (MulAut G) = 3 * Nat.card G) [Finite (MulAut G)] : RadRigid 3 G := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcen := center_eq_bot_of_simple_nonabelian hs hna
  have hinj := mulAut_conj_injective_of_center_bot hcen
  intro R hR α hfix hord
  obtain ⟨g, rfl⟩ := inner_of_coprime_three hcen hAut α hord
  have hg : ∀ r ∈ R, g * r = r * g := by
    intro r hr
    have h := hfix r hr
    simp only [MulAut.conj_apply] at h
    calc g * r = (g * r * g⁻¹) * g := by group
      _ = r * g := by rw [h]
  have hgo : Nat.Coprime (orderOf g) 3 := by
    rw [← orderOf_injective _ hinj g]
    exact hord
  have := radRigidInner_three_of_centralizers hcard hK R hR g hg hgo
  rw [this, map_one]

end L28Abstract

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
