module

public import CFSG.FeitThompson.Local.ReducedKernelExponentPrimeSpecial
public import CFSG.FeitThompson.Local.InvariantHallPiSubgroupExtension
public import CFSG.FeitThompson.Local.PrimeCentralizerMinimalFittingAbelian
public import CFSG.FeitThompson.Local.MinimalPrimeCentralizerCounterexample
public import CFSG.FeitThompson.Local.FittingSplitsNormalHall
public import CFSG.FeitThompson.Local.PiCoreQuotientPiCore
public import CFSG.FeitThompson.Local.PLengthOneNormalSeries
public import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
public import CFSG.FeitThompson.Local.FittingSupportExcludesNormalCore
public import CFSG.FeitThompson.Local.FittingMonoNormal
public import CFSG.FeitThompson.Local.OvergroupJoinsInvariantPrimeSubgroups
public import CFSG.FeitThompson.Local.PSubgroupNormalizingFullPSubgroup
public import CFSG.FeitThompson.Foundations.SolvableHallConjugacy
public import CFSG.FeitThompson.Foundations.FittingContainsCentralizerSolvable

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup QuotientGroup Pointwise

universe u

section Aux

variable {G : Type*} [Group G]

theorem fittingRawPreimage_eq_comap (X : Type*) [Group X] [Finite X] :
    haveI := fittingRaw_normal X
    fittingRawPreimage X = comap (mk' (fittingRaw X)) (fittingRaw (X ⧸ fittingRaw X)) := by
  have := fittingRaw_normal X
  ext x
  rw [mem_fittingRawPreimage_iff]
  simp [Subgroup.mem_comap]

instance fittingRawPreimage_characteristic (X : Type*) [Group X] [Finite X] :
    (fittingRawPreimage X).Characteristic := by
  have := fittingRaw_normal X
  rw [fittingRawPreimage_eq_comap]
  exact Subgroup.Characteristic.comap_quotient_mk (fittingRaw_characteristic _)

theorem normal_map_subtype_fittingRawPreimage [Finite G] {H : Subgroup G} (hH : H.Normal) :
    ((fittingRawPreimage ↥H).map H.subtype).Normal :=
  haveI := hH
  ConjAct.normal_of_characteristic_of_normal

variable [Finite G] {p : ℕ}

theorem not_dvd_natCard_fittingRaw_of_pCore_eq_bot (hp : p.Prime) (h : pCore p G = ⊥) :
    ¬ p ∣ Nat.card ↥(fittingRaw G) := by
  have hbot : fittingPiPart ({p} : Set ℕ) G = ⊥ := by
    refine le_bot_iff.1 ?_
    rw [← h]
    exact le_pCore hp (fittingPiPart_normal _ _)
      ((isPiSubgroup_singleton_iff hp _).1 (isPiSubgroup_fittingPiPart _ _))
  have hs : sylowPiPart ({p} : Set ℕ) ↥(fittingRaw G) = ⊥ := by
    rw [fittingPiPart_eq_map] at hbot
    exact (Subgroup.map_eq_bot_iff_of_injective _ (fittingRaw G).subtype_injective).1 hbot
  have hHall := isHallSubgroup_sylowPiPart ({p} : Set ℕ) ↥(fittingRaw G)
  rw [hs] at hHall
  have hpi := isPiNumber_iff.1 (isHallSubgroup_bot_iff.1 hHall)
  intro hdvd
  exact hpi p (Nat.mem_primeFactors.2 ⟨hp, hdvd, Nat.card_pos.ne'⟩) rfl

theorem not_dvd_natCard_fittingRaw_quotient (hp : p.Prime) (hF : fittingRaw G = pCore p G) :
    ¬ p ∣ Nat.card ↥(fittingRaw (G ⧸ fittingRaw G)) := by
  have := fittingRaw_normal G
  refine not_dvd_natCard_fittingRaw_of_pCore_eq_bot hp ?_
  rw [pCore_eq_piCore]
  exact piCore_quotient_eq_bot_of_eq_piCore {p} G (by rw [hF, pCore_eq_piCore])

theorem isHallSubgroup_subgroupOf_fittingRaw (hp : p.Prime) (hF : fittingRaw G = pCore p G) :
    IsHallSubgroup ({p} : Set ℕ) ((fittingRaw G).subgroupOf (fittingRawPreimage G)) := by
  have hn := fittingRaw_normal G
  refine ⟨?_, ?_⟩
  · rw [natCard_subgroupOf_of_le (fittingRaw_le_fittingRawPreimage G)]
    refine isPiSubgroup_iff_isPiNumber.1 ((isPiSubgroup_singleton_iff hp _).2 ?_)
    rw [hF]
    exact isPGroup_pCore hp G
  · rw [index_subgroupOf, fittingRawPreimage_eq_comap, relIndex_comap_mk']
    refine isPiNumber_iff.2 fun q hq hq' => ?_
    rw [Set.mem_singleton_iff] at hq'
    subst hq'
    exact not_dvd_natCard_fittingRaw_quotient hp hF (Nat.dvd_of_mem_primeFactors hq)

theorem natCard_eq_pow_factorization_of_isHallSubgroup_singleton (hp : p.Prime)
    {P N : Subgroup G} (hPN : P ≤ N) (h : IsHallSubgroup ({p} : Set ℕ) (P.subgroupOf N)) :
    Nat.card ↥P = p ^ (Nat.card ↥N).factorization p := by
  have := Fact.mk hp
  have e1 : Nat.card ↥(P.subgroupOf N) = Nat.card ↥P := natCard_subgroupOf_of_le hPN
  have hPp : IsPGroup p ↥(P.subgroupOf N) :=
    (isPiSubgroup_singleton_iff hp _).1 (isPiSubgroup_iff_isPiNumber.2 h.natCard)
  have hidx : ¬ p ∣ (P.subgroupOf N).index := fun hd =>
    isPiNumber_iff.1 h.index p
      (Nat.mem_primeFactors.2 ⟨hp, hd, Subgroup.index_ne_zero_of_finite⟩) rfl
  have hS : Nat.card ↥((hPp.toSylow hidx : Sylow p ↥N) : Subgroup ↥N)
      = p ^ (Nat.card ↥N).factorization p := Sylow.card_eq_multiplicity _
  rw [IsPGroup.toSylow_coe] at hS
  rw [← e1, hS]

theorem sup_eq_and_inf_eq_bot_of_isHallSubgroup_compl {π : Set ℕ} {U V K : Subgroup G}
    (hVU : V ≤ U) (hKU : K ≤ U) (hV : IsHallSubgroup π (V.subgroupOf U))
    (hK : IsHallSubgroup πᶜ (K.subgroupOf U)) (hKV : K ≤ normalizer (V : Set G)) :
    V ⊔ K = U ∧ V ⊓ K = ⊥ := by
  have eV : Nat.card ↥(V.subgroupOf U) = Nat.card ↥V := natCard_subgroupOf_of_le hVU
  have eK : Nat.card ↥(K.subgroupOf U) = Nat.card ↥K := natCard_subgroupOf_of_le hKU
  have hVπ : IsPiNumber π (Nat.card ↥V) := eV ▸ hV.natCard
  have hKπ : IsPiNumber πᶜ (Nat.card ↥K) := eK ▸ hK.natCard
  have hVi : IsPiNumber πᶜ (V.subgroupOf U).index := hV.index
  have hKi : IsPiNumber π (K.subgroupOf U).index :=
    isPiNumber_iff.2 fun q hq => by
      by_contra hcon; exact isPiNumber_iff.1 hK.index q hq hcon
  have hcop : (Nat.card ↥V).Coprime (Nat.card ↥K) :=
    hVπ.coprime_of_compl hKπ Nat.card_pos.ne' Nat.card_pos.ne'
  have hinf : V ⊓ K = ⊥ := disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard hcop)
  have hVmul : Nat.card ↥V * (V.subgroupOf U).index = Nat.card ↥U := by
    rw [← eV]; exact Subgroup.card_mul_index _
  have hKmul : Nat.card ↥K * (K.subgroupOf U).index = Nat.card ↥U := by
    rw [← eK]; exact Subgroup.card_mul_index _
  have hcop2 : ((V.subgroupOf U).index).Coprime ((K.subgroupOf U).index) :=
    IsPiNumber.coprime_of_compl (π := πᶜ) hVi
      (isPiNumber_iff.2 fun q hq hq' => hq' (isPiNumber_iff.1 hKi q hq))
      Subgroup.index_ne_zero_of_finite Subgroup.index_ne_zero_of_finite
  have hd1 : Nat.card ↥K ∣ Nat.card ↥V * (V.subgroupOf U).index :=
    ⟨(K.subgroupOf U).index, by rw [hVmul, hKmul]⟩
  have hd2 : (V.subgroupOf U).index ∣ Nat.card ↥K * (K.subgroupOf U).index :=
    ⟨Nat.card ↥V, by rw [hKmul, ← hVmul]; ring⟩
  have hKeq : Nat.card ↥K = (V.subgroupOf U).index :=
    Nat.dvd_antisymm (Nat.Coprime.dvd_of_dvd_mul_left hcop.symm hd1)
      (Nat.Coprime.dvd_of_dvd_mul_right hcop2 hd2)
  refine ⟨?_, hinf⟩
  refine Subgroup.eq_of_le_of_card_ge (sup_le hVU hKU) ?_
  have hprod : Nat.card ↥(V ⊔ K : Subgroup G) * Nat.card ↥(V ⊓ K : Subgroup G)
      = Nat.card ↥V * Nat.card ↥K := natCard_sup_mul_natCard_inf_of_le_normalizer hKV
  rw [hinf, Subgroup.card_bot, mul_one] at hprod
  rw [hprod, hKeq, hVmul]

theorem isHallSubgroup_subgroupOf_of_natCard_eq {G' : Type*} [Group G'] [Finite G']
    {π : Set ℕ} {A B : Subgroup G} {A' B' : Subgroup G'} (hAB : A ≤ B) (hAB' : A' ≤ B')
    (hA : Nat.card A = Nat.card A') (hB : Nat.card B = Nat.card B')
    (h : IsHallSubgroup π (A.subgroupOf B)) : IsHallSubgroup π (A'.subgroupOf B') := by
  have e1 : Nat.card (A.subgroupOf B) = Nat.card A := natCard_subgroupOf_of_le hAB
  have e2 : Nat.card (A'.subgroupOf B') = Nat.card A' := natCard_subgroupOf_of_le hAB'
  have hidx : (A'.subgroupOf B').index = (A.subgroupOf B).index := by
    refine Nat.eq_of_mul_eq_mul_left (n := Nat.card A) Nat.card_pos ?_
    calc Nat.card A * (A'.subgroupOf B').index
        = Nat.card (A'.subgroupOf B') * (A'.subgroupOf B').index := by rw [e2, hA]
      _ = Nat.card B' := Subgroup.card_mul_index _
      _ = Nat.card B := hB.symm
      _ = Nat.card (A.subgroupOf B) * (A.subgroupOf B).index := (Subgroup.card_mul_index _).symm
      _ = Nat.card A * (A.subgroupOf B).index := by rw [e1]
  exact ⟨by rw [e2, ← hA, ← e1]; exact h.natCard, by rw [hidx]; exact h.index⟩

theorem le_normalizer_normalizer {K R : Subgroup G} (h : R ≤ normalizer (K : Set G)) :
    R ≤ normalizer ((normalizer (K : Set G) : Subgroup G) : Set G) := by
  intro r hr
  have hK : Subgroup.map ((MulAut.conj r : G ≃* G) : G →* G) K = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (h hr)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  calc Subgroup.map ((MulAut.conj r : G ≃* G) : G →* G) (normalizer (K : Set G))
      = normalizer ((Subgroup.map ((MulAut.conj r : G ≃* G) : G →* G) K : Subgroup G) : Set G) :=
        Subgroup.map_equiv_normalizer_eq K (MulAut.conj r)
    _ = normalizer (K : Set G) := by rw [hK]

theorem eq_sup_normalizer_inf_of_isHallSubgroup {π : Set ℕ} {U K H : Subgroup G}
    [Group.IsSolvable ↥U] (hHU : H ≤ normalizer (U : Set G)) (hKU : K ≤ U) (hUH : U ≤ H)
    (hK : IsHallSubgroup π (K.subgroupOf U)) :
    U ⊔ (normalizer (K : Set G) ⊓ H) = H := by
  refine le_antisymm (sup_le hUH inf_le_right) fun h hh => ?_
  have hUconj : MulAut.conj h • U = U := Subgroup.mem_normalizer_iff_map_conj_eq.1 (hHU hh)
  have hKcU : MulAut.conj h • K ≤ U := by
    rw [← hUconj]; exact Subgroup.map_mono hKU
  have hcard : Nat.card (MulAut.conj h • K : Subgroup G) = Nat.card K := by
    rw [conj_smul_eq_map_conj]
    exact Subgroup.card_map_of_injective (MulAut.conj h).injective
  have hHallc : IsHallSubgroup π ((MulAut.conj h • K).subgroupOf U) :=
    isHallSubgroup_subgroupOf_of_natCard_eq hKU hKcU hcard.symm rfl hK
  obtain ⟨g, hg⟩ := exists_conj_smul_eq_of_isHallSubgroup (G := ↥U) hK hHallc
  have hgG : MulAut.conj (g : G) • K = MulAut.conj h • K := by
    have h2 := congrArg (Subgroup.map U.subtype) hg
    rwa [map_subtype_conj_smul, subgroupOf_map_subtype, subgroupOf_map_subtype,
      inf_eq_left.2 hKU, inf_eq_left.2 hKcU] at h2
  have hmem : (h : G)⁻¹ * (g : G) ∈ normalizer (K : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← conj_smul_eq_map_conj]
    calc MulAut.conj ((h : G)⁻¹ * (g : G)) • K
        = (MulAut.conj (h : G)⁻¹ * MulAut.conj (g : G)) • K := by rw [map_mul]
      _ = MulAut.conj (h : G)⁻¹ • (MulAut.conj (g : G) • K) := mul_smul _ _ _
      _ = MulAut.conj (h : G)⁻¹ • (MulAut.conj (h : G) • K) := by rw [hgG]
      _ = (MulAut.conj (h : G)⁻¹ * MulAut.conj (h : G)) • K := (mul_smul _ _ _).symm
      _ = K := by rw [← map_mul, inv_mul_cancel, map_one, one_smul]
  have hmemH : (h : G)⁻¹ * (g : G) ∈ H := mul_mem (H.inv_mem hh) (hUH g.2)
  have hrw : h = (g : G) * ((h : G)⁻¹ * (g : G))⁻¹ := by group
  rw [hrw]
  exact mul_mem_sup g.2 (inv_mem ⟨hmem, hmemH⟩)

theorem inf_le_of_natCard_eq_pow_factorization [Fact p.Prime] {V N P : Subgroup G} [V.Normal]
    (hVp : IsPGroup p ↥V) (hPN : P ≤ N)
    (hPcard : Nat.card ↥P = p ^ (Nat.card ↥N).factorization p) : V ⊓ N ≤ P := by
  have hT : IsPGroup p ↥((V ⊓ N).subgroupOf N) := by
    have h : Nat.card ↥((V ⊓ N).subgroupOf N) = Nat.card ↥(V ⊓ N) :=
      natCard_subgroupOf_of_le inf_le_right
    obtain ⟨m, hm⟩ := (hVp.to_inf_left (K := N)).exists_card_eq
    exact IsPGroup.of_card (by rw [h, hm])
  have hS : Nat.card ↥(P.subgroupOf N) = p ^ (Nat.card ↥N).factorization p := by
    rw [natCard_subgroupOf_of_le hPN, hPcard]
  have h1 := hT.le_sylow_of_normal (Sylow.ofCard (P.subgroupOf N) hS)
  rw [Sylow.coe_ofCard] at h1
  have h2 := Subgroup.map_mono (f := N.subtype) h1
  rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_right : V ⊓ N ≤ N),
    Subgroup.map_subgroupOf_eq_of_le hPN] at h2
  exact h2

theorem natCard_eq_pow_factorization_of_natCard_eq_mul [Fact p.Prime] {X S : Subgroup G}
    (hS : IsPGroup p ↥S) {m : ℕ} (hm : Nat.card ↥X = Nat.card ↥S * m) (hpm : ¬ p ∣ m) :
    Nat.card ↥S = p ^ (Nat.card ↥X).factorization p := by
  have hp : p.Prime := Fact.out
  obtain ⟨d, hd⟩ := hS.exists_card_eq
  have hm0 : m ≠ 0 := by
    intro h; rw [h, mul_zero] at hm; exact Nat.card_pos.ne' hm
  rw [hm, hd, Nat.factorization_mul (pow_ne_zero _ hp.pos.ne') hm0]
  simp [hp.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hpm]

theorem not_dvd_index_subgroupOf_of_natCard_eq_pow_factorization (hp : p.Prime)
    {N S : Subgroup G} (hSN : S ≤ N)
    (hS : Nat.card ↥S = p ^ (Nat.card ↥N).factorization p) : ¬ p ∣ (S.subgroupOf N).index := by
  intro hd
  have h1 : Nat.card ↥(S.subgroupOf N) * (S.subgroupOf N).index = Nat.card ↥N :=
    Subgroup.card_mul_index _
  rw [natCard_subgroupOf_of_le hSN, hS] at h1
  obtain ⟨c, hc⟩ := hd
  refine Nat.pow_succ_factorization_not_dvd (n := Nat.card ↥N) Nat.card_pos.ne' hp ?_
  generalize (Nat.card ↥N).factorization p = k at h1
  exact ⟨c, by rw [pow_succ, ← h1, hc]; ring⟩

theorem hasPLengthLeOne_of_normal_of_natCard_eq [Fact p.Prime] {X V : Subgroup G} [V.Normal]
    (hVX : V ≤ X) (hVcard : Nat.card ↥V = p ^ (Nat.card ↥X).factorization p) :
    HasPLengthLeOne p ↥X :=
  hasPLengthLeOne_of_isPGroup_of_not_dvd_index (T := V.subgroupOf X) inferInstance
    (IsPGroup.of_card (by rw [natCard_subgroupOf_of_le hVX, hVcard]))
    (not_dvd_index_subgroupOf_of_natCard_eq_pow_factorization Fact.out hVX hVcard)

theorem natCard_sup_mul_index_subgroupOf {V N P X : Subgroup G} [V.Normal] (hPN : P ≤ N)
    (hVN : V ⊔ N = X) (hVP : V ⊓ N ≤ P) :
    Nat.card ↥(V ⊔ P : Subgroup G) * (P.subgroupOf N).index = Nat.card ↥X := by
  have hVnorm : ∀ T : Subgroup G, T ≤ normalizer (V : Set G) := fun _ => by
    rw [Subgroup.normalizer_eq_top (H := V)]; exact le_top
  have hinfeq : V ⊓ P = V ⊓ N := le_antisymm (inf_le_inf_left _ hPN) (le_inf inf_le_left hVP)
  have e1 : Nat.card ↥(V ⊔ P : Subgroup G) * Nat.card ↥(V ⊓ N : Subgroup G)
      = Nat.card ↥V * Nat.card ↥P := by
    rw [← hinfeq]
    exact natCard_sup_mul_natCard_inf_of_le_normalizer (hVnorm P)
  have e2 : Nat.card ↥X * Nat.card ↥(V ⊓ N : Subgroup G) = Nat.card ↥V * Nat.card ↥N := by
    rw [← hVN]
    exact natCard_sup_mul_natCard_inf_of_le_normalizer (hVnorm N)
  have e3 : Nat.card ↥P * (P.subgroupOf N).index = Nat.card ↥N := by
    rw [← natCard_subgroupOf_of_le hPN]; exact Subgroup.card_mul_index _
  refine Nat.eq_of_mul_eq_mul_right (m := Nat.card ↥(V ⊓ N : Subgroup G)) Nat.card_pos ?_
  calc Nat.card ↥(V ⊔ P : Subgroup G) * (P.subgroupOf N).index * Nat.card ↥(V ⊓ N : Subgroup G)
      = (Nat.card ↥(V ⊔ P : Subgroup G) * Nat.card ↥(V ⊓ N : Subgroup G))
          * (P.subgroupOf N).index := by ring
    _ = Nat.card ↥V * (Nat.card ↥P * (P.subgroupOf N).index) := by rw [e1]; ring
    _ = Nat.card ↥V * Nat.card ↥N := by rw [e3]
    _ = Nat.card ↥X * Nat.card ↥(V ⊓ N : Subgroup G) := e2.symm

theorem le_map_subtype_fittingRaw_of_commutator_eq_bot [Fact p.Prime] {H : Subgroup G}
    [Group.IsSolvable ↥H] (hF : fittingRaw ↥H = pCore p ↥H) {K P : Subgroup G} (hKH : K ≤ H)
    (hPH : P ≤ H)
    (hsup : (fittingRaw ↥H).map H.subtype ⊔ K = (fittingRawPreimage ↥H).map H.subtype)
    (hPp : IsPGroup p ↥P) (hcomm : ⁅K, P⁆ = ⊥) : P ≤ (fittingRaw ↥H).map H.subtype := by
  have hp : p.Prime := Fact.out
  have hVn' := fittingRaw_normal (↥H)
  set V : Subgroup G := (fittingRaw ↥H).map H.subtype with hVdef
  have hVH : V ≤ H := Subgroup.map_subtype_le _
  set q : ↥H →* (↥H ⧸ fittingRaw ↥H) := mk' (fittingRaw ↥H) with hq
  have hPK : P ≤ centralizer (K : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]; exact hcomm
  have hP' : P.subgroupOf H ≤ centralizer ((K.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    refine Subtype.ext ?_
    push_cast
    exact Subgroup.mem_centralizer_iff.1 (hPK (Subgroup.mem_subgroupOf.1 hx)) _
      (Subgroup.mem_subgroupOf.1 hy)
  have hKV : fittingRaw ↥H ⊔ K.subgroupOf H = fittingRawPreimage ↥H := by
    have h1 : (V ⊔ K).subgroupOf H = V.subgroupOf H ⊔ K.subgroupOf H :=
      Subgroup.subgroupOf_sup hVH hKH
    rw [hsup] at h1
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective] at h1
    rw [hVdef, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective] at h1
    exact h1.symm
  have himg : Subgroup.map q (K.subgroupOf H) = fittingRaw (↥H ⧸ fittingRaw ↥H) := by
    rw [← map_mk'_fittingRawPreimage (↥H), ← hKV, Subgroup.map_sup]
    simp [hq]
  have hPq : Subgroup.map q (P.subgroupOf H) ≤
      centralizer ((fittingRaw (↥H ⧸ fittingRaw ↥H) : Subgroup (↥H ⧸ fittingRaw ↥H)) :
        Set (↥H ⧸ fittingRaw ↥H)) := by
    rw [← himg]
    rintro x ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro y ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 (hP' ha) b hb]
  have hPle : Subgroup.map q (P.subgroupOf H) ≤ fittingRaw (↥H ⧸ fittingRaw ↥H) :=
    le_fittingRaw_of_le_centralizer_fittingRaw hPq
  have hPsub : IsPGroup p ↥(P.subgroupOf H) := by
    obtain ⟨m, hm⟩ := hPp.exists_card_eq
    exact IsPGroup.of_card (by rw [natCard_subgroupOf_of_le hPH, hm])
  have hbot : Subgroup.map q (P.subgroupOf H) = ⊥ := by
    obtain ⟨m, hm⟩ := (hPsub.map q).exists_card_eq
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [← Subgroup.card_eq_one, hm, h0, pow_zero]
    · exact absurd (((dvd_pow_self p h0.ne').trans hm.symm.dvd).trans
        (Subgroup.card_dvd_of_le hPle)) (not_dvd_natCard_fittingRaw_quotient hp hF)
  rw [Subgroup.map_eq_bot_iff, hq, QuotientGroup.ker_mk'] at hbot
  have h2 := Subgroup.map_mono (f := H.subtype) hbot
  rwa [Subgroup.map_subgroupOf_eq_of_le hPH] at h2

end Aux

section Main

variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {H R R0 : Subgroup G}
  (hadm : IsAdmissibleCoprimeActionQuadruple G H R R0)
  (hnot : ¬ HasPLengthLeOne p ↥⁅H, R⁆)
  (hmin : ∀ (Y : Type u) [Group Y] [Finite Y] (J A A0 : Subgroup Y),
    IsAdmissibleCoprimeActionQuadruple Y J A A0 → Nat.card Y < Nat.card G →
    HasPLengthLeOne p ↥⁅J, A⁆)

include hadm hnot hmin

theorem isHallSubgroup_fittingRaw_subgroupOf_fittingRawPreimage_of_minimal :
    IsHallSubgroup ({p} : Set ℕ) ((fittingRaw ↥H).subgroupOf (fittingRawPreimage ↥H)) :=
  isHallSubgroup_subgroupOf_fittingRaw Fact.out (fittingRaw_eq_pCore_of_minimal hadm hnot hmin)

theorem fittingRawPreimage_ne_fittingRaw_of_minimal :
    fittingRawPreimage ↥H ≠ fittingRaw ↥H := by
  have hsolvG : Group.IsSolvable G := hadm.isSolvable
  have hV := fittingRaw_normal (↥H)
  have hVp : IsPGroup p ↥(fittingRaw ↥H) := isPGroup_fittingRaw_of_minimal hadm hnot hmin
  intro hUV
  have hFq : fittingRaw (↥H ⧸ fittingRaw ↥H) = ⊥ := by
    have h1 := map_mk'_fittingRawPreimage (↥H)
    rw [hUV] at h1
    rw [← h1]
    refine le_bot_iff.1 ?_
    rintro x ⟨y, hy, rfl⟩
    simpa using (QuotientGroup.eq_one_iff (y : ↥H)).2 hy
  have hsub : Subsingleton (↥H ⧸ fittingRaw ↥H) := subsingleton_of_fittingRaw_eq_bot _ hFq
  have htop : fittingRaw ↥H = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact (QuotientGroup.eq_one_iff x).1
      (Subsingleton.elim (QuotientGroup.mk (s := fittingRaw ↥H) x) 1)
  refine not_hasPLengthLeOne_of_minimal hadm hnot hmin ?_
  refine hasPLengthLeOne_of_isPGroup_of_not_dvd_index (T := fittingRaw ↥H) hV hVp ?_
  rw [htop, Subgroup.index_top]
  exact fun hd => (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 hd)

theorem normal_map_subtype_fittingRawPreimage_of_minimal :
    ((fittingRawPreimage ↥H).map H.subtype).Normal :=
  normal_map_subtype_fittingRawPreimage hadm.normal

theorem exists_invariant_complement_sylow_of_minimal :
    ∃ K P : Subgroup G,
      K ≠ ⊥ ∧ K ≤ (fittingRawPreimage ↥H).map H.subtype ∧
        R ≤ normalizer (K : Set G) ∧
      (fittingRaw ↥H).map H.subtype ⊔ K = (fittingRawPreimage ↥H).map H.subtype ∧
      (fittingRaw ↥H).map H.subtype ⊓ K = ⊥ ∧
      (Nat.card ↥K).Coprime p ∧
      (fittingRaw ↥H).map H.subtype ⊔ (normalizer (K : Set G) ⊓ H) = H ∧
      R ≤ normalizer (P : Set G) ∧ P ≤ normalizer (K : Set G) ⊓ H ∧
      Nat.card ↥P
        = p ^ (Nat.card ↥(normalizer (K : Set G) ⊓ H : Subgroup G)).factorization p ∧
      Nat.card ↥((fittingRaw ↥H).map H.subtype ⊔ P)
        = p ^ (Nat.card ↥H).factorization p ∧
      ⁅K, P⁆ ≠ ⊥ := by
  have hp : p.Prime := Fact.out
  have hsolvG : Group.IsSolvable G := hadm.isSolvable
  have hHn : H.Normal := hadm.normal
  have hVn' := fittingRaw_normal (↥H)
  set V : Subgroup G := (fittingRaw ↥H).map H.subtype with hVdef
  set U : Subgroup G := (fittingRawPreimage ↥H).map H.subtype with hUdef
  have hnormOf : ∀ T S : Subgroup G, S.Normal → T ≤ normalizer (S : Set G) := fun T S hS => by
    have := hS
    rw [Subgroup.normalizer_eq_top (H := S)]
    exact le_top
  haveI hVn : V.Normal := normal_map_subtype_fittingRaw hHn
  have hUn : U.Normal := normal_map_subtype_fittingRawPreimage_of_minimal hadm hnot hmin
  have hUH : U ≤ H := Subgroup.map_subtype_le _
  have hVH : V ≤ H := Subgroup.map_subtype_le _
  have hVU : V ≤ U := Subgroup.map_mono (fittingRaw_le_fittingRawPreimage _)
  have hVp : IsPGroup p ↥V := by
    obtain ⟨m, hm⟩ := (isPGroup_fittingRaw_of_minimal hadm hnot hmin).exists_card_eq
    exact IsPGroup.of_card (by rw [hVdef, Subgroup.card_map_of_injective H.subtype_injective, hm])
  have hHall : IsHallSubgroup ({p} : Set ℕ) (V.subgroupOf U) := by
    refine isHallSubgroup_subgroupOf_of_natCard_eq (fittingRaw_le_fittingRawPreimage ↥H) hVU
      ((Subgroup.card_map_of_injective H.subtype_injective).symm)
      ((Subgroup.card_map_of_injective H.subtype_injective).symm)
      (isHallSubgroup_fittingRaw_subgroupOf_fittingRawPreimage_of_minimal hadm hnot hmin)
  have hcopU : (Nat.card ↥U).Coprime (Nat.card ↥R) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hUH) hadm.coprime
  obtain ⟨K, hKU, hKHall, -, hRK⟩ :=
    exists_isHallSubgroup_subgroupOf_ge_le_normalizer_of_le_normalizer (D := U) (A := R)
      (R := ⊥) inferInstance (hnormOf R U inferInstance) hcopU ({p} : Set ℕ)ᶜ
      bot_le (by simp [isPiNumber_iff]) (hnormOf R ⊥ inferInstance)
  have hKH : K ≤ H := hKU.trans hUH
  obtain ⟨hsup, hinf⟩ := sup_eq_and_inf_eq_bot_of_isHallSubgroup_compl hVU hKU hHall hKHall
    (hnormOf K V inferInstance)
  have hKcop : (Nat.card ↥K).Coprime p := by
    have h1 : IsPiNumber ({p} : Set ℕ)ᶜ (Nat.card ↥K) := by
      have h := hKHall.natCard
      rwa [natCard_subgroupOf_of_le hKU] at h
    refine Nat.Coprime.symm (hp.coprime_iff_not_dvd.2 fun hd => ?_)
    exact isPiNumber_iff.1 h1 p (Nat.mem_primeFactors.2 ⟨hp, hd, Nat.card_pos.ne'⟩) rfl
  have hKne : K ≠ ⊥ := by
    intro h0
    refine fittingRawPreimage_ne_fittingRaw_of_minimal hadm hnot hmin
      (Subgroup.map_injective H.subtype_injective ?_)
    rw [← hUdef, ← hVdef, ← hsup, h0, sup_bot_eq]
  have hfrat : U ⊔ (normalizer (K : Set G) ⊓ H) = H :=
    eq_sup_normalizer_inf_of_isHallSubgroup (hnormOf H U inferInstance) hKU hUH hKHall
  set N : Subgroup G := normalizer (K : Set G) ⊓ H with hNdef
  have hNH : N ≤ H := inf_le_right
  have hKN : K ≤ N := le_inf Subgroup.le_normalizer hKH
  have hVNsup : V ⊔ N = H := by
    refine le_antisymm (sup_le hVH hNH) ?_
    rw [← hfrat, ← hsup]
    exact sup_le (sup_le le_sup_left (hKN.trans le_sup_right)) le_sup_right
  have hRN : R ≤ normalizer (N : Set G) :=
    fun _ hr => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_normalizer hRK hr, hnormOf R H inferInstance hr⟩
  have hcopN : (Nat.card ↥N).Coprime (Nat.card ↥R) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hNH) hadm.coprime
  obtain ⟨P, hPN, hPHall, -, hRP⟩ :=
    exists_isHallSubgroup_subgroupOf_ge_le_normalizer_of_le_normalizer (D := N) (A := R)
      (R := ⊥) inferInstance hRN hcopN ({p} : Set ℕ)
      bot_le (by simp [isPiNumber_iff]) (hnormOf R ⊥ inferInstance)
  have hPcard : Nat.card ↥P = p ^ (Nat.card ↥N).factorization p :=
    natCard_eq_pow_factorization_of_isHallSubgroup_singleton hp hPN hPHall
  have hPp : IsPGroup p ↥P := IsPGroup.of_card hPcard
  have hPH : P ≤ H := hPN.trans hNH
  have hVPp : IsPGroup p ↥(V ⊔ P : Subgroup G) := hVp.to_sup_of_normal_left hPp
  have hVPcard : Nat.card ↥(V ⊔ P : Subgroup G) = p ^ (Nat.card ↥H).factorization p :=
    natCard_eq_pow_factorization_of_natCard_eq_mul hVPp
      (natCard_sup_mul_index_subgroupOf hPN hVNsup
        (inf_le_of_natCard_eq_pow_factorization hVp hPN hPcard)).symm
      (not_dvd_index_subgroupOf_of_natCard_eq_pow_factorization hp hPN hPcard)
  refine ⟨K, P, hKne, hKU, hRK, hsup, hinf, hKcop, ?_, hRP, hPN, hPcard, hVPcard, ?_⟩
  · rw [← hNdef, ← hVNsup]
  · intro hcomm
    have hPV : P ≤ V := le_map_subtype_fittingRaw_of_commutator_eq_bot
      (fittingRaw_eq_pCore_of_minimal hadm hnot hmin) hKH hPH hsup hPp hcomm
    refine not_hasPLengthLeOne_of_minimal hadm hnot hmin ?_
    refine hasPLengthLeOne_of_normal_of_natCard_eq hVH ?_
    rw [← hVPcard, sup_eq_left.2 hPV]

end Main

end

end CFSG.FeitThompson

