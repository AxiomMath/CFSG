module

public import CFSG.GH74.GLS.Stage2.Local.Concl
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cICent
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cILift
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Quot
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Frat
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29E

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

theorem mem_O2Of_of_coprime {G : Type} [Group G] {C : Subgroup G} {x : G} (hxC : x ∈ C)
    (hx : Nat.Coprime (orderOf x) 2) : x ∈ O2Of C := by
  refine Subgroup.mem_map.mpr ⟨⟨x, hxC⟩, Subgroup.subset_closure ?_, rfl⟩
  show Nat.Coprime (orderOf (⟨x, hxC⟩ : ↥C)) 2
  rw [Subgroup.orderOf_mk]
  exact hx

theorem alt3_equiv : Nonempty (alternatingGroup (Fin 3) ≃* Multiplicative (ZMod 3)) := by
  have h1 : Nat.card (alternatingGroup (Fin 3)) = 3 := by rw [Nat.card_eq_fintype_card]; decide
  have h2 : Nat.card (Multiplicative (ZMod 3)) = 3 := by rw [Nat.card_eq_fintype_card]; decide
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic (alternatingGroup (Fin 3)) := isCyclic_of_prime_card h1
  have : IsCyclic (Multiplicative (ZMod 3)) := isCyclic_of_prime_card h2
  exact ⟨mulEquivOfCyclicCardEq (h1.trans h2.symm)⟩

section CardLemmas
variable {C E : Type} [Group C] [Group E]

theorem card_eq_card_map_mul (π : C →* E) (D : Subgroup C) :
    Nat.card ↥D = Nat.card ↥(D.map π) * Nat.card ↥(D ⊓ π.ker) := by
  have h1 := Subgroup.index_mul_card (π.ker.subgroupOf D)
  have h2 : (π.ker.subgroupOf D).index = Nat.card ↥(D.map π) := by
    have : π.ker.subgroupOf D = (π.comp D.subtype).ker := rfl
    rw [this, Subgroup.index_ker]
    congr 1
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h3 : Nat.card ↥(π.ker.subgroupOf D) = Nat.card ↥(D ⊓ π.ker) := by
    rw [← Subgroup.card_map_of_injective D.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  rw [h2, h3] at h1
  exact h1.symm

end CardLemmas

section Core
open CFSG.GH74.GLS.IVK.Proofs2.Ivk5An in
theorem lemma29b_core {C : Type} [Group C] [Finite C] (n : ℕ) (U : Subgroup C)
    (hU : IVK.IsFourSubgroup U)
    (hab : Concl53ab ⊤ (U.map (QuotientGroup.mk' (pPrimeCore 2 C))))
    (hc : Concl53c ⊤ (U.map (QuotientGroup.mk' (pPrimeCore 2 C))))
    (hd : Concl53d ⊤ (U.map (QuotientGroup.mk' (pPrimeCore 2 C))))
    (he : Concl53e ⊤ n (U.map (QuotientGroup.mk' (pPrimeCore 2 C))))
    (hf : Concl53f ⊤ n (U.map (QuotientGroup.mk' (pPrimeCore 2 C)))) :
    Lemma29b U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := pPrimeCore 2 C with hN
  set π := QuotientGroup.mk' N with hπ
  have hNodd : Odd (Nat.card N) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := C))
  set Ū := U.map π with hŪ
  have hU2 : IsPGroup 2 ↥U := IsPGroup.of_card (n := 2) (by rw [hU.2]; norm_num)
  set D := centralizer (U : Set C) with hD
  have hkerN : π.ker = N := QuotientGroup.ker_mk' N
  have hDN : Odd (Nat.card ↥(D ⊓ π.ker)) := by
    rw [hkerN]
    exact Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_le inf_le_right)
  set CK := D.map π with hCK
  have hCKeq : CenK (⊤ : Subgroup (C ⧸ N)) (Ū : Set (C ⧸ N)) = CK := by
    unfold CenK
    rw [top_inf_eq]
    apply le_antisymm
    · intro y hy
      obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective y
      have hc' : ∀ w ∈ U, π w * π c = π c * π w := fun w hw =>
        (Subgroup.mem_centralizer_iff.mp hy (π w) ⟨w, hw, rfl⟩)
      obtain ⟨x, hx1, hx2⟩ := exists_mem_centralizer_coset N hNodd U hU2 c hc'
      exact ⟨x, hx2, hx1⟩
    · rintro _ ⟨d, hd, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨w, hw, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hd w hw]

  unfold Concl53ab at hab
  unfold Concl53c at hc
  unfold Concl53d at hd
  unfold Concl53e at he
  unfold Concl53f at hf
  rw [hCKeq] at hab hc hd he hf
  obtain ⟨Xb, hXbC, hXb3, ⟨vb, hvbC, hvb2, hdecE⟩, hcommE, hsylE, hCQE⟩ := hab
  set Ob := pPrimeCoreOf 2 CK with hOb
  set Qb := O2core (O2res CK) with hQb
  have hQbO : Qb ≤ O2res CK := Subgroup.map_subtype_le _
  have hO2CK : O2res CK ≤ CK := Subgroup.map_subtype_le _
  have hQbCK : Qb ≤ CK := hQbO.trans hO2CK
  have hQb2 : IsPGroup 2 ↥Qb := (pCore_isPGroup (p := 2) (G := ↥(O2res CK))).map (O2res CK).subtype
  have hQbn : (Qb.subgroupOf CK).Normal := O2core_O2res_normal CK
  have hQbconj : ∀ c ∈ CK, ∀ q ∈ Qb, c * q * c⁻¹ ∈ Qb := by
    intro c hc q hq
    have := hQbn.conj_mem ⟨q, hQbCK hq⟩ (Subgroup.mem_subgroupOf.mpr hq) ⟨c, hc⟩
    exact Subgroup.mem_subgroupOf.mp this
  have hO22 : O22Of CK = Ob ⊔ Qb := O22Of_eq_of_concl53 CK n he hf
  have hUbQb : Ū ≤ Qb := hCQE ▸ inf_le_left

  have : IsMulCommutative ↥U := hU.1.toIsMulCommutative
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥U) ⟨b, hb⟩)
  have hUD : U ≤ D := by
    intro u hu
    show u ∈ centralizer (U : Set C)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact hUcomm w hw u hu
  set Pt : Subgroup C := D ⊓ Qb.comap π with hPt
  have hPtD : Pt ≤ D := inf_le_left
  have hPtmap : Pt.map π = Qb := by
    apply le_antisymm
    · rintro _ ⟨p, hp, rfl⟩
      exact (Subgroup.mem_inf.mp hp).2
    · intro q hq
      obtain ⟨d, hd, rfl⟩ := hQbCK hq
      exact ⟨d, Subgroup.mem_inf.mpr ⟨hd, hq⟩, rfl⟩
  have hPtnorm : ∀ g ∈ D, ∀ p ∈ Pt, g * p * g⁻¹ ∈ Pt := by
    intro g hg p hp
    obtain ⟨hpD, hpQ⟩ := Subgroup.mem_inf.mp hp
    refine Subgroup.mem_inf.mpr ⟨D.mul_mem (D.mul_mem hg hpD) (D.inv_mem hg), ?_⟩
    show π (g * p * g⁻¹) ∈ Qb
    rw [map_mul, map_mul, map_inv]
    exact hQbconj (π g) ⟨g, hg, rfl⟩ (π p) hpQ
  have hDnormPt : D ≤ normalizer (Pt : Set C) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    exact ⟨fun hh => hPtnorm g hg h hh, fun hh => by
      have := hPtnorm g⁻¹ (D.inv_mem hg) _ hh
      simpa [mul_assoc] using this⟩
  have hUPt : U ≤ Pt := fun u hu =>
    Subgroup.mem_inf.mpr ⟨hUD hu, hUbQb ⟨u, hu, rfl⟩⟩
  obtain ⟨S, hS⟩ := (hU2.comap_subtype (K := Pt)).exists_le_sylow
  set Q : Subgroup C := (S : Subgroup ↥Pt).map Pt.subtype with hQ
  have hQsyl : IsSylowOf 2 Q Pt := ⟨S, rfl⟩
  have hUQ : U ≤ Q := fun u hu =>
    ⟨⟨u, hUPt hu⟩, hS (Subgroup.mem_subgroupOf.mpr hu), rfl⟩
  have hQPt : Q ≤ Pt := hQsyl.le
  have hQD : Q ≤ D := hQPt.trans hPtD
  have hQ2 : IsPGroup 2 ↥Q := hQsyl.isPGroup
  have hQN : Q ⊓ N = ⊥ := isPGroup_two_inf_eq_bot_of_odd Q N hQ2 hNodd
  have hQmap : Q.map π = Qb := by
    have h1 := isSylowOf_map_mk_of_odd N hNodd hQsyl
    rw [hPtmap] at h1
    exact (h1.eq_of_le h1.le le_rfl hQb2).symm
  obtain ⟨xb, hxbX, hxb1⟩ : ∃ xb ∈ Xb, xb ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Xb = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [this, Subgroup.card_bot] at hXb3
    omega
  have hxb3 : orderOf xb = 3 := by
    have hd : orderOf xb ∣ 3 := by
      have := orderOf_dvd_natCard (⟨xb, hxbX⟩ : ↥Xb)
      rwa [hXb3, Subgroup.orderOf_mk] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hxb1
    · exact h
  have hXbz : zpowers xb = Xb := by
    apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hxbX)
    rw [Nat.card_zpowers, hxb3, hXb3]
  obtain ⟨x2, hx2D, hx2π⟩ := hXbC hxbX
  set Y : Subgroup C := Pt ⊔ zpowers x2 with hY
  have hYD : Y ≤ D := sup_le hPtD (zpowers_le.mpr hx2D)
  have hPtY : Pt ≤ Y := le_sup_left
  have hPtnormY : (Pt.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPtY).mpr (hYD.trans hDnormPt)
  obtain ⟨n1, hn1N, hn1Y, hn1π⟩ := frattini_lift Pt Q Y hPtY hPtnormY hQsyl π
    (by rw [hPtmap, hQmap]) x2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers x2))
  obtain ⟨x, hxn, hx3, hxπ⟩ := exists_pow_three_part π n1 (by rw [hn1π, hx2π, hxb3])
  have hxQ : x ∈ normalizer (Q : Set C) := (zpowers_le.mpr hn1N) hxn
  have hxD : x ∈ D := (zpowers_le.mpr (hYD hn1Y)) hxn
  have hxπ' : π x = xb := by rw [hxπ, hn1π, hx2π]
  set Xg : Subgroup C := zpowers x with hXg
  have hXgmap : Xg.map π = Xb := by
    rw [hXg, MonoidHom.map_zpowers, hxπ', hXbz]

  have hUN : U ⊓ N = ⊥ := isPGroup_two_inf_eq_bot_of_odd U N hU2 hNodd
  have hŪ4 : Nat.card ↥Ū = 4 := by
    rw [hŪ, card_map_of_inf_eq_bot N hUN, hU.2]
  have hŪ2 : IsPGroup 2 ↥Ū := hU2.map π
  have hOodd : Odd (Nat.card ↥Ob) := by
    rw [hOb]
    unfold pPrimeCoreOf
    rw [Subgroup.card_map_of_injective CK.subtype_injective]
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥CK))
  have hObmap : (pPrimeCoreOf 2 D).map π = Ob := map_pPrimeCoreOf_of_odd π D hDN
  have hObcomap : D ⊓ (Ob).comap π = pPrimeCoreOf 2 D := comap_pPrimeCoreOf_of_odd π D hDN
  have hker : (π.subgroupMap D).ker = π.ker.subgroupOf D := by
    ext d
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hρk : Odd (Nat.card (π.subgroupMap D).ker) := by
    rw [hker]
    have : Nat.card ↥(π.ker.subgroupOf D) = Nat.card ↥(D ⊓ π.ker) := by
      rw [← Subgroup.card_map_of_injective D.subtype_injective, Subgroup.subgroupOf_map_subtype,
        inf_comm]
    rw [this]
    exact hDN
  obtain ⟨vD, hvD2, hvDπ⟩ := exists_involution_lift_of_surjective (π.subgroupMap D)
    (π.subgroupMap_surjective D) hρk ⟨vb, hvbC⟩ (Subtype.ext (by simpa [pow_two] using hvb2))
  have hvD : (vD : C) ∈ D := vD.2
  have hv2 : (vD : C) * (vD : C) = 1 := by simpa using congrArg Subtype.val hvD2
  have hvπ : π (vD : C) = vb := congrArg Subtype.val hvDπ
  have hvzmap : (zpowers (vD : C)).map π = zpowers vb := by
    rw [MonoidHom.map_zpowers, hvπ]
  have hdec : ∀ c ∈ D, ∃ o ∈ pPrimeCoreOf 2 D, ∃ q ∈ Q, ∃ a ∈ Xg, ∃ b ∈ zpowers (vD : C),
      c = o * q * a * b := by
    intro c hcD
    obtain ⟨ob, hob, qb, hqb, xb', hxb', e, he', hce⟩ := hdecE (π c) ⟨c, hcD, rfl⟩
    obtain ⟨o₀, ho₀, hoπ⟩ : ob ∈ (pPrimeCoreOf 2 D).map π := by rw [hObmap]; exact hob
    obtain ⟨q, hq, hqπ⟩ : qb ∈ Q.map π := by rw [hQmap]; exact hqb
    obtain ⟨a, ha, haπ⟩ : xb' ∈ Xg.map π := by rw [hXgmap]; exact hxb'
    obtain ⟨b, hb, hbπ⟩ : e ∈ (zpowers (vD : C)).map π := by rw [hvzmap]; exact he'
    have hc'D : o₀ * q * a * b ∈ D := by
      refine D.mul_mem (D.mul_mem (D.mul_mem ?_ (hQD hq)) ?_) ?_
      · exact (Subgroup.map_subtype_le _ : pPrimeCoreOf 2 D ≤ D) ho₀
      · exact (zpowers_le.mpr hxD) ha
      · exact (zpowers_le.mpr hvD) hb
    have hπc' : π (o₀ * q * a * b) = π c := by
      rw [map_mul, map_mul, map_mul, hoπ, hqπ, haπ, hbπ, hce]
    have hm : c * (o₀ * q * a * b)⁻¹ ∈ pPrimeCoreOf 2 D := by
      rw [← hObcomap]
      refine Subgroup.mem_inf.mpr ⟨D.mul_mem hcD (D.inv_mem hc'D), ?_⟩
      show π (c * (o₀ * q * a * b)⁻¹) ∈ Ob
      rw [map_mul, map_inv, hπc', mul_inv_cancel]
      exact Ob.one_mem
    refine ⟨c * (o₀ * q * a * b)⁻¹ * o₀, (pPrimeCoreOf 2 D).mul_mem hm ho₀, q, hq, a, ha, b, hb, ?_⟩
    group

  have hO22D : (O22Of D).map π = Ob ⊔ Qb := by
    rw [map_O22Of_of_odd π D hDN]
    exact hO22
  have hO22comap : D ⊓ (O22Of CK).comap π = O22Of D := comap_O22Of_of_odd π D hDN
  have hQO22 : Q ≤ O22Of D := by
    rw [← hO22comap]
    refine le_inf hQD fun q hq => ?_
    show π q ∈ O22Of CK
    rw [hO22]
    have h1 : π q ∈ Q.map π := ⟨q, hq, rfl⟩
    rw [hQmap] at h1
    exact Subgroup.mem_sup_right h1
  have hObO : Ob ≤ O2res CK := by
    intro x hx
    have hxCK : x ∈ CK := (Subgroup.map_subtype_le _ : Ob ≤ CK) hx
    refine mem_O2Of_of_coprime hxCK ?_
    obtain ⟨y, hy, rfl⟩ := hx
    have h1 : orderOf (⟨y, hy⟩ : ↥(pPrimeCore 2 ↥CK)) ∣ Nat.card ↥(pPrimeCore 2 ↥CK) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    have h2 : orderOf (CK.subtype y) = orderOf y := Subgroup.orderOf_coe y
    rw [h2]
    exact Nat.Coprime.coprime_dvd_left h1
      (Nat.coprime_comm.mp (pPrimeCore_coprime_card (p := 2) (G := ↥CK)))
  have hObQbO : Ob ⊔ Qb ≤ O2res CK := sup_le hObO hQbO
  have hsylQb : IsSylowOf 2 Qb (Ob ⊔ Qb) := hsylE.of_le le_sup_right hObQbO
  have hcardQb : Nat.card ↥Qb = 2 ^ (Nat.card ↥(Ob ⊔ Qb)).factorization 2 := hsylQb.card_eq
  have hcardO22 : (Nat.card ↥(O22Of D)).factorization 2 =
      (Nat.card ↥(Ob ⊔ Qb)).factorization 2 := by
    have h1 := card_eq_card_map_mul π (O22Of D)
    have hodd : Odd (Nat.card ↥(O22Of D ⊓ π.ker)) :=
      Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_le (inf_le_right.trans hkerN.le))
    rw [h1, hO22D, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
    have h0 : (Nat.card ↥(O22Of D ⊓ π.ker)).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hodd.not_two_dvd_nat
    rw [Finsupp.add_apply, h0, add_zero]
  have hQsyl22 : IsSylowOf 2 Q (O22Of D) := by
    refine isSylowOf_of_card hQO22 ?_
    rw [← card_map_of_inf_eq_bot N hQN, hQmap, hcardQb, hcardO22]
  have hXgQ : Xg ≤ normalizer (Q : Set C) := zpowers_le.mpr hxQ
  have hcommQ : ⁅Q, Xg⁆ = Q := by
    have hle : ⁅Q, Xg⁆ ≤ Q := (Subgroup.le_normalizer_iff_commutator_le_left).mp hXgQ
    apply eq_of_map_eq N hQN hle le_rfl
    rw [Subgroup.map_commutator, hQmap, hXgmap, hcommE]
  have hQL34 : IsL34Two ↥Q := by
    obtain ⟨e₁⟩ := nonempty_equiv_map_of_inf_eq_bot N hQN
    obtain ⟨e₂⟩ := hc
    exact ⟨e₁.trans ((MulEquiv.subgroupCongr hQmap).trans e₂)⟩
  have hQXg : Q ⊓ centralizer (Xg : Set C) = U := by
    apply le_antisymm
    · intro q hq
      obtain ⟨hqQ, hqX⟩ := Subgroup.mem_inf.mp hq
      have hπq : π q ∈ Qb := by
        have h1 : π q ∈ Q.map π := ⟨q, hqQ, rfl⟩
        rwa [hQmap] at h1
      have hπqc : π q ∈ centralizer (Xb : Set (C ⧸ N)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [← hXgmap] at hy
        obtain ⟨g, hg, rfl⟩ := hy
        rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hqX g hg]
      have h2 : π q ∈ Ū := hCQE ▸ Subgroup.mem_inf.mpr ⟨hπq, hπqc⟩
      obtain ⟨u, hu, hπu⟩ := h2
      have h3 := mk_inj_of_inf_eq_bot N hQN (hUQ hu) hqQ hπu
      rw [← h3]
      exact hu
    · intro u hu
      refine Subgroup.mem_inf.mpr ⟨hUQ hu, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hgD : g ∈ D := (zpowers_le.mpr hxD) hg
      exact (Subgroup.mem_centralizer_iff.mp hgD u hu).symm
  have hx3mem : x ^ 3 ∈ pPrimeCoreOf 2 D := by
    rw [← hObcomap]
    refine Subgroup.mem_inf.mpr ⟨D.pow_mem hxD 3, ?_⟩
    show π (x ^ 3) ∈ Ob
    have h1 : xb ^ 3 = 1 := hxb3 ▸ pow_orderOf_eq_one xb
    rw [map_pow, hxπ', h1]
    exact Ob.one_mem
  have hUQc : U ≤ centralizer (Q : Set C) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (Subgroup.mem_centralizer_iff.mp (hQD hq) u hu).symm
  have hRD : centralizer (Q : Set C) ≤ D := by
    intro r hr
    show r ∈ centralizer (U : Set C)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact Subgroup.mem_centralizer_iff.mp hr u (hUQ hu)
  have hπR : (centralizer (Q : Set C)).map π ≤ Ū ⊔ Ob := by
    rintro _ ⟨r, hr, rfl⟩
    have h1 : π r ∈ CenK (⊤ : Subgroup (C ⧸ N)) (Qb : Set (C ⧸ N)) := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_top _, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [← hQmap] at hy
      obtain ⟨q, hq, rfl⟩ := hy
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hr q hq]
    rw [hd.1] at h1
    exact h1
  have hsylU : IsSylowOf 2 Ū (Ū ⊔ Ob) := isSylowOf_sup_of_commute_odd Ū Ob hŪ2 hOodd hd.2.2
  have hcardŪ : Nat.card ↥Ū = 2 ^ (Nat.card ↥(Ū ⊔ Ob)).factorization 2 := hsylU.card_eq
  have hv2ŪOb : (Nat.card ↥(Ū ⊔ Ob)).factorization 2 = 2 := by
    have h1 : (2 : ℕ) ^ (Nat.card ↥(Ū ⊔ Ob)).factorization 2 = 2 ^ 2 := by
      rw [← hcardŪ, hŪ4]
      norm_num
    exact Nat.pow_right_injective le_rfl h1
  have hv2R : (Nat.card ↥(centralizer (Q : Set C))).factorization 2 ≤ 2 := by
    have h1 := card_eq_card_map_mul π (centralizer (Q : Set C))
    have hdvd : Nat.card ↥((centralizer (Q : Set C)).map π) ∣ Nat.card ↥(Ū ⊔ Ob) :=
      Subgroup.card_dvd_of_le hπR
    have hodd : Odd (Nat.card ↥(centralizer (Q : Set C) ⊓ π.ker)) :=
      Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_le (inf_le_right.trans hkerN.le))
    have h0 : (Nat.card ↥(centralizer (Q : Set C) ⊓ π.ker)).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hodd.not_two_dvd_nat
    rw [h1, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
    simp only [Finsupp.coe_add, Pi.add_apply, h0, add_zero]
    have := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr hdvd 2
    rw [hv2ŪOb] at this
    exact this
  have hv2Rge : 2 ≤ (Nat.card ↥(centralizer (Q : Set C))).factorization 2 := by
    have h1 : Nat.card ↥U ∣ Nat.card ↥(centralizer (Q : Set C)) := Subgroup.card_dvd_of_le hUQc
    rw [hU.2] at h1
    have h2 : 2 ^ 2 ∣ Nat.card ↥(centralizer (Q : Set C)) := by simpa using h1
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h2
  have hUsylR : IsSylowOf 2 U (centralizer (Q : Set C)) := by
    refine isSylowOf_of_card hUQc ?_
    rw [hU.2, le_antisymm hv2R hv2Rge]
    norm_num

  have hQI : ∀ (P : Type) [Group P] (φ : ↥CK →* P), Function.Surjective φ →
      φ.ker = (O22Of CK).subgroupOf CK →
      CFSG.GH74.GLS.Stage2.Local.QuotIso D (O22Of D) P := by
    intro P _ φ hφs hφk
    set ψ : ↥D →* P := φ.comp (π.subgroupMap D) with hψ
    have hψs : Function.Surjective ψ := hφs.comp (π.subgroupMap_surjective D)
    have hψk : ψ.ker = (O22Of D).subgroupOf D := by
      ext d
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hO22comap]
      change φ (π.subgroupMap D d) = 1 ↔ _
      rw [← MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        exact Subgroup.mem_inf.mpr ⟨d.2, h⟩
      · intro h
        exact (Subgroup.mem_inf.mp h).2
    have hnorm : ((O22Of D).subgroupOf D).Normal := by
      rw [← hψk]
      exact MonoidHom.normal_ker ψ
    exact ⟨hnorm, ⟨(QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)⟩⟩
  have hquot : CFSG.GH74.GLS.Stage2.Local.QuotIso D (O22Of D) (Multiplicative (ZMod 3)) ∨
      CFSG.GH74.GLS.Stage2.Local.QuotIso D (O22Of D) (Equiv.Perm (Fin 3)) := by
    by_cases hn : n ≤ 9
    · left
      obtain ⟨φ, hφs, hφk⟩ := hf.1 hn
      have hObbot : Ob = ⊥ := by
        have h1 : Nat.card ↥Ob = 1 := by
          rw [he]
          have : n ≠ 11 := by omega
          simp [this]
        exact Subgroup.eq_bot_of_card_eq _ h1
      have hO22Q : O22Of CK = Qb := by rw [hO22, hObbot, bot_sup_eq]
      obtain ⟨eA⟩ := alt3_equiv
      have hs : Function.Surjective
          ((eA : ↥(alternatingGroup (Fin 3)) →* Multiplicative (ZMod 3)).comp φ) :=
        eA.surjective.comp hφs
      refine hQI _ ((eA : ↥(alternatingGroup (Fin 3)) →* Multiplicative (ZMod 3)).comp φ) hs ?_
      rw [MonoidHom.ker_mulEquiv_comp, hφk, hO22Q]
    · right
      obtain ⟨φ, hφs, hφk⟩ := hf.2 (by omega)
      exact hQI _ φ hφs (by rw [hφk, hO22])
  refine ⟨Q, Xg, (vD : C), hQsyl22, hv2, ⟨x, rfl, hx3, Subgroup.mem_inf.mpr ⟨hxQ, hxD⟩, hx3mem⟩,
    hdec, hcommQ, hQL34, hQXg, hUsylR, hquot⟩

end Core

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
