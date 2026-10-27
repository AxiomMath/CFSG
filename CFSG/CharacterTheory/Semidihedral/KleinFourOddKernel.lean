module

public import CFSG.CharacterTheory.Semidihedral.CentralHall
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.Dihedral.DisconnectedInvolutionGraph.CoprimeFixedLift

public noncomputable section

namespace CFSG.Semidihedral.KleinFourOddKernel

universe u v

variable {C : Type u} [Group C]

@[expose] def fourSubgroup (t s : C) : Subgroup C :=
  Subgroup.zpowers t ⊔ Subgroup.zpowers s

@[expose] def centralizer (s : C) : Subgroup C := Subgroup.centralizer {s}

@[expose] def oddPrimes : Set Nat.Primes := {p | p.val ≠ 2}

@[expose] def oddKernel (s : C) : Subgroup (centralizer s) :=
  CFSG.piCore oddPrimes (centralizer s)

@[expose] def centralizerKernel (N : Subgroup C) (s : C) : Subgroup (centralizer s) :=
  N.subgroupOf (centralizer s)

@[expose] def oddKernelIntersection (N : Subgroup C) (s : C) : Subgroup (oddKernel s) :=
  (centralizerKernel N s).subgroupOf (oddKernel s)

theorem mem_zpowers_involution [Finite C] (t x : C) (ht : orderOf t = 2) :
    x ∈ Subgroup.zpowers t ↔ x = 1 ∨ x = t := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, ht]
  constructor
  · rintro hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    have hn' : n < 2 := Finset.mem_range.mp hn
    have hcases : n = 0 ∨ n = 1 := by omega
    rcases hcases with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact Finset.mem_image.mpr ⟨0, by simp, pow_zero t⟩
    · exact Finset.mem_image.mpr ⟨1, by simp, by simp⟩

theorem commute_of_central (t s : C) (hc : t ∈ Subgroup.center C) : Commute t s :=
  (Subgroup.mem_center_iff.mp hc s).symm

theorem mem_fourSubgroup [Finite C] (t s x : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2) :
    x ∈ fourSubgroup t s ↔ x = 1 ∨ x = t ∨ x = s ∨ x = t * s := by
  have htc : Subgroup.zpowers t ≤ Subgroup.center C := Subgroup.zpowers_le.mpr hc
  let : (Subgroup.zpowers t).Normal := Subgroup.normal_of_le_center htc
  rw [fourSubgroup, Subgroup.mem_sup_of_normal_left]
  simp only [mem_zpowers_involution t _ ht, mem_zpowers_involution s _ hs]
  constructor
  · rintro ⟨a, rfl | rfl, b, rfl | rfl, rfl⟩ <;> simp
  · intro hx
    rcases hx with h | h | h | h
    · exact ⟨1, Or.inl rfl, 1, Or.inl rfl, by simp [h]⟩
    · exact ⟨t, Or.inr rfl, 1, Or.inl rfl, by simp [h]⟩
    · exact ⟨1, Or.inl rfl, s, Or.inr rfl, by simp [h]⟩
    · exact ⟨t, Or.inr rfl, s, Or.inr rfl, h.symm⟩

theorem fourSubgroup_card [Finite C] (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) : Nat.card (fourSubgroup t s) = 4 := by
  classical
  have ht1 : t ≠ 1 := by intro h; simp [h] at ht
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hprod := mul_notMem_of_orderOf_eq_two ht hs hne
  have heq : (fourSubgroup t s : Set C) = {t * s, t, s, 1} := by
    ext x
    simp only [SetLike.mem_coe, mem_fourSubgroup t s x hc ht hs,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  change Nat.card (fourSubgroup t s : Set C) = 4
  rw [heq, Nat.card_coe_set_eq]
  simp [Set.ncard_insert_of_notMem, hprod, ht1, hs1, hne]

theorem fourSubgroup_square [Finite C] (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (x : fourSubgroup t s) : x ^ 2 = 1 := by
  apply Subtype.ext
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have hs2 : s ^ 2 = 1 := hs ▸ pow_orderOf_eq_one s
  rcases (mem_fourSubgroup t s x hc ht hs).mp x.property with h | h | h | h
  · simp [h]
  · simpa [h] using ht2
  · simpa [h] using hs2
  · simp [h, (commute_of_central t s hc).mul_pow, ht2, hs2]

theorem fourSubgroup_isKleinFour [Finite C] (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) : IsKleinFour (fourSubgroup t s) := by
  refine ⟨fourSubgroup_card t s hc ht hs hne, ?_⟩
  apply Nat.dvd_antisymm
  · exact Monoid.exponent_dvd_of_forall_pow_eq_one (fourSubgroup_square t s hc ht hs)
  · let a : fourSubgroup t s := ⟨t, Subgroup.mem_sup_left (Subgroup.mem_zpowers t)⟩
    have ha : orderOf a = 2 := by rw [← Subgroup.orderOf_coe]; exact ht
    rw [← ha]
    exact Monoid.order_dvd_exponent a

theorem isPiSubgroup_odd_iff (K : Subgroup C) :
    CFSG.IsPiSubgroup oddPrimes K ↔ Odd (Nat.card K) := by
  constructor
  · intro h
    apply Nat.coprime_two_left.mp
    apply Nat.prime_two.coprime_iff_not_dvd.mpr
    intro hd
    exact h ⟨2, Nat.prime_two⟩ hd rfl
  · intro h p hd heq
    have hdiv : 2 ∣ Nat.card K := by simpa only [heq] using hd
    exact (Nat.prime_two.coprime_iff_not_dvd.mp h.coprime_two_left) hdiv

theorem piCore_odd_eq_pPrimeCore : CFSG.piCore oddPrimes C = CFSG.pPrimeCore 2 C := by
  unfold CFSG.piCore CFSG.pPrimeCore
  congr 1
  ext K
  simp only [Set.mem_ofPred_eq, isPiSubgroup_odd_iff, Nat.coprime_two_left]

instance oddKernel_normal (s : C) : (oddKernel s).Normal := by
  unfold oddKernel
  rw [piCore_odd_eq_pPrimeCore]
  infer_instance

theorem oddKernel_card [Finite C] (s : C) : Odd (Nat.card (oddKernel s)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold oddKernel
  rw [piCore_odd_eq_pPrimeCore]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

theorem le_oddKernel (s : C) (K : Subgroup (centralizer s))
    (hK : K.Normal) (hodd : Odd (Nat.card K)) : K ≤ oddKernel s :=
  le_sSup ⟨hK, (isPiSubgroup_odd_iff K).mpr hodd⟩

theorem fourSubgroup_le_centralizer (t s : C) (hc : t ∈ Subgroup.center C) :
    fourSubgroup t s ≤ centralizer s := by
  change Subgroup.zpowers t ⊔ Subgroup.zpowers s ≤ centralizer s
  apply sup_le <;> apply Subgroup.zpowers_le.mpr
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_center_iff.mp hc s).symm
  · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl

@[expose] def fourInCentralizer (t s : C) : Subgroup (centralizer s) :=
  (fourSubgroup t s).subgroupOf (centralizer s)

theorem fourInCentralizer_card [Finite C] (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) : Nat.card (fourInCentralizer t s) = 4 := by
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (fourSubgroup_le_centralizer t s hc)).toEquiv).trans
      (fourSubgroup_card t s hc ht hs hne)

theorem fourInCentralizer_central [Finite C] (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2) :
    fourInCentralizer t s ≤ Subgroup.center (centralizer s) := by
  intro v hv
  apply Subgroup.mem_center_iff.mpr
  intro x
  apply Subtype.ext
  change (x : C) * v = (v : C) * x
  rcases (mem_fourSubgroup t s v hc ht hs).mp hv with h | h | h | h
  · simp [h]
  · simpa only [h] using Subgroup.mem_center_iff.mp hc (x : C)
  · simpa only [h] using
      (Subgroup.mem_centralizer_singleton_iff.mp x.property)
  · rw [h, ← mul_assoc, Subgroup.mem_center_iff.mp hc (x : C), mul_assoc,
      (Subgroup.mem_centralizer_singleton_iff.mp x.property), ← mul_assoc]

@[expose] def onCentralizer (N : Subgroup C) [N.Normal] (s : C) :
    centralizer s →* Subgroup.centralizer {QuotientGroup.mk' N s} :=
  ((QuotientGroup.mk' N).comp (centralizer s).subtype).codRestrict _ (fun x => by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg (QuotientGroup.mk' N)
      (Subgroup.mem_centralizer_singleton_iff.mp x.property))

theorem onCentralizer_coe (N : Subgroup C) [N.Normal] (s : C) (x : centralizer s) :
    (onCentralizer N s x : C ⧸ N) = QuotientGroup.mk' N (x : C) := rfl

theorem onCentralizer_ker (N : Subgroup C) [N.Normal] (s : C) :
    (onCentralizer N s).ker = centralizerKernel N s := by
  ext x
  change (onCentralizer N s x = 1) ↔ (x : C) ∈ N
  rw [← Subtype.coe_inj]
  exact QuotientGroup.eq_one_iff _

theorem quotient_centralizer_lift [Finite C] (N : Subgroup C) [N.Normal]
    (hN : Odd (Nat.card N)) (s : C) (hs : orderOf s = 2)
    (q : C ⧸ N) (hq : q ∈ Subgroup.centralizer {QuotientGroup.mk' N s}) :
    ∃ x : C, QuotientGroup.mk' N x = q ∧ x ∈ centralizer s := by
  let : Finite (ConjAct C) := Finite.of_equiv C ConjAct.toConjAct.toEquiv
  let actor := ConjAct.toConjAct s
  let A := Subgroup.zpowers actor
  let nu := QuotientGroup.mk' N
  let original : A →* C := ConjAct.ofConjAct.toMonoidHom.comp A.subtype
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : MulDistribMulAction A C :=
    MulDistribMulAction.compHom C (MulAut.conj.comp original)
  let : MulDistribMulAction A (C ⧸ N) :=
    MulDistribMulAction.compHom (C ⧸ N) (MulAut.conj.comp (nu.comp original))
  have hactor : orderOf actor = 2 := (orderOf_injective ConjAct.toConjAct.toMonoidHom ConjAct.toConjAct.injective s).trans hs
  have hA : IsPGroup 2 A := IsPGroup.iff_card.mpr ⟨1, by simp [A, Nat.card_zpowers, hactor]⟩
  have hequiv (a : A) (x : C) : nu (a • x) = a • nu x := by
    change nu (original a * x * (original a)⁻¹) = nu (original a) * nu x * (nu (original a))⁻¹
    simp only [map_mul, map_inv]
  have hcop : ¬ 2 ∣ Nat.card nu.ker := by
    rw [QuotientGroup.ker_mk']
    exact Nat.prime_two.coprime_iff_not_dvd.mp hN.coprime_two_left
  have hfix (a : A) : a • q = q := by
    change nu (original a) * q * (nu (original a))⁻¹ = q
    rcases (mem_zpowers_involution actor a hactor).mp a.property with h | h
    · have ha : original a = 1 := by change ConjAct.ofConjAct (a : ConjAct C) = 1; simp [h]
      simp [ha]
    · have ha : original a = s := by change ConjAct.ofConjAct (a : ConjAct C) = s; simp [h, actor]
      rw [ha, ← Subgroup.mem_centralizer_singleton_iff.mp hq, mul_assoc,
        mul_inv_cancel, mul_one]
  obtain ⟨x, hx, hfixed⟩ :=
    CFSG.DisconnectedInvolutionGraph.Helpers.coprime_pgroup_fixed_lift 2 hA nu
      hequiv hcop q (by obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N q; exact ⟨x, hx⟩) hfix
  refine ⟨x, hx, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have h := hfixed (⟨actor, Subgroup.mem_zpowers actor⟩ : A)
  change s * x * s⁻¹ = x at h
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

theorem onCentralizer_surjective [Finite C] (N : Subgroup C) [N.Normal]
    (hN : Odd (Nat.card N)) (s : C) (hs : orderOf s = 2) :
    Function.Surjective (onCentralizer N s) := by
  intro q
  obtain ⟨x, hx, hxD⟩ := quotient_centralizer_lift N hN s hs q q.property
  exact ⟨⟨x, hxD⟩, Subtype.ext hx⟩

theorem centralizer_map_quotient [Finite C] (N : Subgroup C) [N.Normal]
    (hN : Odd (Nat.card N)) (s : C) (hs : orderOf s = 2) :
    (centralizer s).map (QuotientGroup.mk' N) =
      Subgroup.centralizer {QuotientGroup.mk' N s} := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (onCentralizer N s ⟨x, hx⟩).property
  · intro hq
    obtain ⟨x, hx, hxD⟩ := quotient_centralizer_lift N hN s hs q hq
    exact ⟨x, hxD, hx⟩

theorem hom_eq_one_of_coprime_card {E : Type v} [Group E]
    (f : C →* E) (hcop : (Nat.card C).Coprime (Nat.card E)) (x : C) : f x = 1 := by
  apply (pow_eq_one_iff_of_coprime hcop).mp
  exact ⟨by rw [← map_pow, pow_card_eq_one', map_one], pow_card_eq_one'⟩

theorem involution_zpowers_disjoint [Finite C] (t s : C)
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hne : t ≠ s) :
    Disjoint (Subgroup.zpowers t) (Subgroup.zpowers s) := by
  apply Subgroup.disjoint_def.mpr
  intro x hx hy
  rcases (mem_zpowers_involution t x ht).mp hx with h | h
  · exact h
  · rcases (mem_zpowers_involution s x hs).mp hy with h' | h'
    · exact h'
    · exact False.elim (hne (h.symm.trans h'))

@[expose] def fourProductEquiv [Finite C] (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) : Subgroup.zpowers t × Subgroup.zpowers s ≃* fourSubgroup t s := by
  let V := fourSubgroup t s
  let T := (Subgroup.zpowers t).subgroupOf V
  let S := (Subgroup.zpowers s).subgroupOf V
  have htV : Subgroup.zpowers t ≤ V := le_sup_left
  have hsV : Subgroup.zpowers s ≤ V := le_sup_right
  have hTcard : Nat.card T = 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe htV).toEquiv).trans
      (by rw [Nat.card_zpowers, ht])
  have hScard : Nat.card S = 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsV).toEquiv).trans
      (by rw [Nat.card_zpowers, hs])
  have hd : Disjoint T S := by
    apply Subgroup.disjoint_def.mpr
    intro x hx hy
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp (involution_zpowers_disjoint t s ht hs hne) hx hy
  have hcomp : T.IsComplement' S := Subgroup.isComplement'_of_card_mul_and_disjoint
    (by rw [hTcard, hScard, fourSubgroup_card t s hc ht hs hne]) hd
  have hcentral : T ≤ Subgroup.center V := by
    intro x hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp ((Subgroup.zpowers_le.mpr hc) hx) (y : C)
  exact ((Subgroup.subgroupOfEquivOfLe htV).symm.prodCongr
    (Subgroup.subgroupOfEquivOfLe hsV).symm).trans
      (OddFieldLift.internalDirectEquiv T S hcentral hcomp)

theorem fourProductEquiv_coe [Finite C] (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) (a : Subgroup.zpowers t) (b : Subgroup.zpowers s) :
    (fourProductEquiv t s hc ht hs hne (a, b) : C) = (a : C) * b := rfl

@[expose] def cyclicTwoEquiv (t : C) (ht : orderOf t = 2) :
    Multiplicative (ZMod 2) ≃* Subgroup.zpowers t := by
  let g : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1
  let a : Subgroup.zpowers t := ⟨t, Subgroup.mem_zpowers t⟩
  have hg : orderOf g = 2 := by simp [g]
  have ha : orderOf a = 2 := by rw [← Subgroup.orderOf_coe]; exact ht
  have hg1 : g ≠ 1 := by
    intro h
    have horder := hg
    rw [h, orderOf_one] at horder
    omega
  have hgen : ∀ x : Multiplicative (ZMod 2), x ∈ Subgroup.zpowers g := by
    intro x
    exact mem_zpowers_of_prime_card (p := 2)
      (G := Multiplicative (ZMod 2)) (by simp) hg1
  have hagen : ∀ x : Subgroup.zpowers t, x ∈ Subgroup.zpowers a := by
    intro x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.property
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext hk⟩
  exact mulEquivOfOrderOfEq hgen hagen (hg.trans ha.symm)

@[expose] def fourC2Equiv [Finite C] (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) :
    Multiplicative (ZMod 2) × Multiplicative (ZMod 2) ≃* fourSubgroup t s :=
  ((cyclicTwoEquiv t ht).prodCongr (cyclicTwoEquiv s hs)).trans
    (fourProductEquiv t s hc ht hs hne)

theorem fourC2Equiv_coe [Finite C] (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) (a b : Multiplicative (ZMod 2)) :
    (fourC2Equiv t s hc ht hs hne (a, b) : C) =
      (cyclicTwoEquiv t ht a : C) * (cyclicTwoEquiv s hs b : C) := rfl

theorem normalOdd_disjoint_four [Finite C] (N : Subgroup C)
    (hN : Odd (Nat.card N)) (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) : Disjoint N (fourSubgroup t s) := by
  apply Subgroup.disjoint_of_coprime_natCard
  rw [fourSubgroup_card t s hc ht hs hne]
  exact (by simpa using hN.coprime_two_right.pow_right 2)

theorem quotient_onFour_injective [Finite C] (N : Subgroup C) [N.Normal]
    (hN : Odd (Nat.card N)) (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) :
    Function.Injective ((QuotientGroup.mk' N).subgroupMap (fourSubgroup t s)) := by
  intro x y hxy
  apply Subtype.ext
  have hq : QuotientGroup.mk' N ((y : C)⁻¹ * x) = 1 := by
    have heq := congrArg Subtype.val hxy
    change QuotientGroup.mk' N (x : C) = QuotientGroup.mk' N (y : C) at heq
    rw [map_mul, map_inv, heq, inv_mul_cancel]
  have hNmem : (y : C)⁻¹ * x ∈ N := (QuotientGroup.eq_one_iff _).mp hq
  have hVmem : (y : C)⁻¹ * x ∈ fourSubgroup t s :=
    (fourSubgroup t s).mul_mem ((fourSubgroup t s).inv_mem y.property) x.property
  exact (inv_mul_eq_one.mp (Subgroup.disjoint_def.mp
    (normalOdd_disjoint_four N hN t s hc ht hs hne) hNmem hVmem)).symm

@[expose] def quotientFour (N : Subgroup C) [N.Normal] (t s : C) : Subgroup (C ⧸ N) :=
  (fourSubgroup t s).map (QuotientGroup.mk' N)

theorem quotientFour_le_centralizer (N : Subgroup C) [N.Normal] (t s : C)
    (hc : t ∈ Subgroup.center C) :
    quotientFour N t s ≤ Subgroup.centralizer {QuotientGroup.mk' N s} := by
  rintro _ ⟨x, hx, rfl⟩
  exact (onCentralizer N s ⟨x, fourSubgroup_le_centralizer t s hc hx⟩).property

theorem quotientFour_card [Finite C] (N : Subgroup C) [N.Normal]
    (hN : Odd (Nat.card N)) (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) : Nat.card (quotientFour N t s) = 4 := by
  let e := MulEquiv.ofBijective ((QuotientGroup.mk' N).subgroupMap (fourSubgroup t s))
    ⟨quotient_onFour_injective N hN t s hc ht hs hne,
      (QuotientGroup.mk' N).subgroupMap_surjective (fourSubgroup t s)⟩
  exact (Nat.card_congr e.toEquiv).symm.trans (fourSubgroup_card t s hc ht hs hne)

@[expose] def quotientFourInCentralizer (N : Subgroup C) [N.Normal] (t s : C) :
    Subgroup (Subgroup.centralizer {QuotientGroup.mk' N s}) :=
  (quotientFour N t s).subgroupOf (Subgroup.centralizer {QuotientGroup.mk' N s})

theorem fourInCentralizer_map (N : Subgroup C) [N.Normal] (t s : C)
    (hc : t ∈ Subgroup.center C) :
    (fourInCentralizer t s).map (onCentralizer N s) = quotientFourInCentralizer N t s := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨(v : C), hv, rfl⟩
  · rintro ⟨v, hv, hvx⟩
    exact ⟨⟨v, fourSubgroup_le_centralizer t s hc hv⟩, hv, Subtype.ext hvx⟩

theorem quotientFourInCentralizer_central [Finite C] (N : Subgroup C) [N.Normal]
    (hN : Odd (Nat.card N)) (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2) :
    quotientFourInCentralizer N t s ≤
      Subgroup.center (Subgroup.centralizer {QuotientGroup.mk' N s}) := by
  rw [← fourInCentralizer_map N t s hc]
  exact (Subgroup.map_mono (fourInCentralizer_central t s hc ht hs)).trans
    (Subgroup.map_center_le_center (onCentralizer_surjective N hN s hs))

theorem quotientFourInCentralizer_card [Finite C] (N : Subgroup C) [N.Normal]
    (hN : Odd (Nat.card N)) (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) : Nat.card (quotientFourInCentralizer N t s) = 4 :=
  (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (quotientFour_le_centralizer N t s hc)).toEquiv).trans
      (quotientFour_card N hN t s hc ht hs hne)

instance centralizerKernel_normal (N : Subgroup C) [N.Normal] (s : C) :
    (centralizerKernel N s).Normal := by
  change (N.subgroupOf (centralizer s)).Normal
  infer_instance

instance oddKernelIntersection_normal (N : Subgroup C) [N.Normal] (s : C) :
    (oddKernelIntersection N s).Normal := by
  change ((centralizerKernel N s).subgroupOf (oddKernel s)).Normal
  infer_instance

theorem centralizerKernel_odd (N : Subgroup C)
    (hN : Odd (Nat.card N)) (s : C) : Odd (Nat.card (centralizerKernel N s)) := by
  have hdvd : Nat.card (centralizerKernel N s) ∣ Nat.card N := by
    have hle : (centralizerKernel N s).map (centralizer s).subtype ≤ N := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    have h := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (centralizer s).subtype_injective] at h
    exact h
  exact Nat.coprime_two_left.mp (Nat.Coprime.of_dvd_right hdvd hN.coprime_two_left)

theorem centralizerKernel_le_oddKernel (N : Subgroup C) [N.Normal]
    (hN : Odd (Nat.card N)) (s : C) : centralizerKernel N s ≤ oddKernel s :=
  le_oddKernel s _ inferInstance (centralizerKernel_odd N hN s)

theorem oddKernelIntersection_card (N : Subgroup C) [N.Normal]
    (hN : Odd (Nat.card N)) (s : C) :
    Nat.card (oddKernelIntersection N s) = Nat.card (centralizerKernel N s) :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (centralizerKernel_le_oddKernel N hN s)).toEquiv

@[expose] def IsInternalDirectProduct {E : Type v} [Group E] (A B : Subgroup E) : Prop :=
  A.IsComplement' B ∧ ∀ (a : A) (b : B), Commute (a : E) (b : E)

@[expose] def quotientOddInCentralizer (N : Subgroup C) [N.Normal] (s : C)
    (B : Subgroup (C ⧸ N)) : Subgroup (Subgroup.centralizer {QuotientGroup.mk' N s}) :=
  B.subgroupOf (Subgroup.centralizer {QuotientGroup.mk' N s})

theorem quotientOddInCentralizer_card (N : Subgroup C) [N.Normal] (s : C)
    (B : Subgroup (C ⧸ N)) (hB : B ≤ Subgroup.centralizer {QuotientGroup.mk' N s}) :
    Nat.card (quotientOddInCentralizer N s B) = Nat.card B :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv

theorem quotient_centralizer_card [Finite C] (N : Subgroup C) [N.Normal]
    (hN : Odd (Nat.card N)) (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) (B : Subgroup (C ⧸ N))
    (hB : B ≤ Subgroup.centralizer {QuotientGroup.mk' N s})
    (hdir : IsInternalDirectProduct (quotientFourInCentralizer N t s)
      (quotientOddInCentralizer N s B)) :
    Nat.card (Subgroup.centralizer {QuotientGroup.mk' N s}) = 4 * Nat.card B := by
  have hcard := hdir.1.card_mul_card
  rw [quotientFourInCentralizer_card N hN t s hc ht hs hne,
    quotientOddInCentralizer_card N s B hB] at hcard
  exact hcard.symm

theorem lifted_centralizer_card [Finite C] (N : Subgroup C) [N.Normal]
    (hN : Odd (Nat.card N)) (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) (B : Subgroup (C ⧸ N))
    (hB : B ≤ Subgroup.centralizer {QuotientGroup.mk' N s})
    (hdir : IsInternalDirectProduct (quotientFourInCentralizer N t s)
      (quotientOddInCentralizer N s B)) :
    Nat.card (centralizer s) = 4 * Nat.card (centralizerKernel N s) * Nat.card B := by
  have hcard := (onCentralizer N s).ker.card_mul_index
  rw [Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (onCentralizer_surjective N hN s hs),
    Subgroup.card_top, onCentralizer_ker,
    quotient_centralizer_card N hN t s hc ht hs hne B hB hdir] at hcard
  calc
    Nat.card (centralizer s) = Nat.card (centralizerKernel N s) * (4 * Nat.card B) := hcard.symm
    _ = 4 * Nat.card (centralizerKernel N s) * Nat.card B := by ac_rfl

theorem fourInCentralizer_index [Finite C] (N : Subgroup C) [N.Normal]
    (hN : Odd (Nat.card N)) (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) (B : Subgroup (C ⧸ N))
    (hB : B ≤ Subgroup.centralizer {QuotientGroup.mk' N s})
    (hdir : IsInternalDirectProduct (quotientFourInCentralizer N t s)
      (quotientOddInCentralizer N s B)) :
    (fourInCentralizer t s).index = Nat.card (centralizerKernel N s) * Nat.card B := by
  have hcard := (fourInCentralizer t s).card_mul_index
  rw [fourInCentralizer_card t s hc ht hs hne,
    lifted_centralizer_card N hN t s hc ht hs hne B hB hdir] at hcard
  have hmul : 4 * (fourInCentralizer t s).index =
      4 * (Nat.card (centralizerKernel N s) * Nat.card B) := by
    simpa only [mul_assoc] using hcard
  omega

theorem central_four_complement_eq_piCore [Finite C] (A : Subgroup C)
    (hA : A ≤ Subgroup.center C) (hcard : Nat.card A = 4) (hodd : Odd A.index) :
    ∃ hcop : (Nat.card A).Coprime A.index,
      CFSG.piCore oddPrimes C = centralHallComplement A hA hcop := by
  have hcop : (Nat.card A).Coprime A.index := by
    rw [hcard]
    simpa using hodd.coprime_two_left.pow_left 2
  let K := centralHallComplement A hA hcop
  let R := CFSG.piCore oddPrimes C
  have hKodd : Odd (Nat.card K) := by
    rw [centralHallComplement_card A hA hcop]
    exact hodd
  have hRK : K ≤ R := le_sSup ⟨inferInstance, (isPiSubgroup_odd_iff K).mpr hKodd⟩
  have hRodd : Odd (Nat.card R) := by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [show R = CFSG.pPrimeCore 2 C from piCore_odd_eq_pPrimeCore]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  let e := centralHallComplementMulEquiv A hA hcop
  let pr : C →* A := (MonoidHom.fst A K).comp e.symm.toMonoidHom
  have htrivial (r : R) : pr r = 1 := by
    apply hom_eq_one_of_coprime_card (pr.comp R.subtype) _ r
    rw [hcard]
    simpa using hRodd.coprime_two_right.pow_right 2
  have hKR : R ≤ K := by
    intro r hr
    have hfirst : (e.symm r).1 = 1 := htrivial ⟨r, hr⟩
    have heq : e (e.symm r) = ((e.symm r).2 : C) := by
      rw [centralHallComplementMulEquiv_apply, hfirst]
      simp
    rw [e.apply_symm_apply] at heq
    rw [heq]
    exact (e.symm r).2.property
  exact ⟨hcop, le_antisymm hKR hRK⟩

theorem four_oddKernel_isComplement [Finite C] (N : Subgroup C) [N.Normal]
    (hN : Odd (Nat.card N)) (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) (B : Subgroup (C ⧸ N))
    (hB : B ≤ Subgroup.centralizer {QuotientGroup.mk' N s}) (hBodd : Odd (Nat.card B))
    (hdir : IsInternalDirectProduct (quotientFourInCentralizer N t s)
      (quotientOddInCentralizer N s B)) :
    (fourInCentralizer t s).IsComplement' (oddKernel s) := by
  have hodd : Odd (fourInCentralizer t s).index := by
    rw [fourInCentralizer_index N hN t s hc ht hs hne B hB hdir]
    exact (centralizerKernel_odd N hN s).mul hBodd
  obtain ⟨hcop, heq⟩ := central_four_complement_eq_piCore
    (fourInCentralizer t s) (fourInCentralizer_central t s hc ht hs)
      (fourInCentralizer_card t s hc ht hs hne) hodd
  change (fourInCentralizer t s).IsComplement' (CFSG.piCore oddPrimes (centralizer s))
  rw [heq]
  exact centralHallComplement_isComplement _ _ _

theorem fourInCentralizer_isSylow [Finite C] (N : Subgroup C) [N.Normal]
    (hN : Odd (Nat.card N)) (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) (B : Subgroup (C ⧸ N))
    (hB : B ≤ Subgroup.centralizer {QuotientGroup.mk' N s}) (hBodd : Odd (Nat.card B))
    (hdir : IsInternalDirectProduct (quotientFourInCentralizer N t s)
      (quotientOddInCentralizer N s B)) :
    ∃ P : Sylow 2 (centralizer s), (P : Subgroup (centralizer s)) = fourInCentralizer t s := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (fourInCentralizer t s) :=
    IsPGroup.iff_card.mpr ⟨2, by rw [fourInCentralizer_card t s hc ht hs hne]; rfl⟩
  have hnot : ¬ 2 ∣ (fourInCentralizer t s).index := by
    apply Nat.prime_two.coprime_iff_not_dvd.mp
    apply Odd.coprime_two_left
    rw [fourInCentralizer_index N hN t s hc ht hs hne B hB hdir]
    exact (centralizerKernel_odd N hN s).mul hBodd
  exact ⟨hP.toSylow hnot, IsPGroup.toSylow_coe _ _⟩

@[expose] def centralizerDirectEquiv [Finite C] (N : Subgroup C) [N.Normal]
    (hN : Odd (Nat.card N)) (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) (B : Subgroup (C ⧸ N))
    (hB : B ≤ Subgroup.centralizer {QuotientGroup.mk' N s}) (hBodd : Odd (Nat.card B))
    (hdir : IsInternalDirectProduct (quotientFourInCentralizer N t s)
      (quotientOddInCentralizer N s B)) :
    fourSubgroup t s × oddKernel s ≃* centralizer s :=
  ((Subgroup.subgroupOfEquivOfLe (fourSubgroup_le_centralizer t s hc)).symm.prodCongr
    (MulEquiv.refl (oddKernel s))).trans
      (OddFieldLift.internalDirectEquiv _ _ (fourInCentralizer_central t s hc ht hs)
        (four_oddKernel_isComplement N hN t s hc ht hs hne B hB hBodd hdir))

theorem centralizerDirectEquiv_coe [Finite C] (N : Subgroup C) [N.Normal]
    (hN : Odd (Nat.card N)) (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) (B : Subgroup (C ⧸ N))
    (hB : B ≤ Subgroup.centralizer {QuotientGroup.mk' N s}) (hBodd : Odd (Nat.card B))
    (hdir : IsInternalDirectProduct (quotientFourInCentralizer N t s)
      (quotientOddInCentralizer N s B)) (v : fourSubgroup t s) (r : oddKernel s) :
    (centralizerDirectEquiv N hN t s hc ht hs hne B hB hBodd hdir (v, r) : C) =
      (v : C) * (r : centralizer s) := rfl

@[expose] def onOddKernel (N : Subgroup C) [N.Normal] (s : C) :
    oddKernel s →* (C ⧸ N) :=
  (QuotientGroup.mk' N).comp ((centralizer s).subtype.comp (oddKernel s).subtype)

theorem onOddKernel_apply (N : Subgroup C) [N.Normal] (s : C) (r : oddKernel s) :
    onOddKernel N s r = QuotientGroup.mk' N ((r : centralizer s) : C) := rfl

theorem oddKernel_image_le_quotientOdd [Finite C] (N : Subgroup C) [N.Normal]
    (hN : Odd (Nat.card N)) (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) (B : Subgroup (C ⧸ N))
    (hdir : IsInternalDirectProduct (quotientFourInCentralizer N t s)
      (quotientOddInCentralizer N s B)) :
    (oddKernel s).map (onCentralizer N s) ≤ quotientOddInCentralizer N s B := by
  let A := quotientFourInCentralizer N t s
  let K := quotientOddInCentralizer N s B
  let e := OddFieldLift.internalDirectEquiv A K
    (quotientFourInCentralizer_central N hN t s hc ht hs) hdir.1
  let pr : Subgroup.centralizer {QuotientGroup.mk' N s} →* A :=
    (MonoidHom.fst A K).comp e.symm.toMonoidHom
  have hfirst (r : oddKernel s) : (e.symm (onCentralizer N s r)).1 = 1 := by
    apply hom_eq_one_of_coprime_card (pr.comp ((onCentralizer N s).comp (oddKernel s).subtype)) _ r
    rw [quotientFourInCentralizer_card N hN t s hc ht hs hne]
    simpa using (oddKernel_card s).coprime_two_right.pow_right 2
  rintro _ ⟨r, hr, rfl⟩
  have heq : e (e.symm (onCentralizer N s r)) =
      ((e.symm (onCentralizer N s r)).2 : Subgroup.centralizer {QuotientGroup.mk' N s}) := by
    rw [OddFieldLift.internalDirectEquiv_apply, hfirst ⟨r, hr⟩]
    exact one_mul _
  rw [e.apply_symm_apply] at heq
  rw [heq]
  exact (e.symm (onCentralizer N s r)).2.property

theorem oddKernel_image_eq_quotientOdd [Finite C] (N : Subgroup C) [N.Normal]
    (hN : Odd (Nat.card N)) (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) (B : Subgroup (C ⧸ N))
    (hB : B ≤ Subgroup.centralizer {QuotientGroup.mk' N s}) (hBodd : Odd (Nat.card B))
    (hdir : IsInternalDirectProduct (quotientFourInCentralizer N t s)
      (quotientOddInCentralizer N s B)) :
    (oddKernel s).map (onCentralizer N s) = quotientOddInCentralizer N s B := by
  have hle := oddKernel_image_le_quotientOdd N hN t s hc ht hs hne B hdir
  apply le_antisymm hle
  intro b hb
  obtain ⟨d, hd⟩ := onCentralizer_surjective N hN s hs b
  obtain ⟨⟨v, r⟩, hvr⟩ :=
    (four_oddKernel_isComplement N hN t s hc ht hs hne B hB hBodd hdir).2 d
  change (v : centralizer s) * (r : centralizer s) = d at hvr
  have hmul : onCentralizer N s v * onCentralizer N s r = b := by
    rw [← map_mul, hvr, hd]
  have hrB : onCentralizer N s r ∈ quotientOddInCentralizer N s B :=
    hle ⟨r, r.property, rfl⟩
  have hvB : onCentralizer N s v ∈ quotientOddInCentralizer N s B := by
    have heq : onCentralizer N s v = b * (onCentralizer N s r)⁻¹ :=
      eq_mul_inv_iff_mul_eq.mpr hmul
    rw [heq]
    exact (quotientOddInCentralizer N s B).mul_mem hb
      ((quotientOddInCentralizer N s B).inv_mem hrB)
  have hvA : onCentralizer N s v ∈ quotientFourInCentralizer N t s := by
    rw [← fourInCentralizer_map N t s hc]
    exact ⟨v, v.property, rfl⟩
  have hvone : onCentralizer N s v = 1 :=
    Subgroup.disjoint_def.mp hdir.1.disjoint hvA hvB
  rw [hvone, one_mul] at hmul
  exact ⟨r, r.property, hmul⟩

theorem onOddKernel_range [Finite C] (N : Subgroup C) [N.Normal]
    (hN : Odd (Nat.card N)) (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) (B : Subgroup (C ⧸ N))
    (hB : B ≤ Subgroup.centralizer {QuotientGroup.mk' N s}) (hBodd : Odd (Nat.card B))
    (hdir : IsInternalDirectProduct (quotientFourInCentralizer N t s)
      (quotientOddInCentralizer N s B)) : (onOddKernel N s).range = B := by
  have hmap := oddKernel_image_eq_quotientOdd N hN t s hc ht hs hne B hB hBodd hdir
  ext q
  constructor
  · rintro ⟨r, rfl⟩
    have hr : onCentralizer N s r ∈ quotientOddInCentralizer N s B := by
      rw [← hmap]
      exact ⟨r, r.property, rfl⟩
    exact hr
  · intro hq
    have hq' : (⟨q, hB hq⟩ : Subgroup.centralizer {QuotientGroup.mk' N s}) ∈
        (oddKernel s).map (onCentralizer N s) := by
      rw [hmap]
      exact hq
    obtain ⟨r, hr, heq⟩ := hq'
    exact ⟨⟨r, hr⟩, congrArg Subtype.val heq⟩

theorem onOddKernel_ker (N : Subgroup C) [N.Normal] (s : C) :
    (onOddKernel N s).ker = oddKernelIntersection N s := by
  ext r
  change QuotientGroup.mk' N ((r : centralizer s) : C) = 1 ↔
    ((r : centralizer s) : C) ∈ N
  exact QuotientGroup.eq_one_iff _

theorem oddKernelIntersection_map (N : Subgroup C) [N.Normal]
    (hN : Odd (Nat.card N)) (s : C) :
    (oddKernelIntersection N s).map
      ((centralizer s).subtype.comp (oddKernel s).subtype) = N ⊓ centralizer s := by
  unfold oddKernelIntersection
  rw [← Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le (centralizerKernel_le_oddKernel N hN s)]
  exact Subgroup.subgroupOf_map_subtype N (centralizer s)

@[expose] def toQuotientOdd [Finite C] (N : Subgroup C) [N.Normal]
    (hN : Odd (Nat.card N)) (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) (B : Subgroup (C ⧸ N))
    (hB : B ≤ Subgroup.centralizer {QuotientGroup.mk' N s}) (hBodd : Odd (Nat.card B))
    (hdir : IsInternalDirectProduct (quotientFourInCentralizer N t s)
      (quotientOddInCentralizer N s B)) : oddKernel s →* B :=
  (onOddKernel N s).codRestrict B (fun r => by
    rw [← onOddKernel_range N hN t s hc ht hs hne B hB hBodd hdir]
    exact ⟨r, rfl⟩)

theorem toQuotientOdd_coe [Finite C] (N : Subgroup C) [N.Normal]
    (hN : Odd (Nat.card N)) (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) (B : Subgroup (C ⧸ N))
    (hB : B ≤ Subgroup.centralizer {QuotientGroup.mk' N s}) (hBodd : Odd (Nat.card B))
    (hdir : IsInternalDirectProduct (quotientFourInCentralizer N t s)
      (quotientOddInCentralizer N s B)) (r : oddKernel s) :
    (toQuotientOdd N hN t s hc ht hs hne B hB hBodd hdir r : C ⧸ N) =
      QuotientGroup.mk' N ((r : centralizer s) : C) := rfl

theorem toQuotientOdd_surjective [Finite C] (N : Subgroup C) [N.Normal]
    (hN : Odd (Nat.card N)) (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) (B : Subgroup (C ⧸ N))
    (hB : B ≤ Subgroup.centralizer {QuotientGroup.mk' N s}) (hBodd : Odd (Nat.card B))
    (hdir : IsInternalDirectProduct (quotientFourInCentralizer N t s)
      (quotientOddInCentralizer N s B)) :
    Function.Surjective (toQuotientOdd N hN t s hc ht hs hne B hB hBodd hdir) := by
  intro b
  have hb : (b : C ⧸ N) ∈ (onOddKernel N s).range := by
    rw [onOddKernel_range N hN t s hc ht hs hne B hB hBodd hdir]
    exact b.property
  obtain ⟨r, hr⟩ := hb
  exact ⟨r, Subtype.ext hr⟩

theorem toQuotientOdd_ker [Finite C] (N : Subgroup C) [N.Normal]
    (hN : Odd (Nat.card N)) (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) (B : Subgroup (C ⧸ N))
    (hB : B ≤ Subgroup.centralizer {QuotientGroup.mk' N s}) (hBodd : Odd (Nat.card B))
    (hdir : IsInternalDirectProduct (quotientFourInCentralizer N t s)
      (quotientOddInCentralizer N s B)) :
    (toQuotientOdd N hN t s hc ht hs hne B hB hBodd hdir).ker = oddKernelIntersection N s := by
  ext r
  change (toQuotientOdd N hN t s hc ht hs hne B hB hBodd hdir r = 1) ↔
    ((r : centralizer s) : C) ∈ N
  rw [← Subtype.coe_inj]
  exact QuotientGroup.eq_one_iff _

@[expose] def oddKernelQuotientEquiv [Finite C] (N : Subgroup C) [N.Normal]
    (hN : Odd (Nat.card N)) (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) (B : Subgroup (C ⧸ N))
    (hB : B ≤ Subgroup.centralizer {QuotientGroup.mk' N s}) (hBodd : Odd (Nat.card B))
    (hdir : IsInternalDirectProduct (quotientFourInCentralizer N t s)
      (quotientOddInCentralizer N s B)) :
    oddKernel s ⧸ oddKernelIntersection N s ≃* B :=
  QuotientGroup.liftEquiv (oddKernelIntersection N s)
    (toQuotientOdd_surjective N hN t s hc ht hs hne B hB hBodd hdir)
      (toQuotientOdd_ker N hN t s hc ht hs hne B hB hBodd hdir).symm

theorem oddKernelQuotientEquiv_mk [Finite C] (N : Subgroup C) [N.Normal]
    (hN : Odd (Nat.card N)) (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) (B : Subgroup (C ⧸ N))
    (hB : B ≤ Subgroup.centralizer {QuotientGroup.mk' N s}) (hBodd : Odd (Nat.card B))
    (hdir : IsInternalDirectProduct (quotientFourInCentralizer N t s)
      (quotientOddInCentralizer N s B)) (r : oddKernel s) :
    (oddKernelQuotientEquiv N hN t s hc ht hs hne B hB hBodd hdir
      (QuotientGroup.mk' (oddKernelIntersection N s) r) : C ⧸ N) =
        QuotientGroup.mk' N ((r : centralizer s) : C) := rfl

theorem oddKernel_order [Finite C] (N : Subgroup C) [N.Normal]
    (hN : Odd (Nat.card N)) (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) (B : Subgroup (C ⧸ N))
    (hB : B ≤ Subgroup.centralizer {QuotientGroup.mk' N s}) (hBodd : Odd (Nat.card B))
    (hdir : IsInternalDirectProduct (quotientFourInCentralizer N t s)
      (quotientOddInCentralizer N s B)) :
    Nat.card (oddKernel s) = Nat.card (oddKernelIntersection N s) * Nat.card B := by
  have hcard := (toQuotientOdd N hN t s hc ht hs hne B hB hBodd hdir).ker.card_mul_index
  rw [Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (toQuotientOdd_surjective N hN t s hc ht hs hne B hB hBodd hdir),
    Subgroup.card_top, toQuotientOdd_ker] at hcard
  exact hcard.symm

theorem centralizer_order [Finite C] (N : Subgroup C) [N.Normal]
    (hN : Odd (Nat.card N)) (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) (B : Subgroup (C ⧸ N))
    (hB : B ≤ Subgroup.centralizer {QuotientGroup.mk' N s})
    (hdir : IsInternalDirectProduct (quotientFourInCentralizer N t s)
      (quotientOddInCentralizer N s B)) :
    Nat.card (centralizer s) = 4 * Nat.card (oddKernelIntersection N s) * Nat.card B := by
  rw [oddKernelIntersection_card N hN s]
  exact lifted_centralizer_card N hN t s hc ht hs hne B hB hdir

structure LiftedCentralizerConclusion (N : Subgroup C) [N.Normal] (t s : C)
    (B : Subgroup (C ⧸ N)) : Prop where
  klein_four : IsKleinFour (fourSubgroup t s)
  c2_product : ∃ e : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) ≃* fourSubgroup t s,
    ∀ a b, ∃ x : Subgroup.zpowers t, ∃ y : Subgroup.zpowers s,
      (e (a, b) : C) = (x : C) * y
  four_card : Nat.card (fourSubgroup t s) = 4
  central_four : fourInCentralizer t s ≤ Subgroup.center (centralizer s)
  sylow_two : ∃ P : Sylow 2 (centralizer s),
    (P : Subgroup (centralizer s)) = fourInCentralizer t s
  odd_core_normal : (oddKernel s).Normal
  odd_core_odd : Odd (Nat.card (oddKernel s))
  internal_direct : IsInternalDirectProduct (fourInCentralizer t s) (oddKernel s)
  generated_join : fourInCentralizer t s ⊔ oddKernel s = ⊤
  trivial_intersection : fourInCentralizer t s ⊓ oddKernel s = ⊥
  direct_equiv : ∃ e : fourSubgroup t s × oddKernel s ≃* centralizer s,
    ∀ (v : fourSubgroup t s) (r : oddKernel s),
      (e (v, r) : C) = (v : C) * (r : centralizer s)
  kernel_in_core : centralizerKernel N s ≤ oddKernel s
  kernel_normal : (oddKernelIntersection N s).Normal
  kernel_exact : (oddKernelIntersection N s).map
    ((centralizer s).subtype.comp (oddKernel s).subtype) = N ⊓ centralizer s
  kernel_card : Nat.card (oddKernelIntersection N s) = Nat.card (centralizerKernel N s)
  quotient_lift : Function.Surjective (onCentralizer N s)
  quotient_kernel : (onCentralizer N s).ker = centralizerKernel N s
  original_range : (onOddKernel N s).range = B
  original_kernel : (onOddKernel N s).ker = oddKernelIntersection N s
  restricted_quotient : ∃ f : oddKernel s →* B,
    Function.Surjective f ∧ f.ker = oddKernelIntersection N s ∧
      ∀ r : oddKernel s, (f r : C ⧸ N) = QuotientGroup.mk' N ((r : centralizer s) : C)
  first_isomorphism : ∃ e : oddKernel s ⧸ oddKernelIntersection N s ≃* B,
    ∀ r : oddKernel s,
      (e (QuotientGroup.mk' (oddKernelIntersection N s) r) : C ⧸ N) =
        QuotientGroup.mk' N ((r : centralizer s) : C)
  core_order : Nat.card (oddKernel s) = Nat.card (oddKernelIntersection N s) * Nat.card B
  centralizer_order : Nat.card (centralizer s) =
    4 * Nat.card (oddKernelIntersection N s) * Nat.card B

theorem odd_kernel_central_Klein_four_centralizer_lifting [Finite C]
    (N : Subgroup C) [N.Normal] (hN : Odd (Nat.card N)) (t s : C)
    (hc : t ∈ Subgroup.center C) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hne : t ≠ s) (B : Subgroup (C ⧸ N))
    (hB : B ≤ Subgroup.centralizer {QuotientGroup.mk' N s}) (hBodd : Odd (Nat.card B))
    (hdir : IsInternalDirectProduct (quotientFourInCentralizer N t s)
      (quotientOddInCentralizer N s B)) : LiftedCentralizerConclusion N t s B := by
  have hcentral := fourInCentralizer_central t s hc ht hs
  have hcomp := four_oddKernel_isComplement N hN t s hc ht hs hne B hB hBodd hdir
  exact
    { klein_four := fourSubgroup_isKleinFour t s hc ht hs hne
      c2_product := ⟨fourC2Equiv t s hc ht hs hne,
        fun a b => ⟨cyclicTwoEquiv t ht a, cyclicTwoEquiv s hs b,
          fourC2Equiv_coe t s hc ht hs hne a b⟩⟩
      four_card := fourSubgroup_card t s hc ht hs hne
      central_four := hcentral
      sylow_two := fourInCentralizer_isSylow N hN t s hc ht hs hne B hB hBodd hdir
      odd_core_normal := inferInstance
      odd_core_odd := oddKernel_card s
      internal_direct := ⟨hcomp, fun v r => (Subgroup.mem_center_iff.mp (hcentral v.property) r).symm⟩
      generated_join := hcomp.sup_eq_top
      trivial_intersection := hcomp.isCompl.inf_eq_bot
      direct_equiv := ⟨centralizerDirectEquiv N hN t s hc ht hs hne B hB hBodd hdir,
        centralizerDirectEquiv_coe N hN t s hc ht hs hne B hB hBodd hdir⟩
      kernel_in_core := centralizerKernel_le_oddKernel N hN s
      kernel_normal := inferInstance
      kernel_exact := oddKernelIntersection_map N hN s
      kernel_card := oddKernelIntersection_card N hN s
      quotient_lift := onCentralizer_surjective N hN s hs
      quotient_kernel := onCentralizer_ker N s
      original_range := onOddKernel_range N hN t s hc ht hs hne B hB hBodd hdir
      original_kernel := onOddKernel_ker N s
      restricted_quotient := ⟨toQuotientOdd N hN t s hc ht hs hne B hB hBodd hdir,
        toQuotientOdd_surjective N hN t s hc ht hs hne B hB hBodd hdir,
        toQuotientOdd_ker N hN t s hc ht hs hne B hB hBodd hdir,
        toQuotientOdd_coe N hN t s hc ht hs hne B hB hBodd hdir⟩
      first_isomorphism := ⟨oddKernelQuotientEquiv N hN t s hc ht hs hne B hB hBodd hdir,
        oddKernelQuotientEquiv_mk N hN t s hc ht hs hne B hB hBodd hdir⟩
      core_order := oddKernel_order N hN t s hc ht hs hne B hB hBodd hdir
      centralizer_order := centralizer_order N hN t s hc ht hs hne B hB hdir }

end CFSG.Semidihedral.KleinFourOddKernel
